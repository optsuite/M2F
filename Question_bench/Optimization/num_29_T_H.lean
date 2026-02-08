import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace

class OriginalProblem where
  n_var : ℕ
  constraints : (Fin n_var → ℝ) → Prop
  objective : (Fin n_var → ℝ) → ℝ

class OptProblem extends OriginalProblem where
  n_eqs : ℕ
  eq_constraints : (Fin n_var → ℝ) → (Fin n_eqs → ℝ)
  n_ieqs : ℕ
  ieq_constraints : (Fin n_var → ℝ) → (Fin n_ieqs → ℝ)
  constraints := fun x => eq_constraints x = 0 ∧ ieq_constraints x ≤ 0
  h_constraints : constraints =  fun x => eq_constraints x = 0 ∧ ieq_constraints x ≤ 0 := by simp

class LP extends OptProblem where
  c : Fin n_var → ℝ
  A_eq : Matrix (Fin n_eqs) (Fin n_var) ℝ
  b_eq : Fin n_eqs → ℝ
  A_ieq : Matrix (Fin n_ieqs) (Fin n_var) ℝ
  b_ieq : Fin n_ieqs → ℝ
  objective := fun x => c ⬝ᵥ x
  eq_constraints := fun x => A_eq *ᵥ x - b_eq
  ieq_constraints := fun x => A_ieq *ᵥ x - b_ieq
  h_objective : objective = fun x => c ⬝ᵥ x := by simp
  h_eq : eq_constraints = fun x => A_eq *ᵥ x - b_eq := by simp
  h_ieq : ieq_constraints = fun x => A_ieq *ᵥ x - b_ieq := by simp

class SDP extends OriginalProblem where
  c : Fin n_var → ℝ
  n_eqs : ℕ
  A_eq : Matrix (Fin n_eqs) (Fin n_var) ℝ
  b_eq : Fin n_eqs → ℝ
  eq_constraints := fun x => A_eq *ᵥ x - b_eq
  n_ieqs : ℕ
  A_sd : Fin n_var → Matrix (Fin n_ieqs) (Fin n_ieqs) ℝ
  B_sd : Matrix (Fin n_ieqs) (Fin n_ieqs) ℝ
  ieq_constraints := fun x => ∑ i, x i • A_sd i + B_sd
  constraints := fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef
  h_constraints : constraints =  fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef := by
simp
  objective := fun x => c ⬝ᵥ x
  h_objective : objective = fun x => c ⬝ᵥ x := by simp

def subequivlance (p q : OriginalProblem) : Prop :=
  ∀ (x : Fin p.n_var → ℝ), (p.constraints x) →
  ∃ (y : Fin q.n_var → ℝ), (q.constraints y) ∧
  q.objective y = p.objective x

def equivalence (p q : OriginalProblem) : Prop :=
  subequivlance p q ∧ subequivlance q p

class DualProblem (p : OptProblem) where
  dual_objective : (Fin p.n_eqs → ℝ) → (Fin p.n_ieqs → ℝ) → EReal
  dual_domain : Set ((Fin p.n_eqs → ℝ) × (Fin p.n_ieqs → ℝ))
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ), ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by
simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp


/-Derive the Lagrange dual problem
\[
\begin{array}{ll}
\text{minimize} & x^T W x \\
\text{subject to} & x_i^2 = 1, \quad i = 1, \ldots, n.
\end{array}
\]


-/
noncomputable section

variable (n : ℕ) (W : Matrix (Fin n) (Fin n) ℝ)

def P : OptProblem where
  n_var := n
  n_eqs := n
  eq_constraints := fun x i => x i * x i - 1
  n_ieqs := 0
  ieq_constraints := 0
  objective := fun x => x ⬝ᵥ W *ᵥ x

/-- Lagrangian dual objective for an optimization problem. -/
abbrev lagrangianDualObjective (p : OptProblem) :
    (Fin p.n_eqs → ℝ) → (Fin p.n_ieqs → ℝ) → EReal :=
  fun lam mu =>
    ⨅ x : (Fin p.n_var → ℝ),
      ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal

/-- Feasible domain for the Lagrangian dual variables. -/
abbrev lagrangianDualDomain (p : OptProblem) :
    Set ((Fin p.n_eqs → ℝ) × (Fin p.n_ieqs → ℝ)) :=
  { (lam, mu) | lagrangianDualObjective p lam mu ≠ ⊥ ∧ mu ≥ 0 }

/-- Package the standard Lagrangian dual as a `DualProblem`. -/
def mkDualProblem (p : OptProblem) : DualProblem p :=
  { dual_objective := lagrangianDualObjective p
    dual_domain := lagrangianDualDomain p
    h_objective := rfl
    h_domain := rfl }

def Q : DualProblem (P n W) := mkDualProblem (P n W)

end

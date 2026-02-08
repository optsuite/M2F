import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace
set_option linter.style.longLine false

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


/-Find the dual function of the LP
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & G x \preceq h \\
& A x = b.
\end{array}
\]
Give the dual problem, and make the implicit equality constraints explicit.


-/
noncomputable section

variable (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ) (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l →
ℝ)

def P : LP where
  n_var := n
  n_eqs := l
  A_eq := A
  b_eq := b
  n_ieqs := m
  A_ieq := G
  b_ieq := h
  c := c

/-- Dual objective for the LP `P` in standard Lagrangian form. -/
def dualObjective_P (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin m → ℝ) (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l → ℝ) :
    (Fin ((P n m l c G h A b).toOptProblem.n_eqs) → ℝ) →
      (Fin ((P n m l c G h A b).toOptProblem.n_ieqs) → ℝ) → EReal :=
  let p := (P n m l c G h A b).toOptProblem
  fun lam mu =>
    ⨅ x : (Fin p.n_var → ℝ),
      ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal

/-- Dual domain for the LP `P` using the standard nonbottom/nonnegative constraints. -/
def dualDomain_P (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin m → ℝ) (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l → ℝ) :
    Set ((Fin ((P n m l c G h A b).toOptProblem.n_eqs) → ℝ) ×
      (Fin ((P n m l c G h A b).toOptProblem.n_ieqs) → ℝ)) :=
  {(lam, mu) | dualObjective_P n m l c G h A b lam mu ≠ ⊥ ∧ mu ≥ 0}

/-- The dual objective `dualObjective_P` matches the generic Lagrangian template. -/
lemma dualObjective_P_h_objective (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin m → ℝ) (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l → ℝ) :
    dualObjective_P n m l c G h A b =
      (fun lam mu =>
        ⨅ x : (Fin ((P n m l c G h A b).toOptProblem.n_var) → ℝ),
          ((lam ⬝ᵥ (P n m l c G h A b).toOptProblem.eq_constraints x) +
            (mu ⬝ᵥ (P n m l c G h A b).toOptProblem.ieq_constraints x) +
              (P n m l c G h A b).toOptProblem.objective x).toEReal) := by
  rfl

/-- The dual domain `dualDomain_P` matches the standard nonbottom/nonnegative form. -/
lemma dualDomain_P_h_domain (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin m → ℝ) (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l → ℝ) :
    dualDomain_P n m l c G h A b =
      {(lam, mu) | dualObjective_P n m l c G h A b lam mu ≠ ⊥ ∧ mu ≥ 0} := by
  rfl

/-- Construct the dual problem for `P` from the standard templates. -/
def Q_mk (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l → ℝ) :
    DualProblem (P n m l c G h A b).toOptProblem :=
  { dual_objective := dualObjective_P n m l c G h A b
    dual_domain := dualDomain_P n m l c G h A b
    h_objective := dualObjective_P_h_objective n m l c G h A b
    h_domain := dualDomain_P_h_domain n m l c G h A b }

def Q (n m l : ℕ) (c : Fin n → ℝ) (G : Matrix (Fin m) (Fin n) ℝ) (h : Fin m → ℝ)
    (A : Matrix (Fin l) (Fin n) ℝ) (b : Fin l → ℝ) :
    DualProblem (P n m l c G h A b).toOptProblem :=
  Q_mk n m l c G h A b

end

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


/-Derive a dual problem for
\[
\begin{array}{ll}
\text{min} \quad &\sum_{i=1}^{N} \|y_i\|_2 + (1/2)\|x - x_0\|_2^2. \\
\text{subject to} & y_i = A_ix+b_i, i=1, 2, \cdots n
\end{array}
\]
The problem data are \( A_i \in \mathbb{R}^{m_i \times n},  b_i \in \mathbb{R}^{m_i} \), and \( x_0 \in \mathbb{R}^n
\).

-/
noncomputable section

variable (n m k : ℕ) [NeZero n] [NeZero m] [NeZero k] (A : Fin k → Matrix (Fin m) (Fin n) ℝ) (b : Fin k → Fin m → ℝ) (x0 : Fin n → ℝ) (x : Fin (m * k + n) → ℝ) (x0 : Fin n →
ℝ)


noncomputable def P : OptProblem where
  n_var := n + m * k
  n_eqs := m * k
  eq_constraints := fun x i =>
    let (j, l) := (i / m, i.toNat % m)
    let jj := Fin.ofNat k j; let ll := Fin.ofNat m l
    let xx := fun t : Fin n => x (Fin.ofNat (n + m * k) t)
    (A jj *ᵥ xx + b jj ) ll - x (Fin.ofNat (n + m * k) (m * j + l))
  n_ieqs := 0
  ieq_constraints := 0
  objective := fun x =>
    let xx := fun t : Fin n => x (Fin.ofNat (n + m * k) t)
    let yy (j : Fin k) : Fin m → ℝ := fun l => x (Fin.ofNat (n + m * k) (m * j + l))
    (xx - x0) ⬝ᵥ (xx - x0) + ∑ j, sqrt ((yy j) ⬝ᵥ (yy j))

/-- The dual objective functional attached to `P n m k A b x0`. -/
def Q_dualObjective (n m k : ℕ) [NeZero n] [NeZero m] [NeZero k]
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ) (b : Fin k → Fin m → ℝ) (x0 : Fin n → ℝ) :
    (Fin (P n m k A b x0).n_eqs → ℝ) → (Fin (P n m k A b x0).n_ieqs → ℝ) → EReal :=
  fun lam mu =>
    ⨅ x : Fin (P n m k A b x0).n_var → ℝ,
      ((lam ⬝ᵥ (P n m k A b x0).eq_constraints x) +
          (mu ⬝ᵥ (P n m k A b x0).ieq_constraints x) +
          (P n m k A b x0).objective x).toEReal

/-- The dual feasible domain for the dual objective of `P n m k A b x0`. -/
def Q_dualDomain (n m k : ℕ) [NeZero n] [NeZero m] [NeZero k]
    (A : Fin k → Matrix (Fin m) (Fin n) ℝ) (b : Fin k → Fin m → ℝ) (x0 : Fin n → ℝ) :
    Set ((Fin (P n m k A b x0).n_eqs → ℝ) × (Fin (P n m k A b x0).n_ieqs → ℝ)) :=
  {(lam, mu) | Q_dualObjective n m k A b x0 lam mu ≠ ⊥ ∧ mu ≥ 0}

def Q : DualProblem (P n m k A b x0) :=
  { dual_objective := Q_dualObjective n m k A b x0
    dual_domain := Q_dualDomain n m k A b x0
    h_objective := rfl
    h_domain := rfl }

end

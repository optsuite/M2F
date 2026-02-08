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
  h_constraints : constraints = fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef := by
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
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ),
    ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp



noncomputable section

def answer : ℝ × ℝ := ((2 : ℝ) / 5, (1 : ℝ) / 5)

/-- A linear lower bound on `y1 + y2` from the two active constraints. -/
lemma num_1_S_E_lower_bound (y1 y2 : ℝ) (h1 : 2 * y1 + y2 ≥ 1)
    (h2 : y1 + 3 * y2 ≥ 1) : (3 / 5 : ℝ) ≤ y1 + y2 := by
  linarith

/-- The proposed `answer` satisfies all feasibility inequalities. -/
lemma num_1_S_E_answer_feasible : let (x1, x2) := answer
  2 * x1 + x2 ≥ 1 ∧ x1 + 3 * x2 ≥ 1 ∧ x1 ≥ 0 ∧ x2 ≥ 0 := by
  simp [answer]
  constructor
  · norm_num
  · constructor
    · norm_num
    · norm_num

/--
\[
\begin{array}{ll}
\text{min}_{x_1, x_2} & f_0(x_1, x_2) \\
\text{subject to} & 2x_1 + x_2 \geq 1 \\
& x_1 + 3x_2 \geq 1 \\
& x_1 \geq 0, \quad x_2 \geq 0.
\end{array}
\]
Find an optimal point \((x_1, x_2)\) for the problem, where \( f_0(x_1, x_2) = x_1 + x_2 \).
-/
theorem num_1_S_E : let (x1, x2) := answer
  ∀ y1 y2 : ℝ, 2 * y1 + y2 ≥ 1 → y1 + 3 * y2 ≥ 1 → y1 ≥ 0 → y2 ≥ 0 → x1 + x2 ≤ y1 + y2 ∧
  2 * x1 + x2 ≥ 1 ∧ x1 + 3 * x2 ≥ 1 ∧ x1 ≥ 0 ∧ x2 ≥ 0 := by
  simp [answer]
  intro y1 y2 h1 h2 _ _
  constructor
  · have hbound : (3 / 5 : ℝ) ≤ y1 + y2 := num_1_S_E_lower_bound y1 y2 h1 h2
    linarith
  ·
    simpa [answer] using num_1_S_E_answer_feasible

end

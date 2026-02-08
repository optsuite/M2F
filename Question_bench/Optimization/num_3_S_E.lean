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

def answer : Fin 3 → ℝ := ![1, (1 : ℝ) / 2, -1]

/-- Compute the gradient term `A *ᵥ answer + b`. -/
lemma num_3_S_E_grad :
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![13, 12, -2; 12, 17, 6; -2, 6, 12]
  let b : Fin 3 → ℝ := ![-22, -14.5, 13]
  (A *ᵥ answer + b) = ![-1, 0, 2] := by
  classical
  ext i
  fin_cases i <;>
    simp [answer] <;>
    ring_nf

/-- Sum-of-squares decomposition for the quadratic form associated to `A`. -/
lemma num_3_S_E_qform_eq_sum_squares :
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![13, 12, -2; 12, 17, 6; -2, 6, 12]
  ∀ d : Fin 3 → ℝ,
    d ⬝ᵥ A *ᵥ d =
      13 * (d 0 + (12/13) * d 1 - (2/13) * d 2)^2
      + (77/13) * (d 1 + (102/77) * d 2)^2
      + (100/77) * (d 2)^2 := by
  classical
  dsimp
  intro d
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring_nf

/-- Nonnegativity of the quadratic form associated to `A`. -/
lemma num_3_S_E_qform_nonneg :
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![13, 12, -2; 12, 17, 6; -2, 6, 12]
  ∀ d : Fin 3 → ℝ, 0 ≤ d ⬝ᵥ A *ᵥ d := by
  classical
  dsimp
  intro d
  have hsum := num_3_S_E_qform_eq_sum_squares (d := d)
  have hsq0 : 0 ≤ (d 0 + (12/13) * d 1 - (2/13) * d 2)^2 := by
    exact sq_nonneg _
  have hsq1 : 0 ≤ (d 1 + (102/77) * d 2)^2 := by
    exact sq_nonneg _
  have hsq2 : 0 ≤ (d 2)^2 := by
    exact sq_nonneg _
  rw [hsum]
  nlinarith [hsq0, hsq1, hsq2]

/-- Quadratic objective expansion around `answer`. -/
lemma num_3_S_E_objective_diff :
  let x := answer
  let A : Matrix (Fin 3) (Fin 3) ℝ := !![13, 12, -2; 12, 17, 6; -2, 6, 12]
  let b : Fin 3 → ℝ := ![-22, -14.5, 13]
  let c : ℝ := 1
  ∀ y : Fin 3 → ℝ,
    (1/2) * (y ⬝ᵥ A *ᵥ y) + (b ⬝ᵥ y) + c =
      ((1/2) * (x ⬝ᵥ A *ᵥ x) + (b ⬝ᵥ x) + c)
      + (A *ᵥ x + b) ⬝ᵥ (y - x)
      + (1/2) * ((y - x) ⬝ᵥ A *ᵥ (y - x)) := by
  classical
  dsimp
  intro y
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Matrix.of_apply]
  ring_nf

/-- The linear term is nonnegative on the box constraints. -/
lemma num_3_S_E_grad_dot_nonneg_on_box :
  let x := answer
  let g : Fin 3 → ℝ := ![-1, 0, 2]
  ∀ y : Fin 3 → ℝ, (∀ i : Fin 3, -1 ≤ y i ∧ y i ≤ 1) → 0 ≤ g ⬝ᵥ (y - x) := by
  classical
  dsimp
  intro y hy
  have hy0 : y 0 ≤ 1 := (hy 0).2
  have hy2 : -1 ≤ y 2 := (hy 2).1
  simp [dotProduct, Fin.sum_univ_three, answer]
  nlinarith [hy0, hy2]

/--
\[
\begin{array}{ll}
\text{min}_{x\in\mathbb{R}^3} & (1/2)x^T P x + q^T x + r \\
\text{subject to} & -1 \leq x_i \leq 1, \quad i = 1, 2, 3,
\end{array}
\]

Find an optimal point of the problem above, where
\[
P =
\begin{bmatrix}
13 & 12 & -2 \\
12 & 17 & 6 \\
-2 & 6 & 12
\end{bmatrix}, \quad q =
\begin{bmatrix}
-22.0 \\
-14.5 \\
13.0
\end{bmatrix}, \quad r = 1.
\]
-/
theorem num_3_S_E : let x := answer
  let A : Matrix (Fin 3) (Fin 3) ℝ:= !![13, 12, -2; 12, 17, 6; -2, 6, 12]
  let b : Fin 3 → ℝ := ![-22, -14.5, 13]
  let c := 1
  IsMinOn (fun y => (1 / 2) * (y ⬝ᵥ A *ᵥ y) + (b ⬝ᵥ y) + c) {x | ∀ i : Fin 3, -1 ≤ x i ∧ x i ≤ 1} x
  ∧ ∀ i : Fin 3, -1 ≤ x i ∧ x i ≤ 1:= by
  classical
  simp only [isMinOn_iff, Set.mem_setOf_eq]
  constructor
  · intro y hy
    have hgrad :
        ((!![13, 12, -2; 12, 17, 6; -2, 6, 12] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ answer
            + ![-22, -14.5, 13]) = ![-1, 0, 2] := by
      simpa using num_3_S_E_grad
    have hg0 : 0 ≤ ![-1, 0, 2] ⬝ᵥ (y - answer) :=
      num_3_S_E_grad_dot_nonneg_on_box (y := y) hy
    have hg :
        0 ≤
          ((!![13, 12, -2; 12, 17, 6; -2, 6, 12] : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ answer
              + ![-22, -14.5, 13]) ⬝ᵥ (y - answer) := by
      rw [hgrad]
      exact hg0
    have hq :
        0 ≤
          (y - answer)
            ⬝ᵥ
            ((!![13, 12, -2; 12, 17, 6; -2, 6, 12] :
                Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (y - answer)) := by
      simpa using (num_3_S_E_qform_nonneg (d := y - answer))
    have hq' :
        0 ≤
          (1/2) *
            ((y - answer)
              ⬝ᵥ
              ((!![13, 12, -2; 12, 17, 6; -2, 6, 12] :
                  Matrix (Fin 3) (Fin 3) ℝ) *ᵥ (y - answer))) := by
      nlinarith [hq]
    have hdiff := num_3_S_E_objective_diff (y := y)
    rw [hdiff]
    linarith [hg, hq']
  · intro i
    fin_cases i <;> constructor <;> norm_num [answer]

end

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


/-Show that $A$ is copositive ($\forall x \in \mathbb{R}^n, 0\preceq x$, then$    x^TAx\geq0$) if it can be decomposed as a sum of a positive semidefinite and an elementwise nonnegative
matrix:
\[
A = B + C, \quad B \succeq 0, \quad C_{ij} \geq 0, \quad i,j = 1, \ldots, n. \tag{4.71}
\]


-/
/-- Quadratic form of a sum splits into the sum of quadratic forms. -/
lemma quadForm_add_mulVec (n : ℕ) (B C : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((B + C) *ᵥ x) = x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ (C *ᵥ x) := by
  simp [add_mulVec, dotProduct_add]

/-- Over `ℝ`, a positive semidefinite matrix has nonnegative quadratic form. -/
lemma posSemidef_quadForm_nonneg_real (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.PosSemidef) : ∀ x : Fin n → ℝ, 0 ≤ x ⬝ᵥ (B *ᵥ x) := by
  intro x
  simpa using (hB.2 x)

/-- Entrywise nonnegativity plus a nonnegative vector yields a nonnegative quadratic form. -/
lemma entrywise_nonneg_quadForm_nonneg (n : ℕ) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, 0 ≤ C i j) :
    ∀ x : Fin n → ℝ, x ≥ 0 → 0 ≤ x ⬝ᵥ (C *ᵥ x) := by
  intro x hx
  classical
  have hx' : (0 : Fin n → ℝ) ≤ x := by
    simpa [ge_iff_le] using hx
  have hx_i : ∀ i, 0 ≤ x i := by
    intro i
    simpa using hx' i
  have h_inner : ∀ i, 0 ≤ ∑ j, C i j * x j := by
    intro i
    refine Finset.sum_nonneg ?_
    intro j hj
    exact mul_nonneg (hC i j) (hx_i j)
  have h_outer : ∀ i, 0 ≤ x i * ∑ j, C i j * x j := by
    intro i
    exact mul_nonneg (hx_i i) (h_inner i)
  have h_sum : 0 ≤ ∑ i, x i * ∑ j, C i j * x j := by
    refine Finset.sum_nonneg ?_
    intro i hi
    exact h_outer i
  simpa [dotProduct, mulVec] using h_sum

theorem num_12_P_E (n : ℕ) (A B C: Matrix (Fin n) (Fin n) ℝ)  (h : A = B + C) (hB : B.PosSemidef) (hC : ∀ i j, C i j ≥ 0) : ∀ x , x ≥ 0 → x ⬝ᵥ A *ᵥ x ≥ 0 := by
  intro x hx
  have hB' : 0 ≤ x ⬝ᵥ (B *ᵥ x) := posSemidef_quadForm_nonneg_real n B hB x
  have hC' : 0 ≤ x ⬝ᵥ (C *ᵥ x) := entrywise_nonneg_quadForm_nonneg n C hC x hx
  have hsum : 0 ≤ x ⬝ᵥ ((B + C) *ᵥ x) := by
    have hsplit : x ⬝ᵥ ((B + C) *ᵥ x) =
        x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ (C *ᵥ x) := quadForm_add_mulVec n B C x
    have hnonneg : 0 ≤ x ⬝ᵥ (B *ᵥ x) + x ⬝ᵥ (C *ᵥ x) := add_nonneg hB' hC'
    simpa [hsplit] using hnonneg
  have hA : 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    simpa [h] using hsum
  simpa [ge_iff_le] using hA

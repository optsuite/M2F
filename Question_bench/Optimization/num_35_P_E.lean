import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace Filter

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


/-Consider the problem of minimizing a quadratic function:
\[
\text{minimize} \quad f(x) = \frac{1}{2}x^T P x + q^T x + r,
\]
where \( P \in \mathbf{S}^n \) (but we do not assume \( P \succeq 0 \)).

Show that if \( P  \not\succeq 0 \), i.e., the objective function \( f \) is not convex, then the problem is unbounded
below.


-/
/-- From a non-positive-semidefinite symmetric matrix, extract a direction with negative quadratic form. -/
lemma exists_quadForm_neg_of_isSymm_not_PosSemidef {n : ℕ}
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.IsSymm) (hPn : ¬ P.PosSemidef) :
    ∃ v : Fin n → ℝ, (v ⬝ᵥ (P *ᵥ v)) < 0 := by
  classical
  have hHerm : P.IsHermitian := by
    -- Over `ℝ`, Hermitian equals symmetric.
    simpa [Matrix.IsHermitian, Matrix.IsSymm, conjTranspose_eq_transpose_of_trivial] using hP
  have hNot : ¬ ∀ v : Fin n → ℝ, 0 ≤ star v ⬝ᵥ (P *ᵥ v) := by
    intro hforall
    exact hPn ⟨hHerm, hforall⟩
  rcases not_forall.mp hNot with ⟨v, hv⟩
  have hv' : ¬ 0 ≤ v ⬝ᵥ (P *ᵥ v) := by simpa using hv
  exact ⟨v, lt_of_not_ge hv'⟩

/-- Dot product with a scalar multiple on the right over `ℝ`. -/
lemma dotProduct_smul_right_real {n : ℕ} (q v : Fin n → ℝ) (t : ℝ) :
    q ⬝ᵥ (t • v) = t * (q ⬝ᵥ v) := by
  simp [dotProduct_smul, smul_eq_mul]

/-- Quadratic form scales by `t^2` along a ray. -/
lemma quadForm_smul {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (t : ℝ) :
    (t • v) ⬝ᵥ (P *ᵥ (t • v)) = (t^2) * (v ⬝ᵥ (P *ᵥ v)) := by
  calc
    (t • v) ⬝ᵥ (P *ᵥ (t • v))
        = (t • v) ⬝ᵥ (t • (P *ᵥ v)) := by simp [mulVec_smul]
    _ = t • ((t • v) ⬝ᵥ (P *ᵥ v)) := by simp [dotProduct_smul]
    _ = t • (t • (v ⬝ᵥ (P *ᵥ v))) := by simp [smul_dotProduct]
    _ = (t * t) • (v ⬝ᵥ (P *ᵥ v)) := by
        exact smul_smul t t (v ⬝ᵥ (P *ᵥ v))
    _ = (t * t) * (v ⬝ᵥ (P *ᵥ v)) := by simp [smul_eq_mul]
    _ = (t^2) * (v ⬝ᵥ (P *ᵥ v)) := by simp [pow_two, mul_assoc]

/-- A real quadratic with negative leading coefficient is unbounded below. -/
lemma exists_lt_quadratic_of_neg_lead {a b c : ℝ} (ha : a < 0) (M : ℝ) :
    ∃ t : ℝ, a * t^2 + b * t + c < M := by
  have h : Tendsto (fun x : ℝ => (a * x + b) * x + c) atTop atBot :=
    tendsto_atBot_add_const_right _ c <|
      (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
        tendsto_id
  rcases (h.eventually_lt_atBot M).exists with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  have ht' : (a * t + b) * t + c = a * t^2 + b * t + c := by ring
  simpa [ht'] using ht

theorem num_35_P_E (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (r : ℝ) (hP : P.IsSymm) (hPn : ¬ P.PosSemidef) : ∀ M : ℝ, ∃ x , M > 1/2 * x ⬝ᵥ P *ᵥ x + q ⬝ᵥ x + r := by
  intro M
  obtain ⟨v, hvneg⟩ := exists_quadForm_neg_of_isSymm_not_PosSemidef hP hPn
  set a : ℝ := (1 / 2) * (v ⬝ᵥ (P *ᵥ v))
  set b : ℝ := q ⬝ᵥ v
  have ha : a < 0 := by
    have hhalf : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
    dsimp [a]
    nlinarith [hvneg, hhalf]
  obtain ⟨t, ht⟩ := exists_lt_quadratic_of_neg_lead (a := a) (b := b) (c := r) ha M
  refine ⟨t • v, ?_⟩
  have hquad : (t • v) ⬝ᵥ (P *ᵥ (t • v)) = (t^2) * (v ⬝ᵥ (P *ᵥ v)) :=
    quadForm_smul (P := P) (v := v) (t := t)
  have hlin : q ⬝ᵥ (t • v) = t * (q ⬝ᵥ v) :=
    dotProduct_smul_right_real (q := q) (v := v) (t := t)
  have hrewrite :
      (1 / 2) * ((t • v) ⬝ᵥ (P *ᵥ (t • v))) + (q ⬝ᵥ (t • v)) + r
        = a * t^2 + b * t + r := by
    calc
      (1 / 2) * ((t • v) ⬝ᵥ (P *ᵥ (t • v))) + (q ⬝ᵥ (t • v)) + r
          = (1 / 2) * ((t^2) * (v ⬝ᵥ (P *ᵥ v))) + t * (q ⬝ᵥ v) + r := by
              simp [hquad, hlin]
      _ = a * t^2 + b * t + r := by
              dsimp [a, b]
              ring
  have ht' :
      (1 / 2) * ((t • v) ⬝ᵥ (P *ᵥ (t • v))) + (q ⬝ᵥ (t • v)) + r < M := by
    calc
      (1 / 2) * ((t • v) ⬝ᵥ (P *ᵥ (t • v))) + (q ⬝ᵥ (t • v)) + r
          = a * t^2 + b * t + r := hrewrite
      _ < M := ht
  exact ht'

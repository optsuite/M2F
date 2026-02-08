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


/-Minimizing a linear function over an ellipsoid centered at the origin.
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & x^T A x \leq 1,
\end{array}
\]
where \( A \in \mathbb{S}_{++}^n \) and \( c \neq 0 \)


-/
noncomputable section

variable (n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (h : A.PosDef) (hc : c ≠ 0)

def answer (n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (h : A.PosDef) (hc : c ≠ 0) : Fin n → ℝ  :=
-((Real.sqrt (c ⬝ᵥ (A⁻¹ *ᵥ c)))⁻¹ • (A⁻¹ *ᵥ c))

/-- Multiplying by the inverse matrix recovers the vector. -/
lemma mulVec_inv_mulVec (h : A.PosDef) : A *ᵥ (A⁻¹ *ᵥ c) = c := by
  classical
  letI := (Matrix.PosDef.isUnit h).invertible
  calc
    A *ᵥ (A⁻¹ *ᵥ c) = (A * A⁻¹) *ᵥ c := by
      simp [mulVec_mulVec]
    _ = c := by
      simp

/-- Dot product identity for the inverse action. -/
lemma inv_dot_mulVec (h : A.PosDef) (y : Fin n → ℝ) : (A⁻¹ *ᵥ c) ⬝ᵥ (A *ᵥ y) = c ⬝ᵥ y := by
  classical
  have hA : Aᵀ = A := by
    simpa using (Matrix.PosDef.isHermitian h).eq
  let u := A⁻¹ *ᵥ c
  have htrans : u ᵥ* A = Aᵀ *ᵥ u := by
    simpa using (mulVec_transpose (A:=A) (x:=u)).symm
  calc
    u ⬝ᵥ (A *ᵥ y) = u ᵥ* A ⬝ᵥ y := by
      simp [dotProduct_mulVec]
    _ = (Aᵀ *ᵥ u) ⬝ᵥ y := by
      simp [htrans]
    _ = (A *ᵥ u) ⬝ᵥ y := by
      simpa [hA]
    _ = c ⬝ᵥ y := by
      simp [u, mulVec_inv_mulVec (n:=n) (c:=c) (A:=A) h]

/-- Positivity of `t = c ⬝ᵥ (A⁻¹ *ᵥ c)` for `c ≠ 0`. -/
lemma t_pos (h : A.PosDef) (hc : c ≠ 0) : let t := c ⬝ᵥ (A⁻¹ *ᵥ c); 0 < t := by
  classical
  let t := c ⬝ᵥ (A⁻¹ *ᵥ c)
  have hInv : (A⁻¹).PosDef := Matrix.PosDef.inv (hM := h)
  have ht : 0 < c ⬝ᵥ (A⁻¹ *ᵥ c) := by
    simpa using hInv.2 c hc
  simpa [t] using ht

/-- For positive `t`, `t * (Real.sqrt t)⁻¹ = Real.sqrt t`. -/
lemma sqrt_mul_inv {t : ℝ} (ht : 0 < t) : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
  have hne : (Real.sqrt t) ≠ 0 := (Real.sqrt_ne_zero').2 ht
  field_simp [hne]
  simp [Real.sq_sqrt (le_of_lt ht)]

/-- For positive `t`, `((Real.sqrt t)⁻¹)^2 * t = 1`. -/
lemma inv_sqrt_sq_mul {t : ℝ} (ht : 0 < t) : (Real.sqrt t)⁻¹ ^ 2 * t = 1 := by
  have hne : (Real.sqrt t) ≠ 0 := (Real.sqrt_ne_zero').2 ht
  calc
    (Real.sqrt t)⁻¹ ^ 2 * t = (Real.sqrt t)⁻¹ * (Real.sqrt t)⁻¹ * t := by
      simp [pow_two, mul_assoc]
    _ = (Real.sqrt t)⁻¹ * (t * (Real.sqrt t)⁻¹) := by
      simp [mul_assoc, mul_left_comm, mul_comm]
    _ = (Real.sqrt t)⁻¹ * (Real.sqrt t) := by
      simp [sqrt_mul_inv (t:=t) ht]
    _ = 1 := by
      simp [hne]

/-- The proposed answer lies on the boundary of the ellipsoid. -/
lemma answer_feasible_eq_one : let x := answer n c A h hc; x ⬝ᵥ (A *ᵥ x) = 1 := by
  classical
  let t := c ⬝ᵥ (A⁻¹ *ᵥ c)
  let u := A⁻¹ *ᵥ c
  let a : ℝ := (Real.sqrt t)⁻¹
  let b : ℝ := -a
  let x := answer n c A h hc
  have ht : 0 < t := by
    simpa [t] using (t_pos (n:=n) (c:=c) (A:=A) h hc)
  have hx : x = b • u := by
    simp [x, answer, a, b, t, u]
  have hAu : A *ᵥ u = c := by
    simpa [u] using (mulVec_inv_mulVec (n:=n) (c:=c) (A:=A) h)
  calc
    x ⬝ᵥ (A *ᵥ x) = b * b * (u ⬝ᵥ (A *ᵥ u)) := by
      calc
        x ⬝ᵥ (A *ᵥ x) = (b • u) ⬝ᵥ (A *ᵥ (b • u)) := by
          rw [hx]
        _ = (b • u) ⬝ᵥ (b • (A *ᵥ u)) := by
          simp [mulVec_smul]
        _ = b * b * (u ⬝ᵥ (A *ᵥ u)) := by
          calc
            (b • u) ⬝ᵥ (b • (A *ᵥ u)) =
                b * (u ⬝ᵥ (b • (A *ᵥ u))) := by
                  simp [smul_dotProduct]
            _ = b * (b * (u ⬝ᵥ (A *ᵥ u))) := by
                  rw [dotProduct_smul]
                  simp [smul_eq_mul]
            _ = b * b * (u ⬝ᵥ (A *ᵥ u)) := by
                  ring
    _ = a ^ 2 * t := by
      simp [b, pow_two, t, u, hAu, dotProduct_comm, mul_assoc, mul_left_comm, mul_comm]
    _ = 1 := by
      simpa [a] using inv_sqrt_sq_mul (t:=t) ht

/-- Objective value at the proposed answer. -/
lemma answer_objective :
    let t := c ⬝ᵥ (A⁻¹ *ᵥ c); let x := answer n c A h hc; c ⬝ᵥ x = -Real.sqrt t := by
  classical
  let t := c ⬝ᵥ (A⁻¹ *ᵥ c)
  let u := A⁻¹ *ᵥ c
  let a : ℝ := (Real.sqrt t)⁻¹
  let b : ℝ := -a
  let x := answer n c A h hc
  have ht : 0 < t := by
    simpa [t] using (t_pos (n:=n) (c:=c) (A:=A) h hc)
  have hx : x = b • u := by
    simp [x, answer, a, b, t, u]
  calc
    c ⬝ᵥ x = b * (c ⬝ᵥ u) := by
      simp [hx, dotProduct_smul, mul_assoc, mul_left_comm, mul_comm]
    _ = -Real.sqrt t := by
      have hmul : (c ⬝ᵥ u) * (Real.sqrt t)⁻¹ = Real.sqrt t := by
        simpa [t, u, mul_comm] using (sqrt_mul_inv (t:=t) ht)
      calc
        b * (c ⬝ᵥ u) = -((c ⬝ᵥ u) * a) := by
          ring
        _ = -Real.sqrt t := by
          simp [a, hmul, mul_comm]

/-- A Cauchy–Schwarz type inequality for the quadratic form induced by `A`. -/
lemma generalized_cauchy_schwarz (h : A.PosDef) :
    let t := c ⬝ᵥ (A⁻¹ *ᵥ c); ∀ y : Fin n → ℝ,
      (c ⬝ᵥ y) ^ 2 ≤ (y ⬝ᵥ (A *ᵥ y)) * t := by
  classical
  intro t y
  let u := A⁻¹ *ᵥ c
  letI := Matrix.toSeminormedAddCommGroup A (Matrix.PosDef.posSemidef h)
  letI := Matrix.toInnerProductSpace A (Matrix.PosDef.posSemidef h)
  have hcs :=
    (real_inner_mul_inner_self_le (x:=u) (y:=y) :
      ⟪u, y⟫_ℝ * ⟪u, y⟫_ℝ ≤ ⟪u, u⟫_ℝ * ⟪y, y⟫_ℝ)
  change ((A *ᵥ y) ⬝ᵥ u) * ((A *ᵥ y) ⬝ᵥ u) ≤
      ((A *ᵥ u) ⬝ᵥ u) * ((A *ᵥ y) ⬝ᵥ y) at hcs
  have hs1 : (A *ᵥ y) ⬝ᵥ u = c ⬝ᵥ y := by
    simpa [u, dotProduct_comm] using (inv_dot_mulVec (n:=n) (c:=c) (A:=A) h y)
  have hs2 : (A *ᵥ u) ⬝ᵥ u = t := by
    simpa [u, t, dotProduct_comm] using congrArg (fun v => v ⬝ᵥ u)
      (mulVec_inv_mulVec (n:=n) (c:=c) (A:=A) h)
  have hcs' :
      (c ⬝ᵥ y) * (c ⬝ᵥ y) ≤ (y ⬝ᵥ (A *ᵥ y)) * t := by
    simpa [hs1, hs2, dotProduct_comm, mul_comm, mul_left_comm, mul_assoc] using hcs
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hcs'

/-- Lower bound on the objective over the feasible set. -/
lemma lower_bound_on_feasible (h : A.PosDef) (hc : c ≠ 0) :
    let t := c ⬝ᵥ (A⁻¹ *ᵥ c); ∀ y, y ⬝ᵥ (A *ᵥ y) ≤ 1 → -Real.sqrt t ≤ c ⬝ᵥ y := by
  classical
  intro t y hy
  have ht : 0 < t := by
    simpa [t] using (t_pos (n:=n) (c:=c) (A:=A) h hc)
  have hcs : (c ⬝ᵥ y) ^ 2 ≤ (y ⬝ᵥ (A *ᵥ y)) * t := by
    simpa [t] using (generalized_cauchy_schwarz (n:=n) (c:=c) (A:=A) h y)
  have hcs' : (c ⬝ᵥ y) ^ 2 ≤ t := by
    have ht0 : 0 ≤ t := le_of_lt ht
    have hmul : (y ⬝ᵥ (A *ᵥ y)) * t ≤ 1 * t := by
      exact mul_le_mul_of_nonneg_right hy ht0
    exact le_trans hcs (by simpa using hmul)
  exact Real.neg_sqrt_le_of_sq_le hcs'

theorem num_8_S_H : let x := answer n c A h hc
  IsMinOn (fun y => c ⬝ᵥ y) {x | x ⬝ᵥ (A *ᵥ x) ≤ 1} x ∧ (x ⬝ᵥ A *ᵥ x) ≤ 1:= by
  classical
  dsimp
  set x := answer n c A h hc
  refine And.intro ?hmin ?hfeas
  · simp [IsMinOn, IsMinFilter]
    intro y hy
    let t := c ⬝ᵥ (A⁻¹ *ᵥ c)
    have hobj : c ⬝ᵥ x = -Real.sqrt t := by
      simpa [x, t] using (answer_objective (n:=n) (c:=c) (A:=A) (h:=h) (hc:=hc))
    have hbound : -Real.sqrt t ≤ c ⬝ᵥ y := by
      simpa [t] using (lower_bound_on_feasible (n:=n) (c:=c) (A:=A) h hc y hy)
    simpa [hobj] using hbound
  ·
    have hfeas : x ⬝ᵥ (A *ᵥ x) = 1 := by
      simpa [x] using (answer_feasible_eq_one (n:=n) (c:=c) (A:=A) (h:=h) (hc:=hc))
    exact le_of_eq hfeas

end

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
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ),
    ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp

/-- For real Hermitian matrices, left and right multiplication by a vector coincide. -/
lemma vecMul_eq_mulVec_of_isHermitian_real {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (s : Fin n → ℝ) : s ᵥ* B = B *ᵥ s := by
  have hBt : B.transpose = B := by
    simpa [conjTranspose_eq_transpose_of_trivial] using hB.eq
  calc
    s ᵥ* B = B.transpose.mulVec s := by
      simpa using (Matrix.mulVec_transpose (A := B) (x := s)).symm
    _ = B *ᵥ s := by
      simp [hBt]

/-- Trace of the BFGS middle term for a real Hermitian matrix. -/
lemma trace_B_mul_vecMulVec_mul_B_of_isHermitian {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.IsHermitian) (s : Fin n → ℝ) :
    (B * vecMulVec s s * B).trace = (B *ᵥ s) ⬝ᵥ (B *ᵥ s) := by
  calc
    (B * vecMulVec s s * B).trace
        = ((Matrix.vecMulVec (B *ᵥ s) s) * B).trace := by
            simp [Matrix.mul_vecMulVec]
    _ = (Matrix.vecMulVec (B *ᵥ s) (s ᵥ* B)).trace := by
            simpa using
              congrArg Matrix.trace
                (Matrix.vecMulVec_mul (x := B *ᵥ s) (y := s) (M := B))
    _ = (B *ᵥ s) ⬝ᵥ (s ᵥ* B) := by
            simp
    _ = (B *ᵥ s) ⬝ᵥ (B *ᵥ s) := by
            simp [vecMul_eq_mulVec_of_isHermitian_real (B := B) hB]

/--
Consider the BFGS formula: \(B_{k+1} = B_k - \frac{B_k s_k s_k^\top B_k}{s_k^\top B_k s_k} +
\frac{ y_k y_k^\top} {y_k^\top s_k}\), where $B_k$ is symmetric. Prove that \(\mbox{trace}(B_{k+1})
= \mbox{trace}(B_{k}) - \frac{\|B_ks_k\|_2^2}{s_k^\top B_k s_k} + \frac{\|y_k\|_2^2}{y_k^\top s_k}\)
-/
theorem num_44_P_E (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (symmB : B.IsHermitian)
  (y s : Fin n → ℝ) (eq : A = B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B +
  (1 / s ⬝ᵥ y) • vecMulVec y y) :
  A.trace = B.trace - (B *ᵥ s) ⬝ᵥ (B *ᵥ s) / (s ⬝ᵥ B *ᵥ s) + y ⬝ᵥ y / (y ⬝ᵥ s) := by
  rw [eq]
  have hys : s ⬝ᵥ y = y ⬝ᵥ s := by
    simpa using (dotProduct_comm s y)
  simp [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul,
    hys, trace_B_mul_vecMulVec_mul_B_of_isHermitian (B := B) symmB,
    Matrix.trace_vecMulVec, div_eq_mul_inv, mul_comm]

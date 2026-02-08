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


/-Prove that \(\det(I+xy^\top + u v^\top) = (1+y^\top x) (1+v^\top u) - (x^\top v) (y^\top u)\).

-/
/-- The `n × 2` matrix with columns `x` and `u`. -/
abbrev num_41_P_E_cols2 (n : ℕ) (x u : Fin n → ℝ) : Matrix (Fin n) (Fin 2) ℝ :=
  fun i j => if j = 0 then x i else u i

/-- The `2 × n` matrix with rows `y` and `v`. -/
abbrev num_41_P_E_rows2 (n : ℕ) (y v : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  fun i j => if i = 0 then y j else v j

/-- Multiplying the column/row matrices gives the rank-two update. -/
lemma num_41_P_E_cols2_mul_rows2 (n : ℕ) (x y u v : Fin n → ℝ) :
    num_41_P_E_cols2 n x u * num_41_P_E_rows2 n y v = vecMulVec x y + vecMulVec u v := by
  ext i j
  simp [Matrix.mul_apply, num_41_P_E_cols2, num_41_P_E_rows2, Fin.sum_univ_two, vecMulVec]

/-- Determinant of `1 + B*A` for the 2×n and n×2 matrices. -/
lemma num_41_P_E_det_one_add_rows2_mul_cols2 (n : ℕ) (x y u v : Fin n → ℝ) :
    det (1 + num_41_P_E_rows2 n y v * num_41_P_E_cols2 n x u)
      = (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct x v) * (dotProduct y u) := by
  classical
  let A := num_41_P_E_cols2 n x u
  let B := num_41_P_E_rows2 n y v
  have h00 : (B * A) 0 0 = dotProduct y x := by
    simp [A, B, Matrix.mul_apply, num_41_P_E_rows2, num_41_P_E_cols2, dotProduct]
  have h01 : (B * A) 0 1 = dotProduct y u := by
    simp [A, B, Matrix.mul_apply, num_41_P_E_rows2, num_41_P_E_cols2, dotProduct]
  have h10 : (B * A) 1 0 = dotProduct v x := by
    simp [A, B, Matrix.mul_apply, num_41_P_E_rows2, num_41_P_E_cols2, dotProduct]
  have h11 : (B * A) 1 1 = dotProduct v u := by
    simp [A, B, Matrix.mul_apply, num_41_P_E_rows2, num_41_P_E_cols2, dotProduct]
  have hdet :
      det (1 + B * A) =
        (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct y u) * (dotProduct v x) := by
    simp [Matrix.det_fin_two, h00, h01, h10, h11, A, B]
  have hvx : dotProduct v x = dotProduct x v := by
    simpa using (dotProduct_comm (v:=v) (w:=x))
  have hmul : (dotProduct y u) * (dotProduct x v) = (dotProduct x v) * (dotProduct y u) := by
    ac_rfl
  calc
    det (1 + B * A) =
        (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct y u) * (dotProduct v x) := hdet
    _ =
        (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct y u) * (dotProduct x v) := by
          simp [hvx]
    _ =
        (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct x v) * (dotProduct y u) := by
          simp [hmul]

theorem num_41_P_E (n : ℕ) (x y u v : Fin n → ℝ) : det (1 + vecMulVec x y + vecMulVec u v) = (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct x v) * (dotProduct y u) := by
  classical
  let A := num_41_P_E_cols2 n x u
  let B := num_41_P_E_rows2 n y v
  have hAB : A * B = vecMulVec x y + vecMulVec u v := by
    simpa [A, B] using num_41_P_E_cols2_mul_rows2 (n:=n) (x:=x) (y:=y) (u:=u) (v:=v)
  calc
    det (1 + vecMulVec x y + vecMulVec u v)
        = det (1 + (vecMulVec x y + vecMulVec u v)) := by
            simp [add_assoc]
    _ = det (1 + A * B) := by
            simp [hAB]
    _ = det (1 + B * A) := by
            simpa using (Matrix.det_one_add_mul_comm A B)
    _ = (1 + dotProduct y x) * (1 + dotProduct v u) - (dotProduct x v) * (dotProduct y u) := by
            simpa [A, B] using
              num_41_P_E_det_one_add_rows2_mul_cols2 (n:=n) (x:=x) (y:=y) (u:=u) (v:=v)

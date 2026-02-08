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


/-Consider the linear programming
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & A x \preceq b
\end{array}
\]
with $A$ square and nonsingular. Find its optimal point if $A^{-T} c \preceq 0$

-/
noncomputable section

variable (n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (h : A.det ≠ 0 ∧ A⁻¹ᵀ *ᵥ c ≤
0)

def answer (n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (h : A.det ≠ 0 ∧ A⁻¹ᵀ *ᵥ c ≤ 0): Fin n → ℝ  :=
  A⁻¹ *ᵥ b

/-- Multiplying by a nonsingular matrix and its inverse recovers the vector. -/
lemma num_6_S_H_mulVec_answer (hdet : A.det ≠ 0) :
    A *ᵥ (A⁻¹ *ᵥ b) = b := by
  classical
  have hunit : IsUnit A.det := (isUnit_iff_ne_zero).2 hdet
  calc
    A *ᵥ (A⁻¹ *ᵥ b) = (A * A⁻¹) *ᵥ b := by
      simpa using (Matrix.mulVec_mulVec b A A⁻¹)
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ b := by
      simp [Matrix.mul_nonsing_inv A hunit]
    _ = b := by
      simpa using (Matrix.one_mulVec b)

/-- The transpose cancels the transposed inverse when `det A ≠ 0`. -/
lemma num_6_S_H_mulVec_transpose_invTranspose (hdet : A.det ≠ 0) :
    Aᵀ *ᵥ (A⁻¹ᵀ *ᵥ c) = c := by
  classical
  have hunit : IsUnit A.det := (isUnit_iff_ne_zero).2 hdet
  have hmul : A⁻¹ * A = (1 : Matrix (Fin n) (Fin n) ℝ) := Matrix.nonsing_inv_mul A hunit
  have hmulT : Aᵀ * A⁻¹ᵀ = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    simpa [transpose_mul] using congrArg Matrix.transpose hmul
  calc
    Aᵀ *ᵥ (A⁻¹ᵀ *ᵥ c) = (Aᵀ * A⁻¹ᵀ) *ᵥ c := by
      simpa using (Matrix.mulVec_mulVec c Aᵀ A⁻¹ᵀ)
    _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ c := by
      simp [hmulT]
    _ = c := by
      simpa using (Matrix.one_mulVec c)

/-- A nonpositive left vector makes dot product antitone. -/
lemma dotProduct_antitone_of_nonpos_left {d u v : Fin n → ℝ} (hd : d ≤ 0) (huv : u ≤ v) :
    d ⬝ᵥ v ≤ d ⬝ᵥ u := by
  have hd' : 0 ≤ -d := by
    intro i
    exact (neg_nonneg.mpr (hd i))
  have hneg : (-d) ⬝ᵥ u ≤ (-d) ⬝ᵥ v :=
    dotProduct_le_dotProduct_of_nonneg_left (u:=u) (v:=v) (w:=-d) huv hd'
  have hneg' : -(d ⬝ᵥ u) ≤ -(d ⬝ᵥ v) := by
    simpa using hneg
  exact (neg_le_neg_iff.mp hneg')

/-- Rewrite the objective using the transposed inverse. -/
lemma num_6_S_H_objective_rewrite (hdet : A.det ≠ 0) (y : Fin n → ℝ) :
    (A⁻¹ᵀ *ᵥ c) ⬝ᵥ (A *ᵥ y) = c ⬝ᵥ y := by
  classical
  calc
    (A⁻¹ᵀ *ᵥ c) ⬝ᵥ (A *ᵥ y) = (A⁻¹ᵀ *ᵥ c) ᵥ* A ⬝ᵥ y := by
      simpa using (Matrix.dotProduct_mulVec (A⁻¹ᵀ *ᵥ c) A y)
    _ = (Aᵀ *ᵥ (A⁻¹ᵀ *ᵥ c)) ⬝ᵥ y := by
      simpa [Matrix.mulVec_transpose]
    _ = c ⬝ᵥ y := by
      simpa [num_6_S_H_mulVec_transpose_invTranspose (n:=n) (c:=c) (A:=A) hdet]

/-- Objective value at the proposed point expressed via the transposed inverse. -/
lemma num_6_S_H_objective_at_answer :
    c ⬝ᵥ (A⁻¹ *ᵥ b) = (A⁻¹ᵀ *ᵥ c) ⬝ᵥ b := by
  classical
  calc
    c ⬝ᵥ (A⁻¹ *ᵥ b) = (c ᵥ* A⁻¹) ⬝ᵥ b := by
      simpa using (Matrix.dotProduct_mulVec c A⁻¹ b)
    _ = (A⁻¹ᵀ *ᵥ c) ⬝ᵥ b := by
      simpa [Matrix.mulVec_transpose]

theorem num_6_S_H : let x := answer n c A b h
  IsMinOn (fun y => c ⬝ᵥ y) {x | A *ᵥ x ≤ b} x ∧ A *ᵥ x ≤ b:= by
  classical
  dsimp [answer]
  constructor
  · apply (isMinOn_iff).2
    intro y hy
    set d : Fin n → ℝ := A⁻¹ᵀ *ᵥ c
    have hd : d ≤ 0 := by
      simpa [d] using h.2
    calc
      c ⬝ᵥ (A⁻¹ *ᵥ b) = d ⬝ᵥ b := by
        simpa [d] using (num_6_S_H_objective_at_answer (n:=n) (c:=c) (A:=A) (b:=b))
      _ ≤ d ⬝ᵥ (A *ᵥ y) := by
        simpa using
          (dotProduct_antitone_of_nonpos_left (n:=n) (d:=d) (u:=A *ᵥ y) (v:=b) hd hy)
      _ = c ⬝ᵥ y := by
        simpa [d] using (num_6_S_H_objective_rewrite (n:=n) (c:=c) (A:=A) (y:=y) h.1)
  · exact le_of_eq (num_6_S_H_mulVec_answer (n:=n) (A:=A) (b:=b) h.1)

end

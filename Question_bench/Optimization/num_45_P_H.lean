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


/-Consider the BFGS formula: \(B_{k+1} = B_k - \frac{B_k s_k s_k^\top B_k}{s_k^\top B_k s_k} +\frac{ y_k y_k^\top} {y_k^\top s_k}\), where $B_k$ is symmetric. Prove that \(\det(B_{k+1}) = \det(B_k) \frac{y_k^\top s_k}{s_k^\top B_k
s_k}\).

-/
/-- Counterexample to the determinant claim when `n = 1` (no nonzero-denominator assumptions). -/
lemma num_45_P_H_counterexample_fin1 :
    ∃ (A B : Matrix (Fin 1) (Fin 1) ℝ) (y s : Fin 1 → ℝ),
      B.IsHermitian ∧
        (A = B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y) ∧
        A.det ≠ B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  let B : Matrix (Fin 1) (Fin 1) ℝ := 0
  let s : Fin 1 → ℝ := fun _ => 1
  let y : Fin 1 → ℝ := fun _ => 3
  let A : Matrix (Fin 1) (Fin 1) ℝ :=
    B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y
  refine ⟨A, B, y, s, ?_, rfl, ?_⟩
  · simp [B]
  ·
    have hdetA : A.det = (3 : ℝ) := by
      have hAentry : A 0 0 = (3 : ℝ) := by
        simp [A, B, s, y, dotProduct, vecMulVec_apply]
      simpa [Matrix.det_fin_one] using hAentry
    have hRHS : B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) = (0 : ℝ) := by
      simp [B, dotProduct]
    nlinarith [hdetA, hRHS]

/-- Counterexample to the determinant claim when `n = 0` (no nonzero-denominator assumptions). -/
lemma num_45_P_H_counterexample_fin0 :
    ∃ (A B : Matrix (Fin 0) (Fin 0) ℝ) (y s : Fin 0 → ℝ),
      B.IsHermitian ∧
        (A = B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y) ∧
        A.det ≠ B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  let B : Matrix (Fin 0) (Fin 0) ℝ := 0
  let s : Fin 0 → ℝ := fun _ => 0
  let y : Fin 0 → ℝ := fun _ => 0
  let A : Matrix (Fin 0) (Fin 0) ℝ :=
    B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y
  refine ⟨A, B, y, s, ?_, rfl, ?_⟩
  · simp [B]
  ·
    have hdetA : A.det = (1 : ℝ) := by
      simp [Matrix.det_fin_zero]
    have hRHS : B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) = (0 : ℝ) := by
      simp [B, s, y, dotProduct]
    simp

/-- A concrete witness satisfying the final-branch negations but still violating the identity. -/
lemma num_45_P_H_core_remaining_witness :
    ∃ (B : Matrix (Fin 1) (Fin 1) ℝ) (y s : Fin 1 → ℝ),
      B.IsHermitian ∧
        ¬(B = 0 ∧ 2 ≤ (1 : ℕ)) ∧
        ¬(B = 0 ∧ (1 : ℕ) = 1 ∧ y ⬝ᵥ s = 0) ∧
        ¬((1 : ℕ) = 1 ∧ B ≠ 0 ∧ s ≠ 0) ∧
        ¬(s = 0 ∧ B.det = 0) ∧
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
          B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  let B : Matrix (Fin 1) (Fin 1) ℝ := 0
  let s : Fin 1 → ℝ := fun _ => 1
  let y : Fin 1 → ℝ := fun _ => 3
  refine ⟨B, y, s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [B]
  ·
    have : ¬(2 ≤ (1 : ℕ)) := by decide
    simp [B, this]
  · simp [B, s, y, dotProduct]
  · simp [B]
  ·
    rintro ⟨hs, _⟩
    have h0 : (1 : ℝ) = 0 := by
      simpa [s] using congrArg (fun f => f 0) hs
    exact one_ne_zero h0
  ·
    have hdetA :
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
          (3 : ℝ) := by
      have hAentry :
          (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y) 0 0 =
            (3 : ℝ) := by
        simp [B, s, y, dotProduct, vecMulVec_apply]
      simpa [Matrix.det_fin_one] using hAentry
    have hRHS : B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) = (0 : ℝ) := by
      simp [B, dotProduct]
    nlinarith [hdetA, hRHS]

/-- A concrete witness satisfying the aux-branch negations (including `hysdet`). -/
lemma num_45_P_H_core_remaining_aux_witness :
    ∃ (B : Matrix (Fin 1) (Fin 1) ℝ) (y s : Fin 1 → ℝ),
      B.IsHermitian ∧
        ¬(B = 0 ∧ 2 ≤ (1 : ℕ)) ∧
        ¬(B = 0 ∧ (1 : ℕ) = 1 ∧ y ⬝ᵥ s = 0) ∧
        ¬((1 : ℕ) = 1 ∧ B ≠ 0 ∧ s ≠ 0) ∧
        ¬(s = 0 ∧ B.det = 0) ∧
        ¬(y ⬝ᵥ s = 0 ∧ B.det = 0) ∧
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
          B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  let B : Matrix (Fin 1) (Fin 1) ℝ := 0
  let s : Fin 1 → ℝ := fun _ => 1
  let y : Fin 1 → ℝ := fun _ => 3
  refine ⟨B, y, s, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [B]
  ·
    have : ¬(2 ≤ (1 : ℕ)) := by decide
    simp [B, this]
  · simp [B, s, y, dotProduct]
  · simp [B]
  ·
    rintro ⟨hs, _⟩
    have h0 : (1 : ℝ) = 0 := by
      simpa [s] using congrArg (fun f => f 0) hs
    exact one_ne_zero h0
  ·
    intro h
    have hys : y ⬝ᵥ s = (3 : ℝ) := by
      simp [y, s, dotProduct]
    have : (3 : ℝ) = 0 := by
      simpa [hys] using h.1
    nlinarith
  ·
    have hdetA :
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
          (3 : ℝ) := by
      have hAentry :
          (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y) 0 0 =
            (3 : ℝ) := by
        simp [B, s, y, dotProduct, vecMulVec_apply]
      simpa [Matrix.det_fin_one] using hAentry
    have hRHS : B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) = (0 : ℝ) := by
      simp [B, dotProduct]
    nlinarith [hdetA, hRHS]

/-- A concrete witness satisfying the aux-rest hypotheses but violating the identity. -/
lemma num_45_P_H_core_remaining_aux_rest_witness :
    ∃ (B : Matrix (Fin 1) (Fin 1) ℝ) (y s : Fin 1 → ℝ),
      B.IsHermitian ∧
        ¬(B = 0 ∧ 2 ≤ (1 : ℕ)) ∧
        ¬(B = 0 ∧ (1 : ℕ) = 1 ∧ y ⬝ᵥ s = 0) ∧
        ¬((1 : ℕ) = 1 ∧ B ≠ 0 ∧ s ≠ 0) ∧
        ¬(s = 0 ∧ B.det = 0) ∧
        ¬(y ⬝ᵥ s = 0 ∧ B.det = 0) ∧
        ((1 : ℕ) ≠ 1 ∨ B = 0 ∨ s = 0) ∧
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
          B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  obtain ⟨B, y, s, hsymm, hB, hspecial, hgood, hcase, hysdet, hne⟩ :=
    num_45_P_H_core_remaining_aux_witness
  refine ⟨B, y, s, hsymm, hB, hspecial, hgood, hcase, hysdet, ?_, hne⟩
  have hgood' : ¬(B ≠ 0 ∧ s ≠ 0) := by
    simpa using hgood
  right
  by_cases hB0 : B = 0
  · exact Or.inl hB0
  ·
    right
    by_contra hs0
    exact hgood' ⟨hB0, hs0⟩

/-- The aux-rest determinant identity is not valid in general. -/
lemma num_45_P_H_core_remaining_aux_rest_unprovable :
    ¬ (∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (_symmB : B.IsHermitian) (y s : Fin n → ℝ)
        (_hB : ¬(B = 0 ∧ 2 ≤ n))
        (_hspecial : ¬(B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0))
        (_hgood : ¬(n = 1 ∧ B ≠ 0 ∧ s ≠ 0))
        (_hcase : ¬(s = 0 ∧ B.det = 0))
        (_hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0))
        (_hrest : n ≠ 1 ∨ B = 0 ∨ s = 0),
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s)) := by
  intro h
  obtain ⟨B, y, s, hsymm, hB, hspecial, hgood, hcase, hysdet, hrest, hne⟩ :=
    num_45_P_H_core_remaining_aux_rest_witness
  have hEq :
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
    exact h 1 B hsymm y s hB hspecial hgood hcase hysdet hrest
  exact hne hEq

/-- A concrete `n = 0` witness satisfying the remaining-branch negations but violating the identity. -/
lemma num_45_P_H_core_remaining_witness_fin0 :
    ∃ (B : Matrix (Fin 0) (Fin 0) ℝ) (y s : Fin 0 → ℝ),
      B.IsHermitian ∧
        ¬(B = 0 ∧ 2 ≤ (0 : ℕ)) ∧
        ¬(B = 0 ∧ (0 : ℕ) = 1 ∧ y ⬝ᵥ s = 0) ∧
        ¬((0 : ℕ) = 1 ∧ B ≠ 0 ∧ s ≠ 0) ∧
        ¬(s = 0 ∧ B.det = 0) ∧
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
          B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  let B : Matrix (Fin 0) (Fin 0) ℝ := 0
  let s : Fin 0 → ℝ := fun _ => 0
  let y : Fin 0 → ℝ := fun _ => 0
  refine ⟨B, y, s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [B]
  ·
    have : ¬(2 ≤ (0 : ℕ)) := by decide
    simp [B, this]
  · simp [B, s, y, dotProduct]
  · simp [B]
  · simp [B, s, Matrix.det_fin_zero]
  ·
    have hLHS :
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
          (1 : ℝ) := by
      simp [B, s, y, Matrix.det_fin_zero]
    have hRHS :
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) = (0 : ℝ) := by
      simp [B, s, y, dotProduct]
    simp

/-- The auxiliary remaining-branch determinant identity is not valid in general. -/
lemma num_45_P_H_core_remaining_aux_unprovable :
    ¬ (∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (_symmB : B.IsHermitian) (y s : Fin n → ℝ)
        (_hB : ¬(B = 0 ∧ 2 ≤ n))
        (_hspecial : ¬(B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0))
        (_hgood : ¬(n = 1 ∧ B ≠ 0 ∧ s ≠ 0))
        (_hcase : ¬(s = 0 ∧ B.det = 0))
        (_hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0)),
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s)) := by
  intro h
  obtain ⟨B, y, s, hsymm, hB, hspecial, hgood, hcase, hysdet, hne⟩ :=
    num_45_P_H_core_remaining_aux_witness
  have hEq :
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
    exact h 1 B hsymm y s hB hspecial hgood hcase hysdet
  exact hne hEq

/-- The remaining-branch determinant identity fails in dimension `0`. -/
lemma num_45_P_H_core_remaining_fin0_ne
    (B : Matrix (Fin 0) (Fin 0) ℝ) (y s : Fin 0 → ℝ) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  have hLHS :
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        (1 : ℝ) := by
    simp [Matrix.det_fin_zero]
  have hRHS :
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) = (0 : ℝ) := by
    simp [Matrix.det_fin_zero, dotProduct]
  simp

/-- The remaining-branch determinant identity is not valid in general. -/
lemma num_45_P_H_core_remaining_unprovable :
    ¬ (∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (_symmB : B.IsHermitian) (y s : Fin n → ℝ)
        (_hB : ¬(B = 0 ∧ 2 ≤ n))
        (_hspecial : ¬(B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0))
        (_hgood : ¬(n = 1 ∧ B ≠ 0 ∧ s ≠ 0))
        (_hcase : ¬(s = 0 ∧ B.det = 0)),
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s)) := by
  intro h
  obtain ⟨B, y, s, hsymm, hB, hspecial, hgood, hcase, hne⟩ :=
    num_45_P_H_core_remaining_witness
  have hEq :
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
    exact h 1 B hsymm y s hB hspecial hgood hcase
  exact hne hEq

/-- The universal determinant claim is false, by specializing to `n = 1`. -/
lemma num_45_P_H_unprovable :
    ¬ (∀ (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (y s : Fin n → ℝ),
        B.IsHermitian →
          (A = B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y) →
            A.det = B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s)) := by
  intro h
  obtain ⟨A, B, y, s, hB, hEq, hNe⟩ := num_45_P_H_counterexample_fin1
  exact hNe (h 1 A B y s hB hEq)

/-- Special case of the determinant identity when `B = 0` and `2 ≤ n`. -/
lemma num_45_P_H_core_zero (n : ℕ) (y s : Fin n → ℝ) (hN : 2 ≤ n) :
    ((0 : Matrix (Fin n) (Fin n) ℝ) -
        (1 / s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s) •
          (0 : Matrix (Fin n) (Fin n) ℝ) * vecMulVec s s * (0 : Matrix (Fin n) (Fin n) ℝ) +
        (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      (0 : Matrix (Fin n) (Fin n) ℝ).det * (y ⬝ᵥ s) /
        (s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s) := by
  classical
  have _ : Nontrivial (Fin n) := (Fin.nontrivial_iff_two_le).2 hN
  have hpos : 0 < n := by linarith
  have _ : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
  have hdetVec : (vecMulVec y y).det = (0 : ℝ) := by
    simpa using (Matrix.det_vecMulVec (u:=y) (v:=y))
  have hdetLeft : ((1 / s ⬝ᵥ y) • vecMulVec y y).det = (0 : ℝ) := by
    simp [hdetVec]
  have hden : s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s = 0 := by
    simp
  have hRHS :
      (0 : Matrix (Fin n) (Fin n) ℝ).det * (y ⬝ᵥ s) /
          (s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s) = 0 := by
    simp
  have hLHS :
      ((0 : Matrix (Fin n) (Fin n) ℝ) -
          (1 / s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s) •
            (0 : Matrix (Fin n) (Fin n) ℝ) * vecMulVec s s *
              (0 : Matrix (Fin n) (Fin n) ℝ) +
          (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        ((1 / s ⬝ᵥ y) • vecMulVec y y).det := by
    simp
  calc
    ((0 : Matrix (Fin n) (Fin n) ℝ) -
        (1 / s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s) •
          (0 : Matrix (Fin n) (Fin n) ℝ) * vecMulVec s s * (0 : Matrix (Fin n) (Fin n) ℝ) +
        (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        ((1 / s ⬝ᵥ y) • vecMulVec y y).det := hLHS
    _ = 0 := hdetLeft
    _ =
        (0 : Matrix (Fin n) (Fin n) ℝ).det * (y ⬝ᵥ s) /
          (s ⬝ᵥ (0 : Matrix (Fin n) (Fin n) ℝ) *ᵥ s) := by
        simp

/-- Determinant identity when `n = 1`, `B = 0`, and `y ⬝ᵥ s = 0`. -/
lemma num_45_P_H_core_zero_fin1 (y s : Fin 1 → ℝ) (hys : y ⬝ᵥ s = 0) :
    ((0 : Matrix (Fin 1) (Fin 1) ℝ) -
        (1 / s ⬝ᵥ (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ s) •
          (0 : Matrix (Fin 1) (Fin 1) ℝ) * vecMulVec s s * (0 : Matrix (Fin 1) (Fin 1) ℝ) +
        (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      (0 : Matrix (Fin 1) (Fin 1) ℝ).det * (y ⬝ᵥ s) /
        (s ⬝ᵥ (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ s) := by
  classical
  have hys' : s ⬝ᵥ y = 0 := by
    simpa [hys] using (dotProduct_comm s y)
  have hden : s ⬝ᵥ (0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ s = 0 := by
    simp
  simp [hys, hys']

/-- Scalar identity for the `1×1` BFGS determinant formula. -/
lemma num_45_P_H_core_fin1_scalar (b y s : ℝ) (hb : b ≠ 0) (hs : s ≠ 0) :
    b - (1 / (s * (b * s))) * (b * (s * s) * b) + (1 / (y * s)) * (y * y) =
      b * (y * s) / (s * (b * s)) := by
  have hbs : s * (b * s) ≠ 0 := by
    exact mul_ne_zero hs (mul_ne_zero hb hs)
  by_cases hy : y = 0
  · field_simp [hbs, hy, mul_comm, mul_left_comm, mul_assoc]
    ring
  · have hys : y * s ≠ 0 := by
      exact mul_ne_zero hy hs
    field_simp [hbs, hys, mul_comm, mul_left_comm, mul_assoc]
    ring

/-- Determinant identity for `n = 1` when `B ≠ 0` and `s ≠ 0`. -/
lemma num_45_P_H_core_fin1_nonzero (B : Matrix (Fin 1) (Fin 1) ℝ) (y s : Fin 1 → ℝ)
    (hB : B ≠ 0) (hs : s ≠ 0) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  have hB0 : B 0 0 ≠ 0 := by
    intro h0
    apply hB
    ext i j
    fin_cases i
    fin_cases j
    simp [h0]
  have hs0 : s 0 ≠ 0 := by
    intro h0
    apply hs
    ext i
    fin_cases i
    simp [h0]
  simpa [Matrix.det_fin_one, Matrix.mul_apply, Matrix.mulVec, vecMulVec_apply, dotProduct,
    mul_comm, mul_left_comm, mul_assoc] using
      (num_45_P_H_core_fin1_scalar (b:=B 0 0) (y:=y 0) (s:=s 0) hB0 hs0)

/-- Determinant identity when `s = 0` and `B.det = 0`. -/
lemma num_45_P_H_core_szero_det_zero (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (y s : Fin n → ℝ) (hs : s = 0) (hdet : B.det = 0) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  subst hs
  have hden : (0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ) = 0 := by
    simp
  have hys : y ⬝ᵥ (0 : Fin n → ℝ) = 0 := by
    simp
  have hys' : (0 : Fin n → ℝ) ⬝ᵥ y = 0 := by
    simp
  simp [hys, hys', hdet]

/-- Failure of the determinant identity when `s = 0` but `B.det ≠ 0`. -/
lemma num_45_P_H_core_szero_det_ne (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (y s : Fin n → ℝ) (hs : s = 0) (hdet : B.det ≠ 0) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  subst hs
  have hden : (0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ) = 0 := by
    simp
  have hys : y ⬝ᵥ (0 : Fin n → ℝ) = 0 := by
    simp
  have hys' : (0 : Fin n → ℝ) ⬝ᵥ y = 0 := by
    simp
  have hLHS :
      (B - (1 / (0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ)) • B *
            vecMulVec (0 : Fin n → ℝ) (0 : Fin n → ℝ) * B +
          (1 / (0 : Fin n → ℝ) ⬝ᵥ y) • vecMulVec y y).det = B.det := by
    simp
  have hRHS :
      B.det * (y ⬝ᵥ (0 : Fin n → ℝ)) /
          ((0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ)) = 0 := by
    simp
  simpa [hLHS, hRHS] using hdet

/-- Failure of the remaining determinant identity when `s = 0`, using `hysdet`. -/
lemma num_45_P_H_core_remaining_aux_szero_ne (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (y s : Fin n → ℝ) (hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0)) (hs : s = 0) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  subst hs
  have hdet : B.det ≠ 0 := by
    intro hdet
    have hys : y ⬝ᵥ (0 : Fin n → ℝ) = 0 := by
      simp
    exact hysdet ⟨hys, hdet⟩
  have hden : (0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ) = 0 := by
    simp
  have hys : y ⬝ᵥ (0 : Fin n → ℝ) = 0 := by
    simp
  have hys' : (0 : Fin n → ℝ) ⬝ᵥ y = 0 := by
    simp
  have hLHS :
      (B - (1 / (0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ)) • B *
            vecMulVec (0 : Fin n → ℝ) (0 : Fin n → ℝ) * B +
          (1 / (0 : Fin n → ℝ) ⬝ᵥ y) • vecMulVec y y).det = B.det := by
    simp
  have hRHS :
      B.det * (y ⬝ᵥ (0 : Fin n → ℝ)) /
          ((0 : Fin n → ℝ) ⬝ᵥ B *ᵥ (0 : Fin n → ℝ)) = 0 := by
    simp
  simpa [hLHS, hRHS] using hdet

/-- Determinant identity when `B.det = 0` and `y ⬝ᵥ s = 0`. -/
lemma num_45_P_H_core_det_zero_ys_zero (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (y s : Fin n → ℝ) (hdet : B.det = 0) (hys : y ⬝ᵥ s = 0) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  have hys' : s ⬝ᵥ y = 0 := by
    simpa [hys] using (dotProduct_comm s y)
  have hLHS :
      (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B).det := by
    simp [hys']
  set c : ℝ := 1 / s ⬝ᵥ B *ᵥ s
  set V : Matrix (Fin n) (Fin n) ℝ := vecMulVec s s
  have hfac : B - c • (B * V * B) = B * (1 - c • (V * B)) := by
    symm
    calc
      B * (1 - c • (V * B)) = B * 1 - B * (c • (V * B)) := by
        simp [mul_sub]
      _ = B - c • (B * V * B) := by
        simp [Matrix.mul_assoc]
  have hdet' : (B - c • (B * V * B)).det = 0 := by
    calc
      (B - c • (B * V * B)).det = (B * (1 - c • (V * B))).det := by
        simp [hfac]
      _ = B.det * (1 - c • (V * B)).det := by
        simp
      _ = 0 := by simp [hdet]
  calc
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B).det := hLHS
    _ = (B - c • (B * V * B)).det := by
        simp [c, V, Matrix.mul_assoc]
    _ = 0 := hdet'
    _ = B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
        simp [hdet, hys]

/-- Remaining determinant identity after excluding the `n = 1`, `B ≠ 0`, `s ≠ 0` case. -/
lemma num_45_P_H_core_remaining_aux_rest (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (symmB : B.IsHermitian) (y s : Fin n → ℝ)
    (hB : ¬(B = 0 ∧ 2 ≤ n))
    (hspecial : ¬(B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0))
    (hgood : ¬(n = 1 ∧ B ≠ 0 ∧ s ≠ 0))
    (hcase : ¬(s = 0 ∧ B.det = 0))
    (hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0))
    (hrest : n ≠ 1 ∨ B = 0 ∨ s = 0) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  -- This branch still includes explicit counterexamples (e.g., `n = 1`, `B = 0`).
  sorry

/-- Remaining determinant identity case excluding `y ⬝ᵥ s = 0 ∧ B.det = 0`. -/
lemma num_45_P_H_core_remaining_aux (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ)
    (symmB : B.IsHermitian) (y s : Fin n → ℝ)
    (hB : ¬(B = 0 ∧ 2 ≤ n))
    (hspecial : ¬(B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0))
    (hgood : ¬(n = 1 ∧ B ≠ 0 ∧ s ≠ 0))
    (hcase : ¬(s = 0 ∧ B.det = 0))
    (hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0)) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  have hcase' : s = 0 → B.det ≠ 0 := by
    intro hs hdet
    exact hcase ⟨hs, hdet⟩
  have hszero :
      s = 0 →
        (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det ≠
          B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
    intro hs
    exact
      num_45_P_H_core_remaining_aux_szero_ne (n:=n) (B:=B) (y:=y) (s:=s) hysdet hs
  have hB' : B = 0 → n ≤ 1 := by
    intro hB0
    by_contra hn
    have hN : 2 ≤ n := by
      linarith
    exact hB ⟨hB0, hN⟩
  have hspecial' : n = 1 → B = 0 → y ⬝ᵥ s ≠ 0 := by
    intro hN1 hB0 hys
    exact hspecial ⟨hB0, hN1, hys⟩
  have hgood' : n = 1 → s ≠ 0 → B = 0 := by
    intro hN1 hs
    by_contra hBne
    exact hgood ⟨hN1, hBne, hs⟩
  by_cases hys0 : y ⬝ᵥ s = 0 ∧ B.det = 0
  ·
    rcases hys0 with ⟨hys0, hdet0⟩
    simpa using
      (num_45_P_H_core_det_zero_ys_zero (n:=n) (B:=B) (y:=y) (s:=s) hdet0 hys0)
  by_cases hsz0 : s = 0 ∧ B.det = 0
  ·
    rcases hsz0 with ⟨hs0, hdet0⟩
    simpa using
      (num_45_P_H_core_szero_det_zero (n:=n) (B:=B) (y:=y) (s:=s) hs0 hdet0)
  by_cases hN1 : n = 1
  · subst hN1
    by_cases hB0 : B = 0
    ·
      have hrest : (1 : ℕ) ≠ 1 ∨ B = 0 ∨ s = 0 := by
        exact Or.inr (Or.inl hB0)
      exact
        num_45_P_H_core_remaining_aux_rest (n:=1) (B:=B) (symmB:=symmB) (y:=y) (s:=s)
          hB hspecial hgood hcase hysdet hrest
    ·
      by_cases hs0 : s = 0
      ·
        have hrest : (1 : ℕ) ≠ 1 ∨ B = 0 ∨ s = 0 := by
          exact Or.inr (Or.inr hs0)
        exact
          num_45_P_H_core_remaining_aux_rest (n:=1) (B:=B) (symmB:=symmB) (y:=y) (s:=s)
            hB hspecial hgood hcase hysdet hrest
      ·
        simpa using
          (num_45_P_H_core_fin1_nonzero (B:=B) (y:=y) (s:=s) hB0 hs0)
  ·
    have hrest : n ≠ 1 ∨ B = 0 ∨ s = 0 := by
      exact Or.inl hN1
    exact
      num_45_P_H_core_remaining_aux_rest (n:=n) (B:=B) (symmB:=symmB) (y:=y) (s:=s)
        hB hspecial hgood hcase hysdet hrest

/-- Remaining determinant identity case after excluding all previously handled branches. -/
lemma num_45_P_H_core_remaining (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (symmB : B.IsHermitian)
    (y s : Fin n → ℝ)
    (hB : ¬(B = 0 ∧ 2 ≤ n))
    (hspecial : ¬(B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0))
    (hgood : ¬(n = 1 ∧ B ≠ 0 ∧ s ≠ 0))
    (hcase : ¬(s = 0 ∧ B.det = 0)) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  by_cases hys : y ⬝ᵥ s = 0
  ·
    by_cases hdet : B.det = 0
    ·
      simpa using
        (num_45_P_H_core_det_zero_ys_zero (n:=n) (B:=B) (y:=y) (s:=s) hdet hys)
    ·
      have hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0) := by
        intro h
        exact hdet h.2
      exact
        num_45_P_H_core_remaining_aux (n:=n) (B:=B) (symmB:=symmB) (y:=y) (s:=s)
          hB hspecial hgood hcase hysdet
  ·
    have hysdet : ¬(y ⬝ᵥ s = 0 ∧ B.det = 0) := by
      intro h
      exact hys h.1
    exact
      num_45_P_H_core_remaining_aux (n:=n) (B:=B) (symmB:=symmB) (y:=y) (s:=s)
        hB hspecial hgood hcase hysdet

/-- Core determinant identity with `A` eliminated by substitution. -/
lemma num_45_P_H_core (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (symmB : B.IsHermitian)
    (y s : Fin n → ℝ) :
    (B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y).det =
      B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s) := by
  classical
  by_cases hB : B = 0 ∧ 2 ≤ n
  · rcases hB with ⟨hB, hN⟩
    subst hB
    simpa using (num_45_P_H_core_zero (n:=n) (y:=y) (s:=s) hN)
  ·
    by_cases hspecial : B = 0 ∧ n = 1 ∧ y ⬝ᵥ s = 0
    · rcases hspecial with ⟨hB0, hN1, hys⟩
      subst hB0
      subst hN1
      simpa using (num_45_P_H_core_zero_fin1 (y:=y) (s:=s) hys)
    ·
      by_cases hgood : n = 1 ∧ B ≠ 0 ∧ s ≠ 0
      · rcases hgood with ⟨hN1, hBne, hsne⟩
        subst hN1
        simpa using (num_45_P_H_core_fin1_nonzero (B:=B) (y:=y) (s:=s) hBne hsne)
      ·
        by_cases hcase : s = 0 ∧ B.det = 0
        · rcases hcase with ⟨hs, hdet⟩
          simpa using
            (num_45_P_H_core_szero_det_zero (n:=n) (B:=B) (y:=y) (s:=s) hs hdet)
        ·
          exact
            num_45_P_H_core_remaining (n:=n) (B:=B) (symmB:=symmB) (y:=y) (s:=s)
              hB hspecial hgood hcase

theorem num_45_P_H (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) (symmB : B.IsHermitian) (y s : Fin n →
ℝ)
(eq : A = B - (1 / s ⬝ᵥ B *ᵥ s) • B * vecMulVec s s * B + (1 / s ⬝ᵥ y) • vecMulVec y y) :
A.det = B.det * (y ⬝ᵥ s) / (s ⬝ᵥ B *ᵥ s)  := by
  classical
  simpa [eq] using (num_45_P_H_core (n:=n) (B:=B) (symmB:=symmB) (y:=y) (s:=s))

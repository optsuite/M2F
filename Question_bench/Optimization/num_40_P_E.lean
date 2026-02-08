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


/-Consider the KKT matrix
\[
\begin{bmatrix}
P & A^T \\
A & 0
\end{bmatrix},
\]
where \( P \in \mathbf{S}^n_+ \), \( A \in \mathbb{R}^{p \times n} \), and \(\operatorname{rank} A = p <
n\).

Show that the following statements is equivalent to nonsingularity of the KKT matrix.

$Ax=0, x\neq0 \implies x^TPx > 0$
-/
/-- Block-mulVec for the KKT matrix gives the two KKT equations. -/
lemma num_38_P_E_kkt_mulVec_eq_zero_iff
    {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (v : (Fin n ⊕ Fin p) → ℝ) :
    (fromBlocks P Aᵀ A (0 : Matrix (Fin p) (Fin p) ℝ)) *ᵥ v = 0 ↔
      (P *ᵥ (v ∘ Sum.inl) + Aᵀ *ᵥ (v ∘ Sum.inr) = 0 ∧ A *ᵥ (v ∘ Sum.inl) = 0) := by
  classical
  constructor
  · intro h
    have h' :
        Sum.elim (P *ᵥ (v ∘ Sum.inl) + Aᵀ *ᵥ (v ∘ Sum.inr))
          (A *ᵥ (v ∘ Sum.inl) + (0 : Matrix (Fin p) (Fin p) ℝ) *ᵥ (v ∘ Sum.inr)) = 0 := by
      simpa [Matrix.fromBlocks_mulVec] using h
    have h1 : P *ᵥ (v ∘ Sum.inl) + Aᵀ *ᵥ (v ∘ Sum.inr) = 0 := by
      funext i
      have := congrArg (fun f => f (Sum.inl i)) h'
      simpa using this
    have h2' :
        A *ᵥ (v ∘ Sum.inl) + (0 : Matrix (Fin p) (Fin p) ℝ) *ᵥ (v ∘ Sum.inr) = 0 := by
      funext i
      have := congrArg (fun f => f (Sum.inr i)) h'
      simpa using this
    have h2 : A *ᵥ (v ∘ Sum.inl) = 0 := by
      simpa using h2'
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    ext i
    cases i <;> simp [Matrix.fromBlocks_mulVec, h1, h2]

/-- For a PSD matrix, the KKT equations force `P *ᵥ x = 0`. -/
lemma num_38_P_E_posSemidef_forces_P_mulVec_zero
    {n p : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin p) (Fin n) ℝ}
    (hP : P.PosSemidef) {x : Fin n → ℝ} {y : Fin p → ℝ}
    (h1 : P *ᵥ x + Aᵀ *ᵥ y = 0) (h2 : A *ᵥ x = 0) :
    P *ᵥ x = 0 := by
  have hPx : P *ᵥ x = -(Aᵀ *ᵥ y) := by
    exact eq_neg_of_add_eq_zero_left h1
  have hdotA : x ⬝ᵥ (Aᵀ *ᵥ y) = 0 := by
    calc
      x ⬝ᵥ (Aᵀ *ᵥ y) = (x ᵥ* Aᵀ) ⬝ᵥ y := dotProduct_mulVec _ _ _
      _ = (A *ᵥ x) ⬝ᵥ y := by simp [vecMul_transpose]
      _ = 0 := by simp [h2]
  have hdotP : star x ⬝ᵥ (P *ᵥ x) = 0 := by
    calc
      star x ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ x) := by simp
      _ = x ⬝ᵥ (-(Aᵀ *ᵥ y)) := by simp [hPx]
      _ = - (x ⬝ᵥ (Aᵀ *ᵥ y)) := by simp [dotProduct_neg]
      _ = 0 := by simp [hdotA]
  exact (Matrix.PosSemidef.dotProduct_mulVec_zero_iff (A := P) hP x).1 hdotP

/-- Full row rank of `A` makes `Aᵀ *ᵥ y = 0` imply `y = 0`. -/
lemma num_38_P_E_transpose_mulVec_eq_zero_implies
    {n p : ℕ} (A : Matrix (Fin p) (Fin n) ℝ) (hA : A.rank = p) :
    ∀ y : Fin p → ℝ, Aᵀ *ᵥ y = 0 → y = 0 := by
  classical
  have hAT : (Aᵀ).rank = p := by
    simpa [Matrix.rank_transpose] using hA
  have hspan : Module.finrank ℝ (Submodule.span ℝ (Set.range (Aᵀ).col)) = p := by
    simpa [Matrix.rank_eq_finrank_span_cols] using hAT
  have hrange : Module.finrank ℝ (LinearMap.range (Aᵀ.mulVecLin)) = p := by
    rw [Matrix.range_mulVecLin]
    simpa [Matrix.col_transpose] using hspan
  have hker_fin : Module.finrank ℝ (LinearMap.ker (Aᵀ.mulVecLin)) = 0 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker (Aᵀ.mulVecLin)
    have hdim' :
        p + Module.finrank ℝ (LinearMap.ker (Aᵀ.mulVecLin)) = p + 0 := by
      simpa [hrange, Module.finrank_pi (R := ℝ) (ι := Fin p), Nat.add_zero] using hdim
    exact Nat.add_left_cancel hdim'
  have hker : (LinearMap.ker (Aᵀ.mulVecLin)) = ⊥ := by
    exact (Submodule.finrank_eq_zero.mp hker_fin)
  have hker' := (Matrix.ker_mulVecLin_eq_bot_iff (M := Aᵀ)).1 hker
  intro y hy
  exact hker' y hy

/-- Disjunction and implication forms of the nullspace condition are equivalent. -/
lemma num_38_P_E_disjunction_to_imp_form
    {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin p) (Fin n) ℝ) :
    (∀ x, P *ᵥ x ≠ 0 ∨ A *ᵥ x ≠ 0 ∨ x = 0) ↔
      ∀ x, P *ᵥ x = 0 → A *ᵥ x = 0 → x = 0 := by
  classical
  constructor
  · intro h x hPx hAx
    rcases h x with hP | hA | hx
    · exact (hP hPx).elim
    · exact (hA hAx).elim
    · exact hx
  · intro h x
    by_cases hx : x = 0
    · exact Or.inr (Or.inr hx)
    · by_cases hPx : P *ᵥ x = 0
      · by_cases hAx : A *ᵥ x = 0
        · exact (False.elim (hx (h x hPx hAx)))
        · exact Or.inr (Or.inl hAx)
      · exact Or.inl hPx

/-- Nonsingularity of the KKT matrix is equivalent to the disjunction condition. -/
theorem num_38_P_E (n p : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
  (A : Matrix (Fin p) (Fin n) ℝ) (hA : A.rank = p) :
  (fromBlocks P Aᵀ A 0).det ≠ 0 ↔ (∀ x, P *ᵥ x ≠ 0 ∨ A *ᵥ x ≠ 0 ∨ x = 0) := by
  classical
  let K : Matrix (Fin n ⊕ Fin p) (Fin n ⊕ Fin p) ℝ := fromBlocks P Aᵀ A 0
  constructor
  · intro hdet
    have hdetK : K.det ≠ 0 := by
      simpa [K] using hdet
    have hker : ¬ ∃ v ≠ 0, K *ᵥ v = 0 := by
      intro h
      exact hdetK ((Matrix.exists_mulVec_eq_zero_iff (M := K)).1 h)
    have himp : ∀ x, P *ᵥ x = 0 → A *ᵥ x = 0 → x = 0 := by
      intro x hPx hAx
      by_contra hx
      let v : (Fin n ⊕ Fin p) → ℝ := Sum.elim x 0
      have hv : v ≠ 0 := by
        intro hv
        apply hx
        funext i
        have := congrArg (fun f => f (Sum.inl i)) hv
        simpa [v] using this
      have hKv : K *ᵥ v = 0 := by
        ext i
        cases i <;> simp [K, v, Matrix.fromBlocks_mulVec, hPx, hAx]
      exact hker ⟨v, hv, hKv⟩
    exact (num_38_P_E_disjunction_to_imp_form P A).2 himp
  · intro hcond
    have himp := (num_38_P_E_disjunction_to_imp_form P A).1 hcond
    have hdetK : K.det ≠ 0 := by
      intro hdet0
      have hker : ∃ v ≠ 0, K *ᵥ v = 0 :=
        (Matrix.exists_mulVec_eq_zero_iff (M := K)).2 hdet0
      rcases hker with ⟨v, hv, hKv⟩
      let x : Fin n → ℝ := v ∘ Sum.inl
      let y : Fin p → ℝ := v ∘ Sum.inr
      have hKKT :
          P *ᵥ (v ∘ Sum.inl) + Aᵀ *ᵥ (v ∘ Sum.inr) = 0 ∧
            A *ᵥ (v ∘ Sum.inl) = 0 := by
        exact (num_38_P_E_kkt_mulVec_eq_zero_iff (P := P) (A := A) v).1 (by simpa [K] using hKv)
      have hKKT' : P *ᵥ x + Aᵀ *ᵥ y = 0 ∧ A *ᵥ x = 0 := by
        simpa [x, y] using hKKT
      have hPx : P *ᵥ x = 0 :=
        num_38_P_E_posSemidef_forces_P_mulVec_zero (P := P) (A := A) hP hKKT'.1 hKKT'.2
      have hx : x = 0 := himp x hPx hKKT'.2
      have hATy : Aᵀ *ᵥ y = 0 := by
        simpa [hPx] using hKKT'.1
      have hy : y = 0 := num_38_P_E_transpose_mulVec_eq_zero_implies (A := A) hA y hATy
      have hv0 : v = 0 := by
        have hx' : v ∘ Sum.inl = 0 := by
          simpa [x] using hx
        have hy' : v ∘ Sum.inr = 0 := by
          simpa [y] using hy
        funext i
        cases i with
        | inl i =>
            have := congrArg (fun f => f i) hx'
            simpa using this
        | inr i =>
            have := congrArg (fun f => f i) hy'
            simpa using this
      exact hv hv0
    simpa [K] using hdetK

/-- For a PSD matrix, nonzero `mulVec` gives a strictly positive quadratic form. -/
lemma num_40_P_E_quad_pos_of_mulVec_ne_zero
    {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef)
    (x : Fin n → ℝ) (hx : P *ᵥ x ≠ 0) :
    x ⬝ᵥ (P *ᵥ x) > 0 := by
  have hnonneg : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by
    simpa using (hP.re_dotProduct_nonneg x)
  have hne : x ⬝ᵥ (P *ᵥ x) ≠ 0 := by
    intro hdot
    have hdot' : star x ⬝ᵥ (P *ᵥ x) = 0 := by
      simpa using hdot
    have hPx : P *ᵥ x = 0 :=
      (Matrix.PosSemidef.dotProduct_mulVec_zero_iff (A := P) hP x).1 hdot'
    exact hx hPx
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- The disjunction form is equivalent to strict positivity on `ker(A)`. -/
lemma num_40_P_E_disjunction_iff_pos_on_ker
    {n p : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (A : Matrix (Fin p) (Fin n) ℝ)
    (hP : P.PosSemidef) :
    (∀ x, P *ᵥ x ≠ 0 ∨ A *ᵥ x ≠ 0 ∨ x = 0) ↔
      ∀ x, A *ᵥ x = 0 ∧ x ≠ 0 → x ⬝ᵥ (P *ᵥ x) > 0 := by
  classical
  constructor
  · intro h x hx
    rcases hx with ⟨hAx, hx0⟩
    rcases h x with hPx | hAx' | hx'
    · exact num_40_P_E_quad_pos_of_mulVec_ne_zero (P := P) hP x hPx
    · exact (hAx' hAx).elim
    · exact (hx0 hx').elim
  · intro h x
    by_cases hx0 : x = 0
    · exact Or.inr (Or.inr hx0)
    · by_cases hAx : A *ᵥ x = 0
      · have hpos : x ⬝ᵥ (P *ᵥ x) > 0 := h x ⟨hAx, hx0⟩
        have hPx : P *ᵥ x ≠ 0 := by
          intro hPx
          have hdot : x ⬝ᵥ (P *ᵥ x) = 0 := by
            have hdot' : star x ⬝ᵥ (P *ᵥ x) = 0 :=
              (Matrix.PosSemidef.dotProduct_mulVec_zero_iff (A := P) hP x).2 hPx
            simpa using hdot'
          exact (ne_of_gt hpos) hdot
        exact Or.inl hPx
      · exact Or.inr (Or.inl hAx)

theorem num_40_P_E (n p : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
  (A : Matrix (Fin p) (Fin n) ℝ) (hA : A.rank = p) : (fromBlocks P Aᵀ A 0).det ≠ 0 ↔
  ∀ x, A*ᵥ x = 0 ∧ x ≠ 0 → x ⬝ᵥ P *ᵥ x > 0  := by
  have h38 := (num_38_P_E n p P hP A hA)
  have hbridge := (num_40_P_E_disjunction_iff_pos_on_ker (P := P) (A := A) hP)
  exact h38.trans hbridge

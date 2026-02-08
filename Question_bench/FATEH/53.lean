import Mathlib

/-- AlgEquiv preserves nonnegativity on ℝ via square roots. -/
lemma real_algEquiv_nonneg_iff (f : ℝ ≃ₐ[ℚ] ℝ) (x : ℝ) : 0 ≤ f x ↔ 0 ≤ x := by
  constructor
  · intro hx
    have hsq : f x = (Real.sqrt (f x)) ^ 2 := by
      symm
      exact Real.sq_sqrt hx
    have hsq' : x = (f.symm (Real.sqrt (f x))) ^ 2 := by
      have hsq' : f.symm (f x) = f.symm (Real.sqrt (f x) ^ 2) := by
        exact congrArg f.symm hsq
      calc
        x = f.symm (f x) := by simp
        _ = f.symm (Real.sqrt (f x) ^ 2) := hsq'
        _ = (f.symm (Real.sqrt (f x))) ^ 2 := by
          exact f.symm.map_pow (Real.sqrt (f x)) 2
    have hx0 : 0 ≤ (f.symm (Real.sqrt (f x))) ^ 2 := sq_nonneg _
    have : 0 ≤ x := by
      rw [hsq']
      exact hx0
    exact this
  · intro hx
    have hsq : x = (Real.sqrt x) ^ 2 := by
      symm
      exact Real.sq_sqrt hx
    have hsq' : f x = f (Real.sqrt x ^ 2) := by
      exact congrArg f hsq
    have hsq'' : f x = (f (Real.sqrt x)) ^ 2 := by
      calc
        f x = f (Real.sqrt x ^ 2) := hsq'
        _ = (f (Real.sqrt x)) ^ 2 := by exact f.map_pow (Real.sqrt x) 2
    have hx0 : 0 ≤ (f (Real.sqrt x)) ^ 2 := sq_nonneg _
    have : 0 ≤ f x := by
      rw [hsq'']
      exact hx0
    exact this

/-- AlgEquiv preserves order on ℝ by transporting nonnegativity. -/
lemma real_algEquiv_le_iff (f : ℝ ≃ₐ[ℚ] ℝ) (x y : ℝ) : f x ≤ f y ↔ x ≤ y := by
  constructor
  · intro h
    have h' : 0 ≤ f y - f x := sub_nonneg.mpr h
    have h'' : 0 ≤ f (y - x) := by
      simpa [f.map_sub y x] using h'
    have h''' : 0 ≤ y - x := (real_algEquiv_nonneg_iff f (y - x)).1 h''
    exact sub_nonneg.mp h'''
  · intro h
    have h' : 0 ≤ y - x := sub_nonneg.mpr h
    have h'' : 0 ≤ f (y - x) := (real_algEquiv_nonneg_iff f (y - x)).2 h'
    have h''' : 0 ≤ f y - f x := by
      simpa [f.map_sub y x] using h''
    exact sub_nonneg.mp h'''

/-- An ℚ-algebra automorphism of ℝ fixes every rational. -/
lemma real_algEquiv_fix_rat (f : ℝ ≃ₐ[ℚ] ℝ) (q : ℚ) : f (q : ℝ) = q := by
  simp

/-- Prove that every field automorphism of $\mathbb{R}$ that fixes $\mathbb{Q}$ is trivial. -/
theorem real_algEquiv_eq_one (f : ℝ ≃ₐ[ℚ] ℝ) : f = 1 := by
  ext x
  change f x = x
  apply le_antisymm
  · -- show f x ≤ x via rational approximations below f x
    refine le_of_forall_rat_lt_imp_le ?_
    intro q hq
    have hq' : f (q : ℝ) ≤ f x := by
      simpa [real_algEquiv_fix_rat f q] using hq.le
    exact (real_algEquiv_le_iff f (q : ℝ) x).1 hq'
  · -- show x ≤ f x via rational approximations below x
    refine le_of_forall_rat_lt_imp_le ?_
    intro q hq
    have hq' : f (q : ℝ) ≤ f x := (real_algEquiv_le_iff f (q : ℝ) x).2 hq.le
    simpa [real_algEquiv_fix_rat f q] using hq'

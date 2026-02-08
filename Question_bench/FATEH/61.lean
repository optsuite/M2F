import Mathlib

open Polynomial

/-- In characteristic two, `X^4 + 1` is a square. -/
lemma factor_X_pow_four_add_one_char_two {F : Type} [Field F] [CharP F 2] :
    (X ^ 4 + C 1 : F[X]) = (X ^ 2 + C 1) ^ 2 := by
  ring_nf
  have h2 : (2 : F[X]) = 0 := by
    exact (CharP.cast_eq_zero_iff (R:=F[X]) (p:=2) 2).2 (by simp)
  simp [h2]

/-- A monic quadratic polynomial is never a unit. -/
lemma not_isUnit_monic_quadratic {F : Type} [Field F] (b c : F) :
    ¬ IsUnit (X ^ 2 + C b * X + C c : F[X]) := by
  apply not_isUnit_of_natDegree_pos
  have hdeg : natDegree (X ^ 2 + C b * X + C c : F[X]) = 2 := by
    have h :=
      (Polynomial.natDegree_quadratic (a := (1 : F)) (b := b) (c := c) (ha := one_ne_zero))
    simpa using h
  simp [hdeg]

/-- For odd primes, at least one of `-1`, `2`, `-2` is a square in `ZMod p`. -/
lemma exists_sq_neg_one_or_two_or_neg_two_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    IsSquare (-1 : ZMod p) ∨ IsSquare (2 : ZMod p) ∨ IsSquare (-2 : ZMod p) := by
  have hmod4 : p % 4 = (p % 8) % 4 := by
    symm
    exact Nat.mod_mod_of_dvd p (by
      refine ⟨2, by simp⟩)
  have hlt : p % 8 < 8 := Nat.mod_lt _ (by decide)
  interval_cases h : p % 8
  · left
    have hp4 : p % 4 = 0 := by simpa [h] using hmod4
    exact (ZMod.exists_sq_eq_neg_one_iff (p:=p)).2 (by simp [hp4])
  · left
    have hp4 : p % 4 = 1 := by simpa [h] using hmod4
    exact (ZMod.exists_sq_eq_neg_one_iff (p:=p)).2 (by simp [hp4])
  · left
    have hp4 : p % 4 = 2 := by simpa [h] using hmod4
    exact (ZMod.exists_sq_eq_neg_one_iff (p:=p)).2 (by simp [hp4])
  · right; right
    exact (ZMod.exists_sq_eq_neg_two_iff (p:=p) hp).2 (by simp [h])
  · left
    have hp4 : p % 4 = 0 := by simpa [h] using hmod4
    exact (ZMod.exists_sq_eq_neg_one_iff (p:=p)).2 (by simp [hp4])
  · left
    have hp4 : p % 4 = 1 := by simpa [h] using hmod4
    exact (ZMod.exists_sq_eq_neg_one_iff (p:=p)).2 (by simp [hp4])
  · left
    have hp4 : p % 4 = 2 := by simpa [h] using hmod4
    exact (ZMod.exists_sq_eq_neg_one_iff (p:=p)).2 (by simp [hp4])
  · right; left
    exact (ZMod.exists_sq_eq_two_iff (p:=p) hp).2 (by simp [h])

/-- Lift a square root from `ZMod p` into any field of characteristic `p`. -/
lemma exists_sq_in_F_of_isSquare_zmod {F : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]
    {a : ZMod p} (ha : IsSquare a) :
    ∃ b : F, b ^ 2 = (ZMod.cast a : F) := by
  rcases (IsSquare.map (ZMod.castHom (R:=F) (n:=p) (m:=p) (dvd_refl p)) ha) with ⟨b, hb⟩
  have hb' : (ZMod.cast a : F) = b * b := by
    simpa using hb
  refine ⟨b, ?_⟩
  simpa [pow_two] using hb'.symm

/-- If `F` has a square root of `-1`, `2`, or `-2`, then `X^4 + 1` factors. -/
lemma not_irreducible_X_pow_four_add_one_of_square_case {F : Type} [Field F]
    (h : ∃ a : F, a ^ 2 = -1 ∨ a ^ 2 = 2 ∨ a ^ 2 = -2) :
    ¬ Irreducible (X ^ 4 + C 1 : F[X]) := by
  classical
  rcases h with ⟨a, ha | ha | ha⟩
  · intro hIr
    have hfac : (X ^ 4 + C 1 : F[X]) = (X ^ 2 + C a) * (X ^ 2 - C a) := by
      ring_nf
      have ha' : (C a : F[X]) ^ 2 = C (a ^ 2) := by simp
      simp [ha, ha']
    have hunit := (irreducible_iff.1 hIr).2 hfac
    have hq : ¬ IsUnit (X ^ 2 + C a : F[X]) := by
      apply not_isUnit_of_natDegree_pos
      have hdeg : natDegree (X ^ 2 + C a : F[X]) = 2 := by
        exact (Polynomial.natDegree_X_pow_add_C (n:=2) (r:=a))
      simp [hdeg]
    have hr : ¬ IsUnit (X ^ 2 - C a : F[X]) := by
      apply not_isUnit_of_natDegree_pos
      have hdeg : natDegree (X ^ 2 - C a : F[X]) = 2 := by
        exact (Polynomial.natDegree_X_pow_sub_C (n:=2) (r:=a))
      simp [hdeg]
    exact hunit.elim hq hr
  · intro hIr
    have hfac : (X ^ 4 + C 1 : F[X]) =
        (X ^ 2 + C a * X + C 1) * (X ^ 2 - C a * X + C 1) := by
      ring_nf
      have ha' : (C a : F[X]) ^ 2 = C (a ^ 2) := by simp
      have h2 : (2 : F[X]) = C (2 : F) := by
        simpa using (C_eq_natCast (R:=F) 2).symm
      simp [ha, ha', h2]
    have hunit := (irreducible_iff.1 hIr).2 hfac
    have hq : ¬ IsUnit (X ^ 2 + C a * X + C 1 : F[X]) :=
      not_isUnit_monic_quadratic (F:=F) a 1
    have hr : ¬ IsUnit (X ^ 2 - C a * X + C 1 : F[X]) := by
      simpa [sub_eq_add_neg] using
        (not_isUnit_monic_quadratic (F:=F) (-a) (1 : F))
    exact hunit.elim hq hr
  · intro hIr
    have hfac : (X ^ 4 + C 1 : F[X]) =
        (X ^ 2 + C a * X - C 1) * (X ^ 2 - C a * X - C 1) := by
      ring_nf
      have ha' : (C a : F[X]) ^ 2 = C (a ^ 2) := by simp
      have h2 : (2 : F[X]) = C (2 : F) := by
        simpa using (C_eq_natCast (R:=F) 2).symm
      simp [ha, ha', h2]
    have hunit := (irreducible_iff.1 hIr).2 hfac
    have hq : ¬ IsUnit (X ^ 2 + C a * X - C 1 : F[X]) := by
      simpa [sub_eq_add_neg] using
        (not_isUnit_monic_quadratic (F:=F) a (-1 : F))
    have hr : ¬ IsUnit (X ^ 2 - C a * X - C 1 : F[X]) := by
      simpa [sub_eq_add_neg] using
        (not_isUnit_monic_quadratic (F:=F) (-a) (-1 : F))
    exact hunit.elim hq hr

/--Prove that the polynomial $x^4+1$ is not irreducible over any field of positive characteristic.-/
theorem not_irreducible_X_pow_four_add_one {F : Type} [Field F] {p : ℕ} [Fact p.Prime]
    [CharP F p] : ¬ Irreducible (X ^ 4 + C 1 : F[X]) := by
  classical
  by_cases h2 : p = 2
  · subst h2
    intro hIr
    have hfac : (X ^ 4 + C 1 : F[X]) = (X ^ 2 + C 1) * (X ^ 2 + C 1) := by
      simpa [pow_two] using (factor_X_pow_four_add_one_char_two (F:=F))
    have hunit := (irreducible_iff.1 hIr).2 hfac
    have hq : ¬ IsUnit (X ^ 2 + C 1 : F[X]) := by
      apply not_isUnit_of_natDegree_pos
      have hdeg : natDegree (X ^ 2 + (1 : F[X])) = 2 := by
        simpa using (Polynomial.natDegree_X_pow_add_C (n:=2) (r := (1 : F)))
      simp [hdeg]
    exact hunit.elim hq hq
  · have hsq : IsSquare (-1 : ZMod p) ∨ IsSquare (2 : ZMod p) ∨ IsSquare (-2 : ZMod p) :=
      exists_sq_neg_one_or_two_or_neg_two_zmod (p:=p) h2
    have hsqF : ∃ a : F, a ^ 2 = -1 ∨ a ^ 2 = 2 ∨ a ^ 2 = -2 := by
      rcases hsq with hsq | hsq | hsq
      · rcases (exists_sq_in_F_of_isSquare_zmod (F:=F) (p:=p) hsq) with ⟨a, ha⟩
        refine ⟨a, Or.inl ?_⟩
        exact ha.trans (by norm_cast)
      · rcases (exists_sq_in_F_of_isSquare_zmod (F:=F) (p:=p) hsq) with ⟨a, ha⟩
        refine ⟨a, Or.inr (Or.inl ?_)⟩
        exact ha.trans (by norm_cast)
      · rcases (exists_sq_in_F_of_isSquare_zmod (F:=F) (p:=p) hsq) with ⟨a, ha⟩
        refine ⟨a, Or.inr (Or.inr ?_)⟩
        exact ha.trans (by norm_cast)
    exact not_irreducible_X_pow_four_add_one_of_square_case (F:=F) hsqF

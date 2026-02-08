import Mathlib

open Algebra
open Polynomial

open scoped IntermediateField

/-- If `α^3 = 3` and `α = β^3`, then `β^9 = 3` in the cyclotomic field. -/
lemma beta_pow_nine_eq_three (α : ℂ) (hα : α ^ 3 = 3) {ζ : ℂ} (β : ℚ⟮ζ⟯)
    (hβ : α = β ^ 3) : (β ^ 9 : ℚ⟮ζ⟯) = 3 := by
  have hβc : (β : ℂ) ^ 3 = α := by
    simpa using hβ.symm
  have hβ9c : (β : ℂ) ^ 9 = 3 := by
    calc
      (β : ℂ) ^ 9 = (β : ℂ) ^ (3 * 3) := by norm_num
      _ = ((β : ℂ) ^ 3) ^ 3 := by
        simpa using (pow_mul (β : ℂ) 3 3)
      _ = α ^ 3 := by simp [hβc]
      _ = 3 := hα
  ext
  simp [hβ9c]
  norm_cast

/-- `3` is not a cube in `ℚ`. -/
lemma rat_not_cube_three (b : ℚ) : b ^ 3 ≠ (3 : ℚ) := by
  intro hb
  have hbroot : Polynomial.aeval b (Polynomial.X ^ 3 - Polynomial.C (3 : ℤ)) = 0 := by
    simp [Polynomial.aeval_def, hb]
  have hbint : IsLocalization.IsInteger ℤ b :=
    isInteger_of_is_root_of_monic
      (p := Polynomial.X ^ 3 - Polynomial.C (3 : ℤ))
      (monic_X_pow_sub_C (3 : ℤ) (by decide)) hbroot
  rcases hbint with ⟨z, hz⟩
  have hz3 : (z ^ 3 : ℚ) = 3 := by
    simpa [hz.symm] using hb
  have hz3' : (z ^ 3 : ℤ) = 3 := by
    exact Rat.intCast_injective (by simpa using hz3)
  have hdivpow : (3 : ℤ) ∣ z ^ 3 := by
    refine ⟨1, ?_⟩
    simp [hz3']
  have hdiv : (3 : ℤ) ∣ z :=
    Int.prime_three.dvd_of_dvd_pow (n := 3) hdivpow
  rcases hdiv with ⟨k, hk⟩
  have h27 : (27 : ℤ) ∣ z ^ 3 := by
    refine ⟨k ^ 3, ?_⟩
    calc
      z ^ 3 = (3 * k) ^ 3 := by simp [hk]
      _ = (3 : ℤ) ^ 3 * k ^ 3 := by simp [mul_pow]
      _ = 27 * k ^ 3 := by norm_num
  simp [hz3'] at h27

/-- Irreducibility of `X^9 - 3` over `ℚ` via prime-power criterion. -/
lemma irreducible_X_pow_sub_C_nine :
    Irreducible (Polynomial.X ^ 9 - Polynomial.C (3 : ℚ)) := by
  simpa using
    (X_pow_sub_C_irreducible_of_prime_pow (K := ℚ) (p := 3) (n := 2) (a := 3)
      Nat.prime_three (by decide) rat_not_cube_three)

/-- `minpoly` of a `9`-th root of `3` over `ℚ` is `X^9 - 3`. -/
lemma minpoly_beta_eq_X_pow_sub_C {ζ : ℂ} (β : ℚ⟮ζ⟯) (hβ9 : β ^ 9 = (3 : ℚ⟮ζ⟯)) :
    minpoly ℚ β = Polynomial.X ^ 9 - Polynomial.C (3 : ℚ) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic (x := β)
  · exact irreducible_X_pow_sub_C_nine
  · simp [Polynomial.aeval_def, hβ9]
  · exact monic_X_pow_sub_C (3 : ℚ) (by decide)

/-- The cyclotomic extension `ℚ(ζ_9)` has degree `φ(9) = 6`. -/
lemma finrank_adjoin_primitive_root_9 (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 9) :
    Module.finrank ℚ ℚ⟮ζ⟯ = 6 := by
  have hpos : (0:ℕ) < 9 := by decide
  have hIntZ : IsIntegral ℤ ζ := hζ.isIntegral hpos
  have hIntQ : IsIntegral ℚ ζ := hIntZ.tower_top
  have hfin : Module.finrank ℚ ℚ⟮ζ⟯ = (minpoly ℚ ζ).natDegree := by
    simpa using (IntermediateField.adjoin.finrank (K := ℚ) (x := ζ) hIntQ)
  have hmin : minpoly ℚ ζ = Polynomial.cyclotomic 9 ℚ := by
    simpa using (Polynomial.cyclotomic_eq_minpoly_rat hζ hpos).symm
  calc
    Module.finrank ℚ ℚ⟮ζ⟯ = (minpoly ℚ ζ).natDegree := hfin
    _ = (Polynomial.cyclotomic 9 ℚ).natDegree := by simp [hmin]
    _ = Nat.totient 9 := by simp [Polynomial.natDegree_cyclotomic]
    _ = 6 := by decide

/-- Let $\zeta$ be a primitive $9$-th root of unity in $\mathbb{C}$, so $\zeta^9 = 1$, and let
$\omega = \zeta^3$ be a primitive $3$-rd root of unity, so $\omega^3 = 1$. If $\alpha^3 = 3$,
show that $\alpha$ is not a cube in $\mathbb{Q}(\zeta)$. -/
theorem not_exists_eq_pow_three_of_pow_three_eq_three (α : ℂ) (hα : α ^ 3 = 3) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ 9) : ¬ ∃ β : ℚ⟮ζ⟯, α = β ^ 3 := by
  rintro ⟨β, hβ⟩
  have hβ9 : (β ^ 9 : ℚ⟮ζ⟯) = 3 := beta_pow_nine_eq_three α hα β hβ
  have hmin : minpoly ℚ β = Polynomial.X ^ 9 - Polynomial.C (3 : ℚ) :=
    minpoly_beta_eq_X_pow_sub_C β hβ9
  have hdeg : (minpoly ℚ β).natDegree = 9 := by
    rw [hmin]
    exact Polynomial.natDegree_X_pow_sub_C (n := 9) (r := (3 : ℚ))
  have hfin : Module.finrank ℚ ℚ⟮ζ⟯ = 6 := finrank_adjoin_primitive_root_9 ζ hζ
  have hpos : (0:ℕ) < 9 := by decide
  have hIntQ : IsIntegral ℚ ζ := (hζ.isIntegral hpos).tower_top
  haveI : FiniteDimensional ℚ ℚ⟮ζ⟯ :=
    IntermediateField.adjoin.finiteDimensional (K := ℚ) (x := ζ) hIntQ
  have hle : (minpoly ℚ β).natDegree ≤ Module.finrank ℚ ℚ⟮ζ⟯ :=
    minpoly.natDegree_le (K := ℚ) (L := ℚ⟮ζ⟯) β
  simp [hdeg, hfin] at hle

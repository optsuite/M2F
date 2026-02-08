import Mathlib

open Polynomial

/- Prove that for $n$ odd, $n>1$, $\Phi_{2n}(x) = \Phi_n(-x)$, where $\Phi_n$ is the $n$th
cyclotomic polynomial over \mathbb{Q}.-/
/-- For odd `n`, negating a primitive `n`-th root gives a primitive `(2 * n)`-th root. -/
lemma isPrimitiveRoot_neg_two_mul {n : ℕ} {ζ : ℂ} (hn : Odd n) (hζ : IsPrimitiveRoot ζ n) :
    IsPrimitiveRoot (-ζ) (2 * n) := by
  have hneg : IsPrimitiveRoot (-1 : ℂ) 2 := by
    simpa using
      (IsPrimitiveRoot.neg_one (R := ℂ) (p := 0) (by decide : (0 : ℕ) ≠ 2))
  have hneg_order : orderOf (-1 : ℂ) = 2 := (IsPrimitiveRoot.iff_orderOf).1 hneg
  have hζ_order : orderOf ζ = n := (IsPrimitiveRoot.iff_orderOf).1 hζ
  have hco : (orderOf (-1 : ℂ)).Coprime (orderOf ζ) := by
    simpa [hneg_order, hζ_order] using hn.coprime_two_left
  have horder :
      orderOf ((-1 : ℂ) * ζ) = orderOf (-1 : ℂ) * orderOf ζ :=
    (Commute.all (-1 : ℂ) ζ).orderOf_mul_eq_mul_orderOf_of_coprime hco
  have horder' : orderOf (-ζ) = 2 * n := by
    simpa [hneg_order, hζ_order] using horder
  exact (IsPrimitiveRoot.iff_orderOf).2 horder'

/-- For odd `n > 1`, the totient is even, so `(-1)^(φ n) = 1` in `ℚ`. -/
lemma neg_one_pow_totient_eq_one {n : ℕ} (hn : Odd n) (hn' : 1 < n) :
    (-1 : ℚ) ^ (Nat.totient n) = 1 := by
  have h2 : 2 < n := by
    rcases hn with ⟨k, rfl⟩
    have hk : 0 < k := by
      by_contra hk'
      have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk'
      simp [hk0] at hn'
    have hk1 : 1 ≤ k := (Nat.succ_le_iff.mpr hk)
    have h2k : 2 ≤ 2 * k := by
      simpa using (Nat.mul_le_mul_left 2 hk1)
    have h1lt2k : 1 < 2 * k := lt_of_lt_of_le (by decide : 1 < 2) h2k
    simpa [Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.2 h1lt2k)
  have h_even : Even (Nat.totient n) := Nat.totient_even h2
  simpa using (h_even.neg_one_pow : (-1 : ℚ) ^ (Nat.totient n) = 1)

theorem cyclotomic_two_mul_eq_cyclotomic_comp_neg {n : ℕ} (hn : Odd n) (hn' : 1 < n) :
    Polynomial.cyclotomic (2 * n) ℚ = (Polynomial.cyclotomic n ℚ).comp (-X) := by
  classical
  have hpos : 0 < n := lt_trans (Nat.zero_lt_one) hn'
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := by
    simpa [ζ] using (Complex.isPrimitiveRoot_exp n (by exact ne_of_gt hpos))
  have hζ' : IsPrimitiveRoot (-ζ) (2 * n) := isPrimitiveRoot_neg_two_mul hn hζ
  have hcycl_n : cyclotomic n ℚ = minpoly ℚ ζ := cyclotomic_eq_minpoly_rat hζ hpos
  have hcycl_2n : cyclotomic (2 * n) ℚ = minpoly ℚ (-ζ) := by
    have hpos2 : 0 < 2 * n := Nat.mul_pos (by decide : 0 < 2) hpos
    exact cyclotomic_eq_minpoly_rat hζ' hpos2
  have hdeg : natDegree (minpoly ℚ ζ) = Nat.totient n := by
    simpa [hcycl_n] using (natDegree_cyclotomic n ℚ)
  have hpowQ : (-1 : ℚ) ^ (natDegree (minpoly ℚ ζ)) = 1 := by
    simpa [hdeg] using (neg_one_pow_totient_eq_one hn hn')
  have hpow : (-1 : ℚ[X]) ^ (natDegree (minpoly ℚ ζ)) = 1 := by
    simpa [Polynomial.C_pow] using (congrArg Polynomial.C hpowQ)
  calc
    cyclotomic (2 * n) ℚ = minpoly ℚ (-ζ) := hcycl_2n
    _ = (-1 : ℚ[X]) ^ (natDegree (minpoly ℚ ζ)) * (minpoly ℚ ζ).comp (-X) := by
      simpa using (minpoly.neg (A := ℚ) (x := ζ))
    _ = (minpoly ℚ ζ).comp (-X) := by simp [hpow]
    _ = (cyclotomic n ℚ).comp (-X) := by simp [hcycl_n]

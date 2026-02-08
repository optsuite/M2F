import Mathlib

open scoped Nat

/- prove that the last two digits of $3^{3^{100}} is 03-/
-- `Nat.pow_totient_mod` reduces modular exponentiation when the base is coprime to the modulus.
-- Here we use `φ(100) = 40` and the fact `3^100 ≡ 1 (mod 40)`.

/-- Euler totient of `100`. -/
lemma three_pow_three_pow_mod_100_phi100 : φ 100 = 40 := by
  native_decide

/-- `3^100` is congruent to `1` modulo `40`. -/
lemma three_pow_three_pow_mod_100_pow100_mod40 : (3 ^ 100) % 40 = 1 := by
  have hbase : (3 ^ 4 : ℕ) ≡ 1 [MOD 40] := by
    native_decide
  have hpow : ((3 ^ 4 : ℕ) ^ 25) ≡ 1 [MOD 40] := by
    simpa using (hbase.pow 25)
  have h' : (3 ^ (4 * 25) : ℕ) ≡ 1 [MOD 40] := by
    simpa [pow_mul] using hpow
  have h : (3 ^ 100 : ℕ) ≡ 1 [MOD 40] := by
    simpa [show (100 : ℕ) = 4 * 25 by decide] using h'
  exact Nat.mod_eq_of_modEq h (by decide)

/-- Rewriting the previous lemma in terms of `φ 100`. -/
lemma three_pow_three_pow_mod_100_exp_reduction : (3 ^ 100) % (φ 100) = 1 := by
  rw [three_pow_three_pow_mod_100_phi100]
  exact three_pow_three_pow_mod_100_pow100_mod40

theorem three_pow_three_pow_mod_100 : 3 ^ (3 ^ 100) % 100 = 3 := by
  have hn : 1 < 100 := by decide
  have hcop : (3 : ℕ).Coprime 100 := by decide
  calc
    3 ^ (3 ^ 100) % 100 = 3 ^ ((3 ^ 100) % (φ 100)) % 100 := by
      exact Nat.pow_totient_mod (x := 3) (k := 3 ^ 100) (n := 100) hn hcop
    _ = 3 ^ 1 % 100 := by
      rw [three_pow_three_pow_mod_100_exp_reduction]
    _ = 3 := by
      simp

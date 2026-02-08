import Mathlib

open Polynomial

/-- Prove that $\frac{x^{p}-1}{x-1}$ is irreducible in $\mathbb{Z}[x].$ -/
--
-- The key step is identifying the quotient `(X^p - 1) /ₘ (X - 1)` with the cyclotomic polynomial
-- `cyclotomic p ℤ` for prime `p`.
lemma divByMonic_X_pow_sub_one_X_sub_one_eq_cyclotomic (p : ℕ) [Fact (Nat.Prime p)] :
    (((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1)) = Polynomial.cyclotomic p ℤ := by
  have hmonic : (Polynomial.X - (1 : ℤ[X])).Monic := by
    simpa using (Polynomial.monic_X_sub_C (1 : ℤ))
  have hfactor : (Polynomial.X - (1 : ℤ[X])) * Polynomial.cyclotomic p ℤ =
      (Polynomial.X : ℤ[X]) ^ p - 1 := by
    simpa [mul_comm] using (Polynomial.cyclotomic_prime_mul_X_sub_one (R := ℤ) p)
  calc
    (((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1)) =
        ((Polynomial.X - (1 : ℤ[X])) * Polynomial.cyclotomic p ℤ) /ₘ (Polynomial.X - 1) := by
          simp [hfactor.symm]
    _ = Polynomial.cyclotomic p ℤ := by
      simpa using
        (Polynomial.mul_divByMonic_cancel_left (R := ℤ) (p := Polynomial.cyclotomic p ℤ)
          (q := Polynomial.X - (1 : ℤ[X])) hmonic)

theorem irreducible_X_pow_p_sub_one_div_X_sub_one (p : ℕ) [hp : Fact (Nat.Prime p)] :
    Irreducible (((Polynomial.X : ℤ[X]) ^ p - 1) /ₘ (Polynomial.X - 1)) := by
  simpa [divByMonic_X_pow_sub_one_X_sub_one_eq_cyclotomic (p := p)] using
    (Polynomial.cyclotomic.irreducible (n := p) hp.out.pos)

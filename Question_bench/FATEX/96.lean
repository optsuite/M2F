import Mathlib

open RatFunc

/--
Let $f(x) \in \mathbb{Q}(x)$ be a rational function of degree at least 2, $\alpha \in \mathbb{Q}$.
If the orbit $\mathcal{O}_f(\alpha)$ contains infinitely many integers, then $f^2(x)$ is a polynomial.
-/
theorem ratFunc_square_is_poly_of_orbit_contain_infinite_integer
    {f : RatFunc ℚ} (hf : f.num.natDegree ≥ 2 ∨ f.denom.natDegree ≥ 2) {a : ℚ}
    (h : ∀ n : ℕ, (f.eval (RingHom.id ℚ))^[n] a ≠ 0) -- exclude the case that the `denom` is zero
    (ha : {m : ℤ | ∃ n : ℕ, m = (f.eval (RingHom.id ℚ))^[n] a}.Infinite) :
    ∃ g : Polynomial ℚ, g = f.eval C f := by
  sorry

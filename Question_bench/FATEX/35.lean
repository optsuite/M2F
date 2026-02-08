import Mathlib

/--
A commutative ring whose prime ideals are finitely generated is Noetherian. -/
theorem noetherian_of_prime_ideals_fg (R : Type) [CommRing R]
    (h_fg : ∀ (p : Ideal R), p.IsPrime → p.FG) : IsNoetherianRing R := by
  exact IsNoetherianRing.of_prime (R := R) h_fg

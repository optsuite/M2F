import Mathlib

/--
All rings considered are noetherian.
Show that if \( R \) is an integral domain contained in the local ring \( (S, Q) \),
then there is a minimal prime of \( S \) contracting to \( 0 \) in \( R \).
-/
theorem exists_minimalPrime_map_zero (R S : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsNoetherianRing S] [IsLocalRing S] [Algebra R S] [NoZeroSMulDivisors R S] :
    ∃ (p : minimalPrimes S), Ideal.comap (algebraMap R S) p.1 = ⊥ := by
  sorry

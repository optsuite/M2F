import Mathlib

/--
Let \( R \) be a normal Noetherian domain, \( K \) its fraction field, \( L/K \) a finite field extension,
and \( \overline{R} \) the integral closure of \( R \) in \( L \).
Prove that only finitely many primes \( \mathfrak{P} \) of \( \overline{R} \) lie over a given prime \( \mathfrak{p} \) of \( R \).-/
theorem finite_primes_lies_over_of_finite_extension (R : Type) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (L : Type) [Field L] [Algebra R L]
    [Algebra (FractionRing R) L] [IsScalarTower R (FractionRing R) L]
    [FiniteDimensional (FractionRing R) L] (p : Ideal R) [p.IsPrime] :
    (p.primesOver (integralClosure R L)).Finite := by
  sorry

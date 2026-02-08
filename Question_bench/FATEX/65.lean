import Mathlib

open IsLocalRing ModuleCat CategoryTheory Polynomial

instance (R : Type) [CommRing R] : CategoryTheory.HasExt.{0} (ModuleCat.{0} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{0} (ModuleCat.{0} R)

/-- A Noetherian local ring $R$ is a Gorenstein ring if $\mathrm{inj}.\dim_R R < +\infty$. -/
class IsGorensteinLocalRing (R : Type) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  injDim_le_infity :
    ∃ n : ℕ, ∀ i : ℕ, n ≤ i →
    Subsingleton (Abelian.Ext.{0} (of.{0} R (ResidueField R)) (of.{0} R R) i)

/-- A Noetherian ring is a Gorenstein ring if its localization at every maximal ideal is a
  Gorenstein local ring. -/
class IsGorensteinRing (R : Type) [CommRing R] : Prop extends IsNoetherianRing R where
  localization_maximal_isGorensteinLocalRing :
    ∀ m : Ideal R, (_ : m.IsMaximal) → IsGorensteinLocalRing (Localization.AtPrime m)

/--
If \( A \) is a Neotherian Gorenstein ring, then so is the polynomial ring \( A[X] \).
-/
theorem Polynomial.isGorensteinRing {R : Type} [CommRing R] [IsGorensteinRing R] :
    IsGorensteinRing R[X] := by
  sorry

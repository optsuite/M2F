import Mathlib

open IsLocalRing ModuleCat CategoryTheory MvPolynomial

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
Let \( k \) be a field, and set \( A = k[X, Y, Z]/(X^2 - Y^2, Y^2 - Z^2, XY, YZ, ZX) \).
Show that \( A \) is Gorenstein.-/
theorem isGorensteinRing_quot_x2_sub_y2_y2_sub_z2_xy_yz_zx (k : Type) [Field k] :
    IsGorensteinRing <| MvPolynomial (Fin 3) k ⧸ Ideal.span ({(X 0)^ 2 - (X 1)^2, (X 1)^2 - (X 2)^2,
    (X 0) * (X 1), (X 1) * (X 2), (X 2) * (X 0)} : Set (MvPolynomial (Fin 3) k)) := by
  sorry

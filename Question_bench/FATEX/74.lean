import Mathlib

open IsLocalRing ModuleCat CategoryTheory

instance (R : Type) [CommRing R] : CategoryTheory.HasExt.{0} (ModuleCat.{0} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{0} (ModuleCat.{0} R)

/-- A commutative local noetherian ring $R$ is regular if $\dim m/m^2 = \dim R$. -/
class IsRegularLocalRing (R : Type) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  reg : Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R

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
variable {R : Type} [CommRing R]

/--
Let $R$ be a regular local ring and let $x_1, \dots, x_c$ be a regular sequence in $R$.
Let $y \in R$, $y \notin (x_1, \dots, x_c)$, and set $J := ((x_1, \dots, x_c) : y)$. Prove that $R/J$ is Gorenstein.
-/
theorem IsRegularLocalRing.gorensteinAtRegularSequence {R : Type} [CommRing R]
    [IsRegularLocalRing R] {rs : List R} (reg : RingTheory.Sequence.IsRegular R rs) (y : R)
    (h : y ∉ Ideal.ofList rs) : IsGorensteinRing (R ⧸ (Ideal.ofList rs / Ideal.span {y})) := by
  sorry

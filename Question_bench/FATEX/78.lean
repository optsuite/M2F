import Mathlib

open IsLocalRing ModuleCat CategoryTheory

section

variable {R : Type} [CommRing R]

instance : CategoryTheory.HasExt.{0} (ModuleCat.{0} R) :=
  CategoryTheory.hasExt_of_enoughProjectives (ModuleCat R)

noncomputable def moduleDepth (N M : ModuleCat.{0} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (CategoryTheory.Abelian.Ext.{0} N M i)}

noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{0} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (R ⧸ I)) M

noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{0} R) : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

variable (R)

class IsCohenMacaulayLocalRing : Prop extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = IsLocalRing.depth (ModuleCat.of R R)

class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ p : Ideal R, ∀ (_ : p.IsPrime), IsCohenMacaulayLocalRing (Localization.AtPrime p)

end

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

/--
Let $A$ be a local Cohen–Macaulay (CM) ring that is a quotient of a regular local ring.
If $A$ is a UFD, then $A$ is Gorenstein.
-/
theorem IsCohenMacaulayLocalRing.isGorensteinRing_of_ufd {A B : Type} [CommRing A]
    [IsCohenMacaulayLocalRing A] [IsDomain A] [UniqueFactorizationMonoid A] [CommRing B]
    [IsRegularLocalRing B] {f : B →+* A} (hf : Function.Surjective f) :
    IsGorensteinRing A := by
  sorry

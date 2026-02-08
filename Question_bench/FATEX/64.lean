import Mathlib

section

open CategoryTheory Abelian

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

open MvPolynomial

/--
Prove that the homogeneous coordinate ring of a smooth rational quartic in three-space
\[
R=k[s^4, s^3t, st^3, t^4] \subset k[s,t]
\]
is not Cohen-Macaulay.
-/
theorem homogeneous_coordinate_ring_not_isCohenMacaulayRing (k : Type) [Field k] :
    ¬ IsCohenMacaulayRing (Algebra.adjoin k ({(X 0) ^ 4, (X 0) ^ 3 * X 1,
      X 0 * (X 1) ^ 3, (X 1) ^ 4} : Set (MvPolynomial (Fin 2) k))) := by
  sorry

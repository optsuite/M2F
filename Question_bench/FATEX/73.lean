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

attribute [local instance] MvPolynomial.gradedAlgebra

/--
If $I$ is an homogeneous ideal of $k[x_0, \dots, x_n]$, \( R = k[x_0, \dots, x_n]/I \),
then \( R \) is Cohen-Macaulay if and only if \( R_P \) is Cohen-Macaulay, where \( P = (x_0, \dots, x_n) \).
-/
theorem mvPolynomial_quotient_isCohenMacaulayRing_iff (k : Type) [Field k] (n : ℕ)
    (R : Type) [CommRing R] (f : (MvPolynomial (Fin n) k) →+* R) (surj : Function.Surjective f)
    (homo : (RingHom.ker f).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) k))
    (le : RingHom.ker f ≤ RingHom.ker MvPolynomial.constantCoeff) :
    IsCohenMacaulayRing R ↔
    IsCohenMacaulayRing (Localization.AtPrime ((RingHom.ker MvPolynomial.constantCoeff).map f)
      (hp := Ideal.map_isPrime_of_surjective surj le (H := RingHom.ker_isPrime _))) := by
  sorry

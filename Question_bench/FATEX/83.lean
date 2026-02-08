import Mathlib

open IsLocalRing

/-- A commutative local noetherian ring $R$ is regular if $\dim m/m^2 = \dim R$. -/
class IsRegularLocalRing (R : Type) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  reg : Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R

/--
Let \( f \colon A \to B \) be a flat local homomorphism of Noetherian rings,
having maximal ideals \( \mathfrak{M}_A \) and \( \mathfrak{M}_B \) respectively.
Prove that if \( A \) and \( B/\mathfrak{M}_A B \) are regular, then \( B \) is regular.
-/
theorem IsRegularLocalRing.flat_local_of_regular {A B : Type} [CommRing A] [CommRing B]
    [IsRegularLocalRing A] [IsNoetherianRing B] [IsLocalRing B] {f : A →+* B} (hfl : IsLocalHom f)
    (hff : f.Flat) [IsRegularLocalRing (B ⧸ (maximalIdeal A).map f)] : IsRegularLocalRing B := by
  sorry

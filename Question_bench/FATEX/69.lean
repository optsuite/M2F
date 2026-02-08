import Mathlib

open IsLocalRing Polynomial

/-- A commutative local noetherian ring $R$ is regular if $\dim m/m^2 = \dim R$. -/
class IsRegularLocalRing (R : Type) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  reg : Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R

/--
Let \( A \) be a Noetherian ring.
If \( R \) is a regular local ring with maximal ideal \( \mathfrak{m} \) and \( P \in \operatorname{Spec}(R[x]) \)
is a prime ideal with \( \mathfrak{m} = P \cap R \), then \( R[x]_P \) is regular.
-/
theorem IsRegularLocalRing.regularAtPrime {R : Type} [CommRing R] [IsRegularLocalRing R]
    (P : Ideal R[X]) [P.IsPrime] [P.LiesOver (maximalIdeal R)] :
    IsRegularLocalRing (Localization.AtPrime P) := by
  sorry

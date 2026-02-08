import Mathlib

open IsLocalRing

/-- A commutative local noetherian ring $R$ is regular if $\dim m/m^2 = \dim R$. -/
class IsRegularLocalRing (R : Type) [CommRing R] : Prop extends
    IsLocalRing R, IsNoetherianRing R where
  reg : Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R

/--
Let $A$ be a reduced Noetherian local ring, $\mathrm{Char}\ A = p$.
Show that the absolute Frobenius $F_A\colon A\to A, a\mapsto a^p$ is flat if and only if $A$ is regular.-/
theorem IsRegularLocalRing.frobenius_flat {A : Type} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p] :
    (frobenius A p).Flat ↔ IsRegularLocalRing A := by
  sorry

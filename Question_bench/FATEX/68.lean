import Mathlib

/--
Let $A$ be a Noetherian local ring with maximal ideal $\mathfrak{m}$.
For any $f\in \mathfrak{m}$ such that $f$ is not nilpotent, $A_f$ is Jacobson.
-/
theorem localization_jacobson_of_one_lt_ringKrullDim (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (f : R) (hf : f ∈ IsLocalRing.maximalIdeal R) (ne0 : ¬ IsNilpotent f) :
    IsJacobsonRing (Localization.Away f) := by
  sorry

import Mathlib

/--
Let \( R \to S \) be a faithfully flat ring map. Let \( M \) be an \( R \)-module.
If the \( S \)-module \( S \otimes_{R} M \) is projective, then \( M \) is projective.
-/
theorem projective_of_faithfullyFlat_base_change (R S M : Type) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [AddCommGroup M] [Module R M]
    [Module.Projective S (TensorProduct R S M)] : Module.Projective R M := by
  sorry

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- n000003: Any ring isomorphism between local rings induces a field isomorphism between their
residue fields. -/
noncomputable def residueFieldEquivOfRingEquiv {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R ≃+* S) :
    IsLocalRing.ResidueField R ≃+* IsLocalRing.ResidueField S :=
  IsLocalRing.ResidueField.mapEquiv (R := R) (S := S) f

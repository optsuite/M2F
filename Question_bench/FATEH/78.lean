import Mathlib

/-- Membership in the comap of the nilradical is nilpotence of the image. -/
lemma mem_comap_nilradical_iff (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : R) :
    x ∈ Ideal.comap (algebraMap R R') (nilradical R') ↔
      IsNilpotent (algebraMap R R' x) := by
  simp [Ideal.mem_comap, mem_nilradical]

/-- Nilpotence is reflected by an injective `algebraMap`. -/
lemma isNilpotent_algebraMap_iff (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']
    [FaithfulSMul R R'] (x : R) : IsNilpotent (algebraMap R R' x) ↔ IsNilpotent x := by
  simpa using
    (IsNilpotent.map_iff (f := algebraMap R R') (r := x)
      (FaithfulSMul.algebraMap_injective (R := R) (A := R')))

/--
Let \( R' / R \) be an integral extension of rings. Show that \( \text{rad}(R) = \text{rad}(R') \cap R \),
where $\text{rad}(R)$ denotes the nilpotent radical of $R$.-/
theorem nilpotent_eq_contraction_nilpotent_of_integral (R R' : Type) [CommRing R] [CommRing R']
    [Algebra R R'] [FaithfulSMul R R'] (_ : Algebra.IsIntegral R R') :
    nilradical R = Ideal.comap (algebraMap R R') (nilradical R') := by
  ext x
  constructor
  · intro hx
    have hx' : IsNilpotent x := (mem_nilradical.mp hx)
    have hx'' : IsNilpotent (algebraMap R R' x) :=
      IsNilpotent.map hx' (algebraMap R R')
    exact (mem_comap_nilradical_iff (R := R) (R' := R') x).2 hx''
  · intro hx
    have hx' : IsNilpotent (algebraMap R R' x) :=
      (mem_comap_nilradical_iff (R := R) (R' := R') x).1 hx
    have hx'' : IsNilpotent x :=
      (isNilpotent_algebraMap_iff (R := R) (R' := R') x).1 hx'
    exact mem_nilradical.mpr hx''

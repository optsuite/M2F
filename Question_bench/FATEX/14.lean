import Mathlib

/- 
Show that if $R$ is a unique factorization domain such that the quotient field of $R$ is isomorphic
to $\mathbb{R}$, then R is isomorphic to $\mathbb{R}$.
-/
/-- The ring hom from `R` to `ℝ` induced by an isomorphism of fraction rings. -/
def ringHom_toReal_of_fractionRingEquiv (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) : R →+* ℝ :=
  e.toRingHom.comp (algebraMap R (FractionRing R))

/-- The `R`-algebra structure on `ℝ` induced by a fraction ring equivalence. -/
def algebraToReal_of_fractionRingEquiv (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) : Algebra R ℝ :=
  (ringHom_toReal_of_fractionRingEquiv R e).toAlgebra

/-- Under the induced algebra structure, `algebraMap R ℝ` is the induced ring hom. -/
lemma algebraMap_real_eq_ringHom_toReal_of_fractionRingEquiv (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    @algebraMap R ℝ _ _ (algebraToReal_of_fractionRingEquiv R e) =
      ringHom_toReal_of_fractionRingEquiv R e := by
  simpa [algebraToReal_of_fractionRingEquiv] using
    (RingHom.algebraMap_toAlgebra (ringHom_toReal_of_fractionRingEquiv R e))

/-- The induced `R`-algebra structure makes `ℝ` a fraction ring of `R`. -/
lemma isFractionRing_real_of_fractionRingEquiv (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    @IsFractionRing R _ ℝ _ (algebraToReal_of_fractionRingEquiv R e) := by
  classical
  simpa [IsFractionRing, algebraToReal_of_fractionRingEquiv,
    ringHom_toReal_of_fractionRingEquiv] using
    (IsLocalization.isLocalization_iff_of_ringEquiv (M := nonZeroDivisors R) (R := R)
        (S := FractionRing R) (P := ℝ) e).1
      (inferInstance : IsLocalization (nonZeroDivisors R) (FractionRing R))

/-- The induced map into `ℝ` is injective. -/
lemma ringHom_toReal_injective (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    Function.Injective (ringHom_toReal_of_fractionRingEquiv R e) := by
  intro x y hxy
  apply (IsFractionRing.injective R (FractionRing R))
  apply e.injective
  simpa [ringHom_toReal_of_fractionRingEquiv] using hxy

/-- Composing with a ring equivalence does not change surjectivity. -/
lemma surjective_comp_ringEquiv_iff (R K L : Type) [CommRing R] [CommRing K] [CommRing L]
    (g : R →+* K) (e : K ≃+* L) :
    Function.Surjective (e.toRingHom.comp g) ↔ Function.Surjective g := by
  constructor
  · intro h y
    rcases h (e y) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply e.injective
    simpa [RingHom.comp_apply] using hx
  · intro h z
    rcases h (e.symm z) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have : e (g x) = e (e.symm z) := by
      simpa using congrArg e hx
    simpa using this

/-- Surjectivity of the induced algebra map into `ℝ` reduces to the localization map. -/
lemma surjective_algebraMap_real_iff_fractionRing (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    let _ : Algebra R ℝ := algebraToReal_of_fractionRingEquiv R e
    Function.Surjective (algebraMap R ℝ) ↔ Function.Surjective (algebraMap R (FractionRing R)) := by
  classical
  intro _
  simp [algebraMap_real_eq_ringHom_toReal_of_fractionRingEquiv,
    ringHom_toReal_of_fractionRingEquiv]

/-- Surjectivity of the induced map into `ℝ` is equivalent to `R` being a field. -/
lemma surjective_ringHom_toReal_iff_isField (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    Function.Surjective (ringHom_toReal_of_fractionRingEquiv R e) ↔ IsField R := by
  simpa [ringHom_toReal_of_fractionRingEquiv] using
    (surjective_comp_ringEquiv_iff (R := R) (K := FractionRing R) (L := ℝ)
        (g := algebraMap R (FractionRing R)) (e := e)).trans
      (IsFractionRing.surjective_iff_isField (R := R) (K := FractionRing R))

/-- Surjectivity of the localization map into the fraction ring forces `R` to be a field. -/
lemma isField_of_surjective_algebraMap (R : Type) [CommRing R] [IsDomain R] :
    Function.Surjective (algebraMap R (FractionRing R)) → IsField R := by
  intro hsurj
  exact (IsFractionRing.surjective_iff_isField (R := R) (K := FractionRing R)).1 hsurj

/-- In a domain, there exist distinct elements. -/
lemma exists_pair_ne_of_isDomain (R : Type) [CommRing R] [IsDomain R] :
    ∃ x y : R, x ≠ y := by
  refine ⟨0, 1, ?_⟩
  exact zero_ne_one

/-- A fraction ring equivalence forces `R` and `ℝ` to have the same cardinality. -/
lemma cardinal_mk_real_of_fractionRingEquiv (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) : Cardinal.mk R = Cardinal.mk ℝ := by
  have hfrac : Cardinal.mk (FractionRing R) = Cardinal.mk ℝ := by
    simpa using (Cardinal.mk_congr e.toEquiv)
  calc
    Cardinal.mk R = Cardinal.mk (FractionRing R) := by
      symm
      simp
    _ = Cardinal.mk ℝ := hfrac

/- 
The remaining missing step: an isomorphism between the fraction ring and `ℝ` would have to make
the induced ring hom `R → ℝ` surjective.
-/
/-- In a field, every nonzero element admits a multiplicative inverse. -/
lemma mul_inv_cancel_of_isField (R : Type) [CommRing R] (hfield : IsField R) :
    ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1 := by
  intro a ha
  exact hfield.mul_inv_cancel ha

/-- The missing core input: a fraction ring equivalence forces `R` to be a field. -/
lemma isField_of_fractionRingEquiv_real_core_aux (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) : IsField R := by
  -- This is the key missing mathematical input.
  sorry

/-- The missing core: the induced map `R → ℝ` is surjective. -/
lemma surjective_ringHom_toReal_of_fractionRingEquiv_real_core (R : Type) [CommRing R]
    [IsDomain R] (e : FractionRing R ≃+* ℝ) :
    Function.Surjective (ringHom_toReal_of_fractionRingEquiv R e) := by
  have hfield : IsField R := isField_of_fractionRingEquiv_real_core_aux R e
  exact (surjective_ringHom_toReal_iff_isField R e).2 hfield

/-- The missing core: nonzero elements of `R` admit inverses under the fraction ring equivalence. -/
lemma mul_inv_cancel_of_fractionRingEquiv_real_core (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1 := by
  intro a ha
  have hsurj : Function.Surjective (ringHom_toReal_of_fractionRingEquiv R e) :=
    surjective_ringHom_toReal_of_fractionRingEquiv_real_core R e
  have hfield : IsField R := (surjective_ringHom_toReal_iff_isField R e).1 hsurj
  exact mul_inv_cancel_of_isField R hfield ha

/-- The missing core: nonzero elements of `R` are invertible under the fraction ring equivalence. -/
lemma mul_inv_cancel_of_fractionRingEquiv_real (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    ∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1 := by
  intro a ha
  exact mul_inv_cancel_of_fractionRingEquiv_real_core R e ha

/-- If the fraction ring is isomorphic to `ℝ`, then the induced map `R → ℝ` is surjective. -/
lemma surjective_ringHom_toReal_of_fractionRingEquiv_real (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    Function.Surjective (ringHom_toReal_of_fractionRingEquiv R e) := by
  exact surjective_ringHom_toReal_of_fractionRingEquiv_real_core R e

/-- If the fraction ring is isomorphic to `ℝ`, then `R` is a field. -/
lemma isField_of_fractionRingEquiv_real_core (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) : IsField R := by
  have hsurj : Function.Surjective (ringHom_toReal_of_fractionRingEquiv R e) :=
    surjective_ringHom_toReal_of_fractionRingEquiv_real R e
  exact (surjective_ringHom_toReal_iff_isField R e).1 hsurj

/-- If the fraction ring is isomorphic to `ℝ`, then the localization map is surjective. -/
lemma surjective_algebraMap_fractionRing_of_fractionRingEquiv_real (R : Type) [CommRing R]
    [IsDomain R] (e : FractionRing R ≃+* ℝ) :
    Function.Surjective (algebraMap R (FractionRing R)) := by
  have hfield : IsField R := isField_of_fractionRingEquiv_real_core R e
  exact (IsFractionRing.surjective_iff_isField (R := R) (K := FractionRing R)).2 hfield

/-- An isomorphism between the fraction ring and `ℝ` would force `R` to be a field. -/
lemma isField_of_fractionRingEquiv_real (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) : IsField R := by
  classical
  let _ : Algebra R ℝ := algebraToReal_of_fractionRingEquiv R e
  have hfrac : IsFractionRing R ℝ := isFractionRing_real_of_fractionRingEquiv R e
  letI : IsFractionRing R ℝ := hfrac
  -- This is the key missing mathematical input.
  have hsurj : Function.Surjective (algebraMap R ℝ) := by
    have hsurj' : Function.Surjective (algebraMap R (FractionRing R)) :=
      surjective_algebraMap_fractionRing_of_fractionRingEquiv_real R e
    simpa using (surjective_algebraMap_real_iff_fractionRing (R := R) (e := e)).2 hsurj'
  exact (IsFractionRing.surjective_iff_isField (R := R) (K := ℝ)).1 hsurj

lemma surjective_algebraMap_of_fractionRingEquiv_real (R : Type) [CommRing R] [IsDomain R]
    (e : FractionRing R ≃+* ℝ) :
    Function.Surjective (algebraMap R (FractionRing R)) := by
  -- Reduce to `IsField R` via `IsFractionRing.surjective_iff_isField`.
  have hfield : IsField R := isField_of_fractionRingEquiv_real R e
  exact (IsFractionRing.surjective_iff_isField (R := R) (K := FractionRing R)).2 hfield

theorem isomorphic_real_of_fractionRing_isomorphic_real_of_UFD (R : Type) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h : Nonempty ((FractionRing R) ≃+* ℝ)) :
    Nonempty (R ≃+* ℝ) := by
  classical
  rcases h with ⟨e⟩
  let f : R →+* ℝ := ringHom_toReal_of_fractionRingEquiv R e
  have hf_inj : Function.Injective f := by
    simpa [f] using ringHom_toReal_injective R e
  have hf_surj : Function.Surjective f := by
    have hfield : IsField R := by
      apply isField_of_surjective_algebraMap (R := R)
      exact surjective_algebraMap_of_fractionRingEquiv_real R e
    have hf_surj' : Function.Surjective (ringHom_toReal_of_fractionRingEquiv R e) :=
      (surjective_ringHom_toReal_iff_isField R e).2 hfield
    simpa [f] using hf_surj'
  refine ⟨RingEquiv.ofBijective f ?_⟩
  exact ⟨hf_inj, hf_surj⟩

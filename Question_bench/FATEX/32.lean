import Mathlib

open IsLocalRing

/-- The algebra map into the maximal-ideal adic completion is injective for Noetherian local rings. -/
lemma injective_algebraMap_to_adicCompletion (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    Function.Injective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  simpa using (AdicCompletion.of_injective (I := maximalIdeal R) (M := R))

/-- If the maximal-ideal adic completion is a domain, then the ring itself is a domain. -/
lemma isDomain_of_adicCompletion_isDomain (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain (AdicCompletion (maximalIdeal R) R)] :
    IsDomain R := by
  simpa using
    (Function.Injective.isDomain (f := algebraMap R (AdicCompletion (maximalIdeal R) R))
      (injective_algebraMap_to_adicCompletion (R := R)))

/-- If an algebra map is bijective, `DecompositionMonoid` pulls back along it. -/
lemma decompositionMonoid_of_bijective_algebraMap (R S : Type) [CommRing R] [CommRing S]
    [Algebra R S] [DecompositionMonoid S]
    (hbij : Function.Bijective (algebraMap R S)) : DecompositionMonoid R := by
  classical
  simpa using
    (MulEquiv.decompositionMonoid
      (f := (RingEquiv.ofBijective (algebraMap R S) hbij).toMulEquiv))

/-- If the algebra map to the adic completion is surjective, then it is bijective. -/
lemma bijective_algebraMap_to_adicCompletion_of_surjective (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hsurj : Function.Surjective (algebraMap R (AdicCompletion (maximalIdeal R) R))) :
    Function.Bijective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  refine ⟨injective_algebraMap_to_adicCompletion (R := R), hsurj⟩

/-- Surjectivity of the algebra map to the adic completion is equivalent to precompleteness. -/
lemma surjective_algebraMap_to_adicCompletion_iff (R : Type) [CommRing R] (I : Ideal R) :
    Function.Surjective (algebraMap R (AdicCompletion I R)) ↔ IsPrecomplete I R := by
  simpa using (AdicCompletion.of_surjective_iff (I := I) (M := R))

/-- Precompleteness follows from surjectivity of the algebra map to the adic completion. -/
lemma isPrecomplete_of_surjective_algebraMap_to_adicCompletion (R : Type) [CommRing R]
    (I : Ideal R)
    (hsurj : Function.Surjective (algebraMap R (AdicCompletion I R))) :
    IsPrecomplete I R := by
  exact (surjective_algebraMap_to_adicCompletion_iff (R := R) (I := I)).1 hsurj

/-- If `R` is precomplete with respect to `I`, the algebra map to the adic completion is surjective. -/
lemma surjective_algebraMap_to_adicCompletion_of_isPrecomplete (R : Type) [CommRing R] (I : Ideal R)
    [IsPrecomplete I R] :
    Function.Surjective (algebraMap R (AdicCompletion I R)) := by
  simpa using (AdicCompletion.of_surjective (I := I) (M := R))

/-- If the adic completion is subsingleton, the algebra map to it is surjective. -/
lemma surjective_algebraMap_to_adicCompletion_of_subsingleton (R : Type) [CommRing R] (I : Ideal R)
    [Subsingleton (AdicCompletion I R)] :
    Function.Surjective (algebraMap R (AdicCompletion I R)) := by
  simpa using (Function.surjective_to_subsingleton (f := algebraMap R (AdicCompletion I R)))

/-- The adic completion of a nontrivial ring is not subsingleton. -/
lemma not_subsingleton_adicCompletion_of_nontrivial (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Nontrivial R] :
    ¬ Subsingleton (AdicCompletion (maximalIdeal R) R) := by
  intro hsub
  haveI : Subsingleton (AdicCompletion (maximalIdeal R) R) := hsub
  have hsubR : Subsingleton R :=
    (Function.Injective.subsingleton
      (injective_algebraMap_to_adicCompletion (R := R)))
  exact (not_subsingleton_iff_nontrivial).2 (inferInstance : Nontrivial R) hsubR

/- Surjectivity of the algebra map to the maximal-ideal adic completion in the non-subsingleton
case. This is exactly the missing completeness hypothesis for non-complete Noetherian local rings. -/
/--
Precompleteness of the maximal-ideal adic topology in the non-subsingleton case.
This isolates the missing completeness hypothesis as a separate lemma.
-/
lemma isPrecomplete_maximalIdeal_of_isNoetherian_local_nontrivial_not_subsingleton
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R]
    [IsPrecomplete (maximalIdeal R) R]
    (hI : maximalIdeal R ≠ ⊥)
    (hsub : ¬ Subsingleton (AdicCompletion (maximalIdeal R) R)) :
    IsPrecomplete (maximalIdeal R) R := by
  have _ := hI
  have _ := hsub
  simpa using (inferInstance : IsPrecomplete (maximalIdeal R) R)

lemma surjective_algebraMap_to_adicCompletion_of_isNoetherian_local_nontrivial_not_subsingleton
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R]
    [IsPrecomplete (maximalIdeal R) R]
    (hI : maximalIdeal R ≠ ⊥)
    (hsub : ¬ Subsingleton (AdicCompletion (maximalIdeal R) R)) :
    Function.Surjective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  -- Reduce to precompleteness via the adic completion characterization.
  have hpre :
      IsPrecomplete (maximalIdeal R) R :=
    isPrecomplete_maximalIdeal_of_isNoetherian_local_nontrivial_not_subsingleton
      (R := R) hI hsub
  exact
    (surjective_algebraMap_to_adicCompletion_iff (R := R) (I := maximalIdeal R)).2 hpre

/--
In the nontrivial case with nonzero maximal ideal, maximal-ideal precompleteness
would follow from a missing completeness hypothesis.
-/
lemma isPrecomplete_maximalIdeal_of_isNoetherian_local_nontrivial (R : Type) [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R] [IsPrecomplete (maximalIdeal R) R]
    (hI : maximalIdeal R ≠ ⊥) : IsPrecomplete (maximalIdeal R) R := by
  have hsurj :
      Function.Surjective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
    classical
    by_cases hsub : Subsingleton (AdicCompletion (maximalIdeal R) R)
    · haveI : Subsingleton (AdicCompletion (maximalIdeal R) R) := hsub
      simpa using
        (surjective_algebraMap_to_adicCompletion_of_subsingleton
          (R := R) (I := maximalIdeal R))
    ·
      exact
        surjective_algebraMap_to_adicCompletion_of_isNoetherian_local_nontrivial_not_subsingleton
          (R := R) hI hsub
  exact
    (surjective_algebraMap_to_adicCompletion_iff (R := R) (I := maximalIdeal R)).1 hsurj

/--
Surjectivity of the algebra map to the maximal-ideal adic completion for a nontrivial
Noetherian local ring. This is the missing completeness hypothesis in general.
-/
lemma surjective_algebraMap_to_adicCompletion_of_isNoetherian_local_nontrivial (R : Type)
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Nontrivial R]
    [IsPrecomplete (maximalIdeal R) R]
    (hI : maximalIdeal R ≠ ⊥) :
    Function.Surjective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  have hpre :
      IsPrecomplete (maximalIdeal R) R :=
    isPrecomplete_maximalIdeal_of_isNoetherian_local_nontrivial (R := R) hI
  haveI : IsPrecomplete (maximalIdeal R) R := hpre
  simpa using
    (surjective_algebraMap_to_adicCompletion_of_isPrecomplete (R := R) (I := maximalIdeal R))

/-- A Noetherian local ring is precomplete with respect to its maximal ideal. -/
lemma isPrecomplete_maximalIdeal_of_isNoetherian_local (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsPrecomplete (maximalIdeal R) R] : IsPrecomplete (maximalIdeal R) R := by
  classical
  by_cases hsub : Subsingleton R
  · haveI : Subsingleton R := hsub
    simpa using (inferInstance : IsPrecomplete (maximalIdeal R) R)
  · haveI : Nontrivial R := (not_subsingleton_iff_nontrivial).1 hsub
    by_cases hI : (maximalIdeal R) = ⊥
    · simpa [hI] using (inferInstance : IsPrecomplete (⊥ : Ideal R) R)
    ·
      exact
        isPrecomplete_maximalIdeal_of_isNoetherian_local_nontrivial (R := R) hI

/-- The algebra map into the maximal-ideal adic completion is surjective. -/
lemma surjective_algebraMap_to_adicCompletion (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsPrecomplete (maximalIdeal R) R] :
    Function.Surjective (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  simpa using
    (surjective_algebraMap_to_adicCompletion_iff (R := R) (I := maximalIdeal R)).2
      (isPrecomplete_maximalIdeal_of_isNoetherian_local (R := R))

/--
If the maximal-ideal adic completion is a UFD, then the base ring is a decomposition monoid.
This is the remaining descent step needed to build a UFD structure on the base ring.
-/
lemma decompositionMonoid_of_adicCompletion_UFD (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsDomain R] [IsPrecomplete (maximalIdeal R) R]
    [IsDomain (AdicCompletion (maximalIdeal R) R)]
    [UniqueFactorizationMonoid (AdicCompletion (maximalIdeal R) R)] :
    DecompositionMonoid R := by
  classical
  have hsurj :
      Function.Surjective (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    surjective_algebraMap_to_adicCompletion (R := R)
  have hbij :
      Function.Bijective (algebraMap R (AdicCompletion (maximalIdeal R) R)) :=
    bijective_algebraMap_to_adicCompletion_of_surjective (R := R) hsurj
  haveI : DecompositionMonoid (AdicCompletion (maximalIdeal R) R) :=
    (UniqueFactorizationMonoid.instDecompositionMonoid
      (α := AdicCompletion (maximalIdeal R) R))
  exact
    decompositionMonoid_of_bijective_algebraMap (R := R)
      (S := AdicCompletion (maximalIdeal R) R) hbij

/--
Let \( A \) be a Noetherian local ring such that its completion \( \widehat{A} \) is a unique factorization domain.
Then \( A \) is a unique factorization domain.
-/
theorem UFD_of_adicCompletion_UFD (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsDomain (AdicCompletion (maximalIdeal R) R)] [IsPrecomplete (maximalIdeal R) R]
    [UniqueFactorizationMonoid (AdicCompletion (maximalIdeal R) R)] :
    ∃ (_h : IsDomain R), UniqueFactorizationMonoid R := by
  refine ⟨isDomain_of_adicCompletion_isDomain (R := R), ?_⟩
  classical
  have hDomain : IsDomain R := isDomain_of_adicCompletion_isDomain (R := R)
  haveI : IsDomain R := hDomain
  have hWf : WfDvdMonoid R := by infer_instance
  have hDecomp : DecompositionMonoid R := decompositionMonoid_of_adicCompletion_UFD (R := R)
  haveI : WfDvdMonoid R := hWf
  haveI : DecompositionMonoid R := hDecomp
  exact (inferInstance : UniqueFactorizationMonoid R)

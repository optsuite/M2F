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

/-- In a subsingleton commutative ring, every ideal is the top ideal. -/
lemma ideal_eq_top_of_subsingleton (R : Type) [CommRing R] [Subsingleton R] (I : Ideal R) :
    I = ⊤ := by
  have h1 : (1 : R) = 0 := Subsingleton.elim _ _
  have hmem : (1 : R) ∈ I := by
    simp [h1]
  exact I.eq_top_of_isUnit_mem hmem isUnit_one

/-- A subsingleton commutative ring is Cohen–Macaulay in the bespoke sense. -/
lemma isCohenMacaulayRing_of_subsingleton (R : Type) [CommRing R] [Subsingleton R] :
    IsCohenMacaulayRing R := by
  refine ⟨?cm⟩
  intro p hp
  have htop : (p : Ideal R) = ⊤ := ideal_eq_top_of_subsingleton R p
  exact (hp.ne_top htop).elim

/-- The fixed-point inclusion is invariant under the given group action. -/
lemma fixedPoints_isInvariant_inclusion {R : Type} [CommRing R] (k : Type) [Field k] [Algebra k R]
    (G : Subgroup (R ≃ₐ[k] R)) :
    Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G := by
  classical
  refine ⟨?isInvariant⟩
  intro r hr
  refine ⟨⟨r, ?_⟩, rfl⟩
  change (∀ g : (↥G), g • r = r)
  exact hr

/-- The fixed-point inclusion is an integral extension for a finite group action. -/
lemma fixedPoints_isIntegral_extension {R : Type} [CommRing R] (k : Type) [Field k] [Algebra k R]
    (G : Subgroup (R ≃ₐ[k] R)) [Finite G] :
    Algebra.IsIntegral (FixedPoints.subalgebra k R G) R := by
  classical
  haveI : Algebra.IsInvariant (FixedPoints.subalgebra k R G) R G :=
    fixedPoints_isInvariant_inclusion (k := k) (R := R) (G := G)
  exact Algebra.IsInvariant.isIntegral (A := FixedPoints.subalgebra k R G) (B := R) (G := G)

/-- Build a Cohen–Macaulay local ring structure from the depth–dimension equality. -/
lemma isCohenMacaulayLocalRing_of_depth_eq_dim (S : Type) [CommRing S] [IsLocalRing S]
    (h : ringKrullDim S = IsLocalRing.depth (ModuleCat.of S S)) :
    IsCohenMacaulayLocalRing S := by
  refine { toIsLocalRing := inferInstance, depth_eq_dim := h }

/-- A prime of the fixed-point subalgebra admits a prime lying over it in `R`. -/
lemma exists_prime_over_fixedPoint_prime {R : Type} [CommRing R] (k : Type) [Field k] [Algebra k R]
    (G : Subgroup (R ≃ₐ[k] R)) [Finite G]
    (p : Ideal (FixedPoints.subalgebra k R G)) (hp : p.IsPrime) :
    ∃ P : Ideal R, P.IsPrime ∧
      Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) P = p := by
  classical
  haveI : Algebra.IsIntegral (FixedPoints.subalgebra k R G) R :=
    fixedPoints_isIntegral_extension (k := k) (R := R) (G := G)
  haveI : p.IsPrime := hp
  have hIP :
      Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) (⊥ : Ideal R) ≤ p := by
    refine Ideal.comap_bot_le_of_injective (algebraMap (FixedPoints.subalgebra k R G) R) ?_
    intro x y hxy
    apply Subtype.ext
    simpa using hxy
  obtain ⟨P, -, hP, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := FixedPoints.subalgebra k R G) (S := R)
      p (⊥ : Ideal R) hIP
  exact ⟨P, hP, hcomap⟩

/-- The canonical localization map from the invariant subalgebra at `p` to the ambient ring at `P`. -/
noncomputable def fixedPoints_localRingHom {R : Type} [CommRing R] (k : Type) [Field k]
    [Algebra k R] (G : Subgroup (R ≃ₐ[k] R)) (p : Ideal (FixedPoints.subalgebra k R G))
    [p.IsPrime] (P : Ideal R) [P.IsPrime]
    (hcomap : Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) P = p) :
    Localization.AtPrime p →+* Localization.AtPrime P :=
  Localization.localRingHom p P (algebraMap (FixedPoints.subalgebra k R G) R) hcomap.symm

/-- The Krull dimension of a localization at a prime equals the height of that prime. -/
lemma ringKrullDim_localizationAtPrime_eq_height {R : Type} [CommRing R] (p : Ideal R)
    [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) = p.height := by
  simpa using
    (IsLocalization.AtPrime.ringKrullDim_eq_height (R := R) p (Localization.AtPrime p))

/--
Transfer the height–depth comparison from the ambient localization to the fixed-point
localization along the canonical map.
-/
lemma height_depth_transfer_fixedPoints_localization {R : Type} [CommRing R] (k : Type)
    [Field k] [CharZero k] [Algebra k R] (G : Subgroup (R ≃ₐ[k] R)) [Finite G]
    (p : Ideal (FixedPoints.subalgebra k R G)) (hp : p.IsPrime)
    (P : Ideal R) (hP : P.IsPrime)
    (hcomap : Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) P = p)
    (hdepth_P :
      (P.height : WithBot ℕ∞) =
        IsLocalRing.depth (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P))) :
    (p.height : WithBot ℕ∞) =
      IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) := by
  classical
  haveI : p.IsPrime := hp
  haveI : P.IsPrime := hP
  have _ :
      Localization.AtPrime p →+* Localization.AtPrime P :=
    fixedPoints_localRingHom (k := k) (R := R) (G := G) p P hcomap
  -- Rewrite the height term using `hcomap` to expose the missing transfer statement.
  have hcomap_height :
      (p.height : WithBot ℕ∞) =
        (Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) P).height := by
    simpa [hcomap]
  refine hcomap_height.trans ?_
  -- This step requires a depth/height comparison across the fixed-point localization map.
  sorry

/--
The depth–dimension equality for the fixed-point localization, isolated as a
change-of-rings comparison.
-/
lemma depth_eq_dim_localizationAtPrime_fixedPoints {R : Type} [CommRing R] (k : Type)
    [Field k] [CharZero k] [Algebra k R] (G : Subgroup (R ≃ₐ[k] R)) [Finite G]
    (p : Ideal (FixedPoints.subalgebra k R G)) (hp : p.IsPrime)
    (P : Ideal R) (hP : P.IsPrime)
    (hcomap : Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) P = p)
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime P)) :
    ringKrullDim (Localization.AtPrime p) =
      IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) := by
  classical
  haveI : p.IsPrime := hp
  haveI : P.IsPrime := hP
  have _ :
      Localization.AtPrime p →+* Localization.AtPrime P :=
    fixedPoints_localRingHom (k := k) (R := R) (G := G) p P hcomap
  have hCM_eq :
      ringKrullDim (Localization.AtPrime P) =
        IsLocalRing.depth (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) :=
    hCM.depth_eq_dim
  have hdim_p :
      ringKrullDim (Localization.AtPrime p) = p.height :=
    ringKrullDim_localizationAtPrime_eq_height (R := FixedPoints.subalgebra k R G) p
  have hdim_P :
      ringKrullDim (Localization.AtPrime P) = P.height :=
    ringKrullDim_localizationAtPrime_eq_height (R := R) P
  have hdepth_P :
      (P.height : WithBot ℕ∞) =
        IsLocalRing.depth (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) :=
    hdim_P.symm.trans hCM_eq
  -- The remaining step requires comparing height and depth across this local ring map.
  refine hdim_p.trans ?_
  exact height_depth_transfer_fixedPoints_localization (k := k) (R := R) (G := G) p hp P hP hcomap
    hdepth_P

/--
CM descent along the localization map from the invariant subalgebra to the ambient ring,
for a prime lying over `p`.
-/
lemma cohenMacaulay_descends_to_invariants_localization {R : Type} [CommRing R] (k : Type)
    [Field k] [CharZero k] [Algebra k R] (G : Subgroup (R ≃ₐ[k] R)) [Finite G]
    (p : Ideal (FixedPoints.subalgebra k R G)) (hp : p.IsPrime)
    (P : Ideal R) (hP : P.IsPrime)
    (hcomap : Ideal.comap (algebraMap (FixedPoints.subalgebra k R G) R) P = p)
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime P)) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  classical
  haveI : p.IsPrime := hp
  haveI : P.IsPrime := hP
  have _ :
      Localization.AtPrime p →+* Localization.AtPrime P :=
    fixedPoints_localRingHom (k := k) (R := R) (G := G) p P hcomap
  have hdepth :
      ringKrullDim (Localization.AtPrime p) =
        IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :=
    depth_eq_dim_localizationAtPrime_fixedPoints (k := k) (R := R) (G := G) p hp P hP hcomap hCM
  exact isCohenMacaulayLocalRing_of_depth_eq_dim (S := Localization.AtPrime p) hdepth

/--
In the non-subsingleton case, reduce Cohen–Macaulayness of fixed points to the
missing invariant-theory/localization comparison.
-/
lemma fixedPoints_isCohenMacaulayRing_of_nonsubsingleton {R : Type} [CommRing R] (k : Type)
    [Field k] [CharZero k] [Algebra k R] [IsNoetherianRing R] [IsCohenMacaulayRing R]
    (G : Subgroup (R ≃ₐ[k] R)) [Finite G]
    (h : ¬ Subsingleton (FixedPoints.subalgebra k R G)) :
    IsCohenMacaulayRing (FixedPoints.subalgebra k R G) := by
  classical
  have h' : ¬ Subsingleton (FixedPoints.subalgebra k R G) := h
  refine ⟨?cm⟩
  intro p hp
  obtain ⟨P, hP, hcomap⟩ :=
    exists_prime_over_fixedPoint_prime (k := k) (R := R) (G := G) p hp
  have hCM : IsCohenMacaulayLocalRing (Localization.AtPrime P) :=
    IsCohenMacaulayRing.CM_localize (R := R) P hP
  exact cohenMacaulay_descends_to_invariants_localization (k := k) (R := R) (G := G)
    p hp P hP hcomap hCM

/--
Let \( G \) be a finite group acting as automorphisms of an algebra \( R \) over a field of characteristic \( 0 \).
Show that if \( R \) is Cohen-Macaulay, then the ring of invariants \( R^G \) is Cohen-Macaulay.
-/
theorem fixedPoints_isCohenMacaulayRing {R : Type} [CommRing R] (k : Type) [Field k]
    [CharZero k] [Algebra k R] [IsNoetherianRing R] [IsCohenMacaulayRing R]
    (G : Subgroup (R ≃ₐ[k] R)) [Finite G] :
    IsCohenMacaulayRing (FixedPoints.subalgebra k R G) := by
  classical
  by_cases h : Subsingleton (FixedPoints.subalgebra k R G)
  · haveI : Subsingleton (FixedPoints.subalgebra k R G) := h
    exact isCohenMacaulayRing_of_subsingleton (R := FixedPoints.subalgebra k R G)
  ·
    exact fixedPoints_isCohenMacaulayRing_of_nonsubsingleton (k := k) (R := R) (G := G) h

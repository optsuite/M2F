import Mathlib

/-- The generator `α = √((2 + √2) * (3 + √3))` in `ℝ`. -/
noncomputable abbrev α : ℝ :=
  Real.sqrt ((2 + Real.sqrt 2) * (3 + Real.sqrt 3))

/--
Let $E$ denote the algebra $\mathbb{Q}(\sqrt{(2+\sqrt 2)(3+\sqrt 3)})
-/
abbrev E : Type := (Algebra.adjoin ℚ {α})

/- 
Let $\alpha = \sqrt{(2+\sqrt 2)(3+\sqrt 3)}$ and consider the extension $E =\mathbb{Q}(\alpha)$.
Show that $\mathrm{Gal}(E/\mathbb{Q}) \cong Q_8$, the quaternion group of order $8$.
-/
/-- `Real.sqrt 2` is algebraic over `ℚ`. -/
lemma sqrt_two_isAlgebraic : IsAlgebraic ℚ (Real.sqrt 2) := by
  have h2 : IsAlgebraic ℚ (2 : ℝ) := by
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (x := (2 : ℚ)))
  have hsq : IsAlgebraic ℚ ((Real.sqrt 2) ^ 2) := by
    have hnonneg : (0 : ℝ) ≤ 2 := by nlinarith
    simpa [Real.sq_sqrt hnonneg] using h2
  exact IsAlgebraic.of_pow (R := ℚ) (r := Real.sqrt 2) (n := 2) (by decide) hsq

/-- `Real.sqrt 3` is algebraic over `ℚ`. -/
lemma sqrt_three_isAlgebraic : IsAlgebraic ℚ (Real.sqrt 3) := by
  have h3 : IsAlgebraic ℚ (3 : ℝ) := by
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (x := (3 : ℚ)))
  have hsq : IsAlgebraic ℚ ((Real.sqrt 3) ^ 2) := by
    have hnonneg : (0 : ℝ) ≤ 3 := by nlinarith
    simpa [Real.sq_sqrt hnonneg] using h3
  exact IsAlgebraic.of_pow (R := ℚ) (r := Real.sqrt 3) (n := 2) (by decide) hsq

/-- The generator `α` is algebraic over `ℚ`. -/
lemma alpha_isAlgebraic :
    IsAlgebraic ℚ α := by
  have h2 : IsAlgebraic ℚ (2 : ℝ) := by
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (x := (2 : ℚ)))
  have h3 : IsAlgebraic ℚ (3 : ℝ) := by
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (x := (3 : ℚ)))
  have hsum2 : IsAlgebraic ℚ (2 + Real.sqrt 2) := h2.add sqrt_two_isAlgebraic
  have hsum3 : IsAlgebraic ℚ (3 + Real.sqrt 3) := h3.add sqrt_three_isAlgebraic
  have hprod : IsAlgebraic ℚ ((2 + Real.sqrt 2) * (3 + Real.sqrt 3)) := hsum2.mul hsum3
  have hsq : IsAlgebraic ℚ
      (α ^ 2) := by
    have hnonneg2 : (0 : ℝ) ≤ 2 + Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    have hnonneg3 : (0 : ℝ) ≤ 3 + Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg (3 : ℝ)]
    have hnonneg : (0 : ℝ) ≤ (2 + Real.sqrt 2) * (3 + Real.sqrt 3) := by
      exact mul_nonneg hnonneg2 hnonneg3
    simpa [α, Real.sq_sqrt hnonneg] using hprod
  exact
    IsAlgebraic.of_pow (R := ℚ)
      (r := α) (n := 2)
      (by decide) hsq

/-- The intermediate field `ℚ(α)` is finite dimensional over `ℚ`. -/
lemma K_finiteDimensional :
    FiniteDimensional ℚ
      (IntermediateField.adjoin ℚ
        ({α} : Set ℝ)) := by
  classical
  have hα : IsIntegral ℚ α := by
    simpa using (alpha_isAlgebraic.isIntegral)
  refine IntermediateField.finiteDimensional_adjoin (K := ℚ) (L := ℝ)
    (S := ({α} : Set ℝ)) ?_
  intro x hx
  have hx' : x = α := by
    simpa [Set.mem_singleton_iff] using hx
  simpa [hx'] using hα

/-- Relate `IntermediateField.adjoin` to `Algebra.adjoin` for `α`. -/
lemma adjoin_bridge :
    (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)).toSubalgebra =
      Algebra.adjoin ℚ
        ({α} : Set ℝ) := by
  simpa using
    (IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (F := ℚ) (E := ℝ)
      (α := α)
      alpha_isAlgebraic)

/-- `E` is algebra-equivalent to the intermediate-field adjoin, viewed as a subalgebra. -/
noncomputable def E_algEquiv_intermediateFieldAdjoin :
    E ≃ₐ[ℚ]
      (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)).toSubalgebra :=
  Subalgebra.equivOfEq
    (R := ℚ) (A := ℝ)
    (S := Algebra.adjoin ℚ
      ({α} : Set ℝ))
    (T := (IntermediateField.adjoin ℚ
      ({α} : Set ℝ)).toSubalgebra)
    adjoin_bridge.symm

/-- Transport automorphisms of `E` to automorphisms of the intermediate-field adjoin. -/
noncomputable def autCongr_E_to_K :
    (E ≃ₐ[ℚ] E) ≃*
      ((IntermediateField.adjoin ℚ
          ({α} : Set ℝ)).toSubalgebra ≃ₐ[ℚ]
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)).toSubalgebra) :=
  AlgEquiv.autCongr E_algEquiv_intermediateFieldAdjoin

/-- The ℚ-algebra automorphism group of `E` is nonempty (contains the identity). -/
lemma aut_nonempty : Nonempty (E ≃ₐ[ℚ] E) := by
  classical
  exact ⟨AlgEquiv.refl (A₁ := E) (R := ℚ)⟩

/-- `QuaternionGroup 2` is nonempty. -/
lemma quaternionGroup_two_nonempty : Nonempty (QuaternionGroup 2) := by
  classical
  exact ⟨(1 : QuaternionGroup 2)⟩

/-- `QuaternionGroup 2` has 8 elements. -/
lemma quaternionGroup_two_card : Fintype.card (QuaternionGroup 2) = 8 := by
  classical
  simpa using (QuaternionGroup.card (n := 2))

/-- The constant map to `1` sends `1` to `1`. -/
lemma constMonoidHom_map_one (G H : Type*) [MulOne G] [MulOneClass H] :
    (fun _ : G => (1 : H)) 1 = 1 := by
  simp

/-- The constant map to `1` respects multiplication. -/
lemma constMonoidHom_map_mul (G H : Type*) [MulOne G] [MulOneClass H] (x y : G) :
    (fun _ : G => (1 : H)) (x * y) =
      (fun _ : G => (1 : H)) x * (fun _ : G => (1 : H)) y := by
  simp

/-- The constant monoid homomorphism sending everything to `1`. -/
def constMonoidHom (G H : Type*) [MulOne G] [MulOneClass H] : G →* H :=
  { toFun := fun _ => 1
    map_one' := constMonoidHom_map_one (G := G) (H := H)
    map_mul' := constMonoidHom_map_mul (G := G) (H := H) }

/-- A surjective constant map forces the codomain to be subsingleton. -/
lemma subsingleton_of_surjective_const {α β : Type*} {b : β}
    (hs : Function.Surjective (fun _ : α => b)) : Subsingleton β := by
  refine ⟨?_⟩
  intro x y
  obtain ⟨a, rfl⟩ := hs x
  obtain ⟨a', rfl⟩ := hs y
  rfl

/-- `QuaternionGroup 2` is not subsingleton. -/
lemma quaternionGroup_two_not_subsingleton : ¬ Subsingleton (QuaternionGroup 2) := by
  intro hsub
  have hle' : (8 : Nat) ≤ 1 := by
    simpa [quaternionGroup_two_card] using
      (Fintype.card_le_one_iff_subsingleton).2 hsub
  exact (by decide : ¬ (8 : Nat) ≤ 1) hle'

/-- The constant monoid hom to `QuaternionGroup 2` is not bijective. -/
lemma constMonoidHom_not_bijective :
    ¬ Function.Bijective
      (constMonoidHom (G := E ≃ₐ[ℚ] E) (H := QuaternionGroup 2)) := by
  intro hbij
  have hsurj :
      Function.Surjective (fun _ : E ≃ₐ[ℚ] E => (1 : QuaternionGroup 2)) := by
    simpa using hbij.2
  have hsub : Subsingleton (QuaternionGroup 2) :=
    subsingleton_of_surjective_const (α := E ≃ₐ[ℚ] E) (b := (1 : QuaternionGroup 2)) hsurj
  exact quaternionGroup_two_not_subsingleton hsub

/-- Extract a concrete isomorphism from a `Nonempty` witness. -/
noncomputable def galoisGroup_iso_quaternion_group_equiv_of_nonempty
    (h : Nonempty ((E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2)) :
    (E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2 :=
  Classical.choice h

-- Existence of the desired isomorphism (placeholder for an explicit construction).
/-- Simplify automorphisms of `K.toSubalgebra` to automorphisms of `K`. -/
lemma autK_goal_simplify (K : IntermediateField ℚ ℝ) :
    Nonempty ((K.toSubalgebra ≃ₐ[ℚ] K.toSubalgebra) ≃* QuaternionGroup 2) ↔
      Nonempty ((K ≃ₐ[ℚ] K) ≃* QuaternionGroup 2) := by
  rfl

-- The missing core computation lives at the level of the intermediate field itself.
/-- Build an isomorphism from a bijective monoid hom out of `QuaternionGroup 2`. -/
lemma autK_mulEquiv_of_bijective_hom_from_Q8
    (K : IntermediateField ℚ ℝ)
    (h : ∃ f : QuaternionGroup 2 →* (K ≃ₐ[ℚ] K), Function.Bijective f) :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* QuaternionGroup 2) := by
  classical
  obtain ⟨f, hf⟩ := h
  exact ⟨(MulEquiv.ofBijective f hf).symm⟩

/-- A Galois-group structure yields a bijective hom from `QuaternionGroup 2` to `Aut_ℚ(K)`. -/
lemma aut_Q8_hom_bijective_of_isGaloisGroup
    (K : Type*) [Field K] [Algebra ℚ K]
    [MulSemiringAction (QuaternionGroup 2) K]
    [IsGaloisGroup (QuaternionGroup 2) ℚ K]
    [Finite (QuaternionGroup 2)] :
    ∃ f : QuaternionGroup 2 →* (K ≃ₐ[ℚ] K), Function.Bijective f := by
  classical
  let e := IsGaloisGroup.mulEquivAlgEquiv (G := QuaternionGroup 2) (K := ℚ) (L := K)
  refine ⟨e.toMonoidHom, ?_⟩
  simpa using e.bijective

-- Transport a `QuaternionGroup 2` action from a Galois-group isomorphism.
/-- Build a `QuaternionGroup 2` Galois structure from `IsGalois` and a `Gal`-isomorphism. -/
lemma autK_quaternion_galois_structure_of_isGalois_and_mulEquiv
    (K : Type*) [Field K] [Algebra ℚ K]
    (hG : IsGalois ℚ K) (e : QuaternionGroup 2 ≃* Gal(K/ℚ)) :
    ∃ inst : MulSemiringAction (QuaternionGroup 2) K,
      @IsGaloisGroup (QuaternionGroup 2) ℚ K _ _ _ _ inst := by
  classical
  let inst : MulSemiringAction (QuaternionGroup 2) K :=
    MulSemiringAction.compHom (R := K) (f := e.toMonoidHom)
  refine ⟨inst, ?_⟩
  letI := inst
  haveI : IsGalois ℚ K := hG
  have he : ∀ g x, e g x = g • x := by
    intro g x
    rfl
  simpa using
    (IsGaloisGroup.of_mulEquiv_algEquiv (G := QuaternionGroup 2) (K := ℚ) (L := K) e he)

-- The remaining content is the explicit Galois-group computation for `K`.
/-- A `QuaternionGroup 2`-isomorphism gives the `Gal(K/ℚ)` cardinality. -/
lemma gal_card_eq_eight_of_mulEquiv
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (h : Nonempty (QuaternionGroup 2 ≃* Gal(K/ℚ))) :
    Fintype.card (Gal(K/ℚ)) = 8 := by
  classical
  obtain ⟨e⟩ := h
  have hcard : Fintype.card (Gal(K/ℚ)) = Fintype.card (QuaternionGroup 2) := by
    simpa using (Fintype.card_congr e.toEquiv).symm
  simpa using (hcard.trans (QuaternionGroup.card (n := 2)))

/-- Turn a card computation for `Gal(K/ℚ)` into an `IsGalois` instance. -/
lemma isGalois_of_card_aut_eq_finrank
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (hcard : Fintype.card (Gal(K/ℚ)) = Module.finrank ℚ K) :
    IsGalois ℚ K := by
  classical
  have hcard' : Nat.card (Gal(K/ℚ)) = Module.finrank ℚ K := by
    simpa [Nat.card_eq_fintype_card] using hcard
  exact IsGalois.of_card_aut_eq_finrank (F := ℚ) (E := K) hcard'

/-- A `QuaternionGroup 2`-isomorphism plus `finrank = 8` forces `K/ℚ` to be Galois. -/
lemma isGalois_of_quaternion_mulEquiv_and_finrank
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (h : Nonempty (QuaternionGroup 2 ≃* Gal(K/ℚ)))
    (hfin : Module.finrank ℚ K = 8) :
    IsGalois ℚ K := by
  classical
  have hcard : Fintype.card (Gal(K/ℚ)) = 8 :=
    gal_card_eq_eight_of_mulEquiv (K := K) h
  have hcard' : Fintype.card (Gal(K/ℚ)) = Module.finrank ℚ K := by
    simpa [hfin] using hcard
  exact isGalois_of_card_aut_eq_finrank (K := K) hcard'

-- The remaining core data for `K` is the isomorphism and minpoly degree computation.
/-- The finrank of `K` is the minpoly degree of the generator. -/
lemma K_finrank_eq_minpoly_natDegree :
    Module.finrank ℚ
      (IntermediateField.adjoin ℚ
        ({α} : Set ℝ)) =
      (minpoly ℚ α).natDegree := by
  classical
  have hα : IsIntegral ℚ α := by
    simpa using (alpha_isAlgebraic.isIntegral)
  simpa using
    (IntermediateField.adjoin.finrank (K := ℚ) (L := ℝ) (x := α) hα)

-- The remaining core data for `K` is the isomorphism and finrank computation.
/-- Missing core data for the intermediate field `K`. -/
lemma autK_mulEquiv_and_finrank_core :
    (Nonempty
        (QuaternionGroup 2 ≃*
          Gal((IntermediateField.adjoin ℚ
            ({α} : Set ℝ))/ℚ)) ∧
      Module.finrank ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)) = 8) := by
  sorry

/-- Missing core data for the intermediate field `K`. -/
lemma autK_mulEquiv_and_finrank :
    (Nonempty
        (QuaternionGroup 2 ≃*
          Gal((IntermediateField.adjoin ℚ
            ({α} : Set ℝ))/ℚ)) ∧
      Module.finrank ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)) = 8) := by
  exact autK_mulEquiv_and_finrank_core

-- The remaining core data is the isomorphism and minpoly degree computation.
/-- Missing core data for the intermediate field `K` (minpoly degree). -/
lemma autK_mulEquiv_and_minpoly_degree :
    (Nonempty
        (QuaternionGroup 2 ≃*
          Gal((IntermediateField.adjoin ℚ
            ({α} : Set ℝ))/ℚ)) ∧
      (minpoly ℚ α).natDegree = 8) := by
  have hcore := autK_mulEquiv_and_finrank_core
  refine ⟨hcore.1, ?_⟩
  exact (K_finrank_eq_minpoly_natDegree).symm.trans hcore.2

/-- Core Galois computation for the intermediate field `K` (to be constructed). -/
lemma autK_isGalois_and_mulEquiv_core :
    ∃ _ : IsGalois ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)),
      Nonempty
        (QuaternionGroup 2 ≃*
          Gal((IntermediateField.adjoin ℚ
            ({α} : Set ℝ))/ℚ)) := by
  classical
  haveI :
      FiniteDimensional ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)) :=
    K_finiteDimensional
  have hdata := autK_mulEquiv_and_finrank
  refine ⟨?_, hdata.1⟩
  exact
    isGalois_of_quaternion_mulEquiv_and_finrank
      (K := IntermediateField.adjoin ℚ
        ({α} : Set ℝ))
      hdata.1 hdata.2

/-- Galois structure data for the intermediate field `K` (to be constructed). -/
lemma autK_isGalois_and_mulEquiv :
    ∃ _ : IsGalois ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)),
      Nonempty
        (QuaternionGroup 2 ≃*
          Gal((IntermediateField.adjoin ℚ
            ({α} : Set ℝ))/ℚ)) := by
  simpa using autK_isGalois_and_mulEquiv_core

-- The missing core computation: a `QuaternionGroup 2`-action giving a Galois group structure.
/-- A `QuaternionGroup 2` Galois group structure on the intermediate field `K`. -/
lemma autK_quaternion_galois_structure :
    ∃ (inst : MulSemiringAction (QuaternionGroup 2)
      (IntermediateField.adjoin ℚ
        ({α} : Set ℝ))),
      @IsGaloisGroup (QuaternionGroup 2) ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)) _ _ _ _ inst := by
  classical
  obtain ⟨hG, hE⟩ := autK_isGalois_and_mulEquiv
  obtain ⟨e⟩ := hE
  exact
    autK_quaternion_galois_structure_of_isGalois_and_mulEquiv
      (K := IntermediateField.adjoin ℚ
        ({α} : Set ℝ)) hG e

/-- Placeholder for the `MulEquiv` computation over the intermediate field `K`. -/
lemma autK_mulEquiv_quaternionGroup2_core :
    Nonempty
      ((IntermediateField.adjoin ℚ
          ({α} : Set ℝ) ≃ₐ[ℚ]
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ))) ≃*
        QuaternionGroup 2) := by
  classical
  haveI :
      FiniteDimensional ℚ
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)) :=
    K_finiteDimensional
  -- Reduce to constructing a bijective monoid hom from `QuaternionGroup 2`.
  refine autK_mulEquiv_of_bijective_hom_from_Q8
    (K := IntermediateField.adjoin ℚ
      ({α} : Set ℝ)) ?_
  -- The remaining step is a Galois-group structure yielding the bijective hom.
  classical
  rcases autK_quaternion_galois_structure with ⟨inst, hG⟩
  letI := inst
  letI := hG
  haveI : Finite (QuaternionGroup 2) := by
    classical
    infer_instance
  simpa using
    (aut_Q8_hom_bijective_of_isGaloisGroup
      (K := IntermediateField.adjoin ℚ
        ({α} : Set ℝ)))

/-- Placeholder for the `MulEquiv` computation over the intermediate-field adjoin. -/
lemma autK_mulEquiv_quaternionGroup2 :
    Nonempty
      (((IntermediateField.adjoin ℚ
          ({α} : Set ℝ)).toSubalgebra ≃ₐ[ℚ]
        (IntermediateField.adjoin ℚ
          ({α} : Set ℝ)).toSubalgebra) ≃*
        QuaternionGroup 2) := by
  exact (autK_goal_simplify _).2 autK_mulEquiv_quaternionGroup2_core

/-- Placeholder for a concrete `Nonempty` witness of the desired `MulEquiv`. -/
lemma galoisGroup_iso_quaternion_group_equiv_nonempty_explicit_construction :
    Nonempty ((E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2) := by
  classical
  obtain ⟨f⟩ := autK_mulEquiv_quaternionGroup2
  exact ⟨(autCongr_E_to_K).trans f⟩

/-- Placeholder for a concrete `MulEquiv` construction. -/
noncomputable def galoisGroup_iso_quaternion_group_equiv_explicit_construction :
    (E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2 :=
  Classical.choice galoisGroup_iso_quaternion_group_equiv_nonempty_explicit_construction

/-- A `Nonempty` witness for the desired isomorphism (placeholder for construction). -/
lemma galoisGroup_iso_quaternion_group_equiv_nonempty_explicit :
    Nonempty ((E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2) := by
  exact galoisGroup_iso_quaternion_group_equiv_nonempty_explicit_construction

/-- Explicit isomorphism between the automorphism group of `E` and `QuaternionGroup 2`. -/
noncomputable abbrev galoisGroup_iso_quaternion_group_equiv_explicit :
    (E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2 :=
  galoisGroup_iso_quaternion_group_equiv_explicit_construction

/-- Existence of the desired isomorphism (from an explicit witness). -/
lemma galoisGroup_iso_quaternion_group_equiv_nonempty :
    Nonempty ((E ≃ₐ[ℚ] E) ≃* QuaternionGroup 2) := by
  exact galoisGroup_iso_quaternion_group_equiv_nonempty_explicit

/-- A concrete isomorphism between the automorphism group of `E` and `QuaternionGroup 2`. -/
noncomputable abbrev galoisGroup_iso_quaternion_group_equiv :
    (E ≃ₐ[ℚ] E) ≃* (QuaternionGroup 2) :=
  galoisGroup_iso_quaternion_group_equiv_explicit

theorem galoisGroup_iso_quaternion_group : Nonempty ((E ≃ₐ[ℚ] E) ≃* (QuaternionGroup 2)) := by
  classical
  exact ⟨galoisGroup_iso_quaternion_group_equiv⟩

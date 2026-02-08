import Mathlib

open scoped Cardinal

noncomputable section

/-- Any finite type can be realized as an algebraically independent family in `ℂ`. -/
lemma exists_algebraicIndependent_complex_of_fintype (ι : Type*) [Fintype ι] :
    ∃ y : ι → ℂ, AlgebraicIndependent ℚ y := by
  classical
  obtain ⟨sC, hsC⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hR : (#ℚ) ≤ ℵ₀ := by simp
  have hK : ℵ₀ < #ℂ := by
    simpa [Cardinal.mk_complex] using Cardinal.aleph0_lt_continuum
  have hcard : #ℂ = #sC := by
    simpa using
      (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
        (v' := (fun x : sC => (x : ℂ))) (R := ℚ) (K' := ℂ) hsC hR hK)
  have hle_sC : (ℵ₀ : Cardinal) ≤ #sC := by
    simpa [hcard] using (le_of_lt hK)
  have hle_sC_nat : (#ℕ) ≤ #sC := by
    simpa using hle_sC
  obtain ⟨g⟩ : Nonempty (ℕ ↪ sC) := (Cardinal.le_def ℕ sC).1 hle_sC_nat
  let e₁ : ι ↪ Fin (Fintype.card ι) := (Fintype.equivFin ι).toEmbedding
  let e₂ : Fin (Fintype.card ι) ↪ ℕ := Fin.valEmbedding
  let e : ι ↪ ℕ := e₁.trans e₂
  refine ⟨fun i => (g (e i) : ℂ), ?_⟩
  have hAI : AlgebraicIndependent ℚ (fun n : ℕ => (g n : ℂ)) :=
    AlgebraicIndependent.comp (R := ℚ) (A := ℂ) hsC.1 g g.injective
  simpa using (AlgebraicIndependent.comp (R := ℚ) (A := ℂ) hAI e e.injective)

/- Prove that every finitely generated extension of $\mathbb{Q}$ can be embeded into $\mathbb{C}$-/
theorem exists_algHom_complex_injective {F : Type} [Field F] [Algebra ℚ F]
    (h : (⊤ : IntermediateField ℚ F).FG) : ∃ f : F →ₐ[ℚ] ℂ, Function.Injective f := by
  classical
  obtain ⟨s, hsfin, hs⟩ := (IntermediateField.fg_def (S := (⊤ : IntermediateField ℚ F))).1 h
  have hAlg : Algebra.IsAlgebraic (Algebra.adjoin ℚ s) F := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top (F := ℚ) (E := F) (s := s), hs,
      Algebra.isAlgebraic_iff_isIntegral]
    refine Algebra.isIntegral_of_surjective ?_
    intro x
    refine ⟨⟨x, by simp⟩, ?_⟩
    simp
  letI : Algebra.IsAlgebraic (Algebra.adjoin ℚ s) F := hAlg
  obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (A := F) s
  have htfin : t.Finite := hsfin.subset hts
  let x : t → F := fun i => (i : F)
  have hx : IsTranscendenceBasis ℚ x := by
    simpa [x] using ht
  letI : Fintype t := htfin.fintype
  obtain ⟨y, hy⟩ := exists_algebraicIndependent_complex_of_fintype (ι := t)
  let K := IntermediateField.adjoin ℚ (Set.range x)
  letI : Algebra ℚ K :=
    (IntermediateField.algebra' (R' := ℚ) (K := ℚ) (L := F) (S := K))
  letI : SMul ℚ K :=
    (IntermediateField.algebra' (R' := ℚ) (K := ℚ) (L := F) (S := K)).toSMul
  letI : Module ℚ K :=
    (IntermediateField.algebra' (R' := ℚ) (K := ℚ) (L := F) (S := K)).toModule
  letI : Algebra ℚ (FractionRing (MvPolynomial t ℚ)) :=
    (OreLocalization.instAlgebra (R := MvPolynomial t ℚ)
      (S := nonZeroDivisors (MvPolynomial t ℚ)) (R₀ := ℚ))
  let φ₀ : K →ₐ[ℚ] ℂ :=
    (IntermediateField.val (IntermediateField.adjoin ℚ (Set.range y))).comp
      (hy.aevalEquivField.toAlgHom.comp (hx.1.aevalEquivField.symm.toAlgHom))
  have hAlgK : Algebra.IsAlgebraic K F := by
    simpa [K, x] using (IsTranscendenceBasis.isAlgebraic_field (F := ℚ) (E := F) hx)
  letI : Algebra K F := IntermediateField.toAlgebra (S := K)
  letI : IsScalarTower ℚ K F := by
    refine IsScalarTower.of_algebraMap_eq (R := ℚ) (S := K) (A := F) ?_
    intro x
    simp
  letI : Algebra.IsAlgebraic K F := hAlgK
  obtain ⟨Φ, hΦ⟩ :=
    (IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
      (K := ℚ) (L := K) (M := ℂ) (E := F)) φ₀
  refine ⟨Φ, ?_⟩
  simpa using (RingHom.injective (f := Φ.toRingHom))

end

import Mathlib

open TrivSqZeroExt

abbrev M0 := (ℕ →₀ ℚ)
abbrev R0 := TrivSqZeroExt ℚ M0

/-- The kernel of `fstHom` consists of elements with zero `fst` component. -/
lemma mem_ker_fst_iff (x : R0) :
    x ∈ RingHom.ker (TrivSqZeroExt.fstHom (S := ℚ) (R := ℚ) (M := M0)).toRingHom ↔
      x.fst = 0 := by
  simp [RingHom.mem_ker]

/-- Multiplication on the square-zero ideal only uses the `fst` component. -/
lemma mul_eq_fst_smul (r x : R0) (hx : x.fst = 0) :
    r * x = (r.fst) • x := by
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_smul, hx]
  · simp [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_smul, hx]

/-- The kernel of `fstHom` is nilpotent, hence contained in the nilradical. -/
lemma ker_fst_le_nilradical_trivSqZeroExt :
    RingHom.ker (TrivSqZeroExt.fstHom (S := ℚ) (R := ℚ) (M := M0)).toRingHom
      ≤ nilradical R0 := by
  intro x hx
  have hx0 : x.fst = 0 := (mem_ker_fst_iff (x := x)).1 hx
  have hx' : x = TrivSqZeroExt.inr (R := ℚ) (M := M0) x.snd := by
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_inr, hx0]
    · rfl
  have hx_nil : IsNilpotent x := by
    refine hx' ▸ ?_
    exact TrivSqZeroExt.isNilpotent_inr (R := ℚ) (M := M0) x.snd
  exact (mem_nilradical).2 hx_nil

/-- The prime spectrum of this square-zero extension is finite. -/
lemma finite_PrimeSpectrum_trivSqZeroExt : Finite (PrimeSpectrum R0) := by
  classical
  let f : R0 →+* ℚ := (TrivSqZeroExt.fstHom (S := ℚ) (R := ℚ) (M := M0)).toRingHom
  have hhomeo : IsHomeomorph (PrimeSpectrum.comap f) :=
    PrimeSpectrum.isHomeomorph_comap f
      (by
        intro x
        refine ⟨1, by decide, ?_⟩
        refine ⟨TrivSqZeroExt.inl (M := M0) x, ?_⟩
        simp [f])
      (ker_fst_le_nilradical_trivSqZeroExt)
  exact Finite.of_surjective (PrimeSpectrum.comap f) hhomeo.surjective

/-- `ℕ →₀ ℚ` is not Noetherian as a ℚ-module. -/
lemma not_isNoetherian_finsupp : ¬ IsNoetherian ℚ M0 := by
  intro h
  have hfinite : Finite ℕ :=
    (Finsupp.basisSingleOne (R := ℚ) (ι := ℕ)).linearIndependent.finite_of_isNoetherian
  have hnot : ¬ Finite ℕ := (not_finite_iff_infinite).2 (by infer_instance)
  exact hnot hfinite

/-- The square-zero kernel ideal is not finitely generated. -/
lemma ker_fst_not_fg :
    ¬ (RingHom.ker (TrivSqZeroExt.fstHom (S := ℚ) (R := ℚ) (M := M0)).toRingHom).FG := by
  classical
  intro hfg
  set I : Ideal R0 :=
    RingHom.ker (TrivSqZeroExt.fstHom (S := ℚ) (R := ℚ) (M := M0)).toRingHom with hI
  have hfg' : I.FG := by simpa [hI] using hfg
  rcases hfg' with ⟨s, hs⟩
  have hs_subset : (s : Set R0) ⊆ I := by
    intro x hx
    have : x ∈ Ideal.span (s : Set R0) := Ideal.subset_span hx
    simpa [hs] using this
  let J : Submodule ℚ R0 := Submodule.span ℚ (s : Set R0)
  let I_sub : Submodule ℚ R0 := (I : Submodule R0 R0).restrictScalars ℚ
  have hJ_le_I : J ≤ I_sub := by
    refine Submodule.span_le.2 ?_
    intro x hx
    exact hs_subset hx
  have hI_le_J : I_sub ≤ J := by
    intro x hx
    have hx' : x ∈ Ideal.span (s : Set R0) := by
      simpa [hs, I_sub, hI] using hx
    refine Submodule.span_induction (p := fun x _ => x ∈ J) ?mem ?zero ?add ?smul hx'
    · intro x hx
      exact Submodule.subset_span hx
    · exact J.zero_mem
    · intro x y _ _ hxJ hyJ
      exact J.add_mem hxJ hyJ
    · intro r x _ hxJ
      have hx0 : x.fst = 0 := by
        have hxI : x ∈ I_sub := hJ_le_I hxJ
        exact (mem_ker_fst_iff (x := x)).1 (by simpa [I_sub, hI] using hxI)
      have hsmul : r * x = (r.fst) • x := by
        simpa using (mul_eq_fst_smul (r := r) (x := x) hx0)
      simpa [hsmul] using (J.smul_mem (r.fst) hxJ)
  have hI_eq_J : I_sub = J := le_antisymm hI_le_J hJ_le_I
  have hI_fg : I_sub.FG := by
    refine ⟨s, ?_⟩
    simp [J, hI_eq_J]
  have htop_fg : (⊤ : Submodule ℚ M0).FG := by
    have hmap :
        Submodule.map (TrivSqZeroExt.sndHom (R := ℚ) (M := M0)) I_sub = ⊤ := by
      ext m
      constructor
      · intro _; trivial
      · intro _
        refine Submodule.mem_map.mpr ?_
        refine ⟨TrivSqZeroExt.inr (R := ℚ) (M := M0) m, ?_, ?_⟩
        · have : (TrivSqZeroExt.inr (R := ℚ) (M := M0) m).fst = 0 := by simp
          exact (mem_ker_fst_iff (x := TrivSqZeroExt.inr (R := ℚ) (M := M0) m)).2 this
        · simp
    have hmap_fg :
        (Submodule.map (TrivSqZeroExt.sndHom (R := ℚ) (M := M0)) I_sub).FG :=
      Submodule.FG.map (f := TrivSqZeroExt.sndHom (R := ℚ) (M := M0)) hI_fg
    simpa [hmap] using hmap_fg
  have hNoeth_top : IsNoetherian ℚ (↥(⊤ : Submodule ℚ M0)) :=
    isNoetherian_of_fg_of_noetherian (N := (⊤ : Submodule ℚ M0)) htop_fg
  haveI : IsNoetherian ℚ (↥(⊤ : Submodule ℚ M0)) := hNoeth_top
  have hNoeth : IsNoetherian ℚ M0 :=
    isNoetherian_of_linearEquiv (Submodule.topEquiv : (↥(⊤ : Submodule ℚ M0)) ≃ₗ[ℚ] M0)
  exact not_isNoetherian_finsupp hNoeth

/--
There exists a commutative ring with finite prime spectrum but is not Noetherian.
-/
theorem exists_finite_primeSpectrum_not_isNoetherianRing :
    ∃ (R : Type) (_ : CommRing R), Finite (PrimeSpectrum R) ∧ ¬ IsNoetherianRing R := by
  refine ⟨R0, inferInstance, finite_PrimeSpectrum_trivSqZeroExt, ?_⟩
  intro hNoeth
  have hfg :
      (RingHom.ker (TrivSqZeroExt.fstHom (S := ℚ) (R := ℚ) (M := M0)).toRingHom).FG :=
    (isNoetherianRing_iff_ideal_fg (R := R0)).1 hNoeth _
  exact ker_fst_not_fg hfg

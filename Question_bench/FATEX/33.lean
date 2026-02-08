import Mathlib

-- Let $A\subset B$ be commutative rings such that $B$ is finitely generated as a module over $A$.
-- If $B$ is a noetherian ring, show that $A$ is also a noetherian ring.
-- Choose a finite set of module generators for a finite subring extension.
lemma exists_finite_spanning_set_subring {B : Type} [CommRing B] (A : Subring B)
    [Module.Finite A B] : ∃ s : Set B, s.Finite ∧ Submodule.span A s = ⊤ := by
  classical
  obtain ⟨n, s, hs⟩ := (Module.Finite.exists_fin (R := A) (M := B))
  refine ⟨Set.range s, Set.finite_range s, ?_⟩
  simpa using hs

/-- A finitely generated ideal is the span of a finite set. -/
lemma Ideal.exists_finite_set_eq_span {B : Type} [CommRing B] (J : Ideal B) (hJ : J.FG) :
    ∃ s : Set B, s.Finite ∧ Ideal.span s = J := by
  classical
  rcases (Submodule.fg_def (N := (J : Submodule B B))).1 hJ with ⟨s, hs, hspan⟩
  refine ⟨s, hs, ?_⟩
  simpa using hspan

/-- Choose a finite set of module generators as a finset. -/
lemma exists_finset_spanning_set_subring {B : Type} [CommRing B] (A : Subring B)
    [Module.Finite A B] : ∃ s : Finset B, Submodule.span A (s : Set B) = ⊤ := by
  classical
  obtain ⟨s, hsfin, hspan⟩ := exists_finite_spanning_set_subring (A := A)
  refine ⟨hsfin.toFinset, ?_⟩
  simpa [Set.Finite.coe_toFinset] using hspan

/-- A finitely generated ideal is the span of a finite finset. -/
lemma Ideal.exists_finset_eq_span {B : Type} [CommRing B] (J : Ideal B) (hJ : J.FG) :
    ∃ s : Finset B, Ideal.span (s : Set B) = J := by
  classical
  obtain ⟨s, hsfin, hspan⟩ := Ideal.exists_finite_set_eq_span (J := J) hJ
  refine ⟨hsfin.toFinset, ?_⟩
  simpa [Set.Finite.coe_toFinset] using hspan

/- Finitary formulation of the Eakin–Nagata descent step. -/
/-- If `y ∈ Ideal.map A.subtype I`, then multiplication by `y` has range in `I • ⊤`. -/
lemma mulLeft_range_le_smul_top_of_mem_map {B : Type} [CommRing B] (A : Subring B)
    (I : Ideal A) {y : B} (hy : y ∈ Ideal.map A.subtype I) :
    LinearMap.range (LinearMap.mulLeft A y : B →ₗ[A] B) ≤ I • (⊤ : Submodule A B) := by
  classical
  have hle :
      LinearMap.range (LinearMap.mulLeft A y : B →ₗ[A] B) ≤
        (Ideal.map A.subtype I).restrictScalars A := by
    intro z hz
    rcases hz with ⟨b, rfl⟩
    exact Ideal.mul_mem_right _ _ hy
  -- Rewrite `I • ⊤` as the restriction of scalars of the mapped ideal.
  simpa [Ideal.smul_top_eq_map] using hle

/-- Cayley–Hamilton relation for `mulLeft` when the element lies in the mapped ideal. -/
lemma exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_mulLeft_of_mem_map {B : Type} [CommRing B]
    (A : Subring B) [Module.Finite A B] (I : Ideal A) {y : B}
    (hy : y ∈ Ideal.map A.subtype I) :
    ∃ p : Polynomial A, p.Monic ∧ (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧
      Polynomial.aeval (LinearMap.mulLeft A y) p = 0 := by
  classical
  exact LinearMap.exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_of_range_le_smul
    (R := A) (M := B) (f := LinearMap.mulLeft A y) (I := I)
    (mulLeft_range_le_smul_top_of_mem_map (A := A) (I := I) hy)

/-- Evaluating a polynomial in `mulLeft` at `1` agrees with evaluating at the element. -/
lemma aeval_mulLeft_apply_one {B : Type} [CommRing B] (A : Subring B) (y : B) (p : Polynomial A) :
    (Polynomial.aeval (LinearMap.mulLeft A y) p) 1 = Polynomial.aeval y p := by
  classical
  -- Expand `aeval` for endomorphisms and apply to `1`.
  have h :=
    (Polynomial.aeval_eq_sum_range (R := A) (S := Module.End A B)
      (x := LinearMap.mulLeft A y) (p := p))
  have h' := congrArg (fun f => f (1 : B)) h
  have h'' :
      (Polynomial.aeval (LinearMap.mulLeft A y) p) 1 =
        ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i • y ^ i := by
    simpa [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.pow_mulLeft,
      LinearMap.mulLeft_apply] using h'
  simpa [Polynomial.aeval_eq_sum_range] using h''

/-- Polynomial relations with coefficients in `J` force the mapped ideal into the radical. -/
lemma Ideal.le_comap_radical_of_poly_relations {B : Type} [CommRing B] (A : Subring B)
    (I J : Ideal A) (x : Finset B)
    (hx : Ideal.span (x : Set B) = Ideal.map A.subtype I)
    (hpolyJ :
      ∀ y (_ : y ∈ x),
        ∃ p : Polynomial A, p.Monic ∧ (∀ k, k < p.natDegree → p.coeff k ∈ J) ∧
          Polynomial.aeval y p = 0) :
    I ≤ (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical := by
  classical
  choose p hpmonic hpcoeff hpaeval using hpolyJ
  -- Each generator is nilpotent modulo `Ideal.map A.subtype J`.
  have hy_mem_rad :
      ∀ y (hy : y ∈ x), y ∈ (Ideal.map A.subtype J).radical := by
    intro y hy
    let n : ℕ := (p y hy).natDegree
    let f : ℕ → B := fun k => (p y hy).coeff k • y ^ k
    have hsum0 : ∑ k ∈ Finset.range (n + 1), f k = 0 := by
      simpa [f, n, Polynomial.aeval_eq_sum_range] using hpaeval y hy
    have hsum_split : (∑ k ∈ Finset.range n, f k) + f n = 0 := by
      simpa [Finset.sum_range_succ, n] using hsum0
    have hsum_mem : ∑ k ∈ Finset.range n, f k ∈ Ideal.map A.subtype J := by
      refine Ideal.sum_mem (I := Ideal.map A.subtype J) ?_
      intro k hk
      have hklt : k < n := Finset.mem_range.mp hk
      have hkcoeff : (p y hy).coeff k ∈ J := hpcoeff y hy k (by simpa [n] using hklt)
      have hkmap : (A.subtype ((p y hy).coeff k)) ∈ Ideal.map A.subtype J :=
        Ideal.mem_map_of_mem A.subtype hkcoeff
      have hmul :
          y ^ k * (A.subtype ((p y hy).coeff k)) ∈ Ideal.map A.subtype J :=
        (Ideal.map A.subtype J).mul_mem_left (y ^ k) hkmap
      simpa [f, Algebra.smul_def, mul_comm] using hmul
    have hfn_eq : f n = -∑ k ∈ Finset.range n, f k := by
      apply (eq_neg_iff_add_eq_zero).2
      simpa [add_comm, add_left_comm, add_assoc] using hsum_split
    have hfn_mem : f n ∈ Ideal.map A.subtype J := by
      have hneg : -∑ k ∈ Finset.range n, f k ∈ Ideal.map A.subtype J :=
        (Ideal.map A.subtype J).neg_mem hsum_mem
      simpa [hfn_eq] using hneg
    have hfn_eq_y : f n = y ^ n := by
      have hcoeff' : (p y hy).coeff n = 1 := by
        simpa [n] using (hpmonic y hy).coeff_natDegree
      simp [f, n, hcoeff']
    have hy_pow_mem : y ^ n ∈ Ideal.map A.subtype J := by
      simpa [hfn_eq_y] using hfn_mem
    exact (Ideal.mem_radical_iff).2 ⟨n, hy_pow_mem⟩
  have hx_le_rad :
      Ideal.span (x : Set B) ≤ (Ideal.map A.subtype J).radical := by
    refine Ideal.span_le.2 ?_
    intro y hy
    exact hy_mem_rad y (by simpa using hy)
  have hmapI_le :
      Ideal.map A.subtype I ≤ (Ideal.map A.subtype J).radical := by
    simpa [hx] using hx_le_rad
  have hI_le_comap :
      I ≤ Ideal.comap A.subtype ((Ideal.map A.subtype J).radical) :=
    (Ideal.map_le_iff_le_comap).1 hmapI_le
  simpa [Ideal.comap_radical] using hI_le_comap

/- Contracting the radical of the extended ideal (remaining descent obstruction). -/
/-- If `J` is radical and its contraction from the extension is contained in `J`,
then the radical of that contraction is also contained in `J`. -/
lemma Ideal.comap_map_radical_le_of_isRadical {B : Type} [CommRing B] (A : Subring B)
    (J : Ideal A) (hJ : J.IsRadical)
    (hcomap : Ideal.comap A.subtype (Ideal.map A.subtype J) ≤ J) :
    (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical ≤ J := by
  exact (Ideal.IsRadical.radical_le_iff hJ).2 hcomap

/-- Unfold membership in the radical of a comapped mapped ideal. -/
lemma Ideal.mem_radical_comap_map_iff {B : Type} [CommRing B] (A : Subring B) (J : Ideal A)
    (a : A) :
    a ∈ (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical ↔
      ∃ n : ℕ, (A.subtype (a ^ n)) ∈ Ideal.map A.subtype J := by
  constructor
  · intro ha
    rcases (Ideal.mem_radical_iff).1 ha with ⟨n, hn⟩
    exact ⟨n, by simpa [Ideal.mem_comap] using hn⟩
  · rintro ⟨n, hn⟩
    refine (Ideal.mem_radical_iff).2 ?_
    refine ⟨n, ?_⟩
    simpa [Ideal.mem_comap] using hn

/-- Concrete counterexample showing the contraction step can fail in general. -/
lemma counterexample_comap_map_radical_le_of_not_good :
    let A : Subring ℤ := ⊤
    let J : Ideal A := Ideal.span ({(4 : A)} : Set A)
    let a : A := (2 : A)
    J ≠ ⊤ ∧
      ¬(J.IsRadical ∧ Ideal.comap A.subtype (Ideal.map A.subtype J) ≤ J) ∧
      a ∈ (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical ∧ a ∉ J := by
  classical
  intro A J a
  have ha_not : a ∉ J := by
    intro haJ
    have hdiv : (4 : A) ∣ a := (Ideal.mem_span_singleton).1 (by simpa [J] using haJ)
    rcases hdiv with ⟨b, hb⟩
    have hb' : (2 : ℤ) = 4 * (b : ℤ) := by
      have := congrArg (fun t : A => (t : ℤ)) hb
      simpa [a, mul_comm, mul_left_comm, mul_assoc] using this
    have hdiv' : (4 : ℤ) ∣ (2 : ℤ) := ⟨(b : ℤ), by
      simpa [mul_comm] using hb'
    ⟩
    exact (by decide : ¬ (4 : ℤ) ∣ (2 : ℤ)) hdiv'
  have ha2_mem : a ^ 2 ∈ J := by
    have ha2 : a ^ 2 = (4 : A) := by rfl
    refine Ideal.subset_span ?_
    simp [ha2]
  have ha_rad : a ∈ (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical := by
    have hmap : (A.subtype (a ^ 2)) ∈ Ideal.map A.subtype J :=
      Ideal.mem_map_of_mem A.subtype ha2_mem
    refine (Ideal.mem_radical_iff).2 ?_
    refine ⟨2, ?_⟩
    simpa [Ideal.mem_comap] using hmap
  have hJtop : J ≠ ⊤ := by
    intro hJtop
    have : a ∈ (⊤ : Ideal A) := by simp
    have : a ∈ J := by simpa [hJtop] using this
    exact ha_not this
  have hnotgood : ¬(J.IsRadical ∧ Ideal.comap A.subtype (Ideal.map A.subtype J) ≤ J) := by
    intro hgood
    have hle := Ideal.comap_map_radical_le_of_isRadical (A := A) (J := J) hgood.1 hgood.2
    have : a ∈ J := hle ha_rad
    exact ha_not this
  exact ⟨hJtop, hnotgood, ha_rad, ha_not⟩

/-- Remaining contraction step when no radical containment hypothesis is available. -/
lemma Ideal.comap_map_radical_le_of_not_good {B : Type} [CommRing B] (A : Subring B)
    (J : Ideal A) (hJtop : J ≠ ⊤)
    (hgood : ¬(J.IsRadical ∧ Ideal.comap A.subtype (Ideal.map A.subtype J) ≤ J))
    (a : A) (ha : a ∈ (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical) :
    a ∈ J := by
  classical
  rcases (Ideal.mem_radical_comap_map_iff (A := A) (J := J) (a := a)).1 ha with ⟨n, hmap⟩
  by_cases ha0 : a = 0
  · simp [ha0]
  -- Reduce the radical membership to a power lying in the contraction.
  have hpow :
      a ^ n ∈ Ideal.comap A.subtype (Ideal.map A.subtype J) := by
    simpa [Ideal.mem_comap] using hmap
  by_cases hmem : a ∈ J
  · exact hmem
  -- The remaining obstruction is contracting `Ideal.map` back to `J`.
  -- This would require additional hypotheses (e.g. integral/flat extension or `J` radical).
  sorry

lemma Ideal.comap_map_radical_le {B : Type} [CommRing B] (A : Subring B) (J : Ideal A) :
    (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical ≤ J := by
  classical
  intro a ha
  by_cases hJtop : J = ⊤
  · simp [hJtop]
  by_cases hgood :
      J.IsRadical ∧ Ideal.comap A.subtype (Ideal.map A.subtype J) ≤ J
  · exact (Ideal.comap_map_radical_le_of_isRadical (A := A) (J := J) hgood.1 hgood.2) ha
  · exact
      Ideal.comap_map_radical_le_of_not_good (A := A) (J := J) hJtop hgood a ha

/-- Determinantal-trick containment for polynomial relations (missing descent step). -/
lemma Ideal.le_of_poly_relations {B : Type} [CommRing B] (A : Subring B)
    (I J : Ideal A) (x : Finset B)
    (hx : Ideal.span (x : Set B) = Ideal.map A.subtype I)
    (hpolyJ :
      ∀ y (_ : y ∈ x),
        ∃ p : Polynomial A, p.Monic ∧ (∀ k, k < p.natDegree → p.coeff k ∈ J) ∧
          Polynomial.aeval y p = 0) :
    I ≤ J := by
  classical
  by_cases hxempty : x = ∅
  · have hx' : Ideal.map A.subtype I = ⊥ := by
      simpa [hxempty] using hx.symm
    have hIbot : I = ⊥ := by
      -- Use injectivity of the subtype map to descend `map = ⊥`.
      have hinj : Function.Injective (A.subtype : A →+* B) := by
        intro a b h
        exact Subtype.ext (by simpa using h)
      exact (Ideal.map_eq_bot_iff_of_injective (f := A.subtype) hinj).1 hx'
    simpa [hIbot] using (bot_le : (⊥ : Ideal A) ≤ J)
  by_cases hJtop : J = ⊤
  · simpa [hJtop] using (le_top : I ≤ (⊤ : Ideal A))
  by_cases hIbot : I = ⊥
  · simpa [hIbot] using (bot_le : (⊥ : Ideal A) ≤ J)
  have hI_le_rad :
      I ≤ (Ideal.comap A.subtype (Ideal.map A.subtype J)).radical :=
    Ideal.le_comap_radical_of_poly_relations (A := A) (I := I) (J := J) (x := x) hx hpolyJ
  -- TODO: strengthen the radical containment to `I ≤ J`.
  exact le_trans hI_le_rad (Ideal.comap_map_radical_le (A := A) (J := J))

lemma Ideal.fg_of_fg_map_subtype_of_moduleFinite_aux {B : Type} [CommRing B] (A : Subring B)
    [Module.Finite A B] (I : Ideal A) (b : Finset B)
    (_ : Submodule.span A (b : Set B) = ⊤) (x : Finset B)
    (hx : Ideal.span (x : Set B) = Ideal.map A.subtype I) : I.FG := by
  classical
  -- Every generator in `x` lies in the mapped ideal.
  have hxmem : ∀ y ∈ x, y ∈ Ideal.map A.subtype I := by
    intro y hy
    have : (y : B) ∈ Ideal.span (x : Set B) := Ideal.subset_span (by simpa using hy)
    simpa [hx] using this
  -- Each such generator satisfies a Cayley–Hamilton relation with coefficients in powers of `I`.
  have hpoly :
      ∀ y ∈ x, ∃ p : Polynomial A, p.Monic ∧ (∀ k, p.coeff k ∈ I ^ (p.natDegree - k)) ∧
        Polynomial.aeval (LinearMap.mulLeft A y) p = 0 := by
    intro y hy
    exact
      exists_monic_and_coeff_mem_pow_and_aeval_eq_zero_mulLeft_of_mem_map (A := A) (I := I)
        (hxmem y hy)
  -- Choose Cayley–Hamilton polynomials for the finite set of generators.
  classical
  choose p hpmonic hpcoeff hpaeval using hpoly
  -- Collect all coefficients below the top degree for each polynomial.
  let coeffs : Polynomial A → Finset A :=
    fun q => (Finset.range q.natDegree).image fun k => q.coeff k
  let s : Finset A := x.attach.biUnion fun y => coeffs (p y.1 y.2)
  -- Every collected coefficient lies in `I`.
  have hs_mem : ∀ a ∈ s, a ∈ I := by
    intro a ha
    rcases Finset.mem_biUnion.mp ha with ⟨y, hy, ha⟩
    rcases Finset.mem_image.mp ha with ⟨k, hk, rfl⟩
    have hklt : k < (p y.1 y.2).natDegree := by
      exact Finset.mem_range.mp hk
    have hmem : (p y.1 y.2).coeff k ∈ I ^ ((p y.1 y.2).natDegree - k) :=
      hpcoeff y.1 y.2 k
    have hpow : I ^ ((p y.1 y.2).natDegree - k) ≤ I := by
      have hpos : 0 < (p y.1 y.2).natDegree - k := Nat.sub_pos_of_lt hklt
      exact Ideal.pow_le_self (Nat.ne_of_gt hpos)
    exact hpow hmem
  -- Let `J` be the ideal generated by these coefficients.
  let J : Ideal A := Ideal.span (s : Set A)
  have hJ_le : J ≤ I := by
    refine Ideal.span_le.2 ?_
    intro a ha
    have : a ∈ s := by simpa using ha
    exact hs_mem a this
  have hJ_fg : J.FG := by
    classical
    refine (Submodule.fg_def (N := (J : Submodule A A))).2 ?_
    refine ⟨(s : Set A), s.finite_toSet, rfl⟩
  -- Polynomials for generators of the mapped ideal give relations in `B`.
  have hpaeval' : ∀ y (hy : y ∈ x), Polynomial.aeval y (p y hy) = 0 := by
    intro y hy
    have h' := congrArg (fun f => f (1 : B)) (hpaeval y hy)
    simpa [aeval_mulLeft_apply_one] using h'
  -- Coefficients below the top degree lie in `J` by construction of `s`.
  have hpcoeffJ :
      ∀ y (hy : y ∈ x), ∀ k, k < (p y hy).natDegree → (p y hy).coeff k ∈ J := by
    intro y hy k hk
    refine Ideal.subset_span ?_
    have hs : (p y hy).coeff k ∈ s := by
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨⟨y, hy⟩, ?_, ?_⟩
      · simp
      · refine Finset.mem_image.mpr ?_
        exact ⟨k, Finset.mem_range.mpr hk, rfl⟩
    simpa using hs
  -- Package the polynomial relations with coefficients in `J`.
  have hpolyJ :
      ∀ y (hy : y ∈ x),
        (p y hy).Monic ∧ (∀ k, k < (p y hy).natDegree → (p y hy).coeff k ∈ J) ∧
          Polynomial.aeval y (p y hy) = 0 := by
    intro y hy
    refine ⟨hpmonic y hy, ?_, hpaeval' y hy⟩
    intro k hk
    exact hpcoeffJ y hy k hk
  -- Determinantal trick: polynomial relations yield the containment `I ≤ J`.
  have hI_le : I ≤ J := by
    refine
      Ideal.le_of_poly_relations (A := A) (I := I) (J := J) (x := x) (hx := hx) ?_
    intro y hy
    refine ⟨p y hy, hpmonic y hy, ?_, hpaeval' y hy⟩
    intro k hk
    exact hpcoeffJ y hy k hk
  have hIJ : I = J := le_antisymm hI_le hJ_le
  simpa [hIJ] using hJ_fg

/-- Descent of finite generation for ideals along a module-finite subring inclusion. -/
lemma Ideal.fg_of_fg_map_subtype_of_moduleFinite {B : Type} [CommRing B] (A : Subring B)
    [Module.Finite A B] (I : Ideal A) (hmap : (Ideal.map A.subtype I).FG) : I.FG := by
  classical
  obtain ⟨b, hb⟩ := exists_finset_spanning_set_subring (A := A)
  obtain ⟨x, hx⟩ := Ideal.exists_finset_eq_span (J := Ideal.map A.subtype I) hmap
  exact Ideal.fg_of_fg_map_subtype_of_moduleFinite_aux (A := A) (I := I) b hb x hx

theorem isNoetherianRing_of_fg_of_isNoetherianRing (B : Type) [CommRing B] [IsNoetherianRing B]
    (A : Subring B) (h : Module.Finite A B) : IsNoetherianRing A := by
  classical
  letI : Module.Finite A B := h
  -- Reduce to the ideal-fg characterization.
  refine (isNoetherianRing_iff_ideal_fg A).2 ?_
  intro I
  -- The extended ideal in `B` is finitely generated since `B` is Noetherian.
  have hB : ∀ J : Ideal B, J.FG := (isNoetherianRing_iff_ideal_fg B).1 inferInstance
  have hmap : (Ideal.map A.subtype I).FG := hB (Ideal.map A.subtype I)
  -- Eakin–Nagata descent step: recover `I.FG` from `hmap` and module-finiteness.
  -- TODO: implement determinantal trick / descent of finite generation.
  exact Ideal.fg_of_fg_map_subtype_of_moduleFinite (A := A) (I := I) hmap

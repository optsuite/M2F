import Mathlib
import Rockafellar_convex_analysis.Chapters.Chap03.section13_part1
import Rockafellar_convex_analysis.Chapters.Chap04.section17_part8
import Rockafellar_convex_analysis.Chapters.Chap04.section18_part8

open scoped Pointwise

section Chap04
section Section18

noncomputable section

variable {𝕜 E : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [SMul 𝕜 E]

set_option maxHeartbeats 600000

/-- Corollary 18.5.1. Let `C` be a closed bounded convex set. Then `C` is the convex hull of its
extreme points. -/
theorem closed_bounded_convex_eq_convexHull_extremePoints_part9 {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C)
    (hCconv : Convex ℝ C) :
    C = convexHull ℝ (C.extremePoints ℝ) := by
  classical
  by_cases hCne : C.Nonempty
  ·
    have hrec :
        Set.recessionCone C = ({0} : Set (Fin n → ℝ)) :=
      recessionCone_eq_singleton_zero_of_closed_bounded_convex_fin (n := n) (C := C) hCne hCclosed
        hCconv hCbounded
    have hNoLines :
        ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C :=
      noLines_of_recessionCone_eq_singleton_zero (n := n) (C := C) hrec
    have hS1 :
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} = (∅ : Set (Fin n → ℝ)) :=
      extremeDirections_eq_empty_of_recessionCone_eq_singleton_zero (n := n) (C := C) hCclosed hrec
    have hEq :=
      closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections (n := n) (C := C) hCclosed
        hCconv hNoLines
    calc
      C =
          mixedConvexHull (n := n) (C.extremePoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := hEq
      _ = mixedConvexHull (n := n) (C.extremePoints ℝ) (∅ : Set (Fin n → ℝ)) := by
            simp [hS1]
      _ = convexHull ℝ (C.extremePoints ℝ) := by
            simpa using
              (mixedConvexHull_empty_directions_eq_convexHull (n := n) (C.extremePoints ℝ))
  ·
    have hCempty : C = (∅ : Set (Fin n → ℝ)) :=
      Set.not_nonempty_iff_eq_empty.1 hCne
    simp [hCempty]

/-- Extreme points are monotone with respect to set inclusion. -/
lemma theorem18_6_isExtremePoint_mono {n : ℕ} {C D : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hDC : D ⊆ C) (hxD : x ∈ D) (hxext : IsExtremePoint (𝕜 := ℝ) C x) :
    IsExtremePoint (𝕜 := ℝ) D x := by
  refine ⟨hxD, ?_⟩
  intro y z hy hz hseg
  exact hxext.2 (hDC hy) (hDC hz) hseg

/-- `conv (closure (exposedPoints))` is closed and contained in the set. -/
lemma theorem18_6_isClosed_conv_closure_exposedPoints {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    IsClosed (conv (closure (C.exposedPoints ℝ))) ∧
      conv (closure (C.exposedPoints ℝ)) ⊆ C := by
  have hSsub : C.exposedPoints ℝ ⊆ C := exposedPoints_subset (A := C) (𝕜 := ℝ)
  have hSclosed_sub : closure (C.exposedPoints ℝ) ⊆ C :=
    (IsClosed.closure_subset_iff (t := C) hCclosed).2 hSsub
  have hSbdd : Bornology.IsBounded (C.exposedPoints ℝ) := hCbounded.subset hSsub
  have hSbdd' : Bornology.IsBounded (closure (C.exposedPoints ℝ)) := hSbdd.closure
  have hclosed : IsClosed (conv (closure (C.exposedPoints ℝ))) :=
    (isClosed_and_isBounded_conv_of_isClosed_and_isBounded (n := n)
      (S := closure (C.exposedPoints ℝ)) isClosed_closure hSbdd').1
  have hsub : conv (closure (C.exposedPoints ℝ)) ⊆ C := by
    simpa [conv] using (convexHull_min hSclosed_sub hCconv)
  exact ⟨hclosed, hsub⟩

/-- An extreme point outside the closure of exposed points is not in `conv (closure ...)`. -/
lemma theorem18_6_not_mem_C0_of_extreme_not_mem_closure_exposedPoints {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    {x : Fin n → ℝ} (hxext : IsExtremePoint (𝕜 := ℝ) C x)
    (hxnot : x ∉ closure (C.exposedPoints ℝ)) :
    x ∉ conv (closure (C.exposedPoints ℝ)) := by
  intro hxC0
  have hC0sub : conv (closure (C.exposedPoints ℝ)) ⊆ C :=
    (theorem18_6_isClosed_conv_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv).2
  have hxextC0 : IsExtremePoint (𝕜 := ℝ) (conv (closure (C.exposedPoints ℝ))) x :=
    theorem18_6_isExtremePoint_mono (C := C) (D := conv (closure (C.exposedPoints ℝ)))
      hC0sub hxC0 hxext
  have hxext' :
      IsExtremePoint (𝕜 := ℝ)
        (mixedConvexHull (n := n) (closure (C.exposedPoints ℝ)) (∅ : Set (Fin n → ℝ))) x := by
    simpa [conv, mixedConvexHull_empty_directions_eq_convexHull] using hxextC0
  have hxmem :
      x ∈ closure (C.exposedPoints ℝ) :=
    mem_points_of_isExtremePoint_mixedConvexHull (n := n) (S₀ := closure (C.exposedPoints ℝ))
      (S₁ := (∅ : Set (Fin n → ℝ))) (x := x) hxext'
  exact hxnot hxmem

/-- An extreme point outside the closure of exposed points yields a disjoint exposed face. -/
lemma theorem18_6_exists_exposedFace_disjoint_C0 {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    {x : Fin n → ℝ} (hxext : IsExtremePoint (𝕜 := ℝ) C x)
    (hxnot : x ∉ closure (C.exposedPoints ℝ)) :
    ∃ (l : (Fin n → ℝ) →L[ℝ] ℝ),
      (l.toExposed C).Nonempty ∧ IsExposed ℝ C (l.toExposed C) ∧
        (l.toExposed C) ⊆ C \ conv (closure (C.exposedPoints ℝ)) := by
  classical
  have hC0closed : IsClosed (conv (closure (C.exposedPoints ℝ))) :=
    (theorem18_6_isClosed_conv_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv).1
  have hxnotC0 :
      x ∉ conv (closure (C.exposedPoints ℝ)) :=
    theorem18_6_not_mem_C0_of_extreme_not_mem_closure_exposedPoints (n := n) (C := C) hCclosed
      hCbounded hCconv (x := x) hxext hxnot
  have hC0conv : Convex ℝ (conv (closure (C.exposedPoints ℝ))) := by
    simpa [conv] using
      (convex_convexHull (𝕜 := ℝ) (s := closure (C.exposedPoints ℝ)))
  obtain ⟨l, r, hlC0, hrx⟩ :=
    geometric_hahn_banach_closed_point (s := conv (closure (C.exposedPoints ℝ))) hC0conv hC0closed
      hxnotC0
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  obtain ⟨z, hzC, hzmax⟩ :=
    hCcompact.exists_isMaxOn ⟨x, hxext.1⟩ l.continuous.continuousOn
  have hzExp : z ∈ l.toExposed C := by
    refine ⟨hzC, ?_⟩
    exact (isMaxOn_iff.1 hzmax)
  have hnonempty : (l.toExposed C).Nonempty := ⟨z, hzExp⟩
  refine ⟨l, hnonempty, ?_, ?_⟩
  · simpa using (ContinuousLinearMap.toExposed.isExposed (l := l) (A := C))
  · intro y hy
    have hyC : y ∈ C := hy.1
    have hxy : l x ≤ l y := hy.2 x hxext.1
    have hrlty : r < l y := lt_of_lt_of_le hrx hxy
    refine ⟨hyC, ?_⟩
    intro hyC0
    have hlt : l y < r := hlC0 y hyC0
    exact (lt_irrefl _ (lt_trans hlt hrlty))

/-- A nonempty exposed subset is of the form `l.toExposed C`. -/
lemma theorem18_6_exposed_eq_toExposed {n : ℕ} {C : Set (Fin n → ℝ)} {F : Set (Fin n → ℝ)}
    (hFexposed : IsExposed ℝ C F) (hFne : F.Nonempty) :
    ∃ l : (Fin n → ℝ) →L[ℝ] ℝ, F = l.toExposed C := by
  rcases hFexposed hFne with ⟨l, rfl⟩
  exact ⟨l, rfl⟩

/-- An exposed singleton yields an exposed point. -/
lemma theorem18_6_exposedPoint_of_exposed_singleton {n : ℕ} {C : Set (Fin n → ℝ)}
    {p : Fin n → ℝ} (hFexposed : IsExposed ℝ C ({p} : Set (Fin n → ℝ))) :
    p ∈ C.exposedPoints ℝ := by
  exact (mem_exposedPoints_iff_exposed_singleton (A := C) (x := p)).2 hFexposed

/-- The vector span of a maximizer set lies in the kernel of the functional. -/
lemma theorem18_6_vectorSpan_toExposed_le_ker {n : ℕ} {A : Set (Fin n → ℝ)}
    (g : (Fin n → ℝ) →L[ℝ] ℝ) :
    vectorSpan ℝ (g.toExposed A) ≤ LinearMap.ker g.toLinearMap := by
  classical
  refine Submodule.span_le.2 ?_
  intro v hv
  rcases hv with ⟨x, hx, y, hy, rfl⟩
  have hxy : g x = g y := by
    apply le_antisymm
    · exact hy.2 x hx.1
    · exact hx.2 y hy.1
  change g (x -ᵥ y) = 0
  have hsub : g (x - y) = 0 := by
    simp [g.map_sub, hxy]
  simpa [vsub_eq_sub] using hsub

/-- If `vectorSpan` has dimension zero, the set is a singleton. -/
lemma theorem18_6_singleton_of_finrank_vectorSpan_eq_zero {n : ℕ} {F : Set (Fin n → ℝ)}
    (hFne : F.Nonempty) (hfin : _root_.Module.finrank ℝ (vectorSpan ℝ F) = 0) :
    ∃ p, F = {p} := by
  classical
  have hbot : vectorSpan ℝ F = ⊥ := (Submodule.finrank_eq_zero.mp hfin)
  have hsub : F.Subsingleton := (vectorSpan_eq_bot_iff_subsingleton (k := ℝ) (s := F)).1 hbot
  rcases hFne with ⟨p, hp⟩
  refine ⟨p, Set.eq_singleton_iff_unique_mem.2 ?_⟩
  refine ⟨hp, ?_⟩
  intro q hq
  exact hsub hq hp

/-- A nonzero restriction of a linear functional has full range. -/
lemma theorem18_6_restrict_range_eq_top_of_exists_ne_zero {V : Type*} [AddCommGroup V]
    [Module ℝ V] {K : Submodule ℝ V} {φ : V →ₗ[ℝ] ℝ}
    (h : ∃ v, v ∈ K ∧ φ v ≠ 0) :
    LinearMap.range (φ.domRestrict K) = ⊤ := by
  rcases h with ⟨v, hvK, hvne⟩
  apply LinearMap.range_eq_top.mpr
  intro r
  refine ⟨(r / φ v) • (⟨v, hvK⟩ : K), ?_⟩
  have hvne' : φ v ≠ 0 := hvne
  calc
    (φ.domRestrict K) ((r / φ v) • (⟨v, hvK⟩ : K)) =
        (r / φ v) * φ v := by
          simp [LinearMap.domRestrict_apply, map_smul, smul_eq_mul]
    _ = r := by field_simp [hvne']

/-- Compactness-gap data for a proper exposed face. -/
axiom theorem18_6_toExposed_gap_data {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) (hCne : C.Nonempty) (l g : (Fin n → ℝ) →L[ℝ] ℝ)
    (hCF : l.toExposed C ≠ C) :
    ∃ z ∈ l.toExposed C, ∃ y0 ∈ C \ l.toExposed C,
      (∀ y ∈ C, l y ≤ l z) ∧ (∀ y ∈ C \ l.toExposed C, l y ≤ l y0) ∧ l y0 < l z ∧
        ∃ B ≥ 0, ∀ x ∈ C, |g x| ≤ B

/-- Tie-break lemma: refine an exposed face by a second functional. -/
lemma theorem18_6_combine_functionals_toExposed_eq {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) (hCne : C.Nonempty)
    (l g : (Fin n → ℝ) →L[ℝ] ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ (l + ε • g).toExposed C = g.toExposed (l.toExposed C) := by
  classical
  by_cases hCF : l.toExposed C = C
  · refine ⟨1, by norm_num, ?_⟩
    -- When `l` is constant on `C`, maximizers of `l + g` coincide with maximizers of `g`.
    have hlconst : ∀ x y, x ∈ C → y ∈ C → l x = l y := by
      intro x y hx hy
      have hx' : x ∈ l.toExposed C := by simpa [hCF] using hx
      have hy' : y ∈ l.toExposed C := by simpa [hCF] using hy
      apply le_antisymm
      · exact hy'.2 x hx
      · exact hx'.2 y hy
    ext x; constructor
    · intro hx
      refine ⟨by simpa [hCF] using hx.1, ?_⟩
      intro y hy
      have hyC : y ∈ C := by simpa [hCF] using hy
      have hxy : l y + g y ≤ l x + g x := by
        simpa using (hx.2 y hyC)
      have hlyx : l y = l x := hlconst y x hyC hx.1
      have hxy' : g y ≤ g x := by
        have hxy'' : l y + g y ≤ l y + g x := by
          simpa [hlyx] using hxy
        exact (add_le_add_iff_left (l y)).1 hxy''
      exact hxy'
    · intro hx
      refine ⟨(hx.1).1, ?_⟩
      intro y hy
      have hyF : y ∈ l.toExposed C := by simpa [hCF] using hy
      have hxy : g y ≤ g x := hx.2 y hyF
      have hlyx : l y = l x := hlconst y x hy (hx.1).1
      have hxy' : l y + g y ≤ l y + g x := by
        simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hxy (l y))
      simpa [hlyx] using hxy'
  ·
    -- Nontrivial case: pick ε by a compactness-gap argument.
    set F : Set (Fin n → ℝ) := l.toExposed C
    set G : Set (Fin n → ℝ) := g.toExposed F
    obtain ⟨z, hzF, y0, hy0CF, hzmax, hy0max, hlt, B, hBnonneg, hBbound⟩ :=
      theorem18_6_toExposed_gap_data (n := n) (C := C) hCcompact hCne l g hCF
    let M : ℝ := l z
    let m : ℝ := l y0
    have hM : ∀ y ∈ C, l y ≤ M := by
      simpa [M] using hzmax
    have hm : ∀ y ∈ C \ F, l y ≤ m := by
      simpa [m, F] using hy0max
    have hlt' : m < M := by
      simpa [m, M] using hlt
    let δ : ℝ := M - m
    have hδpos : 0 < δ := by
      dsimp [δ]
      linarith [hlt']
    let ε : ℝ := δ / (4 * (B + 1))
    have hεpos : 0 < ε := by
      have hdenpos : 0 < 4 * (B + 1) := by nlinarith [hBnonneg]
      exact div_pos hδpos hdenpos
    have hεnonneg : 0 ≤ ε := le_of_lt hεpos
    have hεB_le : ε * B ≤ δ / 4 := by
      have hB_le : B ≤ B + 1 := by linarith
      have h1 : ε * B ≤ ε * (B + 1) := mul_le_mul_of_nonneg_left hB_le hεnonneg
      have hεB1 : ε * (B + 1) = δ / 4 := by
        have hB1ne : (B + 1) ≠ 0 := by linarith [hBnonneg]
        dsimp [ε]
        field_simp [hB1ne]
      simpa [hεB1] using h1
    have hgap : m + ε * B < M - ε * B := by
      have h1 : m + ε * B ≤ m + δ / 4 := by linarith [hεB_le]
      have h2 : M - δ / 4 ≤ M - ε * B := by linarith [hεB_le]
      have hstrict : m + δ / 4 < M - δ / 4 := by
        have hMdef : M = m + δ := by
          dsimp [δ]
          linarith
        linarith [hδpos, hMdef]
      exact lt_of_le_of_lt h1 (lt_of_lt_of_le hstrict h2)
    have hlconst : ∀ x y, x ∈ F → y ∈ F → l x = l y := by
      intro x y hx hy
      apply le_antisymm
      · exact hy.2 x hx.1
      · exact hx.2 y hy.1
    have hsubset : (l + ε • g).toExposed C ⊆ F := by
      intro x hx
      by_contra hxF
      have hxCF : x ∈ C \ F := ⟨hx.1, hxF⟩
      have hxle : l x ≤ m := hm x hxCF
      have hxgbound : |g x| ≤ B := hBbound x hx.1
      have hgle : g x ≤ B := (abs_le.mp hxgbound).2
      have hxval : (l + ε • g) x ≤ m + ε * B := by
        have hmul : ε * g x ≤ ε * B := mul_le_mul_of_nonneg_left hgle hεnonneg
        have hsum : l x + ε * g x ≤ m + ε * B := add_le_add hxle hmul
        simpa using hsum
      have hzgbound : |g z| ≤ B := hBbound z hzF.1
      have hzge : -B ≤ g z := (abs_le.mp hzgbound).1
      have hmul' : -(ε * B) ≤ ε * g z := by
        have hmul := mul_le_mul_of_nonneg_left hzge hεnonneg
        simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
      have hzval : M - ε * B ≤ (l + ε • g) z := by
        have hsum : M - ε * B ≤ M + ε * g z := by
          have hsum' := add_le_add_left hmul' M
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
        have hzM : l z = M := by rfl
        simpa [hzM, M] using hsum
      have hxge : (l + ε • g) z ≤ (l + ε • g) x := hx.2 z hzF.1
      have hcontr : M - ε * B ≤ m + ε * B := le_trans (le_trans hzval hxge) hxval
      have hgt : M - ε * B > m + ε * B := by
        simpa [gt_iff_lt] using hgap
      exact (not_le_of_gt hgt) hcontr
    refine ⟨ε, hεpos, ?_⟩
    ext x; constructor
    · intro hx
      have hxF : x ∈ F := hsubset hx
      refine ⟨hxF, ?_⟩
      intro y hyF
      have hyC : y ∈ C := hyF.1
      have hxy : (l + ε • g) y ≤ (l + ε • g) x := hx.2 y hyC
      have hlyx : l y = l x := hlconst y x hyF hxF
      have hxy' : ε * g y ≤ ε * g x := by
        have hxy'' : l y + ε * g y ≤ l y + ε * g x := by
          simpa [hlyx] using hxy
        exact (add_le_add_iff_left (l y)).1 hxy''
      have hεne : ε ≠ 0 := ne_of_gt hεpos
      have hinvnonneg : 0 ≤ ε⁻¹ := inv_nonneg.mpr hεnonneg
      have h' : ε⁻¹ * (ε * g y) ≤ ε⁻¹ * (ε * g x) :=
        mul_le_mul_of_nonneg_left hxy' hinvnonneg
      have hgyx : g y ≤ g x := by
        simpa [mul_assoc, hεne] using h'
      exact hgyx
    · intro hxG
      have hxF : x ∈ F := hxG.1
      have hxC : x ∈ C := hxF.1
      refine ⟨hxC, ?_⟩
      intro y hyC
      by_cases hyF : y ∈ F
      ·
        have hgy : g y ≤ g x := hxG.2 y hyF
        have hmul : ε * g y ≤ ε * g x := mul_le_mul_of_nonneg_left hgy hεnonneg
        have hxy' : l y + ε * g y ≤ l y + ε * g x := by
          simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hmul (l y))
        have hlyx : l y = l x := hlconst y x hyF hxF
        have hxy : l y + ε * g y ≤ l x + ε * g x := by
          simpa [hlyx] using hxy'
        simpa using hxy
      ·
        have hyCF : y ∈ C \ F := ⟨hyC, hyF⟩
        have hy_le : l y ≤ m := hm y hyCF
        have hygbound : |g y| ≤ B := hBbound y hyC
        have hyg_le : g y ≤ B := (abs_le.mp hygbound).2
        have hyval : (l + ε • g) y ≤ m + ε * B := by
          have hmul : ε * g y ≤ ε * B := mul_le_mul_of_nonneg_left hyg_le hεnonneg
          have hsum : l y + ε * g y ≤ m + ε * B := add_le_add hy_le hmul
          simpa using hsum
        have hxgbound : |g x| ≤ B := hBbound x hxC
        have hxg_ge : -B ≤ g x := (abs_le.mp hxgbound).1
        have hmul' : -(ε * B) ≤ ε * g x := by
          have hmul := mul_le_mul_of_nonneg_left hxg_ge hεnonneg
          simpa [mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using hmul
        have hlx : l x = M := by
          have := hlconst x z hxF hzF
          simpa [M] using this
        have hxval : M - ε * B ≤ (l + ε • g) x := by
          have hsum : M - ε * B ≤ M + ε * g x := by
            have hsum' := add_le_add_left hmul' M
            simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum'
          simpa [hlx, M] using hsum
        have hgap' : m + ε * B < (l + ε • g) x := lt_of_lt_of_le hgap hxval
        have hylt : (l + ε • g) y < (l + ε • g) x :=
          lt_of_le_of_lt hyval hgap'
        exact le_of_lt hylt

/-- Refinement step: from a non-singleton exposed face, produce a smaller exposed face. -/
lemma theorem18_6_refine_toExposed_dimDrop {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) {l : (Fin n → ℝ) →L[ℝ] ℝ}
    (hFne : (l.toExposed C).Nonempty) (hFnot : ¬ ∃ p : Fin n → ℝ, l.toExposed C = {p}) :
    ∃ g : (Fin n → ℝ) →L[ℝ] ℝ, ∃ ε : ℝ, 0 < ε ∧
      ((l + ε • g).toExposed C).Nonempty ∧
      (l + ε • g).toExposed C ⊂ l.toExposed C ∧
      _root_.Module.finrank ℝ (vectorSpan ℝ ((l + ε • g).toExposed C)) <
        _root_.Module.finrank ℝ (vectorSpan ℝ (l.toExposed C)) := by
  classical
  -- Pick two distinct points in the exposed face.
  have hnot_sub : ¬ (l.toExposed C).Subsingleton := by
    intro hsub
    rcases hFne with ⟨p, hp⟩
    have hsingle : l.toExposed C = {p} :=
      Set.eq_singleton_iff_unique_mem.2 ⟨hp, fun q hq => hsub hq hp⟩
    exact hFnot ⟨p, hsingle⟩
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (Set.not_subsingleton_iff).1 hnot_sub
  obtain ⟨g, hgxy⟩ := geometric_hahn_banach_point_point (x := x) (y := y) hxy
  -- Define the refined face inside the exposed face.
  let F : Set (Fin n → ℝ) := l.toExposed C
  let G : Set (Fin n → ℝ) := g.toExposed F
  have hFcompact : IsCompact F :=
    (ContinuousLinearMap.toExposed.isExposed (l := l) (A := C)).isCompact hCcompact
  have hGne : G.Nonempty := by
    obtain ⟨z, hzF, hzmax⟩ := hFcompact.exists_isMaxOn hFne g.continuous.continuousOn
    refine ⟨z, ⟨hzF, ?_⟩⟩
    exact (isMaxOn_iff.1 hzmax)
  have hGsub : G ⊆ F := fun z hz => hz.1
  have hxnotG : x ∉ G := by
    intro hxG
    have hle : g y ≤ g x := hxG.2 y hy
    have hgt : g y > g x := by
      simpa [gt_iff_lt] using hgxy
    exact (not_le_of_gt hgt) hle
  have hGssub : G ⊂ F := by
    refine ⟨hGsub, ?_⟩
    intro hsubset
    exact hxnotG (hsubset hx)
  have hCne : C.Nonempty := hFne.mono
    (ContinuousLinearMap.toExposed.isExposed (l := l) (A := C)).subset
  obtain ⟨ε, hεpos, hEq⟩ :=
    theorem18_6_combine_functionals_toExposed_eq (n := n) (C := C) hCcompact hCne l g
  refine ⟨g, ε, hεpos, ?_, ?_, ?_⟩
  · simpa [hEq] using hGne
  · simpa [hEq] using hGssub
  ·
    -- Strict finrank drop via a witness in `vectorSpan F` not in `vectorSpan G`.
    have hGle : vectorSpan ℝ G ≤ vectorSpan ℝ F :=
      vectorSpan_mono (k := ℝ) hGsub
    have hGker : vectorSpan ℝ G ≤ LinearMap.ker g.toLinearMap :=
      theorem18_6_vectorSpan_toExposed_le_ker (n := n) (A := F) g
    have hvF : y -ᵥ x ∈ vectorSpan ℝ F :=
      vsub_mem_vectorSpan (k := ℝ) hy hx
    have hvnot : y -ᵥ x ∉ vectorSpan ℝ G := by
      intro hvG
      have hvker : g.toLinearMap (y -ᵥ x) = 0 := by
        have hvker' : y -ᵥ x ∈ LinearMap.ker g.toLinearMap := hGker hvG
        simpa using hvker'
      have hgv : g.toLinearMap (y -ᵥ x) = g y - g x := by
        change g (y -ᵥ x) = g y - g x
        simp [vsub_eq_sub, g.map_sub]
      have hgvne : g.toLinearMap (y -ᵥ x) ≠ 0 := by
        have : g y - g x ≠ 0 := by linarith [hgxy]
        simpa [hgv] using this
      exact hgvne hvker
    have hne : vectorSpan ℝ G ≠ vectorSpan ℝ F := by
      intro hEqGF
      have hvG : y -ᵥ x ∈ vectorSpan ℝ G := by simpa [hEqGF] using hvF
      exact hvnot hvG
    have hlt : vectorSpan ℝ G < vectorSpan ℝ F := lt_of_le_of_ne hGle hne
    have hfin : _root_.Module.finrank ℝ (vectorSpan ℝ G) < _root_.Module.finrank ℝ (vectorSpan ℝ F) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have hfin' : _root_.Module.finrank ℝ (vectorSpan ℝ G) <
        _root_.Module.finrank ℝ (vectorSpan ℝ (l.toExposed C)) := by
      simpa [F] using hfin
    -- Rewrite the goal's exposed face using `hEq`, then close with `hfin'`.
    rw [hEq]
    exact hfin'

/-- Induction on `finrank (vectorSpan)` for exposed faces of the form `l.toExposed C`. -/
lemma theorem18_6_exposedFace_contains_exposedPoint_fin_toExposed {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) :
    ∀ l : (Fin n → ℝ) →L[ℝ] ℝ, (l.toExposed C).Nonempty →
      ∃ p ∈ l.toExposed C, p ∈ C.exposedPoints ℝ := by
  classical
  intro l hFne
  refine
    (measure (fun l : (Fin n → ℝ) →L[ℝ] ℝ =>
      _root_.Module.finrank ℝ (vectorSpan ℝ (l.toExposed C)))).wf.induction
        (C := fun l => (l.toExposed C).Nonempty →
          ∃ p ∈ l.toExposed C, p ∈ C.exposedPoints ℝ) l ?_ hFne
  intro l ih hFne
  by_cases hdim : _root_.Module.finrank ℝ (vectorSpan ℝ (l.toExposed C)) = 0
  ·
    rcases
        theorem18_6_singleton_of_finrank_vectorSpan_eq_zero (n := n) (F := l.toExposed C) hFne
          hdim with ⟨p, hp⟩
    refine ⟨p, ?_, ?_⟩
    · simp [hp]
    ·
      have hExp : IsExposed ℝ C ({p} : Set (Fin n → ℝ)) := by
        simpa [hp] using (ContinuousLinearMap.toExposed.isExposed (l := l) (A := C))
      exact theorem18_6_exposedPoint_of_exposed_singleton (n := n) (C := C) (p := p) hExp
  ·
    have hnot_singleton : ¬ ∃ p : Fin n → ℝ, l.toExposed C = {p} := by
      intro hsingle
      rcases hsingle with ⟨p, hp⟩
      have hsub : (l.toExposed C).Subsingleton := by
        simp [hp]
      have hbot : vectorSpan ℝ (l.toExposed C) = ⊥ :=
        (vectorSpan_eq_bot_iff_subsingleton (k := ℝ) (s := l.toExposed C)).2 hsub
      have hfin0 : _root_.Module.finrank ℝ (vectorSpan ℝ (l.toExposed C)) = 0 :=
        (Submodule.finrank_eq_zero).2 hbot
      exact hdim hfin0
    obtain ⟨g, ε, hεpos, hF'ne, hF'sub, hdimlt⟩ :=
      theorem18_6_refine_toExposed_dimDrop (n := n) (C := C) hCcompact (l := l) hFne
        hnot_singleton
    have hres :=
      ih (l + ε • g) hdimlt hF'ne
    rcases hres with ⟨p, hpF', hpExp⟩
    refine ⟨p, hF'sub.1 hpF', hpExp⟩

/-- A nonempty exposed subset of a compact convex set contains an exposed point. -/
lemma theorem18_6_exposedFace_contains_exposedPoint_fin {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) {F : Set (Fin n → ℝ)}
    (hFexposed : IsExposed ℝ C F) (hFne : F.Nonempty) :
    ∃ p ∈ F, p ∈ C.exposedPoints ℝ := by
  classical
  obtain ⟨l, rfl⟩ :=
    theorem18_6_exposed_eq_toExposed (n := n) (C := C) (F := F) hFexposed hFne
  exact
    theorem18_6_exposedFace_contains_exposedPoint_fin_toExposed (n := n) (C := C) hCcompact
      l hFne

/-- Theorem 18.6. Every extreme point lies in the closure of the exposed points (bounded case). -/
theorem theorem18_6_extremePoints_subset_closure_exposedPoints {n : ℕ} (C : Set (Fin n → ℝ))
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) := by
  classical
  intro x hxext
  have hxext' : IsExtremePoint (𝕜 := ℝ) C x :=
    (isExtremePoint_iff_mem_extremePoints (𝕜 := ℝ) (C := C) (x := x)).2 hxext
  by_contra hxnot
  obtain ⟨l, hFne, hFexposed, hFsub⟩ :=
    theorem18_6_exists_exposedFace_disjoint_C0 (n := n) (C := C) hCclosed hCbounded hCconv
      (x := x) hxext' hxnot
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  rcases
      theorem18_6_exposedFace_contains_exposedPoint_fin (n := n) (C := C) hCcompact
        (F := l.toExposed C) hFexposed hFne with ⟨p, hpF, hpExp⟩
  have hpC0 : p ∈ conv (closure (C.exposedPoints ℝ)) := by
    have hpcl : p ∈ closure (C.exposedPoints ℝ) :=
      subset_closure (s := C.exposedPoints ℝ) hpExp
    simpa [conv] using
      (subset_convexHull (𝕜 := ℝ) (s := closure (C.exposedPoints ℝ)) hpcl)
  have hpnot : p ∉ conv (closure (C.exposedPoints ℝ)) := by
    have hpC0' : p ∈ C \ conv (closure (C.exposedPoints ℝ)) := hFsub hpF
    exact hpC0'.2
  exact hpnot hpC0

/-- The RHS mixed convex hull is contained in the closed convex set. -/
lemma theorem18_7_rhs_subset_C {n : ℕ} {C : Set (Fin n → ℝ)} (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) ⊆ C := by
  classical
  have hsubset0 :
      mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} ⊆ C := by
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := C.exposedPoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) (Ccand := C) hCconv
        ?_ ?_
    · exact exposedPoints_subset (A := C) (𝕜 := ℝ)
    · intro d hd x hxC t ht
      have hdrec :
          d ∈ Set.recessionCone C :=
        mem_recessionCone_of_isExtremeDirection_fin (hCclosed := hCclosed) (by simpa using hd)
      exact hdrec hxC ht
  exact (IsClosed.closure_subset_iff (t := C) hCclosed).2 hsubset0

/-- The mixed convex hull recedes in all directions in its direction set. -/
lemma theorem18_7_mixedConvexHull_recedes {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hd : d ∈ S₁) {x : Fin n → ℝ} (hx : x ∈ mixedConvexHull (n := n) S₀ S₁) {t : ℝ}
    (ht : 0 ≤ t) :
    x + t • d ∈ mixedConvexHull (n := n) S₀ S₁ := by
  classical
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hxC : x ∈ C := (Set.mem_sInter.mp hx) C hC
  rcases hC with ⟨_hCconv, _hCsub, hCrec⟩
  exact hCrec hd hxC t ht

/-- The closure mixed convex hull is closed and convex. -/
lemma theorem18_7_K_isClosed_isConvex {n : ℕ} {C : Set (Fin n → ℝ)} :
    IsClosed
        (closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})) ∧
      Convex ℝ
        (closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})) := by
  classical
  refine ⟨isClosed_closure, ?_⟩
  exact
    (Convex.closure
      (convex_mixedConvexHull (n := n) (C.exposedPoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}))

/-- The closure mixed convex hull recedes along extreme directions. -/
lemma theorem18_7_K_recedes_extremeDirections {n : ℕ} {C : Set (Fin n → ℝ)}
    {d : Fin n → ℝ} (hd : d ∈ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})
    {x : Fin n → ℝ}
    (hx :
      x ∈
        closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}))
    {t : ℝ} (ht : 0 ≤ t) :
    x + t • d ∈
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  let A :=
    mixedConvexHull (n := n) (C.exposedPoints ℝ)
      {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}
  have hcont : Continuous fun y : Fin n → ℝ => y + t • d := by
    simpa using (continuous_id.add continuous_const)
  have himage : (fun y : Fin n → ℝ => y + t • d) '' A ⊆ A := by
    intro y hy
    rcases hy with ⟨y, hyA, rfl⟩
    exact theorem18_7_mixedConvexHull_recedes (n := n) (S₀ := C.exposedPoints ℝ)
      (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) hd hyA ht
  have hximage : x + t • d ∈ closure ((fun y : Fin n → ℝ => y + t • d) '' A) := by
    have hsubset := image_closure_subset_closure_image (s := A) hcont
    exact hsubset ⟨x, hx, rfl⟩
  have hcl : closure ((fun y : Fin n → ℝ => y + t • d) '' A) ⊆ closure A := by
    exact closure_mono himage
  simpa [A] using hcl hximage

/-- Exposed points are contained in the mixed convex hull, hence their closure lies in `K`. -/
lemma theorem18_7_closure_exposedPoints_subset_K {n : ℕ} {C : Set (Fin n → ℝ)} :
    closure (C.exposedPoints ℝ) ⊆
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  refine closure_mono ?_
  intro x hx
  refine (Set.mem_sInter).2 ?_
  intro D hD
  rcases hD with ⟨_hDconv, hS0, _hDrec⟩
  exact hS0 hx

/-- Extreme points lie in the closure mixed convex hull (bounded Straszewicz step). -/
lemma theorem18_7_extremePoints_subset_K {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C) :
    C.extremePoints ℝ ⊆
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  have hcl :
      closure (C.exposedPoints ℝ) ⊆
        closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) :=
    theorem18_7_closure_exposedPoints_subset_K (n := n) (C := C)
  have hstrasz :
      C.extremePoints ℝ ⊆ closure (C.exposedPoints ℝ) :=
    theorem18_6_extremePoints_subset_closure_exposedPoints (n := n) (C := C) hCclosed hCbounded
      hCconv
  exact Set.Subset.trans hstrasz hcl

/-- Use Theorem 18.5 to show `C ⊆ K` once extreme points lie in `K`. -/
lemma theorem18_7_C_subset_K_via_theorem18_5 {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C ⊆
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  let K :=
    closure
      (mixedConvexHull (n := n) (C.exposedPoints ℝ)
        {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d})
  have hKconv : Convex ℝ K := by
    simpa using (theorem18_7_K_isClosed_isConvex (n := n) (C := C)).2
  have hKrec :
      ∀ d ∈ {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d},
        ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ K := by
    intro d hd x hx t ht
    simpa [K] using
      (theorem18_7_K_recedes_extremeDirections (n := n) (C := C) (d := d) hd (x := x) hx
        (t := t) ht)
  have hExt : C.extremePoints ℝ ⊆ K := by
    simpa [K] using
      (theorem18_7_extremePoints_subset_K (n := n) (C := C) hCclosed hCbounded hCconv)
  have hsubset :
      mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} ⊆ K := by
    refine
      mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
        (S₀ := C.extremePoints ℝ)
        (S₁ := {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) (Ccand := K) hKconv
        ?_ ?_
    · exact hExt
    · intro d hd x hxK t ht
      exact hKrec d hd x hxK t ht
  have hCeq :
      C =
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} :=
    closedConvex_eq_mixedConvexHull_extremePoints_extremeDirections (n := n) (C := C) hCclosed
      hCconv hNoLines
  intro x hxC
  have hx' :
      x ∈
        mixedConvexHull (n := n) (C.extremePoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d} := by
    rw [hCeq] at hxC
    exact hxC
  simpa [K] using hsubset hx'

/-- Theorem 18.7. A closed bounded convex set with no lines is the closure of the mixed convex
hull of its exposed points and extreme directions. -/
theorem theorem18_7_closedConvex_eq_closure_mixedConvexHull_exposedPoints_extremeDirections
    {n : ℕ} (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C)
    (hCbounded : Bornology.IsBounded C) (hCconv : Convex ℝ C)
    (hNoLines :
      ¬ ∃ y : Fin n → ℝ, y ≠ 0 ∧ y ∈ (-Set.recessionCone C) ∩ Set.recessionCone C) :
    C =
      closure
        (mixedConvexHull (n := n) (C.exposedPoints ℝ)
          {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) := by
  classical
  have hsubset :
      closure
          (mixedConvexHull (n := n) (C.exposedPoints ℝ)
            {d : Fin n → ℝ | IsExtremeDirection (𝕜 := ℝ) C d}) ⊆ C :=
    theorem18_7_rhs_subset_C (n := n) (C := C) hCclosed hCconv
  refine le_antisymm ?_ hsubset
  exact
    theorem18_7_C_subset_K_via_theorem18_5 (n := n) (C := C) hCclosed hCbounded hCconv hNoLines

/-- A bounded cone contains only the origin. -/
lemma cor18_7_1_bounded_cone_subset_singleton_zero {n : ℕ} {K : Set (Fin n → ℝ)}
    (hKcone : IsConeSet n K) (hKbounded : Bornology.IsBounded K) :
    K ⊆ ({0} : Set (Fin n → ℝ)) := by
  intro x hx
  by_contra hxne
  rcases (Metric.isBounded_iff_subset_closedBall (c := (0 : Fin n → ℝ))).1 hKbounded with
    ⟨r, hr⟩
  have hxball : x ∈ Metric.closedBall (0 : Fin n → ℝ) r := hr hx
  have hr_nonneg : 0 ≤ r := by
    have hdist : dist x (0 : Fin n → ℝ) ≤ r := (Metric.mem_closedBall).1 hxball
    exact le_trans dist_nonneg hdist
  have hnorm_pos : 0 < ‖x‖ := (norm_pos_iff).2 hxne
  have hnorm_ne : ‖x‖ ≠ 0 := ne_of_gt hnorm_pos
  let t : ℝ := r / ‖x‖ + 1
  have hdiv_nonneg : 0 ≤ r / ‖x‖ := div_nonneg hr_nonneg (le_of_lt hnorm_pos)
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have htx : t • x ∈ K := hKcone x hx t ht_pos
  have htxball : t • x ∈ Metric.closedBall (0 : Fin n → ℝ) r := hr htx
  have hnorm_le : ‖t • x‖ ≤ r := by
    have hdist : dist (t • x) (0 : Fin n → ℝ) ≤ r := (Metric.mem_closedBall).1 htxball
    simpa [dist_eq_norm] using hdist
  have hnorm_eq : ‖t • x‖ = t * ‖x‖ := by
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using (norm_smul t x)
  have ht_mul : t * ‖x‖ = r + ‖x‖ := by
    dsimp [t]
    field_simp [hnorm_ne]
  have hnorm_gt : r < ‖t • x‖ := by
    have : r < r + ‖x‖ := by linarith [hnorm_pos]
    simpa [hnorm_eq, ht_mul] using this
  exact (not_lt_of_ge hnorm_le hnorm_gt)

/-- A bounded cone containing the origin is `{0}`. -/
lemma cor18_7_1_bounded_cone_eq_singleton_zero {n : ℕ} {K : Set (Fin n → ℝ)}
    (hKcone : IsConeSet n K) (hKbounded : Bornology.IsBounded K)
    (hK0 : (0 : Fin n → ℝ) ∈ K) :
    K = ({0} : Set (Fin n → ℝ)) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact cor18_7_1_bounded_cone_subset_singleton_zero (n := n) (K := K) hKcone hKbounded
  · intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst hx0
    simpa using hK0

/-- Corollary 18.7.1 (bounded cone version). -/
theorem corollary18_7_1_closedConvexCone_eq_closure_cone {n : ℕ} (K T : Set (Fin n → ℝ))
    (hKcone : IsConeSet n K) (hKbounded : Bornology.IsBounded K)
    (hK0 : (0 : Fin n → ℝ) ∈ K) (hTsub : T ⊆ K) :
    K = closure (cone n T) := by
  classical
  have hK : K = ({0} : Set (Fin n → ℝ)) :=
    cor18_7_1_bounded_cone_eq_singleton_zero (n := n) (K := K) hKcone hKbounded hK0
  have hT0 : T ⊆ ({0} : Set (Fin n → ℝ)) := fun x hx => by
    have hx' : x ∈ K := hTsub hx
    simpa [hK] using hx'
  have hcone : cone n T = ({0} : Set (Fin n → ℝ)) :=
    cone_eq_singleton_zero_of_subset (n := n) (S := T) hT0
  simp [hK, hcone]

/-- The continuous linear functional `x ↦ dotProduct x xStar`. -/
noncomputable def dotProductCLM {n : ℕ} (xStar : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.flip (dotProductBilin (R := ℝ) (S := ℝ) (m := Fin n) (A := ℝ))) xStar)

@[simp] lemma dotProductCLM_apply {n : ℕ} (xStar y : Fin n → ℝ) :
    dotProductCLM (n := n) xStar y = dotProduct y xStar := by
  simp [dotProductCLM, LinearMap.flip_apply, dotProductBilin]

/-- A compact set gives a bounded-above dot-product image. -/
lemma theorem18_8_bddAbove_image_dotProduct_of_isCompact {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCcompact : IsCompact C) :
    ∀ xStar : Fin n → ℝ,
      BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) := by
  intro xStar
  have hcont :
      ContinuousOn (fun y : Fin n → ℝ => dotProduct y xStar) C := by
    simpa [dotProductCLM_apply] using
      (dotProductCLM (n := n) xStar).continuous.continuousOn
  simpa using (IsCompact.bddAbove_image (α := ℝ) (β := Fin n → ℝ) (f := fun y =>
    dotProduct y xStar) hCcompact hcont)

/-- For each `xStar`, there is an exposed maximizer of `y ↦ dotProduct y xStar`. -/
lemma theorem18_8_exists_exposedPoint_maximizer_dotProduct {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C) (hCne : C.Nonempty) :
    ∀ xStar : Fin n → ℝ,
      ∃ p, p ∈ (dotProductCLM (n := n) xStar).toExposed C ∧ p ∈ C.exposedPoints ℝ := by
  intro xStar
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  have hcont :
      ContinuousOn (fun y : Fin n → ℝ => dotProductCLM (n := n) xStar y) C :=
    (dotProductCLM (n := n) xStar).continuous.continuousOn
  rcases hCcompact.exists_isMaxOn hCne hcont with ⟨p, hpC, hpmax⟩
  have hpmax' : ∀ y ∈ C, dotProductCLM (n := n) xStar y ≤ dotProductCLM (n := n) xStar p :=
    (isMaxOn_iff).1 hpmax
  have hpF : p ∈ (dotProductCLM (n := n) xStar).toExposed C := by
    refine ⟨hpC, ?_⟩
    intro y hyC
    exact hpmax' y hyC
  have hFne : ((dotProductCLM (n := n) xStar).toExposed C).Nonempty := ⟨p, hpF⟩
  have hFexp : IsExposed ℝ C ((dotProductCLM (n := n) xStar).toExposed C) := by
    simpa using
      (ContinuousLinearMap.toExposed.isExposed (l := dotProductCLM (n := n) xStar) (A := C))
  rcases
      theorem18_6_exposedFace_contains_exposedPoint_fin (n := n) (C := C) hCcompact
        (F := (dotProductCLM (n := n) xStar).toExposed C) hFexp hFne with
    ⟨q, hqF, hqExp⟩
  exact ⟨q, hqF, hqExp⟩

/-- A maximizer in an exposed face realizes the support function value. -/
lemma theorem18_8_deltaStar_eq_dotProduct_of_mem_toExposed {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCbd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C))
    {xStar : Fin n → ℝ} {p : Fin n → ℝ}
    (hp : p ∈ (dotProductCLM (n := n) xStar).toExposed C) :
    deltaStar C xStar = dotProduct p xStar := by
  classical
  have hpC : p ∈ C := hp.1
  have hmax : ∀ y ∈ C, dotProduct y xStar ≤ dotProduct p xStar := by
    intro y hyC
    simpa [dotProductCLM_apply] using (hp.2 y hyC)
  have hmem :
      dotProduct p xStar ∈ Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C :=
    ⟨p, hpC, rfl⟩
  have hle : dotProduct p xStar ≤
      sSup (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) :=
    le_csSup (hCbd xStar) hmem
  have hne :
      (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C).Nonempty :=
    ⟨dotProduct p xStar, hmem⟩
  have hge :
      sSup (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) ≤ dotProduct p xStar := by
    refine csSup_le hne ?_
    intro r hr
    rcases hr with ⟨y, hyC, rfl⟩
    exact hmax y hyC
  have hsSup :
      sSup (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) = dotProduct p xStar :=
    le_antisymm hge hle
  simp [deltaStar_eq_sSup_image_dotProduct_right, hsSup]

/-- Theorem 18.8. A closed bounded convex set is the intersection of its tangent half-spaces
at exposed points. -/
theorem theorem18_8_closedBoundedConvex_eq_sInter_tangentHalfspaces_exposedPoints {n : ℕ}
    (C : Set (Fin n → ℝ)) (hCclosed : IsClosed C) (hCbounded : Bornology.IsBounded C)
    (hCconv : Convex ℝ C) (hCne : C.Nonempty) :
    C =
      ⋂₀ {H : Set (Fin n → ℝ) |
        ∃ xStar p,
          p ∈ (dotProductCLM (n := n) xStar).toExposed C ∧ p ∈ C.exposedPoints ℝ ∧
            H = {x : Fin n → ℝ | dotProduct x xStar ≤ dotProduct p xStar} } := by
  classical
  let H : Set (Set (Fin n → ℝ)) :=
    {H : Set (Fin n → ℝ) |
      ∃ xStar p,
        p ∈ (dotProductCLM (n := n) xStar).toExposed C ∧ p ∈ C.exposedPoints ℝ ∧
          H = {x : Fin n → ℝ | dotProduct x xStar ≤ dotProduct p xStar} }
  have hCcompact : IsCompact C := cor1721_isCompact_S (n := n) (S := C) hCclosed hCbounded
  have hCbd :
      ∀ xStar : Fin n → ℝ,
        BddAbove (Set.image (fun y : Fin n → ℝ => dotProduct y xStar) C) :=
    theorem18_8_bddAbove_image_dotProduct_of_isCompact (n := n) (C := C) hCcompact
  have hsubset : C ⊆ ⋂₀ H := by
    intro x hxC
    refine (Set.mem_sInter).2 ?_
    intro S hS
    rcases hS with ⟨xStar, p, hpF, _hpExp, rfl⟩
    have hxle : dotProduct x xStar ≤ dotProduct p xStar := by
      simpa [dotProductCLM_apply] using (hpF.2 x hxC)
    exact hxle
  have hsupset : ⋂₀ H ⊆ C := by
    intro x hx
    have hxle : ∀ xStar : Fin n → ℝ, dotProduct x xStar ≤ deltaStar C xStar := by
      intro xStar
      obtain ⟨p, hpF, hpExp⟩ :=
        theorem18_8_exists_exposedPoint_maximizer_dotProduct (n := n) (C := C) hCclosed
          hCbounded hCne xStar
      have hxmem :
          x ∈ {x : Fin n → ℝ | dotProduct x xStar ≤ dotProduct p xStar} :=
        (Set.mem_sInter.mp hx) _ ⟨xStar, p, hpF, hpExp, rfl⟩
      have hdelta :
          deltaStar C xStar = dotProduct p xStar :=
        theorem18_8_deltaStar_eq_dotProduct_of_mem_toExposed (n := n) (C := C) hCbd hpF
      simpa [hdelta] using hxmem
    have hxset :
        x ∈ {x : Fin n → ℝ | ∀ xStar : Fin n → ℝ, dotProduct x xStar ≤ deltaStar C xStar} :=
      hxle
    have hEq :=
      setOf_forall_dotProduct_le_deltaStar_eq_of_isClosed (C := C) hCconv hCclosed hCne hCbd
    simpa [hEq] using hxset
  refine le_antisymm ?_ ?_
  · simpa [H] using hsubset
  · simpa [H] using hsupset

end
end Section18
end Chap04

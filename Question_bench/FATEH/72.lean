import Mathlib

open Set

/-- Elements avoiding all maximal ideals that contain `x` form a submonoid. -/
def avoidMaximalsSubmonoid {A : Type*} [CommRing A] (x : A) : Submonoid A :=
  { carrier := {a : A | ∀ m : Ideal A, m.IsMaximal ∧ x ∈ m → a ∉ m}
    one_mem' := by
      intro m hm
      exact (Ideal.ne_top_iff_one (I := m)).1 (Ideal.IsMaximal.ne_top hm.1)
    mul_mem' := by
      intro a b ha hb m hm hmem
      exact (hm.1.isPrime.mem_or_mem hmem).elim (ha m hm) (hb m hm) }

/-- A maximal ideal disjoint from a multiplicative set remains maximal after localization. -/
lemma isMaximal_map_of_isMaximal_disjoint {A : Type*} [CommRing A] (S : Submonoid A)
    {m : Ideal A} (hm : m.IsMaximal) (hdisj : Disjoint (S : Set A) m) :
    (Ideal.map (algebraMap A (Localization S)) m).IsMaximal := by
  classical
  have hne_top :
      Ideal.map (algebraMap A (Localization S)) m ≠ ⊤ := by
    exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint (M := S)
      (S := Localization S) m).2 hdisj
  refine (Ideal.isMaximal_def).2 ?_
  refine ⟨hne_top, ?_⟩
  intro J hJ
  by_contra hJne
  have hle : m ≤ Ideal.comap (algebraMap A (Localization S)) J := by
    exact (Ideal.map_le_iff_le_comap).1 hJ.1
  have hcomap_ne : Ideal.comap (algebraMap A (Localization S)) J ≠ ⊤ := by
    intro htop
    have hcomap_one :
        (1 : A) ∈ Ideal.comap (algebraMap A (Localization S)) J := by
      simp [htop]
    have hJone : (1 : Localization S) ∈ J := by
      simpa [Ideal.mem_comap] using hcomap_one
    exact hJne ((Ideal.eq_top_iff_one (I := J)).2 hJone)
  have hcomap_eq : Ideal.comap (algebraMap A (Localization S)) J = m :=
    (hm.eq_of_le hcomap_ne hle).symm
  have hmap_comap :
      Ideal.map (algebraMap A (Localization S))
        (Ideal.comap (algebraMap A (Localization S)) J) = J :=
    IsLocalization.map_comap (M := S) (S := Localization S) J
  have hJeq : J = Ideal.map (algebraMap A (Localization S)) m := by
    simpa [hcomap_eq] using hmap_comap.symm
  exact hJ.ne' hJeq

/-- Prime avoidance for a finite family of maximal ideals. -/
lemma prime_le_some_maximal_in_M {A : Type*} [CommRing A] {M : Set (Ideal A)}
    (hM : M.Finite) (hMmax : ∀ m ∈ M, m.IsMaximal) {P : Ideal A}
    (hPM : ((P : Set A) ⊆ ⋃ m ∈ M, (m : Set A))) :
    ∃ m ∈ M, P ≤ m := by
  classical
  have hprime :
      ∀ m ∈ M, m ≠ (⊥ : Ideal A) → m ≠ (⊥ : Ideal A) → (m : Ideal A).IsPrime := by
    intro m hm _ _
    exact (hMmax m hm).isPrime
  exact (Ideal.subset_union_prime_finite (s := M) hM (f := fun m => (m : Ideal A))
    (a := (⊥ : Ideal A)) (b := (⊥ : Ideal A)) hprime (I := P)).1 hPM

-- Maximal ideals of the localization away from `x` come from maximal ideals containing `x`.
lemma maximal_of_localization_comap_in_M {A : Type*} [CommRing A] {x : A}
    (hM : Set.Finite {m : Ideal A | m.IsMaximal ∧ x ∈ m})
    (P : MaximalSpectrum (Localization (avoidMaximalsSubmonoid (A := A) x))) :
    ∃ m : Ideal A, m.IsMaximal ∧ x ∈ m ∧
      Ideal.map
          (algebraMap A (Localization (avoidMaximalsSubmonoid (A := A) x))) m =
        P.asIdeal := by
  classical
  let S : Submonoid A := avoidMaximalsSubmonoid (A := A) x
  let M : Set (Ideal A) := {m : Ideal A | m.IsMaximal ∧ x ∈ m}
  have hMmax : ∀ m ∈ M, m.IsMaximal := by
    intro m hm
    exact hm.1
  let p : Ideal A := Ideal.comap (algebraMap A (Localization S)) P.asIdeal
  have hprime_disj :
      p.IsPrime ∧ Disjoint (S : Set A) p := by
    have hprime : P.asIdeal.IsPrime := P.isMaximal.isPrime
    simpa [p] using
      (IsLocalization.isPrime_iff_isPrime_disjoint (M := S) (S := Localization S)
        P.asIdeal).1 hprime
  have hsubset : ((p : Set A) ⊆ ⋃ m ∈ M, (m : Set A)) := by
    intro a ha
    have ha_notS : a ∉ (S : Set A) := by
      intro haS
      exact (Set.disjoint_left.1 hprime_disj.2) haS ha
    classical
    rcases (by
      classical
      simpa [S, M, avoidMaximalsSubmonoid] using ha_notS) with ⟨m, hmmax, hxmem, hamem⟩
    refine Set.mem_iUnion.2 ⟨m, ?_⟩
    refine Set.mem_iUnion.2 ?_
    exact ⟨⟨hmmax, hxmem⟩, hamem⟩
  obtain ⟨m, hmM, hpm⟩ := prime_le_some_maximal_in_M (A := A) (M := M) hM hMmax hsubset
  have hmmax : m.IsMaximal := hmM.1
  have hxmem : x ∈ m := hmM.2
  have hdisj : Disjoint (S : Set A) m := by
    refine Set.disjoint_left.2 ?_
    intro a haS hamem
    have haS' : ∀ m' : Ideal A, m'.IsMaximal ∧ x ∈ m' → a ∉ m' := by
      simpa [S, avoidMaximalsSubmonoid] using haS
    exact (haS' m ⟨hmmax, hxmem⟩) hamem
  have hmaple :
      P.asIdeal ≤ Ideal.map (algebraMap A (Localization S)) m := by
    have hmap_comap :
        Ideal.map (algebraMap A (Localization S))
          (Ideal.comap (algebraMap A (Localization S)) P.asIdeal) = P.asIdeal :=
      IsLocalization.map_comap (M := S) (S := Localization S) P.asIdeal
    have hmaple' :
        Ideal.map (algebraMap A (Localization S)) p ≤
          Ideal.map (algebraMap A (Localization S)) m :=
      Ideal.map_mono hpm
    simpa [p, hmap_comap] using hmaple'
  have hmap_ne :
      Ideal.map (algebraMap A (Localization S)) m ≠ ⊤ := by
    exact (Ideal.IsMaximal.ne_top (isMaximal_map_of_isMaximal_disjoint (S := S) hmmax hdisj))
  have hEq :
      Ideal.map (algebraMap A (Localization S)) m = P.asIdeal :=
    (P.isMaximal.eq_of_le hmap_ne hmaple).symm
  exact ⟨m, hmmax, hxmem, hEq⟩

/-- Finite maximal spectrum after localizing away from a finite set of maximal ideals. -/
lemma finite_maximalSpectrum_localization_of_finite_maximals_containing {A : Type*} [CommRing A]
    {x : A} (_hx : x ≠ 0)
    (hM : Set.Finite {m : Ideal A | m.IsMaximal ∧ x ∈ m}) :
    Finite (MaximalSpectrum (Localization (avoidMaximalsSubmonoid (A := A) x))) := by
  classical
  let S : Submonoid A := avoidMaximalsSubmonoid (A := A) x
  let M : Set (Ideal A) := {m : Ideal A | m.IsMaximal ∧ x ∈ m}
  have hM' : M.Finite := hM
  let _ : Fintype {m : Ideal A // m ∈ M} := hM'.fintype
  refine Finite.of_surjective (fun m : {m : Ideal A // m ∈ M} => ?_) ?_
  · refine ⟨Ideal.map (algebraMap A (Localization S)) m.1, ?_⟩
    have hmmax : m.1.IsMaximal := m.2.1
    have hxmem : x ∈ m.1 := m.2.2
    have hdisj : Disjoint (S : Set A) m.1 := by
      refine Set.disjoint_left.2 ?_
      intro a haS hamem
      have haS' :
          ∀ m' : Ideal A, m'.IsMaximal ∧ x ∈ m' → a ∉ m' := by
        simpa [S, avoidMaximalsSubmonoid] using haS
      exact (haS' m.1 ⟨hmmax, hxmem⟩) hamem
    exact isMaximal_map_of_isMaximal_disjoint (S := S) hmmax hdisj
  · intro P
    rcases maximal_of_localization_comap_in_M (A := A) (x := x) hM P with
      ⟨m, hmmax, hxmem, hmap⟩
    refine ⟨⟨m, ?_⟩, ?_⟩
    · exact ⟨hmmax, hxmem⟩
    · refine MaximalSpectrum.ext ?_
      simpa [S] using hmap

/-- The localization away from finitely many maximal ideals is Noetherian. -/
lemma noetherian_localization_compl {A : Type*} [CommRing A] {x : A} (hx : x ≠ 0)
    (h_local : ∀ (m : Ideal A), [m.IsMaximal] → IsNoetherianRing (Localization.AtPrime m))
    (hM : Set.Finite {m : Ideal A | m.IsMaximal ∧ x ∈ m}) :
    IsNoetherianRing (Localization (avoidMaximalsSubmonoid (A := A) x)) := by
  classical
  let S : Submonoid A := avoidMaximalsSubmonoid (A := A) x
  have hfinite :
      Finite (MaximalSpectrum (Localization S)) :=
    finite_maximalSpectrum_localization_of_finite_maximals_containing (A := A) hx hM
  let _ : Finite (MaximalSpectrum (Localization S)) := hfinite
  refine IsNoetherianRing.of_isLocalization_maximal (Rₚ := fun P => Localization.AtPrime P) ?_
  intro P hP
  let P' : MaximalSpectrum (Localization S) := ⟨P, hP⟩
  rcases maximal_of_localization_comap_in_M (A := A) (x := x) hM P' with
    ⟨m, hmmax, hxmem, hmap⟩
  have hdisj : Disjoint (S : Set A) m := by
    refine Set.disjoint_left.2 ?_
    intro a haS hamem
    have haS' :
        ∀ m' : Ideal A, m'.IsMaximal ∧ x ∈ m' → a ∉ m' := by
      simpa [S, avoidMaximalsSubmonoid] using haS
    exact (haS' m ⟨hmmax, hxmem⟩) hamem
  have hcomap' :
      Ideal.comap (algebraMap A (Localization S)) P'.asIdeal = m := by
    have hmprime : m.IsPrime := hmmax.isPrime
    simpa [S, hmap] using
      (IsLocalization.comap_map_of_isPrime_disjoint (M := S) (S := Localization S)
        m hmprime hdisj)
  have hcomap :
      Ideal.comap (algebraMap A (Localization S)) P = m := by
    simpa [P'] using hcomap'
  have _ : m.IsMaximal := hmmax
  have hNoeth_m : IsNoetherianRing (Localization.AtPrime m) := h_local m
  have hEquiv :
      Localization.AtPrime m ≃+* Localization.AtPrime P := by
    cases hcomap
    simpa using
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (M := S) (p := P)).toRingEquiv
  exact isNoetherianRing_of_ringEquiv (Localization.AtPrime m) hEquiv

/-- Equality after localizing at `S` descends to the localization at a maximal ideal disjoint from
`S`. -/
lemma Ideal.map_eq_atPrime_of_eq_map_localization {A : Type*} [CommRing A] {S : Submonoid A}
    {m : Ideal A} (hm : m.IsMaximal) (hdisj : Disjoint (S : Set A) m)
    {I J : Ideal A}
    (hIJ : Ideal.map (algebraMap A (Localization S)) I =
      Ideal.map (algebraMap A (Localization S)) J) :
    Ideal.map (algebraMap A (Localization.AtPrime m)) I =
      Ideal.map (algebraMap A (Localization.AtPrime m)) J := by
  classical
  have hSm : S ≤ m.primeCompl := by
    intro s hs
    change (s : A) ∉ m
    exact (Set.disjoint_left.1 hdisj) hs
  let g : Localization S →+* Localization.AtPrime m :=
    IsLocalization.map (M := S) (T := m.primeCompl) (Q := Localization.AtPrime m)
      (g := RingHom.id A) hSm
  have hcomp :
      g.comp (algebraMap A (Localization S)) = algebraMap A (Localization.AtPrime m) := by
    ext x
    simp [g]
  have hmapI :
      Ideal.map g (Ideal.map (algebraMap A (Localization S)) I) =
        Ideal.map (algebraMap A (Localization.AtPrime m)) I := by
    simpa [hcomp] using
      (Ideal.map_map (I := I) (f := algebraMap A (Localization S)) (g := g))
  have hmapJ :
      Ideal.map g (Ideal.map (algebraMap A (Localization S)) J) =
        Ideal.map (algebraMap A (Localization.AtPrime m)) J := by
    simpa [hcomp] using
      (Ideal.map_map (I := J) (f := algebraMap A (Localization S)) (g := g))
  have hIJ' :
      Ideal.map g (Ideal.map (algebraMap A (Localization S)) I) =
        Ideal.map g (Ideal.map (algebraMap A (Localization S)) J) := by
    simpa using congrArg (fun K => Ideal.map g K) hIJ
  calc
    Ideal.map (algebraMap A (Localization.AtPrime m)) I =
        Ideal.map g (Ideal.map (algebraMap A (Localization S)) I) := hmapI.symm
    _ = Ideal.map g (Ideal.map (algebraMap A (Localization S)) J) := hIJ'
    _ = Ideal.map (algebraMap A (Localization.AtPrime m)) J := hmapJ

/-- If `x ∉ m`, then any ideal containing `x` becomes `⊤` after localizing at `m`. -/
lemma Ideal.map_eq_top_of_not_mem_maximal {A : Type*} [CommRing A] {m : Ideal A}
    (hm : m.IsMaximal) {I : Ideal A} {x : A} (hxI : x ∈ I) (hx : x ∉ m) :
    Ideal.map (algebraMap A (Localization.AtPrime m)) I = ⊤ := by
  classical
  have _ : m.IsPrime := hm.isPrime
  have hxunit : IsUnit (algebraMap A (Localization.AtPrime m) x) := by
    have hx' : x ∈ m.primeCompl := by
      simpa [Ideal.primeCompl] using hx
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (S := Localization.AtPrime m) (I := m) x).2 hx'
  have hxmem :
      algebraMap A (Localization.AtPrime m) x ∈
        Ideal.map (algebraMap A (Localization.AtPrime m)) I :=
    Ideal.mem_map_of_mem _ hxI
  exact Ideal.eq_top_of_isUnit_mem (I := Ideal.map (algebraMap A (Localization.AtPrime m)) I)
    (x := algebraMap A (Localization.AtPrime m) x) hxmem hxunit

/-- Descend finite generation from the localization away from maximal ideals containing `x`. -/
lemma Ideal.fg_of_map_of_isPrime_disjoint {A : Type*} [CommRing A] {x : A}
    (P : Ideal A) (_hP : P.IsPrime) (hxP : x ∈ P)
    (hfg :
      (Ideal.map (algebraMap A (Localization (avoidMaximalsSubmonoid (A := A) x))) P).FG) :
    P.FG := by
  classical
  let S : Submonoid A := avoidMaximalsSubmonoid (A := A) x
  have hfg' :
      (Submodule.span (Localization S)
          ((algebraMap A (Localization S)) '' (P : Set A))).FG := by
    simpa [Ideal.map, S] using hfg
  obtain ⟨s, hs_sub, hspan⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset
      (s := (algebraMap A (Localization S)) '' (P : Set A))).1 hfg'
  have hs' : ∀ y : {y // y ∈ s}, ∃ a : A, a ∈ P ∧
      algebraMap A (Localization S) a = y := by
    intro y
    have hy :
        (y : Localization S) ∈ (algebraMap A (Localization S)) '' (P : Set A) :=
      hs_sub y.property
    rcases hy with ⟨a, haP, haeq⟩
    exact ⟨a, haP, haeq⟩
  classical
  choose g hgP hgeq using hs'
  let t : Finset A := s.attach.image g
  have htP : (t : Set A) ⊆ P := by
    intro a ha
    rcases Finset.mem_image.1 ha with ⟨y, hy, rfl⟩
    exact hgP y
  let J : Ideal A := Ideal.span ((t : Set A) ∪ {x})
  have hxJ : x ∈ J := by
    refine Ideal.subset_span ?_
    simp
  have hs_t :
      (s : Set (Localization S)) ⊆
        (algebraMap A (Localization S)) '' (t : Set A) := by
    intro y hy
    refine ⟨g ⟨y, hy⟩, ?_, ?_⟩
    · have : g ⟨y, hy⟩ ∈ t := by
        apply Finset.mem_image.2
        refine ⟨⟨y, hy⟩, ?_, rfl⟩
        simp
      simpa using this
    · simpa using (hgeq ⟨y, hy⟩)
  have hmapP_eq :
      Ideal.map (algebraMap A (Localization S)) P =
        Ideal.span (s : Set (Localization S)) := by
    simpa [Ideal.map, S] using hspan
  have hmapJ_le' :
      Ideal.span ((algebraMap A (Localization S)) '' ((t : Set A) ∪ {x})) ≤
        Ideal.map (algebraMap A (Localization S)) P := by
    refine Ideal.span_le.2 ?_
    intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    rcases ha with ha | ha
    · exact Ideal.mem_map_of_mem _ (htP ha)
    · have hax : a = x := by simpa using ha
      subst hax
      exact Ideal.mem_map_of_mem _ hxP
  have hmapJ_le :
      Ideal.map (algebraMap A (Localization S)) J ≤
        Ideal.map (algebraMap A (Localization S)) P := by
    simpa [J, Ideal.map_span] using hmapJ_le'
  have hs_t' :
      (s : Set (Localization S)) ⊆
        (algebraMap A (Localization S)) '' ((t : Set A) ∪ {x}) := by
    intro y hy
    rcases hs_t hy with ⟨a, ha, rfl⟩
    exact ⟨a, Or.inl ha, rfl⟩
  have hmapP_le' :
      Ideal.span (s : Set (Localization S)) ≤
        Ideal.span ((algebraMap A (Localization S)) '' ((t : Set A) ∪ {x})) := by
    refine Ideal.span_le.2 ?_
    intro y hy
    exact Ideal.subset_span (hs_t' hy)
  have hmapP_le :
      Ideal.map (algebraMap A (Localization S)) P ≤
        Ideal.map (algebraMap A (Localization S)) J := by
    calc
      Ideal.map (algebraMap A (Localization S)) P =
          Ideal.span (s : Set (Localization S)) := hmapP_eq
      _ ≤ Ideal.span ((algebraMap A (Localization S)) '' ((t : Set A) ∪ {x})) := hmapP_le'
      _ = Ideal.map (algebraMap A (Localization S)) J := by
        simp [J, Ideal.map_span]
  have hmap :
      Ideal.map (algebraMap A (Localization S)) J =
        Ideal.map (algebraMap A (Localization S)) P :=
    le_antisymm hmapJ_le hmapP_le
  have hJP : J = P := by
    refine Ideal.eq_of_localization_maximal ?_
    intro m hm
    by_cases hxmem : x ∈ m
    · have hdisj : Disjoint (S : Set A) m := by
        refine Set.disjoint_left.2 ?_
        intro a haS hamem
        have haS' :
            ∀ m' : Ideal A, m'.IsMaximal ∧ x ∈ m' → a ∉ m' := by
          simpa [S, avoidMaximalsSubmonoid] using haS
        exact (haS' m ⟨hm, hxmem⟩) hamem
      exact
        Ideal.map_eq_atPrime_of_eq_map_localization (S := S) hm hdisj hmap
    · have hJtop :
        Ideal.map (algebraMap A (Localization.AtPrime m)) J = ⊤ :=
        Ideal.map_eq_top_of_not_mem_maximal hm hxJ hxmem
      have hPtop :
        Ideal.map (algebraMap A (Localization.AtPrime m)) P = ⊤ :=
        Ideal.map_eq_top_of_not_mem_maximal hm hxP hxmem
      simp [hJtop, hPtop]
  refine ⟨insert x t, ?_⟩
  simpa [J, Finset.coe_insert, Set.union_comm, Set.union_left_comm, Set.union_assoc] using hJP

/-- Let $A$ be a ring such that for each maximal ideal $\mathfrak{m}$ of $A$, the local ring
$A_{\mathfrak{m}}$ is Noetherian; and for each $x \neq 0$ in $A$, the set of maximal ideals of $A$
which contain $x$ is finite. Show that $A$ is Noetherian. -/
theorem isNoetherianRing_of_finite_isMaximal_and_mem {A : Type} [CommRing A]
    (h_local : ∀ (m : Ideal A), [m.IsMaximal] → IsNoetherianRing (Localization.AtPrime m))
    (h_finite : ∀ x : A, x ≠ 0 → Set.Finite {m : Ideal A | m.IsMaximal ∧ x ∈ m}) :
    IsNoetherianRing A := by
  classical
  -- Use the prime-ideal criterion for Noetherianity.
  refine IsNoetherianRing.of_prime_ne_bot ?_
  intro P hP hPne
  -- Choose a nonzero element of `P` and localize away from the maximal ideals containing it.
  obtain ⟨x, hxP, hx0⟩ := P.ne_bot_iff.mp hPne
  have hM : Set.Finite {m : Ideal A | m.IsMaximal ∧ x ∈ m} := h_finite x hx0
  let S : Submonoid A := avoidMaximalsSubmonoid (A := A) x
  -- The localization at `S` is Noetherian.
  have hloc : IsNoetherianRing (Localization S) :=
    noetherian_localization_compl (A := A) hx0 h_local hM
  -- Hence the extended ideal is finitely generated, and we descend along disjointness.
  have hmap_fg : (Ideal.map (algebraMap A (Localization S)) P).FG := by
    exact (IsNoetherian.noetherian (R := Localization S) (Ideal.map (algebraMap A _) P))
  -- Clear denominators using the maximal-avoidance localization.
  simpa [S] using (Ideal.fg_of_map_of_isPrime_disjoint (x := x) P hP hxP hmap_fg)

import Mathlib

open scoped IntermediateField
open scoped Topology

/-- Coercion of an absolute Galois element to an `AlgHom`. -/
abbrev FATEX28.absGal_toAlgHom (K : Type*) [Field K] (g : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K →ₐ[K] AlgebraicClosure K :=
  (show AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K from g).toAlgHom

/-- Coercion of a fixing subgroup to a set in the absolute Galois group. -/
abbrev FATEX28.fixingSubgroupSet (K : Type*) [Field K]
    (E : IntermediateField K (AlgebraicClosure K)) : Set (Field.absoluteGaloisGroup K) :=
  (show Subgroup (Field.absoluteGaloisGroup K) from E.fixingSubgroup)

/-- The absolute Galois group of a number field is Hausdorff. -/
noncomputable instance FATEX28.t2Space_absoluteGaloisGroup (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] :
    T2Space (Field.absoluteGaloisGroup K) := by
  simpa [Field.absoluteGaloisGroup] using
    (krullTopology_t2 (K := K) (L := AlgebraicClosure K))

/- 
Let $K/\mathbb{Q}$ be a finite extension.
Let $g$ be a nontrivial element of the absolute Galois group $G(K)$ of $K$.
Show that $g$ admits an infinite number of conjugates.
-/
/-- The conjugacy class of `g` is the orbit of the conjugation action. -/
lemma FATEX28.conjSet_eq_orbit_conjAct {G : Type*} [Group G] (g : G) :
    ({g' : G | IsConj g g'} : Set G) = MulAction.orbit (ConjAct G) g := by
  ext g'
  constructor
  · intro hg
    exact (ConjAct.mem_orbit_conjAct (g := g') (h := g)).2 (IsConj.symm hg)
  · intro hg
    exact IsConj.symm ((ConjAct.mem_orbit_conjAct (g := g') (h := g)).1 hg)

/-- If the stabilizer has infinite index, the orbit is infinite. -/
lemma FATEX28.orbit_infinite_of_not_finiteIndex {G : Type*} [Group G]
    {X : Type*} [MulAction G X] (x : X)
    (h : ¬ (MulAction.stabilizer G x).FiniteIndex) :
    (MulAction.orbit G x).Infinite := by
  classical
  by_contra hinf
  have hfinite : (MulAction.orbit G x).Finite := by
    rcases (MulAction.orbit G x).finite_or_infinite with hfinite | hinf'
    · exact hfinite
    · exact (hinf hinf').elim
  have hmem : x ∈ MulAction.orbit G x := MulAction.mem_orbit_self x
  have hncard_ne : (MulAction.orbit G x).ncard ≠ 0 :=
    Set.ncard_ne_zero_of_mem hmem hfinite
  have hindex_ne : (MulAction.stabilizer G x).index ≠ 0 := by
    simpa [MulAction.index_stabilizer (G := G) (x := x)] using hncard_ne
  have hindex : (MulAction.stabilizer G x).FiniteIndex :=
    (Subgroup.finiteIndex_iff).2 hindex_ne
  exact h hindex

/-- A centralizer of infinite index yields an infinite conjugacy orbit. -/
lemma FATEX28.orbit_infinite_of_centralizer_not_finiteIndex {G : Type*} [Group G] (g : G)
    (h : ¬ (Subgroup.centralizer ({g} : Set G)).FiniteIndex) :
    (MulAction.orbit (ConjAct G) g).Infinite := by
  have h' : ¬ (MulAction.stabilizer (ConjAct G) g).FiniteIndex := by
    intro hfin
    have hfin' : (Subgroup.centralizer ({g} : Set G)).FiniteIndex := by
      simpa [ConjAct.stabilizer_eq_centralizer (g := g)] using hfin
    exact h hfin'
  exact FATEX28.orbit_infinite_of_not_finiteIndex (G := ConjAct G) (x := g) h'

/-- The centralizer of a singleton in a Hausdorff topological group is closed. -/
lemma FATEX28.isClosed_centralizer_singleton {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed (Subgroup.centralizer ({g} : Set G) : Set G) := by
  simpa using (Set.isClosed_centralizer ({g} : Set G))

/-- A nontrivial automorphism moves an element of a finite intermediate field. -/
lemma FATEX28.exists_finite_intermediateField_not_fixed (K : Type*) [Field K]
    (g : Field.absoluteGaloisGroup K) (h : g ≠ 1) :
    ∃ E : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K E ∧ ∃ x ∈ E, (FATEX28.absGal_toAlgHom (K := K) g) x ≠ x := by
  classical
  let g' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := g
  have h' : g' ≠ 1 := by
    simpa [g'] using h
  obtain ⟨x, hx⟩ := DFunLike.exists_ne h'
  let E : IntermediateField K (AlgebraicClosure K) := K⟮x⟯
  have hfin : FiniteDimensional K E := by
    simpa [E] using
      (IntermediateField.adjoin.finiteDimensional (K := K) (x := x)
        (Algebra.IsIntegral.isIntegral x))
  have hxE : x ∈ E := by
    simpa [E] using (IntermediateField.mem_adjoin_simple_self K x)
  refine ⟨E, hfin, x, hxE, ?_⟩
  simpa [FATEX28.absGal_toAlgHom, g'] using hx

/-- The fixed field of an open centralizer is finite-dimensional. -/
lemma FATEX28.finiteDimensional_fixedField_of_isOpen_centralizer (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K)
    (hopen :
      IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K))) :
    FiniteDimensional K
      (IntermediateField.fixedField
        ((⟨Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)),
            FATEX28.isClosed_centralizer_singleton (G := Field.absoluteGaloisGroup K) g⟩ :
            ClosedSubgroup (Gal(AlgebraicClosure K/K))) :
          Subgroup (Gal(AlgebraicClosure K/K)))) := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : IsGalois K (AlgebraicClosure K) := by infer_instance
  let Hc :
      ClosedSubgroup (Gal(AlgebraicClosure K/K)) :=
    ⟨Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)),
      FATEX28.isClosed_centralizer_singleton (G := Field.absoluteGaloisGroup K) g⟩
  have hfix :
      (IntermediateField.fixedField Hc).fixingSubgroup = Hc.1 := by
    simpa using
      (InfiniteGalois.fixingSubgroup_fixedField (k := K) (K := AlgebraicClosure K) Hc)
  have hopen' :
      IsOpen (FATEX28.fixingSubgroupSet (K := K) (IntermediateField.fixedField Hc)) := by
    dsimp [FATEX28.fixingSubgroupSet]
    simpa [Hc, hfix] using hopen
  simpa [Hc] using
    (InfiniteGalois.isOpen_iff_finite (k := K) (K := AlgebraicClosure K)
      (L := IntermediateField.fixedField Hc)).1 hopen'

/-- An open centralizer is a neighborhood of `1`. -/
lemma FATEX28.centralizer_mem_nhds_one_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (g : G)
    (hopen : IsOpen (Subgroup.centralizer ({g} : Set G) : Set G)) :
    (Subgroup.centralizer ({g} : Set G) : Set G) ∈ 𝓝 (1 : G) := by
  have hmem :
      (1 : G) ∈ (Subgroup.centralizer ({g} : Set G) : Set G) := by
    simpa using (Subgroup.one_mem (Subgroup.centralizer ({g} : Set G)))
  exact IsOpen.mem_nhds hopen hmem

/-- An open centralizer contains a fixing subgroup of a finite intermediate field. -/
lemma FATEX28.exists_finite_intermediateField_fixingSubgroup_le_centralizer_of_isOpen (K : Type)
    [Field K] (g : Field.absoluteGaloisGroup K)
    (hopen :
      IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K))) :
    ∃ E : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K E ∧
        FATEX28.fixingSubgroupSet (K := K) E ⊆
          (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
            (Field.absoluteGaloisGroup K)) := by
  have hmem :
      (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
        (Field.absoluteGaloisGroup K)) ∈ 𝓝 (1 : Field.absoluteGaloisGroup K) :=
    FATEX28.centralizer_mem_nhds_one_of_isOpen (G := Field.absoluteGaloisGroup K) g hopen
  simpa using
    (krullTopology_mem_nhds_one_iff (K := K) (L := AlgebraicClosure K)
      (s := (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
        (Field.absoluteGaloisGroup K)))).1 hmem

/-- If `g` does not normalize `H`, then some element of `H` fails to commute with `g`. -/
lemma FATEX28.exists_noncommuting_of_not_mem_normalizer {G : Type*} [Group G]
    (H : Subgroup G) (g : G) (hg : g ∉ H.normalizer) :
    ∃ σ ∈ (H : Set G), σ * g ≠ g * σ := by
  classical
  have hnot : ¬ ∀ h, h ∈ H ↔ g * h * g⁻¹ ∈ H := by
    intro hall
    exact hg ((Subgroup.mem_normalizer_iff).2 hall)
  obtain ⟨σ, hσ⟩ := not_forall.mp hnot
  by_cases hσH : σ ∈ H
  · have hσnot : g * σ * g⁻¹ ∉ H := by
      intro hconj
      have hiff : σ ∈ H ↔ g * σ * g⁻¹ ∈ H := by
        constructor
        · intro _
          exact hconj
        · intro _
          exact hσH
      exact hσ hiff
    refine ⟨σ, hσH, ?_⟩
    intro hcomm
    have hconj : g * σ * g⁻¹ = σ := by
      have h' := congrArg (fun t => t * g⁻¹) hcomm
      have h'' : σ = g * σ * g⁻¹ := by
        simpa [mul_assoc] using h'
      exact h''.symm
    have hmem : g * σ * g⁻¹ ∈ H := by
      simpa [hconj] using hσH
    exact hσnot hmem
  · have hσin : g * σ * g⁻¹ ∈ H := by
      by_contra hconj
      have hiff : σ ∈ H ↔ g * σ * g⁻¹ ∈ H := by
        constructor
        · intro h
          exact (hσH h).elim
        · intro h
          exact (hconj h).elim
      exact hσ hiff
    refine ⟨g * σ * g⁻¹, hσin, ?_⟩
    intro hcomm
    have h' := congrArg (fun t => g⁻¹ * t) hcomm
    have h'' : g⁻¹ * (g * σ * g⁻¹) * g = g * σ * g⁻¹ := by
      simpa [mul_assoc] using h'
    have hσeq : σ = g * σ * g⁻¹ := by
      calc
        σ = g⁻¹ * (g * σ * g⁻¹) * g := by
          simp [mul_assoc]
        _ = g * σ * g⁻¹ := h''
    have hσmem : σ ∈ H := by
      simpa [hσeq.symm] using hσin
    exact hσH hσmem

open scoped Pointwise

/-- If `E.map g ≠ E`, then some element of `E.fixingSubgroup` fails to commute with `g`. -/
lemma FATEX28.exists_noncommuting_in_fixingSubgroup_of_map_ne (K : Type) [Field K]
    [Algebra ℚ K] [Module.Finite ℚ K]
    (g : Field.absoluteGaloisGroup K) (E : IntermediateField K (AlgebraicClosure K))
    (hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) ≠ E) :
    ∃ σ ∈ FATEX28.fixingSubgroupSet (K := K) E, σ * g ≠ g * σ := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : IsGalois K (AlgebraicClosure K) := by infer_instance
  let g' : Gal(AlgebraicClosure K/K) := g
  have hnot : g' ∉ (E.fixingSubgroup).normalizer := by
    intro hnorm
    have hconj : (MulAut.conj g') • E.fixingSubgroup = E.fixingSubgroup := by
      ext σ
      have hmem := (Subgroup.mem_normalizer_iff'').1 hnorm σ
      have hsmul :
          σ ∈ (MulAut.conj g') • E.fixingSubgroup ↔ g'⁻¹ * σ * g' ∈ E.fixingSubgroup := by
        simpa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.conj_symm_apply, mul_assoc]
      exact hsmul.trans hmem.symm
    have hfix : (E.map (FATEX28.absGal_toAlgHom (K := K) g)).fixingSubgroup = E.fixingSubgroup := by
      calc
        (E.map (FATEX28.absGal_toAlgHom (K := K) g)).fixingSubgroup =
            (MulAut.conj g') • E.fixingSubgroup := by
              simpa [FATEX28.absGal_toAlgHom, g'] using
                (IsGalois.map_fixingSubgroup (K := K) (L := AlgebraicClosure K) (E := E) g')
        _ = E.fixingSubgroup := hconj
    have hE : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E := by
      have hfixed :
          IntermediateField.fixedField (E.map (FATEX28.absGal_toAlgHom (K := K) g)).fixingSubgroup =
            E.map (FATEX28.absGal_toAlgHom (K := K) g) :=
        (InfiniteGalois.fixedField_fixingSubgroup (k := K) (K := AlgebraicClosure K)
          (L := E.map (FATEX28.absGal_toAlgHom (K := K) g)))
      calc
        E.map (FATEX28.absGal_toAlgHom (K := K) g) =
            IntermediateField.fixedField (E.map (FATEX28.absGal_toAlgHom (K := K) g)).fixingSubgroup := by
              exact hfixed.symm
        _ = IntermediateField.fixedField E.fixingSubgroup := by
              rw [hfix]
        _ = E := by
              simpa using
                (InfiniteGalois.fixedField_fixingSubgroup (k := K) (K := AlgebraicClosure K)
                  (L := E))
    exact hmap hE
  obtain ⟨σ, hσ, hcomm⟩ :=
    FATEX28.exists_noncommuting_of_not_mem_normalizer (H := E.fixingSubgroup) g' hnot
  refine ⟨σ, ?_, ?_⟩
  ·
    dsimp [FATEX28.fixingSubgroupSet]
    exact hσ
  · simpa [g'] using hcomm

/-- Arithmetic input in the stable case: produce a noncommuting element in the fixing subgroup. -/
lemma FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case_arithmetic (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : FiniteDimensional K E)
    (hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E) :
    ∃ σ ∈ FATEX28.fixingSubgroupSet (K := K) E, σ * g ≠ g * σ := by
  sorry

/-- Arithmetic input: a nontrivial element has non-open centralizer (auxiliary form). -/
lemma FATEX28.centralizer_not_open_of_ne_one_aux (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1) :
    ¬ IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) := by
  intro hopen
  obtain ⟨E, hfin, hsub⟩ :=
    FATEX28.exists_finite_intermediateField_fixingSubgroup_le_centralizer_of_isOpen
      (K := K) g hopen
  have hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E := by
    by_contra hmap
    obtain ⟨σ, hσ, hcomm⟩ :=
      FATEX28.exists_noncommuting_in_fixingSubgroup_of_map_ne (K := K) g E hmap
    have hσ' :
        σ ∈ (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) :=
      hsub hσ
    have hcomm' : σ * g = g * σ :=
      (Subgroup.mem_centralizer_singleton_iff.mp hσ')
    exact hcomm hcomm'
  obtain ⟨σ, hσ, hcomm⟩ :=
    FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case_arithmetic
      (K := K) g h E hfin hmap
  have hσ' :
      σ ∈ (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
        (Field.absoluteGaloisGroup K)) :=
    hsub hσ
  have hcomm' : σ * g = g * σ :=
    (Subgroup.mem_centralizer_singleton_iff.mp hσ')
  exact hcomm hcomm'

/-- Stable-case arithmetic input when `g` preserves `E`. -/
lemma FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case (K : Type) [Field K]
    [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : FiniteDimensional K E)
    (hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E) :
    ∃ σ ∈ FATEX28.fixingSubgroupSet (K := K) E, σ * g ≠ g * σ := by
  simpa using
    FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case_arithmetic
      (K := K) g h E hE hmap

/-- Arithmetic input: a nontrivial element fails to commute with some element of a finite fixing subgroup. -/
lemma FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one (K : Type) [Field K]
    [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : FiniteDimensional K E) :
    ∃ σ ∈ FATEX28.fixingSubgroupSet (K := K) E, σ * g ≠ g * σ := by
  classical
  by_cases hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E
  · exact
      FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case
        (K := K) g h E hE hmap
  · exact FATEX28.exists_noncommuting_in_fixingSubgroup_of_map_ne (K := K) g E hmap

/-- Arithmetic input: a nontrivial element has non-open centralizer. -/
lemma FATEX28.centralizer_not_open_of_ne_one (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1) :
    ¬ IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) := by
  intro hopen
  obtain ⟨E, hfin, hsub⟩ :=
    FATEX28.exists_finite_intermediateField_fixingSubgroup_le_centralizer_of_isOpen
      (K := K) g hopen
  obtain ⟨σ, hσ, hcomm⟩ :=
    FATEX28.exists_noncommuting_in_fixingSubgroup_of_ne_one (K := K) g h E hfin
  have hσ' :
      σ ∈ (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
        (Field.absoluteGaloisGroup K)) :=
    hsub hσ
  have hcomm' : σ * g = g * σ :=
    (Subgroup.mem_centralizer_singleton_iff.mp hσ')
  exact hcomm hcomm'

/-- Stable-case obstruction: the fixing subgroup is not contained in the centralizer. -/
theorem Field.absoluteGaloisGroup.not_le_centralizer_fixingSubgroup_of_ne_one_stable_case
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (g : Field.absoluteGaloisGroup K) (h : g ≠ 1)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : FiniteDimensional K E)
    (hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E) :
    ¬ (FATEX28.fixingSubgroupSet (K := K) E ⊆
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K))) := by
  intro hsubset
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : IsGalois K (AlgebraicClosure K) := by infer_instance
  have hopen_fix :
      IsOpen (FATEX28.fixingSubgroupSet (K := K) E) := by
    simpa [FATEX28.fixingSubgroupSet] using
      (InfiniteGalois.isOpen_iff_finite (k := K) (K := AlgebraicClosure K) (L := E)).2 hE
  have hsubset' :
      E.fixingSubgroup ≤
        Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) := by
    intro σ hσ
    exact hsubset hσ
  have hopen_centralizer :
      IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) :=
    Subgroup.isOpen_mono (H₁ := E.fixingSubgroup)
      (H₂ := Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K))) hsubset' hopen_fix
  exact (FATEX28.centralizer_not_open_of_ne_one (K := K) g h) hopen_centralizer

/-- Stable-case arithmetic input when `g` preserves `E`. -/
theorem Field.absoluteGaloisGroup.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (g : Field.absoluteGaloisGroup K) (h : g ≠ 1)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : FiniteDimensional K E)
    (hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E) :
    ∃ σ ∈ FATEX28.fixingSubgroupSet (K := K) E, σ * g ≠ g * σ := by
  classical
  by_contra hcomm
  have hsubset :
      FATEX28.fixingSubgroupSet (K := K) E ⊆
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) := by
    intro σ hσ
    have hcomm' : σ * g = g * σ := by
      by_contra hne
      exact hcomm ⟨σ, hσ, hne⟩
    exact (Subgroup.mem_centralizer_singleton_iff).2 hcomm'
  exact
    (Field.absoluteGaloisGroup.not_le_centralizer_fixingSubgroup_of_ne_one_stable_case
        (K := K) g h E hE hmap) hsubset

/-- Arithmetic input: a nontrivial element fails to commute with some fixing subgroup element. -/
theorem Field.absoluteGaloisGroup.exists_noncommuting_in_fixingSubgroup_of_ne_one (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1)
    (E : IntermediateField K (AlgebraicClosure K)) (hE : FiniteDimensional K E) :
    ∃ σ ∈ FATEX28.fixingSubgroupSet (K := K) E, σ * g ≠ g * σ := by
  classical
  by_cases hmap : E.map (FATEX28.absGal_toAlgHom (K := K) g) = E
  · exact
      Field.absoluteGaloisGroup.exists_noncommuting_in_fixingSubgroup_of_ne_one_stable_case
        (K := K) g h E hE hmap
  · exact FATEX28.exists_noncommuting_in_fixingSubgroup_of_map_ne (K := K) g E hmap

/-- Arithmetic input: a nontrivial element has non-open centralizer. -/
theorem Field.absoluteGaloisGroup.centralizer_not_open_of_ne_one (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1) :
    ¬ IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) := by
  intro hopen
  obtain ⟨E, hfin, hsub⟩ :=
    FATEX28.exists_finite_intermediateField_fixingSubgroup_le_centralizer_of_isOpen
      (K := K) g hopen
  obtain ⟨σ, hσ, hcomm⟩ :=
    Field.absoluteGaloisGroup.exists_noncommuting_in_fixingSubgroup_of_ne_one
      (K := K) g h E hfin
  have hσ' :
      σ ∈ (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
        (Field.absoluteGaloisGroup K)) :=
    hsub hσ
  have hcomm' : σ * g = g * σ :=
    (Subgroup.mem_centralizer_singleton_iff.mp hσ')
  exact hcomm hcomm'

/-- Arithmetic input: the centralizer of a nontrivial element has infinite index. -/
theorem Field.absoluteGaloisGroup.centralizer_not_finiteIndex_of_ne_one (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1) :
    ¬ Subgroup.FiniteIndex (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K))) := by
  classical
  intro hfin
  haveI :
      (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K))).FiniteIndex := hfin
  have hclosed :
      IsClosed
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) :=
    FATEX28.isClosed_centralizer_singleton (G := Field.absoluteGaloisGroup K) g
  have hopen :
      IsOpen
        (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K)) : Set
          (Field.absoluteGaloisGroup K)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex
      (H := Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K))) hclosed
  exact (Field.absoluteGaloisGroup.centralizer_not_open_of_ne_one (K := K) g h) hopen

theorem infinite_conj_of_ne_1_absoluteGaloisGroup (K : Type)
    [Field K] [Algebra ℚ K] [Module.Finite ℚ K] (g : Field.absoluteGaloisGroup K) (h : g ≠ 1) :
    {g' : Field.absoluteGaloisGroup K | IsConj g g'}.Infinite := by
  classical
  have hcentral :
      ¬ Subgroup.FiniteIndex (Subgroup.centralizer ({g} : Set (Field.absoluteGaloisGroup K))) :=
    Field.absoluteGaloisGroup.centralizer_not_finiteIndex_of_ne_one (K := K) g h
  have horbit :
      (MulAction.orbit (ConjAct (Field.absoluteGaloisGroup K)) g).Infinite :=
    FATEX28.orbit_infinite_of_centralizer_not_finiteIndex (G := Field.absoluteGaloisGroup K) g hcentral
  simpa [FATEX28.conjSet_eq_orbit_conjAct (G := Field.absoluteGaloisGroup K) (g := g)] using horbit

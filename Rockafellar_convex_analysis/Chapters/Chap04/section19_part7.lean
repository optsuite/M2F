import Mathlib
import Rockafellar_convex_analysis.Chapters.Chap04.section19_part6

open scoped BigOperators
open scoped Pointwise
open Topology

section Chap19
section Section19

/-- Helper for Corollary 19.1.2: coercing a nonempty lower-bounded real set into `EReal`
preserves its infimum. -/
lemma helperForCorollary_19_1_2_sInf_coe_image_eq_sInf_real
    {T : Set ℝ}
    (hT_nonempty : T.Nonempty)
    (hT_bddBelow : BddBelow T) :
    (sInf ((fun q : ℝ => (q : EReal)) '' T) : EReal) = (sInf T : ℝ) := by
  let S' : Set (WithTop ℝ) := ((fun q : ℝ => (q : WithTop ℝ)) '' T)
  have hS'_bdd : BddBelow S' := by
    refine Monotone.map_bddBelow ?_ hT_bddBelow
    intro a b hab
    exact WithTop.coe_le_coe.mpr hab
  have hsInf_S' :
      (WithBot.some (sInf S') : EReal) =
        sInf ((fun y : WithTop ℝ => (WithBot.some y : EReal)) '' S') := by
    simpa using (WithBot.coe_sInf' (α := WithTop ℝ) (s := S') hS'_bdd)
  have hsInf_T : ((sInf T : ℝ) : WithTop ℝ) = sInf S' := by
    simpa [S'] using (WithTop.coe_sInf' (α := ℝ) (s := T) hT_nonempty hT_bddBelow)
  have himage_eq :
      ((fun q : ℝ => (q : EReal)) '' T) =
        ((fun y : WithTop ℝ => (WithBot.some y : EReal)) '' S') := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨q, hqT, rfl⟩
      exact ⟨(q : WithTop ℝ), ⟨q, hqT, rfl⟩, rfl⟩
    · intro hz
      rcases hz with ⟨y, hyS', hyz⟩
      rcases hyS' with ⟨q, hqT, hyq⟩
      subst hyq
      exact ⟨q, hqT, hyz⟩
  calc
    (sInf ((fun q : ℝ => (q : EReal)) '' T) : EReal)
        = sInf ((fun y : WithTop ℝ => (WithBot.some y : EReal)) '' S') := by
          simp [himage_eq]
    _ = (WithBot.some (sInf S') : EReal) := by
          simpa using hsInf_S'.symm
    _ = (WithBot.some (((sInf T : ℝ) : WithTop ℝ)) : EReal) := by
          simp [hsInf_T]
    _ = (sInf T : ℝ) := rfl

/-- Helper for Corollary 19.1.2: nonemptiness of the objective-value set gives one
admissible coefficient vector. -/
lemma helperForCorollary_19_1_2_exists_lam_of_nonemptyObjectiveSet
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ}
    (hSnonempty :
      ({r : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r = ((∑ i, lam i * α i : ℝ) : EReal)}).Nonempty) :
    ∃ (lam : Fin m → ℝ) (r : EReal),
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i) ∧
      r = ((∑ i, lam i * α i : ℝ) : EReal) := by
  rcases hSnonempty with ⟨r, hr⟩
  rcases hr with ⟨lam, hlin, hnorm, hnonneg, hobj⟩
  exact ⟨lam, r, hlin, hnorm, hnonneg, hobj⟩

/-- Helper for Corollary 19.1.2: the objective-value set equals the image of the feasible
coefficient set under the linear objective map (cast to `EReal`). -/
lemma helperForCorollary_19_1_2_objectiveValueSet_eq_image_feasibleCoefficients
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} :
    {r' : EReal |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        r' = ((∑ i, lam i * α i : ℝ) : EReal)} =
      (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
        {lam : Fin m → ℝ |
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i)} := by
  ext r'
  constructor
  · intro hr
    rcases hr with ⟨lam, hlin, hnorm, hnonneg, hobj⟩
    refine ⟨lam, ?_, hobj.symm⟩
    exact ⟨hlin, hnorm, hnonneg⟩
  · intro hr
    rcases hr with ⟨lam, hfeas, hobj⟩
    rcases hfeas with ⟨hlin, hnorm, hnonneg⟩
    exact ⟨lam, hlin, hnorm, hnonneg, hobj.symm⟩

/-- Helper for Corollary 19.1.2: continuity of the coefficient objective map into `EReal`. -/
lemma helperForCorollary_19_1_2_objectiveValueMap_continuous
    {m : ℕ} {α : Fin m → ℝ} :
    Continuous (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) := by
  have hcont_real :
      Continuous (fun lam : Fin m → ℝ => (∑ i, lam i * α i : ℝ)) := by
    exact
      continuous_finset_sum Finset.univ (by
        intro i hi
        exact (continuous_apply i).mul continuous_const)
  exact continuous_coe_real_ereal.comp hcont_real

/-- Helper for Corollary 19.1.2: compactness of the feasible coefficient set implies
closedness of the objective-value set. -/
lemma helperForCorollary_19_1_2_objectiveValueSet_closed_of_compactFeasible
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ}
    (hcompact_feasible :
      IsCompact
        {lam : Fin m → ℝ |
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i)}) :
    IsClosed
      {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} := by
  have hcont_obj :
      Continuous (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) :=
    helperForCorollary_19_1_2_objectiveValueMap_continuous (m := m) (α := α)
  have himage_compact :
      IsCompact
        ((fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
          {lam : Fin m → ℝ |
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i)}) :=
    hcompact_feasible.image hcont_obj
  have himage_closed :
      IsClosed
        ((fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
          {lam : Fin m → ℝ |
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i)}) :=
    himage_compact.isClosed
  have hEq :
      {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} =
        (fun lam : Fin m → ℝ => ((∑ i, lam i * α i : ℝ) : EReal)) ''
          {lam : Fin m → ℝ |
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i)} :=
    helperForCorollary_19_1_2_objectiveValueSet_eq_image_feasibleCoefficients
      (n := n) (k := k) (m := m) (a := a) (α := α) (x := x)
  simpa [hEq] using himage_closed

/-- Helper for Corollary 19.1.2: finite generation of the feasible coefficient set implies
closedness of the associated objective-value set. -/
lemma helperForCorollary_19_1_2_closed_objectiveValueSet_of_feasibleFG
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ}
    (hfg_feasible :
      IsFinitelyGeneratedConvexSet m
        {lam : Fin m → ℝ |
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i)}) :
    IsClosed
      {q : ℝ |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          q = (∑ i, lam i * α i : ℝ)} := by
  let F : Set (Fin m → ℝ) :=
    {lam : Fin m → ℝ |
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i)}
  let T : Set ℝ :=
    {q : ℝ |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        q = (∑ i, lam i * α i : ℝ)}
  let objectiveToReal : (Fin m → ℝ) →ₗ[ℝ] ℝ :=
    ∑ i, α i • LinearMap.proj i
  let realToFin1 : ℝ →ₗ[ℝ] (Fin 1 → ℝ) :=
    LinearMap.pi (fun _ : Fin 1 => (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  let objectiveToFin1 : (Fin m → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) :=
    realToFin1.comp objectiveToReal
  have hObjectiveEval :
      ∀ lam : Fin m → ℝ, objectiveToReal lam = (∑ i, lam i * α i : ℝ) := by
    intro lam
    calc
      objectiveToReal lam = ∑ i, α i * lam i := by
            simp [objectiveToReal]
      _ = ∑ i, lam i * α i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
  have hfgF : IsFinitelyGeneratedConvexSet m F := by
    simpa [F] using hfg_feasible
  have hfg_image : IsFinitelyGeneratedConvexSet 1 (objectiveToFin1 '' F) :=
    helperForCorollary_19_1_2_linearImage_finitelyGeneratedSet
      (n := m) (p := 1) (C := F) (L := objectiveToFin1)
      hfgF
  have hconv_image : Convex ℝ (objectiveToFin1 '' F) := by
    rcases hfg_image with ⟨S₀, S₁, hS₀finite, hS₁finite, hEqImage⟩
    simpa [hEqImage] using convex_mixedConvexHull (n := 1) S₀ S₁
  have hpoly_image : IsPolyhedralConvexSet 1 (objectiveToFin1 '' F) :=
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := 1) (C := objectiveToFin1 '' F) hconv_image hfg_image
  have hclosed_image : IsClosed (objectiveToFin1 '' F) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := 1) (C := objectiveToFin1 '' F) hpoly_image).1
  let embedRealToFin1 : ℝ → Fin 1 → ℝ := fun q _ => q
  have hEmbed_continuous : Continuous embedRealToFin1 :=
    continuous_pi (fun _ => continuous_id)
  have hT_eq_preimage : T = embedRealToFin1 ⁻¹' (objectiveToFin1 '' F) := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨lam, hlin, hnorm, hnonneg, hqObj⟩
      change embedRealToFin1 q ∈ objectiveToFin1 '' F
      refine ⟨lam, ?_, ?_⟩
      · exact ⟨hlin, hnorm, hnonneg⟩
      · funext i
        simp [embedRealToFin1, objectiveToFin1, realToFin1, hObjectiveEval, hqObj]
    · intro hq
      change embedRealToFin1 q ∈ objectiveToFin1 '' F at hq
      rcases hq with ⟨lam, hlamF, hEqFun⟩
      rcases hlamF with ⟨hlin, hnorm, hnonneg⟩
      have hqObj : q = (∑ i, lam i * α i : ℝ) := by
        have hEval := congrArg (fun u : Fin 1 → ℝ => u 0) hEqFun
        exact (by
          simpa [embedRealToFin1, objectiveToFin1, realToFin1, hObjectiveEval] using hEval.symm)
      exact ⟨lam, hlin, hnorm, hnonneg, hqObj⟩
  have hclosed_preimage : IsClosed (embedRealToFin1 ⁻¹' (objectiveToFin1 '' F)) :=
    hclosed_image.preimage hEmbed_continuous
  simpa [hT_eq_preimage, T] using hclosed_preimage

/-- Helper for Corollary 19.1.2: the feasible coefficient set for fixed `x` is finitely
generated because it is the solution set of finitely many linear equalities and inequalities. -/
lemma helperForCorollary_19_1_2_feasibleCoeffSet_finitelyGenerated
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {x : Fin n → ℝ} :
    IsFinitelyGeneratedConvexSet m
      {lam : Fin m → ℝ |
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i)} := by
  let F : Set (Fin m → ℝ) :=
    {lam : Fin m → ℝ |
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i)}
  let aEq : Fin (n + 1) → Fin m → ℝ :=
    Fin.cases (fun i : Fin m => if (i : ℕ) < k then (1 : ℝ) else 0)
      (fun j : Fin n => fun i : Fin m => a i j)
  let αEq : Fin (n + 1) → ℝ :=
    Fin.cases (1 : ℝ) (fun j : Fin n => x j)
  let bIneq : Fin m → Fin m → ℝ :=
    fun i j => if j = i then (-1 : ℝ) else 0
  let βIneq : Fin m → ℝ := fun _ => 0
  have hpoly_system :
      IsPolyhedralConvexSet m
        {lam : Fin m → ℝ |
          (∀ t, lam ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, lam ⬝ᵥ bIneq i ≤ βIneq i)} := by
    simpa [βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        m (n + 1) m aEq αEq bIneq βIneq)
  have hF_eq_system :
      F =
        {lam : Fin m → ℝ |
          (∀ t, lam ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, lam ⬝ᵥ bIneq i ≤ βIneq i)} := by
    ext lam
    simp [F, aEq, αEq, bIneq, βIneq, dotProduct, Finset.sum_filter,
      Fin.forall_fin_succ, and_left_comm, and_assoc]
  have hpolyF : IsPolyhedralConvexSet m F := by
    simpa [hF_eq_system] using hpoly_system
  have hconvF : Convex ℝ F :=
    helperForTheorem_19_1_polyhedral_isConvex (n := m) (C := F) hpolyF
  have hTFAE :
      [IsPolyhedralConvexSet m F,
          (IsClosed F ∧ {C' : Set (Fin m → ℝ) | IsFace (𝕜 := ℝ) F C'}.Finite),
        IsFinitelyGeneratedConvexSet m F].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := m) (C := F) hconvF
  exact (hTFAE.out 0 2).1 hpolyF

/-- Helper for Corollary 19.1.2: closedness of the objective-value set attached to one
finitely generated representation at fixed `x`. -/
lemma helperForCorollary_19_1_2_closed_objectiveValueSet
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} :
    IsClosed
      {q : ℝ |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          q = (∑ i, lam i * α i : ℝ)} := by
  let F : Set (Fin m → ℝ) :=
    {lam : Fin m → ℝ |
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i)}
  have hfg_feasible : IsFinitelyGeneratedConvexSet m F := by
    simpa [F] using
      helperForCorollary_19_1_2_feasibleCoeffSet_finitelyGenerated
        (n := n) (k := k) (m := m) (a := a) (x := x)
  simpa [F] using
    helperForCorollary_19_1_2_closed_objectiveValueSet_of_feasibleFG
      (n := n) (k := k) (m := m) (a := a) (α := α) (x := x)
      hfg_feasible

/-- Helper for Corollary 19.1.2: if the infimum of the objective-value set is a finite real,
then that real value belongs to the objective-value set. -/
lemma helperForCorollary_19_1_2_memObjectiveSet_of_finiteValue
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hsInf_real :
      sInf {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} = (r : EReal)) :
    (r : EReal) ∈
      {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} := by
  let Sx : Set EReal :=
    {r' : EReal |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        r' = ((∑ i, lam i * α i : ℝ) : EReal)}
  let T : Set ℝ :=
    {q : ℝ |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        q = (∑ i, lam i * α i : ℝ)}
  have hSx_eq_coeImage_T :
      Sx = (fun q : ℝ => (q : EReal)) '' T := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨lam, hlin, hnorm, hnonneg, hzobj⟩
      refine ⟨(∑ i, lam i * α i : ℝ), ?_, ?_⟩
      · exact ⟨lam, hlin, hnorm, hnonneg, rfl⟩
      · simp [hzobj]
    · intro hz
      rcases hz with ⟨q, hqT, hzq⟩
      rcases hqT with ⟨lam, hlin, hnorm, hnonneg, hqobj⟩
      have hzobj : z = ((∑ i, lam i * α i : ℝ) : EReal) := by
        calc
          z = (q : EReal) := hzq.symm
          _ = ((∑ i, lam i * α i : ℝ) : EReal) := by simp [hqobj]
      exact ⟨lam, hlin, hnorm, hnonneg, hzobj⟩
  have hsInf_real_Sx : sInf Sx = (r : EReal) := by
    simpa [Sx] using hsInf_real
  have hSx_nonempty : Sx.Nonempty :=
    helperForCorollary_19_1_2_nonempty_of_sInf_eq_real
      (S := Sx) (r := r) hsInf_real_Sx
  have hT_nonempty : T.Nonempty := by
    rcases hSx_nonempty with ⟨z, hz⟩
    rcases hz with ⟨lam, hlin, hnorm, hnonneg, hzobj⟩
    refine ⟨(∑ i, lam i * α i : ℝ), ?_⟩
    exact ⟨lam, hlin, hnorm, hnonneg, rfl⟩
  have hT_bddBelow : BddBelow T := by
    refine ⟨r, ?_⟩
    intro q hqT
    have hqSx : (q : EReal) ∈ Sx := by
      have hqImage : (q : EReal) ∈ (fun q : ℝ => (q : EReal)) '' T :=
        ⟨q, hqT, rfl⟩
      simpa [hSx_eq_coeImage_T] using hqImage
    have hsInf_le_qE : sInf Sx ≤ (q : EReal) := sInf_le hqSx
    have hr_le_qE : (r : EReal) ≤ (q : EReal) := by
      simpa [hsInf_real_Sx] using hsInf_le_qE
    exact (EReal.coe_le_coe_iff).1 hr_le_qE
  have hsInf_coeImage_T :
      (sInf ((fun q : ℝ => (q : EReal)) '' T) : EReal) = (sInf T : ℝ) :=
    helperForCorollary_19_1_2_sInf_coe_image_eq_sInf_real
      (T := T) hT_nonempty hT_bddBelow
  have hsInfT_eq_rE : ((sInf T : ℝ) : EReal) = (r : EReal) := by
    calc
      ((sInf T : ℝ) : EReal)
          = sInf ((fun q : ℝ => (q : EReal)) '' T) := by
              exact hsInf_coeImage_T.symm
      _ = sInf Sx := by simp [hSx_eq_coeImage_T]
      _ = (r : EReal) := hsInf_real_Sx
  have hsInfT_eq_r : sInf T = r := by
    exact EReal.coe_injective hsInfT_eq_rE
  have hT_closed : IsClosed T := by
    simpa [T] using
      helperForCorollary_19_1_2_closed_objectiveValueSet
        (n := n) (k := k) (m := m) (a := a) (α := α) (x := x)
  have hsInf_mem_T : sInf T ∈ T :=
    IsClosed.csInf_mem hT_closed hT_nonempty hT_bddBelow
  have hr_mem_T : r ∈ T := by
    simpa [hsInfT_eq_r] using hsInf_mem_T
  rcases hr_mem_T with ⟨lam, hlin, hnorm, hnonneg, hrobj⟩
  have hrobjE : (r : EReal) = ((∑ i, lam i * α i : ℝ) : EReal) := by
    simp [hrobj]
  exact ⟨lam, hlin, hnorm, hnonneg, hrobjE⟩

/-- Helper for Corollary 19.1.2: membership of the finite infimum value in the objective set
gives coefficients attaining exactly `f x`. -/
lemma helperForCorollary_19_1_2_attainment_value_of_infMember
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} {x : Fin n → ℝ} {r : ℝ}
    (hrfx : f x = (r : EReal))
    (hrmem :
      (r : EReal) ∈
        {r' : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r' = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ∃ (lam : Fin m → ℝ),
      (∀ j, (∑ i, lam i * a i j) = x j) ∧
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1 ∧
      (∀ i, 0 ≤ lam i) ∧
      f x = ((∑ i, lam i * α i : ℝ) : EReal) := by
  rcases hrmem with ⟨lam, hlin, hnorm, hnonneg, hobj⟩
  refine ⟨lam, hlin, hnorm, hnonneg, ?_⟩
  calc
    f x = (r : EReal) := hrfx
    _ = ((∑ i, lam i * α i : ℝ) : EReal) := by simpa using hobj

/-- Helper for Corollary 19.1.2: in a fixed finite-generation representation, finite values are
attained by admissible coefficients. -/
lemma helperForCorollary_19_1_2_attainment_of_finiteValue
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ∀ x,
      (∃ r : ℝ, f x = (r : EReal)) →
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          f x = ((∑ i, lam i * α i : ℝ) : EReal) := by
  intro x hxfinite
  rcases hxfinite with ⟨r, hrfx⟩
  have hsInf_real :
      sInf {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} = (r : EReal) := by
    calc
      sInf {r' : EReal |
        ∃ (lam : Fin m → ℝ),
          (∀ j, (∑ i, lam i * a i j) = x j) ∧
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 1 ∧
          (∀ i, 0 ≤ lam i) ∧
          r' = ((∑ i, lam i * α i : ℝ) : EReal)} = f x := by
            exact (hrepr x).symm
      _ = (r : EReal) := hrfx
  have hrmem :
      (r : EReal) ∈
        {r' : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r' = ((∑ i, lam i * α i : ℝ) : EReal)} :=
    helperForCorollary_19_1_2_memObjectiveSet_of_finiteValue
      (n := n) (k := k) (m := m) (a := a) (α := α) (x := x) (r := r) hsInf_real
  exact
    helperForCorollary_19_1_2_attainment_value_of_infMember
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) (x := x) (r := r)
      hrfx hrmem

/-- Corollary 19.1.2: A convex function is polyhedral iff it is finitely generated; such a
function, if proper, is closed; and in the finitely generated representation the infimum at
`x`, when finite, is attained by some coefficients `λ`. -/
theorem polyhedral_convex_iff_finitelyGenerated_and_closed_and_attainment
    (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    (IsPolyhedralConvexFunction n f ↔ IsFinitelyGeneratedConvexFunction n f) ∧
      (IsPolyhedralConvexFunction n f →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
        ClosedConvexFunction f) ∧
      (IsFinitelyGeneratedConvexFunction n f →
        ∃ (k m : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ),
          k ≤ m ∧
            (∀ x,
              f x =
                sInf {r : EReal |
                  ∃ (lam : Fin m → ℝ),
                    (∀ j, (∑ i, lam i * a i j) = x j) ∧
                    (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                      (fun i => lam i)) = 1 ∧
                    (∀ i, 0 ≤ lam i) ∧
                    r = ((∑ i, lam i * α i : ℝ) : EReal)}) ∧
            (∀ x,
              (∃ r : ℝ, f x = (r : EReal)) →
                ∃ (lam : Fin m → ℝ),
                  (∀ j, (∑ i, lam i * a i j) = x j) ∧
                (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                  (fun i => lam i)) = 1 ∧
                (∀ i, 0 ≤ lam i) ∧
                f x = ((∑ i, lam i * α i : ℝ) : EReal))) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hfpoly
      exact
        helperForCorollary_19_1_2_polyhedral_imp_finitelyGenerated
          (n := n) (f := f) hfpoly
    · intro hfgen
      exact
        helperForCorollary_19_1_2_finitelyGenerated_imp_polyhedral
          (n := n) (f := f) hfgen
  · intro hfpoly hfproper
    exact
      helperForCorollary_19_1_2_closed_of_polyhedral_proper
        (n := n) (f := f) hfpoly hfproper
  · intro hfgen
    rcases
      helperForCorollary_19_1_2_unpack_finitelyGeneratedData
        (n := n) (f := f) hfgen with
      ⟨k, m, a, α, hk, hrepr⟩
    refine ⟨k, m, a, α, hk, hrepr, ?_⟩
    intro x hxfinite
    exact
      helperForCorollary_19_1_2_attainment_of_finiteValue
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hrepr x hxfinite

/-- Text 19.0.11: The function `f(x) = |ξ₁| + ··· + |ξₙ|` on `ℝ^n` is polyhedral convex,
since it is the pointwise supremum of the `2^n` linear functions
`x ↦ ε₁ ξ₁ + ··· + εₙ ξₙ` with `εⱼ ∈ {+1, -1}`. -/
theorem polyhedralConvex_absSum (n : ℕ) :
    IsPolyhedralConvexFunction n (fun x => ((∑ i, |x i| : ℝ) : EReal)) := sorry

/-- Text 19.0.12: The Tchebycheff (supremum) norm `f : ℝ^n → ℝ` defined by
`f(x) = max {|ξ₁|, …, |ξₙ|}` (with `x = (ξ₁, …, ξₙ)`) is polyhedral convex, since it is the
pointwise supremum of the `2n` linear functions `x ↦ ε_j ξ_j` with
`ε_j ∈ {+1, -1}` for `j = 1, …, n`. -/
theorem polyhedralConvex_tchebycheffSupNorm (n : ℕ) :
    IsPolyhedralConvexFunction n
      (fun x => ((sSup {r : ℝ | ∃ i : Fin n, r = |x i|} : ℝ) : EReal)) := sorry

/-- Helper for Text 19.0.13: build an explicit affine line in `ℝ²` with equation `x 1 = 1`
and record that the origin is not on it. -/
lemma helperForText_19_0_13_affineLine_x1_eq_one_data :
    ∃ L : AffineSubspace ℝ (Fin 2 → ℝ),
      Module.finrank ℝ L.direction = 1 ∧
        ((L : Set (Fin 2 → ℝ)) = {x | x 1 = 1}) ∧
        ((0 : Fin 2 → ℝ) ∉ (L : Set (Fin 2 → ℝ))) := by
  let x0 : Fin 2 → ℝ := ![(0 : ℝ), 1]
  let v : Fin 2 → ℝ := ![(1 : ℝ), 0]
  let L : AffineSubspace ℝ (Fin 2 → ℝ) := AffineSubspace.mk' x0 (ℝ ∙ v)
  have hv_ne : v ≠ 0 := by
    intro hv
    have : (1 : ℝ) = 0 := by
      simpa [v] using congrArg (fun z : Fin 2 → ℝ => z 0) hv
    norm_num at this
  have hdir : L.direction = (ℝ ∙ v) := by
    simp [L]
  have hfinrank : Module.finrank ℝ L.direction = 1 := by
    rw [hdir]
    exact finrank_span_singleton hv_ne
  have hcarrier : (L : Set (Fin 2 → ℝ)) = {x : Fin 2 → ℝ | x 1 = 1} := by
    ext x
    constructor
    · intro hx
      have hxdir : x -ᵥ x0 ∈ (ℝ ∙ v) := by
        simpa [L] using (AffineSubspace.mem_mk'.1 hx)
      rcases (Submodule.mem_span_singleton).1 hxdir with ⟨a, ha⟩
      have ha1 : (a • v) 1 = (x -ᵥ x0) 1 := congrArg (fun z : Fin 2 → ℝ => z 1) ha
      have ha1' : x 1 - 1 = 0 := by
        simpa [v, x0, vsub_eq_sub] using ha1.symm
      have hx1 : x 1 = 1 := by linarith
      simpa using hx1
    · intro hx
      have hxdir : x -ᵥ x0 ∈ (ℝ ∙ v) := by
        refine (Submodule.mem_span_singleton).2 ?_
        refine ⟨x 0, ?_⟩
        ext i
        fin_cases i
        · simp [v, x0, vsub_eq_sub]
        · have hx1 : x 1 = 1 := hx
          simp [v, x0, vsub_eq_sub, hx1]
      have hxmk : x ∈ AffineSubspace.mk' x0 (ℝ ∙ v) := (AffineSubspace.mem_mk').2 hxdir
      have hxL : x ∈ L := by
        simpa [L] using hxmk
      exact hxL
  have h0not : (0 : Fin 2 → ℝ) ∉ (L : Set (Fin 2 → ℝ)) := by
    intro h0
    have hzero : (0 : Fin 2 → ℝ) 1 = 1 := by
      simp [hcarrier] at h0
    norm_num at hzero
  exact ⟨L, hfinrank, hcarrier, h0not⟩

/-- Helper for Text 19.0.13: the explicit line `{x | x 1 = 1}` is polyhedral convex. -/
lemma helperForText_19_0_13_lineSet_polyhedral :
    IsPolyhedralConvexSet 2 {x : Fin 2 → ℝ | x 1 = 1} := by
  let a : Fin 1 → Fin 2 → ℝ := fun _ => Pi.single 1 (1 : ℝ)
  let α : Fin 1 → ℝ := fun _ => 1
  let b : Fin 0 → Fin 2 → ℝ := fun _ => 0
  let β : Fin 0 → ℝ := fun _ => 0
  have hpoly :
      IsPolyhedralConvexSet 2
        {x : Fin 2 → ℝ | (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j)} :=
    polyhedralConvexSet_solutionSet_linearEq_and_inequalities 2 1 0 a α b β
  have hEq :
      {x : Fin 2 → ℝ | (∀ i, x ⬝ᵥ a i = α i) ∧ (∀ j, x ⬝ᵥ b j ≤ β j)} =
        {x : Fin 2 → ℝ | x 1 = 1} := by
    ext x
    simp [a, α, b, β, dotProduct]
  rw [hEq] at hpoly
  exact hpoly

/-- Helper for Text 19.0.13: the convex hull of the line `{x | x 1 = 1}` united with
`{0}` is not closed. -/
lemma helperForText_19_0_13_notClosed_convexHull_line_union_origin :
    ¬ IsClosed
      (convexHull ℝ
        ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) := by
  rcases helperForText_19_0_13_affineLine_x1_eq_one_data with ⟨L, hLdim, hLset, h0notin⟩
  have hNotClosed :
      ¬ IsClosed (conv ((L : Set (Fin 2 → ℝ)) ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) :=
    not_isClosed_conv_line_union_singleton (L := L) (p := (0 : Fin 2 → ℝ)) hLdim h0notin
  simpa [conv, hLset] using hNotClosed

/-- Helper for Text 19.0.13: the same convex hull is therefore not polyhedral. -/
lemma helperForText_19_0_13_notPolyhedral_convexHull_line_union_origin :
    ¬ IsPolyhedralConvexSet 2
      (convexHull ℝ
        ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) := by
  intro hpoly
  have hclosed :
      IsClosed
        (convexHull ℝ
          ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)))) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := 2)
      (C :=
        convexHull ℝ
          ({x : Fin 2 → ℝ | x 1 = 1} ∪ ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ))))
      hpoly).1
  exact helperForText_19_0_13_notClosed_convexHull_line_union_origin hclosed

/-- Text 19.0.13: The convex hull of the union of two polyhedral convex sets need not be
polyhedral; for instance, this occurs for a line and a point not on the line. -/
theorem exists_polyhedralConvexSets_convexHull_union_not_polyhedral :
    ∃ (C₁ C₂ : Set (Fin 2 → ℝ)),
      IsPolyhedralConvexSet 2 C₁ ∧
        IsPolyhedralConvexSet 2 C₂ ∧
          ¬ IsPolyhedralConvexSet 2 (convexHull ℝ (C₁ ∪ C₂)) := by
  refine ⟨{x : Fin 2 → ℝ | x 1 = 1}, ({(0 : Fin 2 → ℝ)} : Set (Fin 2 → ℝ)), ?_, ?_, ?_⟩
  · exact helperForText_19_0_13_lineSet_polyhedral
  · simpa using (helperForTheorem_19_1_zero_set_polyhedral (m := 2))
  · exact helperForText_19_0_13_notPolyhedral_convexHull_line_union_origin

/-- Helper for Text 19.0.14: every polytope in `ℝ^n` is compact. -/
lemma helperForText_19_0_14_compact_of_polytope
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolytope n C) :
    IsCompact C := by
  rcases hCpoly with ⟨T, hTfinite, hTeq⟩
  rw [hTeq]
  exact hTfinite.isCompact_convexHull

/-- Helper for Text 19.0.14: a nonempty compact set in `ℝ^n` invariant under translation
by `d` must satisfy `d = 0`. -/
lemma helperForText_19_0_14_shift_eq_zero_of_compact_translateInvariant
    {n : ℕ} {C : Set (Fin n → ℝ)} {d : Fin n → ℝ}
    (hCcompact : IsCompact C)
    (hCnonempty : C.Nonempty)
    (htranslate : C + {d} = C) :
    d = 0 := by
  have hcontFun : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ d) := by
    simpa [dotProduct] using
      (continuous_finset_sum Finset.univ (fun i hi => (continuous_apply i).mul continuous_const))
  have hcont : ContinuousOn (fun x : Fin n → ℝ => x ⬝ᵥ d) C := hcontFun.continuousOn
  rcases hCcompact.exists_isMaxOn hCnonempty hcont with ⟨x, hxC, hxMax⟩
  have hxPlusMemAdd : x + d ∈ C + {d} := by
    refine Set.mem_add.2 ?_
    refine ⟨x, hxC, d, ?_, ?_⟩
    · simp
    · rfl
  have hxPlusMem : x + d ∈ C := by
    simpa [htranslate] using hxPlusMemAdd
  have hmaxIneq : (x + d) ⬝ᵥ d ≤ x ⬝ᵥ d := by
    exact (isMaxOn_iff.mp hxMax) (x + d) hxPlusMem
  have hddLeZero : d ⬝ᵥ d ≤ 0 := by
    have hsumIneq : x ⬝ᵥ d + d ⬝ᵥ d ≤ x ⬝ᵥ d := by
      simpa [add_dotProduct] using hmaxIneq
    linarith
  have hzeroLeDd : 0 ≤ d ⬝ᵥ d := by
    simpa [dotProduct] using (Finset.sum_nonneg (fun i hi => mul_self_nonneg (d i)))
  have hddEqZero : d ⬝ᵥ d = 0 := le_antisymm hddLeZero hzeroLeDd
  exact (dotProduct_self_eq_zero.mp hddEqZero)

/-- Helper for Text 19.0.14: if two translates of `S` both equal `C`, then the
translation vectors coincide. -/
lemma helperForText_19_0_14_unique_translation_parameter
    {n : ℕ} {C S : Set (Fin n → ℝ)} {y₀ y : Fin n → ℝ}
    (hSnonempty : S.Nonempty)
    (hSC : S ⊆ C)
    (hCcompact : IsCompact C)
    (hy₀ : S + {y₀} = C)
    (hy : S + {y} = C) :
    y = y₀ := by
  have hCnonempty : C.Nonempty := by
    rcases hSnonempty with ⟨s, hsS⟩
    exact ⟨s, hSC hsS⟩
  let d : Fin n → ℝ := y - y₀
  have htranslateSubsetLeft : C + {d} ⊆ C := by
    intro z hz
    rcases Set.mem_add.1 hz with ⟨c, hcC, u, huSingleton, hzu⟩
    have huEq : u = d := by
      simpa using huSingleton
    have hcS : c ∈ S + {y₀} := by
      simpa [hy₀] using hcC
    rcases Set.mem_add.1 hcS with ⟨s, hsS, v, hvSingleton, hsv⟩
    have hvEq : v = y₀ := by
      simpa using hvSingleton
    have hzEq : z = s + y := by
      calc
        z = c + u := by
          simpa using hzu.symm
        _ = c + d := by
          rw [huEq]
        _ = (s + v) + d := by
          rw [hsv]
        _ = (s + y₀) + d := by
          rw [hvEq]
        _ = s + y := by
          dsimp [d]
          abel_nf
    have hsAddMem : s + y ∈ S + {y} := by
      refine Set.mem_add.2 ?_
      refine ⟨s, hsS, y, ?_, ?_⟩
      · simp
      · rfl
    have hzMemTranslate : z ∈ S + {y} := by
      exact hzEq ▸ hsAddMem
    have hzMemC : z ∈ C := by
      simpa [hy] using hzMemTranslate
    exact hzMemC
  have htranslateSubsetRight : C ⊆ C + {d} := by
    intro z hzC
    have hzS : z ∈ S + {y} := by
      simpa [hy] using hzC
    rcases Set.mem_add.1 hzS with ⟨s, hsS, u, huSingleton, hzu⟩
    have huEq : u = y := by
      simpa using huSingleton
    have hsAddMemY₀ : s + y₀ ∈ S + {y₀} := by
      refine Set.mem_add.2 ?_
      refine ⟨s, hsS, y₀, ?_, ?_⟩
      · simp
      · rfl
    have hsAddMemC : s + y₀ ∈ C := by
      simpa [hy₀] using hsAddMemY₀
    have hzEq : z = (s + y₀) + d := by
      calc
        z = s + u := by
          simpa using hzu.symm
        _ = s + y := by
          rw [huEq]
        _ = (s + y₀) + d := by
          dsimp [d]
          abel_nf
    have hzMemAdd : z ∈ C + {d} := by
      refine Set.mem_add.2 ?_
      refine ⟨s + y₀, hsAddMemC, d, ?_, ?_⟩
      · simp
      · exact hzEq.symm
    exact hzMemAdd
  have htranslate : C + {d} = C := by
    exact Set.Subset.antisymm htranslateSubsetLeft htranslateSubsetRight
  have hdEqZero : d = 0 :=
    helperForText_19_0_14_shift_eq_zero_of_compact_translateInvariant
      (C := C) (d := d) hCcompact hCnonempty htranslate
  have hySubEqZero : y - y₀ = 0 := by
    simpa [d] using hdEqZero
  exact sub_eq_zero.mp hySubEqZero

/-- Helper for Text 19.0.14: both the empty set and every singleton in `ℝ^n` are
polytopes. -/
lemma helperForText_19_0_14_polytope_of_empty_or_singleton
    (n : ℕ) :
    IsPolytope n (∅ : Set (Fin n → ℝ)) ∧
      ∀ y₀ : Fin n → ℝ, IsPolytope n ({y₀} : Set (Fin n → ℝ)) := by
  constructor
  · refine ⟨∅, Set.finite_empty, ?_⟩
    simp
  · intro y₀
    refine ⟨{y₀}, Set.finite_singleton y₀, ?_⟩
    simp

/-- Text 19.0.14: Let `C ⊆ ℝ^n` be a convex polytope and let `S ⊆ C` be nonempty. For
`y ∈ ℝ^n`, define the translate `S + {y}` and `D := {y | S + {y} = C}`. Then `D` is a
possibly empty convex polytope in `ℝ^n`. -/
theorem polytope_setOf_translate_eq
    (n : ℕ) (C S : Set (Fin n → ℝ)) :
    IsPolytope n C →
      S.Nonempty →
        S ⊆ C →
          IsPolytope n {y : Fin n → ℝ | S + {y} = C} := by
  intro hCpoly hSnonempty hSC
  let D : Set (Fin n → ℝ) := {y : Fin n → ℝ | S + {y} = C}
  change IsPolytope n D
  by_cases hDne : D.Nonempty
  · rcases hDne with ⟨y₀, hy₀⟩
    have hCcompact : IsCompact C :=
      helperForText_19_0_14_compact_of_polytope (n := n) (C := C) hCpoly
    have hDsubsetSingleton : D ⊆ ({y₀} : Set (Fin n → ℝ)) := by
      intro y hyD
      have hyEq : y = y₀ :=
        helperForText_19_0_14_unique_translation_parameter
          (C := C) (S := S) (y₀ := y₀) (y := y)
          hSnonempty hSC hCcompact hy₀ hyD
      simp [hyEq]
    have hSingletonSubsetD : ({y₀} : Set (Fin n → ℝ)) ⊆ D := by
      intro y hySingleton
      rcases hySingleton with rfl
      exact hy₀
    have hDeqSingleton : D = ({y₀} : Set (Fin n → ℝ)) := by
      exact Set.Subset.antisymm hDsubsetSingleton hSingletonSubsetD
    have hSingletonPoly : IsPolytope n ({y₀} : Set (Fin n → ℝ)) :=
      (helperForText_19_0_14_polytope_of_empty_or_singleton n).2 y₀
    rw [hDeqSingleton]
    exact hSingletonPoly
  · have hDforallNotMem : ∀ y : Fin n → ℝ, y ∉ D := by
      intro y hyD
      exact hDne ⟨y, hyD⟩
    have hDeqEmpty : D = (∅ : Set (Fin n → ℝ)) :=
      Set.eq_empty_iff_forall_notMem.mpr hDforallNotMem
    have hEmptyPoly : IsPolytope n (∅ : Set (Fin n → ℝ)) :=
      (helperForText_19_0_14_polytope_of_empty_or_singleton n).1
    rw [hDeqEmpty]
    exact hEmptyPoly

/-- Helper for Theorem 19.2: extract a finite Text 19.0.10 representation from
polyhedrality. -/
lemma helperForTheorem_19_2_extractFiniteRepresentation
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ∃ (k m : ℕ) (a : Fin m → Fin n → ℝ) (α : Fin m → ℝ),
      k ≤ m ∧
        ∀ x,
          f x =
            sInf {r : EReal |
              ∃ (lam : Fin m → ℝ),
                (∀ j, (∑ i, lam i * a i j) = x j) ∧
                (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                  (fun i => lam i)) = 1 ∧
                (∀ i, 0 ≤ lam i) ∧
                r = ((∑ i, lam i * α i : ℝ) : EReal)} := by
  have hfgen : IsFinitelyGeneratedConvexFunction n f :=
    helperForCorollary_19_1_2_polyhedral_imp_finitelyGenerated (n := n) (f := f) hfpoly
  exact
    helperForCorollary_19_1_2_unpack_finitelyGeneratedData
      (n := n) (f := f) hfgen

/-- Helper for Theorem 19.2: in a Text 19.0.10 representation, `k = 0` forces `f = ⊤`. -/
lemma helperForTheorem_19_2_kZero_forces_constTop
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hk0 : k = 0)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ∀ x, f x = ⊤ := by
  intro x
  let Sx : Set EReal :=
    {r : EReal |
      ∃ (lam : Fin m → ℝ),
        (∀ j, (∑ i, lam i * a i j) = x j) ∧
        (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
          (fun i => lam i)) = 1 ∧
        (∀ i, 0 ≤ lam i) ∧
        r = ((∑ i, lam i * α i : ℝ) : EReal)}
  have hSx_empty : Sx = (∅ : Set EReal) := by
    ext r
    constructor
    · intro hr
      rcases hr with ⟨lam, _hlin, hnorm, _hnonneg, _hobj⟩
      have hsum_zero :
          (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) = 0 := by
        simp [hk0]
      have hzero_one : (0 : ℝ) = 1 := by
        calc
          (0 : ℝ) = (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
            (fun i => lam i)) := hsum_zero.symm
          _ = 1 := hnorm
      norm_num at hzero_one
    · intro hr
      exact False.elim (Set.notMem_empty r hr)
  calc
    f x = sInf Sx := by simpa [Sx] using (hrepr x)
    _ = sInf (∅ : Set EReal) := by simp [hSx_empty]
    _ = ⊤ := by simp

/-- Helper for Theorem 19.2: the degenerate `k = 0` branch gives
`fenchelConjugate n f = constNegInf n`. -/
lemma helperForTheorem_19_2_kZero_forces_constTop_and_conjugate_constNegInf
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hk0 : k = 0)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    fenchelConjugate n f = constNegInf n := by
  have htop : ∀ x, f x = ⊤ :=
    helperForTheorem_19_2_kZero_forces_constTop
      (k := k) (m := m) (f := f) (a := a) (α := α) hk0 hrepr
  have hf_eq_constTop : f = (fun _ : Fin n → ℝ => (⊤ : EReal)) := by
    funext x
    exact htop x
  calc
    fenchelConjugate n f =
        fenchelConjugate n (fun _ : Fin n → ℝ => (⊤ : EReal)) := by
          simp [hf_eq_constTop]
    _ = constNegInf n := fenchelConjugate_constPosInf n

/-- Helper for Theorem 19.2: the constant `-∞` function is polyhedral convex. -/
lemma helperForTheorem_19_2_constNegInf_isPolyhedralConvexFunction
    (n : ℕ) :
    IsPolyhedralConvexFunction n (constNegInf n) := by
  refine ⟨?_, ?_⟩
  · have hEpiUniv : epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n) = Set.univ := by
      ext p
      constructor
      · intro hp
        trivial
      · intro hp
        refine ⟨?_, ?_⟩
        · trivial
        · simp [constNegInf]
    simpa [ConvexFunctionOn, hEpiUniv] using
      (convex_univ : Convex ℝ (Set.univ : Set ((Fin n → ℝ) × ℝ)))
  · classical
    let ι : Type := PEmpty
    let b : ι → Fin (n + 1) → ℝ := fun i => nomatch i
    let β : ι → ℝ := fun i => nomatch i
    have hPolyUniv : IsPolyhedralConvexSet (n + 1) (Set.univ : Set (Fin (n + 1) → ℝ)) := by
      refine ⟨ι, inferInstance, b, β, ?_⟩
      ext x
      simp [closedHalfSpaceLE, b, β]
    have hEpiUniv : epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n) = Set.univ := by
      ext p
      constructor
      · intro hp
        trivial
      · intro hp
        refine ⟨?_, ?_⟩
        · trivial
        · simp [constNegInf]
    have hImageUnivCoord :
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n)) =
          (Set.univ : Set (Fin (n + 1) → ℝ)) := by
      rw [hEpiUniv, Set.image_univ]
      exact Set.range_eq_univ.mpr (prodLinearEquiv_append_coord (n := n)).surjective
    have hpolyCoord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (constNegInf n)) := by
      simpa [hImageUnivCoord] using hPolyUniv
    simpa [prodLinearEquiv_append_coord] using hpolyCoord

/-- Helper for Theorem 19.2: positivity of `k` and `k ≤ m` provides a point-index
below `k`. -/
lemma helperForTheorem_19_2_existsPointIndex_of_posK
    {k m : ℕ}
    (hkpos : 0 < k)
    (hk : k ≤ m) :
    ∃ i0 : Fin m, (i0 : ℕ) < k := by
  refine ⟨⟨0, ?_⟩, hkpos⟩
  exact lt_of_lt_of_le hkpos hk

/-- Helper for Theorem 19.2: any feasible coefficient vector gives an upper bound on
the represented function value. -/
lemma helperForTheorem_19_2_value_le_of_feasibleCoefficients
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {x : Fin n → ℝ} {lam : Fin m → ℝ}
    (hlin : ∀ j, (∑ i, lam i * a i j) = x j)
    (hnorm :
      (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
        (fun i => lam i)) = 1)
    (hnonneg : ∀ i, 0 ≤ lam i) :
    f x ≤ ((∑ i, lam i * α i : ℝ) : EReal) := by
  have hmem :
      ((∑ i, lam i * α i : ℝ) : EReal) ∈
        {r : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r = ((∑ i, lam i * α i : ℝ) : EReal)} := by
    exact ⟨lam, hlin, hnorm, hnonneg, rfl⟩
  calc
    f x =
        sInf {r : EReal |
          ∃ (lam : Fin m → ℝ),
            (∀ j, (∑ i, lam i * a i j) = x j) ∧
            (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
              (fun i => lam i)) = 1 ∧
            (∀ i, 0 ≤ lam i) ∧
            r = ((∑ i, lam i * α i : ℝ) : EReal)} := by
          simpa using (hrepr x)
    _ ≤ ((∑ i, lam i * α i : ℝ) : EReal) := sInf_le hmem

/-- Helper for Theorem 19.2: each point-generator value is bounded above by its
coefficient value. -/
lemma helperForTheorem_19_2_generatorValue_le_alpha
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    (i : Fin m)
    (hi : (i : ℕ) < k) :
    f (a i) ≤ (α i : EReal) := by
  classical
  let lam : Fin m → ℝ := fun j => if j = i then 1 else 0
  have hlin : ∀ j, (∑ t, lam t * a t j) = a i j := by
    intro j
    simp [lam]
  have hnorm :
      (Finset.sum (Finset.univ.filter (fun j : Fin m => (j : ℕ) < k))
        (fun j => lam j)) = 1 := by
    have hi_mem : i ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k) := by
      simp [hi]
    simp [lam, hi_mem]
  have hnonneg : ∀ j, 0 ≤ lam j := by
    intro j
    by_cases hji : j = i
    · simp [lam, hji]
    · simp [lam, hji]
  simpa [lam] using
    (helperForTheorem_19_2_value_le_of_feasibleCoefficients
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr
      (x := a i) (lam := lam) hlin hnorm hnonneg)

/-- Helper for Theorem 19.2: a finite upper bound on the conjugate yields the
point-generator inequalities. -/
lemma helperForTheorem_19_2_pointBounds_of_conjugateLe
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hconj : fenchelConjugate n f xStar ≤ (μ : EReal)) :
    ∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ := by
  intro i hi
  have hvalue : f (a i) ≤ (α i : EReal) :=
    helperForTheorem_19_2_generatorValue_le_alpha
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr i hi
  have hAffineAll :
      ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f x :=
    (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μ)).1 hconj
  have hAtA : ((a i ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f (a i) := hAffineAll (a i)
  have hAtA' : ((a i ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ (α i : EReal) := le_trans hAtA hvalue
  have hreal : dotProduct (a i) xStar - μ ≤ α i := by
    exact_mod_cast hAtA'
  linarith

/-- Helper for Theorem 19.2: finite conjugate sublevel bounds imply the two finite
generator inequality families (point and direction). -/
lemma helperForTheorem_19_2_finiteBounds_of_conjugateLe
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hconj : fenchelConjugate n f xStar ≤ (μ : EReal)) :
    (∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ) ∧
      (∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0) := by
  have hpoint : ∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ :=
    helperForTheorem_19_2_pointBounds_of_conjugateLe
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr hconj
  have hdir : ∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0 := by
    have hi0 : ∃ i0 : Fin m, (i0 : ℕ) < k :=
      helperForTheorem_19_2_existsPointIndex_of_posK (k := k) (m := m) hkpos hk
    rcases hi0 with ⟨i0, hi0⟩
    intro i hi
    have hbase : dotProduct (a i0) xStar - α i0 ≤ μ := hpoint i0 hi0
    by_contra hnot
    have hslope_pos : 0 < dotProduct (a i) xStar - α i := lt_of_not_ge hnot
    have hoffset_nonpos : dotProduct (a i0) xStar - α i0 - μ ≤ 0 := by
      linarith
    obtain ⟨t, ht_nonneg, ht_pos⟩ :=
      helperForTheorem_19_1_exists_t_pos_of_neg_offset_pos_slope
        (a := dotProduct (a i0) xStar - α i0 - μ)
        (b := dotProduct (a i) xStar - α i)
        hoffset_nonpos hslope_pos
    have hineq : i ≠ i0 := by
      intro hEq
      have hk_le_i0 : k ≤ (i0 : ℕ) := by simpa [hEq] using hi
      exact (Nat.not_lt_of_ge hk_le_i0) hi0
    let x_t : Fin n → ℝ := a i0 + t • a i
    let lam_t : Fin m → ℝ :=
      fun j => if j = i0 then 1 else if j = i then t else 0
    have hlin_t : ∀ j, (∑ l, lam_t l * a l j) = x_t j := by
      intro j
      have hne : i0 ≠ i := by
        intro hEq
        exact hineq hEq.symm
      have hlam_split : ∀ x : Fin m,
          (if x = i0 then (1 : ℝ) else if x = i then t else 0) =
            (if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0) := by
        intro x
        by_cases hx0 : x = i0
        · subst hx0
          simp [hne]
        · by_cases hxi : x = i
          · subst hxi
            simp [hineq]
          · simp [hx0, hxi]
      calc
        (∑ l, lam_t l * a l j)
            = ∑ x, (((if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0)) * a x j) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [lam_t, hlam_split x]
        _ = ∑ x, ((if x = i0 then (1 : ℝ) else 0) * a x j + (if x = i then t else 0) * a x j) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
        _ = (∑ x, (if x = i0 then (1 : ℝ) else 0) * a x j) +
              (∑ x, (if x = i then t else 0) * a x j) := by
              simp [Finset.sum_add_distrib]
        _ = a i0 j + t * a i j := by
              simp
        _ = x_t j := by
              simp [x_t]
    have hnorm_t :
        (Finset.sum (Finset.univ.filter (fun j : Fin m => (j : ℕ) < k))
          (fun j => lam_t j)) = 1 := by
      let F : Finset (Fin m) :=
        Finset.univ.filter (fun j : Fin m => (j : ℕ) < k)
      have hsum_eq :
          Finset.sum F (fun j => lam_t j) =
            Finset.sum F (fun j => if j = i0 then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hjlt : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
        have hj_ne_i : j ≠ i := by
          have hj_lt_i : (j : ℕ) < (i : ℕ) := lt_of_lt_of_le hjlt hi
          exact fun hji => hj_lt_i.ne (by simp [hji])
        simp [lam_t, hj_ne_i]
      have hi0_mem : i0 ∈ F := by
        simp [F, hi0]
      have hsum_delta : Finset.sum F (fun j => if j = i0 then (1 : ℝ) else 0) = 1 := by
        simp [hi0_mem]
      exact hsum_eq.trans hsum_delta
    have hnonneg_t : ∀ j, 0 ≤ lam_t j := by
      intro j
      by_cases hj0 : j = i0
      · simp [lam_t, hj0]
      · by_cases hji : j = i
        · subst hji
          simp [lam_t, hineq, ht_nonneg]
        · simp [lam_t, hj0, hji]
    have hvalue_t : f x_t ≤ ((∑ j, lam_t j * α j : ℝ) : EReal) :=
      helperForTheorem_19_2_value_le_of_feasibleCoefficients
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hrepr
        (x := x_t) (lam := lam_t) hlin_t hnorm_t hnonneg_t
    have hAffineAll :
        ∀ x : Fin n → ℝ, ((x ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f x :=
      (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μ)).1 hconj
    have hAtXT : ((x_t ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ f x_t := hAffineAll x_t
    have hAtXT' :
        ((x_t ⬝ᵥ xStar - μ : ℝ) : EReal) ≤ ((∑ j, lam_t j * α j : ℝ) : EReal) :=
      le_trans hAtXT hvalue_t
    have hreal : x_t ⬝ᵥ xStar - μ ≤ (∑ j, lam_t j * α j : ℝ) := by
      exact_mod_cast hAtXT'
    have hdot_xt : x_t ⬝ᵥ xStar = dotProduct (a i0) xStar + t * dotProduct (a i) xStar := by
      calc
        x_t ⬝ᵥ xStar = dotProduct (a i0 + t • a i) xStar := by rfl
        _ = dotProduct (a i0) xStar + dotProduct (t • a i) xStar := by
              rw [add_dotProduct]
        _ = dotProduct (a i0) xStar + t * dotProduct (a i) xStar := by
              simp [smul_dotProduct]
    have halpha_lam : (∑ j, lam_t j * α j : ℝ) = α i0 + t * α i := by
      have hne : i0 ≠ i := by
        intro hEq
        exact hineq hEq.symm
      have hlam_split : ∀ x : Fin m,
          (if x = i0 then (1 : ℝ) else if x = i then t else 0) =
            (if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0) := by
        intro x
        by_cases hx0 : x = i0
        · subst hx0
          simp [hne]
        · by_cases hxi : x = i
          · subst hxi
            simp [hineq]
          · simp [hx0, hxi]
      calc
        (∑ j, lam_t j * α j : ℝ)
            = ∑ x, (((if x = i0 then (1 : ℝ) else 0) + (if x = i then t else 0)) * α x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              simp [lam_t, hlam_split x]
        _ = ∑ x, ((if x = i0 then (1 : ℝ) else 0) * α x + (if x = i then t else 0) * α x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
        _ = (∑ x, (if x = i0 then (1 : ℝ) else 0) * α x) +
              (∑ x, (if x = i then t else 0) * α x) := by
              simp [Finset.sum_add_distrib]
        _ = α i0 + t * α i := by
              simp
    have hlinineq :
        dotProduct (a i0) xStar - α i0 - μ + t * (dotProduct (a i) xStar - α i) ≤ 0 := by
      have hreal' :
          dotProduct (a i0) xStar + t * dotProduct (a i) xStar - μ ≤ α i0 + t * α i := by
        simpa [hdot_xt, halpha_lam, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          using hreal
      linarith
    exact (not_le_of_gt ht_pos) hlinineq
  exact ⟨hpoint, hdir⟩

/-- Helper for Theorem 19.2: finite point and direction generator bounds imply the
corresponding finite upper bound for the conjugate. -/
lemma helperForTheorem_19_2_conjugateLe_of_finiteBounds
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ}
    (hpoint : ∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ)
    (hdir : ∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0) :
    fenchelConjugate n f xStar ≤ (μ : EReal) := by
  have _ : 0 < k := hkpos
  have _ : k ≤ m := hk
  refine
    (fenchelConjugate_le_coe_iff_affine_le (n := n) (f := f) (b := xStar) (μ := μ)).2 ?_
  intro x
  rw [hrepr x]
  refine le_sInf ?_
  intro r hr
  rcases hr with ⟨lam, hlin, hnorm, hnonneg, rfl⟩
  let F : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => (i : ℕ) < k)
  have hlin_vec : x = ∑ i, lam i • a i := by
    funext j
    simpa [smul_eq_mul] using (hlin j).symm
  have hdot :
      dotProduct x xStar = ∑ i, lam i * dotProduct (a i) xStar := by
    calc
      dotProduct x xStar = dotProduct xStar x := by simp [dotProduct_comm]
      _ = dotProduct xStar (∑ i, lam i • a i) := by simp [hlin_vec]
      _ = ∑ i, dotProduct xStar (lam i • a i) := by
            simpa using
              (dotProduct_sum (u := xStar) (s := (Finset.univ : Finset (Fin m)))
                (v := fun i => lam i • a i))
      _ = ∑ i, lam i * dotProduct xStar (a i) := by
            simp [dotProduct_smul, smul_eq_mul]
      _ = ∑ i, lam i * dotProduct (a i) xStar := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [dotProduct_comm]
  have hsum_point :
      Finset.sum F (fun i => lam i * (dotProduct (a i) xStar - α i)) ≤
        Finset.sum F (fun i => lam i * μ) := by
    refine Finset.sum_le_sum ?_
    intro i hiF
    exact mul_le_mul_of_nonneg_left
      (hpoint i (Finset.mem_filter.mp hiF).2) (hnonneg i)
  have hsum_dir :
      Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
          (fun i => lam i * (dotProduct (a i) xStar - α i)) ≤ 0 := by
    have hle_each :
        ∀ i ∈ Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k),
          lam i * (dotProduct (a i) xStar - α i) ≤ 0 := by
      intro i hiF
      exact mul_nonpos_of_nonneg_of_nonpos
        (hnonneg i) (hdir i (Nat.not_lt.mp (Finset.mem_filter.mp hiF).2))
    have :
        Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
            (fun i => lam i * (dotProduct (a i) xStar - α i)) ≤
          Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
            (fun _ : Fin m => 0) := by
      refine Finset.sum_le_sum ?_
      intro i hiF
      exact hle_each i hiF
    simpa using this
  have hsum_split :
      (∑ i, lam i * (dotProduct (a i) xStar - α i)) =
        Finset.sum F (fun i => lam i * (dotProduct (a i) xStar - α i)) +
          Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
            (fun i => lam i * (dotProduct (a i) xStar - α i)) := by
    simpa [F] using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun i : Fin m => lam i * (dotProduct (a i) xStar - α i))
        (p := fun i : Fin m => (i : ℕ) < k)).symm
  have hsum_point_mu :
      Finset.sum F (fun i => lam i * μ) = (Finset.sum F (fun i => lam i)) * μ := by
    simpa using (Finset.sum_mul (s := F) (f := fun i : Fin m => lam i) (a := μ)).symm
  have hsum_bound :
      ∑ i, lam i * (dotProduct (a i) xStar - α i) ≤ μ := by
    calc
      ∑ i, lam i * (dotProduct (a i) xStar - α i)
          = Finset.sum F (fun i => lam i * (dotProduct (a i) xStar - α i)) +
              Finset.sum (Finset.univ.filter (fun i : Fin m => ¬ (i : ℕ) < k))
                (fun i => lam i * (dotProduct (a i) xStar - α i)) := hsum_split
      _ ≤ Finset.sum F (fun i => lam i * μ) + 0 := add_le_add hsum_point hsum_dir
      _ = Finset.sum F (fun i => lam i * μ) := by ring
      _ = (Finset.sum F (fun i => lam i)) * μ := hsum_point_mu
      _ = μ := by simp [F, hnorm]
  have hsum_rewrite :
      (∑ i, lam i * (dotProduct (a i) xStar - α i)) =
        (∑ i, lam i * dotProduct (a i) xStar) - (∑ i, lam i * α i) := by
    simp [mul_sub, Finset.sum_sub_distrib]
  have hreal : dotProduct x xStar - μ ≤ (∑ i, lam i * α i : ℝ) := by
    have haux :
        (∑ i, lam i * dotProduct (a i) xStar) - (∑ i, lam i * α i) ≤ μ := by
      simpa [hsum_rewrite] using hsum_bound
    have haux' : dotProduct x xStar - (∑ i, lam i * α i) ≤ μ := by
      simpa [hdot] using haux
    linarith
  exact_mod_cast hreal

/-- Helper for Theorem 19.2: conjugate sublevel membership is equivalent to the two
finite generator-bound families. -/
lemma helperForTheorem_19_2_conjugate_le_iff_finiteGeneratorBounds
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    {xStar : Fin n → ℝ} {μ : ℝ} :
    fenchelConjugate n f xStar ≤ (μ : EReal) ↔
      (∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) xStar - α i ≤ μ) ∧
        (∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) xStar - α i ≤ 0) := by
  constructor
  · intro hconj
    exact
      helperForTheorem_19_2_finiteBounds_of_conjugateLe
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr hconj
  · intro hbounds
    exact
      helperForTheorem_19_2_conjugateLe_of_finiteBounds
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr hbounds.1 hbounds.2

/-- Helper for Theorem 19.2: transformed-epigraph membership is equivalent to the
finite generator-bound families at the pulled-back pair coordinates. -/
lemma helperForTheorem_19_2_memTransformedEpigraphCoord_iff_bounds
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)})
    (y : Fin (n + 1) → ℝ) :
    y ∈ ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) ↔
      (∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2) ∧
        (∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0) := by
  let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hpy⟩
    have hq_eq_p : q = p := by
      dsimp [q]
      calc
        (prodLinearEquiv_append_coord (n := n)).symm y
            = (prodLinearEquiv_append_coord (n := n)).symm
                ((prodLinearEquiv_append_coord (n := n)) p) := by
                  simp [hpy]
        _ = p := by simp
    have hq_epi : q ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      simpa [hq_eq_p] using hp
    have hq_conj : fenchelConjugate n f q.1 ≤ (q.2 : EReal) :=
      (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hq_epi
    have hq_bounds :
        (∀ i : Fin m, (i : ℕ) < k → dotProduct (a i) q.1 - α i ≤ q.2) ∧
          (∀ i : Fin m, k ≤ (i : ℕ) → dotProduct (a i) q.1 - α i ≤ 0) := by
      exact
        (helperForTheorem_19_2_conjugate_le_iff_finiteGeneratorBounds
          (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
          hkpos hk hrepr).1 hq_conj
    simpa [q] using hq_bounds
  · intro hyBounds
    have hq_conj : fenchelConjugate n f q.1 ≤ (q.2 : EReal) := by
      exact
        (helperForTheorem_19_2_conjugate_le_iff_finiteGeneratorBounds
          (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
          hkpos hk hrepr).2 (by simpa [q] using hyBounds)
    have hq_epi : q ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) := by
      exact (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2 hq_conj
    refine ⟨q, hq_epi, ?_⟩
    simp [q]

/-- Helper for Theorem 19.2: packed-coordinate dot products with `(a i, -1)` decode
to the affine expression `dotProduct (a i) x - μ`. -/
lemma helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc
    {n : ℕ} (x0 : Fin n → ℝ) (μ0 : ℝ) (j0 : Fin n) :
    x0 j0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.castSucc j0) := by
  change x0 j0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.castSucc j0)
  change x0 j0 =
    ((appendAffineEquiv n 1).linear
      (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0)
  have happ := congrArg
    (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.castSucc j0))
    (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
  have hlin :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
        (appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
    simpa using congrArg
      (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have happ' :
      ((appendAffineEquiv n 1).linear
        (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0) =
        Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) := by
    simpa [hlin] using happ
  have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) = x0 j0 := by
    exact Fin.append_left (u := x0) (v := Function.const (Fin 1) μ0) j0
  exact (happ'.trans happend).symm

/-- Helper for Theorem 19.2: the last packed coordinate is the appended scalar. -/
lemma helperForTheorem_19_2_prodLinearEquivAppendCoord_last
    {n : ℕ} (x0 : Fin n → ℝ) (μ0 : ℝ) :
    μ0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.last n) := by
  change μ0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.last n)
  change μ0 =
    ((appendAffineEquiv n 1).linear
      (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n)
  have happ := congrArg
    (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.last n))
    (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
  have hlin :
      (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
        (appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
    simpa using congrArg
      (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
  have happ' :
      ((appendAffineEquiv n 1).linear
        (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n) =
        Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) := by
    simpa [hlin] using happ
  have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) = μ0 := by
    change Fin.append x0 (Function.const (Fin 1) μ0) (Fin.natAdd n (0 : Fin 1)) = μ0
    exact Fin.append_right (u := x0) (v := Function.const (Fin 1) μ0) (0 : Fin 1)
  exact (happ'.trans happend).symm

/-- Helper for Theorem 19.2: dot product in packed coordinates splits into the base
dot product plus the product of appended scalar coordinates. -/
lemma helperForTheorem_19_2_dotProduct_prodLinearEquivAppendCoord
    {n : ℕ} (p q : (Fin n → ℝ) × ℝ) :
    dotProduct
      (prodLinearEquiv_append_coord (n := n) p)
      (prodLinearEquiv_append_coord (n := n) q) =
      dotProduct p.1 q.1 + p.2 * q.2 := by
  rcases p with ⟨x, μ⟩
  rcases q with ⟨y, ν⟩
  have hx_cast :
      ∀ j : Fin n,
        (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.castSucc j) = x j := by
    intro j
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc
        (n := n) (x0 := x) (μ0 := μ) (j0 := j)).symm
  have hy_cast :
      ∀ j : Fin n,
        (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.castSucc j) = y j := by
    intro j
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_castSucc
        (n := n) (x0 := y) (μ0 := ν) (j0 := j)).symm
  have hx_last :
      (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.last n) = μ := by
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_last
        (n := n) (x0 := x) (μ0 := μ)).symm
  have hy_last :
      (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.last n) = ν := by
    exact
      (helperForTheorem_19_2_prodLinearEquivAppendCoord_last
        (n := n) (x0 := y) (μ0 := ν)).symm
  calc
    dotProduct
      (prodLinearEquiv_append_coord (n := n) (x, μ))
      (prodLinearEquiv_append_coord (n := n) (y, ν))
        =
          (∑ j : Fin n,
            (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.castSucc j) *
              (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.castSucc j)) +
            (prodLinearEquiv_append_coord (n := n) (x, μ)) (Fin.last n) *
              (prodLinearEquiv_append_coord (n := n) (y, ν)) (Fin.last n) := by
          simp [dotProduct, Fin.sum_univ_castSucc]
    _ = (∑ j : Fin n, x j * y j) + μ * ν := by
          simp [hx_cast, hy_cast, hx_last, hy_last]
    _ = dotProduct x y + μ * ν := by
          simp [dotProduct]

/-- Helper for Theorem 19.2: packed-coordinate dot products with `(a i, -1)` decode
to the affine expression `dotProduct (a i) x - μ`. -/
lemma helperForTheorem_19_2_dotPacked_point
    {n m : ℕ} {a : Fin m → Fin n → ℝ} (i : Fin m)
    (y : Fin (n + 1) → ℝ) :
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) =
      dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
        ((prodLinearEquiv_append_coord (n := n)).symm y).2 := by
  let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
  have hy : prodLinearEquiv_append_coord (n := n) q = y := by
    simp [q]
  calc
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ)))
        = dotProduct (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) y := by
            simp [dotProduct_comm]
    _ = dotProduct
          (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ)))
          (prodLinearEquiv_append_coord (n := n) q) := by
            simp [hy]
    _ = dotProduct (a i) q.1 + (-1 : ℝ) * q.2 := by
          simpa using
            helperForTheorem_19_2_dotProduct_prodLinearEquivAppendCoord
              (n := n) (p := (a i, (-1 : ℝ))) (q := q)
    _ = dotProduct (a i) q.1 - q.2 := by
          ring
    _ = dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
          ((prodLinearEquiv_append_coord (n := n)).symm y).2 := by
            simp [q]

/-- Helper for Theorem 19.2: packed-coordinate dot products with `(a i, 0)` decode
to `dotProduct (a i) x`. -/
lemma helperForTheorem_19_2_dotPacked_direction
    {n m : ℕ} {a : Fin m → Fin n → ℝ} (i : Fin m)
    (y : Fin (n + 1) → ℝ) :
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) =
      dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 := by
  let q : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm y
  have hy : prodLinearEquiv_append_coord (n := n) q = y := by
    simp [q]
  calc
    dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ)))
        = dotProduct (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) y := by
            simp [dotProduct_comm]
    _ = dotProduct
          (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ)))
          (prodLinearEquiv_append_coord (n := n) q) := by
            simp [hy]
    _ = dotProduct (a i) q.1 + (0 : ℝ) * q.2 := by
          simpa using
            helperForTheorem_19_2_dotProduct_prodLinearEquivAppendCoord
              (n := n) (p := (a i, (0 : ℝ))) (q := q)
    _ = dotProduct (a i) q.1 := by
          ring
    _ = dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 := by
          simp [q]

/-- Helper for Theorem 19.2: the point-generator bound family in transformed
coordinates is a polyhedral convex set. -/
lemma helperForTheorem_19_2_pointBoundsCoord_polyhedral
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} :
    IsPolyhedralConvexSet (n + 1)
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2} := by
  let aEq : Fin 0 → Fin (n + 1) → ℝ := Fin.elim0
  let αEq : Fin 0 → ℝ := Fin.elim0
  let bIneq : Fin m → Fin (n + 1) → ℝ :=
    fun i =>
      if (i : ℕ) < k then
        prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))
      else 0
  let βIneq : Fin m → ℝ := fun i => if (i : ℕ) < k then α i else 0
  have hpoly_system :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    simpa [βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        (n + 1) 0 m aEq αEq bIneq βIneq)
  have hset :
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2} =
      {y : Fin (n + 1) → ℝ |
        (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
        (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · intro t
        exact Fin.elim0 t
      · intro i
        by_cases hi : (i : ℕ) < k
        · have hbound :
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2 := hy i hi
          have hdecoded :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) =
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
                  ((prodLinearEquiv_append_coord (n := n)).symm y).2 :=
            helperForTheorem_19_2_dotPacked_point (n := n) (m := m) (a := a) i y
          have hbound' :
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
                  ((prodLinearEquiv_append_coord (n := n)).symm y).2 ≤ α i := by
            linarith
          have hdot :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) ≤ α i := by
            simpa [hdecoded] using hbound'
          simpa [bIneq, βIneq, hi] using hdot
        · simp [bIneq, βIneq, hi]
    · intro hy i hi
      have hineq : dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) ≤ α i := by
        have hyi := hy.2 i
        simpa [bIneq, βIneq, hi] using hyi
      have hdecoded :
          dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (-1 : ℝ))) =
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
              ((prodLinearEquiv_append_coord (n := n)).symm y).2 :=
        helperForTheorem_19_2_dotPacked_point (n := n) (m := m) (a := a) i y
      have hineq' :
          dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 -
            ((prodLinearEquiv_append_coord (n := n)).symm y).2 ≤ α i := by
        simpa [hdecoded] using hineq
      linarith
  have hpoly_target :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} := by
    have hpoly_system' :
        IsPolyhedralConvexSet (n + 1)
          {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      simpa [aEq, αEq] using hpoly_system
    have hset' :
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} =
        {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      calc
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2}
            =
          {y : Fin (n + 1) → ℝ |
            (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
            (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := hset
        _ = {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
            ext y
            simp [aEq, αEq]
    exact hset'.symm ▸ hpoly_system'
  exact hpoly_target

/-- Helper for Theorem 19.2: the direction-generator bound family in transformed
coordinates is a polyhedral convex set. -/
lemma helperForTheorem_19_2_directionBoundsCoord_polyhedral
    {n k m : ℕ} {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ} :
    IsPolyhedralConvexSet (n + 1)
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} := by
  let aEq : Fin 0 → Fin (n + 1) → ℝ := Fin.elim0
  let αEq : Fin 0 → ℝ := Fin.elim0
  let bIneq : Fin m → Fin (n + 1) → ℝ :=
    fun i =>
      if k ≤ (i : ℕ) then
        prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))
      else 0
  let βIneq : Fin m → ℝ := fun i => if k ≤ (i : ℕ) then α i else 0
  have hpoly_system :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
          (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    simpa [βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        (n + 1) 0 m aEq αEq bIneq βIneq)
  have hset :
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} =
      {y : Fin (n + 1) → ℝ |
        (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
        (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := by
    ext y
    constructor
    · intro hy
      refine ⟨?_, ?_⟩
      · intro t
        exact Fin.elim0 t
      · intro i
        by_cases hi : k ≤ (i : ℕ)
        · have hbound :
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0 := hy i hi
          have hdecoded :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) =
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 :=
            helperForTheorem_19_2_dotPacked_direction (n := n) (m := m) (a := a) i y
          have hbound' :
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 ≤ α i := by
            linarith
          have hdot :
              dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) ≤ α i := by
            simpa [hdecoded] using hbound'
          simpa [bIneq, βIneq, hi] using hdot
        · simp [bIneq, βIneq, hi]
    · intro hy i hi
      have hineq : dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) ≤ α i := by
        have hyi := hy.2 i
        simpa [bIneq, βIneq, hi] using hyi
      have hdecoded :
          dotProduct y (prodLinearEquiv_append_coord (n := n) (a i, (0 : ℝ))) =
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 :=
        helperForTheorem_19_2_dotPacked_direction (n := n) (m := m) (a := a) i y
      have hineq' :
          dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 ≤ α i := by
        simpa [hdecoded] using hineq
      linarith
  have hpoly_target :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} := by
    have hpoly_system' :
        IsPolyhedralConvexSet (n + 1)
          {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      simpa [aEq, αEq] using hpoly_system
    have hset' :
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} =
        {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
      calc
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}
            =
          {y : Fin (n + 1) → ℝ |
            (∀ t, y ⬝ᵥ aEq t = αEq t) ∧
            (∀ i, y ⬝ᵥ bIneq i ≤ βIneq i)} := hset
        _ = {y : Fin (n + 1) → ℝ | ∀ i, y ⬝ᵥ bIneq i ≤ βIneq i} := by
            ext y
            simp [aEq, αEq]
    exact hset'.symm ▸ hpoly_system'
  exact hpoly_target

/-- Helper for Theorem 19.2: the transformed epigraph of the conjugate equals the
intersection of the point- and direction-bound coordinate sets. -/
lemma helperForTheorem_19_2_transformedEpigraphCoord_eq_pointDirInter
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
      ({y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          (i : ℕ) < k →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
              ((prodLinearEquiv_append_coord (n := n)).symm y).2} ∩
      {y : Fin (n + 1) → ℝ |
        ∀ i : Fin m,
          k ≤ (i : ℕ) →
            dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}) := by
  ext y
  constructor
  · intro hy
    have hyBounds :=
      (helperForTheorem_19_2_memTransformedEpigraphCoord_iff_bounds
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr y).1 hy
    exact ⟨hyBounds.1, hyBounds.2⟩
  · intro hy
    exact
      (helperForTheorem_19_2_memTransformedEpigraphCoord_iff_bounds
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
        hkpos hk hrepr y).2 ⟨hy.1, hy.2⟩

/-- Helper for Theorem 19.2: in the nondegenerate branch, the transformed epigraph of
the conjugate is polyhedral. -/
lemma helperForTheorem_19_2_polyhedralTransformedEpigraph_of_conjugate
    {n k m : ℕ} {f : (Fin n → ℝ) → EReal}
    {a : Fin m → Fin n → ℝ} {α : Fin m → ℝ}
    (hkpos : 0 < k)
    (hk : k ≤ m)
    (hrepr :
      ∀ x,
        f x =
          sInf {r : EReal |
            ∃ (lam : Fin m → ℝ),
              (∀ j, (∑ i, lam i * a i j) = x j) ∧
              (Finset.sum (Finset.univ.filter (fun i : Fin m => (i : ℕ) < k))
                (fun i => lam i)) = 1 ∧
              (∀ i, 0 ≤ lam i) ∧
              r = ((∑ i, lam i * α i : ℝ) : EReal)}) :
    IsPolyhedralConvexSet (n + 1)
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
  have hpoint :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} :=
    helperForTheorem_19_2_pointBoundsCoord_polyhedral
      (n := n) (k := k) (m := m) (a := a) (α := α)
  have hdir :
      IsPolyhedralConvexSet (n + 1)
        {y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            k ≤ (i : ℕ) →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0} :=
    helperForTheorem_19_2_directionBoundsCoord_polyhedral
      (n := n) (k := k) (m := m) (a := a) (α := α)
  have hinter :
      IsPolyhedralConvexSet (n + 1)
        ({y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} ∩
          {y : Fin (n + 1) → ℝ |
            ∀ i : Fin m,
              k ≤ (i : ℕ) →
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}) := by
    exact helperForTheorem_19_1_polyhedral_inter hpoint hdir
  have hEq :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
        ({y : Fin (n + 1) → ℝ |
          ∀ i : Fin m,
            (i : ℕ) < k →
              dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤
                ((prodLinearEquiv_append_coord (n := n)).symm y).2} ∩
          {y : Fin (n + 1) → ℝ |
            ∀ i : Fin m,
              k ≤ (i : ℕ) →
                dotProduct (a i) ((prodLinearEquiv_append_coord (n := n)).symm y).1 - α i ≤ 0}) :=
    helperForTheorem_19_2_transformedEpigraphCoord_eq_pointDirInter
      (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
      hkpos hk hrepr
  simpa [hEq] using hinter

/-- Theorem 19.2: The conjugate of a polyhedral convex function is polyhedral. -/
theorem polyhedralConvexFunction_fenchelConjugate (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f →
      IsPolyhedralConvexFunction n (fenchelConjugate n f) := by
  intro hfpoly
  rcases
    helperForTheorem_19_2_extractFiniteRepresentation
      (n := n) (f := f) hfpoly with
    ⟨k, m, a, α, hk, hrepr⟩
  by_cases hk0 : k = 0
  · have hconj : fenchelConjugate n f = constNegInf n :=
      helperForTheorem_19_2_kZero_forces_constTop_and_conjugate_constNegInf
        (n := n) (k := k) (m := m) (f := f) (a := a) (α := α) hk0 hrepr
    simpa [hconj] using
      helperForTheorem_19_2_constNegInf_isPolyhedralConvexFunction (n := n)
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    refine ⟨?_, ?_⟩
    · have hconv : ConvexFunction (fenchelConjugate n f) :=
        (fenchelConjugate_closedConvex (n := n) (f := f)).2
      simpa [ConvexFunction] using hconv
    · have hpoly_coord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
        exact
          helperForTheorem_19_2_polyhedralTransformedEpigraph_of_conjugate
            (n := n) (k := k) (m := m) (f := f) (a := a) (α := α)
            hkpos hk hrepr
      simpa [prodLinearEquiv_append_coord] using hpoly_coord

/-- Helper for Corollary 19.2.1: a polyhedral set yields a polyhedral indicator function
via the max-affine-plus-indicator representation with `k = 0`. -/
lemma helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexFunction n (indicatorFunction C) := by
  rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).1 hCpoly with
    ⟨m, b, β, hCeq⟩
  have hrepr :
      ∃ (k m : ℕ) (b : Fin m → Fin n → ℝ) (β : Fin m → ℝ),
        k ≤ m ∧
          indicatorFunction C =
            (fun x =>
              ((sSup {r : ℝ |
                  ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
                indicatorFunction
                  (C := {y | ∀ i : Fin m, k ≤ (i : ℕ) →
                    (∑ j, y j * b i j) ≤ β i})
                  x) := by
    refine ⟨0, m, b, β, Nat.zero_le m, ?_⟩
    funext x
    let D : Set (Fin n → ℝ) :=
      {y | ∀ i : Fin m, (0 : ℕ) ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
    have hD : D = C := by
      calc
        D = {y : Fin n → ℝ | ∀ i : Fin m, (∑ j, y j * b i j) ≤ β i} := by
              ext y
              simp [D]
        _ = ⋂ i, closedHalfSpaceLE n (b i) (β i) := by
              ext y
              simp [closedHalfSpaceLE, dotProduct]
        _ = C := by
              exact hCeq.symm
    have hSupZero :
        (sSup {r : ℝ |
          ∃ i : Fin m, (i : ℕ) < 0 ∧ r = (∑ j, x j * b i j) - β i} : ℝ) = 0 := by
      simp
    calc
      indicatorFunction C x = indicatorFunction (C := D) x := by
        simp [hD]
      _ = (0 : EReal) + indicatorFunction (C := D) x := by
        simp
      _ =
          ((sSup {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < 0 ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x := by
        simp
  exact
    ((polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := indicatorFunction C)).2 hrepr).1

/-- Helper for Corollary 19.2.1: an equality between an indicator and a max-affine-plus-
indicator representation forces equality of the underlying sets. -/
lemma helperForCorollary_19_2_1_indicatorRepresentation_forces_setEquality
    {n k m : ℕ} {C D : Set (Fin n → ℝ)}
    {b : Fin m → Fin n → ℝ} {β : Fin m → ℝ}
    (hrepr :
      indicatorFunction C =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x) :
    C = D := by
  ext x
  constructor
  · intro hxC
    by_contra hxD
    have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
    have hzero_top : (0 : EReal) = (⊤ : EReal) := by
      calc
        (0 : EReal) = indicatorFunction C x := by
          simp [indicatorFunction, hxC]
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x := hreprx
        _ = (⊤ : EReal) := by
          simp [indicatorFunction, hxD]
    have hzero_ne_top : (0 : EReal) ≠ (⊤ : EReal) := by
      simp
    exact hzero_ne_top hzero_top
  · intro hxD
    by_contra hxC
    have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hrepr
    have htop_coe :
        (⊤ : EReal) =
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
      calc
        (⊤ : EReal) = indicatorFunction C x := by
          simp [indicatorFunction, hxC]
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x := hreprx
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
              simp [indicatorFunction, hxD]
    exact (EReal.coe_ne_top _) htop_coe.symm

/-- Helper for Corollary 19.2.1: if the indicator function is polyhedral, then the set is
polyhedral. -/
lemma helperForCorollary_19_2_1_polyhedralSet_of_indicatorPolyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hIndicatorPoly : IsPolyhedralConvexFunction n (indicatorFunction C)) :
    IsPolyhedralConvexSet n C := by
  have hIndicatorNonbot :
      ∀ x : Fin n → ℝ, indicatorFunction C x ≠ (⊥ : EReal) := by
    intro x
    by_cases hx : x ∈ C <;> simp [indicatorFunction, hx]
  rcases
    (polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := indicatorFunction C)).1 ⟨hIndicatorPoly, hIndicatorNonbot⟩ with
    ⟨k, m, b, β, hk, hrepr⟩
  let D : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  have hreprD :
      indicatorFunction C =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x := by
    simpa [D] using hrepr
  have hCD : C = D :=
    helperForCorollary_19_2_1_indicatorRepresentation_forces_setEquality
      (C := C) (D := D) (b := b) (β := β) hreprD
  have hDpoly : IsPolyhedralConvexSet n D := by
    refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n D).2 ?_
    let b' : Fin m → Fin n → ℝ := fun i => if k ≤ (i : ℕ) then b i else 0
    let β' : Fin m → ℝ := fun i => if k ≤ (i : ℕ) then β i else 0
    refine ⟨m, b', β', ?_⟩
    ext y
    constructor
    · intro hy
      refine Set.mem_iInter.mpr ?_
      intro i
      by_cases hki : k ≤ (i : ℕ)
      · have hyi : (∑ j, y j * b i j) ≤ β i := hy i hki
        simpa [closedHalfSpaceLE, b', β', hki] using hyi
      · simp [closedHalfSpaceLE, b', β', hki]
    · intro hy i hki
      have hmem : y ∈ closedHalfSpaceLE n (b' i) (β' i) :=
        Set.mem_iInter.mp hy i
      simpa [closedHalfSpaceLE, b', β', hki] using hmem
  simpa [hCD] using hDpoly

/-- Helper for Corollary 19.2.1: a closed convex polyhedral set has a polyhedral
support function. -/
lemma helperForCorollary_19_2_1_supportFunctionPolyhedral_of_polyhedralSet
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hClosed : IsClosed C) (hConv : Convex ℝ C)
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexFunction n (supportFunctionEReal C) := by
  have hIndicatorPoly : IsPolyhedralConvexFunction n (indicatorFunction C) :=
    helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
      (n := n) (C := C) hCpoly
  have hConjPoly :
      IsPolyhedralConvexFunction n (fenchelConjugate n (indicatorFunction C)) :=
    polyhedralConvexFunction_fenchelConjugate
      (n := n) (f := indicatorFunction C) hIndicatorPoly
  have hConjEq :
      fenchelConjugate n (indicatorFunction C) = supportFunctionEReal C :=
    (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
      (C := C) hConv hClosed).1
  simpa [hConjEq] using hConjPoly

/-- Helper for Corollary 19.2.1: if the support function is polyhedral, then the closed
convex set is polyhedral. -/
lemma helperForCorollary_19_2_1_polyhedralSet_of_supportFunctionPolyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hClosed : IsClosed C) (hConv : Convex ℝ C)
    (hSupportPoly : IsPolyhedralConvexFunction n (supportFunctionEReal C)) :
    IsPolyhedralConvexSet n C := by
  have hConjPoly :
      IsPolyhedralConvexFunction n (fenchelConjugate n (supportFunctionEReal C)) :=
    polyhedralConvexFunction_fenchelConjugate
      (n := n) (f := supportFunctionEReal C) hSupportPoly
  have hConjEq :
      fenchelConjugate n (supportFunctionEReal C) = indicatorFunction C :=
    (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
      (C := C) hConv hClosed).2
  have hIndicatorPoly : IsPolyhedralConvexFunction n (indicatorFunction C) := by
    simpa [hConjEq] using hConjPoly
  exact
    helperForCorollary_19_2_1_polyhedralSet_of_indicatorPolyhedral
      (n := n) (C := C) hIndicatorPoly

/-- Corollary 19.2.1: A closed convex set `C` is polyhedral iff its support function
`δ^*(· | C)` is polyhedral. -/
theorem polyhedral_convexSet_iff_supportFunction_polyhedral
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsClosed C → Convex ℝ C →
      (IsPolyhedralConvexSet n C ↔
        IsPolyhedralConvexFunction n (supportFunctionEReal C)) := by
  intro hClosed hConv
  constructor
  · intro hCpoly
    exact
      helperForCorollary_19_2_1_supportFunctionPolyhedral_of_polyhedralSet
        (n := n) (C := C) hClosed hConv hCpoly
  · intro hSupportPoly
    exact
      helperForCorollary_19_2_1_polyhedralSet_of_supportFunctionPolyhedral
        (n := n) (C := C) hClosed hConv hSupportPoly

/-- Helper for Corollary 19.2.2: a polyhedral convex set has a polyhedral support
function. -/
lemma helperForCorollary_19_2_2_supportFunction_polyhedral_of_polyhedralSet
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexFunction n (supportFunctionEReal C) := by
  have hClosedC : IsClosed C :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n) (C := C) hCpoly).1
  have hConvC : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  exact
    (polyhedral_convexSet_iff_supportFunction_polyhedral (n := n) (C := C)
      hClosedC hConvC).1 hCpoly

/-- Helper for Corollary 19.2.2: the element `(1 : EReal)` is not top. -/
lemma helperForCorollary_19_2_2_one_ne_top :
    (1 : EReal) ≠ (⊤ : EReal) := by
  simpa using (EReal.coe_ne_top (1 : ℝ))

/-- Corollary 19.2.2: The polar of a polyhedral convex set is polyhedral. -/
theorem polyhedral_convexSet_polar_polyhedral
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet n
        {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} := by
  intro hCpoly
  by_cases hCempty : C = ∅
  · subst hCempty
    have hSetEqUniv :
        {xStar : Fin n → ℝ | supportFunctionEReal (∅ : Set (Fin n → ℝ)) xStar ≤ (1 : EReal)} =
          (Set.univ : Set (Fin n → ℝ)) := by
      ext xStar
      simp [supportFunctionEReal]
    classical
    let ι : Type := PEmpty
    let b : ι → Fin n → ℝ := fun i => nomatch i
    let β : ι → ℝ := fun i => nomatch i
    have hPolyUniv : IsPolyhedralConvexSet n (Set.univ : Set (Fin n → ℝ)) := by
      refine ⟨ι, inferInstance, b, β, ?_⟩
      ext x
      simp [closedHalfSpaceLE, b, β]
    simpa [hSetEqUniv] using hPolyUniv
  have hCne : C.Nonempty := Set.nonempty_iff_ne_empty.mpr hCempty
  have hConvC : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hSupportPoly : IsPolyhedralConvexFunction n (supportFunctionEReal C) :=
    helperForCorollary_19_2_2_supportFunction_polyhedral_of_polyhedralSet
      (n := n) (C := C) hCpoly
  have hSupportNonbot :
      ∀ xStar : Fin n → ℝ, supportFunctionEReal C xStar ≠ (⊥ : EReal) :=
    section13_supportFunctionEReal_ne_bot (n := n) (C := C) hCne hConvC
  rcases
    (polyhedral_convex_function_iff_max_affine_plus_indicator
      (n := n) (f := supportFunctionEReal C)).1 ⟨hSupportPoly, hSupportNonbot⟩ with
    ⟨k, m, b, β, hk, hrepr⟩
  let D : Set (Fin n → ℝ) :=
    {y | ∀ i : Fin m, k ≤ (i : ℕ) → (∑ j, y j * b i j) ≤ β i}
  have hreprD :
      supportFunctionEReal C =
        fun x =>
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
            indicatorFunction (C := D) x := by
    simpa [D] using hrepr
  let P : Set (Fin n → ℝ) :=
    {x | ∀ i : Fin m, (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i)}
  have hSetEq :
      {xStar | supportFunctionEReal C xStar ≤ (1 : EReal)} = P := by
    ext x
    constructor
    · intro hx
      have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hreprD
      have hx_main :
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x ≤ (1 : EReal) := by
        simpa [hreprx] using hx
      have hxD : x ∈ D := by
        by_contra hxD
        have htop_le_one : (⊤ : EReal) ≤ (1 : EReal) := by
          simpa [indicatorFunction, hxD] using hx_main
        have hone_top : (1 : EReal) = ⊤ := top_le_iff.mp htop_le_one
        exact helperForCorollary_19_2_2_one_ne_top hone_top
      intro i
      by_cases hki : (i : ℕ) < k
      · have hsup_le_one :
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) ≤
            (1 : EReal) := by
          simpa [indicatorFunction, hxD] using hx_main
        have hsup_real_le_one :
            sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} ≤ 1 := by
          exact_mod_cast hsup_le_one
        let S : Set ℝ :=
          {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
        have hSfinite : S.Finite := by
          refine (Set.finite_range (fun i : Fin m => (∑ j, x j * b i j) - β i)).subset ?_
          intro r hr
          rcases hr with ⟨i, hki', rfl⟩
          exact ⟨i, rfl⟩
        have hSbdd : BddAbove S := hSfinite.bddAbove
        have hbound_all : ∀ r : ℝ, r ∈ S → r ≤ 1 := by
          intro r hr
          exact le_trans (le_csSup hSbdd hr) hsup_real_le_one
        have hbound_i : (∑ j, x j * b i j) - β i ≤ 1 := by
          exact hbound_all _ ⟨i, hki, rfl⟩
        have hbound_i' : (∑ j, x j * b i j) ≤ β i + 1 := by
          linarith
        simpa [hki] using hbound_i'
      · have hki_ge : k ≤ (i : ℕ) := Nat.le_of_not_lt hki
        have hbound_i : (∑ j, x j * b i j) ≤ β i := hxD i hki_ge
        simpa [hki] using hbound_i
    · intro hxP
      have hreprx := congrArg (fun g : (Fin n → ℝ) → EReal => g x) hreprD
      have hxD : x ∈ D := by
        intro i hki_ge
        have hxi : (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i) := hxP i
        have hki_not : ¬ (i : ℕ) < k := Nat.not_lt.mpr hki_ge
        simpa [hki_not] using hxi
      have hsup_real_le_one :
          sSup {r : ℝ |
            ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} ≤ 1 := by
        let S : Set ℝ :=
          {r : ℝ | ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i}
        have hs : ∀ r : ℝ, r ∈ S → r ≤ 1 := by
          intro r hr
          rcases hr with ⟨i, hki, rfl⟩
          have hxi : (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i) := hxP i
          have hxi' : (∑ j, x j * b i j) ≤ β i + 1 := by
            simpa [hki] using hxi
          linarith
        by_cases hS : S.Nonempty
        · exact csSup_le hS hs
        · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS
          simp [S, hS_empty]
      have hsup_le_one :
          ((sSup {r : ℝ |
              ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) ≤
            (1 : EReal) := by
        exact_mod_cast hsup_real_le_one
      calc
        supportFunctionEReal C x =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction (C := D) x := hreprx
        _ =
            ((sSup {r : ℝ |
                ∃ i : Fin m, (i : ℕ) < k ∧ r = (∑ j, x j * b i j) - β i} : ℝ) : EReal) := by
              simp [indicatorFunction, hxD]
        _ ≤ (1 : EReal) := hsup_le_one
  have hPpoly : IsPolyhedralConvexSet n P := by
    refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n P).2 ?_
    refine ⟨m, b, (fun i => if (i : ℕ) < k then β i + 1 else β i), ?_⟩
    ext x
    constructor
    · intro hx
      refine Set.mem_iInter.mpr ?_
      intro i
      have hxi : (∑ j, x j * b i j) ≤ (if (i : ℕ) < k then β i + 1 else β i) := hx i
      simpa [closedHalfSpaceLE] using hxi
    · intro hx i
      have hmem : x ∈
          closedHalfSpaceLE n (b i) (if (i : ℕ) < k then β i + 1 else β i) :=
        Set.mem_iInter.mp hx i
      simpa [closedHalfSpaceLE] using hmem
  simpa [hSetEq, P] using hPpoly

/-- Helper for Theorem 19.3: linear images of polyhedral convex sets are finitely generated. -/
lemma helperForTheorem_19_3_image_finitelyGenerated_of_polyhedral
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsFinitelyGeneratedConvexSet m (A '' C) := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
        (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  have hCfg : IsFinitelyGeneratedConvexSet n C :=
    (hTFAE.out 0 2).1 hCpoly
  exact
    helperForCorollary_19_1_2_linearImage_finitelyGeneratedSet
      (n := n) (p := m) (C := C) hCfg A

/-- Helper for Theorem 19.3: linear images of polyhedral convex sets are polyhedral. -/
lemma helperForTheorem_19_3_image_polyhedral_of_polyhedral
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet m (A '' C) := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hImageConv : Convex ℝ (A '' C) := hCconv.linear_image A
  have hImageFG : IsFinitelyGeneratedConvexSet m (A '' C) :=
    helperForTheorem_19_3_image_finitelyGenerated_of_polyhedral (A := A) (C := C) hCpoly
  exact
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := m) (C := A '' C) hImageConv hImageFG

/-- Helper for Theorem 19.3: the preimage of one closed half-space under `A` is the
corresponding closed half-space with normal transformed by the transpose matrix of `A`. -/
lemma helperForTheorem_19_3_preimage_closedHalfSpaceLE_eq
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (b : Fin m → ℝ) (β : ℝ) :
    A ⁻¹' (closedHalfSpaceLE m b β) =
      closedHalfSpaceLE n
        (((LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))) A).transpose.mulVec b)
        β := by
  let M : Matrix (Fin m) (Fin n) ℝ :=
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))) A
  ext x
  have hAx : A x = M.mulVec x := by
    have hrepr :=
      LinearMap.toMatrix_mulVec_repr (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m)) A x
    ext i
    have hrepr_i := congrArg (fun v : Fin m → ℝ => v i) hrepr
    simpa [M, Pi.basisFun_repr] using hrepr_i.symm
  have hvec : Matrix.vecMul b M = M.transpose.mulVec b := by
    simpa using (Matrix.mulVec_transpose (A := M) (x := b)).symm
  have hdot :
      dotProduct (A x) b = dotProduct x (M.transpose.mulVec b) := by
    calc
      dotProduct (A x) b = dotProduct (M.mulVec x) b := by simp [hAx]
      _ = b ⬝ᵥ M.mulVec x := by simp [dotProduct_comm]
      _ = Matrix.vecMul b M ⬝ᵥ x := Matrix.dotProduct_mulVec b M x
      _ = M.transpose.mulVec b ⬝ᵥ x := by simp [hvec]
      _ = dotProduct x (M.transpose.mulVec b) := by simp [dotProduct_comm]
  constructor
  · intro hx
    have hAxLe : dotProduct (A x) b ≤ β := by
      simpa [closedHalfSpaceLE] using hx
    have hxLe : dotProduct x (M.transpose.mulVec b) ≤ β := by
      simpa [hdot] using hAxLe
    simpa [closedHalfSpaceLE, M] using hxLe
  · intro hx
    have hxLe : dotProduct x (M.transpose.mulVec b) ≤ β := by
      simpa [closedHalfSpaceLE, M] using hx
    have hAxLe : dotProduct (A x) b ≤ β := by
      simpa [hdot] using hxLe
    simpa [closedHalfSpaceLE] using hAxLe

/-- Helper for Theorem 19.3: linear preimages of polyhedral convex sets are polyhedral. -/
lemma helperForTheorem_19_3_preimage_polyhedral_of_polyhedral
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {D : Set (Fin m → ℝ)}
    (hDpoly : IsPolyhedralConvexSet m D) :
    IsPolyhedralConvexSet n (A ⁻¹' D) := by
  let M : Matrix (Fin m) (Fin n) ℝ :=
    (LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin m))) A
  rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces m D).1 hDpoly with
    ⟨k, b, β, hD⟩
  refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces n (A ⁻¹' D)).2 ?_
  refine ⟨k, (fun i => M.transpose.mulVec (b i)), β, ?_⟩
  ext x
  constructor
  · intro hx
    have hAx_mem : A x ∈ D := hx
    have hAxInter : A x ∈ ⋂ i, closedHalfSpaceLE m (b i) (β i) := by
      simpa [hD] using hAx_mem
    refine Set.mem_iInter.mpr ?_
    intro i
    have hAx_i : A x ∈ closedHalfSpaceLE m (b i) (β i) :=
      Set.mem_iInter.mp hAxInter i
    have hx_pre : x ∈ A ⁻¹' (closedHalfSpaceLE m (b i) (β i)) := hAx_i
    simpa [M, helperForTheorem_19_3_preimage_closedHalfSpaceLE_eq (A := A) (b := b i) (β := β i)]
      using hx_pre
  · intro hx
    have hxInter : x ∈ ⋂ i, closedHalfSpaceLE n (M.transpose.mulVec (b i)) (β i) := hx
    have hAxInter : A x ∈ ⋂ i, closedHalfSpaceLE m (b i) (β i) := by
      refine Set.mem_iInter.mpr ?_
      intro i
      have hx_i : x ∈ closedHalfSpaceLE n (M.transpose.mulVec (b i)) (β i) :=
        Set.mem_iInter.mp hxInter i
      have hx_pre : x ∈ A ⁻¹' (closedHalfSpaceLE m (b i) (β i)) := by
        simpa
          [M, helperForTheorem_19_3_preimage_closedHalfSpaceLE_eq (A := A) (b := b i) (β := β i)]
          using hx_i
      exact hx_pre
    change A x ∈ D
    simpa [hD] using hAxInter

/-- Helper for Theorem 19.3: for a fixed linear map, both the image-preservation and
preimage-preservation polyhedrality statements hold together. -/
lemma helperForTheorem_19_3_image_and_preimage_polyhedral
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet m (A '' C)) ∧
      (∀ D : Set (Fin m → ℝ), IsPolyhedralConvexSet m D →
        IsPolyhedralConvexSet n (A ⁻¹' D)) := by
  constructor
  · intro C hCpoly
    exact helperForTheorem_19_3_image_polyhedral_of_polyhedral (A := A) (C := C) hCpoly
  · intro D hDpoly
    exact
      helperForTheorem_19_3_preimage_polyhedral_of_polyhedral (A := A) (D := D) hDpoly

/-- Theorem 19.3: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. Then `A '' C` is a
polyhedral convex set in `ℝ^m` for each polyhedral convex set `C` in `ℝ^n`, and `A ⁻¹' D` is a
polyhedral convex set in `ℝ^n` for each polyhedral convex set `D` in `ℝ^m`. -/
theorem polyhedralConvexSet_image_preimage_linear
    (n m : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ C : Set (Fin n → ℝ), IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet m (A '' C)) ∧
      (∀ D : Set (Fin m → ℝ), IsPolyhedralConvexSet m D →
        IsPolyhedralConvexSet n (A ⁻¹' D)) := by
  exact helperForTheorem_19_3_image_and_preimage_polyhedral (A := A)

/-- Helper for Corollary 19.3.1: coordinate conjugate of `linearMap_prod A` between
`Fin`-function models of product spaces. -/
noncomputable def helperForCorollary_19_3_1_linearMapProdCoord
    {n m : ℕ} (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) :=
  ((prodLinearEquiv_append_coord (n := m)).toLinearMap).comp
    ((linearMap_prod A).comp ((prodLinearEquiv_append_coord (n := n)).symm.toLinearMap))

/-- Helper for Corollary 19.3.1: after converting product points to `Fin` coordinates, the
image under `linearMap_prod A` is exactly the image under the conjugated map. -/
lemma helperForCorollary_19_3_1_image_linearMapProdCoord
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)}
    {S : Set ((Fin n → ℝ) × ℝ)} :
    ((fun p => prodLinearEquiv_append_coord (n := m) p) '' ((linearMap_prod A) '' S)) =
      (helperForCorollary_19_3_1_linearMapProdCoord A) ''
        ((fun p => prodLinearEquiv_append_coord (n := n) p) '' S) := by
  ext y
  constructor
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(prodLinearEquiv_append_coord (n := n)) x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply]
  · rintro ⟨p, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨linearMap_prod A x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp [helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply]

/-- Helper for Corollary 19.3.1: in `Fin` coordinates, the epigraph of
`inverseImageUnderLinearMap A g` is the preimage of the transformed epigraph of `g` under the
conjugated product map. -/
lemma helperForCorollary_19_3_1_transformedEpigraphCoord_inverseImage_eq_preimage
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {g : (Fin m → ℝ) → EReal} :
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g)) =
      (helperForCorollary_19_3_1_linearMapProdCoord A) ⁻¹'
        ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
          epigraph (Set.univ : Set (Fin m → ℝ)) g) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨x, μ⟩
    have hxle : g (A x) ≤ (μ : EReal) := by
      simpa [inverseImageUnderLinearMap] using
        (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).1 hp
    refine ⟨(A x, μ), ?_, ?_⟩
    · exact (mem_epigraph_univ_iff (f := g)).2 hxle
    · simp [helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply, linearMap_prod]
  · intro hz
    let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm z
    have hz' :
        helperForCorollary_19_3_1_linearMapProdCoord A z ∈
          (fun q => prodLinearEquiv_append_coord (n := m) q) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      exact hz
    have hlin_epi : linearMap_prod A p ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      rcases hz' with ⟨q, hq, hqeq⟩
      have hqeq' : q = linearMap_prod A p := by
        apply (prodLinearEquiv_append_coord (n := m)).injective
        calc
          (prodLinearEquiv_append_coord (n := m)) q
              = helperForCorollary_19_3_1_linearMapProdCoord A z := hqeq
          _ = (prodLinearEquiv_append_coord (n := m)) (linearMap_prod A p) := by
                simp [p, helperForCorollary_19_3_1_linearMapProdCoord, LinearMap.comp_apply]
      simpa [hqeq'] using hq
    have hp_epi : p ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g) := by
      rcases p with ⟨x, μ⟩
      have hAx_epi : (A x, μ) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
        simpa [linearMap_prod] using hlin_epi
      have hxle : g (A x) ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := g)).1 hAx_epi
      have hxle' : inverseImageUnderLinearMap A g x ≤ (μ : EReal) := by
        simpa [inverseImageUnderLinearMap] using hxle
      exact (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).2 hxle'
    refine ⟨p, hp_epi, ?_⟩
    simp [p]

/-- Helper for Corollary 19.3.1: the projected epigraph of a polyhedral convex function under
`linearMap_prod A` is closed. -/
lemma helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  let Acoord := helperForCorollary_19_3_1_linearMapProdCoord (A := A)
  have hpoly_coord_domain :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [prodLinearEquiv_append_coord] using hfpoly.2
  have hpoly_coord_image :
      IsPolyhedralConvexSet (m + 1)
        (Acoord ''
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
    have himg := (polyhedralConvexSet_image_preimage_linear (n + 1) (m + 1) Acoord).1
    exact himg _ hpoly_coord_domain
  have hclosed_embedded :
      IsClosed
        (Acoord ''
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f)) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := m + 1)
      (C := Acoord ''
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f))
      hpoly_coord_image).1
  have himage_eq :
      ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
        ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) =
          Acoord ''
            ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [Acoord] using
      (helperForCorollary_19_3_1_image_linearMapProdCoord
        (A := A) (S := epigraph (Set.univ : Set (Fin n → ℝ)) f))
  have hclosed_image :
      IsClosed
        ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
          ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
    simpa [himage_eq] using hclosed_embedded
  let hhome := ((prodLinearEquiv_append_coord (n := m)).toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosed_homeomorphImage :
      IsClosed
        ((hhome : ((Fin m → ℝ) × ℝ) → (Fin (m + 1) → ℝ)) ''
          ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
    simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using hclosed_image
  exact
    (hhome.isClosed_image
      (s := (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)).1
      hclosed_homeomorphImage

/-- Helper for Corollary 19.3.1: in `Fin` coordinates, the epigraph of
`imageUnderLinearMap A f` is exactly the image of the transformed epigraph of `f` under the
conjugated product map. -/
lemma helperForCorollary_19_3_1_transformedEpigraphCoord_imageUnderLinearMap_eq_image
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f)) =
      (helperForCorollary_19_3_1_linearMapProdCoord A) ''
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
      (A := A) (f := f) hfpoly
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := A) (h := f) himage_closed)
  calc
    ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f))
        = ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
            ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
              simp [hEq_epi]
    _ = (helperForCorollary_19_3_1_linearMapProdCoord A) ''
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
              exact
                helperForCorollary_19_3_1_image_linearMapProdCoord
                  (A := A) (S := epigraph (Set.univ : Set (Fin n → ℝ)) f)

/-- Helper for Corollary 19.3.1: in embedded coordinates, the epigraph of `imageUnderLinearMap`
is exactly the linear image of the embedded epigraph. -/
lemma helperForCorollary_19_3_1_transformedEpigraph_imageUnderLinearMap_eq_embeddedImage
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ((fun p => prodLinearEquiv_append (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f)) =
      (fun z => (linearMap_prod_embedded (A := A)) z) ''
        ((fun p => prodLinearEquiv_append (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
      (A := A) (f := f) hfpoly
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := A) (h := f) himage_closed)
  calc
    ((fun p => prodLinearEquiv_append (n := m) p) ''
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f))
        = ((fun p => prodLinearEquiv_append (n := m) p) ''
            ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
              simp [hEq_epi]
    _ = (fun z => (linearMap_prod_embedded (A := A)) z) ''
          ((fun p => prodLinearEquiv_append (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
              simpa using (image_linearMap_prod_embedded (A := A) (h := f))

/-- Helper for Corollary 19.3.1: if `imageUnderLinearMap A f y` is finite, then the infimum is
attained at some `x` with `A x = y`. -/
lemma helperForCorollary_19_3_1_attainment_of_finite_imageValue
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    ∀ y : Fin m → ℝ,
      (∃ r : ℝ, imageUnderLinearMap A f y = (r : EReal)) →
        ∃ x : Fin n → ℝ, A x = y ∧ imageUnderLinearMap A f y = f x := by
  intro y hyfinite
  rcases hyfinite with ⟨r, hr⟩
  have himage_closed :
      IsClosed ((linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f) :=
    helperForCorollary_19_3_1_closedProjectedEpigraph_of_polyhedralFunction
      (A := A) (f := f) hfpoly
  have hEq_epi :
      epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) =
        (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := A) (h := f) himage_closed)
  have hmem_epi :
      (y, r) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f) := by
    refine (mem_epigraph_univ_iff (f := imageUnderLinearMap A f)).2 ?_
    simp [hr]
  have hmem_image :
      (y, r) ∈ (linearMap_prod A) '' epigraph (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [hEq_epi] using hmem_epi
  have hx_exists :
      ∃ x : Fin n → ℝ, A x = y ∧ f x ≤ (r : EReal) := by
    simpa [image_epigraph_linearMap_eq (A := A) (h := f)] using hmem_image
  rcases hx_exists with ⟨x, hxA, hxle⟩
  have hsInf_le_fx : imageUnderLinearMap A f y ≤ f x := by
    have hxmem :
        f x ∈ {z : EReal | ∃ x' : Fin n → ℝ, A x' = y ∧ z = f x'} := by
      exact ⟨x, hxA, rfl⟩
    simpa [imageUnderLinearMap] using (sInf_le hxmem)
  have hfx_le_image : f x ≤ imageUnderLinearMap A f y := by
    simpa [hr] using hxle
  exact ⟨x, hxA, le_antisymm hsInf_le_fx hfx_le_image⟩

/-- Helper for Corollary 19.3.1: in embedded coordinates, the epigraph of
`inverseImageUnderLinearMap` is the preimage of the embedded epigraph under
`linearMap_prod_embedded`. -/
lemma helperForCorollary_19_3_1_transformedEpigraph_inverseImage_eq_embeddedPreimage
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {g : (Fin m → ℝ) → EReal} :
    ((fun p => prodLinearEquiv_append (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g)) =
      (fun z => (linearMap_prod_embedded (A := A)) z) ⁻¹'
        ((fun p => prodLinearEquiv_append (n := m) p) ''
          epigraph (Set.univ : Set (Fin m → ℝ)) g) := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    rcases p with ⟨x, μ⟩
    have hxle : g (A x) ≤ (μ : EReal) := by
      simpa [inverseImageUnderLinearMap] using
        (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).1 hp
    refine ⟨(A x, μ), ?_, ?_⟩
    · exact (mem_epigraph_univ_iff (f := g)).2 hxle
    · simp [linearMap_prod_embedded, LinearMap.comp_apply, linearMap_prod]
  · intro hz
    let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append (n := n)).symm z
    have hz' :
        (linearMap_prod_embedded (A := A)) z ∈
          (fun q => prodLinearEquiv_append (n := m) q) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      exact hz
    have hlin_epi : linearMap_prod A p ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
      rcases hz' with ⟨q, hq, hqeq⟩
      have hqeq' : q = linearMap_prod A p := by
        apply (prodLinearEquiv_append (n := m)).injective
        calc
          (prodLinearEquiv_append (n := m)) q = (linearMap_prod_embedded (A := A)) z := hqeq
          _ = (prodLinearEquiv_append (n := m)) (linearMap_prod A p) := by
                simp [p, linearMap_prod_embedded, LinearMap.comp_apply]
      simpa [hqeq'] using hq
    have hp_epi : p ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g) := by
      rcases p with ⟨x, μ⟩
      have hAx_epi : (A x, μ) ∈ epigraph (Set.univ : Set (Fin m → ℝ)) g := by
        simpa [linearMap_prod] using hlin_epi
      have hxle : g (A x) ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := g)).1 hAx_epi
      exact (mem_epigraph_univ_iff (f := inverseImageUnderLinearMap A g)).2
        (by simpa [inverseImageUnderLinearMap] using hxle)
    refine ⟨p, hp_epi, ?_⟩
    simp [p]

/-- Helper for Corollary 19.3.1: polyhedral convexity is preserved by
`imageUnderLinearMap` for polyhedral convex functions. -/
lemma helperForCorollary_19_3_1_polyhedral_imageUnderLinearMap
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f) :
    IsPolyhedralConvexFunction m (imageUnderLinearMap A f) := by
  refine ⟨?_, ?_⟩
  · simpa [imageUnderLinearMap] using
      (convexFunctionOn_inf_fiber_linearMap (A := A) (h := f) hfpoly.1)
  · have hpoly_coord_domain :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [prodLinearEquiv_append_coord] using hfpoly.2
    let Acoord := helperForCorollary_19_3_1_linearMapProdCoord (A := A)
    have hpoly_embedded_image :
        IsPolyhedralConvexSet (m + 1)
          (Acoord ''
            ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) f)) := by
      have himg :=
        (polyhedralConvexSet_image_preimage_linear (n + 1) (m + 1)
          Acoord).1
      exact himg _ hpoly_coord_domain
    have hEq :=
      helperForCorollary_19_3_1_transformedEpigraphCoord_imageUnderLinearMap_eq_image
        (A := A) (f := f) hfpoly
    have hpoly_target_coord :
        IsPolyhedralConvexSet (m + 1)
          ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) (imageUnderLinearMap A f)) := by
      simpa [hEq, Acoord] using hpoly_embedded_image
    simpa [prodLinearEquiv_append_coord] using hpoly_target_coord

/-- Helper for Corollary 19.3.1: polyhedral convexity is preserved by
`inverseImageUnderLinearMap` for polyhedral convex functions. -/
lemma helperForCorollary_19_3_1_polyhedral_inverseImageUnderLinearMap
    {n m : ℕ} {A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)} {g : (Fin m → ℝ) → EReal}
    (hgpoly : IsPolyhedralConvexFunction m g) :
    IsPolyhedralConvexFunction n (inverseImageUnderLinearMap A g) := by
  refine ⟨?_, ?_⟩
  · simpa [inverseImageUnderLinearMap] using
      (convexFunctionOn_precomp_linearMap (A := A) (g := g) hgpoly.1)
  · let Acoord := helperForCorollary_19_3_1_linearMapProdCoord (A := A)
    have hpoly_target_coord :
        IsPolyhedralConvexSet (m + 1)
          ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
            epigraph (Set.univ : Set (Fin m → ℝ)) g) := by
      simpa [prodLinearEquiv_append_coord] using hgpoly.2
    have hpoly_embedded_preimage :
        IsPolyhedralConvexSet (n + 1)
          (Acoord ⁻¹'
            ((fun p => prodLinearEquiv_append_coord (n := m) p) ''
              epigraph (Set.univ : Set (Fin m → ℝ)) g)) := by
      have hpre :=
        (polyhedralConvexSet_image_preimage_linear (n + 1) (m + 1)
          Acoord).2
      exact hpre _ hpoly_target_coord
    have hEq :=
      helperForCorollary_19_3_1_transformedEpigraphCoord_inverseImage_eq_preimage
        (A := A) (g := g)
    have hpoly_source_coord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (inverseImageUnderLinearMap A g)) := by
      simpa [hEq, Acoord] using hpoly_embedded_preimage
    simpa [prodLinearEquiv_append_coord] using hpoly_source_coord

/-- Corollary 19.3.1: Let `A` be a linear transformation from `ℝ^n` to `ℝ^m`. For each
polyhedral convex function `f` on `ℝ^n`, the convex function `Af` is polyhedral on `ℝ^m`, and
the infimum in its definition, if finite, is attained. For each polyhedral convex function `g`
on `ℝ^m`, `gA` is polyhedral on `ℝ^n`. -/
theorem polyhedralConvexFunction_image_preimage_linear
    (n m : ℕ) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (∀ f : (Fin n → ℝ) → EReal,
      IsPolyhedralConvexFunction n f →
        IsPolyhedralConvexFunction m (imageUnderLinearMap A f) ∧
          (∀ y : Fin m → ℝ,
            (∃ r : ℝ, imageUnderLinearMap A f y = (r : EReal)) →
              ∃ x : Fin n → ℝ, A x = y ∧ imageUnderLinearMap A f y = f x)) ∧
    (∀ g : (Fin m → ℝ) → EReal,
      IsPolyhedralConvexFunction m g →
        IsPolyhedralConvexFunction n (inverseImageUnderLinearMap A g)) := by
  constructor
  · intro f hfpoly
    refine ⟨?_, ?_⟩
    · exact
        helperForCorollary_19_3_1_polyhedral_imageUnderLinearMap
          (A := A) (f := f) hfpoly
    · exact
        helperForCorollary_19_3_1_attainment_of_finite_imageValue
          (A := A) (f := f) hfpoly
  · intro g hgpoly
    exact
      helperForCorollary_19_3_1_polyhedral_inverseImageUnderLinearMap
        (A := A) (g := g) hgpoly

/-- Helper for Corollary 19.3.2: the intersection of the two split preimages is polyhedral
whenever the two source sets are polyhedral. -/
lemma helperForCorollary_19_3_2_polyhedral_preimage_intersection
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (A₁ A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hC₁ : IsPolyhedralConvexSet n C₁)
    (hC₂ : IsPolyhedralConvexSet n C₂) :
    IsPolyhedralConvexSet (n + n) ((A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂)) := by
  have hPre₁ : IsPolyhedralConvexSet (n + n) (A₁ ⁻¹' C₁) := by
    exact
      (polyhedralConvexSet_image_preimage_linear (n + n) n A₁).2 C₁ hC₁
  have hPre₂ : IsPolyhedralConvexSet (n + n) (A₂ ⁻¹' C₂) := by
    exact
      (polyhedralConvexSet_image_preimage_linear (n + n) n A₂).2 C₂ hC₂
  exact
    helperForTheorem_19_1_polyhedral_inter
      (hC := hPre₁) (hD := hPre₂)

/-- Helper for Corollary 19.3.2: a linear image of a polyhedral carrier in
`Fin (n+n) → ℝ` is polyhedral in `Fin n → ℝ`. -/
lemma helperForCorollary_19_3_2_image_polyhedral_of_polyhedralCarrier
    {n : ℕ}
    (B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (P : Set (Fin (n + n) → ℝ))
    (hPpoly : IsPolyhedralConvexSet (n + n) P) :
    IsPolyhedralConvexSet n (B '' P) := by
  exact
    (polyhedralConvexSet_image_preimage_linear (n + n) n B).1 P hPpoly

/-- Helper for Corollary 19.3.2: split projections recover the two components from
`Fin.append`. -/
lemma helperForCorollary_19_3_2_append_split_projection_eval
    {n : ℕ} (u v : Fin n → ℝ) :
    (LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
        (Fin.append u v) = u) ∧
      (LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
          (Fin.append u v) = v) := by
  constructor
  · funext i
    change Fin.append u v (Fin.castAdd n i) = u i
    exact Fin.append_left (u := u) (v := v) i
  · funext i
    change Fin.append u v (Fin.natAdd n i) = v i
    exact Fin.append_right (u := u) (v := v) i

/-- Helper for Corollary 19.3.2: the split-sum linear image of the split-preimage carrier is
exactly the Minkowski sum `C₁ + C₂`. -/
lemma helperForCorollary_19_3_2_sumMap_image_eq_setAdd
    {n : ℕ} (C₁ C₂ : Set (Fin n → ℝ))
    (A₁ A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hA₁ :
      A₁ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)))
    (hA₂ :
      A₂ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)))
    (hB : B = A₁ + A₂) :
    B '' ((A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂)) = C₁ + C₂ := by
  subst hB
  ext y
  constructor
  · intro hy
    rcases hy with ⟨z, hzP, hzy⟩
    rcases hzP with ⟨hz₁, hz₂⟩
    change y ∈ Set.image2 (· + ·) C₁ C₂
    refine ⟨A₁ z, hz₁, A₂ z, hz₂, ?_⟩
    simpa [LinearMap.add_apply] using hzy
  · intro hy
    change y ∈ Set.image2 (· + ·) C₁ C₂ at hy
    rcases hy with ⟨u, hu, v, hv, rfl⟩
    have hSplit :
        (LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
            (Fin.append u v) = u) ∧
          (LinearMap.pi (fun i : Fin n =>
            (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
              (Fin.append u v) = v) :=
      helperForCorollary_19_3_2_append_split_projection_eval (n := n) (u := u) (v := v)
    have hA₁append : A₁ (Fin.append u v) = u := by
      simpa [hA₁] using hSplit.1
    have hA₂append : A₂ (Fin.append u v) = v := by
      simpa [hA₂] using hSplit.2
    have huAppend : A₁ (Fin.append u v) ∈ C₁ := by
      simpa [hA₁append] using hu
    have hvAppend : A₂ (Fin.append u v) ∈ C₂ := by
      simpa [hA₂append] using hv
    have hPair : A₁ (Fin.append u v) ∈ C₁ ∧ A₂ (Fin.append u v) ∈ C₂ :=
      ⟨huAppend, hvAppend⟩
    refine ⟨Fin.append u v, hPair, ?_⟩
    change (A₁ + A₂) (Fin.append u v) = u + v
    simp [LinearMap.add_apply, hA₁append, hA₂append]

/-- Corollary 19.3.2: If `C₁` and `C₂` are polyhedral convex sets in `ℝ^n`, then `C₁ + C₂`
is polyhedral. -/
theorem polyhedral_convexSet_add
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C₁ →
      IsPolyhedralConvexSet n C₂ →
        IsPolyhedralConvexSet n (C₁ + C₂) := by
  intro hC₁ hC₂
  let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let P : Set (Fin (n + n) → ℝ) := (A₁ ⁻¹' C₁) ∩ (A₂ ⁻¹' C₂)
  let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) := A₁ + A₂
  have hA₁ :
      A₁ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)) := rfl
  have hA₂ :
      A₂ =
        LinearMap.pi (fun i : Fin n =>
          (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ)) := rfl
  have hB : B = A₁ + A₂ := rfl
  have hPpoly : IsPolyhedralConvexSet (n + n) P := by
    simpa [P] using
      helperForCorollary_19_3_2_polyhedral_preimage_intersection
        (n := n) (C₁ := C₁) (C₂ := C₂) A₁ A₂ hC₁ hC₂
  have hImagePoly : IsPolyhedralConvexSet n (B '' P) := by
    exact
      helperForCorollary_19_3_2_image_polyhedral_of_polyhedralCarrier
        (n := n) (B := B) (P := P) hPpoly
  have hImageEq : B '' P = C₁ + C₂ := by
    simpa [P] using
      helperForCorollary_19_3_2_sumMap_image_eq_setAdd
        (n := n) (C₁ := C₁) (C₂ := C₂) A₁ A₂ B hA₁ hA₂ hB
  simpa [hImageEq] using hImagePoly

/-- Helper for Corollary 19.3.3: polyhedral convexity of each set implies convexity of both. -/
lemma helperForCorollary_19_3_3_polyhedral_implies_convex_pair
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂poly : IsPolyhedralConvexSet n C₂) :
    Convex ℝ C₁ ∧ Convex ℝ C₂ := by
  exact ⟨
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C₁) hC₁poly,
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C₂) hC₂poly
  ⟩

/-- Helper for Corollary 19.3.3: negation preserves polyhedral convexity. -/
lemma helperForCorollary_19_3_3_neg_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet n (-C) := by
  have hpre :
      IsPolyhedralConvexSet n
        (((-LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) ⁻¹' C)) :=
    (polyhedralConvexSet_image_preimage_linear n n
      (-LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).2 C hCpoly
  simpa using hpre

/-- Helper for Corollary 19.3.3: the set difference `C₁ - C₂` is polyhedral and closed. -/
lemma helperForCorollary_19_3_3_sub_polyhedral_closed
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁poly : IsPolyhedralConvexSet n C₁)
    (hC₂poly : IsPolyhedralConvexSet n C₂) :
    IsPolyhedralConvexSet n (C₁ - C₂) ∧ IsClosed (C₁ - C₂) := by
  have hnegC₂poly : IsPolyhedralConvexSet n (-C₂) :=
    helperForCorollary_19_3_3_neg_polyhedral (n := n) (C := C₂) hC₂poly
  have hsubPoly : IsPolyhedralConvexSet n (C₁ - C₂) := by
    have hadd : IsPolyhedralConvexSet n (C₁ + (-C₂)) :=
      polyhedral_convexSet_add n C₁ (-C₂) hC₁poly hnegC₂poly
    simpa [set_sub_eq_add_neg] using hadd
  have hsubClosed : IsClosed (C₁ - C₂) :=
    helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C₁ - C₂) hsubPoly
  exact ⟨hsubPoly, hsubClosed⟩

/-- Helper for Corollary 19.3.3: disjointness and closedness of `C₁ - C₂` force
`0 ∉ closure (C₁ - C₂)`. -/
lemma helperForCorollary_19_3_3_zero_not_mem_closure_sub
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hdisj : Disjoint C₁ C₂)
    (hSubClosed : IsClosed (C₁ - C₂)) :
    (0 : Fin n → ℝ) ∉ closure (C₁ - C₂) := by
  have h0notSub : (0 : Fin n → ℝ) ∉ (C₁ - C₂) :=
    zero_not_mem_sub_of_disjoint (hdisj := hdisj)
  simpa [hSubClosed.closure_eq] using h0notSub

/-- Helper for Corollary 19.3.3: the Theorem 11.4 criterion yields a strongly separating
hyperplane from `0 ∉ closure (C₁ - C₂)`. -/
lemma helperForCorollary_19_3_3_apply_strongSeparation_iff
    {n : ℕ} {C₁ C₂ : Set (Fin n → ℝ)}
    (hC₁ne : C₁.Nonempty)
    (hC₂ne : C₂.Nonempty)
    (hC₁conv : Convex ℝ C₁)
    (hC₂conv : Convex ℝ C₂)
    (h0notClosure : (0 : Fin n → ℝ) ∉ closure (C₁ - C₂)) :
    ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂ := by
  exact
    (exists_hyperplaneSeparatesStrongly_iff_zero_not_mem_closure_sub
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁ne hC₂ne hC₁conv hC₂conv).2
      h0notClosure

/-- Corollary 19.3.3: If `C₁` and `C₂` are non-empty disjoint polyhedral convex sets, there exists
a hyperplane separating `C₁` and `C₂` strongly. -/
theorem exists_hyperplaneSeparatesStrongly_of_disjoint_polyhedralConvex
    (n : ℕ) (C₁ C₂ : Set (Fin n → ℝ)) :
    C₁.Nonempty →
      C₂.Nonempty →
        Disjoint C₁ C₂ →
          IsPolyhedralConvexSet n C₁ →
            IsPolyhedralConvexSet n C₂ →
              ∃ H : Set (Fin n → ℝ), HyperplaneSeparatesStrongly n H C₁ C₂ := by
  intro hC₁ne hC₂ne hdisj hC₁poly hC₂poly
  have hconvPair : Convex ℝ C₁ ∧ Convex ℝ C₂ :=
    helperForCorollary_19_3_3_polyhedral_implies_convex_pair
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁poly hC₂poly
  have hSubClosed : IsClosed (C₁ - C₂) :=
    (helperForCorollary_19_3_3_sub_polyhedral_closed
      (n := n) (C₁ := C₁) (C₂ := C₂) hC₁poly hC₂poly).2
  have h0notClosure : (0 : Fin n → ℝ) ∉ closure (C₁ - C₂) :=
    helperForCorollary_19_3_3_zero_not_mem_closure_sub
      (n := n) (C₁ := C₁) (C₂ := C₂) hdisj hSubClosed
  exact
    helperForCorollary_19_3_3_apply_strongSeparation_iff
      (n := n) (C₁ := C₁) (C₂ := C₂)
      hC₁ne hC₂ne hconvPair.1 hconvPair.2 h0notClosure

/-- Helper for Corollary 19.3.4: `infimalConvolution` is an image-under-linear-map infimum for
the split-coordinate sum map. -/
lemma helperForCorollary_19_3_4_imageUnder_sumMap_eq_infimalConvolution
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    imageUnderLinearMap B h = infimalConvolution f₁ f₂ := by
  intro A₁ A₂ B h
  funext x
  have hSetEq :
      {z : EReal | ∃ x' : Fin (n + n) → ℝ, B x' = x ∧ z = h x'} =
        {z : EReal |
          ∃ x₁ x₂ : Fin n → ℝ,
            x₁ + x₂ = x ∧ z = f₁ x₁ + f₂ x₂} := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨x', hx', rfl⟩
      refine ⟨A₁ x', A₂ x', ?_, ?_⟩
      · simpa [B, LinearMap.add_apply] using hx'
      · rfl
    · intro hz
      rcases hz with ⟨x₁, x₂, hxsum, rfl⟩
      refine ⟨Fin.append x₁ x₂, ?_, ?_⟩
      · have hA₁ : A₁ (Fin.append x₁ x₂) = x₁ := by
          funext i
          change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
          exact Fin.append_left (u := x₁) (v := x₂) i
        have hA₂ : A₂ (Fin.append x₁ x₂) = x₂ := by
          funext i
          change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
          exact Fin.append_right (u := x₁) (v := x₂) i
        calc
          B (Fin.append x₁ x₂) = A₁ (Fin.append x₁ x₂) + A₂ (Fin.append x₁ x₂) := by
              simp [B, LinearMap.add_apply]
          _ = x₁ + x₂ := by simp [hA₁, hA₂]
          _ = x := hxsum
      · have hA₁ : A₁ (Fin.append x₁ x₂) = x₁ := by
          funext i
          change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
          exact Fin.append_left (u := x₁) (v := x₂) i
        have hA₂ : A₂ (Fin.append x₁ x₂) = x₂ := by
          funext i
          change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
          exact Fin.append_right (u := x₁) (v := x₂) i
        simp [h, hA₁, hA₂]
  simp [imageUnderLinearMap, infimalConvolution, hSetEq]

/-- Helper for Corollary 19.3.4: split a finite real upper bound on `a + b` into real upper
bounds on each summand, assuming neither summand is `⊥`. -/
lemma helperForCorollary_19_3_4_realSplit_of_sum_le_coe
    {a b : EReal} {μ : ℝ}
    (ha_bot : a ≠ (⊥ : EReal))
    (hb_bot : b ≠ (⊥ : EReal))
    (hab : a + b ≤ (μ : EReal)) :
    ∃ μ₁ μ₂ : ℝ,
      a ≤ (μ₁ : EReal) ∧
      b ≤ (μ₂ : EReal) ∧
      μ₁ + μ₂ = μ := by
  have ha_top : a ≠ (⊤ : EReal) := by
    intro ha
    have htop_le : (⊤ : EReal) ≤ (μ : EReal) := by
      have hsum_top : a + b = (⊤ : EReal) := by
        calc
          a + b = (⊤ : EReal) + b := by simp [ha]
          _ = (⊤ : EReal) := EReal.top_add_of_ne_bot hb_bot
      have hab' := hab
      rw [hsum_top] at hab'
      exact hab'
    have hμ_top : (μ : EReal) = (⊤ : EReal) := top_unique htop_le
    exact (EReal.coe_ne_top μ) hμ_top
  have hb_top : b ≠ (⊤ : EReal) := by
    intro hb
    have htop_le : (⊤ : EReal) ≤ (μ : EReal) := by
      have hsum_top : a + b = (⊤ : EReal) := by
        calc
          a + b = a + (⊤ : EReal) := by simp [hb]
          _ = (⊤ : EReal) := EReal.add_top_of_ne_bot ha_bot
      have hab' := hab
      rw [hsum_top] at hab'
      exact hab'
    have hμ_top : (μ : EReal) = (⊤ : EReal) := top_unique htop_le
    exact (EReal.coe_ne_top μ) hμ_top
  have ha_coe : ((a.toReal : ℝ) : EReal) = a := EReal.coe_toReal ha_top ha_bot
  have hb_coe : ((b.toReal : ℝ) : EReal) = b := EReal.coe_toReal hb_top hb_bot
  have hab_coe :
      ((a.toReal + b.toReal : ℝ) : EReal) ≤ (μ : EReal) := by
    calc
      ((a.toReal + b.toReal : ℝ) : EReal)
          = ((a.toReal : ℝ) : EReal) + ((b.toReal : ℝ) : EReal) := by
              simp [EReal.coe_add]
      _ = a + b := by simp [ha_coe, hb_coe]
      _ ≤ (μ : EReal) := hab
  have hab_real : a.toReal + b.toReal ≤ μ := (EReal.coe_le_coe_iff).1 hab_coe
  refine ⟨a.toReal, μ - a.toReal, ?_, ?_, by ring⟩
  · simp [ha_coe]
  · have hb_real : b.toReal ≤ μ - a.toReal := by linarith [hab_real]
    have hb_le_coe :
        ((b.toReal : ℝ) : EReal) ≤ ((μ - a.toReal : ℝ) : EReal) :=
      (EReal.coe_le_coe_iff).2 hb_real
    simpa [hb_coe] using hb_le_coe

/-- Helper for Corollary 19.3.4: the transformed projected epigraph of the split-sum model equals
the Minkowski sum of the transformed epigraphs of `f₁` and `f₂`. -/
lemma helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    ((fun p => prodLinearEquiv_append (n := n) p) ''
      ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
  intro A₁ A₂ B h
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨⟨z, μ⟩, hp, hpq⟩
    have hz_le : h z ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
    have hA₁_univ : A₁ z ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hA₂_univ : A₂ z ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hf₁_bot : f₁ (A₁ z) ≠ (⊥ : EReal) := hproper₁.2.2 (A₁ z) hA₁_univ
    have hf₂_bot : f₂ (A₂ z) ≠ (⊥ : EReal) := hproper₂.2.2 (A₂ z) hA₂_univ
    have hz_split : f₁ (A₁ z) + f₂ (A₂ z) ≤ (μ : EReal) := by
      simpa [h] using hz_le
    rcases helperForCorollary_19_3_4_realSplit_of_sum_le_coe
      (ha_bot := hf₁_bot) (hb_bot := hf₂_bot) (hab := hz_split)
      with ⟨μ₁, μ₂, hμ₁, hμ₂, hμsum⟩
    refine ⟨prodLinearEquiv_append (n := n) (A₁ z, μ₁), ?_,
      prodLinearEquiv_append (n := n) (A₂ z, μ₂), ?_, ?_⟩
    · refine ⟨(A₁ z, μ₁), ?_, rfl⟩
      exact (mem_epigraph_univ_iff (f := f₁)).2 hμ₁
    · refine ⟨(A₂ z, μ₂), ?_, rfl⟩
      exact (mem_epigraph_univ_iff (f := f₂)).2 hμ₂
    · have hpair : linearMap_prod B (z, μ) = (A₁ z, μ₁) + (A₂ z, μ₂) := by
        ext <;> simp [linearMap_prod, B, LinearMap.add_apply, hμsum]
      have hq_sum :
          prodLinearEquiv_append (n := n) q =
            prodLinearEquiv_append (n := n) (A₁ z, μ₁) +
              prodLinearEquiv_append (n := n) (A₂ z, μ₂) := by
        calc
          prodLinearEquiv_append (n := n) q
              = prodLinearEquiv_append (n := n) (linearMap_prod B (z, μ)) := by
                  simp [hpq]
          _ = prodLinearEquiv_append (n := n) ((A₁ z, μ₁) + (A₂ z, μ₂)) := by
                simp [hpair]
          _ = prodLinearEquiv_append (n := n) (A₁ z, μ₁) +
                prodLinearEquiv_append (n := n) (A₂ z, μ₂) := by
                simpa using
                  (prodLinearEquiv_append (n := n)).map_add (A₁ z, μ₁) (A₂ z, μ₂)
      exact hq_sum.symm
  · rintro ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    rcases hy₁ with ⟨⟨x₁, μ₁⟩, hp₁, rfl⟩
    rcases hy₂ with ⟨⟨x₂, μ₂⟩, hp₂, rfl⟩
    have hx₁_le : f₁ x₁ ≤ (μ₁ : EReal) := by
      simpa using (mem_epigraph_univ_iff (f := f₁)).1 hp₁
    have hx₂_le : f₂ x₂ ≤ (μ₂ : EReal) := by
      simpa using (mem_epigraph_univ_iff (f := f₂)).1 hp₂
    let z : Fin (n + n) → ℝ := Fin.append x₁ x₂
    have hA₁ : A₁ z = x₁ := by
      funext i
      change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
      exact Fin.append_left (u := x₁) (v := x₂) i
    have hA₂ : A₂ z = x₂ := by
      funext i
      change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
      exact Fin.append_right (u := x₁) (v := x₂) i
    have hz_le : h z ≤ ((μ₁ + μ₂ : ℝ) : EReal) := by
      calc
        h z = f₁ (A₁ z) + f₂ (A₂ z) := by
          simp [h]
        _ = f₁ x₁ + f₂ x₂ := by
          simp [hA₁, hA₂]
        _ ≤ (μ₁ : EReal) + (μ₂ : EReal) := add_le_add hx₁_le hx₂_le
        _ = ((μ₁ + μ₂ : ℝ) : EReal) := by
          simp [EReal.coe_add]
    refine ⟨linearMap_prod B (z, μ₁ + μ₂), ?_, ?_⟩
    · refine ⟨(z, μ₁ + μ₂), ?_, rfl⟩
      exact (mem_epigraph_univ_iff (f := h)).2 hz_le
    · calc
        prodLinearEquiv_append (n := n) (linearMap_prod B (z, μ₁ + μ₂))
            = prodLinearEquiv_append (n := n) (B z, μ₁ + μ₂) := by
                simp [linearMap_prod]
        _ = prodLinearEquiv_append (n := n) (x₁ + x₂, μ₁ + μ₂) := by
              have hBz : B z = x₁ + x₂ := by
                simp [B, LinearMap.add_apply, hA₁, hA₂]
              simp [hBz]
        _ = prodLinearEquiv_append (n := n) ((x₁, μ₁) + (x₂, μ₂)) := by
              rfl
        _ = prodLinearEquiv_append (n := n) (x₁, μ₁) +
              prodLinearEquiv_append (n := n) (x₂, μ₂) := by
              simpa using
                (prodLinearEquiv_append (n := n)).map_add (x₁, μ₁) (x₂, μ₂)

/-- Helper for Corollary 19.3.4: coordinate version of
`helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum`. -/
lemma helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum_coord
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
  intro A₁ A₂ B h
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with ⟨⟨z, μ⟩, hp, hpq⟩
    have hz_le : h z ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp
    have hA₁_univ : A₁ z ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hA₂_univ : A₂ z ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hf₁_bot : f₁ (A₁ z) ≠ (⊥ : EReal) := hproper₁.2.2 (A₁ z) hA₁_univ
    have hf₂_bot : f₂ (A₂ z) ≠ (⊥ : EReal) := hproper₂.2.2 (A₂ z) hA₂_univ
    have hz_split : f₁ (A₁ z) + f₂ (A₂ z) ≤ (μ : EReal) := by simpa [h] using hz_le
    rcases helperForCorollary_19_3_4_realSplit_of_sum_le_coe
      (ha_bot := hf₁_bot) (hb_bot := hf₂_bot) (hab := hz_split)
      with ⟨μ₁, μ₂, hμ₁, hμ₂, hμsum⟩
    refine ⟨prodLinearEquiv_append_coord (n := n) (A₁ z, μ₁), ?_,
      prodLinearEquiv_append_coord (n := n) (A₂ z, μ₂), ?_, ?_⟩
    · refine ⟨(A₁ z, μ₁), (mem_epigraph_univ_iff (f := f₁)).2 hμ₁, rfl⟩
    · refine ⟨(A₂ z, μ₂), (mem_epigraph_univ_iff (f := f₂)).2 hμ₂, rfl⟩
    · have hpair : linearMap_prod B (z, μ) = (A₁ z, μ₁) + (A₂ z, μ₂) := by
        ext <;> simp [linearMap_prod, B, LinearMap.add_apply, hμsum]
      have hq_sum :
          prodLinearEquiv_append_coord (n := n) q =
            prodLinearEquiv_append_coord (n := n) (A₁ z, μ₁) +
              prodLinearEquiv_append_coord (n := n) (A₂ z, μ₂) := by
        calc
          prodLinearEquiv_append_coord (n := n) q
              = prodLinearEquiv_append_coord (n := n) (linearMap_prod B (z, μ)) := by
                  simp [hpq]
          _ = prodLinearEquiv_append_coord (n := n) ((A₁ z, μ₁) + (A₂ z, μ₂)) := by
                simp [hpair]
          _ = prodLinearEquiv_append_coord (n := n) (A₁ z, μ₁) +
                prodLinearEquiv_append_coord (n := n) (A₂ z, μ₂) := by
                simpa using
                  (prodLinearEquiv_append_coord (n := n)).map_add (A₁ z, μ₁) (A₂ z, μ₂)
      exact hq_sum.symm
  · rintro ⟨y₁, hy₁, y₂, hy₂, rfl⟩
    rcases hy₁ with ⟨⟨x₁, μ₁⟩, hp₁, rfl⟩
    rcases hy₂ with ⟨⟨x₂, μ₂⟩, hp₂, rfl⟩
    have hx₁_le : f₁ x₁ ≤ (μ₁ : EReal) := by simpa using (mem_epigraph_univ_iff (f := f₁)).1 hp₁
    have hx₂_le : f₂ x₂ ≤ (μ₂ : EReal) := by simpa using (mem_epigraph_univ_iff (f := f₂)).1 hp₂
    let z : Fin (n + n) → ℝ := Fin.append x₁ x₂
    have hA₁ : A₁ z = x₁ := by
      funext i
      change Fin.append x₁ x₂ (Fin.castAdd n i) = x₁ i
      exact Fin.append_left (u := x₁) (v := x₂) i
    have hA₂ : A₂ z = x₂ := by
      funext i
      change Fin.append x₁ x₂ (Fin.natAdd n i) = x₂ i
      exact Fin.append_right (u := x₁) (v := x₂) i
    have hz_le : h z ≤ ((μ₁ + μ₂ : ℝ) : EReal) := by
      calc
        h z = f₁ (A₁ z) + f₂ (A₂ z) := by simp [h]
        _ = f₁ x₁ + f₂ x₂ := by simp [hA₁, hA₂]
        _ ≤ (μ₁ : EReal) + (μ₂ : EReal) := add_le_add hx₁_le hx₂_le
        _ = ((μ₁ + μ₂ : ℝ) : EReal) := by simp [EReal.coe_add]
    refine ⟨linearMap_prod B (z, μ₁ + μ₂), ?_, ?_⟩
    · refine ⟨(z, μ₁ + μ₂), (mem_epigraph_univ_iff (f := h)).2 hz_le, rfl⟩
    · calc
        prodLinearEquiv_append_coord (n := n) (linearMap_prod B (z, μ₁ + μ₂))
            = prodLinearEquiv_append_coord (n := n) (B z, μ₁ + μ₂) := by simp [linearMap_prod]
        _ = prodLinearEquiv_append_coord (n := n) (x₁ + x₂, μ₁ + μ₂) := by
              have hBz : B z = x₁ + x₂ := by simp [B, LinearMap.add_apply, hA₁, hA₂]
              simp [hBz]
        _ = prodLinearEquiv_append_coord (n := n) ((x₁, μ₁) + (x₂, μ₂)) := by rfl
        _ = prodLinearEquiv_append_coord (n := n) (x₁, μ₁) +
              prodLinearEquiv_append_coord (n := n) (x₂, μ₂) := by
              simpa using
                (prodLinearEquiv_append_coord (n := n)).map_add (x₁, μ₁) (x₂, μ₂)

/-- Helper for Corollary 19.3.4: the projected epigraph of the split-sum model is closed, via
its transformed description as a sum of transformed polyhedral epigraphs. -/
lemma helperForCorollary_19_3_4_projectedEpigraph_closed
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁poly : IsPolyhedralConvexFunction n f₁)
    (hf₂poly : IsPolyhedralConvexFunction n f₂)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      LinearMap.pi (fun i : Fin n =>
        (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
    let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      A₁ + A₂
    let h : (Fin (n + n) → ℝ) → EReal :=
      fun z => f₁ (A₁ z) + f₂ (A₂ z)
    IsClosed ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h) := by
  intro A₁ A₂ B h
  have hEq_coord :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) :=
    helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum_coord
      (f₁ := f₁) (f₂ := f₂) (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hpoly₁_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) := by
    simpa [prodLinearEquiv_append_coord] using hf₁poly.2
  have hpoly₂_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂) := by
    simpa [prodLinearEquiv_append_coord] using hf₂poly.2
  have hpoly_sum_coord :
      IsPolyhedralConvexSet (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    exact
      polyhedral_convexSet_add (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁))
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂))
        hpoly₁_coord hpoly₂_coord
  have hclosed_sum_coord :
      IsClosed
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n + 1)
      (C :=
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)))
      hpoly_sum_coord).1
  have hclosed_transformed_coord :
      IsClosed
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) := by
    simpa [hEq_coord] using hclosed_sum_coord
  let hhome := ((prodLinearEquiv_append_coord (n := n)).toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosed_homeomorphImage :
      IsClosed
        ((hhome : ((Fin n → ℝ) × ℝ) → (Fin (n + 1) → ℝ)) ''
          ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) := by
    simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using
      hclosed_transformed_coord
  exact
    (hhome.isClosed_image
      (s := (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)).1
      hclosed_homeomorphImage

/-- Helper for Corollary 19.3.4: the transformed epigraph of `infimalConvolution f₁ f₂` is
polyhedral, obtained from the closed projected-epigraph identity and the transformed sum
description. -/
lemma helperForCorollary_19_3_4_polyhedralEpigraph_infimalConvolution
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁poly : IsPolyhedralConvexFunction n f₁)
    (hf₂poly : IsPolyhedralConvexFunction n f₂)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂) :
    IsPolyhedralConvexSet (n + 1)
      ((fun p => prodLinearEquiv_append (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) := by
  let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    A₁ + A₂
  let h : (Fin (n + n) → ℝ) → EReal :=
    fun z => f₁ (A₁ z) + f₂ (A₂ z)
  have hclosed_proj :
      IsClosed ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h) := by
    exact
      helperForCorollary_19_3_4_projectedEpigraph_closed
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hEq_epi :
      epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h) =
        (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := B) (h := h) hclosed_proj)
  have hImageEqInf : imageUnderLinearMap B h = infimalConvolution f₁ f₂ := by
    exact
      helperForCorollary_19_3_4_imageUnder_sumMap_eq_infimalConvolution
        (f₁ := f₁) (f₂ := f₂)
  have hEq_sum :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    exact
      helperForCorollary_19_3_4_transformedProjectedEpigraph_eq_sum_coord
        (f₁ := f₁) (f₂ := f₂) (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hpoly₁ :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) :=
    by simpa [prodLinearEquiv_append_coord] using hf₁poly.2
  have hpoly₂ :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂) :=
    by simpa [prodLinearEquiv_append_coord] using hf₂poly.2
  have hpoly_sum :
      IsPolyhedralConvexSet (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    exact
      polyhedral_convexSet_add (n + 1)
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁))
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂))
        hpoly₁ hpoly₂
  have htarget_eq :
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) =
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := by
    calc
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂))
          = ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h)) := by
                simp [hImageEqInf]
      _ = ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h)) := by
              simp [hEq_epi]
      _ = (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f₁) +
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) f₂)) := hEq_sum
  have hpoly_target_coord :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) := by
    simpa [htarget_eq] using hpoly_sum
  simpa [prodLinearEquiv_append_coord] using hpoly_target_coord

/-- Helper for Corollary 19.3.4: isolate the first summand in an equality
`u + v = x` as `u = x - v`. -/
lemma helperForCorollary_19_3_4_eq_sub_of_add_eq
    {n : ℕ} {u v x : Fin n → ℝ}
    (h : u + v = x) :
    u = x - v := by
  have hsub := congrArg (fun t : Fin n → ℝ => t - v) h
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub

/-- Helper for Corollary 19.3.4: when the infimal-convolution value at `x` is finite, the
infimum is attained by some `y`. -/
lemma helperForCorollary_19_3_4_attainment_of_finite_value
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁poly : IsPolyhedralConvexFunction n f₁)
    (hf₂poly : IsPolyhedralConvexFunction n f₂)
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂)
    (x : Fin n → ℝ) {r : ℝ}
    (hr : infimalConvolution f₁ f₂ x = (r : EReal)) :
    ∃ y : Fin n → ℝ, infimalConvolution f₁ f₂ x = f₁ (x - y) + f₂ y := by
  let A₁ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.castAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let A₂ : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    LinearMap.pi (fun i : Fin n =>
      (LinearMap.proj (i := Fin.natAdd n i) : (Fin (n + n) → ℝ) →ₗ[ℝ] ℝ))
  let B : (Fin (n + n) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    A₁ + A₂
  let h : (Fin (n + n) → ℝ) → EReal :=
    fun z => f₁ (A₁ z) + f₂ (A₂ z)
  have hclosed_proj : IsClosed ((linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h) := by
    exact
      helperForCorollary_19_3_4_projectedEpigraph_closed
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  have hEq_epi_image :
      epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h) =
        (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h := by
    simpa [imageUnderLinearMap] using
      (epigraph_infimum_eq_image_of_closed_image (A := B) (h := h) hclosed_proj)
  have hImageEqInf : imageUnderLinearMap B h = infimalConvolution f₁ f₂ := by
    exact helperForCorollary_19_3_4_imageUnder_sumMap_eq_infimalConvolution (f₁ := f₁) (f₂ := f₂)
  have hr_image : imageUnderLinearMap B h x = (r : EReal) := by
    calc
      imageUnderLinearMap B h x = infimalConvolution f₁ f₂ x := by
        simp [hImageEqInf]
      _ = (r : EReal) := hr
  have hmem_epi :
      (x, r) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) (imageUnderLinearMap B h) := by
    refine (mem_epigraph_univ_iff (f := imageUnderLinearMap B h)).2 ?_
    simp [hr_image]
  have hmem_image :
      (x, r) ∈ (linearMap_prod B) '' epigraph (Set.univ : Set (Fin (n + n) → ℝ)) h := by
    simpa [hEq_epi_image] using hmem_epi
  have hz_exists :
      ∃ z : Fin (n + n) → ℝ, B z = x ∧ h z ≤ (r : EReal) := by
    simpa [image_epigraph_linearMap_eq (A := B) (h := h)] using hmem_image
  rcases hz_exists with ⟨z, hzB, hzle⟩
  have hsInf_le_hz : imageUnderLinearMap B h x ≤ h z := by
    have hz_mem_set :
        h z ∈ {w : EReal | ∃ z' : Fin (n + n) → ℝ, B z' = x ∧ w = h z'} := by
      exact ⟨z, hzB, rfl⟩
    simpa [imageUnderLinearMap] using sInf_le hz_mem_set
  have hhz_le_image : h z ≤ imageUnderLinearMap B h x := by
    simpa [hr_image] using hzle
  have himage_eq_hz : imageUnderLinearMap B h x = h z :=
    le_antisymm hsInf_le_hz hhz_le_image
  have hA₁A₂ : A₁ z + A₂ z = x := by
    simpa [B, LinearMap.add_apply] using hzB
  have hA₁eq : A₁ z = x - A₂ z :=
    helperForCorollary_19_3_4_eq_sub_of_add_eq (h := hA₁A₂)
  refine ⟨A₂ z, ?_⟩
  calc
    infimalConvolution f₁ f₂ x = imageUnderLinearMap B h x := by
      simp [hImageEqInf]
    _ = h z := himage_eq_hz
    _ = f₁ (A₁ z) + f₂ (A₂ z) := by simp [h]
    _ = f₁ (x - A₂ z) + f₂ (A₂ z) := by simp [hA₁eq]

/-- Helper for Corollary 19.3.4: if the infimal-convolution value at `x` is `⊤`, the defining
infimum is attained by the witness `y = 0`. -/
lemma helperForCorollary_19_3_4_attainment_of_top_value
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (htop : infimalConvolution f₁ f₂ x = (⊤ : EReal)) :
    ∃ y : Fin n → ℝ, infimalConvolution f₁ f₂ x = f₁ (x - y) + f₂ y := by
  refine ⟨0, ?_⟩
  have hsInf_le :
      infimalConvolution f₁ f₂ x ≤ f₁ (x - 0) + f₂ 0 := by
    have hmem :
        (f₁ (x - 0) + f₂ 0 : EReal) ∈
          {z : EReal |
            ∃ x₁ x₂ : Fin n → ℝ,
              x₁ + x₂ = x ∧ z = f₁ x₁ + f₂ x₂} := by
      refine ⟨x - 0, 0, ?_, ?_⟩
      · simp
      · simp
    simpa [infimalConvolution] using (sInf_le hmem)
  have htop_le : (⊤ : EReal) ≤ f₁ (x - 0) + f₂ 0 := by
    simpa [htop] using hsInf_le
  have hvalue_top : f₁ (x - 0) + f₂ 0 = (⊤ : EReal) := top_unique htop_le
  calc
    infimalConvolution f₁ f₂ x = (⊤ : EReal) := htop
    _ = f₁ (x - 0) + f₂ 0 := hvalue_top.symm

/-- Corollary 19.3.4: If `f₁` and `f₂` are proper polyhedral convex functions on `ℝ^n`, then
`infimalConvolution f₁ f₂` is a polyhedral convex function. Moreover, if
`infimalConvolution f₁ f₂` is proper, the infimum in the definition of
`(f₁ \sqcup f₂)(x)` is attained for each `x`. -/
theorem polyhedralConvexFunction_infimalConvolution
    (n : ℕ) (f₁ f₂ : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f₁ →
      IsPolyhedralConvexFunction n f₂ →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ →
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ →
            IsPolyhedralConvexFunction n (infimalConvolution f₁ f₂) ∧
              (ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
                (infimalConvolution f₁ f₂) →
                ∀ x : Fin n → ℝ,
                  ∃ y : Fin n → ℝ,
                    infimalConvolution f₁ f₂ x = f₁ (x - y) + f₂ y) := by
  intro hf₁poly hf₂poly hproper₁ hproper₂
  have hconv_inf :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂) :=
    convexFunctionOn_infimalConvolution_of_proper
      (f := f₁) (g := f₂) hproper₁ hproper₂
  have hpoly_inf :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => (prodLinearEquiv_append (n := n)) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (infimalConvolution f₁ f₂)) := by
    exact
      helperForCorollary_19_3_4_polyhedralEpigraph_infimalConvolution
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
  refine ⟨⟨hconv_inf, hpoly_inf⟩, ?_⟩
  intro hproper_inf x
  by_cases htop : infimalConvolution f₁ f₂ x = (⊤ : EReal)
  · exact
      helperForCorollary_19_3_4_attainment_of_top_value
        (f₁ := f₁) (f₂ := f₂) (x := x) htop
  · have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hbot : infimalConvolution f₁ f₂ x ≠ (⊥ : EReal) :=
      hproper_inf.2.2 x hx_univ
    let r : ℝ := (infimalConvolution f₁ f₂ x).toReal
    have hr : infimalConvolution f₁ f₂ x = (r : EReal) := by
      have hcoe :
          ((infimalConvolution f₁ f₂ x).toReal : EReal) = infimalConvolution f₁ f₂ x :=
        EReal.coe_toReal htop hbot
      simpa [r] using hcoe.symm
    exact
      helperForCorollary_19_3_4_attainment_of_finite_value
        (f₁ := f₁) (f₂ := f₂)
        (hf₁poly := hf₁poly) (hf₂poly := hf₂poly)
        (hproper₁ := hproper₁) (hproper₂ := hproper₂)
        (x := x) (r := r) hr

/-- Helper for Theorem 19.4: split a finite upper bound on `f₁ x + f₂ x`
into real upper bounds for each summand. -/
lemma helperForTheorem_19_4_splitRealUpperBound
    {n : ℕ} {f₁ f₂ : (Fin n → ℝ) → EReal}
    (hproper₁ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁)
    (hproper₂ : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂)
    {x : Fin n → ℝ} {μ : ℝ}
    (hsum : f₁ x + f₂ x ≤ (μ : EReal)) :
    ∃ μ₁ μ₂ : ℝ, f₁ x ≤ (μ₁ : EReal) ∧ f₂ x ≤ (μ₂ : EReal) ∧ μ₁ + μ₂ = μ := by
  have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  have hf₁bot : f₁ x ≠ (⊥ : EReal) :=
    hproper₁.2.2 x hx_univ
  have hf₂bot : f₂ x ≠ (⊥ : EReal) :=
    hproper₂.2.2 x hx_univ
  exact
    helperForCorollary_19_3_4_realSplit_of_sum_le_coe
      (ha_bot := hf₁bot) (hb_bot := hf₂bot) (hab := hsum)

/-- Helper for Theorem 19.4: add two real-valued epigraph bounds in `EReal`. -/
lemma helperForTheorem_19_4_addUpperBounds
    {n : ℕ} {f₁ f₂ : (Fin n → ℝ) → EReal} {x : Fin n → ℝ} {μ₁ μ₂ : ℝ}
    (hμ₁ : f₁ x ≤ (μ₁ : EReal))
    (hμ₂ : f₂ x ≤ (μ₂ : EReal)) :
    f₁ x + f₂ x ≤ ((μ₁ + μ₂ : ℝ) : EReal) := by
  calc
    f₁ x + f₂ x ≤ (μ₁ : EReal) + (μ₂ : EReal) := add_le_add hμ₁ hμ₂
    _ = ((μ₁ + μ₂ : ℝ) : EReal) := by simp [EReal.coe_add]

/-- Theorem 19.4: If `f₁` and `f₂` are proper polyhedral convex functions, then `f₁ + f₂`
is polyhedral. -/
theorem polyhedralConvexFunction_add_of_proper
    (n : ℕ) (f₁ f₂ : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f₁ →
      IsPolyhedralConvexFunction n f₂ →
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ →
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ →
            IsPolyhedralConvexFunction n (fun x => f₁ x + f₂ x) := by
  intro hf₁poly hf₂poly hproper₁ hproper₂
  refine ⟨?_, ?_⟩
  · exact convexFunctionOn_add_of_proper hproper₁ hproper₂
  · let μMap1 : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj (i := Fin.natAdd n (0 : Fin 2)) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ)
    let μMap2 : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ :=
      (LinearMap.proj (i := Fin.natAdd n (1 : Fin 2)) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ)
    let L₁ : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      LinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases
          μMap1
          (fun j : Fin n =>
            (LinearMap.proj (i := Fin.castAdd 2 j) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ))
          i)
    let L₂ : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      LinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases
          μMap2
          (fun j : Fin n =>
            (LinearMap.proj (i := Fin.castAdd 2 j) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ))
          i)
    let B : (Fin (n + 2) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
      LinearMap.pi (fun i : Fin (n + 1) =>
        Fin.lastCases
          (μMap1 + μMap2)
          (fun j : Fin n =>
            (LinearMap.proj (i := Fin.castAdd 2 j) : (Fin (n + 2) → ℝ) →ₗ[ℝ] ℝ))
          i)
    let E₁ : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f₁)
    let E₂ : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f₂)
    let P : Set (Fin (n + 2) → ℝ) := (L₁ ⁻¹' E₁) ∩ (L₂ ⁻¹' E₂)
    have hE₁poly : IsPolyhedralConvexSet (n + 1) E₁ := by
      simpa [E₁, prodLinearEquiv_append_coord] using hf₁poly.2
    have hE₂poly : IsPolyhedralConvexSet (n + 1) E₂ := by
      simpa [E₂, prodLinearEquiv_append_coord] using hf₂poly.2
    have hPre₁ : IsPolyhedralConvexSet (n + 2) (L₁ ⁻¹' E₁) := by
      exact
        (polyhedralConvexSet_image_preimage_linear (n + 2) (n + 1) L₁).2
          E₁ hE₁poly
    have hPre₂ : IsPolyhedralConvexSet (n + 2) (L₂ ⁻¹' E₂) := by
      exact
        (polyhedralConvexSet_image_preimage_linear (n + 2) (n + 1) L₂).2
          E₂ hE₂poly
    have hPpoly : IsPolyhedralConvexSet (n + 2) P := by
      exact helperForTheorem_19_1_polyhedral_inter hPre₁ hPre₂
    have hImagePoly : IsPolyhedralConvexSet (n + 1) (B '' P) := by
      exact
        (polyhedralConvexSet_image_preimage_linear (n + 2) (n + 1) B).1
          P hPpoly
    have hcoord_castSucc :
        ∀ (x0 : Fin n → ℝ) (μ0 : ℝ) (j0 : Fin n),
          x0 j0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.castSucc j0) := by
      intro x0 μ0 j0
      change x0 j0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.castSucc j0)
      change x0 j0 =
        ((appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0)
      have happ := congrArg
        (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.castSucc j0))
        (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      have hlin :
          (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
            (appendAffineEquiv n 1).linear
              (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
        simpa using congrArg
          (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
          (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
      have happ' :
          ((appendAffineEquiv n 1).linear
            (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.castSucc j0) =
            Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) := by
        simpa [hlin] using happ
      have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.castSucc j0) = x0 j0 := by
        exact Fin.append_left (u := x0) (v := Function.const (Fin 1) μ0) j0
      exact (happ'.trans happend).symm
    have hcoord_last :
        ∀ (x0 : Fin n → ℝ) (μ0 : ℝ),
          μ0 = (prodLinearEquiv_append_coord (n := n) (x0, μ0)) (Fin.last n) := by
      intro x0 μ0
      change μ0 = (prodLinearEquiv_append (n := n) (x0, μ0)).ofLp (Fin.last n)
      change μ0 =
        ((appendAffineEquiv n 1).linear
          (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n)
      have happ := congrArg
        (fun v => ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin (n + 1))) v) (Fin.last n))
        (appendAffineEquiv_apply n 1 (WithLp.toLp 2 x0) (WithLp.toLp 2 (Function.const (Fin 1) μ0)))
      have hlin :
          (appendAffineEquiv n 1) (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) =
            (appendAffineEquiv n 1).linear
              (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)) := by
        simpa using congrArg
          (fun f => f (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0)))
          (appendAffineEquiv_eq_linear_toAffineEquiv n 1)
      have happ' :
          ((appendAffineEquiv n 1).linear
            (WithLp.toLp 2 x0, WithLp.toLp 2 (Function.const (Fin 1) μ0))).ofLp (Fin.last n) =
            Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) := by
        simpa [hlin] using happ
      have happend : Fin.append x0 (Function.const (Fin 1) μ0) (Fin.last n) = μ0 := by
        change Fin.append x0 (Function.const (Fin 1) μ0) (Fin.natAdd n (0 : Fin 1)) = μ0
        exact Fin.append_right (u := x0) (v := Function.const (Fin 1) μ0) (0 : Fin 1)
      exact (happ'.trans happend).symm
    have hTargetEq :
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (fun x => f₁ x + f₂ x)) =
        B '' P := by
      ext y
      constructor
      · rintro ⟨⟨x, μ⟩, hEpi, rfl⟩
        have hsum : f₁ x + f₂ x ≤ (μ : EReal) :=
          (mem_epigraph_univ_iff (f := fun x => f₁ x + f₂ x)).1 hEpi
        rcases helperForTheorem_19_4_splitRealUpperBound
          (hproper₁ := hproper₁) (hproper₂ := hproper₂) (hsum := hsum) with
          ⟨μ₁, μ₂, hμ₁, hμ₂, hμsum⟩
        let z : Fin (n + 2) → ℝ :=
          Fin.append x (Fin.cases μ₁ (fun _ : Fin 1 => μ₂))
        have hz_right : z (Fin.natAdd n (1 : Fin 2)) = μ₂ := by
          dsimp [z]
          simp only [Fin.append_right]
          simpa using
            (Fin.cases_succ (motive := fun _ : Fin 2 => ℝ)
              (zero := μ₁) (succ := fun _ : Fin 1 => μ₂) (i := (0 : Fin 1)))
        have hL₁z : L₁ z = prodLinearEquiv_append_coord (n := n) (x, μ₁) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₁ z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) := by
                simp [L₁, μMap1]
              _ = μ₁ := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁)) (Fin.last n) := by
                exact hcoord_last x μ₁
          · intro j
            calc
              L₁ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₁]
              _ = x j := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁)) (Fin.castSucc j) := by
                exact hcoord_castSucc x μ₁ j
        have hL₂z : L₂ z = prodLinearEquiv_append_coord (n := n) (x, μ₂) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₂ z (Fin.last n) = z (Fin.natAdd n (1 : Fin 2)) := by
                simp [L₂, μMap2]
              _ = μ₂ := hz_right
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₂)) (Fin.last n) := by
                exact hcoord_last x μ₂
          · intro j
            calc
              L₂ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₂]
              _ = x j := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₂)) (Fin.castSucc j) := by
                exact hcoord_castSucc x μ₂ j
        have hBz : B z = prodLinearEquiv_append_coord (n := n) (x, μ₁ + μ₂) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              B z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) + z (Fin.natAdd n (1 : Fin 2)) := by
                simp [B, μMap1, μMap2]
              _ = μ₁ + μ₂ := by simp [z, hz_right]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁ + μ₂)) (Fin.last n) := by
                exact hcoord_last x (μ₁ + μ₂)
          · intro j
            calc
              B z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [B]
              _ = x j := by simp [z]
              _ = (prodLinearEquiv_append_coord (n := n) (x, μ₁ + μ₂)) (Fin.castSucc j) := by
                exact hcoord_castSucc x (μ₁ + μ₂) j
        have hmemE₁ : L₁ z ∈ E₁ := by
          have hpair : prodLinearEquiv_append_coord (n := n) (x, μ₁) ∈ E₁ := by
            exact ⟨(x, μ₁), (mem_epigraph_univ_iff (f := f₁)).2 hμ₁, rfl⟩
          simpa [hL₁z] using hpair
        have hmemE₂ : L₂ z ∈ E₂ := by
          have hpair : prodLinearEquiv_append_coord (n := n) (x, μ₂) ∈ E₂ := by
            exact ⟨(x, μ₂), (mem_epigraph_univ_iff (f := f₂)).2 hμ₂, rfl⟩
          simpa [hL₂z] using hpair
        have hBy : B z = prodLinearEquiv_append_coord (n := n) (x, μ) := by
          simpa [hμsum] using hBz
        exact ⟨z, ⟨hmemE₁, hmemE₂⟩, hBy⟩
      · rintro ⟨z, hzP, hzy⟩
        rcases hzP with ⟨hz₁, hz₂⟩
        let xz : Fin n → ℝ := fun i => z (Fin.castAdd 2 i)
        let μ₁z : ℝ := z (Fin.natAdd n (0 : Fin 2))
        let μ₂z : ℝ := z (Fin.natAdd n (1 : Fin 2))
        have hL₁z : L₁ z = prodLinearEquiv_append_coord (n := n) (xz, μ₁z) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₁ z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) := by
                simp [L₁, μMap1]
              _ = μ₁z := by simp [μ₁z]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z)) (Fin.last n) := by
                exact hcoord_last xz μ₁z
          · intro j
            calc
              L₁ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₁]
              _ = xz j := by simp [xz]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z)) (Fin.castSucc j) := by
                exact hcoord_castSucc xz μ₁z j
        have hL₂z : L₂ z = prodLinearEquiv_append_coord (n := n) (xz, μ₂z) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              L₂ z (Fin.last n) = z (Fin.natAdd n (1 : Fin 2)) := by
                simp [L₂, μMap2]
              _ = μ₂z := by simp [μ₂z]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₂z)) (Fin.last n) := by
                exact hcoord_last xz μ₂z
          · intro j
            calc
              L₂ z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [L₂]
              _ = xz j := by simp [xz]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₂z)) (Fin.castSucc j) := by
                exact hcoord_castSucc xz μ₂z j
        have hBz : B z = prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z) := by
          ext i
          refine Fin.lastCases ?_ ?_ i
          · calc
              B z (Fin.last n) = z (Fin.natAdd n (0 : Fin 2)) + z (Fin.natAdd n (1 : Fin 2)) := by
                simp [B, μMap1, μMap2]
              _ = μ₁z + μ₂z := by simp [μ₁z, μ₂z]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z)) (Fin.last n) := by
                exact hcoord_last xz (μ₁z + μ₂z)
          · intro j
            calc
              B z (Fin.castSucc j) = z (Fin.castAdd 2 j) := by
                simp [B]
              _ = xz j := by simp [xz]
              _ = (prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z)) (Fin.castSucc j) := by
                exact hcoord_castSucc xz (μ₁z + μ₂z) j
        have hfx₁ : f₁ xz ≤ (μ₁z : EReal) := by
          rcases hz₁ with ⟨p, hpEpi, hpEq⟩
          have hpcoord :
              prodLinearEquiv_append_coord (n := n) p =
                prodLinearEquiv_append_coord (n := n) (xz, μ₁z) := by
            calc
              prodLinearEquiv_append_coord (n := n) p = L₁ z := hpEq
              _ = prodLinearEquiv_append_coord (n := n) (xz, μ₁z) := hL₁z
          have hpPair : p = (xz, μ₁z) :=
            (prodLinearEquiv_append_coord (n := n)).injective hpcoord
          have hpIneq : f₁ p.1 ≤ (p.2 : EReal) :=
            (mem_epigraph_univ_iff (f := f₁)).1 hpEpi
          simpa [hpPair] using hpIneq
        have hfx₂ : f₂ xz ≤ (μ₂z : EReal) := by
          rcases hz₂ with ⟨p, hpEpi, hpEq⟩
          have hpcoord :
              prodLinearEquiv_append_coord (n := n) p =
                prodLinearEquiv_append_coord (n := n) (xz, μ₂z) := by
            calc
              prodLinearEquiv_append_coord (n := n) p = L₂ z := hpEq
              _ = prodLinearEquiv_append_coord (n := n) (xz, μ₂z) := hL₂z
          have hpPair : p = (xz, μ₂z) :=
            (prodLinearEquiv_append_coord (n := n)).injective hpcoord
          have hpIneq : f₂ p.1 ≤ (p.2 : EReal) :=
            (mem_epigraph_univ_iff (f := f₂)).1 hpEpi
          simpa [hpPair] using hpIneq
        have hsum_le : f₁ xz + f₂ xz ≤ ((μ₁z + μ₂z : ℝ) : EReal) := by
          exact helperForTheorem_19_4_addUpperBounds (hμ₁ := hfx₁) (hμ₂ := hfx₂)
        have hycoord : y = prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z) := by
          calc
            y = B z := hzy.symm
            _ = prodLinearEquiv_append_coord (n := n) (xz, μ₁z + μ₂z) := hBz
        refine
          ⟨(xz, μ₁z + μ₂z),
            (mem_epigraph_univ_iff (f := fun x => f₁ x + f₂ x)).2 hsum_le, ?_⟩
        simp [hycoord]
    have hpoly_target_coord :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (fun x => f₁ x + f₂ x)) := by
      simpa [hTargetEq] using hImagePoly
    simpa [prodLinearEquiv_append_coord] using hpoly_target_coord

/-- Helper for Theorem 19.5: scalar multiples of a polyhedral convex set are polyhedral. -/
lemma helperForTheorem_19_5_smul_polyhedral_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCpoly : IsPolyhedralConvexSet n C) :
    ∀ a : ℝ, IsPolyhedralConvexSet n (a • C) := by
  intro a
  let A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    a • (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
  have hImage : IsPolyhedralConvexSet n (A '' C) :=
    (polyhedralConvexSet_image_preimage_linear n n A).1 C hCpoly
  have hEq : a • C = A '' C := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [A]
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      refine ⟨y, hy, ?_⟩
      simpa [A] using hxy
  simpa [hEq] using hImage

/-- Helper for Theorem 19.5: the mixed hull generated by `{0}` and `S₁` sits in the
recession cone of `mixedConvexHull S₀ S₁`. -/
lemma helperForTheorem_19_5_directionHull_subset_recessionCone_of_mixedHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)} :
    mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ ⊆
      Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
  have hConv : Convex ℝ (Set.recessionCone (mixedConvexHull (n := n) S₀ S₁)) := by
    have hMixedConv : Convex ℝ (mixedConvexHull (n := n) S₀ S₁) :=
      convex_mixedConvexHull (n := n) S₀ S₁
    exact recessionCone_convex_fin (C := mixedConvexHull (n := n) S₀ S₁) hMixedConv
  have hZero : ({0} : Set (Fin n → ℝ)) ⊆ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
    intro x hx
    have hx0 : x = 0 := by
      simpa using hx
    subst hx0
    intro y hy t ht
    simpa using hy
  have hRec :
      ∀ d ∈ S₁, ∀ x ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁),
        ∀ t : ℝ, 0 ≤ t →
          x + t • d ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
    intro d hd x hx t ht
    have hdRec : d ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) :=
      mem_recessionCone_mixedConvexHull_of_mem_directions
        (n := n) (S₀ := S₀) (S₁ := S₁) (d := d) hd
    intro y hy s hs
    have hsx : y + s • x ∈ mixedConvexHull (n := n) S₀ S₁ :=
      hx hy hs
    have hs_nonneg : 0 ≤ s * t :=
      mul_nonneg hs ht
    have hsd : (y + s • x) + (s * t) • d ∈ mixedConvexHull (n := n) S₀ S₁ :=
      hdRec hsx hs_nonneg
    have hsd' : y + s • (x + t • d) ∈ mixedConvexHull (n := n) S₀ S₁ := by
      simpa [smul_add, smul_smul, add_assoc, add_left_comm, add_comm, mul_assoc] using hsd
    exact hsd'
  exact
    mixedConvexHull_subset_of_convex_of_subset_of_recedes (n := n)
      (S₀ := ({0} : Set (Fin n → ℝ)))
      (S₁ := S₁)
      (Ccand := Set.recessionCone (mixedConvexHull (n := n) S₀ S₁))
      hConv hZero hRec

/-- Helper for Theorem 19.5: a nonempty mixed convex hull must have at least one point-generator.
-/
lemma helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hMixedNonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty) :
    S₀.Nonempty := by
  by_contra hS₀ne
  have hS₀empty : S₀ = (∅ : Set (Fin n → ℝ)) :=
    (Set.not_nonempty_iff_eq_empty).1 hS₀ne
  have hMixedEmpty : mixedConvexHull (n := n) S₀ S₁ = (∅ : Set (Fin n → ℝ)) := by
    simpa [hS₀empty] using (mixedConvexHull_empty_points (n := n) (S₁ := S₁))
  rcases hMixedNonempty with ⟨x, hx⟩
  have hxEmpty : x ∈ (∅ : Set (Fin n → ℝ)) := by
    rw [hMixedEmpty] at hx
    exact hx
  exact Set.notMem_empty x hxEmpty

/-- Helper for Theorem 19.5: the recession cone of `cone S₁` equals `cone S₁`. -/
lemma helperForTheorem_19_5_recessionCone_cone_eq_cone
    {n : ℕ} {S₁ : Set (Fin n → ℝ)} :
    Set.recessionCone (cone n S₁) = cone n S₁ := by
  have hcone : IsConvexCone n (cone n S₁) := by
    simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₁)] using
      (isConvexCone_convexConeGenerated (n := n) (S₁ := S₁))
  have hadd :
      ∀ x ∈ cone n S₁, ∀ y ∈ cone n S₁, x + y ∈ cone n S₁ :=
    isConvexCone_add_closed n (cone n S₁) hcone
  have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁ :=
    (Set.mem_insert_iff).2 (Or.inl rfl)
  have h0cone : (0 : Fin n → ℝ) ∈ cone n S₁ := by
    exact (subset_convexHull (𝕜 := ℝ) (s := ray n S₁)) h0ray
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    have hyone : (0 : Fin n → ℝ) + (1 : ℝ) • y ∈ cone n S₁ :=
      hy (x := 0) h0cone (t := 1) (by norm_num)
    simpa using hyone
  · intro y hy x hx t ht
    by_cases ht0 : t = 0
    · subst ht0
      simpa using hx
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hty : t • y ∈ cone n S₁ := hcone.1 y hy t htpos
      exact hadd x hx (t • y) hty

/-- Helper for Theorem 19.5: with finite nonempty point-generators, the recession cone of
`conv S₀ + cone S₁` is exactly `cone S₁`. -/
lemma helperForTheorem_19_5_recessionCone_conv_add_cone_of_finite_points
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hS₀fin : Set.Finite S₀) (hS₁fin : Set.Finite S₁) (hS₀ne : S₀.Nonempty) :
    Set.recessionCone (conv S₀ + cone n S₁) = cone n S₁ := by
  classical
  let A : Set (Fin n → ℝ) := conv S₀
  let B : Set (Fin n → ℝ) := cone n S₁
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  let A' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' A
  let B' : Set (EuclideanSpace ℝ (Fin n)) := e.symm '' B
  have hAne : A.Nonempty := by
    rcases hS₀ne with ⟨x, hx⟩
    have hxA : x ∈ A := by
      change x ∈ conv S₀
      exact (subset_convexHull (𝕜 := ℝ) (s := S₀)) hx
    exact ⟨x, hxA⟩
  have hAconv : Convex ℝ A := by
    simpa [A, conv] using (convex_convexHull (𝕜 := ℝ) (s := S₀))
  have hAclosed : IsClosed A := by
    simpa [A, conv] using hS₀fin.isClosed_convexHull
  have hS₀bdd : Bornology.IsBounded S₀ := hS₀fin.isBounded
  have hAbdd : Bornology.IsBounded A := by
    simpa [A, conv] using (isBounded_convexHull (s := S₀)).2 hS₀bdd
  have hArecZero : Set.recessionCone A = ({0} : Set (Fin n → ℝ)) :=
    recessionCone_eq_singleton_zero_of_closed_bounded_convex_fin
      (n := n) (C := A) hAne hAclosed hAconv hAbdd
  have h0ray : (0 : Fin n → ℝ) ∈ ray n S₁ :=
    (Set.mem_insert_iff).2 (Or.inl rfl)
  have h0B : (0 : Fin n → ℝ) ∈ B := by
    change (0 : Fin n → ℝ) ∈ cone n S₁
    exact (subset_convexHull (𝕜 := ℝ) (s := ray n S₁)) h0ray
  have hBne : B.Nonempty := ⟨0, h0B⟩
  have hBconv : Convex ℝ B := by
    simpa [B, cone, conv] using (convex_convexHull (𝕜 := ℝ) (s := ray n S₁))
  have hBclosed : IsClosed B := by
    simpa [B] using
      (helperForTheorem_19_1_isClosed_cone_of_finite_generators
        (m := n) (T := S₁) hS₁fin)
  have hBrec : Set.recessionCone B = B :=
    helperForTheorem_19_5_recessionCone_cone_eq_cone
      (n := n) (S₁ := S₁)
  have hA'ne : A'.Nonempty := by
    rcases hAne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hB'ne : B'.Nonempty := by
    rcases hBne with ⟨x, hx⟩
    exact ⟨e.symm x, ⟨x, hx, rfl⟩⟩
  have hA'conv : Convex ℝ A' := by
    simpa [A'] using hAconv.linear_image e.symm.toLinearMap
  have hB'conv : Convex ℝ B' := by
    simpa [B'] using hBconv.linear_image e.symm.toLinearMap
  have hA'closed : IsClosed A' := by
    simpa [A'] using (e.symm.toHomeomorph.isClosed_image).2 hAclosed
  have hB'closed : IsClosed B' := by
    simpa [B'] using (e.symm.toHomeomorph.isClosed_image).2 hBclosed
  have hA'recZero : Set.recessionCone A' = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
    calc
      Set.recessionCone A' = e.symm '' Set.recessionCone A := by
        simpa [A'] using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := A))
      _ = e.symm '' ({0} : Set (Fin n → ℝ)) := by
        simp [hArecZero]
      _ = ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
        simp
  have hB'recEq : Set.recessionCone B' = B' := by
    calc
      Set.recessionCone B' = e.symm '' Set.recessionCone B := by
        simpa [B'] using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := B))
      _ = e.symm '' B := by
        simp [hBrec]
      _ = B' := rfl
  have hopp :
      ∀ z,
        z ∈ Set.recessionCone A' → -z ∈ Set.recessionCone B' → z = 0 := by
    intro z hzA _hzB
    have hz0 : z ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
      simpa [hA'recZero] using hzA
    simpa [Set.mem_singleton_iff] using hz0
  have hrecAdd' : Set.recessionCone (A' + B') = Set.recessionCone A' + Set.recessionCone B' :=
    (closed_add_recessionCone_eq_of_no_opposite_recession
      (C1 := A') (C2 := B') (hC1ne := hA'ne) (hC2ne := hB'ne)
      (hC1conv := hA'conv) (hC2conv := hB'conv)
      (hC1closed := hA'closed) (hC2closed := hB'closed) (hopp := hopp)).2
  have hzero_add_rec :
      ({0} : Set (EuclideanSpace ℝ (Fin n))) + Set.recessionCone B' = Set.recessionCone B' := by
    ext z
    constructor
    · intro hz
      rcases (Set.mem_add).1 hz with ⟨u, hu, v, hv, huv⟩
      have hu0 : u = 0 := by
        simpa [Set.mem_singleton_iff] using hu
      have hzv : z = v := by
        simpa [hu0] using huv.symm
      simpa [hzv] using hv
    · intro hz
      have h0mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
        simp
      have hsum : (0 : EuclideanSpace ℝ (Fin n)) + z = z := by
        simp
      exact (Set.mem_add).2 ⟨0, h0mem, z, hz, hsum⟩
  have hrecAddEqB' : Set.recessionCone (A' + B') = B' := by
    calc
      Set.recessionCone (A' + B') = Set.recessionCone A' + Set.recessionCone B' := hrecAdd'
      _ = ({0} : Set (EuclideanSpace ℝ (Fin n))) + Set.recessionCone B' := by
        simp [hA'recZero]
      _ = Set.recessionCone B' := hzero_add_rec
      _ = B' := hB'recEq
  have hsumEq : A' + B' = e.symm '' (A + B) := by
    simpa [A', B', e] using
      (euclideanEquiv_symm_image_add (n := n) (C1 := A) (C2 := B)).symm
  have hrecImageSum : Set.recessionCone (A' + B') = e.symm '' Set.recessionCone (A + B) := by
    calc
      Set.recessionCone (A' + B') = Set.recessionCone (e.symm '' (A + B)) := by
        simp [hsumEq]
      _ = e.symm '' Set.recessionCone (A + B) := by
        simpa using
          (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := A + B))
  have himageEq : e.symm '' Set.recessionCone (A + B) = B' := by
    calc
      e.symm '' Set.recessionCone (A + B) = Set.recessionCone (A' + B') := hrecImageSum.symm
      _ = B' := hrecAddEqB'
  have hrecAB : Set.recessionCone (A + B) = B := by
    ext x
    constructor
    · intro hx
      have hxImage : e.symm x ∈ e.symm '' Set.recessionCone (A + B) := ⟨x, hx, rfl⟩
      have hxB' : e.symm x ∈ B' := by
        simpa [himageEq] using hxImage
      rcases hxB' with ⟨y, hyB, hyEq⟩
      have hyx : y = x := by
        exact e.symm.injective hyEq
      simpa [B, hyx] using hyB
    · intro hx
      have hxB' : e.symm x ∈ B' := ⟨x, hx, rfl⟩
      have hxImage : e.symm x ∈ e.symm '' Set.recessionCone (A + B) := by
        simpa [himageEq] using hxB'
      rcases hxImage with ⟨y, hyRec, hyEq⟩
      have hyx : y = x := by
        exact e.symm.injective hyEq
      simpa [hyx] using hyRec
  simpa [A, B, conv] using hrecAB

/-- Helper for Theorem 19.5: for finite mixed-hull data, every recession direction lies in the
mixed hull generated by `{0}` and the direction set. -/
lemma helperForTheorem_19_5_recessionCone_subset_directionHull_of_finiteMixedHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hS₀fin : Set.Finite S₀) (hS₁fin : Set.Finite S₁) (hS₀ne : S₀.Nonempty) :
    Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) ⊆
      mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
  have hreprPair := mixedConvexHull_eq_conv_add_ray_eq_conv_add_cone (n := n) S₀ S₁
  have hrepr : mixedConvexHull (n := n) S₀ S₁ = conv S₀ + cone n S₁ :=
    hreprPair.1.trans hreprPair.2
  have hrecEq :
      Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) = cone n S₁ := by
    calc
      Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) = Set.recessionCone (conv S₀ + cone n S₁) := by
        simp [hrepr]
      _ = cone n S₁ :=
        helperForTheorem_19_5_recessionCone_conv_add_cone_of_finite_points
          (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hdirEq : cone n S₁ = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
    simpa using (mixedConvexHull_singleton_zero_eq_cone (n := n) (T := S₁)).symm
  intro x hx
  have hxCone : x ∈ cone n S₁ := by
    simpa [hrecEq] using hx
  simpa [hdirEq] using hxCone

/-- Helper for Theorem 19.5: finite mixed-hull representations satisfy
`0⁺(mixedConvexHull S₀ S₁) = mixedConvexHull {0} S₁`. -/
lemma helperForTheorem_19_5_recessionCone_eq_directionHull_of_finiteMixedHull
    {n : ℕ} {S₀ S₁ : Set (Fin n → ℝ)}
    (hS₀fin : Set.Finite S₀) (hS₁fin : Set.Finite S₁) (hS₀ne : S₀.Nonempty) :
    Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) =
      mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
  refine Set.Subset.antisymm ?_ ?_
  · exact
      helperForTheorem_19_5_recessionCone_subset_directionHull_of_finiteMixedHull
        (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  · exact
      helperForTheorem_19_5_directionHull_subset_recessionCone_of_mixedHull
        (n := n) (S₀ := S₀) (S₁ := S₁)

/-- Helper for Theorem 19.5: the recession cone of a nonempty polyhedral convex set is
polyhedral. -/
lemma helperForTheorem_19_5_recessionCone_polyhedral_of_polyhedral
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hCpoly : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet n (Set.recessionCone C) := by
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
          (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  have hCfg : IsFinitelyGeneratedConvexSet n C :=
    (hTFAE.out 0 2).1 hCpoly
  rcases hCfg with ⟨S₀, S₁, hS₀fin, hS₁fin, hCeq⟩
  have hMixNonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty := by
    rcases hCne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [hCeq] using hx
  have hS₀ne : S₀.Nonempty :=
    helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
      (n := n) (S₀ := S₀) (S₁ := S₁) hMixNonempty
  have hRecEq :
      Set.recessionCone C = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ := by
    calc
      Set.recessionCone C = Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
        simp [hCeq]
      _ = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ :=
        helperForTheorem_19_5_recessionCone_eq_directionHull_of_finiteMixedHull
          (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hRecConv : Convex ℝ (Set.recessionCone C) :=
    recessionCone_convex_fin (C := C) hCconv
  have hRecFG : IsFinitelyGeneratedConvexSet n (Set.recessionCone C) := by
    refine ⟨({0} : Set (Fin n → ℝ)), S₁, ?_, hS₁fin, ?_⟩
    · simp
    · exact hRecEq
  exact
    helperForTheorem_19_1_finitelyGenerated_imp_polyhedral
      (n := n) (C := Set.recessionCone C) hRecConv hRecFG

/-- Theorem 19.5: Let `C` be a non-empty polyhedral convex set. Then `λ • C` is polyhedral for
every scalar `λ`, the recession cone `0^+ C` is polyhedral, and if `C` is represented as a mixed
convex hull of a finite set of points and directions, then `0^+ C` is the mixed convex hull of
the origin together with the directions. -/
theorem polyhedralConvexSet_smul_recessionCone_and_representation
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    C.Nonempty →
    IsPolyhedralConvexSet n C →
      (∀ a : ℝ, IsPolyhedralConvexSet n (a • C)) ∧
        IsPolyhedralConvexSet n (Set.recessionCone C) ∧
        (∀ (S₀ S₁ : Set (Fin n → ℝ)),
          Set.Finite S₀ →
          Set.Finite S₁ →
          C = mixedConvexHull (n := n) S₀ S₁ →
            Set.recessionCone C =
              mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁) := by
  intro hCne hCpoly
  refine ⟨?_, ?_, ?_⟩
  · exact
      helperForTheorem_19_5_smul_polyhedral_of_polyhedral
        (n := n) (C := C) hCpoly
  · exact
      helperForTheorem_19_5_recessionCone_polyhedral_of_polyhedral
        (n := n) (C := C) hCne hCpoly
  · intro S₀ S₁ hS₀fin hS₁fin hCeq
    have hMixNonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty := by
      rcases hCne with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simpa [hCeq] using hx
    have hS₀ne : S₀.Nonempty :=
      helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
        (n := n) (S₀ := S₀) (S₁ := S₁) hMixNonempty
    calc
      Set.recessionCone C = Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) := by
        simp [hCeq]
      _ = mixedConvexHull (n := n) ({0} : Set (Fin n → ℝ)) S₁ :=
        helperForTheorem_19_5_recessionCone_eq_directionHull_of_finiteMixedHull
          (n := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne

/-- Helper for Corollary 19.5.1: polyhedrality of the transformed epigraph implies
convexity of the corresponding function. -/
lemma helperForCorollary_19_5_1_convexFunctionOn_of_polyhedralTransformedEpigraph
    {n : ℕ} {g : (Fin n → ℝ) → EReal}
    (hpoly :
      IsPolyhedralConvexSet (n + 1)
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) g)) :
    ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
  let e := prodLinearEquiv_append_coord (n := n)
  have hconv_image :
      Convex ℝ (e '' epigraph (Set.univ : Set (Fin n → ℝ)) g) :=
    helperForTheorem_19_1_polyhedral_isConvex
      (n := n + 1)
      (C := e '' epigraph (Set.univ : Set (Fin n → ℝ)) g)
      hpoly
  have hconv_preimage :
      Convex ℝ (e ⁻¹' (e '' epigraph (Set.univ : Set (Fin n → ℝ)) g)) :=
    hconv_image.linear_preimage e.toLinearMap
  have hpreimage_eq :
      e ⁻¹' (e '' epigraph (Set.univ : Set (Fin n → ℝ)) g) =
        epigraph (Set.univ : Set (Fin n → ℝ)) g := by
    exact Set.preimage_image_eq _ e.injective
  simpa [ConvexFunctionOn, e, hpreimage_eq] using hconv_preimage

/-- Helper for Corollary 19.5.1: the recession cone of the transformed epigraph of `f`
is the transformed epigraph of `recessionFunction f`. -/
lemma helperForCorollary_19_5_1_recessionCone_transformedEpigraph_eq_transformedEpigraph_recessionFunction
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hconv : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    Set.recessionCone
        (((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) f)) =
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f)) := by
  let g : Fin 1 → (Fin n → ℝ) → EReal := fun _ => f
  have hconv_epi :
      ∀ i : Fin 1,
        Convex ℝ (epigraph (Set.univ : Set (Fin n → ℝ)) (g i)) := by
    intro i
    simpa [g] using
      (convex_epigraph_of_convexFunctionOn (f := f) hconv)
  have hproper_family :
      ∀ i : Fin 1,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (g i) := by
    intro i
    simpa [g] using hproper
  have hk :
      ∀ (i : Fin 1) (y : Fin n → ℝ),
        recessionFunction f y =
          sSup { r : EReal | ∃ x : Fin n → ℝ, r = g i (x + y) - g i x } := by
    intro i y
    simpa [g] using
      (section16_recessionFunction_eq_sSup_unrestricted (f := f) y)
  have hrec_epi :
      Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) f) =
        epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) := by
    have hrec :=
      recessionCone_epigraph_eq_epigraph_k (f := g) (k := recessionFunction f)
        hconv_epi hproper_family hk
    simpa [g] using hrec (i := 0)
  let e := prodLinearEquiv_append_coord (n := n)
  calc
    Set.recessionCone (e '' epigraph (Set.univ : Set (Fin n → ℝ)) f)
        = e '' Set.recessionCone (epigraph (Set.univ : Set (Fin n → ℝ)) f) := by
          simpa [e] using
            (recessionCone_image_linearEquiv (e := e)
              (C := epigraph (Set.univ : Set (Fin n → ℝ)) f))
    _ = e '' epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) := by
          simp [hrec_epi]

/-- Helper for Corollary 19.5.1: a proper convex function takes a non-`⊤` value. -/
lemma helperForCorollary_19_5_1_exists_nonTop_value_of_proper
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∃ x, f x ≠ (⊤ : EReal) := by
  rcases properConvexFunctionOn_exists_finite_point (n := n) (f := f) hproper with
    ⟨x0, r0, hx0⟩
  refine ⟨x0, ?_⟩
  rw [hx0]
  exact EReal.coe_ne_top r0

/-- Helper for Corollary 19.5.1: positive right scalar multiples have polyhedral
transformed epigraph. -/
lemma helperForCorollary_19_5_1_transformedEpigraph_rightScalarMultiple_polyhedral_of_pos
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    {lam : ℝ} (hlam : 0 < lam) :
    IsPolyhedralConvexSet (n + 1)
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam)) := by
  let C : Set (Fin (n + 1) → ℝ) :=
    ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
      epigraph (Set.univ : Set (Fin n → ℝ)) f)
  have hCne : C.Nonempty := by
    rcases hproper.2.1 with ⟨p, hp⟩
    refine ⟨(prodLinearEquiv_append_coord (n := n)) p, ?_⟩
    exact ⟨p, hp, rfl⟩
  have hCpoly : IsPolyhedralConvexSet (n + 1) C := by
    simpa [C, prodLinearEquiv_append_coord] using hfpoly.2
  have hpoly_smul : IsPolyhedralConvexSet (n + 1) (lam • C) := by
    have hthm :=
      polyhedralConvexSet_smul_recessionCone_and_representation
        (n := n + 1) (C := C) hCne hCpoly
    exact hthm.1 lam
  have hEq :
      lam • C =
        ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
          epigraph (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam)) := by
    simpa [C] using
      (smul_embedded_epigraph_eq_embedded_epigraph_rightScalarMultiple
        (f := f) (hf := hfpoly.1) (lam := lam) hlam)
  simpa [hEq] using hpoly_smul

/-- Helper for Corollary 19.5.1: the endpoint `λ = 0` gives a polyhedral
right scalar multiple. -/
lemma helperForCorollary_19_5_1_zero_scalar_case_polyhedral
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction n f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    IsPolyhedralConvexFunction n (rightScalarMultiple f 0) := by
  have hfinite : ∃ x, f x ≠ (⊤ : EReal) :=
    helperForCorollary_19_5_1_exists_nonTop_value_of_proper
      (n := n) (f := f) hproper
  have hzero_eq :
      rightScalarMultiple f 0 = indicatorFunction ({0} : Set (Fin n → ℝ)) :=
    rightScalarMultiple_zero_eq_indicator (f := f) hfpoly.1 hfinite
  have hzero_poly : IsPolyhedralConvexSet n ({0} : Set (Fin n → ℝ)) :=
    helperForTheorem_19_1_zero_set_polyhedral (m := n)
  have hindicator_poly :
      IsPolyhedralConvexFunction n
        (indicatorFunction ({0} : Set (Fin n → ℝ))) :=
    helperForCorollary_19_2_1_indicatorPolyhedral_of_polyhedralSet
      (n := n) (C := ({0} : Set (Fin n → ℝ))) hzero_poly
  simpa [hzero_eq] using hindicator_poly

/-- Corollary 19.5.1: If `f` is a proper polyhedral convex function, then the right scalar
multiple `rightScalarMultiple f λ` is polyhedral for every `λ ≥ 0`, and the recession function
`recessionFunction f` (the case `λ = 0^+`) is polyhedral. -/
theorem polyhedralConvexFunction_rightScalarMultiple_and_recession
    (n : ℕ) (f : (Fin n → ℝ) → EReal) :
    IsPolyhedralConvexFunction n f →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f →
      (∀ lam : ℝ, 0 ≤ lam → IsPolyhedralConvexFunction n (rightScalarMultiple f lam)) ∧
      IsPolyhedralConvexFunction n (recessionFunction f) := by
  intro hfpoly hproper
  refine ⟨?_, ?_⟩
  · intro lam hlam
    by_cases hlam0 : lam = 0
    · subst hlam0
      exact
        helperForCorollary_19_5_1_zero_scalar_case_polyhedral
          (n := n) (f := f) hfpoly hproper
    · have hlam_pos : 0 < lam := lt_of_le_of_ne hlam (Ne.symm hlam0)
      have hpoly_trans :
          IsPolyhedralConvexSet (n + 1)
            ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
              epigraph (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam)) :=
        helperForCorollary_19_5_1_transformedEpigraph_rightScalarMultiple_polyhedral_of_pos
          (n := n) (f := f) hfpoly hproper hlam_pos
      have hconv_scaled :
          ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (rightScalarMultiple f lam) :=
        helperForCorollary_19_5_1_convexFunctionOn_of_polyhedralTransformedEpigraph
          (n := n) (g := rightScalarMultiple f lam) hpoly_trans
      refine ⟨hconv_scaled, ?_⟩
      simpa [prodLinearEquiv_append_coord] using hpoly_trans
  · let C : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) f)
    have hCne : C.Nonempty := by
      rcases hproper.2.1 with ⟨p, hp⟩
      refine ⟨(prodLinearEquiv_append_coord (n := n)) p, ?_⟩
      exact ⟨p, hp, rfl⟩
    have hCpoly : IsPolyhedralConvexSet (n + 1) C := by
      simpa [C, prodLinearEquiv_append_coord] using hfpoly.2
    have hthm :=
      polyhedralConvexSet_smul_recessionCone_and_representation
        (n := n + 1) (C := C) hCne hCpoly
    have hrec_poly : IsPolyhedralConvexSet (n + 1) (Set.recessionCone C) :=
      hthm.2.1
    have hrec_eq :
        Set.recessionCone C =
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f)) := by
      simpa [C] using
        (helperForCorollary_19_5_1_recessionCone_transformedEpigraph_eq_transformedEpigraph_recessionFunction
          (n := n) (f := f) hfpoly.1 hproper)
    have hpoly_trans :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) (recessionFunction f)) := by
      simpa [hrec_eq] using hrec_poly
    have hconv_rec : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (recessionFunction f) :=
      helperForCorollary_19_5_1_convexFunctionOn_of_polyhedralTransformedEpigraph
        (n := n) (g := recessionFunction f) hpoly_trans
    refine ⟨hconv_rec, ?_⟩
    simpa [prodLinearEquiv_append_coord] using hpoly_trans

/-- Weighted sums using `λ i • C i` for nonzero coefficients and `0^+ C i` for zero
coefficients. -/
def weightedSumSetWithRecession
    (n m : ℕ) (C : Fin m → Set (Fin n → ℝ)) (lam : Fin m → ℝ) :
    Set (Fin n → ℝ) :=
  {x | ∃ y : Fin m → Fin n → ℝ,
      (∀ i, y i ∈ (if lam i = 0 then Set.recessionCone (C i) else (lam i) • (C i))) ∧
      x = ∑ i, y i}

/-- Helper for Theorem 19.6: `weightedSumSetWithRecession` is exactly the finite Minkowski
sum of the branch sets `if λᵢ = 0 then 0⁺Cᵢ else λᵢ • Cᵢ`. -/
lemma helperForTheorem_19_6_weightedSumSetWithRecession_eq_finsetSumIf
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)} {lam : Fin m → ℝ} :
    weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) =
      ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => if lam i = 0 then Set.recessionCone (C i) else lam i • C i)
      (a := ∑ i, y i)).2 ?_
    refine ⟨y, ?_, rfl⟩
    intro i hi
    exact hy i
  · intro hx
    rcases (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => if lam i = 0 then Set.recessionCone (C i) else lam i • C i)
      (a := x)).1 hx with ⟨y, hy, hsum⟩
    refine ⟨y, ?_, ?_⟩
    intro i
    have hiuniv : i ∈ (Finset.univ : Finset (Fin m)) := by
      simp
    exact hy (i := i) hiuniv
    simpa using hsum.symm

/-- Helper for Theorem 19.6: for each index `i`, the branch set
`if λᵢ = 0 then 0⁺Cᵢ else λᵢ • Cᵢ` is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_component_if_zero_or_scaled
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i))
    (lam : Fin m → ℝ) :
    ∀ i, IsPolyhedralConvexSet n
      (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  intro i
  have hrepr :=
    polyhedralConvexSet_smul_recessionCone_and_representation
      (n := n) (C := C i) (h_nonempty i) (h_polyhedral i)
  by_cases hzero : lam i = 0
  · simpa [hzero] using hrepr.2.1
  · simpa [hzero] using (hrepr.1 (lam i))

/-- Helper for Theorem 19.6: finite Minkowski sums of polyhedral convex sets are polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_finset_sum
    {n m : ℕ} {S : Fin m → Set (Fin n → ℝ)}
    (hS_poly : ∀ i, IsPolyhedralConvexSet n (S i)) :
    IsPolyhedralConvexSet n (∑ i, S i) := by
  classical
  have hsum_poly :
      ∀ t : Finset (Fin m), IsPolyhedralConvexSet n (Finset.sum t S) := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · simpa using (helperForTheorem_19_1_zero_set_polyhedral (m := n))
    · intro a t ha ht
      have ha_poly : IsPolyhedralConvexSet n (S a) := hS_poly a
      have hadd_poly : IsPolyhedralConvexSet n (S a + Finset.sum t S) :=
        polyhedral_convexSet_add n (S a) (Finset.sum t S) ha_poly ht
      simpa [Finset.sum_insert ha] using hadd_poly
  simpa using hsum_poly (Finset.univ : Finset (Fin m))

/-- Helper for Theorem 19.6: polyhedral family members are closed and convex. -/
lemma helperForTheorem_19_6_closed_convex_of_polyhedral_family
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)}
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i)) :
    (∀ i, IsClosed (C i)) ∧ (∀ i, Convex ℝ (C i)) := by
  refine ⟨?_, ?_⟩
  · intro i
    exact
      (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
        (n := n) (C := C i) (h_polyhedral i)).1
  · intro i
    exact helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C i) (h_polyhedral i)

/-- Helper for Theorem 19.6: if each `closure (K i)` is polyhedral, then
`closure (∑ i, K i) = ∑ i, closure (K i)`. -/
lemma helperForTheorem_19_6_closure_sum_liftedCones_eq_sum_closure_liftedCones_polyhedral
    {n m : ℕ} {K : Fin m → Set (Fin (n + 1) → ℝ)}
    (hK_poly : ∀ i, IsPolyhedralConvexSet (n + 1) (closure (K i))) :
    closure (∑ i, K i) = ∑ i, closure (K i) := by
  have hsum_poly :
      IsPolyhedralConvexSet (n + 1) (∑ i, closure (K i)) :=
    helperForTheorem_19_6_polyhedral_finset_sum
      (n := n + 1) (m := m) (S := fun i => closure (K i)) hK_poly
  have hsum_closed : IsClosed (∑ i, closure (K i)) :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n + 1) (C := ∑ i, closure (K i)) hsum_poly).1
  have hsubset_left : closure (∑ i, K i) ⊆ ∑ i, closure (K i) := by
    refine closure_minimal ?_ hsum_closed
    intro x hx
    rcases
      (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
        (f := K) (a := x)).1 hx with ⟨y, hy, hsum⟩
    refine (Set.mem_finset_sum (t := (Finset.univ : Finset (Fin m)))
      (f := fun i => closure (K i)) (a := x)).2 ?_
    refine ⟨y, ?_, hsum⟩
    intro i hi
    exact subset_closure (hy (i := i) hi)
  have hsubset_right : (∑ i, closure (K i)) ⊆ closure (∑ i, K i) := by
    classical
    have haux :
        ∀ t : Finset (Fin m),
          Finset.sum t (fun i => closure (K i)) ⊆ closure (Finset.sum t K) := by
      intro t
      refine Finset.induction_on t ?_ ?_
      · intro x hx
        simpa using hx
      · intro a t ha hrec x hx
        rcases (Set.mem_add).1 (by simpa [Finset.sum_insert ha] using hx) with ⟨u, hu, v, hv, rfl⟩
        have hv' : v ∈ closure (Finset.sum t K) := hrec hv
        have hsubset_add :
            closure (K a) + closure (Finset.sum t K) ⊆ closure (K a + Finset.sum t K) := by
          simpa using
            (vadd_set_closure_subset (K := K a) (L := Finset.sum t K))
        have huv : u + v ∈ closure (K a) + closure (Finset.sum t K) :=
          (Set.mem_add).2 ⟨u, hu, v, hv', rfl⟩
        have huvc : u + v ∈ closure (K a + Finset.sum t K) := hsubset_add huv
        simpa [Finset.sum_insert ha] using huvc
    simpa using haux (Finset.univ : Finset (Fin m))
  exact Set.Subset.antisymm hsubset_left hsubset_right

/-- Helper for Theorem 19.6: the empty set in `ℝ^n` is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_empty_set
    {n : ℕ} :
    IsPolyhedralConvexSet n (∅ : Set (Fin n → ℝ)) := by
  classical
  let ι : Type := PUnit
  let b : ι → Fin n → ℝ := fun _ => 0
  let β : ι → ℝ := fun _ => -1
  refine ⟨ι, inferInstance, b, β, ?_⟩
  ext x
  constructor
  · intro hx
    exact False.elim (Set.notMem_empty x hx)
  · intro hx
    have hx' : x ∈ closedHalfSpaceLE n (b PUnit.unit) (β PUnit.unit) := by
      exact Set.mem_iInter.1 hx PUnit.unit
    have hfalse : (0 : ℝ) ≤ -1 := by
      simpa [closedHalfSpaceLE, b, β] using hx'
    linarith

/-- Helper for Theorem 19.6: when the index set is `Fin 0`, the closed convex hull of
the union is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_emptyClosureConvexHull_fin0
    {n : ℕ} {C : Fin 0 → Set (Fin n → ℝ)} :
    IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i : Fin 0, C i))) := by
  have hempty : (⋃ i : Fin 0, C i) = (∅ : Set (Fin n → ℝ)) := by
    ext x
    simp
  have hclosure_empty :
      closure (convexHull ℝ (⋃ i : Fin 0, C i)) = (∅ : Set (Fin n → ℝ)) := by
    simp
  simpa [hclosure_empty] using
    (helperForTheorem_19_6_polyhedral_empty_set (n := n))

/-- Helper for Theorem 19.6: transporting nonemptiness from `Fin n → ℝ` to
`EuclideanSpace ℝ (Fin n)` via `EuclideanSpace.equiv.symm`. -/
lemma helperForTheorem_19_6_nonempty_transport_toEuclidean
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_nonempty : C.Nonempty) :
    (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm) '' C).Nonempty := by
  rcases hC_nonempty with ⟨x, hx⟩
  exact ⟨(EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm x, ⟨x, hx, rfl⟩⟩

/-- Helper for Theorem 19.6: transporting closedness from `Fin n → ℝ` to
`EuclideanSpace ℝ (Fin n)` via `EuclideanSpace.equiv.symm`. -/
lemma helperForTheorem_19_6_closed_transport_toEuclidean
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_closed : IsClosed C) :
    IsClosed (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm) '' C) := by
  simpa using
    (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.toHomeomorph).isClosed_image).2
      hC_closed

/-- Helper for Theorem 19.6: transporting convexity from `Fin n → ℝ` to
`EuclideanSpace ℝ (Fin n)` via `EuclideanSpace.equiv.symm`. -/
lemma helperForTheorem_19_6_convex_transport_toEuclidean
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_convex : Convex ℝ C) :
    Convex ℝ (((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm) '' C) := by
  simpa using
    hC_convex.linear_image ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm.toLinearMap)

/-- Helper for Theorem 19.6: explicit coordinate identities between the `Fin` model
and `EuclideanSpace` via `EuclideanSpace.equiv`. -/
lemma helperForTheorem_19_6_finEuclidean_firstTail_bridge
    {n : ℕ} :
    let eNp1 : (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1)) :=
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))).symm
    let coordsE : EuclideanSpace ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ) :=
      EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (n + 1))
    let firstE : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
      fun v => coordsE v 0
    let tailE : EuclideanSpace ℝ (Fin (n + 1)) → (Fin n → ℝ) :=
      fun v i => coordsE v (Fin.succ i)
    (∀ v, firstE (eNp1 v) = v 0) ∧
      (∀ v, tailE (eNp1 v) = fun i => v (Fin.succ i)) := by
  intro eNp1 coordsE firstE tailE
  constructor
  · intro v
    simp [firstE, coordsE, eNp1]
  · intro v
    funext i
    simp [tailE, coordsE, eNp1]

/-- Helper for Theorem 19.6: the lifted slice `{v | v₀ = 1, tail v ∈ C}` is nonempty
whenever `C` is nonempty. -/
lemma helperForTheorem_19_6_nonempty_liftedSlice
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_nonempty : C.Nonempty) :
    ({v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C}).Nonempty := by
  rcases hC_nonempty with ⟨x, hx⟩
  refine ⟨Fin.cases (1 : ℝ) x, ?_⟩
  constructor
  · simp
  · simpa using hx

/-- Helper for Theorem 19.6: polyhedrality of a base set `C` implies polyhedrality of the
lifted slice `{v | v₀ = 1, tail v ∈ C}`. -/
lemma helperForTheorem_19_6_polyhedral_liftedSlice
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hC_polyhedral : IsPolyhedralConvexSet n C) :
    IsPolyhedralConvexSet (n + 1)
      {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C} := by
  rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces n C).1 hC_polyhedral with
    ⟨k, b, β, hCeq⟩
  let aEq : Fin 1 → Fin (n + 1) → ℝ :=
    fun _ => Fin.cases (1 : ℝ) (fun _ : Fin n => 0)
  let αEq : Fin 1 → ℝ := fun _ => 1
  let bIneq : Fin k → Fin (n + 1) → ℝ := fun r => Fin.cases (0 : ℝ) (b r)
  let βIneq : Fin k → ℝ := β
  have hpoly_system :
      IsPolyhedralConvexSet (n + 1)
        {v : Fin (n + 1) → ℝ |
          (∀ t, v ⬝ᵥ aEq t = αEq t) ∧
            (∀ r, v ⬝ᵥ bIneq r ≤ βIneq r)} := by
    simpa [aEq, αEq, bIneq, βIneq] using
      (polyhedralConvexSet_solutionSet_linearEq_and_inequalities
        (n + 1) 1 k aEq αEq bIneq βIneq)
  have htarget_eq :
      {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C} =
        {v : Fin (n + 1) → ℝ |
          (∀ t, v ⬝ᵥ aEq t = αEq t) ∧
            (∀ r, v ⬝ᵥ bIneq r ≤ βIneq r)} := by
    ext v
    simp [hCeq, aEq, αEq, bIneq, βIneq, dotProduct, Fin.sum_univ_succ, closedHalfSpaceLE]
  simpa [htarget_eq] using hpoly_system

/-- Helper for Theorem 19.6: every point-generator belongs to its mixed convex hull. -/
lemma helperForTheorem_19_6_points_subset_mixedConvexHull
    {d : ℕ} {S₀ S₁ : Set (Fin d → ℝ)} :
    S₀ ⊆ mixedConvexHull (n := d) S₀ S₁ := by
  intro x hx
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hCprop :
      Convex ℝ C ∧ S₀ ⊆ C ∧
        (∀ ⦃dir⦄, dir ∈ S₁ → ∀ ⦃y⦄, y ∈ C → ∀ t : ℝ, 0 ≤ t → y + t • dir ∈ C) := by
    simpa [mixedConvexHull] using hC
  exact hCprop.2.1 hx

/-- Helper for Theorem 19.6: every direction-generator is a recession direction of the mixed
convex hull generated by the same data. -/
lemma helperForTheorem_19_6_directions_subset_recessionCone_mixedConvexHull
    {d : ℕ} {S₀ S₁ : Set (Fin d → ℝ)} :
    S₁ ⊆ Set.recessionCone (mixedConvexHull (n := d) S₀ S₁) := by
  intro dir hdir x hx t ht
  refine (Set.mem_sInter).2 ?_
  intro C hC
  have hCprop :
      Convex ℝ C ∧ S₀ ⊆ C ∧
        (∀ ⦃e⦄, e ∈ S₁ → ∀ ⦃y⦄, y ∈ C → ∀ s : ℝ, 0 ≤ s → y + s • e ∈ C) := by
    simpa [mixedConvexHull] using hC
  have hxC : x ∈ C := (Set.mem_sInter).1 hx C hC
  exact hCprop.2.2 hdir hxC t ht

/-- Helper for Theorem 19.6: every recession direction of a nonempty set lies in the
closure of the convex cone generated by that set. -/
lemma helperForTheorem_19_6_recessionDirection_mem_closure_convexConeHull_of_nonempty
    {d : ℕ} {C : Set (Fin d → ℝ)}
    (hC_nonempty : C.Nonempty)
    {dir : Fin d → ℝ}
    (hdir : dir ∈ Set.recessionCone C) :
    dir ∈ closure ((ConvexCone.hull ℝ C : Set (Fin d → ℝ))) := by
  rcases hC_nonempty with ⟨x0, hx0⟩
  have hlim_coeff :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlim_smul :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ) • x0) Filter.atTop (𝓝 ((0 : ℝ) • x0)) :=
    hlim_coeff.smul_const x0
  have hlim :
      Filter.Tendsto (fun n : ℕ => dir + ((n : ℝ)⁻¹ : ℝ) • x0)
        Filter.atTop (𝓝 dir) := by
    have hlim_const : Filter.Tendsto (fun _ : ℕ => dir) Filter.atTop (𝓝 dir) :=
      tendsto_const_nhds
    have hlim_add := hlim_const.add hlim_smul
    simpa [zero_smul] using hlim_add
  have hmem_event :
      ∀ᶠ n : ℕ in Filter.atTop,
        dir + ((n : ℝ)⁻¹ : ℝ) • x0 ∈ (ConvexCone.hull ℝ C : Set (Fin d → ℝ)) := by
    refine Filter.eventually_atTop.2 ?_
    refine ⟨1, ?_⟩
    intro n hn
    have hn_nat_pos : 0 < n := Nat.succ_le_iff.mp hn
    have hn_real_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hn_real_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_real_pos
    have hxn : x0 + (n : ℝ) • dir ∈ C := hdir hx0 hn_real_nonneg
    have hxn_hull : x0 + (n : ℝ) • dir ∈ (ConvexCone.hull ℝ C : Set (Fin d → ℝ)) :=
      ConvexCone.subset_hull hxn
    have h_inv_pos : 0 < ((n : ℝ)⁻¹ : ℝ) := inv_pos.mpr hn_real_pos
    have hsmul_mem :
        ((n : ℝ)⁻¹ : ℝ) • (x0 + (n : ℝ) • dir) ∈
          (ConvexCone.hull ℝ C : Set (Fin d → ℝ)) :=
      (ConvexCone.hull ℝ C).smul_mem h_inv_pos hxn_hull
    have hn_real_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_real_pos
    have hrewrite :
        ((n : ℝ)⁻¹ : ℝ) • (x0 + (n : ℝ) • dir) =
          dir + ((n : ℝ)⁻¹ : ℝ) • x0 := by
      calc
        ((n : ℝ)⁻¹ : ℝ) • (x0 + (n : ℝ) • dir)
            = ((n : ℝ)⁻¹ : ℝ) • x0 +
                (((n : ℝ)⁻¹ : ℝ) * (n : ℝ)) • dir := by
                  simp [smul_add, smul_smul]
        _ = ((n : ℝ)⁻¹ : ℝ) • x0 + (1 : ℝ) • dir := by
              simp [hn_real_ne]
        _ = dir + ((n : ℝ)⁻¹ : ℝ) • x0 := by
              simp [add_comm]
    simpa [hrewrite] using hsmul_mem
  exact mem_closure_of_tendsto hlim hmem_event

/-- Helper for Theorem 19.6: closure of the convex cone generated by a finite mixed hull equals
the cone generated by the union of finite point and direction generators. -/
lemma helperForTheorem_19_6_closure_convexConeHull_eq_cone_of_finiteMixedData
    {d : ℕ} {S₀ S₁ : Set (Fin d → ℝ)}
    (hS₀fin : Set.Finite S₀)
    (hS₁fin : Set.Finite S₁)
    (hS₀ne : S₀.Nonempty) :
    closure ((ConvexCone.hull ℝ (mixedConvexHull (n := d) S₀ S₁) : Set (Fin d → ℝ))) =
      cone d (S₀ ∪ S₁) := by
  let M : Set (Fin d → ℝ) := mixedConvexHull (n := d) S₀ S₁
  have hM_nonempty : M.Nonempty := by
    rcases hS₀ne with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    exact helperForTheorem_19_6_points_subset_mixedConvexHull
      (d := d) (S₀ := S₀) (S₁ := S₁) hx
  have hcone_isConvexCone : IsConvexCone d (cone d (S₀ ∪ S₁)) := by
    simpa [cone_eq_convexConeGenerated (n := d) (S₁ := S₀ ∪ S₁)] using
      (isConvexCone_convexConeGenerated (n := d) (S₁ := S₀ ∪ S₁))
  have hcone_convex : Convex ℝ (cone d (S₀ ∪ S₁)) := hcone_isConvexCone.2
  have hcone_add :
      ∀ x ∈ cone d (S₀ ∪ S₁),
        ∀ y ∈ cone d (S₀ ∪ S₁), x + y ∈ cone d (S₀ ∪ S₁) :=
    isConvexCone_add_closed d (cone d (S₀ ∪ S₁)) hcone_isConvexCone
  have hS₀_subset_cone : S₀ ⊆ cone d (S₀ ∪ S₁) := by
    intro x hx
    have hxray_nonneg : x ∈ rayNonneg d (S₀ ∪ S₁) := by
      refine ⟨x, ?_, 1, by norm_num, ?_⟩
      · exact Or.inl hx
      · simp
    have hxray : x ∈ ray d (S₀ ∪ S₁) := (Set.mem_insert_iff).2 (Or.inr hxray_nonneg)
    simpa [cone, conv] using
      (subset_convexHull (𝕜 := ℝ) (s := ray d (S₀ ∪ S₁)) hxray)
  have hS₁_subset_cone : S₁ ⊆ cone d (S₀ ∪ S₁) := by
    intro x hx
    have hxray_nonneg : x ∈ rayNonneg d (S₀ ∪ S₁) := by
      refine ⟨x, ?_, 1, by norm_num, ?_⟩
      · exact Or.inr hx
      · simp
    have hxray : x ∈ ray d (S₀ ∪ S₁) := (Set.mem_insert_iff).2 (Or.inr hxray_nonneg)
    simpa [cone, conv] using
      (subset_convexHull (𝕜 := ℝ) (s := ray d (S₀ ∪ S₁)) hxray)
  have hrecedes :
      ∀ ⦃dir⦄, dir ∈ S₁ → ∀ ⦃x⦄, x ∈ cone d (S₀ ∪ S₁) →
        ∀ t : ℝ, 0 ≤ t → x + t • dir ∈ cone d (S₀ ∪ S₁) := by
    intro dir hdir x hx t ht
    by_cases ht0 : t = 0
    · subst ht0
      simpa using hx
    · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have htdir : t • dir ∈ cone d (S₀ ∪ S₁) :=
        hcone_isConvexCone.1 dir (hS₁_subset_cone hdir) t htpos
      exact hcone_add x hx (t • dir) htdir
  have hM_subset_cone : M ⊆ cone d (S₀ ∪ S₁) := by
    refine mixedConvexHull_subset_of_convex_of_subset_of_recedes
      (n := d) (S₀ := S₀) (S₁ := S₁)
      (Ccand := cone d (S₀ ∪ S₁)) hcone_convex hS₀_subset_cone hrecedes
  have hcone_closed : IsClosed (cone d (S₀ ∪ S₁)) :=
    helperForTheorem_19_1_isClosed_cone_of_finite_generators
      (m := d) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
  have hsmul_mem_cone :
      ∀ (r : ℝ), 0 < r → ∀ x ∈ cone d (S₀ ∪ S₁), r • x ∈ cone d (S₀ ∪ S₁) := by
    intro r hr x hx
    exact hcone_isConvexCone.1 x hx r hr
  have hadd_mem_cone :
      ∀ x ∈ cone d (S₀ ∪ S₁), ∀ y ∈ cone d (S₀ ∪ S₁), x + y ∈ cone d (S₀ ∪ S₁) :=
    hcone_add
  let Ccone : ConvexCone ℝ (Fin d → ℝ) :=
    ConvexCone.mk (cone d (S₀ ∪ S₁)) hsmul_mem_cone hadd_mem_cone
  have hHullM_subset_cone :
      (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) ⊆ cone d (S₀ ∪ S₁) := by
    have hHullM_subset_Ccone :
        (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) ⊆ (Ccone : Set (Fin d → ℝ)) :=
      ConvexCone.hull_min (s := M) (C := Ccone) hM_subset_cone
    simpa [Ccone] using hHullM_subset_Ccone
  have hsubset_left :
      closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) ⊆ cone d (S₀ ∪ S₁) := by
    exact closure_minimal hHullM_subset_cone hcone_closed
  have hS₀_subset_closureHull :
      S₀ ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro x hx
    have hxM : x ∈ M :=
      helperForTheorem_19_6_points_subset_mixedConvexHull
        (d := d) (S₀ := S₀) (S₁ := S₁) hx
    exact subset_closure (ConvexCone.subset_hull hxM)
  have hS₁_subset_closureHull :
      S₁ ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro dir hdir
    have hdir_rec : dir ∈ Set.recessionCone M :=
      helperForTheorem_19_6_directions_subset_recessionCone_mixedConvexHull
        (d := d) (S₀ := S₀) (S₁ := S₁) hdir
    exact helperForTheorem_19_6_recessionDirection_mem_closure_convexConeHull_of_nonempty
      (d := d) (C := M) hM_nonempty hdir_rec
  have hUnion_subset_closureHull :
      S₀ ∪ S₁ ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro x hx
    rcases hx with hx0 | hx1
    · exact hS₀_subset_closureHull hx0
    · exact hS₁_subset_closureHull hx1
  let Ccl : ConvexCone ℝ (Fin d → ℝ) := (ConvexCone.hull ℝ M).closure
  have hHullUnion_subset_closure :
      (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin d → ℝ)) ⊆
        closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    have hHullUnion_subset_Ccl :
        (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin d → ℝ)) ⊆ (Ccl : Set (Fin d → ℝ)) :=
      ConvexCone.hull_min (s := S₀ ∪ S₁) (C := Ccl) hUnion_subset_closureHull
    simpa [Ccl] using hHullUnion_subset_Ccl
  have hzero_mem_closureHullM :
      (0 : Fin d → ℝ) ∈ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    rcases hM_nonempty with ⟨x, hxM⟩
    have hxHull : x ∈ (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) := ConvexCone.subset_hull hxM
    have hlim_coeff0 :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ)) Filter.atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim0 :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℝ) • x) Filter.atTop (𝓝 (0 : Fin d → ℝ)) := by
      have hsmul := hlim_coeff0.smul_const x
      simpa [zero_smul] using hsmul
    have hmem_event0 :
        ∀ᶠ n : ℕ in Filter.atTop, ((n : ℝ)⁻¹ : ℝ) • x ∈ (ConvexCone.hull ℝ M : Set (Fin d → ℝ)) := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨1, ?_⟩
      intro n hn
      have hn_nat_pos : 0 < n := Nat.succ_le_iff.mp hn
      have hn_real_pos : 0 < (n : ℝ) := by
        exact_mod_cast hn_nat_pos
      have h_inv_pos : 0 < ((n : ℝ)⁻¹ : ℝ) := inv_pos.mpr hn_real_pos
      exact (ConvexCone.hull ℝ M).smul_mem h_inv_pos hxHull
    exact mem_closure_of_tendsto hlim0 hmem_event0
  have hsubset_right :
      cone d (S₀ ∪ S₁) ⊆ closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) := by
    intro x hx
    have hx' : x ∈ convexConeGenerated d (S₀ ∪ S₁) := by
      simpa [cone_eq_convexConeGenerated (n := d) (S₁ := S₀ ∪ S₁)] using hx
    have hx'' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin d → ℝ)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hx'
    rcases hx'' with rfl | hxHull
    · exact hzero_mem_closureHullM
    · exact hHullUnion_subset_closure hxHull
  have hEq : closure ((ConvexCone.hull ℝ M : Set (Fin d → ℝ))) = cone d (S₀ ∪ S₁) :=
    Set.Subset.antisymm hsubset_left hsubset_right
  simpa [M] using hEq

/-- Helper for Theorem 19.6: closure of the convex cone generated by a nonempty polyhedral set
is polyhedral. -/
lemma helperForTheorem_19_6_polyhedral_closure_convexConeHull_of_polyhedral
    {d : ℕ} {S : Set (Fin d → ℝ)}
    (hS_nonempty : S.Nonempty)
    (hS_polyhedral : IsPolyhedralConvexSet d S) :
    IsPolyhedralConvexSet d (closure ((ConvexCone.hull ℝ S : Set (Fin d → ℝ)))) := by
  have hS_conv : Convex ℝ S :=
    helperForTheorem_19_1_polyhedral_isConvex (n := d) (C := S) hS_polyhedral
  have hTFAE :
      [IsPolyhedralConvexSet d S,
        (IsClosed S ∧ {C' : Set (Fin d → ℝ) | IsFace (𝕜 := ℝ) S C'}.Finite),
        IsFinitelyGeneratedConvexSet d S].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := d) (C := S) hS_conv
  have hS_fg : IsFinitelyGeneratedConvexSet d S :=
    (hTFAE.out 0 2).1 hS_polyhedral
  rcases hS_fg with ⟨S₀, S₁, hS₀fin, hS₁fin, hSeq⟩
  have hMixed_nonempty : (mixedConvexHull (n := d) S₀ S₁).Nonempty := by
    rcases hS_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [hSeq] using hx
  have hS₀ne : S₀.Nonempty :=
    helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
      (n := d) (S₀ := S₀) (S₁ := S₁) hMixed_nonempty
  have hclosure_eq :
      closure ((ConvexCone.hull ℝ S : Set (Fin d → ℝ))) = cone d (S₀ ∪ S₁) := by
    calc
      closure ((ConvexCone.hull ℝ S : Set (Fin d → ℝ))) =
          closure ((ConvexCone.hull ℝ (mixedConvexHull (n := d) S₀ S₁) : Set (Fin d → ℝ))) := by
            simp [hSeq]
      _ = cone d (S₀ ∪ S₁) :=
        helperForTheorem_19_6_closure_convexConeHull_eq_cone_of_finiteMixedData
          (d := d) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hcone_poly : IsPolyhedralConvexSet d (cone d (S₀ ∪ S₁)) :=
    helperForTheorem_19_1_cone_polyhedral_of_finite_generators
      (m := d) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
  simpa [hclosure_eq] using hcone_poly

/-- Helper for Theorem 19.6: transporting `convexHull` of a finite union through the
Euclidean coordinate equivalence. -/
lemma helperForTheorem_19_6_convexHull_iUnion_image_linearEquiv
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)} :
    let eN : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
    let CE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin n)) :=
      fun i => eN '' C i
    eN '' (convexHull ℝ (⋃ i, C i)) = convexHull ℝ (⋃ i, CE i) := by
  intro eN CE
  calc
    eN '' (convexHull ℝ (⋃ i, C i)) = convexHull ℝ (eN '' (⋃ i, C i)) := by
      simpa using (LinearMap.image_convexHull (f := eN.toLinearMap) (s := ⋃ i, C i))
    _ = convexHull ℝ (⋃ i, CE i) := by
      congr 1
      simpa [CE] using (Set.image_iUnion (f := eN) (s := fun i => C i))

/-- Helper for Theorem 19.6: additive equivalences commute with finite Minkowski sums. -/
lemma helperForTheorem_19_6_image_finsetSum_addEquiv
    {α β ι : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Fintype ι]
    (e : α ≃+ β) (A : ι → Set α) :
    e '' (∑ i, A i) = ∑ i, (e '' A i) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := A) (a := x)).1 hx with
      ⟨z, hzmem, hzsum⟩
    refine
      (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := fun i => e '' A i) (a := e x)).2 ?_
    refine ⟨fun i => e (z i), ?_, ?_⟩
    · intro i hi
      exact ⟨z i, hzmem (i := i) hi, rfl⟩
    · simpa using congrArg e hzsum
  · intro hy
    rcases (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := fun i => e '' A i)
      (a := y)).1 hy with ⟨z, hzmem, hzsum⟩
    have hzpre : ∀ i, ∃ x, x ∈ A i ∧ e x = z i := by
      intro i
      rcases hzmem (i := i) (by simp) with ⟨x, hxA, hxz⟩
      exact ⟨x, hxA, hxz⟩
    choose x hxA hxz using hzpre
    have hxsum_mem : (∑ i, x i) ∈ ∑ i, A i := by
      refine (Set.mem_finset_sum (t := (Finset.univ : Finset ι)) (f := A) (a := ∑ i, x i)).2 ?_
      refine ⟨x, ?_, rfl⟩
      intro i hi
      exact hxA i
    refine ⟨∑ i, x i, hxsum_mem, ?_⟩
    calc
      e (∑ i, x i) = ∑ i, e (x i) := by simp
      _ = ∑ i, z i := by simp [hxz]
      _ = y := hzsum

/-- Helper for Theorem 19.6: additive equivalences commute with finite Minkowski sums under
preimage. -/
lemma helperForTheorem_19_6_preimage_finsetSum_addEquiv
    {α β ι : Type*}
    [AddCommMonoid α] [AddCommMonoid β] [Fintype ι]
    (e : α ≃+ β) (A : ι → Set β) :
    e ⁻¹' (∑ i, A i) = ∑ i, (e ⁻¹' A i) := by
  classical
  have hpreimage_eq_image :
      e ⁻¹' (∑ i, A i) = e.symm '' (∑ i, A i) := by
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hpreimage_eq_image_each :
      (fun i => e ⁻¹' A i) = (fun i => e.symm '' A i) := by
    funext i
    ext x
    constructor
    · intro hx
      exact ⟨e x, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  calc
    e ⁻¹' (∑ i, A i) = e.symm '' (∑ i, A i) := hpreimage_eq_image
    _ = ∑ i, e.symm '' A i := by
      simpa using
        (helperForTheorem_19_6_image_finsetSum_addEquiv (e := e.symm) (A := A))
    _ = ∑ i, e ⁻¹' A i := by
      simp [hpreimage_eq_image_each]

/-- Helper for Theorem 19.6: the weighted branch union in the `tail` coordinate transports
through the Euclidean coordinate linear equivalence. -/
lemma helperForTheorem_19_6_image_weightedUnion_linearEquiv
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (eN : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : Fin (Nat.succ m) → ℝ) :
    eN ''
        (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) =
      ∑ i,
        (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i))) := by
  have hbranch :
      ∀ i,
        eN '' (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) =
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i))) := by
    intro i
    by_cases h0 : lam i = 0
    · simpa [h0] using
        (recessionCone_image_linearEquiv (e := eN) (C := C i)).symm
    · simp [h0]
  calc
    eN '' (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) =
        ∑ i, eN '' (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) := by
          simpa using
            (helperForTheorem_19_6_image_finsetSum_addEquiv
              (e := eN.toAddEquiv)
              (A := fun i => if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))
    _ = ∑ i,
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i))) := by
          simp [hbranch]

/-- Helper for Theorem 19.6: transporting the weighted finite union formula back through a linear
equivalence using preimage. -/
lemma helperForTheorem_19_6_preimage_weightedUnion_linearEquiv
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (eN : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (lam : Fin (Nat.succ m) → ℝ) :
    eN ⁻¹'
        (∑ i,
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i)))) =
      ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) := by
  have himage :=
    helperForTheorem_19_6_image_weightedUnion_linearEquiv
      (n := n) (m := m) (C := C) (eN := eN) (lam := lam)
  calc
    eN ⁻¹'
        (∑ i,
          (if lam i = 0 then Set.recessionCone (eN '' C i) else lam i • (eN '' (C i)))) =
      eN ⁻¹' (eN '' (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
        simp [himage]
    _ = ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)) :=
      Set.preimage_image_eq _ eN.injective

/-- Helper for Theorem 19.6: linear equivalences transport convex-cone hulls through set image. -/
lemma helperForTheorem_19_6_convexConeHull_image_linearEquiv
    {α β : Type*}
    [AddCommMonoid α] [Module ℝ α]
    [AddCommMonoid β] [Module ℝ β]
    (e : α ≃ₗ[ℝ] β) (s : Set α) :
    e '' (ConvexCone.hull ℝ s : Set α) = (ConvexCone.hull ℝ (e '' s) : Set β) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hs_to : s ⊆ (ConvexCone.hull ℝ (e '' s)).comap e.toLinearMap := by
      intro x hx
      exact ConvexCone.subset_hull ⟨x, hx, rfl⟩
    have hhull_to :
        ConvexCone.hull ℝ s ≤ (ConvexCone.hull ℝ (e '' s)).comap e.toLinearMap :=
      ConvexCone.hull_min hs_to
    exact hhull_to hx
  · intro hy
    have himage_subset :
        e '' s ⊆ ((ConvexCone.hull ℝ s).map e.toLinearMap : Set β) := by
      rintro y ⟨x, hx, rfl⟩
      exact ⟨x, ConvexCone.subset_hull hx, rfl⟩
    have hhull_image :
        ConvexCone.hull ℝ (e '' s) ≤ (ConvexCone.hull ℝ s).map e.toLinearMap :=
      ConvexCone.hull_min himage_subset
    exact hhull_image hy

/-- Helper for Theorem 19.6: after casting `Fin.natAdd 1 i` from `Fin (1+n)` to `Fin (n+1)`,
it coincides with `Fin.succ i`. -/
lemma helperForTheorem_19_6_cast_natAdd_one_eq_succ
    {n : ℕ} (i : Fin n) :
    (Fin.cast (Nat.add_comm 1 n) (Fin.natAdd 1 i) : Fin (n + 1)) =
      Fin.succ i := by
  apply Fin.ext
  simp [Fin.natAdd, Fin.succ, Nat.add_comm]

/-- Helper for Theorem 19.6: the tail-coordinate function written with casted `Fin.natAdd 1`
agrees with the usual `Fin.succ` tail function. -/
lemma helperForTheorem_19_6_tail_cast_natAdd_eq_tail_succ
    {n : ℕ} (v : Fin (n + 1) → ℝ) :
    (fun i : Fin n =>
      v (Fin.cast (Nat.add_comm 1 n) (Fin.natAdd 1 i))) =
      (fun i : Fin n => v (Fin.succ i)) := by
  funext i
  rw [helperForTheorem_19_6_cast_natAdd_one_eq_succ]

/-- Helper for Theorem 19.6: for a family indexed by `Fin (m+1)`, the weighted-union formula
for `closure (convexHull (⋃ i, C i))` follows from the lifted-cone closure-sum identity. -/
lemma helperForTheorem_19_6_transport_liftedCone_sliceLemmas_toFinCoord
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_closed : ∀ i, IsClosed (C i))
    (h_convex : ∀ i, Convex ℝ (C i)) :
    let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
      fun v => v
    let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
    let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
      fun v i => coords v (Fin.succ i)
    let C0 : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
    let S0 : Set (Fin (n + 1) → ℝ) := {v | first v = 1 ∧ tail v ∈ C0}
    let K0 : Set (Fin (n + 1) → ℝ) :=
      (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ))
    let S : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
      fun i => {v | first v = 1 ∧ tail v ∈ C i}
    let K : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
      fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
    closure K0 = closure (∑ i, K i) ∧
      (closure C0 =
        {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x}) ∧
      (∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
  classical
  intro coords first tail C0 S0 K0 S K
  let eN : (Fin n → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
  let CE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun i => eN '' C i
  have hCE_nonempty : ∀ i, (CE i).Nonempty := by
    intro i
    simpa [CE, eN] using
      (helperForTheorem_19_6_nonempty_transport_toEuclidean (n := n) (C := C i) (h_nonempty i))
  have hCE_closed : ∀ i, IsClosed (CE i) := by
    intro i
    simpa [CE, eN] using
      (helperForTheorem_19_6_closed_transport_toEuclidean (n := n) (C := C i) (h_closed i))
  have hCE_convex : ∀ i, Convex ℝ (CE i) := by
    intro i
    simpa [CE, eN] using
      (helperForTheorem_19_6_convex_transport_toEuclidean (n := n) (C := C i) (h_convex i))
  have hC0_image :
      eN '' C0 = convexHull ℝ (⋃ i, CE i) := by
    simpa [C0, CE, eN] using
      (helperForTheorem_19_6_convexHull_iUnion_image_linearEquiv (n := n) (m := m) (C := C))
  have hweighted_image :
      ∀ lam : Fin (Nat.succ m) → ℝ,
        eN ''
            (∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) =
          ∑ i,
            (if lam i = 0 then Set.recessionCone (CE i) else lam i • (CE i)) := by
    intro lam
    simpa [CE] using
      (helperForTheorem_19_6_image_weightedUnion_linearEquiv
        (n := n) (m := m) (C := C) (eN := eN.toLinearEquiv) (lam := lam))
  have hclosureE :
      let C0E : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (⋃ i, CE i)
      let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
        EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
      let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
      let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
            (fun i => coordsE v (Fin.natAdd 1 i))
      let S0E : Set (EuclideanSpace ℝ (Fin (1 + n))) := {v | firstE v = 1 ∧ tailE v ∈ C0E}
      let K0E : Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        (ConvexCone.hull ℝ S0E : Set (EuclideanSpace ℝ (Fin (1 + n))))
      let SE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => {v | firstE v = 1 ∧ tailE v ∈ CE i}
      let KE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => (ConvexCone.hull ℝ (SE i) : Set (EuclideanSpace ℝ (Fin (1 + n))))
      closure K0E = closure (∑ i, KE i) := by
    simpa [CE] using
      (closure_cone_over_convexHull_eq_closure_sum_cones_succ
        (n := n) (m := m) (C := CE) hCE_nonempty hCE_convex)
  have hsliceE :
      let C0E : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (⋃ i, CE i)
      let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
        EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
      let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
      let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
            (fun i => coordsE v (Fin.natAdd 1 i))
      let S0E : Set (EuclideanSpace ℝ (Fin (1 + n))) := {v | firstE v = 1 ∧ tailE v ∈ C0E}
      let K0E : Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        (ConvexCone.hull ℝ S0E : Set (EuclideanSpace ℝ (Fin (1 + n))))
      closure C0E =
        {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
    have hC0E_convex : Convex ℝ (convexHull ℝ (⋃ i, CE i)) :=
      convex_convexHull (𝕜 := ℝ) (s := ⋃ i, CE i)
    simpa [CE] using
      (closure_C0_eq_first_one_slice_closure_lifted_cone (n := n)
        (C0 := convexHull ℝ (⋃ i, CE i)) hC0E_convex)
  have hmemE :
      let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
        EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
      let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
      let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
        fun v =>
          (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
            (fun i => coordsE v (Fin.natAdd 1 i))
      let SE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => {v | firstE v = 1 ∧ tailE v ∈ CE i}
      let KE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
        fun i => (ConvexCone.hull ℝ (SE i) : Set (EuclideanSpace ℝ (Fin (1 + n))))
      ∀ v, firstE v = 1 →
        (v ∈ ∑ i, closure (KE i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tailE v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (CE i) else lam i • (CE i))) := by
    simpa [CE] using
      (mem_sum_closure_cones_first_eq_one_iff
        (n := n) (m := Nat.succ m) (C := CE) hCE_nonempty hCE_closed hCE_convex)
  let idxNp1 : Fin (n + 1) ≃ Fin (1 + n) :=
    { toFun := fun i => ⟨i.1, by omega⟩
      invFun := fun i => ⟨i.1, by omega⟩
      left_inv := by
        intro i
        ext
        rfl
      right_inv := by
        intro i
        ext
        rfl }
  let eNp1Cast : (Fin (n + 1) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (1 + n)) :=
    (((LinearEquiv.funCongrLeft ℝ ℝ idxNp1).symm).toContinuousLinearEquiv).trans
      ((EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))).symm)
  let C0E : Set (EuclideanSpace ℝ (Fin n)) := convexHull ℝ (⋃ i, CE i)
  let coordsE : EuclideanSpace ℝ (Fin (1 + n)) → (Fin (1 + n) → ℝ) :=
    EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin (1 + n))
  let firstE : EuclideanSpace ℝ (Fin (1 + n)) → ℝ := fun v => coordsE v 0
  let tailE : EuclideanSpace ℝ (Fin (1 + n)) → EuclideanSpace ℝ (Fin n) :=
    fun v =>
      (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)).symm
        (fun i => coordsE v (Fin.natAdd 1 i))
  let S0E : Set (EuclideanSpace ℝ (Fin (1 + n))) := {v | firstE v = 1 ∧ tailE v ∈ C0E}
  let K0E : Set (EuclideanSpace ℝ (Fin (1 + n))) :=
    (ConvexCone.hull ℝ S0E : Set (EuclideanSpace ℝ (Fin (1 + n))))
  let SE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
    fun i => {v | firstE v = 1 ∧ tailE v ∈ CE i}
  let KE : Fin (Nat.succ m) → Set (EuclideanSpace ℝ (Fin (1 + n))) :=
    fun i => (ConvexCone.hull ℝ (SE i) : Set (EuclideanSpace ℝ (Fin (1 + n))))
  let weightedC : (Fin (Nat.succ m) → ℝ) → Set (Fin n → ℝ) :=
    fun lam => ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))
  let weightedCE : (Fin (Nat.succ m) → ℝ) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun lam => ∑ i, (if lam i = 0 then Set.recessionCone (CE i) else lam i • (CE i))
  have hclosureE' : closure K0E = closure (∑ i, KE i) := by
    simpa [C0E, coordsE, firstE, tailE, S0E, K0E, SE, KE] using hclosureE
  have hsliceE' :
      closure C0E = {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
    simpa [C0E, coordsE, firstE, tailE, S0E, K0E] using hsliceE
  have hmemE' :
      ∀ v, firstE v = 1 →
        (v ∈ ∑ i, closure (KE i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tailE v ∈ weightedCE lam) := by
    simpa [coordsE, firstE, tailE, SE, KE, weightedCE] using hmemE
  have hfirst_e : ∀ v, firstE (eNp1Cast v) = first v := by
    intro v
    simp [firstE, first, coordsE, coords, eNp1Cast, idxNp1]
  have hfirst_symm : ∀ w, first (eNp1Cast.symm w) = firstE w := by
    intro w
    have h := hfirst_e (eNp1Cast.symm w)
    simpa using h
  have htail_e : ∀ v, tailE (eNp1Cast v) = eN (tail v) := by
    intro v
    apply eN.symm.injective
    funext i
    simp [tailE, coordsE, eNp1Cast, idxNp1, eN, tail, coords]
    have hidx :
        ((⟨1 + (i : ℕ), by omega⟩ : Fin (n + 1))) = Fin.succ i := by
      apply Fin.ext
      simp [Fin.succ, Nat.add_comm]
    simp [hidx]
  have htail_symm : ∀ w, tail (eNp1Cast.symm w) = eN.symm (tailE w) := by
    intro w
    have h := htail_e (eNp1Cast.symm w)
    have h' : tailE w = eN (tail (eNp1Cast.symm w)) := by
      simpa using h
    have h'' := congrArg eN.symm h'
    simpa using h''.symm
  have hCE_pre : ∀ i, eN ⁻¹' CE i = C i := by
    intro i
    calc
      eN ⁻¹' CE i = eN ⁻¹' (eN '' C i) := by simp [CE]
      _ = C i := Set.preimage_image_eq _ eN.injective
  have hC0_pre : eN ⁻¹' C0E = C0 := by
    calc
      eN ⁻¹' C0E = eN ⁻¹' (eN '' C0) := by
        simpa [C0E] using congrArg (fun s : Set (EuclideanSpace ℝ (Fin n)) => eN ⁻¹' s) hC0_image.symm
      _ = C0 := Set.preimage_image_eq _ eN.injective
  have hS0_image : eNp1Cast '' S0 = S0E := by
    ext w
    constructor
    · rintro ⟨v, hvS0, rfl⟩
      rcases hvS0 with ⟨hv1, hvC0⟩
      refine ⟨by simpa [hfirst_e v] using hv1, ?_⟩
      have htail_pre : tail v ∈ eN ⁻¹' C0E := by
        simpa [hC0_pre] using hvC0
      simpa [Set.mem_preimage, htail_e v] using htail_pre
    · intro hw
      refine ⟨eNp1Cast.symm w, ?_, by simp⟩
      rcases hw with ⟨hw1, hwC0⟩
      refine ⟨(hfirst_symm w).trans hw1, ?_⟩
      have htail_in : eN.symm (tailE w) ∈ C0 := by
        have htail_pre : eN.symm (tailE w) ∈ eN ⁻¹' C0E := by
          simpa [Set.mem_preimage] using hwC0
        simpa [hC0_pre] using htail_pre
      simpa [htail_symm w] using htail_in
  have hSE_image : ∀ i, eNp1Cast '' S i = SE i := by
    intro i
    ext w
    constructor
    · rintro ⟨v, hvS, rfl⟩
      rcases hvS with ⟨hv1, hvCi⟩
      refine ⟨by simpa [hfirst_e v] using hv1, ?_⟩
      have htail_pre : tail v ∈ eN ⁻¹' CE i := by
        simpa [hCE_pre i] using hvCi
      simpa [Set.mem_preimage, htail_e v] using htail_pre
    · intro hw
      refine ⟨eNp1Cast.symm w, ?_, by simp⟩
      rcases hw with ⟨hw1, hwCi⟩
      refine ⟨(hfirst_symm w).trans hw1, ?_⟩
      have htail_in : eN.symm (tailE w) ∈ C i := by
        have htail_pre : eN.symm (tailE w) ∈ eN ⁻¹' CE i := by
          simpa [Set.mem_preimage] using hwCi
        simpa [hCE_pre i] using htail_pre
      simpa [htail_symm w] using htail_in
  have hK0_image : eNp1Cast '' K0 = K0E := by
    calc
      eNp1Cast '' K0 = eNp1Cast '' (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ)) := by rfl
      _ = (ConvexCone.hull ℝ (eNp1Cast '' S0) : Set (EuclideanSpace ℝ (Fin (1 + n)))) := by
        simpa using
          (helperForTheorem_19_6_convexConeHull_image_linearEquiv
            (e := eNp1Cast.toLinearEquiv) (s := S0))
      _ = K0E := by simp [K0E, hS0_image]
  have hKE_image : ∀ i, eNp1Cast '' K i = KE i := by
    intro i
    calc
      eNp1Cast '' K i = eNp1Cast '' (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ)) := by rfl
      _ = (ConvexCone.hull ℝ (eNp1Cast '' S i) : Set (EuclideanSpace ℝ (Fin (1 + n)))) := by
        simpa using
          (helperForTheorem_19_6_convexConeHull_image_linearEquiv
            (e := eNp1Cast.toLinearEquiv) (s := S i))
      _ = KE i := by simp [KE, hSE_image i]
  have hK0_pre : eNp1Cast ⁻¹' K0E = K0 := by
    calc
      eNp1Cast ⁻¹' K0E = eNp1Cast ⁻¹' (eNp1Cast '' K0) := by simp [hK0_image]
      _ = K0 := Set.preimage_image_eq _ eNp1Cast.injective
  have hKE_pre : ∀ i, eNp1Cast ⁻¹' KE i = K i := by
    intro i
    calc
      eNp1Cast ⁻¹' KE i = eNp1Cast ⁻¹' (eNp1Cast '' K i) := by simp [hKE_image i]
      _ = K i := Set.preimage_image_eq _ eNp1Cast.injective
  have hpreK0closure : eNp1Cast ⁻¹' closure K0E = closure K0 := by
    calc
      eNp1Cast ⁻¹' closure K0E = closure (eNp1Cast ⁻¹' K0E) := by
        simpa using eNp1Cast.preimage_closure K0E
      _ = closure K0 := by simp [hK0_pre]
  have hpreC0closure : eN ⁻¹' closure C0E = closure C0 := by
    calc
      eN ⁻¹' closure C0E = closure (eN ⁻¹' C0E) := by
        simpa using eN.preimage_closure C0E
      _ = closure C0 := by simp [hC0_pre]
  have hpre_sum : eNp1Cast ⁻¹' (∑ i, KE i) = ∑ i, K i := by
    calc
      eNp1Cast ⁻¹' (∑ i, KE i) = ∑ i, (eNp1Cast ⁻¹' KE i) := by
        simpa using
          (helperForTheorem_19_6_preimage_finsetSum_addEquiv
            (e := eNp1Cast.toLinearEquiv.toAddEquiv)
            (A := KE))
      _ = ∑ i, K i := by
        simp [hKE_pre]
  have hpre_sum_closure : eNp1Cast ⁻¹' (∑ i, closure (KE i)) = ∑ i, closure (K i) := by
    calc
      eNp1Cast ⁻¹' (∑ i, closure (KE i)) = ∑ i, (eNp1Cast ⁻¹' closure (KE i)) := by
        simpa using
          (helperForTheorem_19_6_preimage_finsetSum_addEquiv
            (e := eNp1Cast.toLinearEquiv.toAddEquiv)
            (A := fun i => closure (KE i)))
      _ = ∑ i, closure (eNp1Cast ⁻¹' KE i) := by
        simp [eNp1Cast.preimage_closure]
      _ = ∑ i, closure (K i) := by
        simp [hKE_pre]
  have hclosure_main : closure K0 = closure (∑ i, K i) := by
    have hpre := congrArg (fun s : Set (EuclideanSpace ℝ (Fin (1 + n))) => eNp1Cast ⁻¹' s) hclosureE'
    simpa [hpreK0closure, eNp1Cast.preimage_closure, hpre_sum] using hpre
  have hslice_main :
      closure C0 = {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
    ext x
    constructor
    · intro hx
      have hxE : eN x ∈ closure C0E := by
        have hxpre : x ∈ eN ⁻¹' closure C0E := by
          simpa [hpreC0closure] using hx
        simpa [Set.mem_preimage] using hxpre
      have hxE' : eN x ∈ {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
        simpa [hsliceE'] using hxE
      rcases hxE' with ⟨vE, hvEcl, hvE1, hvEtail⟩
      have hvcl : eNp1Cast.symm vE ∈ closure K0 := by
        have hvpre : eNp1Cast.symm vE ∈ eNp1Cast ⁻¹' closure K0E := by
          simpa [Set.mem_preimage] using hvEcl
        simpa [hpreK0closure] using hvpre
      refine ⟨eNp1Cast.symm vE, hvcl, (hfirst_symm vE).trans hvE1, ?_⟩
      apply eN.injective
      calc
        eN (tail (eNp1Cast.symm vE)) = tailE vE := by
          simpa using congrArg eN (htail_symm vE)
        _ = eN x := hvEtail
    · rintro ⟨v, hvcl, hv1, hvx⟩
      have hvEcl : eNp1Cast v ∈ closure K0E := by
        have hvpre : v ∈ eNp1Cast ⁻¹' closure K0E := by
          simpa [hpreK0closure] using hvcl
        simpa [Set.mem_preimage] using hvpre
      have hvE1 : firstE (eNp1Cast v) = 1 := by
        simpa [hfirst_e v] using hv1
      have hvEtail : tailE (eNp1Cast v) = eN x := by
        calc
          tailE (eNp1Cast v) = eN (tail v) := htail_e v
          _ = eN x := by simp [hvx]
      have hxE' : eN x ∈ {x | ∃ v, v ∈ closure K0E ∧ firstE v = 1 ∧ tailE v = x} := by
        exact ⟨eNp1Cast v, hvEcl, hvE1, hvEtail⟩
      have hxE : eN x ∈ closure C0E := by
        simpa [hsliceE'] using hxE'
      have hxpre : x ∈ eN ⁻¹' closure C0E := by
        simpa [Set.mem_preimage] using hxE
      simpa [hpreC0closure] using hxpre
  have hweighted_pre : ∀ lam, eN ⁻¹' weightedCE lam = weightedC lam := by
    intro lam
    simpa [weightedC, weightedCE, CE] using
      (helperForTheorem_19_6_preimage_weightedUnion_linearEquiv
        (n := n) (m := m) (C := C) (eN := eN.toLinearEquiv) (lam := lam))
  have hmem_main :
      ∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈ weightedC lam) := by
    intro v hv1
    have hv1E : firstE (eNp1Cast v) = 1 := by
      simpa [hfirst_e v] using hv1
    have hE := hmemE' (eNp1Cast v) hv1E
    constructor
    · intro hvsum
      have hvpre : v ∈ eNp1Cast ⁻¹' (∑ i, closure (KE i)) := by
        simpa [hpre_sum_closure] using hvsum
      have hvsumE : eNp1Cast v ∈ ∑ i, closure (KE i) := by
        simpa [Set.mem_preimage] using hvpre
      rcases (hE.1 hvsumE) with ⟨lam, hlam_nonneg, hsum_lam, htailE_mem⟩
      have htail_pre : tail v ∈ eN ⁻¹' weightedCE lam := by
        simpa [Set.mem_preimage, htail_e v] using htailE_mem
      have htail_mem : tail v ∈ weightedC lam := by
        simpa [hweighted_pre lam] using htail_pre
      exact ⟨lam, hlam_nonneg, hsum_lam, htail_mem⟩
    · rintro ⟨lam, hlam_nonneg, hsum_lam, htail_mem⟩
      have htail_pre : tail v ∈ eN ⁻¹' weightedCE lam := by
        simpa [hweighted_pre lam] using htail_mem
      have htailE_mem : tailE (eNp1Cast v) ∈ weightedCE lam := by
        simpa [Set.mem_preimage, htail_e v] using htail_pre
      have hvsumE : eNp1Cast v ∈ ∑ i, closure (KE i) :=
        (hE.2 ⟨lam, hlam_nonneg, hsum_lam, htailE_mem⟩)
      have hvpre : v ∈ eNp1Cast ⁻¹' (∑ i, closure (KE i)) := by
        simpa [Set.mem_preimage] using hvsumE
      simpa [hpre_sum_closure] using hvpre
  exact ⟨hclosure_main, hslice_main, by simpa [weightedC] using hmem_main⟩

/-- Helper for Theorem 19.6: for a family indexed by `Fin (m+1)`, the weighted-union formula
for `closure (convexHull (⋃ i, C i))` follows from the lifted-cone closure-sum identity. -/
lemma helperForTheorem_19_6_closure_convexHull_eq_weighted_union_core_noLineal
    {n m : ℕ} {C : Fin (Nat.succ m) → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_closed : ∀ i, IsClosed (C i))
    (h_convex : ∀ i, Convex ℝ (C i))
    (hclosure_sum :
      let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
        fun v => v
      let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
      let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
        fun v i => coords v (Fin.succ i)
      let S : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
        fun i => {v | first v = 1 ∧ tail v ∈ C i}
      let K : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
        fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
      closure (∑ i, K i) = ∑ i, closure (K i)) :
    closure (convexHull ℝ (⋃ i, C i)) =
      ⋃ (lam : Fin (Nat.succ m) → ℝ),
        ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  classical
  let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
    fun v => v
  let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
  let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
    fun v i => coords v (Fin.succ i)
  let C0 : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
  let S0 : Set (Fin (n + 1) → ℝ) := {v | first v = 1 ∧ tail v ∈ C0}
  let K0 : Set (Fin (n + 1) → ℝ) :=
    (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ))
  let S : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
    fun i => {v | first v = 1 ∧ tail v ∈ C i}
  let K : Fin (Nat.succ m) → Set (Fin (n + 1) → ℝ) :=
    fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
  have hclosure_sum' : closure (∑ i, K i) = ∑ i, closure (K i) := by
    simpa [coords, first, tail, S, K] using hclosure_sum
  have htransport :=
    helperForTheorem_19_6_transport_liftedCone_sliceLemmas_toFinCoord
      (n := n) (m := m) (C := C) h_nonempty h_closed h_convex
  have htransport' :
      closure K0 = closure (∑ i, K i) ∧
        (closure C0 =
          {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x}) ∧
        (∀ v, first v = 1 →
          (v ∈ ∑ i, closure (K i) ↔
            ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
              tail v ∈
                ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
    simpa [coords, first, tail, C0, S0, K0, S, K] using htransport
  have hclosureK0 : closure K0 = ∑ i, closure (K i) :=
    htransport'.1.trans hclosure_sum'
  have hslice :
      closure C0 =
        {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := htransport'.2.1
  have hslice_sum :
      ∀ v, first v = 1 →
        (v ∈ ∑ i, closure (K i) ↔
          ∃ (lam : Fin (Nat.succ m) → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
            tail v ∈
              ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i))) :=
    htransport'.2.2
  ext x
  constructor
  · intro hx
    have hxC0 : x ∈ closure C0 := by
      simpa [C0] using hx
    have hx' : x ∈ {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} := by
      simpa [hslice] using hxC0
    rcases hx' with ⟨v, hvcl, hv1, hvx⟩
    have hvsum : v ∈ ∑ i, closure (K i) := by
      simpa [hclosureK0] using hvcl
    rcases (hslice_sum v hv1).1 hvsum with ⟨lam, hlam_nonneg, hsum_lam, htail_mem⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨lam, ?_⟩
    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨hlam_nonneg, hsum_lam⟩, ?_⟩
    simpa [hvx] using htail_mem
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨lam, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hlam, htail_mem⟩
    let v : Fin (n + 1) → ℝ := Fin.cases (1 : ℝ) x
    have hv1 : first v = 1 ∧ tail v = x := by
      constructor
      · simp [first, coords, v]
      · funext i
        simp [tail, coords, v]
    have hvsum : v ∈ ∑ i, closure (K i) := by
      exact (hslice_sum v hv1.1).2 ⟨lam, hlam.1, hlam.2, by simpa [hv1.2] using htail_mem⟩
    have hvcl : v ∈ closure K0 := by
      simpa [hclosureK0] using hvsum
    have hx' : x ∈ {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} :=
      ⟨v, hvcl, hv1.1, hv1.2⟩
    have hxC0 : x ∈ closure C0 := by
      simpa [hslice] using hx'
    simpa [C0] using hxC0

/-- Helper for Theorem 19.6: core closure/representation package for
`closure (convexHull (⋃ i, C i))` under polyhedral hypotheses. -/
lemma helperForTheorem_19_6_polyhedral_and_weightedUnion_core
    {n m : ℕ} {C : Fin m → Set (Fin n → ℝ)}
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i)) :
    IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i, C i))) ∧
      closure (convexHull ℝ (⋃ i, C i)) =
        ⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
  classical
  rcases helperForTheorem_19_6_closed_convex_of_polyhedral_family
      (n := n) (m := m) (C := C) h_polyhedral with ⟨h_closed, h_convex⟩
  cases m with
  | zero =>
      have hrepr0 :
          closure (convexHull ℝ (⋃ i : Fin 0, C i)) =
            ⋃ (lam : Fin 0 → ℝ),
              ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
                ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
        ext x
        simp
      have hpoly0 : IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i : Fin 0, C i))) := by
        exact
          helperForTheorem_19_6_polyhedral_emptyClosureConvexHull_fin0
            (n := n) (C := C)
      exact ⟨hpoly0, hrepr0⟩
  | succ m' =>
      let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := fun v => v
      let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
      let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
        fun v i => coords v (Fin.succ i)
      let S : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
        fun i => {v | first v = 1 ∧ tail v ∈ C i}
      let K : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
        fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
      have hK_poly : ∀ i, IsPolyhedralConvexSet (n + 1) (closure (K i)) := by
        intro i
        have hSlice_nonempty :
            ({v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i}).Nonempty :=
          helperForTheorem_19_6_nonempty_liftedSlice
            (n := n) (C := C i) (h_nonempty i)
        have hSlice_poly :
            IsPolyhedralConvexSet (n + 1)
              {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i} :=
          helperForTheorem_19_6_polyhedral_liftedSlice
            (n := n) (C := C i) (h_polyhedral i)
        have hCone_poly :
            IsPolyhedralConvexSet (n + 1)
              (closure
                ((ConvexCone.hull ℝ
                    {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i}) :
                    Set (Fin (n + 1) → ℝ))) :=
          helperForTheorem_19_6_polyhedral_closure_convexConeHull_of_polyhedral
            (d := n + 1)
            (S := {v : Fin (n + 1) → ℝ | v 0 = 1 ∧ (fun j : Fin n => v (Fin.succ j)) ∈ C i})
            hSlice_nonempty hSlice_poly
        simpa [coords, first, tail, S, K] using hCone_poly
      have hclosure_sum : closure (∑ i, K i) = ∑ i, closure (K i) :=
        helperForTheorem_19_6_closure_sum_liftedCones_eq_sum_closure_liftedCones_polyhedral
          (n := n) (m := Nat.succ m') (K := K) hK_poly
      have hrepr :
          closure (convexHull ℝ (⋃ i, C i)) =
            ⋃ (lam : Fin (Nat.succ m') → ℝ),
              ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
                ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := by
        have hclosure_sum_for_repr :
            let coords : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) :=
              fun v => v
            let first : (Fin (n + 1) → ℝ) → ℝ := fun v => coords v 0
            let tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ) :=
              fun v i => coords v (Fin.succ i)
            let S : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
              fun i => {v | first v = 1 ∧ tail v ∈ C i}
            let K : Fin (Nat.succ m') → Set (Fin (n + 1) → ℝ) :=
              fun i => (ConvexCone.hull ℝ (S i) : Set (Fin (n + 1) → ℝ))
            closure (∑ i, K i) = ∑ i, closure (K i) := by
          simpa [coords, first, tail, S, K] using hclosure_sum
        exact
          helperForTheorem_19_6_closure_convexHull_eq_weighted_union_core_noLineal
            (n := n) (m := m') (C := C) h_nonempty h_closed h_convex
            hclosure_sum_for_repr
      have hpoly : IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i, C i))) := by
        let C0 : Set (Fin n → ℝ) := convexHull ℝ (⋃ i, C i)
        let S0 : Set (Fin (n + 1) → ℝ) := {v | first v = 1 ∧ tail v ∈ C0}
        let K0 : Set (Fin (n + 1) → ℝ) :=
          (ConvexCone.hull ℝ S0 : Set (Fin (n + 1) → ℝ))
        have hsum_poly :
            IsPolyhedralConvexSet (n + 1) (∑ i, closure (K i)) :=
          helperForTheorem_19_6_polyhedral_finset_sum
            (n := n + 1) (m := Nat.succ m')
            (S := fun i => closure (K i)) hK_poly
        have htransport :=
          helperForTheorem_19_6_transport_liftedCone_sliceLemmas_toFinCoord
            (n := n) (m := m') (C := C) h_nonempty h_closed h_convex
        have htransport' :
            closure K0 = closure (∑ i, K i) ∧
              (closure C0 =
                {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x}) ∧
              (∀ v, first v = 1 →
                (v ∈ ∑ i, closure (K i) ↔
                  ∃ (lam : Fin (Nat.succ m') → ℝ), (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1 ∧
                    tail v ∈
                      ∑ i,
                        (if lam i = 0 then Set.recessionCone (C i) else lam i • (C i)))) := by
          simpa [coords, first, tail, C0, S0, K0, S, K] using htransport
        have hclosureK0 : closure K0 = ∑ i, closure (K i) :=
          htransport'.1.trans hclosure_sum
        have hslice :
            closure C0 =
              {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} :=
          htransport'.2.1
        have hslice_eq_liftPreimage :
            {x | ∃ v, v ∈ closure K0 ∧ first v = 1 ∧ tail v = x} =
              {x : Fin n → ℝ | (Fin.cases (1 : ℝ) x) ∈ closure K0} := by
          ext x
          constructor
          · rintro ⟨v, hvcl, hv1, hvx⟩
            have hv_eq : v = Fin.cases (1 : ℝ) x := by
              funext j
              refine Fin.cases ?_ ?_ j
              · simpa [first, coords] using hv1
              · intro i
                have htail_i := congrArg (fun f : Fin n → ℝ => f i) hvx
                simpa [tail, coords] using htail_i
            simpa [hv_eq] using hvcl
          · intro hx
            refine ⟨Fin.cases (1 : ℝ) x, ?_, ?_, ?_⟩
            · simpa using hx
            · simp [first, coords]
            · funext i
              simp [tail, coords]
        have hK0_poly : IsPolyhedralConvexSet (n + 1) (closure K0) := by
          simpa [hclosureK0] using hsum_poly
        have hlift_poly :
            IsPolyhedralConvexSet n
              {x : Fin n → ℝ | (Fin.cases (1 : ℝ) x) ∈ closure K0} :=
          helperForTheorem_19_1_lift_preimage_polyhedral
            (n := n) (K := closure K0) hK0_poly
        have hC0_poly : IsPolyhedralConvexSet n (closure C0) := by
          simpa [hslice, hslice_eq_liftPreimage] using hlift_poly
        simpa [C0] using hC0_poly
      exact ⟨hpoly, hrepr⟩

/-- Theorem 19.6: If `C₁, …, Cₘ` are non-empty polyhedral convex sets in `ℝ^n` and
`C = cl (conv (C₁ ∪ ··· ∪ Cₘ))`, then `C` is polyhedral convex, and
`C` is the union of weighted sums `λ₁ C₁ + ··· + λₘ Cₘ` over all choices of
`λ_i ≥ 0` with `∑ i, λ_i = 1`, using `0^+ C_i` in place of `0 • C_i` when `λ_i = 0`. -/
theorem polyhedralConvexSet_closure_convexHull_iUnion_weightedSum
    (n m : ℕ) (C : Fin m → Set (Fin n → ℝ)) (C' : Set (Fin n → ℝ))
    (hC' : C' = closure (convexHull ℝ (⋃ i, C i)))
    (h_nonempty : ∀ i, (C i).Nonempty)
    (h_polyhedral : ∀ i, IsPolyhedralConvexSet n (C i)) :
    IsPolyhedralConvexSet n C' ∧
      C' =
        ⋃ (lam : {lam : Fin m → ℝ // (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1}),
          weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) := by
  subst hC'
  have hcore :
      IsPolyhedralConvexSet n (closure (convexHull ℝ (⋃ i, C i))) ∧
        closure (convexHull ℝ (⋃ i, C i)) =
          ⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
            ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) :=
    helperForTheorem_19_6_polyhedral_and_weightedUnion_core
      (n := n) (m := m) (C := C) h_nonempty h_polyhedral
  refine ⟨hcore.1, ?_⟩
  calc
    closure (convexHull ℝ (⋃ i, C i)) =
        ⋃ (lam : Fin m → ℝ), ⋃ (_ : (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1),
          ∑ i, (if lam i = 0 then Set.recessionCone (C i) else lam i • C i) := hcore.2
    _ =
        ⋃ (lam : {lam : Fin m → ℝ // (∀ i, 0 ≤ lam i) ∧ (∑ i, lam i) = 1}),
          weightedSumSetWithRecession (n := n) (m := m) (C := C) (lam := lam) := by
            ext x
            constructor
            · intro hx
              rcases Set.mem_iUnion.1 hx with ⟨lam, hx⟩
              rcases Set.mem_iUnion.1 hx with ⟨hlam, hx⟩
              refine Set.mem_iUnion.2 ?_
              refine ⟨⟨lam, hlam⟩, ?_⟩
              simpa [helperForTheorem_19_6_weightedSumSetWithRecession_eq_finsetSumIf]
                using hx
            · intro hx
              rcases Set.mem_iUnion.1 hx with ⟨lam, hx⟩
              refine Set.mem_iUnion.2 ?_
              refine ⟨(lam : Fin m → ℝ), ?_⟩
              refine Set.mem_iUnion.2 ?_
              refine ⟨lam.2, ?_⟩
              simpa [helperForTheorem_19_6_weightedSumSetWithRecession_eq_finsetSumIf]
                using hx

/-- Helper for Theorem 19.7: for nonempty `C`, adjoining `0` to the cone hull does not change
the closure. -/
lemma helperForTheorem_19_7_closure_convexConeGenerated_eq_closure_hull
    {n : ℕ} {C : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) :
    closure (convexConeGenerated n C) =
      closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
  have hzero_rec : (0 : Fin n → ℝ) ∈ Set.recessionCone C := by
    intro x hx t ht
    simpa [zero_smul, add_zero] using hx
  have hzero_mem_closure_hull :
      (0 : Fin n → ℝ) ∈ closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
    helperForTheorem_19_6_recessionDirection_mem_closure_convexConeHull_of_nonempty
      (d := n) (C := C) hCne hzero_rec
  have hKdef :
      convexConeGenerated n C =
        ({0} : Set (Fin n → ℝ)) ∪ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := by
    ext x
    constructor
    · intro hx
      have hx' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := by
        simpa [convexConeGenerated, Set.mem_insert_iff] using hx
      rcases hx' with hx0 | hxHull
      · exact Or.inl (by simpa [Set.mem_singleton_iff] using hx0)
      · exact Or.inr hxHull
    · intro hx
      rcases hx with hx0 | hxHull
      · have hx0' : x = 0 := by simpa [Set.mem_singleton_iff] using hx0
        exact (Set.mem_insert_iff).2 (Or.inl hx0')
      · exact (Set.mem_insert_iff).2 (Or.inr hxHull)
  calc
    closure (convexConeGenerated n C)
        = closure (({0} : Set (Fin n → ℝ)) ∪ (ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
          simp [hKdef]
    _ = closure ({0} : Set (Fin n → ℝ)) ∪ closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
          simpa using
            (closure_union
              (s := ({0} : Set (Fin n → ℝ)))
              (t := (ConvexCone.hull ℝ C : Set (Fin n → ℝ))))
    _ = closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) := by
          apply Set.union_eq_right.mpr
          intro x hx
          have hx0 : x = 0 := by
            have hx' : x ∈ ({0} : Set (Fin n → ℝ)) := by
              simpa [closure_singleton] using hx
            simpa [Set.mem_singleton_iff] using hx'
          simpa [hx0] using hzero_mem_closure_hull

/-- Helper for Theorem 19.7: the Euclidean-coordinate transport of the recession cone term
equals the ambient-space recession cone. -/
lemma helperForTheorem_19_7_recessionCone_transport_eq
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
    Set.image e (Set.recessionCone (Set.image e.symm C)) = Set.recessionCone C := by
  intro e
  have hrec :
      Set.recessionCone (Set.image e.symm C) = Set.image e.symm (Set.recessionCone C) := by
    simpa using (recessionCone_image_linearEquiv (e := e.symm.toLinearEquiv) (C := C))
  calc
    Set.image e (Set.recessionCone (Set.image e.symm C))
        = Set.image e (Set.image e.symm (Set.recessionCone C)) := by
            simp [hrec]
    _ = Set.recessionCone C := by
          simp [Set.image_image]

/-- Helper for Theorem 19.7: rewriting the positive-scaling union from nested existential
indices to a subtype index. -/
lemma helperForTheorem_19_7_iUnion_pos_subtype_rewrite
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) =
      ⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨t, ht⟩
    rcases Set.mem_iUnion.1 ht with ⟨htpos, hxt⟩
    exact Set.mem_iUnion.2 ⟨⟨t, htpos⟩, hxt⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨lam, hxl⟩
    exact Set.mem_iUnion.2 ⟨(lam : ℝ), Set.mem_iUnion.2 ⟨lam.property, hxl⟩⟩

/-- Helper for Theorem 19.7: if `0 ∈ C = mixedConvexHull S₀ S₁`, then every direction generator
belongs to `C`. -/
lemma helperForTheorem_19_7_originMem_directions_subset_carrier
    {n : ℕ} {C S₀ S₁ : Set (Fin n → ℝ)}
    (hCeq : C = mixedConvexHull (n := n) S₀ S₁)
    (hC0 : (0 : Fin n → ℝ) ∈ C) :
    S₁ ⊆ C := by
  intro dir hdir
  have hdir_rec_mixed : dir ∈ Set.recessionCone (mixedConvexHull (n := n) S₀ S₁) :=
    helperForTheorem_19_6_directions_subset_recessionCone_mixedConvexHull
      (d := n) (S₀ := S₀) (S₁ := S₁) hdir
  have hdir_rec : dir ∈ Set.recessionCone C := by
    simpa [hCeq] using hdir_rec_mixed
  have h1nonneg : (0 : ℝ) ≤ 1 := by
    norm_num
  have hmem : (0 : Fin n → ℝ) + (1 : ℝ) • dir ∈ C :=
    hdir_rec (x := (0 : Fin n → ℝ)) hC0 (t := (1 : ℝ)) h1nonneg
  simpa using hmem

/-- Helper for Theorem 19.7: with finite mixed-hull data and `0 ∈ C`, the generated cone of `C`
coincides with the finite cone generated by points and directions. -/
lemma helperForTheorem_19_7_originMem_convexConeGenerated_eq_finiteCone
    {n : ℕ} {C S₀ S₁ : Set (Fin n → ℝ)}
    (hCeq : C = mixedConvexHull (n := n) S₀ S₁)
    (hS₀fin : Set.Finite S₀)
    (hS₁fin : Set.Finite S₁)
    (hC0 : (0 : Fin n → ℝ) ∈ C) :
    convexConeGenerated n C = cone n (S₀ ∪ S₁) := by
  have hCne : C.Nonempty := ⟨0, hC0⟩
  have hMixed_nonempty : (mixedConvexHull (n := n) S₀ S₁).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [hCeq] using hC0
  have hS₀ne : S₀.Nonempty :=
    helperForTheorem_19_5_pointsNonempty_of_nonempty_mixedConvexHull
      (n := n) (S₀ := S₀) (S₁ := S₁) hMixed_nonempty
  have hclosure_hull_eq_cone :
      closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) = cone n (S₀ ∪ S₁) := by
    calc
      closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ)))
          = closure ((ConvexCone.hull ℝ (mixedConvexHull (n := n) S₀ S₁) : Set (Fin n → ℝ))) := by
              simp [hCeq]
      _ = cone n (S₀ ∪ S₁) :=
        helperForTheorem_19_6_closure_convexConeHull_eq_cone_of_finiteMixedData
          (d := n) (S₀ := S₀) (S₁ := S₁) hS₀fin hS₁fin hS₀ne
  have hclosureK_eq_cone :
      closure (convexConeGenerated n C) = cone n (S₀ ∪ S₁) := by
    calc
      closure (convexConeGenerated n C)
          = closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
              helperForTheorem_19_7_closure_convexConeGenerated_eq_closure_hull
                (n := n) (C := C) hCne
      _ = cone n (S₀ ∪ S₁) := hclosure_hull_eq_cone
  have hS₀_subset_C : S₀ ⊆ C := by
    intro x hx
    have hxMixed : x ∈ mixedConvexHull (n := n) S₀ S₁ :=
      helperForTheorem_19_6_points_subset_mixedConvexHull
        (d := n) (S₀ := S₀) (S₁ := S₁) hx
    simpa [hCeq] using hxMixed
  have hS₁_subset_C : S₁ ⊆ C :=
    helperForTheorem_19_7_originMem_directions_subset_carrier
      (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCeq hC0
  have hUnion_subset_C : S₀ ∪ S₁ ⊆ C := by
    intro x hx
    rcases hx with hx0 | hx1
    · exact hS₀_subset_C hx0
    · exact hS₁_subset_C hx1
  have hUnion_subset_hullC : S₀ ∪ S₁ ⊆ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := by
    intro x hx
    exact ConvexCone.subset_hull (hUnion_subset_C hx)
  have hHull_subset :
      (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin n → ℝ)) ⊆ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) :=
    ConvexCone.hull_min (s := S₀ ∪ S₁) (C := ConvexCone.hull ℝ C) hUnion_subset_hullC
  have hcone_subset_K : cone n (S₀ ∪ S₁) ⊆ convexConeGenerated n C := by
    intro x hx
    have hx' : x ∈ convexConeGenerated n (S₀ ∪ S₁) := by
      simpa [cone_eq_convexConeGenerated (n := n) (S₁ := S₀ ∪ S₁)] using hx
    have hx'' : x = 0 ∨ x ∈ (ConvexCone.hull ℝ (S₀ ∪ S₁) : Set (Fin n → ℝ)) := by
      simpa [convexConeGenerated, Set.mem_insert_iff] using hx'
    rcases hx'' with hx0 | hxHull
    · subst hx0
      exact Set.mem_insert (0 : Fin n → ℝ) (ConvexCone.hull ℝ C : Set (Fin n → ℝ))
    · have hxHullC : x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := hHull_subset hxHull
      have hxK : x = 0 ∨ x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := Or.inr hxHullC
      simpa [convexConeGenerated, Set.mem_insert_iff] using hxK
  have hK_subset_cone : convexConeGenerated n C ⊆ cone n (S₀ ∪ S₁) := by
    intro x hx
    have hxcl : x ∈ closure (convexConeGenerated n C) := subset_closure hx
    simpa [hclosureK_eq_cone] using hxcl
  exact Set.Subset.antisymm hK_subset_cone hcone_subset_K

/-- Theorem 19.7: Let `C` be a non-empty polyhedral convex set, and let `K` be the closure of the
convex cone generated by `C`. Then `K` is a polyhedral convex cone, and
`K = ⋃ {λ C | λ > 0 or λ = 0^+}`. -/
theorem polyhedralConvexCone_closure_convexConeGenerated
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    C.Nonempty →
    IsPolyhedralConvexSet n C →
      IsPolyhedralConvexSet n (closure (convexConeGenerated n C)) ∧
        IsConeSet n (closure (convexConeGenerated n C)) ∧
        closure (convexConeGenerated n C) =
          (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
  intro hCne hCpoly
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hCclosed : IsClosed C :=
    (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
      (n := n) (C := C) hCpoly).1
  have hpolyClosureHull :
      IsPolyhedralConvexSet n (closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ)))) :=
    helperForTheorem_19_6_polyhedral_closure_convexConeHull_of_polyhedral
      (d := n) (S := C) hCne hCpoly
  have hclosure_eq_hull :
      closure (convexConeGenerated n C) =
        closure ((ConvexCone.hull ℝ C : Set (Fin n → ℝ))) :=
    helperForTheorem_19_7_closure_convexConeGenerated_eq_closure_hull
      (n := n) (C := C) hCne
  have hpolyK : IsPolyhedralConvexSet n (closure (convexConeGenerated n C)) := by
    simpa [hclosure_eq_hull] using hpolyClosureHull
  have hconeBase : IsConeSet n (convexConeGenerated n C) :=
    (isConvexCone_convexConeGenerated (n := n) (S₁ := C)).1
  have hconeClosure : IsConeSet n (closure (convexConeGenerated n C)) :=
    cor11_7_2_isConeSet_closure (n := n) (K := convexConeGenerated n C) hconeBase
  have hrepr :
      closure (convexConeGenerated n C) =
        (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
    by_cases hC0 : (0 : Fin n → ℝ) ∈ C
    · have hTFAE :
        [IsPolyhedralConvexSet n C,
          (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
          IsFinitelyGeneratedConvexSet n C].TFAE :=
        polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
      have hCfg : IsFinitelyGeneratedConvexSet n C := (hTFAE.out 0 2).1 hCpoly
      rcases hCfg with ⟨S₀, S₁, hS₀fin, hS₁fin, hCeq⟩
      have hK_eq_cone :
          convexConeGenerated n C = cone n (S₀ ∪ S₁) :=
        helperForTheorem_19_7_originMem_convexConeGenerated_eq_finiteCone
          (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCeq hS₀fin hS₁fin hC0
      have hcone_poly : IsPolyhedralConvexSet n (cone n (S₀ ∪ S₁)) :=
        helperForTheorem_19_1_cone_polyhedral_of_finite_generators
          (m := n) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
      have hcone_closed : IsClosed (cone n (S₀ ∪ S₁)) :=
        (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
          (n := n) (C := cone n (S₀ ∪ S₁)) hcone_poly).1
      have hclosureK : closure (convexConeGenerated n C) = convexConeGenerated n C := by
        calc
          closure (convexConeGenerated n C)
              = closure (cone n (S₀ ∪ S₁)) := by
                  simp [hK_eq_cone]
          _ = cone n (S₀ ∪ S₁) :=
                (closure_eq_iff_isClosed (s := cone n (S₀ ∪ S₁))).2 hcone_closed
          _ = convexConeGenerated n C := by
                simp [hK_eq_cone]
      have hrec_subset_C : Set.recessionCone C ⊆ C := by
        intro dir hdir
        have h1nonneg : (0 : ℝ) ≤ 1 := by
          norm_num
        have hmem : (0 : Fin n → ℝ) + (1 : ℝ) • dir ∈ C :=
          hdir (x := (0 : Fin n → ℝ)) hC0 (t := (1 : ℝ)) h1nonneg
        simpa using hmem
      have hC_subset_K : C ⊆ convexConeGenerated n C := by
        intro x hx
        have hxHull : x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) :=
          ConvexCone.subset_hull hx
        have hxK : x = 0 ∨ x ∈ (ConvexCone.hull ℝ C : Set (Fin n → ℝ)) := Or.inr hxHull
        simpa [convexConeGenerated, Set.mem_insert_iff] using hxK
      have hrec_subset_K : Set.recessionCone C ⊆ convexConeGenerated n C :=
        hrec_subset_C.trans hC_subset_K
      have hrec0 : (0 : Fin n → ℝ) ∈ Set.recessionCone C := by
        intro x hx t ht
        simpa [zero_smul, add_zero] using hx
      have hK_union :
          convexConeGenerated n C ∪ Set.recessionCone C =
            (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := by
        simpa using
          (convexConeGenerated_union_recession_eq_iUnion_pos (C := C) hCconv
            (recC := Set.recessionCone C) hrec0)
      have hK_eq_union :
          convexConeGenerated n C =
            (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := by
        calc
          convexConeGenerated n C = convexConeGenerated n C ∪ Set.recessionCone C := by
            symm
            exact Set.union_eq_left.mpr hrec_subset_K
          _ = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := hK_union
      calc
        closure (convexConeGenerated n C) = convexConeGenerated n C := hclosureK
        _ = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ Set.recessionCone C := hK_eq_union
        _ = (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
              rw [helperForTheorem_19_7_iUnion_pos_subtype_rewrite (n := n) (C := C)]
    · let e := (EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n))
      let C' : Set (EuclideanSpace ℝ (Fin n)) := Set.image e.symm C
      let recC : Set (Fin n → ℝ) := Set.image e (Set.recessionCone C')
      let K : Set (Fin n → ℝ) := convexConeGenerated n C
      have hcore :
          closure K = K ∪ recC ∧
            K ∪ recC = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ recC := by
        simpa [e, C', recC, K] using
          (closure_convexConeGenerated_eq_union_recessionCone
            (C := C) hCne hCclosed hCconv hC0)
      have hrec_transport : recC = Set.recessionCone C := by
        simpa [e, C', recC] using
          (helperForTheorem_19_7_recessionCone_transport_eq (n := n) (C := C))
      calc
        closure (convexConeGenerated n C) = K ∪ recC := by
          simpa [K] using hcore.1
        _ = (⋃ (t : ℝ), ⋃ (_ : 0 < t), t • C) ∪ recC := hcore.2
        _ = (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ recC := by
              rw [helperForTheorem_19_7_iUnion_pos_subtype_rewrite (n := n) (C := C)]
        _ = (⋃ (lam : {lam : ℝ // 0 < lam}), (lam : ℝ) • C) ∪ Set.recessionCone C := by
              simp [hrec_transport]
  exact ⟨hpolyK, hconeClosure, hrepr⟩

/-- Corollary 19.7.1: If `C` is a polyhedral convex set containing the origin, the convex cone
generated by `C` is polyhedral. -/
theorem polyhedral_convexConeGenerated_of_origin_mem
    (n : ℕ) (C : Set (Fin n → ℝ)) :
    IsPolyhedralConvexSet n C →
      (0 : Fin n → ℝ) ∈ C →
        IsPolyhedralConvexSet n (convexConeGenerated n C) := by
  intro hCpoly hC0
  have hCconv : Convex ℝ C :=
    helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly
  have hTFAE :
      [IsPolyhedralConvexSet n C,
        (IsClosed C ∧ {C' : Set (Fin n → ℝ) | IsFace (𝕜 := ℝ) C C'}.Finite),
        IsFinitelyGeneratedConvexSet n C].TFAE :=
    polyhedral_closed_finiteFaces_finitelyGenerated_equiv (n := n) (C := C) hCconv
  have hCfg : IsFinitelyGeneratedConvexSet n C := (hTFAE.out 0 2).1 hCpoly
  rcases hCfg with ⟨S₀, S₁, hS₀fin, hS₁fin, hCeq⟩
  have hK_eq_cone :
      convexConeGenerated n C = cone n (S₀ ∪ S₁) :=
    helperForTheorem_19_7_originMem_convexConeGenerated_eq_finiteCone
      (n := n) (C := C) (S₀ := S₀) (S₁ := S₁) hCeq hS₀fin hS₁fin hC0
  have hcone_poly : IsPolyhedralConvexSet n (cone n (S₀ ∪ S₁)) :=
    helperForTheorem_19_1_cone_polyhedral_of_finite_generators
      (m := n) (T := S₀ ∪ S₁) (hS₀fin.union hS₁fin)
  simpa [hK_eq_cone] using hcone_poly

end Section19
end Chap19

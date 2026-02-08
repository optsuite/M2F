import Mathlib

open Group

open scoped Pointwise

/-- If a Sylow `p`-subgroup is normal, then it is the unique Sylow `p`-subgroup.

This avoids any `Finite (Sylow p H)` hypotheses by using closure of `p`-groups under `⊔` when one
subgroup is normal, plus the maximality property in the definition of `Sylow`. -/
lemma sylow_eq_of_normal {H : Type*} [Group H] {p : ℕ} [Fact (Nat.Prime p)]
    (P Q : Sylow p H) (hP : P.Normal) : Q = P := by
  classical
  haveI : (P : Subgroup H).Normal := hP
  have hPp : IsPGroup p (P : Subgroup H) := by
    simpa using P.isPGroup'
  have hQp : IsPGroup p (Q : Subgroup H) := by
    simpa using Q.isPGroup'
  have hsup : IsPGroup p ((P : Subgroup H) ⊔ (Q : Subgroup H) : Subgroup H) :=
    IsPGroup.to_sup_of_normal_left hPp hQp
  have hsup_eq_P : ((P : Subgroup H) ⊔ (Q : Subgroup H) : Subgroup H) = (P : Subgroup H) :=
    P.is_maximal' hsup (by simp)
  have hsup_eq_Q : ((P : Subgroup H) ⊔ (Q : Subgroup H) : Subgroup H) = (Q : Subgroup H) :=
    Q.is_maximal' hsup (by simp)
  apply Sylow.ext
  have : (P : Subgroup H) = (Q : Subgroup H) := hsup_eq_P.symm.trans hsup_eq_Q
  simp [this]

/-- If `S` is a finite `p`-subgroup of `G` and `U` is a proper subgroup of `S`, then
`U` is strictly contained in `U.normalizer ⊓ S` (the normalizer of `U` inside `S`). -/
lemma lt_normalizer_inf_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    {S U : Subgroup G} (hS : IsPGroup p S) (hUS : U ≤ S) (hU : U ≠ S) :
    U < U.normalizer ⊓ S := by
  classical
  haveI : Group.IsNilpotent S := hS.isNilpotent
  have hnc : NormalizerCondition S := normalizerCondition_of_isNilpotent (G := S)
  have hU'ne_top : U.subgroupOf S ≠ (⊤ : Subgroup S) := by
    intro htop
    have hSleU : S ≤ U := (Subgroup.subgroupOf_eq_top).1 htop
    exact hU (le_antisymm hUS hSleU)
  have hU'lt_top : U.subgroupOf S < (⊤ : Subgroup S) := lt_top_iff_ne_top.2 hU'ne_top
  have hlt : U.subgroupOf S < (U.subgroupOf S).normalizer := hnc _ hU'lt_top
  rcases SetLike.exists_of_lt hlt with ⟨x, hxN, hxnot⟩
  refine lt_of_le_of_ne (le_inf U.le_normalizer hUS) ?_
  have hx_mem : (x : G) ∈ U.normalizer ⊓ S := by
    refine ⟨?_, x.2⟩
    have hxN' : x ∈ U.normalizer.subgroupOf S := by
      rw [Subgroup.subgroupOf_normalizer_eq (H := U) (N := S) hUS]
      exact hxN
    simpa [Subgroup.mem_subgroupOf] using hxN'
  have hx_not : (x : G) ∉ U := by
    simpa [Subgroup.mem_subgroupOf] using hxnot
  intro hEq
  have : (x : G) ∈ U := by
    rw [hEq]
    exact hx_mem
  exact hx_not this

/-- If `U < K` and `K ≤ S` and `K ≤ Q`, then `|U| < |S ∩ Q|` at the level of `Set.ncard`. -/
lemma ncard_lt_inter_of_lt_of_le {G : Type*} [Group G] [Finite G] {U K S Q : Subgroup G}
    (hUK : U < K) (hKS : K ≤ S) (hKQ : K ≤ Q) :
    (U : Set G).ncard < ((S : Set G) ⊓ (Q : Set G)).ncard := by
  classical
  have hU_ssub_K : (U : Set G) ⊂ (K : Set G) := by
    refine ⟨?_, ?_⟩
    · intro x hx
      exact hUK.1 hx
    · intro hKU
      have hKleU : K ≤ U := by
        intro x hx
        exact hKU hx
      exact (ne_of_lt hUK) (le_antisymm hUK.1 hKleU)
  have hU_card_lt_K : (U : Set G).ncard < (K : Set G).ncard :=
    Set.ncard_lt_ncard hU_ssub_K
  have hK_subset : (K : Set G) ⊆ ((S : Set G) ⊓ (Q : Set G)) := by
    intro x hx
    exact ⟨hKS hx, hKQ hx⟩
  have hK_card_le : (K : Set G).ncard ≤ ((S : Set G) ⊓ (Q : Set G)).ncard :=
    Set.ncard_le_ncard hK_subset
  exact lt_of_lt_of_le hU_card_lt_K hK_card_le

/-- If `K ≤ N` is a `p`-subgroup, and `P` is a normal Sylow `p`-subgroup of `N`, then
`K ≤ P.map N.subtype`. -/
lemma le_mapSubtype_of_normal_sylow {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)]
    {N : Subgroup G} (P : Sylow p N) (hP : P.Normal) {K : Subgroup G}
    (hKN : K ≤ N) (hK : IsPGroup p K) : K ≤ (P : Subgroup N).map N.subtype := by
  classical
  have hK' : IsPGroup p (K.subgroupOf N) := by
    simpa using hK.comap_subtype (K := N)
  obtain ⟨Q, hKQ⟩ := IsPGroup.exists_le_sylow (G := N) (p := p) (P := K.subgroupOf N) hK'
  have hQeq : Q = P := sylow_eq_of_normal (P := P) (Q := Q) hP
  have hK_le_P : K.subgroupOf N ≤ (P : Subgroup N) := by
    simpa [hQeq] using hKQ
  have hmap : (K.subgroupOf N).map N.subtype ≤ (P : Subgroup N).map N.subtype :=
    Subgroup.map_mono hK_le_P
  have hK_map : (K.subgroupOf N).map N.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKN
  -- rewrite `K` as the map of `K.subgroupOf N` into `G`
  simpa [hK_map] using hmap

/--
Let $G$ be a finite group and let $\mathrm{Syl}_p(G)$ denote its set of Sylow $p$-subgroups.
		Suppose that $S$ and $T$ are distinct members of
		$\mathrm{Syl}_p(G)$ chosen so that $\#(S \cap T)$ is maximal
among all such intersections. Prove that the normalizer $N_G(S \cap  T)$ does not admit normal
Sylow $p$-subgroup.
-/
theorem sylow_subgroup_not_normal_of_maximal_intersection (G : Type) [Finite G] [Group G]
    (p : ℕ) [Fact (Nat.Prime p)] (S T : Sylow p G) (h_ne : S ≠ T)
    (h_maximal : ∀ (S' T' : Sylow p G), S' ≠ T' →
    ((S' : Set G) ⊓ T').ncard ≤ ((S : Set G) ⊓ T).ncard) :
    ∀ (P : Sylow p ((S : Subgroup G) ⊓ T).normalizer), ¬ P.Normal := by
  classical
  intro P
  by_contra hP

  let U : Subgroup G := (S : Subgroup G) ⊓ (T : Subgroup G)
  let N : Subgroup G := U.normalizer
  let P0 : Sylow p N := by
    simpa [N, U] using P
  have hP0 : P0.Normal := by
    simpa [P0, N, U] using hP

  have hU_ne_S : U ≠ (S : Subgroup G) := by
    intro hEq
    have hSleT : (S : Subgroup G) ≤ (T : Subgroup G) := by
      have : (S : Subgroup G) ⊓ (T : Subgroup G) ≤ (T : Subgroup G) := inf_le_right
      simpa [U, hEq] using this
    have hTp : IsPGroup p (T : Subgroup G) := by
      simpa using T.isPGroup'
    have hTsub_eq : (T : Subgroup G) = (S : Subgroup G) := S.is_maximal' hTp hSleT
    exact h_ne (Sylow.ext hTsub_eq.symm)
  have hU_ne_T : U ≠ (T : Subgroup G) := by
    intro hEq
    have hTleS : (T : Subgroup G) ≤ (S : Subgroup G) := by
      have : (S : Subgroup G) ⊓ (T : Subgroup G) ≤ (S : Subgroup G) := inf_le_left
      simpa [U, hEq, inf_comm] using this
    have hSp : IsPGroup p (S : Subgroup G) := by
      simpa using S.isPGroup'
    have hSsub_eq : (S : Subgroup G) = (T : Subgroup G) := T.is_maximal' hSp hTleS
    exact h_ne (Sylow.ext hSsub_eq)

  let KS : Subgroup G := U.normalizer ⊓ (S : Subgroup G)
  let KT : Subgroup G := U.normalizer ⊓ (T : Subgroup G)

  have hU_lt_KS : U < KS := by
    have hSp : IsPGroup p (S : Subgroup G) := by
      simpa using S.isPGroup'
    have hUS : U ≤ (S : Subgroup G) := by
      simp [U]
    simpa [KS, U] using lt_normalizer_inf_of_isPGroup (p := p) hSp hUS hU_ne_S
  have hU_lt_KT : U < KT := by
    have hTp : IsPGroup p (T : Subgroup G) := by
      simpa using T.isPGroup'
    have hUT : U ≤ (T : Subgroup G) := by
      simp [U]
    simpa [KT, U, inf_comm] using lt_normalizer_inf_of_isPGroup (p := p) hTp hUT hU_ne_T

  have hKS_le_N : KS ≤ N := by
    simp [KS, N, U]
  have hKT_le_N : KT ≤ N := by
    simp [KT, N, U]

  have hKS_p : IsPGroup p KS := by
    have hSp : IsPGroup p (S : Subgroup G) := by
      simpa using S.isPGroup'
    exact IsPGroup.to_le hSp (by simp [KS])
  have hKT_p : IsPGroup p KT := by
    have hTp : IsPGroup p (T : Subgroup G) := by
      simpa using T.isPGroup'
    exact IsPGroup.to_le hTp (by simp [KT])

  have hKS_le_Pmap : KS ≤ (P0 : Subgroup N).map N.subtype :=
    le_mapSubtype_of_normal_sylow (P := P0) (p := p) hP0 hKS_le_N hKS_p
  have hKT_le_Pmap : KT ≤ (P0 : Subgroup N).map N.subtype :=
    le_mapSubtype_of_normal_sylow (P := P0) (p := p) hP0 hKT_le_N hKT_p

  obtain ⟨Q, hcomap⟩ := Sylow.exists_comap_subtype_eq (P := P0)
  have hPmap_le_Q : (P0 : Subgroup N).map N.subtype ≤ (Q : Subgroup G) := by
    have hP_le_comap : (P0 : Subgroup N) ≤ Subgroup.comap N.subtype (Q : Subgroup G) := by
      simp [hcomap]
    exact (Subgroup.map_le_iff_le_comap).2 hP_le_comap

  have hKS_le_Q : KS ≤ (Q : Subgroup G) := le_trans hKS_le_Pmap hPmap_le_Q
  have hKT_le_Q : KT ≤ (Q : Subgroup G) := le_trans hKT_le_Pmap hPmap_le_Q

  have hU_card_lt_SQ :
      (U : Set G).ncard < ((S : Set G) ⊓ (Q : Set G)).ncard := by
    have hKS_le_S : KS ≤ (S : Subgroup G) := by
      simp [KS]
    exact ncard_lt_inter_of_lt_of_le (hUK := hU_lt_KS) hKS_le_S hKS_le_Q

  have hQ_eq_S : Q = S := by
    by_contra hQS
    have hSQ : S ≠ Q := by
      simpa [eq_comm] using hQS
    have hmax : ((S : Set G) ⊓ Q).ncard ≤ ((S : Set G) ⊓ T).ncard :=
      h_maximal S Q hSQ
    have hmax' : ((S : Set G) ⊓ (Q : Set G)).ncard ≤ (U : Set G).ncard := by
      simpa [U] using hmax
    exact (not_lt_of_ge hmax') (by simpa [Set.inf_eq_inter] using hU_card_lt_SQ)

  have hU_card_lt_TQ :
      (U : Set G).ncard < ((T : Set G) ⊓ (Q : Set G)).ncard := by
    have hKT_le_T : KT ≤ (T : Subgroup G) := by
      simp [KT]
    exact ncard_lt_inter_of_lt_of_le (hUK := hU_lt_KT) hKT_le_T hKT_le_Q

  have hQ_eq_T : Q = T := by
    by_contra hQT
    have hTQ : T ≠ Q := by
      simpa [eq_comm] using hQT
    have hmax : ((T : Set G) ⊓ Q).ncard ≤ ((S : Set G) ⊓ T).ncard :=
      h_maximal T Q hTQ
    have hmax' : ((T : Set G) ⊓ (Q : Set G)).ncard ≤ (U : Set G).ncard := by
      simpa [U, inf_comm] using hmax
    exact (not_lt_of_ge hmax') (by simpa [Set.inf_eq_inter] using hU_card_lt_TQ)

  exact h_ne (hQ_eq_S.symm.trans hQ_eq_T)

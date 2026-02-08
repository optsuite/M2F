import Mathlib

/--
Let $G$ be a finite group and $L$ a maximal subgroup of $G$. Suppose $L$ is non-Abelian and simple.
Then there exist at most two minimal normal subgroups in $G$.
-/
theorem card_minimal_normal_subgroup_le_2 (G : Type) [Group G] [Finite G]
    (L : Subgroup G) (h_ne_top : L ≠ ⊤)
    (h_maximal : IsMax (⟨L, h_ne_top⟩ : {H : Subgroup G // H ≠ ⊤}))
    (h_simple : IsSimpleGroup L) (h_non_comm : ∃ (x y : L), x * y ≠ y * x) :
    {H : {H : Subgroup G // H.Normal} | IsMin H}.ncard ≤ 2 := by
  classical
  have _ := h_maximal
  have _ := h_simple
  have _ := h_non_comm
  -- In any type with `⊥`, an `IsMin` element must be `⊥`, so the set is a singleton.
  let botN : {H : Subgroup G // H.Normal} := ⟨⊥, by infer_instance⟩
  have hset :
      {H : {H : Subgroup G // H.Normal} | IsMin H} = {botN} := by
    ext H
    constructor
    · intro hH
      have hmin : IsMin H := hH
      have hbot : botN ≤ H := by
        change (⊥ : Subgroup G) ≤ (H : Subgroup G)
        exact bot_le
      have hle : H ≤ botN := hmin (b := botN) hbot
      have h_eq : H = botN := le_antisymm hle hbot
      exact Set.mem_singleton_iff.mpr h_eq
    · intro hH
      rcases Set.mem_singleton_iff.mp hH with rfl
      intro b hb
      change (⊥ : Subgroup G) ≤ (b : Subgroup G)
      exact bot_le
  have hle1 : ({H : {H : Subgroup G // H.Normal} | IsMin H}.ncard) ≤ 1 := by
    simp [hset]
  exact hle1.trans (by decide)

import Mathlib

/- Prove that if $H$ is a subgroup of $G$ of index $n$, then there is a normal subgroup $K$ of $G$
such that $K\leq H$ and $[G:K]\leq n!$-/
namespace Subgroup

variable {G : Type*} [Group G]

/-- The action of `G` on `G ⧸ H` gives an embedding `G ⧸ H.normalCore ↪ Equiv.Perm (G ⧸ H)`, hence
`H.normalCore.index` divides `H.index!`. -/
theorem normalCore_index_dvd_index_factorial (H : Subgroup G) [H.FiniteIndex] :
    H.normalCore.index ∣ H.index.factorial := by
  classical
  rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
  exact card_subgroup_dvd_card (MulAction.toPermHom G (G ⧸ H)).range

end Subgroup

theorem subgroup_normal_index_le_factorial {G : Type} [Group G] {n : ℕ} (hn : n ≠ 0)
    (H : Subgroup G) (hH : H.index = n) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ H ∧ K.index ≠ 0 ∧ K.index ≤ n.factorial := by
  classical
  have hH0 : H.index ≠ 0 := by simpa [hH] using hn
  haveI : H.FiniteIndex := (Subgroup.finiteIndex_iff (H := H)).2 hH0
  refine ⟨H.normalCore, ?_⟩
  refine ⟨by infer_instance, Subgroup.normalCore_le H, ?_⟩
  have hdiv : H.normalCore.index ∣ n.factorial := by
    simpa [hH] using (Subgroup.normalCore_index_dvd_index_factorial (H := H))
  have hK0 : H.normalCore.index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Nat.factorial_ne_zero n) hdiv
  refine ⟨hK0, ?_⟩
  exact Nat.le_of_dvd (Nat.factorial_pos n) hdiv

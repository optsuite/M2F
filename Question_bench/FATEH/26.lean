import Mathlib
/-- If the center is not contained in a coatom, their sup is top. -/
lemma center_sup_eq_top_of_not_le {G : Type} [Group G] {H : Subgroup G} (h : IsCoatom H)
    (hcenter : ¬ Subgroup.center G ≤ H) : H ⊔ Subgroup.center G = ⊤ :=
by
  have hcod : Codisjoint H (Subgroup.center G) :=
    (IsCoatom.not_le_iff_codisjoint h).1 hcenter
  exact Codisjoint.eq_top hcod

/-- If a coatom does not contain the center, then it is normal. -/
lemma normal_of_coatom_center_not_le {G : Type} [Group G] {H : Subgroup G} (h : IsCoatom H)
    (hcenter : ¬ Subgroup.center G ≤ H) : H.Normal := by
  have hle : H ≤ H.normalizer := Subgroup.le_normalizer (H := H)
  have hnorm : H.normalizer = ⊤ := by
    rcases (IsCoatom.le_iff h).1 hle with htop | hEq
    · exact htop
    ·
      have hcent : Subgroup.center G ≤ H := by
        have hcentnorm : Subgroup.center G ≤ H.normalizer :=
          Subgroup.center_le_normalizer (H := H)
        simpa [hEq] using hcentnorm
      exact (hcenter hcent).elim
  exact (Subgroup.normalizer_eq_top_iff (H := H)).1 hnorm

/-- A normal subgroup whose sup with the center is top contains the commutator. -/
lemma commutator_le_of_normal_center_sup {G : Type} [Group G] {H : Subgroup G} (hN : H.Normal)
    (hsup : H ⊔ Subgroup.center G = ⊤) : commutator G ≤ H := by
  have _ : H.Normal := hN
  simpa using
    (Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := H)
      (H := Subgroup.center G) hsup (by infer_instance))

/--Suppose \( G \) is a group and \( H \) is a maximal subgroup of \( G \). Show that either \( Z(G)
\leq H \) or \( [G,G] \leq H \). (A maximal subgroup contains either the center or the commutator
 subgroup.)-/
theorem center_le_or_commutator_le_of_isCoatom {G : Type} [Group G] (H : Subgroup G)
    (h : IsCoatom H) : Subgroup.center G ≤ H ∨ commutator G ≤ H := by
  classical
  by_cases hcenter : Subgroup.center G ≤ H
  · exact Or.inl hcenter
  ·
    right
    have hsup : H ⊔ Subgroup.center G = ⊤ :=
      center_sup_eq_top_of_not_le (H := H) h hcenter
    have hN : H.Normal := normal_of_coatom_center_not_le (H := H) h hcenter
    exact commutator_le_of_normal_center_sup (H := H) hN hsup

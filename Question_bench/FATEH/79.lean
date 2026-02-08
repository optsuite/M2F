import Mathlib

/--Let \( R \) be a commutative ring. If all submodules of finitely generated free modules over
\( R \) are free over \( R \), then \( R \) is a PID.-/
theorem isPrincipalIdealRing_of_forall_free {R : Type} [CommRing R]
    (h : ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M],
      ∀ (N : Submodule R M), Module.Free R N) :
    IsPrincipalIdealRing R := by
  classical
  rcases subsingleton_or_nontrivial R with htriv | hnontriv
  · haveI : Subsingleton R := htriv
    refine IsPrincipalIdealRing.mk ?_
    intro I
    refine (Submodule.isPrincipal_iff (S := (I : Submodule R R))).2 ?_
    refine ⟨(0 : R), ?_⟩
    have hI : (I : Submodule R R) = ⊥ := by
      simpa using (Subsingleton.elim I (⊥ : Ideal R))
    calc
      (I : Submodule R R) = (⊥ : Submodule R R) := hI
      _ = R ∙ (0 : R) := by
        symm
        simp
  · haveI : Nontrivial R := hnontriv
    letI : StrongRankCondition R := commRing_strongRankCondition (R := R)
    refine IsPrincipalIdealRing.mk ?_
    intro I
    letI : Module.Free R I := h (M := R) (N := I)
    have hrank : Module.rank R I ≤ 1 := by
      simpa [Module.rank_self] using (Submodule.rank_le (s := (I : Submodule R R)))
    exact (Submodule.rank_le_one_iff_isPrincipal (W := (I : Submodule R R))).1 hrank

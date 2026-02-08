import Mathlib

open MatrixGroups
open scoped OnePoint

set_option maxHeartbeats 0

local instance : DecidableEq (SL(2, ZMod 3)) := by
  dsimp [Matrix.SpecialLinearGroup]
  infer_instance

local instance : Fintype (OnePoint (ZMod 3)) := by
  dsimp [OnePoint]
  infer_instance

local instance : DecidableEq (OnePoint (ZMod 3)) := by
  dsimp [OnePoint]
  infer_instance

local instance : DecidablePred (· ∈ Subgroup.center (SL(2, ZMod 3))) := by
  intro x
  refine
    decidable_of_iff (∀ y : SL(2, ZMod 3), y * x = x * y)
      (Subgroup.mem_center_iff (G := SL(2, ZMod 3)) (z := x)).symm

local instance : DecidableEq (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) := by
  infer_instance

local instance : Fintype (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) :=
  Fintype.ofSurjective (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 3))))
    (QuotientGroup.mk'_surjective (Subgroup.center (SL(2, ZMod 3))))

/-- The natural action of `SL(2, ZMod 3)` on the projective line `OnePoint (ZMod 3)`,
packaged as a permutation representation. -/
noncomputable def sl2ToPermOnePoint :
    SL(2, ZMod 3) →* Equiv.Perm (OnePoint (ZMod 3)) :=
  (MulAction.toPermHom (GL (Fin 2) (ZMod 3)) (OnePoint (ZMod 3))).comp
    (Matrix.SpecialLinearGroup.toGL : SL(2, ZMod 3) →* GL (Fin 2) (ZMod 3))

/-- For the Möbius action, the center acts trivially, so the representation descends to the
quotient `SL(2, ZMod 3) ⧸ Z(SL(2, ZMod 3))`. -/
lemma center_le_ker_sl2ToPermOnePoint :
    Subgroup.center (SL(2, ZMod 3)) ≤ (sl2ToPermOnePoint).ker := by
  intro g hg
  -- Use the description of the center of `SL(2, ZMod 3)` as scalar matrices.
  rcases (Matrix.SpecialLinearGroup.mem_center_iff (A := g)).1 hg with ⟨r, hrpow, hscalar⟩
  -- Show the induced permutation is the identity by checking the action on points.
  -- (We avoid computation: the `GL₂` action on `OnePoint` is not executable.)
  show sl2ToPermOnePoint g = 1
  ext x
  -- Unfold the action via `MulAction.toPermHom` and reduce to the Möbius action.
  simp [sl2ToPermOnePoint, MulAction.toPermHom_apply]
  -- Rewrite matrix entries using the scalar matrix description.
  have hmat :
      ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) :
          Matrix (Fin 2) (Fin 2) (ZMod 3)) =
        Matrix.scalar (Fin 2) r := by
    simpa using hscalar.symm
  have hg10 :
      (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 0 = 0 := by
    simpa [Matrix.scalar_apply] using congrArg (fun M => M 1 0) hmat
  have hg01 :
      (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 1 = 0 := by
    simpa [Matrix.scalar_apply] using congrArg (fun M => M 0 1) hmat
  have hg00 :
      (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 0 = r := by
    simpa [Matrix.scalar_apply] using congrArg (fun M => M 0 0) hmat
  have hg11 :
      (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 1 = r := by
    simpa [Matrix.scalar_apply] using congrArg (fun M => M 1 1) hmat
  have hr0 : (r : ZMod 3) ≠ 0 := by
    intro hr0
    have hrpow' := hrpow
    simp [hr0] at hrpow'
  -- Now compute the action on `∞` and on finite points.
  cases x with
  | infty =>
      simp [OnePoint.smul_infty_eq_ite, hg10]
  | coe a =>
      -- In the non-`∞` case, the Möbius formula simplifies to `(r * a) / r = a`.
      -- Expand the Möbius action and simplify using the scalar matrix entries.
      simp [OnePoint.smul_some_eq_ite, hg10, hg01, hg00, hg11, hr0, mul_div_cancel_left₀]

/-- The descended permutation representation of `PSL(2, 3)` on `OnePoint (ZMod 3)`. -/
noncomputable def psl2ToPermOnePoint :
    SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3)) →* Equiv.Perm (OnePoint (ZMod 3)) :=
  QuotientGroup.lift (Subgroup.center (SL(2, ZMod 3))) sl2ToPermOnePoint
    center_le_ker_sl2ToPermOnePoint

/-- This descended action is faithful (checked by computation on the finite group). -/
lemma psl2ToPermOnePoint_injective : Function.Injective psl2ToPermOnePoint := by
  classical
  -- Show that the kernel of the original action is the center.
  have hker_sl_le : (sl2ToPermOnePoint).ker ≤ Subgroup.center (SL(2, ZMod 3)) := by
    intro g hg
    -- Unpack `g ∈ ker`.
    have hg' : sl2ToPermOnePoint g = 1 := by
      simpa [MonoidHom.mem_ker] using hg
    -- The element `g` acts trivially on `OnePoint (ZMod 3)`.
    have hfix :
        ∀ x : OnePoint (ZMod 3),
          (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) • x = x := by
      intro x
      have := congrArg (fun σ : Equiv.Perm (OnePoint (ZMod 3)) => σ x) hg'
      simpa [sl2ToPermOnePoint, MulAction.toPermHom_apply] using this
    -- Use fixed points `∞`, `0`, `1` to show `g` is scalar, hence central.
    have hg10 : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 0 = 0 := by
      have hinfty :
          (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) • (∞ : OnePoint (ZMod 3)) =
            (∞ : OnePoint (ZMod 3)) := by
        simpa using hfix (∞ : OnePoint (ZMod 3))
      exact (OnePoint.smul_infty_eq_self_iff (g := (Matrix.SpecialLinearGroup.toGL g :
        GL (Fin 2) (ZMod 3)))).1 hinfty

    have hg11ne : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 1 ≠ 0 := by
      have h0 :
          (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) •
              ((0 : ZMod 3) : OnePoint (ZMod 3)) =
            ((0 : ZMod 3) : OnePoint (ZMod 3)) := by
        simpa using hfix (0 : ZMod 3)
      -- If the denominator vanishes, the action sends `0` to `∞`, contradiction.
      intro h11
      have : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) •
            ((0 : ZMod 3) : OnePoint (ZMod 3)) = (∞ : OnePoint (ZMod 3)) := by
        simp [OnePoint.smul_some_eq_ite, hg10, h11]
      have h0' := h0
      simp [this] at h0'
    have hg11ne0 : ((↑g : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 1) ≠ 0 := by
      simpa using hg11ne

    have hg01 : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 1 = 0 := by
      have h0 :
          (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) •
              ((0 : ZMod 3) : OnePoint (ZMod 3)) =
            ((0 : ZMod 3) : OnePoint (ZMod 3)) := by
        simpa using hfix (0 : ZMod 3)
      have hdiv :
          ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 1) /
              ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 1) =
            (0 : ZMod 3) := by
        have h0' := h0
        simp [OnePoint.smul_some_eq_ite, hg10] at h0'
        simp [hg11ne0] at h0'
        have h01 : (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 1 = 0 := by
          simpa using h0'
        exact (div_eq_zero_iff).2 (Or.inl h01)
      have : ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 1 = 0) ∨
          ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 1 = 0) :=
        (div_eq_zero_iff).1 hdiv
      exact this.resolve_right hg11ne

    have hg00eq :
        (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 0 =
          (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 1 := by
      have h1 :
          (Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) •
              ((1 : ZMod 3) : OnePoint (ZMod 3)) =
            ((1 : ZMod 3) : OnePoint (ZMod 3)) := by
        simpa using hfix (1 : ZMod 3)
      have hdiv :
          ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 0 0) /
              ((Matrix.SpecialLinearGroup.toGL g : GL (Fin 2) (ZMod 3)) 1 1) =
            (1 : ZMod 3) := by
        have h1' := h1
        simp [OnePoint.smul_some_eq_ite, hg10, hg01] at h1'
        simp [hg11ne0] at h1'
        simpa using h1'
      -- Clear the denominator.
      simpa using (div_eq_iff hg11ne).1 hdiv
    -- Translate the matrix equalities back to `g : SL(2, ZMod 3)` using the coercions.
    have hg10' : g 1 0 = 0 := by
      simpa using hg10
    have hg01' : g 0 1 = 0 := by
      simpa using hg01
    have hg00eq' : g 0 0 = g 1 1 := by
      simpa using hg00eq
    -- Let `r` be the common diagonal entry.
    refine (Matrix.SpecialLinearGroup.mem_center_iff (A := g)).2 ?_
    refine ⟨g 0 0, ?_, ?_⟩
    · -- Show `(g 0 0)^2 = 1` using `det g = 1` and the vanishing off-diagonal entries.
      have hdet :
          g 0 0 * g 1 1 - g 0 1 * g 1 0 = (1 : ZMod 3) := by
        have hdet' : Matrix.det (↑g : Matrix (Fin 2) (Fin 2) (ZMod 3)) = (1 : ZMod 3) := by
          exact g.prop
        rw [Matrix.det_fin_two] at hdet'
        simpa using hdet'
      -- Simplify using the computed entries.
      have : g 0 0 ^ 2 = (1 : ZMod 3) := by
        -- `g 0 0 * g 1 1 = (g 0 0)^2` and the off-diagonal term vanishes.
        simpa [hg00eq', hg01', hg10', pow_two] using hdet
      simpa using this
    · -- Show the matrix is scalar.
      -- `scalar (Fin 2) (g 0 0)` has the same four entries.
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hg00eq', hg01', hg10']
  have hker_sl_eq : (sl2ToPermOnePoint).ker = Subgroup.center (SL(2, ZMod 3)) := by
    apply le_antisymm
    · exact hker_sl_le
    · exact center_le_ker_sl2ToPermOnePoint
  -- Then the kernel of the descended action is trivial, hence it is injective.
  have hker_psl : (psl2ToPermOnePoint).ker = ⊥ := by
    -- `ker (lift N φ) = map (mk' N) (ker φ)`
    have hker_lift :=
      QuotientGroup.ker_lift (N := Subgroup.center (SL(2, ZMod 3))) (φ := sl2ToPermOnePoint)
        center_le_ker_sl2ToPermOnePoint
    -- The image of the center under the quotient map is trivial.
    have hmap :
        Subgroup.map (QuotientGroup.mk' (Subgroup.center (SL(2, ZMod 3))))
            (Subgroup.center (SL(2, ZMod 3))) =
          (⊥ : Subgroup (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3)))) := by
      ext q
      constructor
      · rintro ⟨g, hg, rfl⟩
        -- `mk'` sends the center to `1` in the quotient.
        simpa [Subgroup.mem_bot] using (QuotientGroup.eq_one_iff (N := Subgroup.center (SL(2, ZMod 3))) g).2 hg
      · intro hq
        -- The bottom subgroup contains only `1`.
        have hq' : q = 1 := by simpa [Subgroup.mem_bot] using hq
        subst hq'
        refine ⟨1, ?_, by simp⟩
        simp
    -- Put everything together.
    simpa [psl2ToPermOnePoint, hker_sl_eq, hmap] using hker_lift
  exact (MonoidHom.ker_eq_bot_iff psl2ToPermOnePoint).1 hker_psl

/-- A convenient identification `OnePoint (ZMod 3) ≃ Fin 4` (since `|ZMod 3| = 3`). -/
noncomputable def onePointZMod3EquivFin4 : OnePoint (ZMod 3) ≃ Fin 4 := by
  classical
  have hcard : Fintype.card (OnePoint (ZMod 3)) = 4 := by
    -- `OnePoint` is `Option`, so its cardinality is `|ZMod 3| + 1 = 4`.
    have hz : Fintype.card (ZMod 3) = 3 := by simp
    calc
      Fintype.card (OnePoint (ZMod 3)) = Fintype.card (Option (ZMod 3)) := by rfl
      _ = Fintype.card (ZMod 3) + 1 := by simp
      _ = 3 + 1 := by simp [hz]
      _ = 4 := by norm_num
  exact Fintype.equivFinOfCardEq hcard

/-- Transport the action along `OnePoint (ZMod 3) ≃ Fin 4`. -/
noncomputable def psl2ToPermFin4 :
    SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3)) →* Equiv.Perm (Fin 4) :=
  (onePointZMod3EquivFin4.permCongrHom.toMonoidHom).comp psl2ToPermOnePoint

/-- The image of `PSL(2, 3)` in `S₄` lands in `A₄` (checked by computation). -/
lemma psl2ToPermFin4_mem_alternating :
    ∀ q, psl2ToPermFin4 q ∈ alternatingGroup (Fin 4) := by
  classical
  -- Show that the range has index `2` in `S₄`, hence it is `A₄`.
  have hinjPermCongr :
      Function.Injective (onePointZMod3EquivFin4.permCongrHom.toMonoidHom) :=
    onePointZMod3EquivFin4.permCongrHom.injective
  have hinjPerm : Function.Injective psl2ToPermFin4 :=
    hinjPermCongr.comp psl2ToPermOnePoint_injective
  -- Compute the cardinality of `PSL(2, 3)` as a quotient of `SL(2, 3)` by its center.
  have hcard_sl2 : Fintype.card (SL(2, ZMod 3)) = 24 := by
    -- This is a finite computation on `2×2` matrices over `ZMod 3`.
    decide
  have hcard_center : Fintype.card (Subgroup.center (SL(2, ZMod 3))) = 2 := by
    -- `Z(SL₂(F₃)) ≃ μ₂(F₃)`, and `-1` is a primitive `2`-nd root of unity in characteristic `3`.
    have hprim : IsPrimitiveRoot (-1 : ZMod 3) 2 := by
      simpa using (IsPrimitiveRoot.neg_one (R := ZMod 3) (p := 3) (by decide))
    have hμ : Fintype.card (rootsOfUnity 2 (ZMod 3)) = 2 := hprim.card_rootsOfUnity
    -- Transport the cardinality along `center_equiv_rootsOfUnity`.
    have hmax : max (Fintype.card (Fin 2)) 1 = 2 := by decide
    have hcongr :
        Fintype.card (Subgroup.center (SL(2, ZMod 3))) =
          Fintype.card (rootsOfUnity 2 (ZMod 3)) := by
      simpa [hmax] using
        Fintype.card_congr
          (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := ZMod 3)).toEquiv
    simpa [hcongr] using hμ
  have hcard_psl :
      Fintype.card (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) = 12 := by
    -- Use the cardinality formula `|G| = |G ⧸ Z(G)| * |Z(G)|`.
    have hmul :
        Fintype.card (SL(2, ZMod 3)) =
          Fintype.card (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) *
            Fintype.card (Subgroup.center (SL(2, ZMod 3))) := by
      simpa [Nat.card_eq_fintype_card] using
        (Subgroup.card_eq_card_quotient_mul_card_subgroup (α := SL(2, ZMod 3))
          (Subgroup.center (SL(2, ZMod 3))))
    have hmul' :
        24 =
          Fintype.card (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) * 2 := by
      simpa [hcard_sl2, hcard_center, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    have hmul'' :
        Fintype.card (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) * 2 = 12 * 2 := by
      calc
        Fintype.card (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) * 2 = 24 := hmul'.symm
        _ = 12 * 2 := by norm_num
    exact Nat.mul_right_cancel (by decide : 0 < 2) hmul''
  -- Now compute the index of the range subgroup in `S₄`.
  have hcard_range : Fintype.card (psl2ToPermFin4.range) = 12 := by
    -- `|range| = |domain|` since `psl2ToPermFin4` is injective.
    have :
        Fintype.card (SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3))) =
          Fintype.card (psl2ToPermFin4.range) :=
      Fintype.card_congr (Equiv.ofInjective (psl2ToPermFin4 : _ → Equiv.Perm (Fin 4)) hinjPerm)
    simpa [hcard_psl] using this.symm
  have hcard_s4 : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by decide
  have hindex_range : (psl2ToPermFin4.range).index = 2 := by
    -- Use `index_mul_card` on the range subgroup.
    have hmul : (psl2ToPermFin4.range).index * Fintype.card (psl2ToPermFin4.range) =
        Fintype.card (Equiv.Perm (Fin 4)) := by
      simpa [Nat.card_eq_fintype_card] using (psl2ToPermFin4.range).index_mul_card
    have hcard_range' :
        Fintype.card { x // ∃ x_1, psl2ToPermFin4 x_1 = x } = 12 := by
      simpa using hcard_range
    have hmul' : (psl2ToPermFin4.range).index * 12 = 24 := by
      simpa [hcard_range', hcard_s4] using hmul
    have hmul'' : (psl2ToPermFin4.range).index * 12 = 2 * 12 := by
      calc
        (psl2ToPermFin4.range).index * 12 = 24 := hmul'
        _ = 2 * 12 := by norm_num
    exact Nat.mul_right_cancel (by decide : 0 < 12) hmul''
  have hrange :
      psl2ToPermFin4.range = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two (α := Fin 4) (G := psl2ToPermFin4.range)
      hindex_range
  intro q
  have : psl2ToPermFin4 q ∈ psl2ToPermFin4.range := ⟨q, rfl⟩
  simpa [hrange] using this

/-- The resulting hom `PSL(2, 3) → A₄` obtained by `codRestrict`. -/
noncomputable def psl2ToAlternatingGroupFin4 :
    SL(2, ZMod 3) ⧸ Subgroup.center (SL(2, ZMod 3)) →* alternatingGroup (Fin 4) :=
  psl2ToPermFin4.codRestrict (alternatingGroup (Fin 4)) psl2ToPermFin4_mem_alternating

/-- The final map `PSL(2, 3) → A₄` is injective (checked by computation). -/
lemma psl2ToAlternatingGroupFin4_injective :
    Function.Injective psl2ToAlternatingGroupFin4 := by
  classical
  have hinjPermCongr :
      Function.Injective (onePointZMod3EquivFin4.permCongrHom.toMonoidHom) :=
    onePointZMod3EquivFin4.permCongrHom.injective
  have hinjPerm : Function.Injective psl2ToPermFin4 :=
    hinjPermCongr.comp psl2ToPermOnePoint_injective
  intro x y hxy
  apply hinjPerm
  -- Reduce to the equality in `S₄` by forgetting the subgroup structure.
  simpa [psl2ToAlternatingGroupFin4] using congrArg Subtype.val hxy

/--
Prove that \( SL_2(\mathbb{F}_3) / Z(SL_2(\mathbb{F}_3)) < A_4 \).
-/
theorem exists_sl_quot_center_monoidHom_alternatingGroup :
    ∃ φ : SL(2,ZMod 3) ⧸ Subgroup.center SL(2,ZMod 3) →* alternatingGroup (Fin 4),
    Function.Injective φ := by
  refine ⟨psl2ToAlternatingGroupFin4, psl2ToAlternatingGroupFin4_injective⟩

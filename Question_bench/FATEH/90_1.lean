import Mathlib

open scoped CategoryTheory

universe u v w

namespace CategoryTheory

open Abelian

namespace ShortComplex

namespace ShortExact

/-!
This helper lemma is a small bridge between the `Ext` class of a short exact sequence and
splittings: the class in `Ext¹` vanishes iff the inclusion admits a retraction.

It is proved using the contravariant long exact sequence of `Ext` (exactness at `Ext⁰`).
-/
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable {S : ShortComplex C} (hS : S.ShortExact)

lemma extClass_eq_zero_iff_exists_retraction :
    hS.extClass = 0 ↔ ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 S.X₁ := by
  classical
  constructor
  · intro h
    have hx₁ :
        hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 S.X₁)) (c := 1) (by simp) = 0 := by
      simpa [Abelian.Ext.comp_mk₀_id] using h
    rcases
        Abelian.Ext.contravariant_sequence_exact₁ (hS := hS) (Y := S.X₁) (n₀ := 0) (n₁ := 1)
          (x₁ := Abelian.Ext.mk₀ (𝟙 S.X₁)) (hn₁ := by simp) hx₁ with
      ⟨x₂, hx₂⟩
    let r : S.X₂ ⟶ S.X₁ := Abelian.Ext.homEquiv₀ x₂
    refine ⟨r, ?_⟩
    have hx₂' :
        (Abelian.Ext.mk₀ S.f).comp (Abelian.Ext.mk₀ r) (zero_add 0) = Abelian.Ext.mk₀ (𝟙 S.X₁) := by
      simpa [r, Abelian.Ext.mk₀_homEquiv₀_apply] using hx₂
    have hx₂'' : Abelian.Ext.mk₀ (S.f ≫ r) = Abelian.Ext.mk₀ (𝟙 S.X₁) := by
      simpa [Abelian.Ext.mk₀_comp_mk₀] using hx₂'
    have hinj :
        Function.Injective (Abelian.Ext.mk₀ (X := S.X₁) (Y := S.X₁)) :=
      (Abelian.Ext.mk₀_bijective (X := S.X₁) (Y := S.X₁)).1
    exact hinj hx₂''
  · rintro ⟨r, hr⟩
    have hx₁ :
        (Abelian.Ext.mk₀ S.f).comp (Abelian.Ext.mk₀ r) (zero_add 0) = Abelian.Ext.mk₀ (𝟙 S.X₁) := by
      simp [Abelian.Ext.mk₀_comp_mk₀, hr]
    have hx :
        hS.extClass.comp (Abelian.Ext.mk₀ (𝟙 S.X₁)) (c := 1) (by simp) = 0 := by
      simpa [hx₁] using
        (ShortComplex.ShortExact.extClass_comp_assoc (hS := hS) (γ := Abelian.Ext.mk₀ r)
          (n := 0) (n' := 1) (h := by simp))
    simpa [Abelian.Ext.comp_mk₀_id] using hx

end ShortExact

end ShortComplex

end CategoryTheory

/-
Suppose that \( R \) is a Noetherian local ring with maximal ideal \( \mathfrak{m} \)
and residue field \( \kappa \). In this case the projective dimension of \( \kappa \)
is \( \geq \dim_{\kappa} \mathfrak{m} / \mathfrak{m}^{2} \).
-/
/-- Field case: the cotangent space has finrank 0, but the residue field module is nonzero. -/
lemma not_hasProjectiveDimensionLT_finrank_cotangentSpace_of_isField {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hR : IsField R) :
      ¬ CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of R (IsLocalRing.ResidueField R))
          (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) := by
  have hfin :
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 0 :=
    (IsLocalRing.finrank_cotangentSpace_eq_zero_iff (R := R)).2 hR
  have hnot :
      ¬ CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of R (IsLocalRing.ResidueField R)) 0 := by
    intro hpd
    have hzero : CategoryTheory.Limits.IsZero (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
      (CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero
        (X := ModuleCat.of R (IsLocalRing.ResidueField R))).1 hpd
    have hsub : Subsingleton (IsLocalRing.ResidueField R) :=
      (ModuleCat.isZero_iff_subsingleton
        (M := ModuleCat.of R (IsLocalRing.ResidueField R))).1 hzero
    have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
    exact zero_ne_one h01
  simpa [hfin] using hnot

/-- If the residue field is a projective `R`-module, then `R` is a field. -/
lemma isField_of_projective_residueField (R : Type) [CommRing R] [IsLocalRing R]
    [CategoryTheory.Projective (ModuleCat.of R (IsLocalRing.ResidueField R))] :
    IsField R := by
  classical
  let e : ModuleCat.of R R ⟶ ModuleCat.of R (IsLocalRing.ResidueField R) :=
    ModuleCat.ofHom (Algebra.linearMap R (IsLocalRing.ResidueField R))
  have he : CategoryTheory.Epi e := by
    refine (ModuleCat.epi_iff_surjective e).2 ?_
    simpa [e, IsLocalRing.residue] using
      (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal R) :
        Function.Surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)))
  letI : CategoryTheory.Epi e := he
  let sec : ModuleCat.of R (IsLocalRing.ResidueField R) ⟶ ModuleCat.of R R :=
    CategoryTheory.Projective.factorThru (f := 𝟙 (ModuleCat.of R (IsLocalRing.ResidueField R)))
      (e := e)
  have hsec :
      sec ≫ e = 𝟙 (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
    simp [sec]
  let u : R := sec (1 : IsLocalRing.ResidueField R)
  have hu1 : IsLocalRing.residue R u = (1 : IsLocalRing.ResidueField R) := by
    have := congrArg (fun g => g (1 : IsLocalRing.ResidueField R)) hsec
    simpa [u, e, IsLocalRing.residue] using this
  have hu_not_mem : u ∉ IsLocalRing.maximalIdeal R := by
    intro hu_mem
    have hu0 : IsLocalRing.residue R u = 0 := by
      simpa [IsLocalRing.residue] using
        (Ideal.Quotient.eq_zero_iff_mem (I := IsLocalRing.maximalIdeal R) (a := u)).2 hu_mem
    have : (1 : IsLocalRing.ResidueField R) = 0 :=
      hu1.symm.trans hu0
    exact one_ne_zero this
  have hu_unit : IsUnit u :=
    (IsLocalRing.notMem_maximalIdeal (R := R) (x := u)).1 hu_not_mem
  have hm_le : IsLocalRing.maximalIdeal R ≤ (⊥ : Ideal R) := by
    intro x hx
    have hx0 : IsLocalRing.residue R x = 0 := by
      simpa [IsLocalRing.residue] using
        (Ideal.Quotient.eq_zero_iff_mem (I := IsLocalRing.maximalIdeal R) (a := x)).2 hx
    have hxsmul : x • (1 : IsLocalRing.ResidueField R) = 0 := by
      simp [Algebra.smul_def, hx0]
    have hxmul : x * u = 0 := by
      have hx' : x • u = 0 := by
        calc
          x • u = x • sec (1 : IsLocalRing.ResidueField R) := by simp [u]
          _ = sec (x • (1 : IsLocalRing.ResidueField R)) := by
              exact (sec.hom.map_smul x (1 : IsLocalRing.ResidueField R)).symm
          _ = sec 0 := by simp [hxsmul]
          _ = 0 := by simp
      simpa [smul_eq_mul] using hx'
    rcases hu_unit with ⟨u', hu'⟩
    have : x = 0 := by
      have hxmul' : x * (↑u' : R) = 0 := by simpa [hu'] using hxmul
      have := congrArg (fun t : R => t * (↑(u'⁻¹) : R)) hxmul'
      simpa [mul_assoc] using this
    simp [this]
  have hm : IsLocalRing.maximalIdeal R = (⊥ : Ideal R) :=
    le_antisymm hm_le bot_le
  exact (IsLocalRing.isField_iff_maximalIdeal_eq (R := R)).2 hm

/-- If `R` is not a field, then its residue field has projective dimension at least `1`. -/
lemma one_le_projectiveDimension_residueField_of_not_isField (R : Type) [CommRing R]
    [IsLocalRing R] (hR : ¬ IsField R) :
    (1 : ℕ) ≤
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  classical
  refine
    (CategoryTheory.projectiveDimension_ge_iff
        (X := ModuleCat.of R (IsLocalRing.ResidueField R)) (n := 1)).2 ?_
  intro hpd
  have hproj : CategoryTheory.Projective (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one
      (X := ModuleCat.of R (IsLocalRing.ResidueField R))).2 hpd
  have : IsField R := by
    classical
    letI : CategoryTheory.Projective (ModuleCat.of R (IsLocalRing.ResidueField R)) := hproj
    exact isField_of_projective_residueField (R := R)
  exact hR this

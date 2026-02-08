import Mathlib

open IntermediateField
open Module

namespace Question_bench.FATEH38

open Multiplicative

variable {p : ℕ} [Fact p.Prime]

/-- The subgroup of `Multiplicative (ZMod p × ZMod p)` consisting of elements with second
coordinate `0` (the first coordinate axis). -/
def axis1 : Subgroup (Multiplicative (ZMod p × ZMod p)) where
  carrier := {x | x.toAdd.2 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : x.toAdd.2 = 0 := by simpa using hx
    have hy' : y.toAdd.2 = 0 := by simpa using hy
    -- `toAdd_mul` turns multiplication into addition on coordinates.
    simp [toAdd_mul, hx', hy']
  inv_mem' := by
    intro x hx
    have hx' : x.toAdd.2 = 0 := by simpa using hx
    simp [toAdd_inv, hx']

/-- The subgroup of `Multiplicative (ZMod p × ZMod p)` consisting of elements with first
coordinate `0` (the second coordinate axis). -/
def axis2 : Subgroup (Multiplicative (ZMod p × ZMod p)) where
  carrier := {x | x.toAdd.1 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    have hx' : x.toAdd.1 = 0 := by simpa using hx
    have hy' : y.toAdd.1 = 0 := by simpa using hy
    simp [toAdd_mul, hx', hy']
  inv_mem' := by
    intro x hx
    have hx' : x.toAdd.1 = 0 := by simpa using hx
    simp [toAdd_inv, hx']

lemma axis1_card : Nat.card (axis1 (p := p)) = p := by
  classical
  let e : axis1 (p := p) ≃ ZMod p :=
    { toFun := fun x => x.1.toAdd.1
      invFun := fun a =>
        ⟨Multiplicative.ofAdd (a, 0), by simp [axis1]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Multiplicative.ext
        -- Compare after applying `toAdd`.
        ext
        · simp
        · simpa [axis1] using x.property.symm
      right_inv := by
        intro a
        simp }
  simpa [Nat.card_zmod] using (Nat.card_congr e)

lemma axis2_card : Nat.card (axis2 (p := p)) = p := by
  classical
  let e : axis2 (p := p) ≃ ZMod p :=
    { toFun := fun x => x.1.toAdd.2
      invFun := fun a =>
        ⟨Multiplicative.ofAdd (0, a), by simp [axis2]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Multiplicative.ext
        -- Compare after applying `toAdd`.
        ext
        · simpa [axis2] using x.property.symm
        · simp
      right_inv := by
        intro a
        simp }
  simpa [Nat.card_zmod] using (Nat.card_congr e)

lemma axis_inf : axis1 (p := p) ⊓ axis2 (p := p) = ⊥ := by
  ext x
  constructor
  · intro hx
    have hx1 : x.toAdd.2 = 0 := hx.1
    have hx2 : x.toAdd.1 = 0 := hx.2
    have : x.toAdd = 0 := by
      ext <;> simp [hx1, hx2]
    exact (toAdd_eq_zero (x := x)).1 this
  · intro hx
    subst hx
    simp [axis1, axis2]

lemma card_zmodProd : Nat.card (Multiplicative (ZMod p × ZMod p)) = p ^ 2 := by
  classical
  calc
    Nat.card (Multiplicative (ZMod p × ZMod p)) = Nat.card (ZMod p × ZMod p) := by
      exact Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p × ZMod p) ≃ _)
    _ = Nat.card (ZMod p) * Nat.card (ZMod p) := by simp
    _ = p ^ 2 := by simp [pow_two]

end Question_bench.FATEH38

/-Let $p$ be a prime number and let $F$ be a field containing $p$-th roots of unity.
Let $K$ be a Galois extension of $F$ with Galois group $\mathbb{Z}_p \times \mathbb{Z}_p$.
Show that there exist two elements $\alpha, \beta \in K^\times$ such that
$K= F(\alpha, \beta)$ and $a = \alpha^p, b = \beta^p \in F$.-/
set_option maxHeartbeats 400000 in
/-- Kummer-style generators for a `ZMod p × ZMod p` Galois extension. -/
theorem exists_pow_p_mem_algebraMap_and_adjoin_eq_top {p : Nat} [Fact p.Prime]
    {F K : Type} [Field F] (hF : (primitiveRoots p F).Nonempty) [Field K] [Algebra F K]
    [IsGalois F K] (hK : (K ≃ₐ[F] K) ≃* Multiplicative (ZMod p × ZMod p)) :
    ∃ (α β : K), α ≠ 0 ∧ β ≠ 0 ∧ α ^ p ∈ (algebraMap F K).range ∧ β ^ p ∈ (algebraMap F K).range ∧
    IntermediateField.adjoin F {α, β} = ⊤ := by
  classical
  -- `Gal(K/F)` is finite since it is (abstractly) `ZMod p × ZMod p`.
  haveI : Finite (Gal(K/F)) := by
    classical
    exact Finite.of_equiv (Multiplicative (ZMod p × ZMod p)) hK.toEquiv.symm
  haveI : FiniteDimensional F K :=
    IsGalois.finiteDimensional_of_finite (F := F) (E := K)

  let A₁ : Subgroup (Multiplicative (ZMod p × ZMod p)) := Question_bench.FATEH38.axis1 (p := p)
  let A₂ : Subgroup (Multiplicative (ZMod p × ZMod p)) := Question_bench.FATEH38.axis2 (p := p)
  have hA₁ : Nat.card A₁ = p := by
    simpa [A₁] using (Question_bench.FATEH38.axis1_card (p := p))
  have hA₂ : Nat.card A₂ = p := by
    simpa [A₂] using (Question_bench.FATEH38.axis2_card (p := p))
  have hA_inf : A₁ ⊓ A₂ = ⊥ := by
    simpa [A₁, A₂] using (Question_bench.FATEH38.axis_inf (p := p))

  let H₁ : Subgroup (Gal(K/F)) := A₁.comap hK.toMonoidHom
  let H₂ : Subgroup (Gal(K/F)) := A₂.comap hK.toMonoidHom

  have hH₁ : Nat.card H₁ = p := by
    have hcomap : A₁.comap hK.toMonoidHom = A₁.map hK.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm' hK A₁
    have hcardMap : Nat.card (A₁.map hK.symm.toMonoidHom) = p := by
      calc
        Nat.card (A₁.map hK.symm.toMonoidHom) = Nat.card A₁ := by
          simpa using (Nat.card_congr (hK.symm.subgroupMap A₁).toEquiv).symm
        _ = p := hA₁
    simpa [H₁, hcomap] using hcardMap

  have hH₂ : Nat.card H₂ = p := by
    have hcomap : A₂.comap hK.toMonoidHom = A₂.map hK.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm' hK A₂
    have hcardMap : Nat.card (A₂.map hK.symm.toMonoidHom) = p := by
      calc
        Nat.card (A₂.map hK.symm.toMonoidHom) = Nat.card A₂ := by
          simpa using (Nat.card_congr (hK.symm.subgroupMap A₂).toEquiv).symm
        _ = p := hA₂
    simpa [H₂, hcomap] using hcardMap

  have hH_inf : H₁ ⊓ H₂ = ⊥ := by
    calc
      H₁ ⊓ H₂ = (A₁ ⊓ A₂).comap hK.toMonoidHom := by
        simpa [H₁, H₂] using (Subgroup.comap_inf A₁ A₂ hK.toMonoidHom).symm
      _ = (⊥ : Subgroup (Multiplicative (ZMod p × ZMod p))).comap hK.toMonoidHom := by
          simp [hA_inf]
      _ = ⊥ := by
          -- `⊥.comap` is the kernel, and `hK.toMonoidHom` is injective.
          simpa using (hK.toMonoidHom.ker_eq_bot_iff.2 hK.injective)

  have hfinrank_FK : finrank F K = p ^ 2 := by
    have hcardG : Nat.card (Gal(K/F)) = p ^ 2 := by
      calc
        Nat.card (Gal(K/F)) = Nat.card (Multiplicative (ZMod p × ZMod p)) := Nat.card_congr hK.toEquiv
        _ = p ^ 2 := Question_bench.FATEH38.card_zmodProd (p := p)
    calc
      finrank F K = Nat.card (Gal(K/F)) := (IsGalois.card_aut_eq_finrank (F := F) (E := K)).symm
      _ = p ^ 2 := hcardG

  -- Degree-`p` fixed fields coming from the axis subgroups.
  haveI : Subgroup.Normal H₁ := by
    dsimp [H₁]
    infer_instance
  haveI : Subgroup.Normal H₂ := by
    dsimp [H₂]
    infer_instance

  let L₁ : IntermediateField F K := IntermediateField.fixedField (F := F) (E := K) H₁
  let L₂ : IntermediateField F K := IntermediateField.fixedField (F := F) (E := K) H₂

  have hLK₁ : finrank L₁ K = p := by
    classical
    letI := Fintype.ofFinite H₁
    have hH₁' : Fintype.card H₁ = p := by
      simpa [Nat.card_eq_fintype_card] using hH₁
    simpa [L₁, hH₁'] using
      (IntermediateField.finrank_fixedField_eq_card (F := F) (E := K) (H := H₁))
  have hLK₂ : finrank L₂ K = p := by
    classical
    letI := Fintype.ofFinite H₂
    have hH₂' : Fintype.card H₂ = p := by
      simpa [Nat.card_eq_fintype_card] using hH₂
    simpa [L₂, hH₂'] using
      (IntermediateField.finrank_fixedField_eq_card (F := F) (E := K) (H := H₂))

  have hLF₁ : finrank F L₁ = p := by
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hmul : finrank F L₁ * p = finrank F K := by
      simpa [hLK₁] using (Module.finrank_mul_finrank (F := F) (K := L₁) (A := K))
    have : finrank F L₁ * p = p * p := by
      simpa [hfinrank_FK, pow_two] using hmul
    exact Nat.mul_right_cancel hp0 this

  have hLF₂ : finrank F L₂ = p := by
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have hmul : finrank F L₂ * p = finrank F K := by
      simpa [hLK₂] using (Module.finrank_mul_finrank (F := F) (K := L₂) (A := K))
    have : finrank F L₂ * p = p * p := by
      simpa [hfinrank_FK, pow_two] using hmul
    exact Nat.mul_right_cancel hp0 this

  have hcyc₁ : IsCyclic (Gal(L₁/F)) := by
    have hcard : Nat.card (Gal(L₁/F)) = p := by
      simpa [hLF₁] using (IsGalois.card_aut_eq_finrank (F := F) (E := L₁))
    exact isCyclic_of_prime_card (p := p) hcard

  have hcyc₂ : IsCyclic (Gal(L₂/F)) := by
    have hcard : Nat.card (Gal(L₂/F)) = p := by
      simpa [hLF₂] using (IsGalois.card_aut_eq_finrank (F := F) (E := L₂))
    exact isCyclic_of_prime_card (p := p) hcard

  have hprim₁ : (primitiveRoots (Module.finrank F L₁) F).Nonempty := by
    simpa [hLF₁] using hF
  have hprim₂ : (primitiveRoots (Module.finrank F L₂) F).Nonempty := by
    simpa [hLF₂] using hF

  -- Apply cyclic Kummer theory to each degree-`p` fixed field.
  have hex₁ :
      ∃ γ : L₁, γ ^ p ∈ Set.range (algebraMap F L₁) ∧ F⟮γ⟯ = ⊤ := by
    have tfae := isCyclic_tfae F L₁ hprim₁
    have h13 :
        (IsGalois F L₁ ∧ IsCyclic Gal(L₁/F)) ↔
          ∃ γ : L₁, γ ^ (finrank F L₁) ∈ Set.range (algebraMap F L₁) ∧ F⟮γ⟯ = ⊤ := by
      -- Avoid indexing into the list: `TFAE` is `∀ x∈l, ∀ y∈l, x ↔ y`.
      simpa [List.TFAE] using
        tfae _ (by simp) _ (by simp)
    rcases h13.mp ⟨inferInstance, hcyc₁⟩ with ⟨γ, hγpow, hγtop⟩
    refine ⟨γ, ?_, hγtop⟩
    simpa [hLF₁] using hγpow

  have hex₂ :
      ∃ γ : L₂, γ ^ p ∈ Set.range (algebraMap F L₂) ∧ F⟮γ⟯ = ⊤ := by
    have tfae := isCyclic_tfae F L₂ hprim₂
    have h13 :
        (IsGalois F L₂ ∧ IsCyclic Gal(L₂/F)) ↔
          ∃ γ : L₂, γ ^ (finrank F L₂) ∈ Set.range (algebraMap F L₂) ∧ F⟮γ⟯ = ⊤ := by
      simpa [List.TFAE] using
        tfae _ (by simp) _ (by simp)
    rcases h13.mp ⟨inferInstance, hcyc₂⟩ with ⟨γ, hγpow, hγtop⟩
    refine ⟨γ, ?_, hγtop⟩
    simpa [hLF₂] using hγpow

  rcases hex₁ with ⟨γ₁, hγ₁pow, hγ₁top⟩
  rcases hex₂ with ⟨γ₂, hγ₂pow, hγ₂top⟩

  have hγ₁ne : (γ₁ : L₁) ≠ 0 := by
    intro h0
    have hEq : (F⟮(0 : L₁)⟯ : IntermediateField F L₁) = ⊤ := by simpa [h0] using hγ₁top
    have hbotTop : (⊥ : IntermediateField F L₁) = ⊤ := by
      simpa [IntermediateField.adjoin_zero] using hEq
    have hfin := congrArg (fun E : IntermediateField F L₁ => finrank F E) hbotTop
    have : (1 : ℕ) = p := by simpa [hLF₁] using hfin
    exact (Fact.out : p.Prime).ne_one (this.symm)

  have hγ₂ne : (γ₂ : L₂) ≠ 0 := by
    intro h0
    have hEq : (F⟮(0 : L₂)⟯ : IntermediateField F L₂) = ⊤ := by simpa [h0] using hγ₂top
    have hbotTop : (⊥ : IntermediateField F L₂) = ⊤ := by
      simpa [IntermediateField.adjoin_zero] using hEq
    have hfin := congrArg (fun E : IntermediateField F L₂ => finrank F E) hbotTop
    have : (1 : ℕ) = p := by simpa [hLF₂] using hfin
    exact (Fact.out : p.Prime).ne_one (this.symm)

  let α : K := (γ₁ : K)
  let β : K := (γ₂ : K)

  have hαne : α ≠ 0 := by
    intro h0
    apply hγ₁ne
    ext
    simpa [α] using h0

  have hβne : β ≠ 0 := by
    intro h0
    apply hγ₂ne
    ext
    simpa [β] using h0

  have hαpow : α ^ p ∈ (algebraMap F K).range := by
    rcases hγ₁pow with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      algebraMap F K a = algebraMap L₁ K (algebraMap F L₁ a) := by
        simp
      _ = algebraMap L₁ K (γ₁ ^ p) := by simp [ha]
      _ = (algebraMap L₁ K γ₁) ^ p := by
          exact (algebraMap L₁ K).map_pow γ₁ p
      _ = α ^ p := rfl

  have hβpow : β ^ p ∈ (algebraMap F K).range := by
    rcases hγ₂pow with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      algebraMap F K a = algebraMap L₂ K (algebraMap F L₂ a) := by
        simp
      _ = algebraMap L₂ K (γ₂ ^ p) := by simp [ha]
      _ = (algebraMap L₂ K γ₂) ^ p := by
          exact (algebraMap L₂ K).map_pow γ₂ p
      _ = β ^ p := rfl

  have hadjoinα : (IntermediateField.adjoin F ({α} : Set K)) = L₁ := by
    have := congrArg (IntermediateField.lift (F := L₁)) hγ₁top
    simpa [α] using this

  have hadjoinβ : (IntermediateField.adjoin F ({β} : Set K)) = L₂ := by
    have := congrArg (IntermediateField.lift (F := L₂)) hγ₂top
    simpa [β] using this

  have hLsup : (L₁ ⊔ L₂ : IntermediateField F K) = ⊤ := by
    have hfix₁ : L₁.fixingSubgroup = H₁ := by
      dsimp [L₁]
      exact (IntermediateField.fixingSubgroup_fixedField (F := F) (E := K) (H := H₁))
    have hfix₂ : L₂.fixingSubgroup = H₂ := by
      dsimp [L₂]
      exact (IntermediateField.fixingSubgroup_fixedField (F := F) (E := K) (H := H₂))
    have hfix : (L₁ ⊔ L₂ : IntermediateField F K).fixingSubgroup = ⊥ := by
      calc
        (L₁ ⊔ L₂ : IntermediateField F K).fixingSubgroup =
            L₁.fixingSubgroup ⊓ L₂.fixingSubgroup :=
          IntermediateField.fixingSubgroup_sup (F := F) (E := K) (K := L₁) (L := L₂)
        _ = H₁ ⊓ H₂ := by rw [hfix₁, hfix₂]
        _ = ⊥ := hH_inf
    -- Convert `fixingSubgroup = ⊥` into `L₁ ⊔ L₂ = ⊤` via `fixedField_fixingSubgroup`.
    have hff :
        IntermediateField.fixedField ((L₁ ⊔ L₂ : IntermediateField F K).fixingSubgroup) =
          (L₁ ⊔ L₂ : IntermediateField F K) :=
      IsGalois.fixedField_fixingSubgroup (F := F) (E := K) (K := (L₁ ⊔ L₂ : IntermediateField F K))
    have hff' :
        IntermediateField.fixedField (F := F) (E := K) (⊥ : Subgroup Gal(K/F)) =
          (L₁ ⊔ L₂ : IntermediateField F K) := by
      have hff' := hff
      rw [hfix] at hff'
      exact hff'
    have : (⊤ : IntermediateField F K) = (L₁ ⊔ L₂ : IntermediateField F K) := by
      calc
        (⊤ : IntermediateField F K) =
            IntermediateField.fixedField (F := F) (E := K) (⊥ : Subgroup Gal(K/F)) := by
              exact (IntermediateField.fixedField_bot (F := F) (E := K)).symm
        _ = (L₁ ⊔ L₂ : IntermediateField F K) := hff'
    exact this.symm

  have hadjoin_pair : IntermediateField.adjoin F ({α, β} : Set K) = ⊤ := by
    have hpair : ({α, β} : Set K) = ({α} ∪ {β} : Set K) := by
      ext x
      simp [or_comm]
    rw [hpair]
    -- `adjoin` turns unions into suprema.
    rw [IntermediateField.adjoin_union (F := F) (E := K) (S := ({α} : Set K)) (T := ({β} : Set K))]
    -- Replace each singleton adjoin by the corresponding fixed field, then use `L₁ ⊔ L₂ = ⊤`.
    rw [hadjoinα, hadjoinβ, hLsup]

  exact ⟨α, β, hαne, hβne, hαpow, hβpow, hadjoin_pair⟩

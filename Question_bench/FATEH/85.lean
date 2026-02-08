import Mathlib


open Submodule
open Finset
open Submodule

/-- Powers of the sum ideal act within the sum of the power submodules. -/
lemma pow_sup_pow_submodule_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 ℬ : Ideal A) (n m : ℕ) :
    ((𝒜 + ℬ) ^ (n + m) • ⊤ : Submodule A M) ≤ (𝒜 ^ n • ⊤) ⊔ (ℬ ^ m • ⊤) := by
  have h :
      (𝒜 + ℬ) ^ (n + m) ≤ (𝒜 ^ n ⊔ ℬ ^ m : Ideal A) := by
    simpa [Ideal.add_eq_sup] using
      (Ideal.sup_pow_add_le_pow_sup_pow (I := 𝒜) (J := ℬ) (n := n) (m := m))
  have h' :
      ((𝒜 + ℬ) ^ (n + m) • ⊤ : Submodule A M) ≤
        ((𝒜 ^ n ⊔ ℬ ^ m : Ideal A) • ⊤ : Submodule A M) :=
    Submodule.smul_mono_left (N := (⊤ : Submodule A M)) h
  simpa [Ideal.add_eq_sup, Submodule.sup_smul] using h'

/-
Helper lemmas for the iterated adic completion comparison.
These are small, reusable facts about the quotient maps involved in the proof.
-/

/-- The sum of power submodules is contained in the power of the sum ideal. -/
lemma sup_pow_submodule_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 ℬ : Ideal A) (n : ℕ) :
    ((𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ n • ⊤)) ≤ ((𝒜 + ℬ) ^ n • ⊤ : Submodule A M) := by
  refine sup_le ?_ ?_
  · have h : 𝒜 ^ n ≤ (𝒜 + ℬ) ^ n := by
      simpa [Ideal.add_eq_sup] using
        (pow_le_pow_left' (le_sup_left : 𝒜 ≤ 𝒜 ⊔ ℬ) n)
    simpa using (Submodule.smul_mono_left (N := (⊤ : Submodule A M)) h)
  · have h : ℬ ^ n ≤ (𝒜 + ℬ) ^ n := by
      simpa [Ideal.add_eq_sup] using
        (pow_le_pow_left' (le_sup_right : ℬ ≤ 𝒜 ⊔ ℬ) n)
    simpa using (Submodule.smul_mono_left (N := (⊤ : Submodule A M)) h)

/- Some monotonicity and compatibility lemmas for power sup quotients. -/

/-- The sup of power submodules is monotone in the exponent. -/
lemma sup_pow_submodule_mono {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 ℬ : Ideal A) {m n : ℕ} (h : m ≤ n) :
    ((𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ n • ⊤)) ≤
      ((𝒜 ^ m • ⊤ : Submodule A M) ⊔ (ℬ ^ m • ⊤)) := by
  refine sup_le ?_ ?_
  · have hA : (𝒜 ^ n : Ideal A) ≤ 𝒜 ^ m := Ideal.pow_le_pow_right h
    exact le_trans (Submodule.smul_mono_left (N := (⊤ : Submodule A M)) hA) le_sup_left
  · have hB : (ℬ ^ n : Ideal A) ≤ ℬ ^ m := Ideal.pow_le_pow_right h
    exact le_trans (Submodule.smul_mono_left (N := (⊤ : Submodule A M)) hB) le_sup_right

/-- The composed evaluation map kills `ℬ^m • ⊤`, so it factors through the quotient. -/
lemma eval_mapQ_kills_pow {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] (n m : ℕ) :
    (ℬ ^ m • ⊤ : Submodule A (AdicCompletion 𝒜 M)) ≤
      LinearMap.ker
        ((Submodule.mapQ (p := (𝒜 ^ n • ⊤ : Submodule A M))
              (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ m • ⊤)) (LinearMap.id)
              (by
                exact le_sup_left)) ∘ₗ
          AdicCompletion.eval 𝒜 M n) := by
  intro x hx
  -- Reduce to the generating smul elements in `ℬ^m • ⊤`.
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    -- The quotient `M ⧸ (𝒜^n • ⊤ ⊔ ℬ^m • ⊤)` is annihilated by `ℬ^m`.
    have hz :
        r • ((Submodule.mapQ (p := (𝒜 ^ n • ⊤ : Submodule A M))
                (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ m • ⊤)) (LinearMap.id)
                (by
                  exact le_sup_left)) (AdicCompletion.eval 𝒜 M n y)) = 0 := by
      refine Quotient.inductionOn' ((Submodule.mapQ
        (p := (𝒜 ^ n • ⊤ : Submodule A M)) (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ m • ⊤))
        (LinearMap.id)
        (by
          exact le_sup_left)) (AdicCompletion.eval 𝒜 M n y)) ?_
      intro z
      have hz' : r • z ∈ (ℬ ^ m • ⊤ : Submodule A M) := by
        exact Submodule.smul_mem_smul hr (by simp)
      have hz'' :
          r • z ∈ (𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ m • ⊤) := by
        exact (show (ℬ ^ m • ⊤ : Submodule A M) ≤
            (𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ m • ⊤) from
          le_sup_right) hz'
      change (Submodule.Quotient.mk (p := (𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ m • ⊤))
        (r • z)) = 0
      exact (Submodule.Quotient.mk_eq_zero
        (p := (𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ m • ⊤)) (x := r • z)).2 hz''
    change
        ((Submodule.mapQ (p := (𝒜 ^ n • ⊤ : Submodule A M))
          (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ m • ⊤)) (LinearMap.id)
          (by
            exact le_sup_left)) (AdicCompletion.eval 𝒜 M n (r • y))) = 0
    simpa using hz
  · intro x y hx hy
    exact Submodule.add_mem _ hx hy

/-- The canonical map from the `ℬ^m`-quotient to the sup-quotient. -/
noncomputable def quotPow_to_sup {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] (n m : ℕ) :
    (AdicCompletion 𝒜 M) ⧸ (ℬ ^ m • ⊤ : Submodule A (AdicCompletion 𝒜 M)) →ₗ[A]
      M ⧸ ((𝒜 ^ n • ⊤ : Submodule A M) ⊔ (ℬ ^ m • ⊤)) :=
  Submodule.liftQ
    (p := (ℬ ^ m • ⊤ : Submodule A (AdicCompletion 𝒜 M)))
    ((Submodule.mapQ (p := (𝒜 ^ n • ⊤ : Submodule A M))
        (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ m • ⊤)) (LinearMap.id)
        (by
          exact le_sup_left)) ∘ₗ
      AdicCompletion.eval 𝒜 M n)
    (eval_mapQ_kills_pow (𝒜 := 𝒜) (ℬ := ℬ) (n := n) (m := m))

/-
Compatibility lemmas for the quotient-level maps used in the main equivalence.
-/

/-- `mapQ` on the `𝒜`-power quotients is compatible with `𝒜`-transition maps. -/
lemma mapQ_comp_factorPow {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] {m n : ℕ} (h : m ≤ n) :
    Submodule.factor (sup_pow_submodule_mono (𝒜 := 𝒜) (ℬ := ℬ) h) ∘ₗ
        (Submodule.mapQ (p := (𝒜 ^ n • ⊤ : Submodule A M))
          (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ n • ⊤)) LinearMap.id
          (by
            exact le_sup_left)) =
      (Submodule.mapQ (p := (𝒜 ^ m • ⊤ : Submodule A M))
          (q := (𝒜 ^ m • ⊤) ⊔ (ℬ ^ m • ⊤)) LinearMap.id
          (by
            exact le_sup_left)) ∘ₗ
        AdicCompletion.transitionMap 𝒜 M h := by
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  simp [AdicCompletion.transitionMap]

/-- `quotPow_to_sup` commutes with the transition maps on `ℬ`-power quotients. -/
lemma quotPow_to_sup_comp_transition {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] {m n : ℕ} (h : m ≤ n) :
    Submodule.factor (sup_pow_submodule_mono (𝒜 := 𝒜) (ℬ := ℬ) h) ∘ₗ
        quotPow_to_sup 𝒜 ℬ n n =
      quotPow_to_sup 𝒜 ℬ m m ∘ₗ
        AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h := by
  classical
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  have hmap :=
    LinearMap.congr_fun
      (mapQ_comp_factorPow (𝒜 := 𝒜) (ℬ := ℬ) (m := m) (n := n) h)
      (AdicCompletion.eval 𝒜 M n y)
  have hcomp :=
    congrArg (fun f => f y)
      (AdicCompletion.transitionMap_comp_eval (I := 𝒜) (M := M) h)
  simp only [LinearMap.comp_apply] at hcomp
  have hcomp' :
      AdicCompletion.transitionMap 𝒜 M h (AdicCompletion.eval 𝒜 M n y) =
        AdicCompletion.eval 𝒜 M m y := hcomp
  have hmap' :
      Submodule.factor (sup_pow_submodule_mono (𝒜 := 𝒜) (ℬ := ℬ) h)
          ((Submodule.mapQ (p := (𝒜 ^ n • ⊤ : Submodule A M))
              (q := (𝒜 ^ n • ⊤) ⊔ (ℬ ^ n • ⊤)) (LinearMap.id)
              (by
                exact le_sup_left)) (AdicCompletion.eval 𝒜 M n y)) =
        (Submodule.mapQ (p := (𝒜 ^ m • ⊤ : Submodule A M))
            (q := (𝒜 ^ m • ⊤) ⊔ (ℬ ^ m • ⊤)) (LinearMap.id)
            (by
              exact le_sup_left)) (AdicCompletion.eval 𝒜 M m y) := by
    -- Rewrite the right-hand side using `transitionMap_comp_eval_apply`.
    rw [← hcomp']
    exact hmap
  simpa [quotPow_to_sup, LinearMap.comp_apply, Submodule.liftQ_apply, Submodule.factor_mk,
    AdicCompletion.transitionMap, Submodule.Quotient.mk''_eq_mk] using hmap'

/-- Compatibility of the factor maps from sup-quotients to `(𝒜+ℬ)`-quotients. -/
lemma pow_sup_pow_factor_comp {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] {m n : ℕ} (h : m ≤ n) :
    AdicCompletion.transitionMap (𝒜 + ℬ) M h ∘ₗ
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) n) =
      Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
        Submodule.factor (sup_pow_submodule_mono (𝒜 := 𝒜) (ℬ := ℬ) h) := by
  apply LinearMap.ext
  intro x
  refine Quotient.inductionOn' x ?_
  intro y
  simp [AdicCompletion.transitionMap]

/-- The family defining the forward map is compatible with transition maps. -/
lemma toSum_lift_compatible {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] :
    ∀ {m n : ℕ} (h : m ≤ n),
      AdicCompletion.transitionMap (𝒜 + ℬ) M h ∘ₗ
          (Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) n) ∘ₗ
            quotPow_to_sup 𝒜 ℬ n n ∘ₗ
              AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n) =
        (Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
          quotPow_to_sup 𝒜 ℬ m m ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) m) := by
  classical
  intro m n h
  calc
    AdicCompletion.transitionMap (𝒜 + ℬ) M h ∘ₗ
        (Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) n) ∘ₗ
          quotPow_to_sup 𝒜 ℬ n n ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n) =
        (AdicCompletion.transitionMap (𝒜 + ℬ) M h ∘ₗ
            Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) n)) ∘ₗ
          quotPow_to_sup 𝒜 ℬ n n ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n := by
      ext x
      simp [LinearMap.comp_apply]
    _ =
        (Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
            Submodule.factor (sup_pow_submodule_mono (𝒜 := 𝒜) (ℬ := ℬ) h)) ∘ₗ
          quotPow_to_sup 𝒜 ℬ n n ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n := by
      rw [pow_sup_pow_factor_comp (𝒜 := 𝒜) (ℬ := ℬ) (m := m) (n := n) h]
    _ =
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
          (Submodule.factor (sup_pow_submodule_mono (𝒜 := 𝒜) (ℬ := ℬ) h) ∘ₗ
            quotPow_to_sup 𝒜 ℬ n n) ∘ₗ
          AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n := by
      ext x
      simp [LinearMap.comp_apply]
    _ =
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
          (quotPow_to_sup 𝒜 ℬ m m ∘ₗ
            AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h) ∘ₗ
          AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n := by
      simp [quotPow_to_sup_comp_transition (𝒜 := 𝒜) (ℬ := ℬ) (m := m) (n := n) h]
    _ =
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
          quotPow_to_sup 𝒜 ℬ m m ∘ₗ
            (AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ
              AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n) := by
      simp [LinearMap.comp_assoc]
    _ =
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) m) ∘ₗ
          quotPow_to_sup 𝒜 ℬ m m ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) m := by
      simp [AdicCompletion.transitionMap_comp_eval (I := ℬ) (M := AdicCompletion 𝒜 M) h]

/-
Extra quotient-compatibility lemmas used to build the inverse map `fromSum`.
-/

/-
Simp lemmas for Noether's third isomorphism theorem in the `sup` formulation.
These avoid unfolding `quotientQuotientEquivQuotientSup` in later diagram chases.
-/

namespace Submodule

@[simp]
lemma quotEquivOfEq_symm_mk {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (p p' : Submodule R M) (h : p = p') (x : M) :
    (Submodule.quotEquivOfEq p p' h).symm (Submodule.Quotient.mk (p := p') x) =
      Submodule.Quotient.mk (p := p) x := by
  cases h
  rfl

/-- `Submodule.quotEquivOfEq` is independent of the proof of equality. -/
lemma quotEquivOfEq_congr {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (p p' : Submodule R M) (h₁ h₂ : p = p') :
    Submodule.quotEquivOfEq p p' h₁ = Submodule.quotEquivOfEq p p' h₂ := by
  ext q
  refine Submodule.Quotient.induction_on p q ?_
  intro x
  simp

lemma quotEquivOfEq_symm_congr {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (p p' : Submodule R M) (h₁ h₂ : p = p') :
    (Submodule.quotEquivOfEq p p' h₁).symm = (Submodule.quotEquivOfEq p p' h₂).symm := by
  exact congrArg LinearEquiv.symm (quotEquivOfEq_congr (p := p) (p' := p') h₁ h₂)

/-- A usable formula for `quotientQuotientEquivQuotientSup` on generators. -/
@[simp]
lemma quotientQuotientEquivQuotientSup_mk_mk {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (S T : Submodule R M) (x : M) :
    (quotientQuotientEquivQuotientSup (S := S) (T := T))
        (Submodule.Quotient.mk (p := T.map S.mkQ) (Submodule.Quotient.mk (p := S) x)) =
      Submodule.Quotient.mk (p := S ⊔ T) x := by
  simp [quotientQuotientEquivQuotientSup]
  rfl

/-- A usable formula for the inverse map of `quotientQuotientEquivQuotientSup` on generators. -/
@[simp]
lemma quotientQuotientEquivQuotientSup_symm_mk {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (S T : Submodule R M) (x : M) :
    (quotientQuotientEquivQuotientSup (S := S) (T := T)).symm
        (Submodule.Quotient.mk (p := S ⊔ T) x) =
      Submodule.Quotient.mk (p := T.map S.mkQ) (Submodule.Quotient.mk (p := S) x) := by
  -- Prove by applying the forward equivalence and using its defining action on generators.
  apply (quotientQuotientEquivQuotientSup (S := S) (T := T)).injective
  simpa [quotientQuotientEquivQuotientSup] using
    (show
        (quotientQuotientEquivQuotient (S := S) (T := S ⊔ T) (by exact le_sup_left))
            (Submodule.Quotient.mk (p := (S ⊔ T).map S.mkQ) (Submodule.Quotient.mk (p := S) x)) =
          Submodule.Quotient.mk (p := S ⊔ T) x from rfl).symm

/-- Naturality of `quotientQuotientEquivQuotientSup.symm` with respect to `Submodule.factor`. -/
lemma quotientQuotientEquivQuotientSup_symm_naturality_factor {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (S T₁ T₂ : Submodule R M) (hT : T₁ ≤ T₂) :
    (Submodule.factor (show T₁.map S.mkQ ≤ T₂.map S.mkQ from Submodule.map_mono hT) : _)
        ∘ₗ (quotientQuotientEquivQuotientSup (S := S) (T := T₁)).symm.toLinearMap =
      (quotientQuotientEquivQuotientSup (S := S) (T := T₂)).symm.toLinearMap ∘ₗ
        (Submodule.factor (show S ⊔ T₁ ≤ S ⊔ T₂ from sup_le_sup_left hT S) : _) := by
  -- Reduce to generators of `M ⧸ (S ⊔ T₁)` using `quot_hom_ext`, then `simp`.
  apply Submodule.quot_hom_ext
  intro x
  simp

/-- Naturality of `quotientQuotientEquivQuotientSup.symm` with respect to `Submodule.factor`
when varying the left submodule. -/
lemma quotientQuotientEquivQuotientSup_symm_naturality_factor_left {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] (S₁ S₂ T : Submodule R M) (hS : S₁ ≤ S₂) :
    (Submodule.mapQ (p := T.map S₁.mkQ) (q := T.map S₂.mkQ)
          (Submodule.factor hS)
          (by
            intro x hx
            rcases (Submodule.mem_map).1 hx with ⟨y, hy, rfl⟩
            refine (Submodule.mem_comap).2 ?_
            refine (Submodule.mem_map).2 ?_
            refine ⟨y, hy, ?_⟩
            simp) : _)
        ∘ₗ (quotientQuotientEquivQuotientSup (S := S₁) (T := T)).symm.toLinearMap =
      (quotientQuotientEquivQuotientSup (S := S₂) (T := T)).symm.toLinearMap ∘ₗ
        (Submodule.factor (show S₁ ⊔ T ≤ S₂ ⊔ T from sup_le_sup_right hS T) : _) := by
  apply Submodule.quot_hom_ext
  intro x
  simp [Submodule.mapQ_apply]

end Submodule

/-- In a quotient module `M ⧸ S`, the submodule `I • ⊤` is the image of `I • ⊤` in `M`. -/
lemma ideal_smul_top_quotient_eq_map {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (I : Ideal A) (S : Submodule A M) :
    (I • (⊤ : Submodule A (M ⧸ S))) = (I • (⊤ : Submodule A M)).map S.mkQ := by
  ext x
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y hy
      -- Reduce `y` to a representative in `M`.
      refine Quotient.inductionOn' y ?_
      intro z
      -- `r • mkQ z = mkQ (r • z)` and `r • z ∈ I • ⊤`.
      refine (Submodule.mem_map).2 ?_
      refine ⟨r • z, ?_, ?_⟩
      · refine Submodule.smul_mem_smul hr ?_
        simp
      · simp [Submodule.mkQ_apply, Submodule.Quotient.mk''_eq_mk]
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
  · intro hx
    rcases (Submodule.mem_map).1 hx with ⟨y, hy, rfl⟩
    -- Show `mkQ y` lies in `I • ⊤` using induction on `hy : y ∈ I • ⊤`.
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro r hr z hz
      -- In the quotient, `r • mkQ z` is in `I • ⊤`.
      simpa [Submodule.mkQ_apply, Submodule.Quotient.mk''_eq_mk] using
        (Submodule.smul_mem_smul hr (by simp))
    · intro x y hx hy
      simpa using Submodule.add_mem _ hx hy

/-- Monotonicity for `𝒜^k•⊤ ⊔ ℬ^n•⊤` in the exponent `k`. -/
lemma sup_pow_submodule_mono_left {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (𝒜 ℬ : Ideal A) (n : ℕ) {m k : ℕ} (h : m ≤ k) :
    ((𝒜 ^ k • ⊤ : Submodule A M) ⊔ (ℬ ^ n • ⊤)) ≤
      ((𝒜 ^ m • ⊤ : Submodule A M) ⊔ (ℬ ^ n • ⊤)) := by
  refine sup_le ?_ le_sup_right
  have hA : (𝒜 ^ k : Ideal A) ≤ 𝒜 ^ m := Ideal.pow_le_pow_right h
  exact le_trans (Submodule.smul_mono_left (N := (⊤ : Submodule A M)) hA) le_sup_left

/-
Stage maps used to build the inverse map in the iterated adic completion comparison.
We fix the `ℬ`-exponent `n`, and for each `k` use the `(k+n)`-th stage of the `(𝒜+ℬ)`-adic system.
-/

/-- The stage map at level `k` for the `𝒜`-adic completion of `M ⧸ (ℬ^n•⊤)`, built from the
`(k+n)`-th stage of the `(𝒜+ℬ)`-adic completion of `M`. -/
noncomputable def fromSumStageMap {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] (n k : ℕ) :
    AdicCompletion (𝒜 + ℬ) M →ₗ[A]
      (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) ⧸
        (𝒜 ^ k • ⊤ : Submodule A (M ⧸ (ℬ ^ n • ⊤ : Submodule A M))) := by
  classical
  -- Abbreviate the left quotient submodule `S = ℬ^n • ⊤` and the right submodule `T = 𝒜^k • ⊤`.
  let S : Submodule A M := (ℬ ^ n • ⊤ : Submodule A M)
  let T : Submodule A M := (𝒜 ^ k • ⊤ : Submodule A M)
  have hPow :
      ((𝒜 + ℬ) ^ (k + n) • ⊤ : Submodule A M) ≤ S ⊔ T := by
    simpa [S, T, sup_comm] using (pow_sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) (M := M) k n)
  have hEq :
      (𝒜 ^ k • (⊤ : Submodule A (M ⧸ S))) = T.map S.mkQ := by
    exact ideal_smul_top_quotient_eq_map (A := A) (M := M) (I := 𝒜 ^ k) (S := S)
  have hTp :
      T.map S.mkQ ≤ (𝒜 ^ k • (⊤ : Submodule A (M ⧸ S))) := by
    exact le_of_eq hEq.symm
  exact
    (Submodule.factor hTp : _) ∘ₗ
      (Submodule.quotientQuotientEquivQuotientSup (S := S) (T := T)).symm.toLinearMap ∘ₗ
          (Submodule.factor hPow : _) ∘ₗ
            AdicCompletion.eval (𝒜 + ℬ) M (k + n)

/-- Compatibility of `fromSumStageMap` with `𝒜`-transition maps. -/
lemma fromSum_stage_lift_compatible {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] (n : ℕ) :
    ∀ {m k : ℕ} (h : m ≤ k),
      AdicCompletion.transitionMap 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) h ∘ₗ
          fromSumStageMap (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n k =
        fromSumStageMap (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n m := by
  classical
  intro m k hmk
  apply LinearMap.ext
  intro x
  have hAdd : m + n ≤ k + n := Nat.add_le_add_right hmk n
  -- Rewrite the `(m+n)`-th stage in terms of the `(k+n)`-th stage using the defining compatibility
  -- condition of `x : AdicCompletion (𝒜+ℬ) M`.
  have hx :
      AdicCompletion.transitionMap (𝒜 + ℬ) M hAdd (x.val (k + n)) = x.val (m + n) := by
    exact AdicCompletion.transitionMap_comp_eval_apply (I := 𝒜 + ℬ) (M := M) hAdd x
  dsimp [fromSumStageMap, LinearMap.comp_apply]
  -- After rewriting, both sides depend on the same element of the `(k+n)`-th stage quotient.
  rw [← hx]
  refine Quotient.inductionOn' (x.val (k + n)) ?_
  intro y
  -- Everything is defined via quotient maps; on representatives the diagram commutes by `simp`.
  simp [AdicCompletion.transitionMap, Submodule.Quotient.mk''_eq_mk,
    Submodule.quotientQuotientEquivQuotientSup_symm_mk]

noncomputable def fromSumStage {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] (n : ℕ) :
    AdicCompletion (𝒜 + ℬ) M →ₗ[A] AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) :=
  AdicCompletion.lift (I := 𝒜)
    (f := fun k => fromSumStageMap (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n k)
    (fromSum_stage_lift_compatible (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n)

/-- Naturality of `fromSumStage` in the exponent of `ℬ`. -/
lemma fromSumStage_naturality {A M : Type} [CommRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] {m n : ℕ} (h : m ≤ n) :
    ((AdicCompletion.map (I := 𝒜) (AdicCompletion.transitionMap ℬ M h)).restrictScalars A) ∘ₗ
        fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n =
      fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m := by
  classical
  apply LinearMap.ext
  intro x
  apply AdicCompletion.ext
  intro k
  -- Reduce to a statement about the stage maps `fromSumStageMap`.
  simp [fromSumStage, AdicCompletion.map_val_apply, AdicCompletion.eval_lift_apply, LinearMap.comp_apply]
  -- Now both sides only depend on the `(k+n)`-th stage of `x : AdicCompletion (𝒜+ℬ) M`.
  have hkn : k + m ≤ k + n := Nat.add_le_add_left h k
  have hxkn :
      AdicCompletion.transitionMap (𝒜 + ℬ) M hkn (x.val (k + n)) = x.val (k + m) := by
    exact AdicCompletion.transitionMap_comp_eval_apply (I := 𝒜 + ℬ) (M := M) hkn x
  -- Unfold the stage maps and rewrite the `(k+m)`-th coordinate using `hxkn`.
  dsimp [fromSumStageMap, LinearMap.comp_apply]
  rw [← hxkn]
  refine Quotient.inductionOn' (x.val (k + n)) ?_
  intro y
  simp [AdicCompletion.transitionMap, LinearMap.reduceModIdeal_apply, Submodule.Quotient.mk''_eq_mk,
    Submodule.quotientQuotientEquivQuotientSup_symm_mk]

/-
For the inverse direction we will need to identify the quotient of an `𝒜`-adic completion
by `ℬ^n` with the `𝒜`-adic completion of the quotient by `ℬ^n`.
We obtain this by rewriting both sides in terms of tensor products.
-/

/-- For finite modules over a Noetherian ring, `𝒜`-adic completion commutes with quotienting
by `ℬ^n`. This is proved by expressing both sides via tensor products. -/
noncomputable def quot_completion_equiv_completion_quot_pow {A M : Type} [CommRing A]
    [IsNoetherianRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (n : ℕ) :
    (AdicCompletion 𝒜 M ⧸ (ℬ ^ n • ⊤ : Submodule A (AdicCompletion 𝒜 M))) ≃ₗ[A]
      AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) := by
  classical
  -- Notation for the completed ring `Â = Â_𝒜`.
  let Â : Type := AdicCompletion 𝒜 A
  -- Express `AdicCompletion 𝒜 M` and `AdicCompletion 𝒜 (M ⧸ ℬ^n)` as tensor products with `Â`.
  let eM : TensorProduct A Â M ≃ₗ[A] AdicCompletion 𝒜 M :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := 𝒜) (M := M)).restrictScalars A
  let eQ : TensorProduct A Â (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) ≃ₗ[A]
      AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) :=
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := 𝒜)
        (M := M ⧸ (ℬ ^ n • ⊤ : Submodule A M))).restrictScalars A
  -- Rewrite both quotients as tensor products with `A ⧸ ℬ^n` and reassociate/commute tensor factors.
  exact
    (TensorProduct.quotTensorEquivQuotSMul (R := A) (M := AdicCompletion 𝒜 M) (I := ℬ ^ n)).symm ≪≫ₗ
      (LinearEquiv.lTensor (R := A) (M := A ⧸ (ℬ ^ n)) eM.symm) ≪≫ₗ
      (TensorProduct.assoc A (A ⧸ (ℬ ^ n)) Â M).symm ≪≫ₗ
      ((TensorProduct.comm A (A ⧸ (ℬ ^ n)) Â).rTensor M) ≪≫ₗ
      (TensorProduct.assoc A Â (A ⧸ (ℬ ^ n)) M) ≪≫ₗ
      (LinearEquiv.lTensor (R := A) (M := Â)
        (TensorProduct.quotTensorEquivQuotSMul (R := A) (M := M) (I := ℬ ^ n))) ≪≫ₗ
      eQ

set_option maxHeartbeats 800000 in
/-- Naturality of `quot_completion_equiv_completion_quot_pow` in the `ℬ`-exponent. -/
lemma quot_completion_equiv_completion_quot_pow_naturality {A M : Type} [CommRing A]
    [IsNoetherianRing A] (𝒜 ℬ : Ideal A) [AddCommGroup M]
    [Module A M] [Module.Finite A M] {m n : ℕ} (h : m ≤ n) :
    ((AdicCompletion.map (I := 𝒜) (AdicCompletion.transitionMap ℬ M h)).restrictScalars A) ∘ₗ
        (quot_completion_equiv_completion_quot_pow (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).toLinearMap =
      (quot_completion_equiv_completion_quot_pow (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m).toLinearMap ∘ₗ
        AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h := by
  classical
  -- Unfold the tensor-product description and check the square on pure tensors.
  apply LinearMap.ext
  intro z
  refine Quotient.inductionOn' z ?_
  intro y
  -- Reduce the quotient-of-tensor equivalences on generators and use tensor `simp` lemmas.
  simp [quot_completion_equiv_completion_quot_pow, AdicCompletion.transitionMap,
    TensorProduct.quotTensorEquivQuotSMul_symm_mk, Submodule.Quotient.mk''_eq_mk,
    LinearEquiv.lTensor_tmul]
  -- Now rewrite the remaining `AdicCompletion.map` using `ofTensorProduct_naturality`, then cancel
  -- `ofTensorProduct` by applying the inverse equivalence.
  set t_n :
      TensorProduct A (AdicCompletion 𝒜 A) (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) :=
    (LinearEquiv.lTensor (AdicCompletion 𝒜 A) (TensorProduct.quotTensorEquivQuotSMul M (ℬ ^ n)))
      ((TensorProduct.assoc A (AdicCompletion 𝒜 A) (A ⧸ ℬ ^ n) M)
        ((LinearEquiv.rTensor M (TensorProduct.comm A (A ⧸ ℬ ^ n) (AdicCompletion 𝒜 A)))
          ((TensorProduct.assoc A (A ⧸ ℬ ^ n) (AdicCompletion 𝒜 A) M).symm
            (1 ⊗ₜ[A] (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian 𝒜 M).symm y)))) with ht_n
  set t_m :
      TensorProduct A (AdicCompletion 𝒜 A) (M ⧸ (ℬ ^ m • ⊤ : Submodule A M)) :=
    (LinearEquiv.lTensor (AdicCompletion 𝒜 A) (TensorProduct.quotTensorEquivQuotSMul M (ℬ ^ m)))
      ((TensorProduct.assoc A (AdicCompletion 𝒜 A) (A ⧸ ℬ ^ m) M)
        ((LinearEquiv.rTensor M (TensorProduct.comm A (A ⧸ ℬ ^ m) (AdicCompletion 𝒜 A)))
          ((TensorProduct.assoc A (A ⧸ ℬ ^ m) (AdicCompletion 𝒜 A) M).symm
            (1 ⊗ₜ[A] (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian 𝒜 M).symm y)))) with ht_m
  -- Replace the left-hand side using the naturality of `ofTensorProduct`.
  have hNat :=
    LinearMap.congr_fun
      (AdicCompletion.ofTensorProduct_naturality (I := 𝒜)
          (f := (Submodule.factorPow ℬ M h))
          (M := M ⧸ (ℬ ^ n • ⊤ : Submodule A M))
          (N := M ⧸ (ℬ ^ m • ⊤ : Submodule A M)))
      t_n
  let idₗ : AdicCompletion 𝒜 A →ₗ[AdicCompletion 𝒜 A] AdicCompletion 𝒜 A := LinearMap.id
  -- Apply the inverse equivalence to reduce to a tensor identity.
  have hNat' :
      (AdicCompletion.map 𝒜 (Submodule.factorPow ℬ M h))
          ((AdicCompletion.ofTensorProduct 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M))) t_n) =
        (AdicCompletion.ofTensorProduct 𝒜 (M ⧸ (ℬ ^ m • ⊤ : Submodule A M)))
          ((TensorProduct.AlgebraTensorModule.map idₗ (Submodule.factorPow ℬ M h)) t_n) := by
    simpa [LinearMap.comp_apply] using hNat
  -- Replace the left-hand side using `hNat'`.
  rw [hNat']
  -- Cancel `ofTensorProduct` using the inverse of the finite/noetherian equivalence.
  let e :=
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := 𝒜)
      (M := M ⧸ (ℬ ^ m • ⊤ : Submodule A M))
  apply_fun e.symm using e.symm.injective
  -- Rewrite `ofTensorProduct` as `e` to simplify `e.symm (e _)`.
  rw [← AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply (I := 𝒜)
        (M := M ⧸ (ℬ ^ m • ⊤ : Submodule A M))
        ((TensorProduct.AlgebraTensorModule.map idₗ (Submodule.factorPow ℬ M h)) t_n)]
  rw [← AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_apply (I := 𝒜)
        (M := M ⧸ (ℬ ^ m • ⊤ : Submodule A M)) t_m]
  -- It remains to check the tensor identity, which is a direct computation on pure tensors.
  -- First cancel `e.symm (e _)` without unfolding `e`.
  rw [e.symm_apply_apply ((TensorProduct.AlgebraTensorModule.map idₗ (Submodule.factorPow ℬ M h)) t_n)]
  rw [e.symm_apply_apply t_m]
  -- Expand `t_n` and `t_m` and reduce to a calculation in the tensor product `Â ⊗ M`.
  rw [ht_n, ht_m]
  set w := (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (I := 𝒜) (M := M)).symm y with hw
  -- The map in question is linear in `w`, so we may prove it by induction on `w`.
  -- (On pure tensors it is a straightforward simp computation.)
  refine TensorProduct.induction_on w ?_ (fun a x => ?_) (fun u v hu hv => ?_)
  · -- All maps involved are linear, so everything sends `0` to `0`.
    simp [TensorProduct.tmul_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  · -- Pure tensor case.
    -- After pushing through the tensor-equivalences, this reduces to the compatibility of the
    -- canonical maps `M ⧸ ℬ^n → M ⧸ ℬ^m` with `quotTensorEquivQuotSMul`.
    simp [idₗ, Submodule.factorPow, TensorProduct.AlgebraTensorModule.map_tmul,
      LinearEquiv.lTensor_tmul, LinearEquiv.rTensor_tmul,
      TensorProduct.assoc_tmul, TensorProduct.comm_tmul]
    have hq_n :
        TensorProduct.quotTensorEquivQuotSMul M (ℬ ^ n) (1 ⊗ₜ[A] x) = Submodule.Quotient.mk x := by
      simpa using
        (TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) (I := ℬ ^ n) (r := (1 : A)) (x := x))
    have hq_m :
        TensorProduct.quotTensorEquivQuotSMul M (ℬ ^ m) (1 ⊗ₜ[A] x) = Submodule.Quotient.mk x := by
      simpa using
        (TensorProduct.quotTensorEquivQuotSMul_mk_tmul (M := M) (I := ℬ ^ m) (r := (1 : A)) (x := x))
    simp [hq_n, hq_m]
  · -- Additive case.
    simp [TensorProduct.tmul_add, hu, hv, LinearEquiv.map_add, LinearMap.map_add]

/- Let $A$ be a Noetherian ring and let $\mathfrak{a}, \mathfrak{b}$ be ideals in $A$. If $M$ is
any $A$-module, let $M_{\mathfrak{a}}$, $M_{\mathfrak{b}}$ denote its $\mathfrak{a}$-adic and
$\mathfrak{b}$-adic completions respectively. If $M$ is finitely generated, prove that
$(M_{\mathfrak{a}})_{\mathfrak{b}} \cong M_{\mathfrak{a} + \mathfrak{b}}$. -/
set_option maxHeartbeats 800000 in
theorem nonempty_adicCompletion_adicCompletion_linearEquiv_aux {A M : Type} [CommRing A]
    [IsNoetherianRing A] (𝒜 : Ideal A) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (ℬ : Ideal A) :
    Nonempty (AdicCompletion ℬ (AdicCompletion 𝒜 M) ≃ₗ[A] AdicCompletion (𝒜 + ℬ) M) := by
  classical
  -- The remaining step is to show that the explicit forward and inverse maps built via
  -- `AdicCompletion.lift` are mutually inverse.
  --
  -- We now have the core compatibility/naturality ingredients available, in particular:
  -- `fromSumStage_naturality` and `quot_completion_equiv_completion_quot_pow_naturality`.

  -- Forward map `(M_𝒜)_ℬ → M_{𝒜+ℬ}`.
  let toSum :
      AdicCompletion ℬ (AdicCompletion 𝒜 M) →ₗ[A] AdicCompletion (𝒜 + ℬ) M :=
    AdicCompletion.lift (I := 𝒜 + ℬ)
      (f := fun n =>
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n) ∘ₗ
          quotPow_to_sup (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n n ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n)
      (by
        intro m n h
        simpa using (toSum_lift_compatible (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h))

  -- Stage maps for the inverse `M_{𝒜+ℬ} → (M_𝒜)_ℬ`, landing in the `n`-th quotient stage.
  let fromSumStage' (n : ℕ) :
      AdicCompletion (𝒜 + ℬ) M →ₗ[A]
        (AdicCompletion 𝒜 M ⧸ (ℬ ^ n • ⊤ : Submodule A (AdicCompletion 𝒜 M))) :=
    (quot_completion_equiv_completion_quot_pow (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).symm.toLinearMap ∘ₗ
      fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n

  have fromSumStage'_compatible :
      ∀ {m n : ℕ} (h : m ≤ n),
        AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ fromSumStage' n =
          fromSumStage' m := by
    intro m n h
    -- Abbreviate the key naturality morphism on the right-hand side.
    let mapₘₙ :
        AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) →ₗ[A]
          AdicCompletion 𝒜 (M ⧸ (ℬ ^ m • ⊤ : Submodule A M)) :=
      (AdicCompletion.map (I := 𝒜) (AdicCompletion.transitionMap ℬ M h)).restrictScalars A
    let e_n :=
      quot_completion_equiv_completion_quot_pow (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n
    let e_m :=
      quot_completion_equiv_completion_quot_pow (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m
    have hnat_e :
        mapₘₙ ∘ₗ e_n.toLinearMap =
          e_m.toLinearMap ∘ₗ AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h := by
      simpa [mapₘₙ, e_n, e_m] using
        (quot_completion_equiv_completion_quot_pow_naturality (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h)
    have hnat_e' :
        AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ e_n.symm.toLinearMap =
          e_m.symm.toLinearMap ∘ₗ mapₘₙ := by
      -- Rearrange `hnat_e` by applying `e_m` and using its injectivity.
      apply LinearMap.ext
      intro x
      apply e_m.injective
      -- Use `hnat_e` with `e_n.symm x`.
      have hx :=
        LinearMap.congr_fun hnat_e (e_n.symm x)
      -- Simplify `e_n (e_n.symm x)` and `e_m (e_m.symm _)`.
      simpa [LinearMap.comp_apply] using hx.symm
    -- Conclude the desired compatibility using naturality of `fromSumStage`.
    calc
      AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ fromSumStage' n =
          (AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ e_n.symm.toLinearMap) ∘ₗ
            fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n := by
        simp [fromSumStage', e_n, LinearMap.comp_assoc]
      _ =
          (e_m.symm.toLinearMap ∘ₗ mapₘₙ) ∘ₗ
            fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n := by
        simp [hnat_e', LinearMap.comp_assoc]
      _ =
          e_m.symm.toLinearMap ∘ₗ
            (mapₘₙ ∘ₗ fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n) := by
        simp [LinearMap.comp_assoc]
      _ =
          e_m.symm.toLinearMap ∘ₗ
            fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m := by
        simp [mapₘₙ, fromSumStage_naturality (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h]
      _ = fromSumStage' m := by
        simp [fromSumStage', e_m]

  let fromSum :
      AdicCompletion (𝒜 + ℬ) M →ₗ[A] AdicCompletion ℬ (AdicCompletion 𝒜 M) :=
    AdicCompletion.lift (I := ℬ)
      (f := fromSumStage')
      (by
        intro m n h
        simpa using fromSumStage'_compatible (m := m) (n := n) h
      )

  refine ⟨LinearEquiv.ofLinear toSum fromSum ?_ ?_⟩
  · -- `toSum` is a left inverse of `fromSum`.
    apply LinearMap.ext
    intro x
    rcases AdicCompletion.mk_surjective (I := 𝒜 + ℬ) (M := M) x with ⟨a, rfl⟩
    apply AdicCompletion.ext
    intro n
    change (toSum (fromSum ((AdicCompletion.mk (𝒜 + ℬ) M) a))).val n = Submodule.Quotient.mk (a n)
    simp [toSum, fromSum, fromSumStage', AdicCompletion.eval_lift_apply, LinearMap.comp_apply]
  · -- `fromSum` is a left inverse of `toSum`.
    apply LinearMap.ext
    intro x
    rcases AdicCompletion.mk_surjective (I := ℬ) (M := AdicCompletion 𝒜 M) x with ⟨a, rfl⟩
    apply AdicCompletion.ext
    intro n
    change (fromSum (toSum ((AdicCompletion.mk ℬ (AdicCompletion 𝒜 M)) a))).val n =
      Submodule.Quotient.mk (a n)
    simp [toSum, fromSum, fromSumStage', AdicCompletion.eval_lift_apply, LinearMap.comp_apply]

theorem nonempty_adicCompletion_adicCompletion_linearEquiv {A M : Type} [CommRing A]
    [IsNoetherianRing A] (𝒜 : Ideal A) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (ℬ : Ideal A) :
    Nonempty (AdicCompletion ℬ (AdicCompletion 𝒜 M) ≃ₗ[A] AdicCompletion (𝒜 + ℬ) M) := by
  simpa using nonempty_adicCompletion_adicCompletion_linearEquiv_aux (A := A) (M := M) 𝒜 ℬ

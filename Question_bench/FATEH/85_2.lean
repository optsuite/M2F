import Mathlib
import Question_bench.FATEH.«85_1»

open Submodule
open Finset
open Submodule
/-!
More fine-grained refactor: split into smaller defs/lemmas (target: each ≤ 40 lines).
This is a structural refactor of your original proof.
-/

section AdicCompletionIter

section
variable {A M : Type} [CommRing A] [IsNoetherianRing A]
variable (𝒜 ℬ : Ideal A)
variable [AddCommGroup M] [Module A M] [Module.Finite A M]

/-! ### Forward map `(M_𝒜)_ℬ → M_{𝒜+ℬ}` -/

/-- The stage map used to build `toSum` via `AdicCompletion.lift`. -/
noncomputable def toSumStage (n : ℕ) :
    AdicCompletion ℬ (AdicCompletion 𝒜 M) →ₗ[A]
      (M ⧸ ((𝒜 + ℬ) ^ n • ⊤ : Submodule A M)) :=
  Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n) ∘ₗ
    quotPow_to_sup (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n n ∘ₗ
      AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- Compatibility of `toSumStage` for the lift. -/
lemma toSumStage_compatible {m n : ℕ} (h : m ≤ n) :
    AdicCompletion.transitionMap (𝒜 + ℬ) M h ∘ₗ toSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n =
      toSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m := by
  classical
  simpa [toSumStage] using (toSum_lift_compatible (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h)

/-- Forward map `(M_𝒜)_ℬ → M_{𝒜+ℬ}`. -/
noncomputable def toSum :
    AdicCompletion ℬ (AdicCompletion 𝒜 M) →ₗ[A] AdicCompletion (𝒜 + ℬ) M := by
  classical
  refine
    AdicCompletion.lift (I := 𝒜 + ℬ)
      (f := fun n =>
        Submodule.factor (sup_pow_submodule_le (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n) ∘ₗ
          quotPow_to_sup (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n n ∘ₗ
            AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n)
      ?_
  intro m n h
  simpa using toSumStage_compatible (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h

/-! ### Inverse map `M_{𝒜+ℬ} → (M_𝒜)_ℬ` -/

/-- The induced map on `𝒜`-adic completions coming from the `ℬ` transition map on quotients. -/
noncomputable def mapₘₙ (m n : ℕ) (h : m ≤ n) :
    AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) →ₗ[A]
      AdicCompletion 𝒜 (M ⧸ (ℬ ^ m • ⊤ : Submodule A M)) :=
  (AdicCompletion.map (I := 𝒜) (AdicCompletion.transitionMap ℬ M h)).restrictScalars A

/-- Abbreviation for the quotient/completion equivalence at stage `n`. -/
noncomputable def e (n : ℕ) :
    (AdicCompletion 𝒜 M ⧸ (ℬ ^ n • ⊤ : Submodule A (AdicCompletion 𝒜 M))) ≃ₗ[A]
      AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) :=
  quot_completion_equiv_completion_quot_pow (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n

/-- Naturality in the “forward” direction: `mapₘₙ ∘ e_n = e_m ∘ transition`. -/
lemma e_naturality {m n : ℕ} (h : m ≤ n) :
    mapₘₙ (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m n h ∘ₗ (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).toLinearMap =
      (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m).toLinearMap ∘ₗ
        AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h := by
  classical
  simpa [mapₘₙ, e] using
    (quot_completion_equiv_completion_quot_pow_naturality (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h)

/-- A small helper: turn `e_naturality` into an equality after applying to `e_n.symm x`. -/
lemma e_symm_naturality_apply {m n : ℕ} (h : m ≤ n) (x) :
    (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m)
        (AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h
            ((e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).symm x))
      =
      mapₘₙ (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m n h x := by
  classical
  have hn := e_naturality (𝒜 := 𝒜) (ℬ := ℬ) (M := M) (m := m) (n := n) h
  -- apply congr_fun to `e_n.symm x`
  have hx := LinearMap.congr_fun hn ( (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).symm x )
  simpa [LinearMap.comp_apply] using hx.symm

lemma e_symm_naturality {m n : ℕ} (h : m ≤ n) :
    AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ
        (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).symm.toLinearMap =
      (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m).symm.toLinearMap ∘ₗ
        mapₘₙ (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m n h := by
  apply LinearMap.ext
  intro x
  apply_fun e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m
  -- show equality by applying `e_m` and using injectivity
  · simp only [LinearMap.coe_comp]
    rw [Function.comp_apply, Function.comp_apply]
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    -- simp only [LinearEquiv.apply_symm_apply]
    have := e_symm_naturality_apply (𝒜 := 𝒜) (ℬ := ℬ) (M := M) (m := m) (n := n) h x
    exact this
  · apply (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m).injective


/-- The raw stage map `M_{𝒜+ℬ} → AdicCompletion 𝒜 (M/ℬ^n)` before transporting via `e`. -/
noncomputable def fromSumStageRaw (n : ℕ) :
    AdicCompletion (𝒜 + ℬ) M →ₗ[A] AdicCompletion 𝒜 (M ⧸ (ℬ ^ n • ⊤ : Submodule A M)) :=
  fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n

/-- Stage maps for the inverse, landing in the `n`-th quotient stage of `(M_𝒜)_ℬ`. -/
noncomputable def fromSumStage' (n : ℕ) :
    AdicCompletion (𝒜 + ℬ) M →ₗ[A]
      (AdicCompletion 𝒜 M ⧸ (ℬ ^ n • ⊤ : Submodule A (AdicCompletion 𝒜 M))) :=
  (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n).symm.toLinearMap ∘ₗ
    fromSumStage (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n

omit [IsNoetherianRing A] [Module.Finite A M] in
/-- Naturality of `fromSumStageRaw`. -/
lemma fromSumStageRaw_naturality {m n : ℕ} (h : m ≤ n) :
    mapₘₙ (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m n h ∘ₗ
        fromSumStageRaw (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n =
      fromSumStageRaw (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m := by
  classical
  simpa [mapₘₙ, fromSumStageRaw] using
    fromSumStage_naturality (𝒜 := 𝒜) (ℬ := ℬ) (M := M) h

/-- Compatibility of `fromSumStage'` with transition maps. -/
lemma fromSumStage'_compatible {m n : ℕ} (h : m ≤ n) :
    AdicCompletion.transitionMap ℬ (AdicCompletion 𝒜 M) h ∘ₗ
        fromSumStage' (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n =
      fromSumStage' (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m := by
  classical
  apply LinearMap.ext
  intro x
  apply (e (𝒜 := 𝒜) (ℬ := ℬ) (M := M) m).injective
  simp [fromSumStage', LinearMap.comp_apply]
  have h1 :=
    e_symm_naturality_apply (𝒜 := 𝒜) (ℬ := ℬ) (M := M) (m := m) (n := n) h
      (fromSumStageRaw (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n x)
  have h2 :=
    LinearMap.congr_fun
      (fromSumStageRaw_naturality (𝒜 := 𝒜) (ℬ := ℬ) (M := M) (m := m) (n := n) h) x
  exact h1.trans h2

/-- Inverse map `M_{𝒜+ℬ} → (M_𝒜)_ℬ`. -/
noncomputable def fromSum :
    AdicCompletion (𝒜 + ℬ) M →ₗ[A] AdicCompletion ℬ (AdicCompletion 𝒜 M) := by
  classical
  refine
    AdicCompletion.lift (I := ℬ)
      (f := fun n => fromSumStage' (𝒜 := 𝒜) (ℬ := ℬ) (M := M) n)
      ?_
  intro m n h
  simpa using fromSumStage'_compatible (𝒜 := 𝒜) (ℬ := ℬ) (M := M) (m := m) (n := n) h

/-! ### Inverse laws split further -/

/-! ### Pointwise evaluation for inverse laws -/

/-- Pointwise evaluation of `toSum (fromSum (mk a))`. -/
lemma toSum_fromSum_mk_eval (a) (n : ℕ) :
    AdicCompletion.eval (𝒜 + ℬ) M n
        (toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
          (fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
            ((AdicCompletion.mk (𝒜 + ℬ) M) a)))
      = Submodule.Quotient.mk (a n) := by
  simp [AdicCompletion.eval_apply, toSum, fromSum, fromSumStage', LinearMap.comp_apply]
  sorry


/-- Pointwise evaluation of `fromSum (toSum (mk a))`. -/
lemma fromSum_toSum_mk_eval (a) (n : ℕ) :
    AdicCompletion.eval ℬ (AdicCompletion 𝒜 M) n
        (fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
          (toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
            ((AdicCompletion.mk ℬ (AdicCompletion 𝒜 M)) a)))
      = Submodule.Quotient.mk (a n) := by
  simp [AdicCompletion.eval_apply, toSum, fromSum, fromSumStage', LinearMap.comp_apply]
  sorry

/-- `toSum (fromSum (mk a)) = mk a`, pointwise on the projective limit. -/
lemma toSum_fromSum_mk (a) :
    toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
        (fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M) ((AdicCompletion.mk (𝒜 + ℬ) M) a))
      =
      (AdicCompletion.mk (𝒜 + ℬ) M) a := by
  classical
  apply AdicCompletion.ext
  intro n
  simpa using toSum_fromSum_mk_eval (𝒜 := 𝒜) (ℬ := ℬ) (M := M) a n
/-- `toSum` is a left inverse of `fromSum`. -/
lemma toSum_fromSum :
    ∀ x, toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
          (fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M) x) = x := by
  classical
  intro x
  rcases AdicCompletion.mk_surjective (I := 𝒜 + ℬ) (M := M) x with ⟨a, rfl⟩
  simpa using toSum_fromSum_mk (𝒜 := 𝒜) (ℬ := ℬ) (M := M) a

/-- `fromSum (toSum (mk a)) = mk a`, pointwise on the projective limit. -/
lemma fromSum_toSum_mk (a) :
    fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
        (toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M) ((AdicCompletion.mk ℬ (AdicCompletion 𝒜 M)) a))
      =
      (AdicCompletion.mk ℬ (AdicCompletion 𝒜 M)) a := by
  classical
  apply AdicCompletion.ext
  intro n
  simpa using fromSum_toSum_mk_eval (𝒜 := 𝒜) (ℬ := ℬ) (M := M) a n

--
/-- `fromSum` is a left inverse of `toSum`. -/
lemma fromSum_toSum :
    ∀ x, fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M)
          (toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M) x) = x := by
  classical
  intro x
  rcases AdicCompletion.mk_surjective (I := ℬ) (M := AdicCompletion 𝒜 M) x with ⟨a, rfl⟩
  simpa using fromSum_toSum_mk (𝒜 := 𝒜) (ℬ := ℬ) (M := M) a

/-! ### Final packaged equivalence -/

set_option maxHeartbeats 800000 in
theorem nonempty_adicCompletion_adicCompletion_linearEquiv_aux :
    Nonempty (AdicCompletion ℬ (AdicCompletion 𝒜 M) ≃ₗ[A] AdicCompletion (𝒜 + ℬ) M) := by
  classical
  refine ⟨LinearEquiv.ofLinear
    (toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M))
    (fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M))
    ?_ ?_⟩
  · apply LinearMap.ext
    intro x
    exact toSum_fromSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M) x
  · apply LinearMap.ext
    intro x
    exact fromSum_toSum (𝒜 := 𝒜) (ℬ := ℬ) (M := M) x

end
end AdicCompletionIter

theorem nonempty_adicCompletion_adicCompletion_linearEquiv {A M : Type} [CommRing A]
    [IsNoetherianRing A] (𝒜 : Ideal A) [AddCommGroup M]
    [Module A M] [Module.Finite A M] (ℬ : Ideal A) :
    Nonempty (AdicCompletion ℬ (AdicCompletion 𝒜 M) ≃ₗ[A] AdicCompletion (𝒜 + ℬ) M) := by
  simpa using nonempty_adicCompletion_adicCompletion_linearEquiv_aux (A := A) (M := M) 𝒜 ℬ

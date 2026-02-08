import Mathlib

/-
Let $F$ be a field with $\mathbb{Q} \subseteq F \subseteq \mathbb{C}$, where $F/\mathbb{Q}$
is a finite \emph{abelian} Galois extension. Prove that $F$ contains only finitely many algebraic integers
(i.e. elements in $F$ whose minimal polynomial over $\mathbb{Q}$ have coefficients in $\mathbb{Z}$) having absolute value $1$,
and each of the algebraic integers is a root of unity.
-/
/-- If all embeddings are uniformly bounded, the corresponding set of algebraic integers is finite. -/
lemma finite_algebraic_integers_of_norm_le
    (F : IntermediateField ℚ ℂ) (h_fin : Module.Finite ℚ F) (B : ℝ) :
    {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ B}.Finite := by
  classical
  letI : Module.Finite ℚ F := h_fin
  haveI : FiniteDimensional ℚ F := by infer_instance
  haveI : NumberField F := NumberField.of_module_finite (K := ℚ) (L := F)
  simpa using (NumberField.Embeddings.finite_of_norm_le (K := F) (A := ℂ) B)

/-- Reduce a uniform bound on all embeddings to a bound on the canonical embedding. -/
lemma embeddings_norm_le_iff_canonical
    (F : IntermediateField ℚ ℂ) [NumberField F] (x : F) (r : ℝ) :
    (∀ φ : F →+* ℂ, ‖φ x‖ ≤ r) ↔ ‖NumberField.canonicalEmbedding F x‖ ≤ r := by
  simpa using (NumberField.canonicalEmbedding.norm_le_iff (K := F) (x := x) (r := r)).symm

/-- Each embedding is bounded by the canonical embedding norm. -/
lemma embedding_norm_le_canonical
    (F : IntermediateField ℚ ℂ) [NumberField F] (x : F) (φ : F →+* ℂ) :
    ‖φ x‖ ≤ ‖NumberField.canonicalEmbedding F x‖ := by
  have hbound :
      (∀ ψ : F →+* ℂ, ‖ψ x‖ ≤ ‖NumberField.canonicalEmbedding F x‖) := by
    exact (embeddings_norm_le_iff_canonical F x ‖NumberField.canonicalEmbedding F x‖).2 le_rfl
  exact hbound φ

/-- The canonical embedding norm dominates the complex norm of an element. -/
lemma canonicalEmbedding_norm_ge_coe
    (F : IntermediateField ℚ ℂ) [NumberField F] (x : F) :
    ‖(x : ℂ)‖ ≤ ‖NumberField.canonicalEmbedding F x‖ := by
  simpa using (embedding_norm_le_canonical F x (algebraMap F ℂ))

/-- If the complex norm is one, the canonical embedding has norm at least one. -/
lemma canonicalEmbedding_norm_ge_one_of_norm_eq_one
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : ‖(x : ℂ)‖ = 1) :
    (1 : ℝ) ≤ ‖NumberField.canonicalEmbedding F x‖ := by
  have hge : ‖(x : ℂ)‖ ≤ ‖NumberField.canonicalEmbedding F x‖ :=
    canonicalEmbedding_norm_ge_coe F x
  simpa [hx] using hge

/-- The distinguished embedding satisfies the unit-norm bound. -/
lemma embedding_norm_le_one_of_eq_algebraMap
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : ‖(x : ℂ)‖ = 1) {φ : F →+* ℂ} (hφ : φ = algebraMap F ℂ) :
    ‖φ x‖ ≤ (1 : ℝ) := by
  simp [hφ, hx]

/-- A root of unity maps to unit norm under any embedding. -/
lemma embedding_norm_eq_one_of_pow_eq_one
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F} {n : ℕ}
    (hn : 0 < n) (hpow : x ^ n = 1) (φ : F →+* ℂ) :
    ‖φ x‖ = 1 := by
  have hpow' : (φ x : ℂ) ^ n = 1 := by
    have h := congrArg φ hpow
    simpa [map_pow] using h
  exact Complex.norm_eq_one_of_pow_eq_one hpow' (Nat.ne_of_gt hn)

/-- An embedding of `x` lands in the root set of its minimal polynomial. -/
lemma embedding_mem_rootSet_minpoly
    (F : IntermediateField ℚ ℂ) [NumberField F] (x : F) (ψ : F →+* ℂ) :
    ψ x ∈ (minpoly ℚ x).rootSet ℂ := by
  have hroot :=
    (NumberField.Embeddings.range_eval_eq_rootSet_minpoly (K := F) (A := ℂ) x)
  have hmem : ψ x ∈ Set.range (fun φ : F →+* ℂ => φ x) := ⟨ψ, rfl⟩
  simpa [hroot] using hmem

/-- A nontrivial root of the minimal polynomial needs a unit-norm conclusion (missing input). -/
lemma embedding_norm_eq_one_of_norm_eq_one_ne_algebraMap
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) {ψ : F →+* ℂ}
    (hψ : ψ ≠ algebraMap F ℂ) :
    ‖ψ x‖ = 1 := by
  -- If this embedding agrees on `x`, the conclusion is immediate.
  by_cases hzx : (ψ x : ℂ) = (x : ℂ)
  · simpa [hzx] using hx.2
  -- TODO: missing Kronecker-type input to upgrade one unit-norm conjugate to all conjugates.
  -- The hypothesis `hx.2` only controls the distinguished embedding.
  -- The remaining case is a nontrivial embedding value `ψ x ≠ x`.
  sorry

/-- A nontrivial root of the minimal polynomial needs a unit-norm conclusion (missing input). -/
lemma rootSet_norm_eq_one_of_norm_eq_one_ne
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) {z : ℂ}
    (hz : z ∈ (minpoly ℚ x).rootSet ℂ) (hz_ne : z ≠ (x : ℂ)) :
    ‖z‖ = 1 := by
  classical
  -- Express `z` as an embedding value via the root set characterization.
  have hz' : z ∈ Set.range (fun ψ : F →+* ℂ => ψ x) := by
    have hroot :=
      (NumberField.Embeddings.range_eval_eq_rootSet_minpoly (K := F) (A := ℂ) x)
    simpa [hroot.symm] using hz
  obtain ⟨ψ, rfl⟩ := hz'
  have hψ : ψ ≠ algebraMap F ℂ := by
    intro hψ
    apply hz_ne
    simp [hψ]
  exact embedding_norm_eq_one_of_norm_eq_one_ne_algebraMap F hx hψ

/-- A nontrivial embedding still needs a unit-norm conclusion (missing input). -/
lemma embeddings_norm_eq_one_of_norm_eq_one_ne_algebraMap
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) {ψ : F →+* ℂ}
    (hψ : ψ ≠ algebraMap F ℂ) :
    ‖ψ x‖ = 1 := by
  have hroot : ψ x ∈ (minpoly ℚ x).rootSet ℂ :=
    embedding_mem_rootSet_minpoly F x ψ
  have hroot_norm : ∀ z ∈ (minpoly ℚ x).rootSet ℂ, ‖z‖ = 1 := by
    intro z hz
    by_cases hz_eq : z = (x : ℂ)
    · simpa [hz_eq] using hx.2
    exact rootSet_norm_eq_one_of_norm_eq_one_ne F hx hz hz_eq
  -- Use `hψ` to avoid the trivial embedding case in downstream proofs.
  by_cases hψ' : ψ = algebraMap F ℂ
  · exact (hψ hψ').elim
  exact hroot_norm _ hroot

/-- Upgrade a single complex unit-norm condition to all embeddings (missing input). -/
lemma embeddings_norm_eq_one_of_norm_eq_one
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) :
    ∀ ψ : F →+* ℂ, ‖ψ x‖ = 1 := by
  intro ψ
  by_cases hψ : ψ = algebraMap F ℂ
  · simpa [hψ] using hx.2
  exact embeddings_norm_eq_one_of_norm_eq_one_ne_algebraMap F hx hψ

/-- A nontrivial embedding still needs a unit-norm bound from a single complex norm condition. -/
lemma embedding_norm_le_one_of_ne_algebraMap
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) {φ : F →+* ℂ}
    (hφ : φ ≠ algebraMap F ℂ) :
    ‖φ x‖ ≤ (1 : ℝ) := by
  have hnorm : ‖φ x‖ = 1 :=
    embeddings_norm_eq_one_of_norm_eq_one_ne_algebraMap F hx hφ
  exact hnorm.le

/-- Pending step: bound the canonical embedding from a single complex norm condition. -/
lemma canonicalEmbedding_norm_le_one_of_norm_eq_one
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) :
    ‖NumberField.canonicalEmbedding F x‖ ≤ (1 : ℝ) := by
  -- Reduce to bounding all embeddings using the canonical-embedding equivalence.
  refine (embeddings_norm_le_iff_canonical F x (1 : ℝ)).1 ?_
  intro φ
  by_cases hφ : φ = (algebraMap F ℂ)
  · exact embedding_norm_le_one_of_eq_algebraMap F hx.2 hφ
  exact embedding_norm_le_one_of_ne_algebraMap F hx hφ

/-- Missing uniform bound needed to control all embeddings from one complex norm condition. -/
lemma embeddings_norm_le_one_of_norm_eq_one
    (F : IntermediateField ℚ ℂ) [NumberField F] {x : F}
    (hx : IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1) :
    ∀ φ : F →+* ℂ, ‖φ x‖ ≤ (1 : ℝ) := by
  intro φ
  have hcanon : ‖NumberField.canonicalEmbedding F x‖ ≤ (1 : ℝ) := by
    exact canonicalEmbedding_norm_le_one_of_norm_eq_one F hx
  exact (embedding_norm_le_canonical F x φ).trans hcanon

/-- The set of algebraic integers in a finite extension with complex norm `1` is finite. -/
lemma finite_algebraic_integers_of_finite_module_finite_S
    (F : IntermediateField ℚ ℂ) (h_fin : Module.Finite ℚ F) :
    {x : F | IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1}.Finite := by
  classical
  letI : Module.Finite ℚ F := h_fin
  haveI : FiniteDimensional ℚ F := by infer_instance
  haveI : NumberField F := NumberField.of_module_finite (K := ℚ) (L := F)
  -- Reduce to finiteness under a uniform bound on all embeddings.
  have hfinite' :
      {x : F | IsIntegral ℤ x ∧ ∀ φ : F →+* ℂ, ‖φ x‖ ≤ (1 : ℝ)}.Finite := by
    simpa using finite_algebraic_integers_of_norm_le F h_fin (1 : ℝ)
  refine hfinite'.subset ?_
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro φ
  have hxcanon :
      ‖NumberField.canonicalEmbedding F x‖ ≤ (1 : ℝ) := by
    exact canonicalEmbedding_norm_le_one_of_norm_eq_one F hx
  have hbound :
      (∀ ψ : F →+* ℂ, ‖ψ x‖ ≤ (1 : ℝ)) := by
    exact (embeddings_norm_le_iff_canonical F x (1 : ℝ)).2 hxcanon
  exact hbound φ

theorem finite_algebraic_integers_of_finite_module
    (F : IntermediateField ℚ ℂ) (h_fin : Module.Finite ℚ F) [IsGalois ℚ F]
    (h : IsMulCommutative (F ≃ₐ[ℚ] F)) : {x : F | IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1}.Finite ∧
    (∀ x : F, IsIntegral ℤ x → ‖(x : ℂ)‖ = 1 → ∃ n,  x ^ n = 1) := by
  classical
  have _ := h
  let S : Set F := {x : F | IsIntegral ℤ x ∧ ‖(x : ℂ)‖ = 1}
  have hfinite : S.Finite := by
    simpa [S] using finite_algebraic_integers_of_finite_module_finite_S F h_fin
  refine ⟨hfinite, ?_⟩
  intro x hxi hxnorm
  have hmap : Set.MapsTo (fun n : ℕ => x ^ n) Set.univ S := by
    intro n hn
    change IsIntegral ℤ (x ^ n) ∧ ‖((x ^ n : F) : ℂ)‖ = 1
    refine ⟨hxi.pow n, ?_⟩
    calc
      ‖((x ^ n : F) : ℂ)‖ = ‖(x : ℂ) ^ n‖ := by simp
      _ = ‖(x : ℂ)‖ ^ n := norm_pow _ _
      _ = 1 := by simp [hxnorm]
  obtain ⟨a, -, b, -, hne, hpow⟩ :=
    Set.Infinite.exists_ne_map_eq_of_mapsTo (s := Set.univ) (t := S)
      (f := fun n : ℕ => x ^ n) Set.infinite_univ hmap hfinite
  have hxne : x ≠ 0 := by
    intro hx0
    have hxnorm0 : (‖(x : ℂ)‖) = 0 := by
      simp [hx0]
    have hxnorm1 : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ‖(x : ℂ)‖ := by simp [hxnorm]
        _ = 0 := hxnorm0
    exact one_ne_zero hxnorm1
  have hpow_of_lt : ∀ {a b : ℕ}, b < a → x ^ a = x ^ b → x ^ (a - b) = (1 : F) := by
    intro a b hlt hpow
    have hmul : x ^ (a - b) * x ^ b = x ^ b := by
      have h' := hpow
      rw [← Nat.sub_add_cancel hlt.le, pow_add] at h'
      exact h'
    have hxne' : x ^ b ≠ (0 : F) := by
      exact pow_ne_zero b hxne
    have hmul' := (mul_left_eq_self₀).1 hmul
    cases hmul' with
    | inl h1 => exact h1
    | inr hb0 => exact (hxne' hb0).elim
  by_cases hlt : b < a
  · exact ⟨a - b, hpow_of_lt hlt hpow⟩
  · have hlt' : a < b := lt_of_le_of_ne (le_of_not_gt hlt) hne
    exact ⟨b - a, hpow_of_lt hlt' hpow.symm⟩

import Mathlib

open Polynomial
open scoped ComplexConjugate

/-- A root of a minimal polynomial over `ℚ` comes from an embedding into `ℂ`. -/
lemma aux_exists_algHom_from_root (F : Type*) [Field F] [Algebra ℚ F] [Algebra.IsAlgebraic ℚ F]
    (α : F) (β : ℂ) (hβ : β ∈ (minpoly ℚ α).rootSet ℂ) :
    ∃ ψ : F →ₐ[ℚ] ℂ, ψ α = β := by
  classical
  have h :
      (Set.range fun ψ : F →ₐ[ℚ] ℂ ↦ ψ α) = (minpoly ℚ α).rootSet ℂ :=
    Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly (A := ℂ) (F := ℚ) (K := F) α
  have hβ' : β ∈ Set.range (fun ψ : F →ₐ[ℚ] ℂ ↦ ψ α) := by
    simpa [h.symm] using hβ
  rcases hβ' with ⟨ψ, rfl⟩
  exact ⟨ψ, rfl⟩

/-- The automorphism from `restrictNormal'` matches the original embedding after `algebraMap`. -/
lemma aux_restrictNormal_apply (F : IntermediateField ℚ ℂ) [Normal ℚ F]
    (ψ : F →ₐ[ℚ] ℂ) (x : F) :
    algebraMap F ℂ ((AlgHom.restrictNormal' (ϕ := ψ) (E := F)) x) = ψ x := by
  simp [AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]

/-- Conjugation on `ℂ` restricts to a normal intermediate field. -/
lemma aux_conj_restrict (F : IntermediateField ℚ ℂ) [Normal ℚ F] (x : F) :
    algebraMap F ℂ ((AlgEquiv.restrictScalars ℚ Complex.conjAe).restrictNormal F x) =
      conj (algebraMap F ℂ x) := by
  simp

/-- In a normal intermediate field, conjugation acts by inversion on norm-one elements. -/
lemma aux_conj_inv_of_norm_one (F : IntermediateField ℚ ℂ) [Normal ℚ F]
    (α : F) (ha : ‖α‖ = 1) :
    (AlgEquiv.restrictScalars ℚ Complex.conjAe).restrictNormal F α = α⁻¹ := by
  apply (FaithfulSMul.algebraMap_injective (R := F) (A := ℂ))
  have hconj : conj (algebraMap F ℂ α) = (algebraMap F ℂ α)⁻¹ := by
    have hnorm : ‖(algebraMap F ℂ α)‖ = 1 := by
      simpa using ha
    simpa using (Complex.inv_eq_conj (z := (algebraMap F ℂ α)) hnorm).symm
  calc
    algebraMap F ℂ ((AlgEquiv.restrictScalars ℚ Complex.conjAe).restrictNormal F α)
        = conj (algebraMap F ℂ α) := aux_conj_restrict (F := F) (x := α)
    _ = (algebraMap F ℂ α)⁻¹ := hconj
    _ = algebraMap F ℂ (α⁻¹) := by
        simp

/-- Let $F$ be a field with $\mathbb{Q} \subseteq F \subseteq \mathbb{C}$,
where $F/\mathbb{Q}$ is a finite \emph
{abelian} Galois extension. Let $\alpha \in F$ and let $f(x) \in \mathbb{Q}[x]$ be its minimal monic
polynomial. Assume that $|\alpha | =1$. Prove that $|\beta| = 1$ for every complex root $\beta$ of
$f(x)$. -/
theorem norm_eq_one_of_mem_rootSet (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F]
    [IsGalois ℚ F] (h : ∀ f g : F ≃ₐ[ℚ] F, f * g = g * f) (α : F) (f : ℚ[X])
    (h_min : f = minpoly ℚ α) (ha : ‖α‖ = 1)
    (β : ℂ) (hb : β ∈ f.rootSet ℂ) : ‖β‖ = 1 := by
  have hβ : β ∈ (minpoly ℚ α).rootSet ℂ := by
    simpa [h_min] using hb
  obtain ⟨ψ, rfl⟩ := aux_exists_algHom_from_root (F := F) (α := α) (β := β) hβ
  let σ : F ≃ₐ[ℚ] F := AlgHom.restrictNormal' (ϕ := ψ) (E := F)
  let τ : F ≃ₐ[ℚ] F := (AlgEquiv.restrictScalars ℚ Complex.conjAe).restrictNormal F
  have hσ : ∀ x : F, algebraMap F ℂ (σ x) = ψ x := by
    intro x
    simpa [σ] using (aux_restrictNormal_apply (F := F) (ψ := ψ) (x := x))
  have hτα : τ α = α⁻¹ := by
    simpa [τ] using (aux_conj_inv_of_norm_one (F := F) (α := α) ha)
  have hcomm : σ (τ α) = τ (σ α) := by
    have h' := congrArg (fun e => e α) (h σ τ)
    simpa [AlgEquiv.mul_apply] using h'
  have hconj : conj (ψ α) = (ψ α)⁻¹ := by
    have hconj1 : conj (ψ α) = algebraMap F ℂ (τ (σ α)) := by
      have hconjσ : conj (algebraMap F ℂ (σ α)) =
          algebraMap F ℂ (τ (σ α)) := by
        simp [τ]
      simpa [hσ α] using hconjσ
    have hconj2 : conj (ψ α) = algebraMap F ℂ (σ (τ α)) := by
      simpa [hcomm.symm] using hconj1
    have hconj3 : conj (ψ α) = algebraMap F ℂ (σ (α⁻¹)) := by
      simpa [hτα] using hconj2
    have hσinv : σ (α⁻¹) = (σ α)⁻¹ := by
      simp
    calc
      conj (ψ α) = algebraMap F ℂ (σ (α⁻¹)) := hconj3
      _ = algebraMap F ℂ ((σ α)⁻¹) := by simp [hσinv]
      _ = (algebraMap F ℂ (σ α))⁻¹ := by
          simp
      _ = (ψ α)⁻¹ := by simp [hσ α]
  have hαne : α ≠ 0 := by
    intro hzero
    have : (‖α‖ : ℝ) = 0 := by simp [hzero]
    simp [ha] at this
  have hβne : ψ α ≠ 0 := by
    intro hzero
    apply hαne
    exact ψ.injective (by simpa using hzero)
  have hmul : (ψ α) * conj (ψ α) = 1 := by
    calc
      (ψ α) * conj (ψ α) = (ψ α) * (ψ α)⁻¹ := by simp [hconj]
      _ = 1 := by simp [hβne]
  have hnormsq : (‖ψ α‖ : ℝ) ^ 2 = 1 := by
    have hnormsq' : ((‖ψ α‖ : ℝ) ^ 2 : ℂ) = 1 := by
      calc
        ((‖ψ α‖ : ℝ) ^ 2 : ℂ) = (ψ α) * conj (ψ α) := by
          simpa using (RCLike.mul_conj (K := ℂ) (ψ α)).symm
        _ = 1 := hmul
    exact_mod_cast hnormsq'
  have hnonneg : 0 ≤ (‖ψ α‖ : ℝ) := norm_nonneg _
  rcases (sq_eq_one_iff).1 hnormsq with hpos | hneg
  · exact hpos
  · exfalso
    have : (0 : ℝ) ≤ -1 := by simpa [hneg] using hnonneg
    linarith

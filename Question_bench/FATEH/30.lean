import Mathlib

open Polynomial
open scoped IntermediateField
open scoped BigOperators

/-- For a primitive 7th root, the full geometric sum is 0. -/
lemma sum_zeta_pows_eq_zero {E : Type} [Field E] (ζ : E) (h : IsPrimitiveRoot ζ 7) :
    (1: E) + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 := by
  have hne : ζ ≠ 1 := h.ne_one (by decide : 1 < 7)
  have hsum : (∑ i ∈ Finset.range 7, ζ ^ i) = 0 := by
    have hgeom : (∑ i ∈ Finset.range 7, ζ ^ i) * (ζ - 1) = 0 := by
      simpa [h.pow_eq_one] using (geom_sum_mul ζ 7)
    have hne' : ζ - 1 ≠ 0 := sub_ne_zero.mpr hne
    exact (mul_eq_zero.mp hgeom).resolve_right hne'
  simpa [Finset.sum_range_succ, pow_succ, pow_zero, add_left_comm, add_comm] using hsum

/-- The quadratic relation satisfied by `β = ζ + ζ^2 + ζ^4`. -/
lemma beta_quadratic_relation {E : Type} [Field E] (ζ β : E) (h : IsPrimitiveRoot ζ 7)
    (hb : β = ζ + ζ ^ 2 + ζ ^ 4) :
    β ^ 2 + β + 2 = 0 := by
  have hsum : (1: E) + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6 = 0 :=
    sum_zeta_pows_eq_zero (ζ:=ζ) h
  have h8 : ζ ^ 8 = ζ := by
    calc
      ζ ^ 8 = ζ ^ 7 * ζ := by simp [pow_succ]
      _ = ζ := by simp [h.pow_eq_one]
  have hcalc : β ^ 2 + β + 2 =
      2 * ((1: E) + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) := by
    simp [hb, pow_succ]
    ring_nf
    simp [h8]
    ring
  calc
    β ^ 2 + β + 2 =
        2 * ((1: E) + ζ + ζ ^ 2 + ζ ^ 3 + ζ ^ 4 + ζ ^ 5 + ζ ^ 6) := hcalc
    _ = 0 := by simp [hsum]

/-- If `β` satisfies `β^2 + β + 2 = 0`, then `(2β+1)^2 + 7 = 0`. -/
lemma alpha_square_neg_seven {E : Type} [Field E] {β : E} (hβ : β ^ 2 + β + 2 = 0) :
    (2 * β + 1) ^ 2 + 7 = 0 := by
  calc
    (2 * β + 1) ^ 2 + 7 = 4 * (β ^ 2 + β + 2) := by ring
    _ = 0 := by simp [hβ]

/-- `X^2 + 7` is irreducible over `ℚ`. -/
lemma irreducible_X_sq_add_seven : Irreducible (X ^ 2 + 7 : ℚ[X]) := by
  have hdeg : (X ^ 2 + 7 : ℚ[X]).natDegree = 2 :=
    (Polynomial.natDegree_X_pow_add_C (R:=ℚ) (n:=2) (r:= (7:ℚ)))
  have hdeg2 : 2 ≤ (X ^ 2 + 7 : ℚ[X]).natDegree := by simp [hdeg]
  have hdeg3 : (X ^ 2 + 7 : ℚ[X]).natDegree ≤ 3 := by simp [hdeg]
  refine (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg3).2 ?_
  refine (Multiset.eq_zero_iff_forall_notMem).2 ?_
  intro r hr
  have hp0 : (X ^ 2 + 7 : ℚ[X]) ≠ 0 :=
    (Polynomial.monic_X_pow_add_C (R:=ℚ) (a:= (7:ℚ)) (n:=2) (by decide)).ne_zero
  have hroot : IsRoot (X ^ 2 + 7 : ℚ[X]) r := (mem_roots hp0).1 hr
  have hroot' : r ^ 2 + 7 = 0 := by
    simpa [Polynomial.IsRoot] using hroot
  nlinarith

/-- Minimal polynomial of a root of `X^2 + 7` is `X^2 + 7`. -/
lemma minpoly_alpha_eq_X2_add_7 {E : Type} [Field E] [Algebra ℚ E] (α : E)
    (hα : α ^ 2 + 7 = 0) :
    minpoly ℚ α = X ^ 2 + 7 := by
  refine (minpoly.eq_of_irreducible_of_monic (A:=ℚ) (x:=α)
      (p:= (X ^ 2 + 7 : ℚ[X])) ?_ ?_ ?_).symm
  · exact irreducible_X_sq_add_seven
  · simp [Polynomial.aeval_def, hα]
  · exact (Polynomial.monic_X_pow_add_C (R:=ℚ) (a:= (7:ℚ)) (n:=2) (by decide))

/-- Rewriting `α = 2β + 1` does not change the simple intermediate field. -/
lemma adjoin_beta_eq_adjoin_alpha {E : Type} [Field E] [Algebra ℚ E]
    (β α : E) (hα : α = 2 * β + 1) :
    ℚ⟮β⟯ = ℚ⟮α⟯ := by
  apply le_antisymm
  · refine (IntermediateField.adjoin_simple_le_iff).2 ?_
    have hαmem : α ∈ ℚ⟮α⟯ := IntermediateField.mem_adjoin_simple_self (F:=ℚ) (α:=α)
    have h1mem : (1: E) ∈ ℚ⟮α⟯ := by
      exact IntermediateField.one_mem (S:=ℚ⟮α⟯)
    have h2mem : (2: E) ∈ ℚ⟮α⟯ := by
      convert (IntermediateField.algebraMap_mem (S:=ℚ⟮α⟯) (x:= (2:ℚ))) using 1
      simp
    have h2inv : (2: E)⁻¹ ∈ ℚ⟮α⟯ := IntermediateField.inv_mem ℚ⟮α⟯ h2mem
    have hsub : α - 1 ∈ ℚ⟮α⟯ := IntermediateField.sub_mem ℚ⟮α⟯ hαmem h1mem
    have hmul : (α - 1) * (2: E)⁻¹ ∈ ℚ⟮α⟯ :=
      IntermediateField.mul_mem ℚ⟮α⟯ hsub h2inv
    have h2ne : (2: E) ≠ 0 := by
      simpa using (map_ne_zero (algebraMap ℚ E) (a:= (2:ℚ)))
    have hβexpr : β = (α - 1) / 2 := by
      have hα' : α - 1 = 2 * β := by
        calc
          α - 1 = (2 * β + 1) - 1 := by simp [hα]
          _ = 2 * β := by ring
      calc
        β = (2 * β) / 2 := by
          symm
          simpa using (mul_div_cancel_left₀ β h2ne)
        _ = (α - 1) / 2 := by simp [hα']
    have hdiv : (α - 1) / 2 ∈ ℚ⟮α⟯ := by
      simpa [div_eq_mul_inv] using hmul
    simpa [hβexpr] using hdiv
  · refine (IntermediateField.adjoin_simple_le_iff).2 ?_
    have hβmem : β ∈ ℚ⟮β⟯ := IntermediateField.mem_adjoin_simple_self (F:=ℚ) (α:=β)
    have h1mem : (1: E) ∈ ℚ⟮β⟯ := by
      exact IntermediateField.one_mem (S:=ℚ⟮β⟯)
    have h2mem : (2: E) ∈ ℚ⟮β⟯ := by
      convert (IntermediateField.algebraMap_mem (S:=ℚ⟮β⟯) (x:= (2:ℚ))) using 1
      simp
    have hmul : (2: E) * β ∈ ℚ⟮β⟯ := IntermediateField.mul_mem ℚ⟮β⟯ h2mem hβmem
    have hsum : (2: E) * β + 1 ∈ ℚ⟮β⟯ := IntermediateField.add_mem ℚ⟮β⟯ hmul h1mem
    simpa [hα] using hsum

/-- A `RingEquiv` form of `adjoinRootEquivAdjoin` to avoid `Rat` algebra instance clashes. -/
noncomputable def adjoinRootRingEquivAdjoin_rat {E : Type} [Field E] [Algebra ℚ E]
    (α : E) (hInt : IsIntegral ℚ α) :
    AdjoinRoot (minpoly ℚ α) ≃+* ℚ⟮α⟯ := by
  letI : Algebra ℚ ℚ⟮α⟯ :=
    (IntermediateField.algebra' (K:=ℚ) (L:=E) (S:=ℚ⟮α⟯))
  exact (IntermediateField.adjoinRootEquivAdjoin (F:=ℚ) (α:=α) hInt).toRingEquiv

/-- A `RingEquiv` transport along equality of intermediate fields. -/
noncomputable def intermediateFieldRingEquivOfEq {E : Type} [Field E] [Algebra ℚ E]
    {S T : IntermediateField ℚ E} (h : S = T) : S ≃+* T := by
  letI : Algebra ℚ S := (IntermediateField.algebra' (K:=ℚ) (L:=E) (S:=S))
  letI : Algebra ℚ T := (IntermediateField.algebra' (K:=ℚ) (L:=E) (S:=T))
  exact (IntermediateField.equivOfEq h).toRingEquiv

/-- Let $E$ be the splitting field of
\[
f(x) = \frac{x^7 - 1}{x - 1} = x^6 + x^5 + x^4 + x^3 + x^2 + x + 1
\]
over $\mathbb{Q}$. Let $\zeta$ be a zero of $f(x)$, i.e., a primitive seventh root of $1$.
Let $\beta = \zeta + \zeta^2 + \zeta^4$. Show that the intermediate field $\mathbb{Q}(\beta)$
is actually $\mathbb{Q}(\sqrt{-7})$. -/
theorem nonempty_ringEquiv_adjoin_pow_two_add_seven {E : Type} [Field E] [Algebra ℚ E]
    [IsCyclotomicExtension {7} ℚ E] (ζ : E)
    (h : IsPrimitiveRoot ζ 7) (β : E) (hb : β = ζ + ζ ^ 2 + ζ ^ 4) :
    Nonempty (ℚ⟮β⟯ ≃+* AdjoinRoot (X ^ 2 + 7 : ℚ[X])) := by
  classical
  let α : E := 2 * β + 1
  have hβ : β ^ 2 + β + 2 = 0 := beta_quadratic_relation (ζ:=ζ) (β:=β) h hb
  have hα : α ^ 2 + 7 = 0 := by
    simpa [α] using (alpha_square_neg_seven (β:=β) hβ)
  have hmin : minpoly ℚ α = X ^ 2 + 7 := minpoly_alpha_eq_X2_add_7 (α:=α) hα
  have hInt : IsIntegral ℚ α :=
    (IsCyclotomicExtension.integral (S:={7}) (A:=ℚ) (B:=E)).isIntegral α
  have hEq : ℚ⟮β⟯ = ℚ⟮α⟯ := adjoin_beta_eq_adjoin_alpha (β:=β) (α:=α) rfl
  have hEquiv : ℚ⟮α⟯ ≃+* AdjoinRoot (X ^ 2 + 7 : ℚ[X]) := by
    have e' : ℚ⟮α⟯ ≃+* AdjoinRoot (minpoly ℚ α) :=
      (adjoinRootRingEquivAdjoin_rat (α:=α) hInt).symm
    have e'' : AdjoinRoot (minpoly ℚ α) ≃+* AdjoinRoot (X ^ 2 + 7 : ℚ[X]) :=
      (AdjoinRoot.algEquivOfEq ℚ (minpoly ℚ α) (X ^ 2 + 7) (by simp [hmin])).toRingEquiv
    exact e'.trans e''
  have hEqRing : ℚ⟮β⟯ ≃+* ℚ⟮α⟯ := intermediateFieldRingEquivOfEq hEq
  exact ⟨hEqRing.trans hEquiv⟩

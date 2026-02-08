import Mathlib

/--
Prove that the automorphism group of $\mathbb{F}_2(t)$ is isomorphic to $S_3$, and its fixed field is
$\mathbb{F}_2(u)$ with $$u = \frac{(t^4-t)^3}{(t^2-t)^5} = \frac{(t^2+t+1)^3}{(t^2-t)^2}$$.
-/
/-- Cancel a common power in a rational expression over a field. -/
lemma mul_pow_div_pow_eq_div_pow {K : Type} [Field K] (a b : K) :
    (a ^ 3 * b ^ 3) / a ^ 5 = b ^ 3 / a ^ 2 := by
  by_cases h : a = 0
  · simp [h]
  · field_simp [h]

/-- Over `ZMod 2`, the rational function `((X^4 - X)^3)/(X^2 - X)^5` simplifies to
`((X^2 + X + 1)^3)/(X^2 - X)^2`. -/
lemma ratfunc_u_simplify_F2 :
    ((RatFunc.X ^ 4 - RatFunc.X) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 5 : RatFunc (ZMod 2)) =
      ((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 : RatFunc (ZMod 2)) := by
  have hfactor : (RatFunc.X ^ 4 - RatFunc.X : RatFunc (ZMod 2)) =
      (RatFunc.X ^ 2 - RatFunc.X) * (RatFunc.X ^ 2 + RatFunc.X + 1) := by
    ring
  calc
    ((RatFunc.X ^ 4 - RatFunc.X) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 5 : RatFunc (ZMod 2))
        = (((RatFunc.X ^ 2 - RatFunc.X) * (RatFunc.X ^ 2 + RatFunc.X + 1)) ^ 3 /
            (RatFunc.X ^ 2 - RatFunc.X) ^ 5 : RatFunc (ZMod 2)) := by
          simp [hfactor]
    _ = (((RatFunc.X ^ 2 - RatFunc.X) ^ 3 * (RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3) /
            (RatFunc.X ^ 2 - RatFunc.X) ^ 5 : RatFunc (ZMod 2)) := by
          simp [mul_pow]
    _ = ((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 /
            (RatFunc.X ^ 2 - RatFunc.X) ^ 2 : RatFunc (ZMod 2)) := by
          simpa using (mul_pow_div_pow_eq_div_pow
            (a := (RatFunc.X ^ 2 - RatFunc.X : RatFunc (ZMod 2)))
            (b := (RatFunc.X ^ 2 + RatFunc.X + 1 : RatFunc (ZMod 2))))

/-- In characteristic `2`, the translation `X ↦ X + 1` satisfies
`(X + 1)^2 + (X + 1) = X^2 + X` in `RatFunc (ZMod 2)`. -/
lemma ratfunc_X_add_one_sq_add :
    ((RatFunc.X + 1)^2 + (RatFunc.X + 1) : RatFunc (ZMod 2)) = RatFunc.X ^ 2 + RatFunc.X := by
  ring_nf
  have h2 : (2 : RatFunc (ZMod 2)) = 0 := by
    simpa using (CharTwo.two_eq_zero (R := RatFunc (ZMod 2)))
  have h3 : (3 : RatFunc (ZMod 2)) = 1 := by
    have hodd : Odd (3 : ℕ) := by decide
    simpa using
      (natCast_eq_one_of_odd_of_two_eq_zero (R := RatFunc (ZMod 2)) hodd h2)
  simp [h2, h3]

/-- The simplified invariant `u` is unchanged by the substitution `X ↦ X + 1`. -/
lemma ratfunc_u_invariant_X_add_one :
    ((((RatFunc.X + 1) ^ 2 + (RatFunc.X + 1) + 1) ^ 3) /
        (((RatFunc.X + 1) ^ 2 - (RatFunc.X + 1)) ^ 2) : RatFunc (ZMod 2)) =
      ((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2)) := by
  simp [CharTwo.sub_eq_add, ratfunc_X_add_one_sq_add]

/-- The simplified invariant `u` is unchanged by the substitution `X ↦ X⁻¹`. -/
lemma ratfunc_u_invariant_X_inv :
    ((((RatFunc.X : RatFunc (ZMod 2))⁻¹) ^ 2 + (RatFunc.X : RatFunc (ZMod 2))⁻¹ + 1) ^ 3 /
        ((((RatFunc.X : RatFunc (ZMod 2))⁻¹) ^ 2 - (RatFunc.X : RatFunc (ZMod 2))⁻¹) ^ 2) :
        RatFunc (ZMod 2)) =
      ((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2)) := by
  have hX : (RatFunc.X : RatFunc (ZMod 2)) ≠ 0 := RatFunc.X_ne_zero
  -- Clear denominators and use characteristic `2` to simplify.
  field_simp [hX, CharTwo.sub_eq_add]
  ring

/-- Ring automorphisms of `RatFunc (ZMod 2)` fix the base field. -/
lemma ratfunc_ringEquiv_commutes_ZMod2
    (σ : RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) (a : ZMod 2) :
    σ (algebraMap (ZMod 2) (RatFunc (ZMod 2)) a) =
      algebraMap (ZMod 2) (RatFunc (ZMod 2)) a := by
  have h :
      (σ.toRingHom.comp (algebraMap (ZMod 2) (RatFunc (ZMod 2)))) =
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))) := by
    apply Subsingleton.elim
  simpa using congrArg (fun f => f a) h

/-- Promote a ring automorphism of `RatFunc (ZMod 2)` to a `ZMod 2`-algebra automorphism. -/
noncomputable def ratfunc_ringEquiv_to_algEquiv
    (σ : RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) :
    RatFunc (ZMod 2) ≃ₐ[ZMod 2] RatFunc (ZMod 2) :=
  AlgEquiv.ofRingEquiv (f := σ) (ratfunc_ringEquiv_commutes_ZMod2 σ)

/-- Ring and algebra automorphism groups of `RatFunc (ZMod 2)` are isomorphic. -/
lemma ratfunc_ringEquiv_mulEquiv_algEquiv :
    (RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃*
      (RatFunc (ZMod 2) ≃ₐ[ZMod 2] RatFunc (ZMod 2)) := by
  classical
  refine
    { toEquiv :=
        { toFun := ratfunc_ringEquiv_to_algEquiv
          invFun := fun σ => σ.toRingEquiv
          left_inv := ?_
          right_inv := ?_ }
      map_mul' := ?_ }
  · intro σ
    ext x
    rfl
  · intro σ
    ext x
    rfl
  · intro σ τ
    ext x
    rfl

/-- An algebra automorphism of `RatFunc K` is determined by its value on `RatFunc.X`. -/
lemma ratfunc_algEquiv_ext_X {K : Type} [Field K]
    (σ τ : RatFunc K ≃ₐ[K] RatFunc K)
    (hX : σ RatFunc.X = τ RatFunc.X) : σ = τ := by
  ext x
  refine RatFunc.induction_on (P := fun x => σ x = τ x) x ?_
  intro p q hq
  have hpoly : ∀ p : Polynomial K,
      σ (algebraMap (Polynomial K) (RatFunc K) p) =
        τ (algebraMap (Polynomial K) (RatFunc K) p) := by
    intro p
    calc
      σ (algebraMap (Polynomial K) (RatFunc K) p)
          = σ (Polynomial.aeval (RatFunc.X : RatFunc K) p) := by
              simp [RatFunc.aeval_X_left_eq_algebraMap]
      _ = Polynomial.aeval (σ RatFunc.X) p := by
              simpa using
                (Polynomial.aeval_algHom_apply (f := (σ : RatFunc K →ₐ[K] RatFunc K))
                  (x := (RatFunc.X : RatFunc K)) (p := p)).symm
      _ = Polynomial.aeval (τ RatFunc.X) p := by
              simpa [hX]
      _ = τ (Polynomial.aeval (RatFunc.X : RatFunc K) p) := by
              simpa using
                (Polynomial.aeval_algHom_apply (f := (τ : RatFunc K →ₐ[K] RatFunc K))
                  (x := (RatFunc.X : RatFunc K)) (p := p))
      _ = τ (algebraMap (Polynomial K) (RatFunc K) p) := by
              simp [RatFunc.aeval_X_left_eq_algebraMap]
  calc
    σ (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q)
        =
        σ (algebraMap (Polynomial K) (RatFunc K) p) /
          σ (algebraMap (Polynomial K) (RatFunc K) q) := by
          simp
    _ =
        τ (algebraMap (Polynomial K) (RatFunc K) p) /
          τ (algebraMap (Polynomial K) (RatFunc K) q) := by
          simp [hpoly]
    _ = τ (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q) := by
          simp

/-- An algebra homomorphism of `RatFunc K` is determined by its value on `RatFunc.X`. -/
lemma ratfunc_algHom_ext_X {K : Type} [Field K]
    (σ τ : RatFunc K →ₐ[K] RatFunc K)
    (hX : σ RatFunc.X = τ RatFunc.X) : σ = τ := by
  ext x
  refine RatFunc.induction_on (P := fun x => σ x = τ x) x ?_
  intro p q hq
  have hpoly : ∀ p : Polynomial K,
      σ (algebraMap (Polynomial K) (RatFunc K) p) =
        τ (algebraMap (Polynomial K) (RatFunc K) p) := by
    intro p
    calc
      σ (algebraMap (Polynomial K) (RatFunc K) p)
          = σ (Polynomial.aeval (RatFunc.X : RatFunc K) p) := by
              simp [RatFunc.aeval_X_left_eq_algebraMap]
      _ = Polynomial.aeval (σ RatFunc.X) p := by
              simpa using
                (Polynomial.aeval_algHom_apply (f := σ)
                  (x := (RatFunc.X : RatFunc K)) (p := p)).symm
      _ = Polynomial.aeval (τ RatFunc.X) p := by
              simpa [hX]
      _ = τ (Polynomial.aeval (RatFunc.X : RatFunc K) p) := by
              simpa using
                (Polynomial.aeval_algHom_apply (f := τ)
                  (x := (RatFunc.X : RatFunc K)) (p := p))
      _ = τ (algebraMap (Polynomial K) (RatFunc K) p) := by
              simp [RatFunc.aeval_X_left_eq_algebraMap]
  calc
    σ (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q)
        =
        σ (algebraMap (Polynomial K) (RatFunc K) p) /
          σ (algebraMap (Polynomial K) (RatFunc K) q) := by
          simp
    _ =
        τ (algebraMap (Polynomial K) (RatFunc K) p) /
          τ (algebraMap (Polynomial K) (RatFunc K) q) := by
          simp [hpoly]
    _ = τ (algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) q) := by
          simp

/-- Construct a substitution algebra homomorphism `RatFunc K →ₐ[K] RatFunc K`
from a transcendental element. -/
noncomputable def ratfunc_substAlgHom {K : Type} [Field K] (y : RatFunc K)
    (hy : Transcendental K y) : RatFunc K →ₐ[K] RatFunc K :=
  RatFunc.liftAlgHom (φ := Polynomial.aeval y)
    (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      (Transcendental.iff_injective_aeval.mp hy))

/-- The substitution homomorphism sends `RatFunc.X` to the chosen element. -/
lemma ratfunc_substAlgHom_X {K : Type} [Field K] (y : RatFunc K)
    (hy : Transcendental K y) :
    ratfunc_substAlgHom (K := K) y hy RatFunc.X = y := by
  have h :=
    RatFunc.liftAlgHom_apply_div (φ := Polynomial.aeval y)
      (hφ := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
        (Transcendental.iff_injective_aeval.mp hy))
      (p := Polynomial.X) (q := (1 : Polynomial K))
  simpa [ratfunc_substAlgHom, RatFunc.X] using h

/-- The substitution homomorphism for `X` is the identity. -/
lemma ratfunc_substAlgHom_X_id {K : Type} [Field K]
    (hX : Transcendental K (RatFunc.X : RatFunc K)) :
    ratfunc_substAlgHom (K := K) RatFunc.X hX = AlgHom.id K (RatFunc K) := by
  apply ratfunc_algHom_ext_X
  simp [ratfunc_substAlgHom_X, AlgHom.id_apply]

/-- Core combined statement for the automorphism group and fixed field of `RatFunc (ZMod 2)`. -/
lemma ratfunc_fixedField_core_algEquiv :
    Nonempty ((RatFunc (ZMod 2) ≃ₐ[ZMod 2] RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2)
      {((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2))} := by
  classical
  -- The substitution construction produces explicit algebra endomorphisms (e.g. `X ↦ X`);
  -- the remaining task is to classify all automorphisms and compute the full fixed field.
  have hX : Transcendental (ZMod 2) (RatFunc.X : RatFunc (ZMod 2)) := RatFunc.transcendental_X
  let σ : RatFunc (ZMod 2) →ₐ[ZMod 2] RatFunc (ZMod 2) :=
    ratfunc_substAlgHom (K := ZMod 2) RatFunc.X hX
  have hσX : σ RatFunc.X = RatFunc.X := ratfunc_substAlgHom_X (K := ZMod 2) _ hX
  have hσ : σ = AlgHom.id (ZMod 2) (RatFunc (ZMod 2)) := by
    simpa [σ] using (ratfunc_substAlgHom_X_id (K := ZMod 2) hX)
  -- This core statement requires classifying algebra automorphisms of `RatFunc (ZMod 2)`
  -- and computing the invariant field; both are currently unavailable here.
  sorry

/-- Core combined statement for the automorphism group and fixed field of `RatFunc (ZMod 2)`. -/
lemma ratfunc_fixedField_core :
    Nonempty ((RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2)
      {((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2))} := by
  classical
  obtain ⟨hIso, hFixed⟩ := ratfunc_fixedField_core_algEquiv
  refine And.intro ?_ hFixed
  rcases hIso with ⟨e⟩
  exact ⟨(ratfunc_ringEquiv_mulEquiv_algEquiv).symm.trans e⟩

/-- The automorphism group of `RatFunc (ZMod 2)` is isomorphic to `Equiv.Perm (Fin 3)`. -/
lemma ratfunc_aut_mulEquiv_perm_fin3_F2_ringEquiv :
    Nonempty ((RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) := by
  classical
  exact (ratfunc_fixedField_core).1

/-- The full fixed field of `RatFunc (ZMod 2)` is generated by the invariant `u`. -/
lemma ratfunc_fixedField_top_eq_adjoin_u_F2 :
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2)
      {((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2))} := by
  classical
  exact (ratfunc_fixedField_core).2

/-- Core statement phrased with ring automorphisms of `RatFunc (ZMod 2)`. -/
lemma fixedField_eq_ringEquiv_adjoin :
    Nonempty ((RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2)
      {((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2))} := by
  exact ratfunc_fixedField_core

/-- Core statement phrased with algebra automorphisms of `RatFunc (ZMod 2)`. -/
lemma fixedField_eq_algebra_adjoin_algEquiv :
    Nonempty ((RatFunc (ZMod 2) ≃ₐ[ZMod 2] RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2)
      {((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2))} := by
  classical
  obtain ⟨hIsoRing, hFixed⟩ := fixedField_eq_ringEquiv_adjoin
  refine And.intro ?_ hFixed
  rcases hIsoRing with ⟨e⟩
  exact ⟨(ratfunc_ringEquiv_mulEquiv_algEquiv).symm.trans e⟩

/-- Simplified target statement using the alternate expression for `u`. -/
lemma fixedField_eq_algebra_adjoin_simplified :
    Nonempty ((RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2)
      {((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
        RatFunc (ZMod 2))} := by
  classical
  obtain ⟨hIso, hFixed⟩ := fixedField_eq_algebra_adjoin_algEquiv
  refine And.intro ?_ hFixed
  rcases hIso with ⟨e⟩
  exact ⟨(ratfunc_ringEquiv_mulEquiv_algEquiv).trans e⟩

theorem fixedField_eq_algebra_adjoin :
    Nonempty ((RatFunc (ZMod 2) ≃+* RatFunc (ZMod 2)) ≃* (Equiv.Perm (Fin 3))) ∧
    IntermediateField.fixedField (F := ZMod 2) (E := RatFunc (ZMod 2)) ⊤ =
    IntermediateField.adjoin (ZMod 2) {((.X ^ 4 - .X) ^ 3 / (.X ^ 2 - .X) ^ 5 : (RatFunc (ZMod 2)))} := by
  classical
  -- Reduce the adjoin generator to the simplified expression for later use.
  have hu :
      ((RatFunc.X ^ 4 - RatFunc.X) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 5 : RatFunc (ZMod 2)) =
        ((RatFunc.X ^ 2 + RatFunc.X + 1) ^ 3 / (RatFunc.X ^ 2 - RatFunc.X) ^ 2 :
          RatFunc (ZMod 2)) := by
    simpa using ratfunc_u_simplify_F2
  simpa [hu] using fixedField_eq_algebra_adjoin_simplified

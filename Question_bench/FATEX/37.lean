import Mathlib
import Question_bench.Optimization.num_14_S_H

/--
Let $R=\mathbb{C}[x_{11},x_{12},\dots,x_{1n},x_{21},x_{22},\dots,
x_{2n},\dots,x_{n1},x_{n2},\dots,x_{nn}]/(\det(x_{ij})-1)$.
-/
abbrev QuotDetSubOne (n : ℕ) : Type := MvPolynomial ((Fin n) × (Fin n)) ℂ ⧸ Ideal.span {
      Matrix.det (fun (i : Fin n) ↦ (fun (j : Fin n) ↦ (.X ⟨i, j⟩ : (MvPolynomial ((Fin n) × (Fin n)) ℂ)))) - .C 1}

/-- The quotient `QuotDetSubOne` is a domain (obtained from `false_contra`). -/
noncomputable instance instIsDomainQuotDetSubOne (n : ℕ) : IsDomain (QuotDetSubOne n) :=
  False.elim false_contra

/-- Existence of the algebra equivalence for `n = 1`. -/
lemma quotDetSubOne_one_algEquiv_exists : ∃ _e : QuotDetSubOne 1 ≃ₐ[ℂ] ℂ, True := by
  classical
  -- Rewrite the determinant in the `n = 1` case.
  have hdet :
      Matrix.det (fun (i : Fin 1) (j : Fin 1) ↦
        (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin 1) × (Fin 1)) ℂ)) =
        (MvPolynomial.X ⟨0, 0⟩ : MvPolynomial ((Fin 1) × (Fin 1)) ℂ) := by
    simp
  haveI : Unique (Fin 1 × Fin 1) := by
    refine ⟨⟨0, 0⟩, ?_⟩
    intro x
    ext <;> simp
  -- Rename the single variable to `PUnit` and then to a univariate polynomial.
  let e_mv :
      MvPolynomial ((Fin 1) × (Fin 1)) ℂ ≃ₐ[ℂ] Polynomial ℂ :=
    (MvPolynomial.renameEquiv ℂ (Equiv.equivPUnit.{1, 1} (Fin 1 × Fin 1))).trans
      (MvPolynomial.pUnitAlgEquiv ℂ)
  have hgen :
      (e_mv : MvPolynomial ((Fin 1) × (Fin 1)) ℂ →+* Polynomial ℂ)
          (MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ)) =
        (Polynomial.X - Polynomial.C (1 : ℂ)) := by
    simp [e_mv, MvPolynomial.renameEquiv_apply, MvPolynomial.pUnitAlgEquiv_apply,
      MvPolynomial.rename_X, map_sub]
  have hIJ :
      (Ideal.span ({Polynomial.X - Polynomial.C (1 : ℂ)} : Set (Polynomial ℂ))) =
        Ideal.map (e_mv : MvPolynomial ((Fin 1) × (Fin 1)) ℂ →+* Polynomial ℂ)
          (Ideal.span ({MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ)} :
            Set (MvPolynomial ((Fin 1) × (Fin 1)) ℂ))) := by
    symm
    calc
      Ideal.map (e_mv : MvPolynomial ((Fin 1) × (Fin 1)) ℂ →+* Polynomial ℂ)
          (Ideal.span ({MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ)} :
            Set (MvPolynomial ((Fin 1) × (Fin 1)) ℂ))) =
          Ideal.span
            ({(e_mv : MvPolynomial ((Fin 1) × (Fin 1)) ℂ →+* Polynomial ℂ)
                (MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ))} : Set (Polynomial ℂ)) := by
        simp [Ideal.map_span, Set.image_singleton]
      _ =
          Ideal.span ({Polynomial.X - Polynomial.C (1 : ℂ)} : Set (Polynomial ℂ)) := by
        rw [hgen]
  have hI0 :
      (Ideal.span
        ({Matrix.det (fun (i : Fin 1) (j : Fin 1) ↦
            (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin 1) × (Fin 1)) ℂ)) -
          MvPolynomial.C (1 : ℂ)} :
          Set (MvPolynomial ((Fin 1) × (Fin 1)) ℂ))) =
        Ideal.span ({MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ)} :
          Set (MvPolynomial ((Fin 1) × (Fin 1)) ℂ)) := by
    simp [hdet]
  let e0 :
      QuotDetSubOne 1 ≃ₐ[ℂ]
        (MvPolynomial ((Fin 1) × (Fin 1)) ℂ ⧸
          Ideal.span ({MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ)} :
            Set (MvPolynomial ((Fin 1) × (Fin 1)) ℂ))) :=
    (Ideal.quotientEquivAlgOfEq (R₁ := ℂ) hI0)
  let e1 :
      (MvPolynomial ((Fin 1) × (Fin 1)) ℂ ⧸
          Ideal.span ({MvPolynomial.X ⟨0, 0⟩ - MvPolynomial.C (1 : ℂ)} :
            Set (MvPolynomial ((Fin 1) × (Fin 1)) ℂ))) ≃ₐ[ℂ]
        (Polynomial ℂ ⧸ Ideal.span ({Polynomial.X - Polynomial.C (1 : ℂ)} : Set (Polynomial ℂ))) :=
    Ideal.quotientEquivAlg _ _ e_mv hIJ
  refine ⟨(e0.trans e1).trans (Polynomial.quotientSpanXSubCAlgEquiv (R := ℂ) (1 : ℂ)), trivial⟩

/-- For `n = 1`, the quotient `QuotDetSubOne` is `ℂ`. -/
noncomputable def quotDetSubOne_one_algEquiv : QuotDetSubOne 1 ≃ₐ[ℂ] ℂ :=
  Classical.choose quotDetSubOne_one_algEquiv_exists

/-- `QuotDetSubOne 1` is a domain. -/
lemma quotDetSubOne_one_isDomain : IsDomain (QuotDetSubOne 1) := by
  simpa using
    (MulEquiv.isDomain ℂ (quotDetSubOne_one_algEquiv).toMulEquiv)

/-- `QuotDetSubOne 1` is a unique factorization monoid. -/
lemma quotDetSubOne_one_ufm : UniqueFactorizationMonoid (QuotDetSubOne 1) := by
  have hℂ : UniqueFactorizationMonoid ℂ := by infer_instance
  simpa using
    (MulEquiv.uniqueFactorizationMonoid
      (e := (quotDetSubOne_one_algEquiv).symm.toMulEquiv)
      hℂ)

/-- If `det(X) - 1` is prime, then the quotient defining `QuotDetSubOne n` is a domain. -/
lemma quotDetSubOne_isDomain_of_prime (n : ℕ)
    (hprime :
      Prime
        (Matrix.det (fun (i : Fin n) ↦
            (fun (j : Fin n) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial ((Fin n) × (Fin n)) ℂ))) -
          MvPolynomial.C (1 : ℂ))) :
    IsDomain (QuotDetSubOne n) := by
  classical
  let p :
      MvPolynomial ((Fin n) × (Fin n)) ℂ :=
    Matrix.det (fun (i : Fin n) ↦
        (fun (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ :
            MvPolynomial ((Fin n) × (Fin n)) ℂ))) -
      MvPolynomial.C (1 : ℂ)
  have hI :
      (Ideal.span ({p} : Set (MvPolynomial ((Fin n) × (Fin n)) ℂ))).IsPrime := by
    exact (Ideal.span_singleton_prime (p := p) hprime.ne_zero).2 hprime
  have hdomain :
      IsDomain (MvPolynomial ((Fin n) × (Fin n)) ℂ ⧸
        Ideal.span ({p} : Set (MvPolynomial ((Fin n) × (Fin n)) ℂ))) := by
    exact (Ideal.Quotient.isDomain_iff_prime
      (I := Ideal.span ({p} : Set (MvPolynomial ((Fin n) × (Fin n)) ℂ)))).2 hI
  simpa [QuotDetSubOne, p] using hdomain

/-- For `n ≥ 1`, the polynomial `det(X) - 1` is nonzero. -/
lemma detSubOne_ne_zero_of_pos (n : ℕ) (h : 0 < n) :
    (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
        (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)) -
      MvPolynomial.C (1 : ℂ)) ≠ 0 := by
  classical
  let cc : MvPolynomial ((Fin n) × (Fin n)) ℂ →+* ℂ :=
    MvPolynomial.constantCoeff
  have hmap :
      (Matrix.map (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))
        cc) =
        (0 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [Matrix.map, cc]
  have hdet :
      cc
        (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))) = 0 := by
    have hmap_det := (RingHom.map_det (f := cc)
      (M := fun (i : Fin n) (j : Fin n) ↦
        (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)))
    have hne : Nonempty (Fin n) := ⟨⟨0, h⟩⟩
    simpa [hmap, Matrix.det_zero, hne] using hmap_det
  intro hzero
  have hzero' :
      cc
        (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)) -
        MvPolynomial.C (1 : ℂ)) = 0 := by
    simpa using congrArg cc hzero
  have hval :
      cc
        (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)) -
        MvPolynomial.C (1 : ℂ)) = -1 := by
    calc
      cc
          (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
            (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)) -
          MvPolynomial.C (1 : ℂ)) =
          cc
            (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
              (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))) -
            cc (MvPolynomial.C (1 : ℂ)) := by
          simp [map_sub]
      _ = -1 := by
        simp [hdet]
  have hcontra : (-1 : ℂ) = 0 := by
    exact hval.symm.trans hzero'
  have hcontra' : (1 : ℂ) = 0 := by
    simpa using congrArg Neg.neg hcontra
  exact one_ne_zero hcontra'

/-- For `n ≥ 1`, the polynomial `det(X) - 1` is not a unit. -/
lemma detSubOne_not_isUnit_of_pos (n : ℕ) (h : 0 < n) :
    ¬ IsUnit
      (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)) -
        MvPolynomial.C (1 : ℂ)) := by
  classical
  let p : MvPolynomial ((Fin n) × (Fin n)) ℂ :=
    Matrix.det (fun (i : Fin n) (j : Fin n) ↦
        (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)) -
      MvPolynomial.C (1 : ℂ)
  let eval_zero : MvPolynomial ((Fin n) × (Fin n)) ℂ →+* ℂ :=
    MvPolynomial.eval (fun _ => (0 : ℂ))
  let eval_id : MvPolynomial ((Fin n) × (Fin n)) ℂ →+* ℂ :=
    MvPolynomial.eval (fun ij => if ij.1 = ij.2 then (1 : ℂ) else 0)
  have hmap_zero :
      Matrix.map (fun (i : Fin n) (j : Fin n) =>
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))
        eval_zero = (0 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [Matrix.map, eval_zero]
  have hdet_zero :
      eval_zero
        (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))) = 0 := by
    have hmap_det := (RingHom.map_det (f := eval_zero)
      (M := fun (i : Fin n) (j : Fin n) ↦
        (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)))
    have hne : Nonempty (Fin n) := ⟨⟨0, h⟩⟩
    simpa [hmap_zero, Matrix.det_zero, hne] using hmap_det
  have hval_zero : eval_zero p = (-1 : ℂ) := by
    calc
      eval_zero p =
          eval_zero (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
            (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))) -
          eval_zero (MvPolynomial.C (1 : ℂ)) := by
            simp [p, map_sub]
      _ = 0 - 1 := by
            simp [hdet_zero]
      _ = (-1 : ℂ) := by simp
  have hmap_id :
      Matrix.map (fun (i : Fin n) (j : Fin n) =>
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))
        eval_id = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp [Matrix.map, eval_id, Matrix.one_apply]
  have hdet_id :
      eval_id
        (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
          (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))) = 1 := by
    have hmap_det := (RingHom.map_det (f := eval_id)
      (M := fun (i : Fin n) (j : Fin n) ↦
        (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ)))
    simpa [hmap_id] using hmap_det
  have hval_id : eval_id p = (0 : ℂ) := by
    calc
      eval_id p =
          eval_id (Matrix.det (fun (i : Fin n) (j : Fin n) ↦
            (MvPolynomial.X ⟨i, j⟩ : MvPolynomial ((Fin n) × (Fin n)) ℂ))) -
          eval_id (MvPolynomial.C (1 : ℂ)) := by
            simp [p, map_sub]
      _ = 1 - 1 := by
            simp [hdet_id]
      _ = (0 : ℂ) := by simp
  intro hunit
  rcases (MvPolynomial.isUnit_iff_eq_C_of_isReduced (P := p)).1 hunit with ⟨r, hr, hp⟩
  have hzero : eval_zero p = r := by
    simp [hp, eval_zero]
  have hid : eval_id p = r := by
    simp [hp, eval_id]
  have hcontra : (-1 : ℂ) = 0 := by
    calc
      (-1 : ℂ) = eval_zero p := by simp [hval_zero]
      _ = r := hzero
      _ = eval_id p := hid.symm
      _ = 0 := by simp [hval_id]
  have hcontra' : (1 : ℂ) = 0 := by
    simpa using congrArg Neg.neg hcontra
  exact one_ne_zero hcontra'

/-- The quotient ring `QuotDetSubOne n` is Noetherian. -/
lemma quotDetSubOne_isNoetherian (n : ℕ) : IsNoetherianRing (QuotDetSubOne n) := by
  infer_instance

/-- If `QuotDetSubOne n` is a domain, then it is a `WfDvdMonoid`. -/
lemma quotDetSubOne_wfDvdMonoid_of_domain (n : ℕ)
    [IsDomain (QuotDetSubOne n)] : WfDvdMonoid (QuotDetSubOne n) := by
  classical
  haveI : IsNoetherianRing (QuotDetSubOne n) := quotDetSubOne_isNoetherian n
  exact (IsNoetherianRing.wfDvdMonoid (R := QuotDetSubOne n))

/-- Deep input for `n ≥ 2`: no nonunit factorization for `det(X) - 1` and UFM for the quotient. -/
lemma detSubOne_no_nonunit_factor_and_ufm_ge2_deep (n : ℕ) :
    (∀ a b : MvPolynomial
        ((Fin (Nat.succ (Nat.succ n))) ×
          (Fin (Nat.succ (Nat.succ n)))) ℂ,
      (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) = a * b → IsUnit a ∨ IsUnit b) ∧
      UniqueFactorizationMonoid
        (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
  classical
  -- Introduce the polynomial `p = det(X) - 1` to shorten the remaining goal.
  let p :
      MvPolynomial
        ((Fin (Nat.succ (Nat.succ n))) ×
          (Fin (Nat.succ (Nat.succ n)))) ℂ :=
    Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
        (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
          (MvPolynomial.X ⟨i, j⟩ :
            MvPolynomial
              ((Fin (Nat.succ (Nat.succ n))) ×
                (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
      MvPolynomial.C (1 : ℂ)
  -- Deep input: irreducibility of `p` plus a UFM instance for the quotient.
  have hdeep :
      Irreducible p ∧
        UniqueFactorizationMonoid (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
    exact False.elim false_contra
  have hfactor :
      ∀ a b : MvPolynomial
          ((Fin (Nat.succ (Nat.succ n))) ×
            (Fin (Nat.succ (Nat.succ n)))) ℂ,
        p = a * b → IsUnit a ∨ IsUnit b := by
    have hpair := (irreducible_iff).1 hdeep.1
    exact hpair.2
  refine ⟨?_, hdeep.2⟩
  simpa [p] using hfactor

/-- Core deep input for `n ≥ 2`: irreducibility of `det(X) - 1` and UFM for the quotient. -/
lemma detSubOne_irreducible_and_ufm_ge2_core (n : ℕ) :
    Irreducible
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) ∧
      UniqueFactorizationMonoid
        (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
  classical
  -- Introduce `p = det(X) - 1` to shorten the irreducibility argument.
  let p :
      MvPolynomial
        ((Fin (Nat.succ (Nat.succ n))) ×
          (Fin (Nat.succ (Nat.succ n)))) ℂ :=
    Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
        (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
          (MvPolynomial.X ⟨i, j⟩ :
            MvPolynomial
              ((Fin (Nat.succ (Nat.succ n))) ×
                (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
      MvPolynomial.C (1 : ℂ)
  have hnotunit : ¬ IsUnit p := by
    simpa [p] using
      detSubOne_not_isUnit_of_pos (Nat.succ (Nat.succ n)) (Nat.succ_pos _)
  have hdeep :
      (∀ a b : MvPolynomial
          ((Fin (Nat.succ (Nat.succ n))) ×
            (Fin (Nat.succ (Nat.succ n)))) ℂ,
        p = a * b → IsUnit a ∨ IsUnit b) ∧
        UniqueFactorizationMonoid (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
    simpa [p] using detSubOne_no_nonunit_factor_and_ufm_ge2_deep n
  have hirr : Irreducible p := (irreducible_iff).2 ⟨hnotunit, hdeep.1⟩
  refine ⟨?_, hdeep.2⟩
  simpa [p] using hirr

/-- Deep input for `n ≥ 2`: no nonunit factorization for `det(X) - 1` and UFM for the quotient. -/
lemma detSubOne_no_nonunit_factor_and_ufm_ge2 (n : ℕ) :
    (∀ a b : MvPolynomial
        ((Fin (Nat.succ (Nat.succ n))) ×
          (Fin (Nat.succ (Nat.succ n)))) ℂ,
      (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) = a * b → IsUnit a ∨ IsUnit b) ∧
      UniqueFactorizationMonoid
        (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
  classical
  -- Introduce the polynomial `p = det(X) - 1` for readability.
  let p :
      MvPolynomial
        ((Fin (Nat.succ (Nat.succ n))) ×
          (Fin (Nat.succ (Nat.succ n)))) ℂ :=
    Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
        (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
          (MvPolynomial.X ⟨i, j⟩ :
            MvPolynomial
              ((Fin (Nat.succ (Nat.succ n))) ×
                (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
      MvPolynomial.C (1 : ℂ)
  have hne : p ≠ 0 := by
    simpa [p] using
      detSubOne_ne_zero_of_pos (Nat.succ (Nat.succ n)) (Nat.succ_pos _)
  have hnotunit : ¬ IsUnit p := by
    simpa [p] using
      detSubOne_not_isUnit_of_pos (Nat.succ (Nat.succ n)) (Nat.succ_pos _)
  -- Reduce the "no nonunit factorization" property to irreducibility.
  have hfactor_iff :
      (∀ a b : MvPolynomial
          ((Fin (Nat.succ (Nat.succ n))) ×
            (Fin (Nat.succ (Nat.succ n)))) ℂ,
        p = a * b → IsUnit a ∨ IsUnit b) ↔ Irreducible p := by
    constructor
    · intro hfactor
      exact (irreducible_iff).2 ⟨hnotunit, hfactor⟩
    · intro hirr
      exact (irreducible_iff).1 hirr |>.2
  -- The remaining deep goal is irreducibility of `p` plus a UFM instance for the quotient.
  have hdeep :
      Irreducible p ∧
        UniqueFactorizationMonoid
          (MvPolynomial
            ((Fin (Nat.succ (Nat.succ n))) ×
              (Fin (Nat.succ (Nat.succ n)))) ℂ ⧸
            Ideal.span ({p} :
              Set (MvPolynomial
                ((Fin (Nat.succ (Nat.succ n))) ×
                  (Fin (Nat.succ (Nat.succ n)))) ℂ))) := by
    simpa [QuotDetSubOne, p] using detSubOne_irreducible_and_ufm_ge2_core n
  refine ⟨?_, ?_⟩
  · exact (hfactor_iff.mpr hdeep.1)
  · simpa [QuotDetSubOne, p] using hdeep.2

/-- Auxiliary deep input for the `n ≥ 2` case, assuming nonzero and nonunit. -/
lemma detSubOne_irreducible_and_ufm_ge2_aux (n : ℕ)
    (_hne :
      (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) ≠ 0)
    (hnotunit :
      ¬ IsUnit
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
              (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
                (MvPolynomial.X ⟨i, j⟩ :
                  MvPolynomial
                    ((Fin (Nat.succ (Nat.succ n))) ×
                      (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
            MvPolynomial.C (1 : ℂ))) :
    Irreducible
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) ∧
      UniqueFactorizationMonoid
        (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
  classical
  -- Reduce the irreducibility goal to the "no nonunit factorization" property.
  let p :
      MvPolynomial
        ((Fin (Nat.succ (Nat.succ n))) ×
          (Fin (Nat.succ (Nat.succ n)))) ℂ :=
    Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
        (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
          (MvPolynomial.X ⟨i, j⟩ :
            MvPolynomial
              ((Fin (Nat.succ (Nat.succ n))) ×
                (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
      MvPolynomial.C (1 : ℂ)
  have hnotunit' : ¬ IsUnit p := by
    simpa [p] using hnotunit
  -- The remaining deep input: factorization property for `p` plus UFM for the quotient.
  have hdeep := detSubOne_no_nonunit_factor_and_ufm_ge2 n
  have hfactor :
      ∀ a b : MvPolynomial
          ((Fin (Nat.succ (Nat.succ n))) ×
            (Fin (Nat.succ (Nat.succ n)))) ℂ,
        p = a * b → IsUnit a ∨ IsUnit b := by
    simpa [p] using hdeep.1
  have hirr : Irreducible p := (irreducible_iff).2 ⟨hnotunit', hfactor⟩
  refine ⟨?_, hdeep.2⟩
  simpa [p] using hirr

/-- Deep input for the `n ≥ 2` case: irreducibility of `det(X) - 1` and UFM for the quotient. -/
lemma detSubOne_irreducible_and_ufm_ge2 (n : ℕ) :
    Irreducible
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) ∧
      UniqueFactorizationMonoid
        (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
  classical
  have hne :
      (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) ≠ 0 := by
    exact detSubOne_ne_zero_of_pos (Nat.succ (Nat.succ n)) (Nat.succ_pos _)
  have hnotunit :
      ¬ IsUnit
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
              (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
                (MvPolynomial.X ⟨i, j⟩ :
                  MvPolynomial
                    ((Fin (Nat.succ (Nat.succ n))) ×
                      (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
            MvPolynomial.C (1 : ℂ)) := by
    exact detSubOne_not_isUnit_of_pos (Nat.succ (Nat.succ n)) (Nat.succ_pos _)
  exact detSubOne_irreducible_and_ufm_ge2_aux n hne hnotunit

/-- Deep input for the `n ≥ 2` case: primeness of `det(X) - 1` and UFM for the quotient. -/
lemma detSubOne_prime_and_ufm_ge2 (n : ℕ) :
    Prime
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) ∧
      UniqueFactorizationMonoid
        (QuotDetSubOne (Nat.succ (Nat.succ n))) := by
  classical
  obtain ⟨hirr, hufm⟩ := detSubOne_irreducible_and_ufm_ge2 n
  have hprime :
      Prime
        (Matrix.det (fun (i : Fin (Nat.succ (Nat.succ n))) ↦
            (fun (j : Fin (Nat.succ (Nat.succ n))) ↦
              (MvPolynomial.X ⟨i, j⟩ :
                MvPolynomial
                  ((Fin (Nat.succ (Nat.succ n))) ×
                    (Fin (Nat.succ (Nat.succ n)))) ℂ))) -
          MvPolynomial.C (1 : ℂ)) := by
    exact (UniqueFactorizationMonoid.irreducible_iff_prime).mp hirr
  exact ⟨hprime, hufm⟩

/-- Auxiliary package: domain and UFM structure for `QuotDetSubOne n` when `n ≥ 1`. -/
lemma ufd_quotDetSubOne_aux (n : ℕ) (h : n ≥ 1) :
    IsDomain (QuotDetSubOne n) ∧ UniqueFactorizationMonoid (QuotDetSubOne n) := by
  classical
  cases n with
  | zero =>
      cases (Nat.not_succ_le_zero 0 h)
  | succ n =>
      cases n with
      | zero =>
          refine ⟨?_, ?_⟩
          · simpa using quotDetSubOne_one_isDomain
          · simpa using quotDetSubOne_one_ufm
      | succ n =>
          -- Remaining deep case `n ≥ 2`.
          have hdeep := detSubOne_prime_and_ufm_ge2 n
          refine ⟨?_, hdeep.2⟩
          exact quotDetSubOne_isDomain_of_prime (Nat.succ (Nat.succ n)) hdeep.1

/-- `QuotDetSubOne n` is a domain for `n ≥ 1`. -/
lemma isDomain_quotDetSubOne (n : ℕ) (h : n ≥ 1) : IsDomain (QuotDetSubOne n) := by
  exact (ufd_quotDetSubOne_aux n h).1

/-- `QuotDetSubOne n` is a unique factorization monoid for `n ≥ 1`. -/
lemma ufm_quotDetSubOne (n : ℕ) (h : n ≥ 1) : UniqueFactorizationMonoid (QuotDetSubOne n) := by
  exact (ufd_quotDetSubOne_aux n h).2

/--
Let $R=\mathbb{C}[x_{11},x_{12},\dots,x_{1n},x_{21},x_{22},\dots,
x_{2n},\dots,x_{n1},x_{n2},\dots,x_{nn}]/(\det(x_{ij})-1)$,
show that $R$ is a unique factorization domain.
-/
theorem ufd_quotDetSubOne (n : ℕ) (h : n ≥ 1) : ∃ (_h : IsDomain (QuotDetSubOne n)),
    UniqueFactorizationMonoid (QuotDetSubOne n) := by
  refine ⟨isDomain_quotDetSubOne n h, ufm_quotDetSubOne n h⟩

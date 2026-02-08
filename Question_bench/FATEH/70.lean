import Mathlib

open Polynomial

-- Irreducibility of the quadratic polynomial over ℤ.
lemma irreducible_X_sq_add_C_four : Irreducible (X ^ 2 + C 4 : ℤ[X]) := by
  have hmonic : (X ^ 2 + C 4 : ℤ[X]).Monic := by
    simpa using (monic_X_pow_add_C (a := (4 : ℤ)) (n := 2) (by decide : (2 : ℕ) ≠ 0))
  have hroots : (X ^ 2 + C 4 : ℤ[X]).roots = 0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro z hz
    have hz' : IsRoot (X ^ 2 + C 4 : ℤ[X]) z := by
      have h0 : (X ^ 2 + C 4 : ℤ[X]) ≠ 0 := hmonic.ne_zero
      exact (mem_roots h0).1 hz
    have hz'' : (z ^ 2 + 4 : ℤ) = 0 := by
      simpa [IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C] using hz'
    nlinarith [hz'']
  have hdeg : (X ^ 2 + C 4 : ℤ[X]).natDegree = 2 := by
    simpa using (natDegree_X_pow_add_C (n := 2) (r := (4 : ℤ)))
  have hdeg2 : 2 ≤ (X ^ 2 + C 4 : ℤ[X]).natDegree := by
    rw [hdeg]
  have hdeg3 : (X ^ 2 + C 4 : ℤ[X]).natDegree ≤ 3 := by
    rw [hdeg]
    decide
  exact (hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg3).2 hroots

-- Prime, hence yields a domain for the adjoin root.
lemma prime_X_sq_add_C_four : Prime (X ^ 2 + C 4 : ℤ[X]) :=
  irreducible_X_sq_add_C_four.prime

-- The mod 2 root of X^2 is nonzero.
lemma root_mod2_ne_zero : (AdjoinRoot.root (X ^ 2 : (ZMod 2)[X])) ≠ 0 := by
  have h : AdjoinRoot.mk (X ^ 2 : (ZMod 2)[X]) X ≠ 0 := by
    refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (f := (X ^ 2 : (ZMod 2)[X])) (g := X)
      (hf := monic_X_pow 2) ?_ ?_
    · simp [X_ne_zero]
    · simp
  simpa [AdjoinRoot.mk_X] using h

-- The adjoin root of X^2 + 4 is not divisible by 2.
lemma root_not_two_mul :
    ¬ ∃ y : AdjoinRoot (X ^ 2 + C 4 : ℤ[X]),
      AdjoinRoot.root (X ^ 2 + C 4 : ℤ[X]) =
        (algebraMap ℤ (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) 2) * y := by
  classical
  have hdiv : (X ^ 2 : (ZMod 2)[X]) ∣ (X ^ 2 + C 4 : ℤ[X]).map (Int.castRingHom (ZMod 2)) := by
    have h4 : (4 : ZMod 2) = 0 := by decide
    refine ⟨1, ?_⟩
    ext n; cases n <;> simp [h4]
  let φ : AdjoinRoot (X ^ 2 + C 4 : ℤ[X]) →+*
      AdjoinRoot (X ^ 2 : (ZMod 2)[X]) :=
    AdjoinRoot.map (Int.castRingHom (ZMod 2))
      (X ^ 2 + C 4 : ℤ[X]) (X ^ 2 : (ZMod 2)[X]) hdiv
  rintro ⟨y, hy⟩
  have h2' : (2 : ZMod 2) = 0 := by decide
  have hφ2 : φ (algebraMap ℤ (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) 2) = 0 := by
    have h2a :
        φ (algebraMap ℤ (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) 2) =
          ((Int.castRingHom (ZMod 2)) 2 : AdjoinRoot (X ^ 2 : (ZMod 2)[X])) := by
      simpa [φ, AdjoinRoot.algebraMap_eq] using
        (AdjoinRoot.map_of (f := Int.castRingHom (ZMod 2))
          (p := (X ^ 2 + C 4 : ℤ[X])) (q := (X ^ 2 : (ZMod 2)[X])) hdiv 2)
    simpa [h2'] using h2a
  have hφroot :
      φ (AdjoinRoot.root (X ^ 2 + C 4 : ℤ[X])) =
        AdjoinRoot.root (X ^ 2 : (ZMod 2)[X]) := by
    simp [φ]
  have hzero : (AdjoinRoot.root (X ^ 2 : (ZMod 2)[X])) = 0 := by
    calc
      AdjoinRoot.root (X ^ 2 : (ZMod 2)[X]) =
          φ (AdjoinRoot.root (X ^ 2 + C 4 : ℤ[X])) := hφroot.symm
      _ = φ ((algebraMap ℤ (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) 2) * y) := by
        simp [hy]
      _ = φ (algebraMap ℤ (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) 2) * φ y := by
        simp [φ]
      _ = 0 := by
        rw [hφ2]
        simp
  exact root_mod2_ne_zero hzero

/-- Show that $\mathbb{Z}[X]/(x^2+4)$ is not integrally closed. -/
theorem not_isIntegrallyClosed_adjoinRoot_pow_two_add_four :
    ¬ IsIntegrallyClosed (AdjoinRoot (X ^ 2 + C 4 : ℤ[X])) := by
  classical
  let A := AdjoinRoot (X ^ 2 + C 4 : ℤ[X])
  let K := FractionRing A
  let a : A := AdjoinRoot.root (X ^ 2 + C 4 : ℤ[X])
  haveI : IsDomain A := AdjoinRoot.isDomain_of_prime (f := (X ^ 2 + C 4 : ℤ[X]))
    prime_X_sq_add_C_four
  haveI : Field K := IsFractionRing.toField (A := A) (K := K)
  -- The defining relation a^2 + 4 = 0 in A, mapped to K.
  have hA : a ^ 2 + (algebraMap ℤ A 4) = 0 := by
    have h := (AdjoinRoot.eval₂_root (f := (X ^ 2 + C 4 : ℤ[X])))
    simpa [a, AdjoinRoot.algebraMap_eq] using h
  have hK : (algebraMap A K a) ^ 2 + algebraMap A K (algebraMap ℤ A 4) = 0 := by
    simpa using congrArg (algebraMap A K) hA
  -- Injectivity of ℤ → A, to show 2 ≠ 0.
  have h_inj : Function.Injective (algebraMap ℤ A) := by
    have hdeg' : (X ^ 2 + C 4 : ℤ[X]).degree = 2 := by
      simpa using (degree_X_pow_add_C (R := ℤ) (n := 2) (a := (4 : ℤ)) (by decide))
    have hdeg : (X ^ 2 + C 4 : ℤ[X]).degree ≠ 0 := by
      intro h
      have h20 : (2 : WithBot ℕ) = 0 := by
        calc
          (2 : WithBot ℕ) = (X ^ 2 + C 4 : ℤ[X]).degree := hdeg'.symm
          _ = 0 := h
      exact (by decide : (2 : WithBot ℕ) ≠ 0) h20
    simpa [AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.of.injective_of_degree_ne_zero (f := (X ^ 2 + C 4 : ℤ[X])) hdeg)
  have h2A : (algebraMap ℤ A 2) ≠ 0 := by
    intro h
    have : (2 : ℤ) = 0 := h_inj (by simpa using h)
    exact (by decide : (2 : ℤ) ≠ 0) this
  let denom : K := algebraMap A K (algebraMap ℤ A 2)
  have h2K : denom ≠ 0 := by
    intro h
    dsimp [denom] at h
    have : (algebraMap ℤ A 2) = 0 := (IsFractionRing.injective A K) (by simpa using h)
    exact h2A this
  let x : K := (algebraMap A K a) / denom
  -- (2^2 = 4) in A, hence in K.
  have h2sqA : (algebraMap ℤ A 2) ^ 2 = (algebraMap ℤ A 4) := by
    norm_num
  have h2sq : denom ^ 2 = algebraMap A K (algebraMap ℤ A 4) := by
    dsimp [denom]
    simpa [map_pow] using congrArg (algebraMap A K) h2sqA
  have h4K : algebraMap A K (algebraMap ℤ A 4) ≠ 0 := by
    intro h4
    have h2sq0 : denom ^ 2 ≠ 0 := pow_ne_zero 2 h2K
    apply h2sq0
    rw [h2sq]
    exact h4
  -- x = a/2 is integral: it is a root of X^2 + 1.
  have hx2 : x ^ 2 = (-1 : K) := by
    have hK' : (algebraMap A K a) ^ 2 = - algebraMap A K (algebraMap ℤ A 4) :=
      eq_neg_of_add_eq_zero_left hK
    calc
      x ^ 2 = (algebraMap A K a) ^ 2 / denom ^ 2 := by
        dsimp [x]
        rw [div_pow]
      _ = -(algebraMap A K (algebraMap ℤ A 4)) / denom ^ 2 := by
        rw [hK']
      _ = -(algebraMap A K (algebraMap ℤ A 4)) /
            (algebraMap A K (algebraMap ℤ A 4)) := by
        rw [h2sq]
      _ = (-1 : K) := by
        exact neg_div_self h4K
  have hx : IsIntegral A x := by
    refine ⟨X ^ 2 + C 1, monic_X_pow_add_C (a := (1 : A)) (n := 2) (by decide), ?_⟩
    have hx' : x ^ 2 + 1 = (0 : K) := by
      calc
        x ^ 2 + 1 = (-1 : K) + 1 := by rw [hx2]
        _ = 0 := by norm_num
    -- Evaluate the polynomial.
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X] using hx'
  -- If A were integrally closed, x would come from A, forcing a = 2*y.
  intro h
  haveI : IsIntegrallyClosed A := h
  obtain ⟨y, hy⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := K) (x := x) hx
  have hy' : algebraMap A K y * denom = algebraMap A K a :=
    (eq_div_iff h2K).1 (by simpa [x] using hy)
  have hyA : a = (algebraMap ℤ A 2) * y := by
    have hmap : algebraMap A K ((algebraMap ℤ A 2) * y) = algebraMap A K a := by
      calc
        algebraMap A K ((algebraMap ℤ A 2) * y)
            = algebraMap A K (algebraMap ℤ A 2) * algebraMap A K y := by simp
        _ = algebraMap A K y * denom := by simp [denom, mul_comm]
        _ = algebraMap A K a := hy'
    exact (IsFractionRing.injective A K) hmap |>.symm
  exact root_not_two_mul ⟨y, hyA⟩

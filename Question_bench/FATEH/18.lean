import Mathlib

open MvPolynomial

/- Prove that \( x^2 + y^2 - 1 \) is irreducible in \( \mathbb{Q}[x, y] \).-/
/-- A monic quadratic `X^2 + C a` over a commutative ring is irreducible if its constant term
is not the negative of a square. -/
lemma irreducible_X_sq_add_C_of_forall_ne_neg_sq {R : Type} [CommRing R] [IsDomain R] (a : R)
    (h : ∀ c : R, a ≠ -(c ^ 2)) :
    Irreducible (((Polynomial.X : Polynomial R) ^ 2) + Polynomial.C a) := by
  classical
  have hm : ((((Polynomial.X : Polynomial R) ^ 2) + Polynomial.C a)).Monic := by
    simpa using (Polynomial.monic_X_pow_add_C a (n := 2) (by decide))
  have hnd : ((((Polynomial.X : Polynomial R) ^ 2) + Polynomial.C a)).natDegree = 2 := by
    simp
  by_contra hIr
  rcases
      (Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff
          (p := ((Polynomial.X : Polynomial R) ^ 2 + Polynomial.C a)) hm hnd).1 hIr with
    ⟨c₁, c₂, h0, h1⟩
  have h1' : c₁ + c₂ = (0 : R) := by
    -- `((X : R[X])^2 + C a).coeff 1 = 0`.
    have h1'' : (0 : R) = c₁ + c₂ := by
      simpa [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow] using h1
    simpa [eq_comm] using h1''
  have hc₂ : c₂ = -c₁ := by
    have : c₂ + c₁ = 0 := by simpa [add_comm] using h1'
    exact eq_neg_of_add_eq_zero_left this
  have ha : a = -(c₁ ^ 2) := by
    have : a = c₁ * c₂ := by
      simpa [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_pow, eq_comm] using h0
    simpa [hc₂, pow_two, mul_assoc, mul_left_comm, mul_comm] using this
  exact (h c₁) ha

/-- In `ℚ[x]`, the polynomial `x^2 - 1` is not the negative of a square.

We prove this by evaluating at `x = 2`, where the left-hand side is `3` but the right-hand side
would be non-positive. -/
lemma mvpoly_fin1_X_sq_sub_one_ne_neg_sq (c : MvPolynomial (Fin 1) ℚ) :
    ((X 0 : MvPolynomial (Fin 1) ℚ) ^ 2 - 1) ≠ -(c ^ 2) := by
  intro h
  have h' := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ))) h
  have h'' : (3 : ℚ) = - (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ)) c) ^ 2 := by
    have h''₀ :
        ((2 : ℚ) ^ 2 - 1) = - (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ)) c) ^ 2 := by
      simpa using h'
    simpa [show ((2 : ℚ) ^ 2 - 1) = (3 : ℚ) by norm_num] using h''₀
  have ht : 0 ≤ (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ)) c) ^ 2 := by
    exact sq_nonneg _
  have hneg : - (MvPolynomial.eval (fun _ : Fin 1 => (2 : ℚ)) c) ^ 2 ≤ 0 := by
    exact neg_nonpos.mpr ht
  have : (3 : ℚ) ≤ 0 := by
    simpa [h''] using hneg
  linarith

theorem irreducible_pow_two_add_pow_two_sub_one :
    Irreducible ((X 0) ^ 2 + (X 1) ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) := by
  classical
  let e := MvPolynomial.finSuccEquiv ℚ 1
  refine (MulEquiv.irreducible_iff e).1 ?_
  -- Under `finSuccEquiv`, this becomes the monic quadratic `X^2 + C ((X 0)^2 - 1)`
  -- over `MvPolynomial (Fin 1) ℚ`.
  have hx0 :
      e (X (0 : Fin 2)) = (Polynomial.X : Polynomial (MvPolynomial (Fin 1) ℚ)) := by
    simpa [e] using (MvPolynomial.finSuccEquiv_X_zero (R := ℚ) (n := 1))
  have hx1 :
      e (X (1 : Fin 2)) =
        (Polynomial.C (X (0 : Fin 1)) : Polynomial (MvPolynomial (Fin 1) ℚ)) := by
    simpa [e] using (MvPolynomial.finSuccEquiv_X_succ (R := ℚ) (n := 1) (j := (0 : Fin 1)))
  have hirr₀ :
      Irreducible
        (Polynomial.X ^ 2 +
          Polynomial.C ((X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ^ 2 - 1)) := by
    exact
      (irreducible_X_sq_add_C_of_forall_ne_neg_sq
        (R := MvPolynomial (Fin 1) ℚ)
        ((X 0 : MvPolynomial (Fin 1) ℚ) ^ 2 - 1)
        (by
          intro c
          exact mvpoly_fin1_X_sq_sub_one_ne_neg_sq c))
  have hC :
      Polynomial.C ((X (0 : Fin 1) : MvPolynomial (Fin 1) ℚ) ^ 2 - 1) =
        ((Polynomial.C (X (0 : Fin 1)) : Polynomial (MvPolynomial (Fin 1) ℚ)) ^ 2 + -1) := by
    simp [sub_eq_add_neg, Polynomial.C_add, Polynomial.C_neg, Polynomial.C_pow]
  have hirr₁ :
      Irreducible
        (Polynomial.X ^ 2 +
          ((Polynomial.C (X (0 : Fin 1)) : Polynomial (MvPolynomial (Fin 1) ℚ)) ^ 2 + -1)) := by
    simpa [hC] using hirr₀
  simpa [hx0, hx1, sub_eq_add_neg, add_assoc] using hirr₁

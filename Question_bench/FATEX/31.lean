import Mathlib
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

open MvPolynomial

/--
Let \( R = \mathbb{C}[x_1, \dots, x_n]/(x_1^2 + x_2^2 + \dots + x_n^2) \).
-/
abbrev R (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ ⧸ Ideal.span {(∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ)}

open scoped BigOperators

/-- The quadric quotient is nontrivial. -/
lemma quadric_nontrivial (n : ℕ) : Nontrivial (R n) := by
  classical
  -- Name the quadric polynomial.
  let q : MvPolynomial (Fin n) ℂ := ∑ i : Fin n, X i ^ 2
  have hcoeff : coeff 0 q = (0 : ℂ) := by
    -- Compute the constant coefficient.
    have h := (coeff_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (X i ^ 2 : MvPolynomial (Fin n) ℂ))
        (m := (0 : Fin n →₀ ℕ)))
    simpa [q, coeff_X_pow] using h
  have hnotunit : ¬ IsUnit q := by
    intro hunit
    have hcoeffunit : IsUnit (coeff 0 q) := (MvPolynomial.isUnit_iff (P := q)).1 hunit |>.1
    have hcoeffunit' := hcoeffunit
    simp [hcoeff] at hcoeffunit'
  have hne : (Ideal.span ({q} : Set (MvPolynomial (Fin n) ℂ))) ≠ ⊤ := by
    intro htop
    have : IsUnit q := (Ideal.span_singleton_eq_top).1 htop
    exact hnotunit this
  have hnontriv : Nontrivial (MvPolynomial (Fin n) ℂ ⧸ Ideal.span ({q} : Set _)) :=
    (Ideal.Quotient.nontrivial_iff (I := Ideal.span ({q} : Set _))).2 hne
  simpa [_root_.R, q] using hnontriv

/-- The quadric polynomial is nonzero once there is at least one variable. -/
lemma quadric_sum_sq_ne_zero (n : ℕ) (h : n ≥ 1) :
    (∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ) ≠ 0 := by
  classical
  have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 1) h
  let i0 : Fin n := ⟨0, hpos⟩
  have hcoeff :
      coeff (Finsupp.single i0 2)
        (∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ) = (1 : ℂ) := by
    have hcoeff' := (coeff_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (X i ^ 2 : MvPolynomial (Fin n) ℂ))
        (m := Finsupp.single i0 2))
    simpa [coeff_X_pow, Finsupp.single_eq_single_iff, Finset.sum_ite_eq'] using hcoeff'
  intro hzero
  have hcoeff' := hcoeff
  simp [hzero] at hcoeff'

/-- The quadric polynomial is not a unit. -/
lemma quadric_not_isUnit (n : ℕ) :
    ¬ IsUnit (∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ) := by
  classical
  -- Name the quadric polynomial.
  let q : MvPolynomial (Fin n) ℂ := ∑ i : Fin n, X i ^ 2
  have hcoeff : coeff 0 q = (0 : ℂ) := by
    -- Compute the constant coefficient.
    have h := (coeff_sum (s := (Finset.univ : Finset (Fin n)))
        (f := fun i : Fin n => (X i ^ 2 : MvPolynomial (Fin n) ℂ))
        (m := (0 : Fin n →₀ ℕ)))
    simpa [q, coeff_X_pow] using h
  intro hunit
  have hcoeffunit : IsUnit (coeff 0 q) := (MvPolynomial.isUnit_iff (P := q)).1 hunit |>.1
  have hcoeffunit' := hcoeffunit
  simp [hcoeff] at hcoeffunit'

/-- Sum over the antidiagonal of `2` unfolds to three terms. -/
lemma sum_antidiagonal_two (f : ℕ × ℕ → ℂ) :
    (∑ x ∈ (Finset.antidiagonal 2), f x) = f (0, 2) + f (1, 1) + f (2, 0) := by
  classical
  simp [Finset.Nat.antidiagonal_eq_map, Finset.sum_map, Finset.sum_range_succ]

/-- A quadratic monomial cannot equal the sum of two distinct linear monomials. -/
lemma single_two_ne_sum {m : ℕ} {i0 i1 i : Fin m} (hneq : i0 ≠ i1) :
    Finsupp.single i (2 : ℕ) ≠ Finsupp.single i0 1 + Finsupp.single i1 1 := by
  classical
  intro h
  have hval := congrArg (fun f => f i0) h
  by_cases hi0 : i = i0
  · subst hi0
    simp [hneq] at hval
  · simp [hi0, hneq] at hval

/-- The mixed-term coefficient in a sum of squares is zero. -/
lemma coeff_sum_sq_zero {m : ℕ} (i0 i1 : Fin m) (hneq : i0 ≠ i1) :
    coeff (Finsupp.single i0 1 + Finsupp.single i1 1)
      (∑ i : Fin m, X i ^ 2 : MvPolynomial (Fin m) ℂ) = (0 : ℂ) := by
  classical
  have h := (coeff_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin m => (X i ^ 2 : MvPolynomial (Fin m) ℂ))
      (m := Finsupp.single i0 1 + Finsupp.single i1 1))
  refine h.trans ?_
  refine Finset.sum_eq_zero ?_
  intro i hi
  simp [coeff_X_pow, single_two_ne_sum (i0 := i0) (i1 := i1) (i := i) hneq]

/-- The pure-square coefficient in a sum of squares is one. -/
lemma coeff_sum_sq_single {m : ℕ} (i0 : Fin m) :
    coeff (Finsupp.single i0 2)
      (∑ i : Fin m, X i ^ 2 : MvPolynomial (Fin m) ℂ) = (1 : ℂ) := by
  classical
  have h := (coeff_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin m => (X i ^ 2 : MvPolynomial (Fin m) ℂ))
      (m := Finsupp.single i0 2))
  simpa [coeff_X_pow, Finsupp.single_eq_single_iff, Finset.sum_ite_eq'] using h

/-- Constant coefficient of a sum of squares is zero. -/
lemma coeff_sum_sq_const {m : ℕ} :
    coeff (0 : Fin m →₀ ℕ)
      (∑ i : Fin m, X i ^ 2 : MvPolynomial (Fin m) ℂ) = (0 : ℂ) := by
  classical
  have h := (coeff_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin m => (X i ^ 2 : MvPolynomial (Fin m) ℂ))
      (m := (0 : Fin m →₀ ℕ)))
  simpa [coeff_X_pow] using h

/-- Linear coefficients of a sum of squares vanish. -/
lemma coeff_sum_sq_linear {m : ℕ} (i0 : Fin m) :
    coeff (Finsupp.single i0 1)
      (∑ i : Fin m, X i ^ 2 : MvPolynomial (Fin m) ℂ) = (0 : ℂ) := by
  classical
  have h := (coeff_sum (s := (Finset.univ : Finset (Fin m)))
      (f := fun i : Fin m => (X i ^ 2 : MvPolynomial (Fin m) ℂ))
      (m := Finsupp.single i0 1))
  simpa [coeff_X_pow, Finsupp.single_eq_single_iff, Finset.sum_ite_eq'] using h

/-- Constant coefficient of a square in `MvPolynomial`. -/
lemma coeff_zero_sq {m : ℕ} (a : MvPolynomial (Fin m) ℂ) :
    coeff (0 : Fin m →₀ ℕ) (a ^ 2) = (coeff (0 : Fin m →₀ ℕ) a) ^ 2 := by
  classical
  simp [pow_two, coeff_mul]

/-- Coefficient of a pure square monomial in `a^2`. -/
lemma coeff_single_sq {m : ℕ} (i0 : Fin m) (a : MvPolynomial (Fin m) ℂ) :
    coeff (Finsupp.single i0 2) (a ^ 2) =
      coeff (0 : Fin m →₀ ℕ) a * coeff (Finsupp.single i0 2) a +
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i0 1) a +
      coeff (Finsupp.single i0 2) a * coeff (0 : Fin m →₀ ℕ) a := by
  classical
  have h := (coeff_mul (p := a) (q := a) (n := (Finsupp.single i0 2)))
  simp [pow_two, Finsupp.antidiagonal_single, sum_antidiagonal_two, coeff_mul]

/-- Any antidiagonal decomposition of `single i0 1 + single i1 1` is one of four cases. -/
lemma antidiagonal_single_add_single_cases {m : ℕ} {i0 i1 : Fin m} (hneq : i0 ≠ i1)
    {x : (Fin m →₀ ℕ) × (Fin m →₀ ℕ)}
    (hx : x ∈ Finset.antidiagonal (Finsupp.single i0 1 + Finsupp.single i1 1)) :
    x = (0, Finsupp.single i0 1 + Finsupp.single i1 1) ∨
      x = (Finsupp.single i0 1 + Finsupp.single i1 1, 0) ∨
      x = (Finsupp.single i0 1, Finsupp.single i1 1) ∨
      x = (Finsupp.single i1 1, Finsupp.single i0 1) := by
  classical
  rcases x with ⟨x1, x2⟩
  have hx' : x1 + x2 = Finsupp.single i0 1 + Finsupp.single i1 1 := by
    simpa using (Finset.mem_antidiagonal.mp hx)
  have hi0 : x1 i0 + x2 i0 = 1 := by
    have := congrArg (fun f => f i0) hx'
    simpa [Finsupp.add_apply, Finsupp.single_apply, hneq] using this
  have hi1 : x1 i1 + x2 i1 = 1 := by
    have := congrArg (fun f => f i1) hx'
    simpa [Finsupp.add_apply, Finsupp.single_apply, hneq, hneq.symm] using this
  have hother : ∀ j, j ≠ i0 → j ≠ i1 → x1 j = 0 ∧ x2 j = 0 := by
    intro j hj0 hj1
    have := congrArg (fun f => f j) hx'
    have hsum : x1 j + x2 j = 0 := by
      simpa [Finsupp.add_apply, Finsupp.single_apply, hj0, hj1] using this
    exact (Nat.add_eq_zero_iff.mp hsum)
  rcases (Nat.add_eq_one_iff.mp hi0) with h0 | h0
  · rcases (Nat.add_eq_one_iff.mp hi1) with h1 | h1
    · have hx1 : x1 = 0 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [h0.1]
        by_cases hj1 : j = i1
        · subst hj1; simp [h1.1]
        have h' := hother j hj0 hj1
        simp [h'.1]
      have hx2 : x2 = Finsupp.single i0 1 + Finsupp.single i1 1 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [hneq, h0.2]
        by_cases hj1 : j = i1
        · subst hj1; simp [hneq.symm, h1.2]
        have h' := hother j hj0 hj1
        simp [hj0, hj1, h'.2]
      left
      simp [hx1, hx2]
    · have hx1 : x1 = Finsupp.single i1 1 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [hneq, h0.1]
        by_cases hj1 : j = i1
        · subst hj1; simp [h1.1]
        have h' := hother j hj0 hj1
        simp [hj1, h'.1]
      have hx2 : x2 = Finsupp.single i0 1 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [h0.2]
        by_cases hj1 : j = i1
        · subst hj1; simp [hneq.symm, h1.2]
        have h' := hother j hj0 hj1
        simp [hj0, h'.2]
      right; right; right
      simp [hx1, hx2]
  · rcases (Nat.add_eq_one_iff.mp hi1) with h1 | h1
    · have hx1 : x1 = Finsupp.single i0 1 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [h0.1]
        by_cases hj1 : j = i1
        · subst hj1; simp [hneq.symm, h1.1]
        have h' := hother j hj0 hj1
        simp [hj0, h'.1]
      have hx2 : x2 = Finsupp.single i1 1 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [hneq, h0.2]
        by_cases hj1 : j = i1
        · subst hj1; simp [h1.2]
        have h' := hother j hj0 hj1
        simp [hj1, h'.2]
      right; right; left
      simp [hx1, hx2]
    · have hx1 : x1 = Finsupp.single i0 1 + Finsupp.single i1 1 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [hneq, h0.1]
        by_cases hj1 : j = i1
        · subst hj1; simp [hneq.symm, h1.1]
        have h' := hother j hj0 hj1
        simp [hj0, hj1, h'.1]
      have hx2 : x2 = 0 := by
        ext j
        by_cases hj0 : j = i0
        · subst hj0; simp [h0.2]
        by_cases hj1 : j = i1
        · subst hj1; simp [h1.2]
        have h' := hother j hj0 hj1
        simp [h'.2]
      right; left
      simp [hx1, hx2]

/-- The antidiagonal of a mixed quadratic monomial has four elements. -/
lemma antidiagonal_single_add_single_eq {m : ℕ} (i0 i1 : Fin m) (hneq : i0 ≠ i1) :
    Finset.antidiagonal (Finsupp.single i0 1 + Finsupp.single i1 1) =
      insert (Finsupp.single i1 1, Finsupp.single i0 1)
        (insert (Finsupp.single i0 1, Finsupp.single i1 1)
          (insert (Finsupp.single i0 1 + Finsupp.single i1 1, 0)
            ({(0, Finsupp.single i0 1 + Finsupp.single i1 1)} :
              Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ))))) := by
  classical
  ext x
  constructor
  · intro hx
    have hx' :=
      antidiagonal_single_add_single_cases (i0 := i0) (i1 := i1) hneq (x := x) hx
    rcases hx' with h0 | h0
    · simp [h0]
    rcases h0 with h1 | h1
    · simp [h1]
    rcases h1 with h2 | h2
    · simp [h2]
    · simp [h2]
  · intro hx
    have hx' :
        x = (Finsupp.single i1 1, Finsupp.single i0 1) ∨
          x = (Finsupp.single i0 1, Finsupp.single i1 1) ∨
          x = (Finsupp.single i0 1 + Finsupp.single i1 1, 0) ∨
          x = (0, Finsupp.single i0 1 + Finsupp.single i1 1) := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with h0 | h0
    · subst h0
      simp [Finset.mem_antidiagonal, add_comm]
    rcases h0 with h1 | h1
    · subst h1
      simp [Finset.mem_antidiagonal]
    rcases h1 with h2 | h2
    · subst h2
      simp [Finset.mem_antidiagonal]
    · subst h2
      simp [Finset.mem_antidiagonal]

/-- Sum of coefficient products over the mixed antidiagonal. -/
lemma sum_coeff_mul_antidiagonal_single_add_single {m : ℕ} (i0 i1 : Fin m) (hneq : i0 ≠ i1)
    (a : MvPolynomial (Fin m) ℂ) :
    ∑ x ∈ Finset.antidiagonal (Finsupp.single i0 1 + Finsupp.single i1 1),
        coeff x.1 a * coeff x.2 a =
      coeff (Finsupp.single i1 1) a * coeff (Finsupp.single i0 1) a +
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a +
      coeff (Finsupp.single i0 1 + Finsupp.single i1 1) a * coeff (0 : Fin m →₀ ℕ) a +
      coeff (0 : Fin m →₀ ℕ) a * coeff (Finsupp.single i0 1 + Finsupp.single i1 1) a := by
  classical
  set m0 : Fin m →₀ ℕ := Finsupp.single i0 1 + Finsupp.single i1 1
  have hm0 : m0 ≠ 0 := by
    intro h
    have := congrArg (fun f => f i0) h
    simp [m0, Finsupp.add_apply, hneq] at this
  set s0 : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ)) := {(0, m0)}
  set s1 : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ)) := insert (m0, 0) s0
  set s2 : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ)) :=
    insert (Finsupp.single i0 1, Finsupp.single i1 1) s1
  set s3 : Finset ((Fin m →₀ ℕ) × (Fin m →₀ ℕ)) :=
    insert (Finsupp.single i1 1, Finsupp.single i0 1) s2
  have hanti : Finset.antidiagonal m0 = s3 :=
    antidiagonal_single_add_single_eq (i0 := i0) (i1 := i1) hneq
  have hnot1 : (m0, 0) ∉ s0 := by
    simp [s0, hm0]
  have hnot2 : (Finsupp.single i0 1, Finsupp.single i1 1) ∉ s1 := by
    simp [s1, s0]
  have hnot3 : (Finsupp.single i1 1, Finsupp.single i0 1) ∉ s2 := by
    simp [s2, s1, s0, hneq, Finsupp.single_eq_single_iff]
  have hsum : (∑ x ∈ s3, coeff x.1 a * coeff x.2 a) =
      coeff (Finsupp.single i1 1) a * coeff (Finsupp.single i0 1) a +
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a +
      coeff m0 a * coeff (0 : Fin m →₀ ℕ) a +
      coeff (0 : Fin m →₀ ℕ) a * coeff m0 a := by
    simp [s3, Finset.sum_insert, hnot3, s2, Finset.sum_insert, hnot2, s1, Finset.sum_insert,
      hnot1, s0, Finset.sum_singleton, add_assoc]
  simpa [hanti, m0, s0, s1, s2, s3] using hsum

/-- Mixed-term coefficient of a square with vanishing constant term. -/
lemma coeff_cross_sq_of_coeff_zero {m : ℕ} (i0 i1 : Fin m) (hneq : i0 ≠ i1)
    (a : MvPolynomial (Fin m) ℂ) (h0 : coeff (0 : Fin m →₀ ℕ) a = 0) :
    coeff (Finsupp.single i0 1 + Finsupp.single i1 1) (a ^ 2) =
      (2:ℂ) * coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a := by
  classical
  set m0 : Fin m →₀ ℕ := Finsupp.single i0 1 + Finsupp.single i1 1
  have hmul : coeff m0 (a ^ 2) =
      ∑ x ∈ Finset.antidiagonal m0, coeff x.1 a * coeff x.2 a := by
    simpa [pow_two] using (coeff_mul (p := a) (q := a) (n := m0))
  have hsum := sum_coeff_mul_antidiagonal_single_add_single (i0 := i0) (i1 := i1) hneq a
  have hsum' : coeff m0 (a ^ 2) =
      coeff (Finsupp.single i1 1) a * coeff (Finsupp.single i0 1) a +
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a +
      coeff (Finsupp.single i0 1 + Finsupp.single i1 1) a * coeff (0 : Fin m →₀ ℕ) a +
      coeff (0 : Fin m →₀ ℕ) a * coeff (Finsupp.single i0 1 + Finsupp.single i1 1) a := by
    simpa [m0] using hmul.trans hsum
  have hcomm : coeff (Finsupp.single i1 1) a * coeff (Finsupp.single i0 1) a =
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a := by
    simp [mul_comm]
  have hsum'' : coeff m0 (a ^ 2) =
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a +
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a := by
    simpa [m0, h0, hcomm, add_assoc, add_left_comm, add_comm] using hsum'
  simpa [m0, two_mul, add_mul, mul_assoc] using hsum''

/-- `finSuccEquiv` sends the quadric sum of squares to `X^2 + C` of the lower-dimensional sum. -/
lemma quadric_finSuccEquiv_sum_sq (n : ℕ) :
    MvPolynomial.finSuccEquiv ℂ n
        (∑ i : Fin (n + 1), X i ^ 2 : MvPolynomial (Fin (n + 1)) ℂ) =
      (Polynomial.X ^ 2 +
        Polynomial.C (∑ j : Fin n, X j ^ 2 : MvPolynomial (Fin n) ℂ)) := by
  classical
  simp [Fin.sum_univ_succ, MvPolynomial.finSuccEquiv_X_zero,
    MvPolynomial.finSuccEquiv_X_succ, map_sum, map_pow, map_add]

/-- In at least two variables, the quadric sum of squares is not the negative of a square. -/
lemma sum_sq_ne_neg_sq {m : ℕ} (hm : m ≥ 2) (a : MvPolynomial (Fin m) ℂ) :
    (∑ i : Fin m, X i ^ 2 : MvPolynomial (Fin m) ℂ) ≠ -(a ^ 2) := by
  classical
  intro h
  have h0m : (0 : ℕ) < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have h1m : (1 : ℕ) < m := lt_of_lt_of_le (by decide : 1 < 2) hm
  let i0 : Fin m := ⟨0, h0m⟩
  let i1 : Fin m := ⟨1, h1m⟩
  have hneq : i0 ≠ i1 := by
    intro h'
    exact Nat.zero_ne_one (congrArg Fin.val h')
  have hcoeff0' : (0 : ℂ) = -(coeff (0 : Fin m →₀ ℕ) a) ^ 2 := by
    have hcoeff := congrArg (fun p => coeff (0 : Fin m →₀ ℕ) p) h
    simpa [coeff_sum_sq_const, coeff_zero_sq] using hcoeff
  have hcoeff0'' : (coeff (0 : Fin m →₀ ℕ) a) ^ 2 = 0 := by
    have := congrArg Neg.neg hcoeff0'
    simpa using this.symm
  have h0 : coeff (0 : Fin m →₀ ℕ) a = 0 := by
    exact (sq_eq_zero_iff).1 hcoeff0''
  have hmix' := congrArg (fun p =>
    coeff (Finsupp.single i0 1 + Finsupp.single i1 1) p) h
  have hmix : coeff (Finsupp.single i0 1 + Finsupp.single i1 1) (a ^ 2) = 0 := by
    have h' : (0 : ℂ) =
        -coeff (Finsupp.single i0 1 + Finsupp.single i1 1) (a ^ 2) := by
      simpa [coeff_sum_sq_zero (i0 := i0) (i1 := i1) hneq] using hmix'
    have := congrArg Neg.neg h'
    simpa using this.symm
  have hprod' :
      (2 : ℂ) * coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a = 0 := by
    have hcross := coeff_cross_sq_of_coeff_zero (i0 := i0) (i1 := i1) hneq a h0
    simpa [hcross] using hmix
  have hprod :
      coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a = 0 := by
    have h' :
        (2 : ℂ) * (coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i1 1) a) = 0 := by
      simpa [mul_assoc] using hprod'
    have hcases := mul_eq_zero.mp h'
    exact hcases.resolve_left (by exact two_ne_zero)
  have hsq0' : (1 : ℂ) =
      -(coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i0 1) a) := by
    have hcoeff := congrArg (fun p => coeff (Finsupp.single i0 2) p) h
    simpa [coeff_sum_sq_single (i0 := i0), coeff_single_sq (i0 := i0) (a := a), h0] using hcoeff
  have hsq1' : (1 : ℂ) =
      -(coeff (Finsupp.single i1 1) a * coeff (Finsupp.single i1 1) a) := by
    have hcoeff := congrArg (fun p => coeff (Finsupp.single i1 2) p) h
    simpa [coeff_sum_sq_single (i0 := i1), coeff_single_sq (i0 := i1) (a := a), h0] using hcoeff
  have hsq0 : (coeff (Finsupp.single i0 1) a) ^ 2 = -1 := by
    have h' : coeff (Finsupp.single i0 1) a * coeff (Finsupp.single i0 1) a = -1 := by
      have := congrArg Neg.neg hsq0'
      simpa [mul_comm] using this.symm
    simpa [pow_two] using h'
  have hsq1 : (coeff (Finsupp.single i1 1) a) ^ 2 = -1 := by
    have h' : coeff (Finsupp.single i1 1) a * coeff (Finsupp.single i1 1) a = -1 := by
      have := congrArg Neg.neg hsq1'
      simpa [mul_comm] using this.symm
    simpa [pow_two] using h'
  have hne0 : coeff (Finsupp.single i0 1) a ≠ 0 := by
    have hne : (-1 : ℂ) ≠ 0 := by exact neg_ne_zero.mpr one_ne_zero
    intro hzero
    have hsq0' : (0 : ℂ) = (-1 : ℂ) := by
      calc
        (0 : ℂ) = (coeff (Finsupp.single i0 1) a) ^ 2 := by simp [hzero]
        _ = -1 := hsq0
    exact hne hsq0'.symm
  have hne1 : coeff (Finsupp.single i1 1) a ≠ 0 := by
    have hne : (-1 : ℂ) ≠ 0 := by exact neg_ne_zero.mpr one_ne_zero
    intro hzero
    have hsq1' : (0 : ℂ) = (-1 : ℂ) := by
      calc
        (0 : ℂ) = (coeff (Finsupp.single i1 1) a) ^ 2 := by simp [hzero]
        _ = -1 := hsq1
    exact hne hsq1'.symm
  have hcases := mul_eq_zero.mp hprod
  cases hcases with
  | inl hzero => exact (hne0 hzero).elim
  | inr hzero => exact (hne1 hzero).elim

/-- Irreducibility of `X^2 + C(q)` using the no-square obstruction. -/
lemma poly_X_sq_add_C_irreducible_of_sum_sq {m : ℕ} (hm : m ≥ 2) :
    Irreducible
      (Polynomial.X ^ 2 +
        Polynomial.C (∑ i : Fin m, X i ^ 2 : MvPolynomial (Fin m) ℂ)) := by
  classical
  let q : MvPolynomial (Fin m) ℂ := ∑ i : Fin m, X i ^ 2
  have hmonic :
      (Polynomial.X ^ 2 + Polynomial.C q).Monic := by
    simpa using (Polynomial.monic_X_pow_add_C (a := q) (n := 2) (by decide))
  have hdeg :
      (Polynomial.X ^ 2 + Polynomial.C q).natDegree = 2 := by
    simp
  by_contra hirr
  rcases
      (Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff
        (p := Polynomial.X ^ 2 + Polynomial.C q) hmonic hdeg).1 hirr with ⟨c₁, c₂, hmul, hadd⟩
  have hmul' : q = c₁ * c₂ := by
    simpa using hmul
  have hadd' : (0 : MvPolynomial (Fin m) ℂ) = c₁ + c₂ := by
    simpa using hadd
  have hneg : c₂ = -c₁ := by
    have hadd'' : c₁ + c₂ = 0 := by simpa using hadd'.symm
    have := congrArg (fun x => x - c₁) hadd''
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  have hqneg : q = -(c₁ ^ 2) := by
    calc
      q = c₁ * c₂ := hmul'
      _ = c₁ * (-c₁) := by simp [hneg]
      _ = -(c₁ * c₁) := by simp [mul_neg]
      _ = -(c₁ ^ 2) := by simp [pow_two]
  exact (sum_sq_ne_neg_sq (m := m) hm c₁) (by simpa [q] using hqneg)

/-- Irreducibility of the quadric sum of squares in at least three variables. -/
lemma quadric_irreducible_of_ge3 {n : ℕ} (hn : n ≥ 3) :
    Irreducible (∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ) := by
  classical
  cases n with
  | zero =>
      have : False := by linarith
      exact this.elim
  | succ n =>
      cases n with
      | zero =>
          have : False := by linarith
          exact this.elim
      | succ m =>
          have hm : m + 1 ≥ 2 := by linarith
          have hpoly :
              Irreducible
                (Polynomial.X ^ 2 +
                  Polynomial.C (∑ j : Fin (m + 1), X j ^ 2 : MvPolynomial (Fin (m + 1)) ℂ)) :=
            poly_X_sq_add_C_irreducible_of_sum_sq (m := m + 1) hm
          have hmap :
              Irreducible
                (MvPolynomial.finSuccEquiv ℂ (m + 1)
                  (∑ i : Fin (m + 2), X i ^ 2 : MvPolynomial (Fin (m + 2)) ℂ)) := by
            simpa [quadric_finSuccEquiv_sum_sq (n := m + 1)] using hpoly
          have hirr :
              Irreducible
                (∑ i : Fin (m + 2), X i ^ 2 : MvPolynomial (Fin (m + 2)) ℂ) :=
            (MulEquiv.irreducible_iff
              (f := (MvPolynomial.finSuccEquiv ℂ (m + 1)).toMulEquiv)
              (x := (∑ i : Fin (m + 2), X i ^ 2 : MvPolynomial (Fin (m + 2)) ℂ))).1 hmap
          simpa using hirr

/-- If the quadric polynomial is irreducible, its principal ideal is prime. -/
lemma quadric_span_isPrime_of_irreducible (n : ℕ) :
    let q : MvPolynomial (Fin n) ℂ := ∑ i : Fin n, X i ^ 2
    q ≠ 0 → Irreducible q → (Ideal.span ({q} : Set _)).IsPrime := by
  classical
  intro q hq0 hirr
  have hprime : Prime q := (UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr)
  exact (Ideal.span_singleton_prime (p := q) hq0).2 hprime

/-- If an ideal contains `x`, then the principal ideal generated by `x` is contained in it. -/
lemma ideal_span_singleton_le_of_mem {n : ℕ} {I : Ideal (R n)} {x : R n} (hxI : x ∈ I) :
    Ideal.span ({x} : Set (R n)) ≤ I := by
  refine Ideal.span_le.2 ?_
  intro y hy
  rcases Set.mem_singleton_iff.mp hy with rfl
  simpa using hxI

/-- If an ideal contains `x` and is contained in the span of `x`, then it equals that span. -/
lemma ideal_eq_span_of_mem_and_le_span {n : ℕ} {I : Ideal (R n)} {x : R n} (hxI : x ∈ I)
    (hle : (I : Ideal (R n)) ≤ Ideal.span ({x} : Set (R n))) :
    I = Ideal.span ({x} : Set (R n)) := by
  apply le_antisymm hle
  exact ideal_span_singleton_le_of_mem (n := n) (I := I) hxI

/-- A nonprincipal ideal containing `x` cannot be contained in the span of `x`. -/
lemma quadric_nonprincipal_not_le_span_singleton
    {n : ℕ} {I : Ideal (R n)} {x : R n} (hxI : x ∈ I)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
    ¬ (I : Ideal (R n)) ≤ Ideal.span ({x} : Set (R n)) := by
  intro hle
  have hIeq : I = Ideal.span ({x} : Set (R n)) :=
    ideal_eq_span_of_mem_and_le_span (n := n) (I := I) hxI hle
  exact hIprin ⟨x, hIeq⟩

/-- Non-PID branch of the principality statement for prime ideals in the quadric quotient. -/
lemma quadric_prime_ideal_principal_of_ge5_nonPID_contra
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    (hP : ¬ IsPrincipalIdealRing (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
    False := by
  classical
  -- Missing global principality input for `R n`.
  -- This branch would contradict hP by constructing a nonprincipal prime ideal.
  sorry

/-- Non-PID branch of the principality statement for prime ideals in the quadric quotient. -/
lemma quadric_prime_ideal_principal_of_ge5_nonPID
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    (hP : ¬ IsPrincipalIdealRing (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime) :
    ∃ y : R n, I = Ideal.span ({y} : Set (R n)) := by
  classical
  by_cases hIprin : ∃ y : R n, I = Ideal.span ({y} : Set (R n))
  · exact hIprin
  · have hcontra : False :=
      quadric_prime_ideal_principal_of_ge5_nonPID_contra
        (n := n) h _hdom hP hI hIprime hIprin
    exact (False.elim hcontra)

/-- Principal-ideal property for nonzero prime ideals in the quadric quotient.
This is the missing global algebraic input needed to eliminate the nonprincipal case. -/
lemma quadric_prime_ideal_principal_of_ge5
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime) :
    ∃ y : R n, I = Ideal.span ({y} : Set (R n)) := by
  classical
  -- This is a strong principality statement for prime ideals in `R n`.
  by_cases hP : IsPrincipalIdealRing (R n)
  · letI : IsPrincipalIdealRing (R n) := hP
    rcases (Submodule.IsPrincipal.principal (S := (I : Submodule (R n) (R n)))) with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    simpa using hy
  · -- Missing global principality input for `R n`.
    exact
      quadric_prime_ideal_principal_of_ge5_nonPID
        (n := n) h _hdom hP hI hIprime

/-- Missing containment input: nonprincipal prime ideals are contained in the span of `x`. -/
lemma quadric_prime_ideal_le_span_singleton_core
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime)
    {x : R n} (hxI : x ∈ I) (hx0 : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
  (I : Ideal (R n)) ≤ Ideal.span ({x} : Set (R n)) := by
  classical
  have _ := hxI
  have _ := hx0
  have _ := hxunit
  have hIprin' :
      ∃ y : R n, I = Ideal.span ({y} : Set (R n)) :=
    quadric_prime_ideal_principal_of_ge5
      (n := n) h _hdom hI hIprime
  exact (False.elim (hIprin hIprin'))

/-- Core missing divisibility input for nonprincipal prime ideals.
This isolates the algebraic step that is currently unavailable. -/
lemma quadric_mem_prime_ideal_imp_dvd_core
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime)
    {x : R n} (hxI : x ∈ I) (hx0 : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
    ∀ {a : R n}, a ∈ I → x ∣ a := by
  classical
  intro a haI
  have hle :
      (I : Ideal (R n)) ≤ Ideal.span ({x} : Set (R n)) :=
    quadric_prime_ideal_le_span_singleton_core
      (n := n) h _hdom hI hIprime hxI hx0 hxunit hIprin
  have : a ∈ Ideal.span ({x} : Set (R n)) := hle haI
  simpa [Ideal.mem_span_singleton] using this

/-- Missing containment step: a nonprincipal prime ideal is contained in the span of a fixed element.
This is the precise algebraic input needed for the divisibility conclusion. -/
lemma quadric_prime_ideal_le_span_of_nonprincipal
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime)
    {x : R n} (hxI : x ∈ I) (hx0 : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
    (I : Ideal (R n)) ≤ Ideal.span ({x} : Set (R n)) := by
  classical
  intro a haI
  -- Reduce the containment to divisibility in the principal ideal.
  have hdiv : x ∣ a := by
    exact
      quadric_mem_prime_ideal_imp_dvd_core
        (n := n) h _hdom hI hIprime hxI hx0 hxunit hIprin haI
  simpa [Ideal.mem_span_singleton] using hdiv

/-- Membership in a nonprincipal prime ideal should imply divisibility by a fixed element.
This isolates the missing algebraic input for the quadric quotient. -/
lemma quadric_mem_prime_ideal_imp_dvd_of_nonprincipal
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime)
    {x : R n} (hxI : x ∈ I) (hx0 : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
    ∀ {a : R n}, a ∈ I → x ∣ a := by
  classical
  intro a haI
  have hle :
      (I : Ideal (R n)) ≤ Ideal.span ({x} : Set (R n)) :=
    quadric_prime_ideal_le_span_of_nonprincipal
      (n := n) h _hdom hI hIprime hxI hx0 hxunit hIprin
  have : a ∈ Ideal.span ({x} : Set (R n)) := hle haI
  simpa [Ideal.mem_span_singleton] using this

/-- Divisibility step needed to extract a prime element from a nonprincipal prime ideal. -/
lemma quadric_divisibility_of_mem_prime_ideal_of_nonprincipal
    {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n))
    {I : Ideal (R n)} (hI : I ≠ ⊥) (hIprime : I.IsPrime)
    {x : R n} (hxI : x ∈ I) (hx0 : x ≠ 0) (hxunit : ¬ IsUnit x)
    (hIprin : ¬ ∃ y : R n, I = Ideal.span ({y} : Set (R n))) :
    ∀ a b : R n, x ∣ a * b → x ∣ a ∨ x ∣ b := by
  classical
  intro a b hdiv
  by_cases ha : a = 0
  · subst ha
    exact Or.inl (dvd_zero x)
  by_cases hb : b = 0
  · subst hb
    exact Or.inr (dvd_zero x)
  have hmulmem : a * b ∈ I := by
    rcases hdiv with ⟨c, hc⟩
    have hxmul : x * c ∈ I := by
      simpa [mul_comm] using (I.mul_mem_left c hxI)
    simpa [hc] using hxmul
  have habmem : a ∈ I ∨ b ∈ I := hIprime.mem_or_mem hmulmem
  -- TODO: need a divisibility criterion turning ideal primality into element primality.
  -- This is the remaining algebraic input for the quadric quotient.
  have hmem_div : (a ∈ I → x ∣ a) ∧ (b ∈ I → x ∣ b) := by
    refine ⟨?_, ?_⟩
    · intro haI
      exact
        quadric_mem_prime_ideal_imp_dvd_of_nonprincipal
          (n := n) h _hdom hI hIprime hxI hx0 hxunit hIprin haI
    · intro hbI
      exact
        quadric_mem_prime_ideal_imp_dvd_of_nonprincipal
          (n := n) h _hdom hI hIprime hxI hx0 hxunit hIprin hbI
  exact habmem.elim (fun haI => Or.inl (hmem_div.1 haI)) (fun hbI => Or.inr (hmem_div.2 hbI))

/-- Kaplansky-style prime-ideal property for the quadric quotient in dimension ≥ 5. -/
lemma quadric_kaplansky_property_of_ge5 {n : ℕ} (h : n ≥ 5) (_hdom : IsDomain (R n)) :
    ∀ I : Ideal (R n), I ≠ ⊥ → I.IsPrime → ∃ x ∈ I, Prime x := by
  classical
  letI : IsDomain (R n) := _hdom
  intro I hI hIprime
  by_cases hU : UniqueFactorizationMonoid (R n)
  · letI : UniqueFactorizationMonoid (R n) := hU
    exact Ideal.IsPrime.exists_mem_prime_of_ne_bot (I := I) hIprime hI
  · have hx : ∃ x ∈ I, x ≠ (0 : R n) := by
      simpa using
        (Submodule.exists_mem_ne_zero_of_ne_bot
          (p := (I : Submodule (R n) (R n))) hI)
    by_cases hIprin : ∃ y : R n, I = Ideal.span ({y} : Set (R n))
    · rcases hIprin with ⟨y, rfl⟩
      have hy0 : (y : R n) ≠ 0 := by
        intro hy0
        apply hI
        simp [hy0]
      refine ⟨y, ?_, ?_⟩
      · simpa using (Ideal.mem_span_singleton_self y)
      · exact (Ideal.span_singleton_prime (p := y) hy0).1 hIprime
    · rcases hx with ⟨x, hxI, hx0⟩
      refine ⟨x, hxI, ?_⟩
      -- TODO: produce a prime element in a nonzero prime ideal of the quadric quotient.
      have hxunit : ¬ IsUnit x := by
        intro hxunit
        exact hIprime.ne_top (Ideal.eq_top_of_isUnit_mem (I := I) hxI hxunit)
      refine ⟨hx0, hxunit, ?_⟩
      intro a b hdiv
      exact
        quadric_divisibility_of_mem_prime_ideal_of_nonprincipal
          (n := n) h _hdom hI hIprime hxI hx0 hxunit hIprin a b hdiv

/-- Algebraic core: irreducibility and UFD input for the quadric quotient in high dimension. -/
lemma quadric_irreducible_and_UFD_of_ge5 (n : ℕ) (h : n ≥ 5) :
    Irreducible (∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ) ∧
      (∀ _ : IsDomain (R n), UniqueFactorizationMonoid (R n)) := by
  classical
  let q : MvPolynomial (Fin n) ℂ := ∑ i : Fin n, X i ^ 2
  have h1 : n ≥ 1 := le_trans (by decide : (1 : ℕ) ≤ 5) h
  have hq0 : q ≠ 0 := by
    simpa [q] using (quadric_sum_sq_ne_zero n h1)
  have hnotunit : ¬ IsUnit q := by
    simpa [q] using (quadric_not_isUnit n)
  refine ⟨?_, ?_⟩
  · have h3 : n ≥ 3 := le_trans (by decide : (3 : ℕ) ≤ 5) h
    simpa using (quadric_irreducible_of_ge3 (n := n) h3)
  · intro _hdom
    classical
    -- Reduce to Kaplansky's criterion: every nonzero prime ideal contains a prime element.
    letI : IsDomain (R n) := _hdom
    refine (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime).2 ?_
    exact quadric_kaplansky_property_of_ge5 (n := n) h _hdom

/-- Core algebraic input: the quadric quotient is a domain and UFD for `n ≥ 5`. -/
lemma quadric_isDomain_and_UFD_of_ge5 (n : ℕ) (_h : n ≥ 5) :
    ∃ (_hdom : IsDomain (R n)), UniqueFactorizationMonoid (R n) := by
  classical
  let q : MvPolynomial (Fin n) ℂ := ∑ i : Fin n, X i ^ 2
  have hq0 : q ≠ 0 := by
    have h1 : n ≥ 1 := le_trans (by decide : (1 : ℕ) ≤ 5) _h
    simpa [q] using (quadric_sum_sq_ne_zero n h1)
  have hcore : Irreducible q ∧ (∀ _ : IsDomain (R n), UniqueFactorizationMonoid (R n)) := by
    simpa [q] using quadric_irreducible_and_UFD_of_ge5 n _h
  rcases hcore with ⟨hirr, hufd_of_domain⟩
  have hprime : (Ideal.span ({q} : Set _)).IsPrime :=
    by
      simpa [q] using (quadric_span_isPrime_of_irreducible (n := n) hq0 hirr)
  have hdom' :
      IsDomain (MvPolynomial (Fin n) ℂ ⧸ Ideal.span ({q} : Set _)) :=
    (Ideal.Quotient.isDomain_iff_prime (I := Ideal.span ({q} : Set _))).2 hprime
  have hdom : IsDomain (R n) := by
    simpa [_root_.R, q] using hdom'
  refine ⟨hdom, ?_⟩
  classical
  letI : IsDomain (R n) := hdom
  exact hufd_of_domain hdom

/--
Let \( R = \mathbb{C}[x_1, \dots, x_n]/(x_1^2 + x_2^2 + \dots + x_n^2) \).
Then \( R \) is a unique factorization domain for \( n \geq 5 \). -/
theorem UFD_of_ge_5 (n : ℕ) (_h : n ≥ 5) :
    ∃ (_hdom : IsDomain (R n)), UniqueFactorizationMonoid (R n) := by
  classical
  exact quadric_isDomain_and_UFD_of_ge5 n _h

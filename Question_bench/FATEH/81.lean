import Mathlib

open MvPolynomial
/--
Let \( R = \mathbb{C}[x_1, \dots, x_n]/(x_1^2 + x_2^2 + \dots + x_n^2) \).
-/
abbrev R (n : ℕ) : Type :=
  MvPolynomial (Fin n) ℂ ⧸ Ideal.span {(∑ i : Fin n, X i ^ 2 : MvPolynomial (Fin n) ℂ)}

namespace Quadric

noncomputable section

open scoped BigOperators

private abbrev R3 : Type := R 3

private abbrev q3 : MvPolynomial (Fin 3) ℂ :=
  ∑ i : Fin 3, X i ^ 2

private abbrev I3 : Ideal (MvPolynomial (Fin 3) ℂ) :=
  Ideal.span ({q3} : Set (MvPolynomial (Fin 3) ℂ))

private abbrev x3 (i : Fin 3) : R3 :=
  Ideal.Quotient.mk I3 (X i)

private abbrev I3c (z : ℂ) : R3 :=
  Ideal.Quotient.mk I3 (C z)

private abbrev u3 : R3 :=
  x3 0 + I3c Complex.I * x3 1

private abbrev v3 : R3 :=
  x3 0 - I3c Complex.I * x3 1

private lemma quadric_relation_R3 :
    (x3 0) ^ 2 + (x3 1) ^ 2 + (x3 2) ^ 2 = 0 := by
  have hq : (Ideal.Quotient.mk I3 q3 : R3) = 0 := by
    simpa [I3] using (Ideal.Quotient.mk_singleton_self q3)
  have hq' : (∑ i : Fin 3, (x3 i) ^ 2 : R3) = 0 := by
    simpa [q3, x3] using hq
  simpa [Fin.sum_univ_three] using hq'

private lemma u3_dvd_x3_2_sq : u3 ∣ (x3 2) ^ 2 := by
  have hrel : (x3 0) ^ 2 + (x3 1) ^ 2 = -((x3 2) ^ 2) := by
    have h := quadric_relation_R3
    -- rewrite `(x0^2 + x1^2) + x2^2 = 0`
    have h' : ((x3 0) ^ 2 + (x3 1) ^ 2) + (x3 2) ^ 2 = 0 := by
      simpa [add_assoc] using h
    exact eq_neg_of_add_eq_zero_left h'
  have hI2 : (I3c Complex.I : R3) * I3c Complex.I = (-1 : R3) := by
    calc
      (I3c Complex.I : R3) * I3c Complex.I =
          (Ideal.Quotient.mk I3 ((C Complex.I : MvPolynomial (Fin 3) ℂ) * C Complex.I) : R3) := by
            simp [I3c]
      _ = (Ideal.Quotient.mk I3 (C (Complex.I * Complex.I)) : R3) := by
        -- rewrite `C a * C b` as `C (a * b)`
        have hC :
            (C Complex.I : MvPolynomial (Fin 3) ℂ) * C Complex.I = C (Complex.I * Complex.I) := by
          simpa using
            (MvPolynomial.C_mul (σ := Fin 3) (a := Complex.I) (a' := Complex.I)).symm
        simp [hC]
      _ = (-1 : R3) := by
        simp [Complex.I_mul_I]
  set i : R3 := I3c Complex.I
  have hi2 : i * i = (-1 : R3) := by simpa [i] using hI2
  have hi2' : i ^ 2 = (-1 : R3) := by simp [pow_two, hi2]
  have huv : u3 * v3 = (x3 0) ^ 2 + (x3 1) ^ 2 := by
    -- Expand and use `i^2 = -1`.
    calc
      u3 * v3 = (x3 0 + i * x3 1) * (x3 0 - i * x3 1) := by simp [u3, v3, i]
      _ = (x3 0) ^ 2 - (i ^ 2) * (x3 1) ^ 2 := by
        ring
      _ = (x3 0) ^ 2 + (x3 1) ^ 2 := by simp [hi2', sub_eq_add_neg]
  refine ⟨-v3, ?_⟩
  -- `x2^2 = u * (-v)` using the quadric relation.
  have h' : u3 * v3 = -((x3 2) ^ 2) := by simpa [huv] using hrel
  have h'' : -(u3 * v3) = (x3 2) ^ 2 := by
    simpa using congrArg Neg.neg h'
  have hmul : -(u3 * v3) = u3 * (-v3) := (mul_neg u3 v3).symm
  simpa [hmul] using h''.symm

private lemma u3_not_dvd_x3_2 : ¬ u3 ∣ x3 2 := by
  classical
  -- Map `R3` to `ℂ[x]/(x^2)` by sending `x0,x1 ↦ 0` and `x2 ↦ x`.
  let S1 : Type := MvPolynomial (Fin 1) ℂ
  let x : S1 := X 0
  let J : Ideal S1 := Ideal.span ({x ^ 2} : Set S1)
  let T : Type := S1 ⧸ J
  let evalS : MvPolynomial (Fin 3) ℂ →+* T :=
    MvPolynomial.eval₂Hom (algebraMap ℂ T) (fun i : Fin 3 =>
      match (i : Fin 3) with
      | 0 => 0
      | 1 => 0
      | 2 => Ideal.Quotient.mk J x)
  have hq : evalS q3 = 0 := by
    -- Only the `x2^2` term survives, and it is zero in `T`.
    have hx2 : (Ideal.Quotient.mk J (x ^ 2) : T) = 0 := by
      simp [J]
    have hx2' : (Ideal.Quotient.mk J x : T) ^ 2 = 0 := by
      -- `x^2 = 0` in `T`.
      have hmap : (Ideal.Quotient.mk J (x ^ 2) : T) = (Ideal.Quotient.mk J x : T) ^ 2 := by
        exact (Ideal.Quotient.mk J).map_pow x 2
      simpa [hmap] using hx2
    -- Expand the sum over `Fin 3`.
    simp [q3, evalS, Fin.sum_univ_three, hx2', x, J]
  let φ : R3 →+* T :=
    Ideal.Quotient.lift I3 evalS <| by
      intro a ha
      rcases (Ideal.mem_span_singleton'.1 ha) with ⟨t, rfl⟩
      simp [map_mul, hq]
  have hφu : φ u3 = 0 := by
    simp [φ, u3, x3, I3c, evalS]
  have hφx2 : φ (x3 2) ≠ 0 := by
    -- If `x = 0` in the quotient by `(x^2)`, then `x^2 ∣ x`, forcing `x` to be a unit.
    have hx0 : (Ideal.Quotient.mk J x : T) = 0 ↔ x ^ 2 ∣ x := by
      simpa [J] using (Ideal.Quotient.eq_zero_iff_dvd (x := x ^ 2) (y := x))
    intro hx
    have hx' : (Ideal.Quotient.mk J x : T) = 0 := by
      simpa [φ, x3, evalS] using hx
    have hxdiv : x ^ 2 ∣ x := (hx0.mp hx')
    rcases hxdiv with ⟨t, ht⟩
    have hx_ne : x ≠ (0 : S1) := X_ne_zero (R := ℂ) (s := (0 : Fin 1))
    have hx_isUnit : IsUnit x := by
      have ht' : x = x * (x * t) := by
        simpa [pow_two, mul_assoc] using ht
      have h1 : (1 : S1) = x * t := by
        apply mul_left_cancel₀ hx_ne
        calc
          x * 1 = x := by simp
          _ = x * (x * t) := by simpa [mul_assoc] using ht'
      refine ⟨⟨x, t, ?_, ?_⟩, rfl⟩
      · exact h1.symm
      ·
        calc
          t * x = x * t := by simp [mul_comm]
          _ = 1 := h1.symm
    -- But `x` evaluates to `0` at the origin, so it is not a unit.
    let ev0 : S1 →+* ℂ :=
      MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun _ : Fin 1 => (0 : ℂ))
    have hx0 : ev0 x = (0 : ℂ) := by
      dsimp [ev0, x]
      exact
        (MvPolynomial.eval₂Hom_X' (f := RingHom.id ℂ) (g := fun _ : Fin 1 => (0 : ℂ))
          (i := (0 : Fin 1)))
    have h0 : IsUnit (0 : ℂ) := by
      simpa [hx0] using (hx_isUnit.map ev0)
    exact not_isUnit_zero h0
  intro hu
  rcases hu with ⟨t, ht⟩
  have : φ u3 ∣ φ (x3 2) := by
    refine ⟨φ t, ?_⟩
    simp [map_mul, ht]
  -- `0 ∣ φ(x2)` forces `φ(x2)=0`, contradiction.
  have : φ (x3 2) = 0 := by
    rcases this with ⟨w, hw⟩
    simpa [hφu] using hw
  exact hφx2 this

private lemma not_prime_u3 : ¬ Prime u3 := by
  intro hu
  have hu_dvd : u3 ∣ (x3 2) * (x3 2) := by
    simpa [pow_two] using u3_dvd_x3_2_sq
  have : u3 ∣ x3 2 := by
    simpa using (hu.dvd_or_dvd hu_dvd)
  exact u3_not_dvd_x3_2 this

/-
Low-degree bookkeeping in `S = ℂ[X₀,X₁,X₂]`:
`q3` is homogeneous of degree 2, hence its multiples have no degree-0 or degree-1 part.

These lemmas are the basic infrastructure needed to make degree-0/1 projections
well-defined on the quotient `R3 = S ⧸ (q3)`.
-/
private lemma q3_isHomogeneous2 : (q3 : MvPolynomial (Fin 3) ℂ).IsHomogeneous 2 := by
  classical
  -- Expand the sum over `Fin 3` and use that each `X i ^ 2` is homogeneous of degree 2.
  have h0 := MvPolynomial.isHomogeneous_X_pow (R := ℂ) (i := (0 : Fin 3)) (n := 2)
  have h1 := MvPolynomial.isHomogeneous_X_pow (R := ℂ) (i := (1 : Fin 3)) (n := 2)
  have h2 := MvPolynomial.isHomogeneous_X_pow (R := ℂ) (i := (2 : Fin 3)) (n := 2)
  simpa [q3, Fin.sum_univ_three, add_assoc] using h0.add (h1.add h2)

private lemma coeff_q3_eq_zero_of_forall_le_one (m : Fin 3 →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
    (MvPolynomial.coeff m q3 : ℂ) = 0 := by
  classical
  have h0 : (fun₀ | (0 : Fin 3) => 2) ≠ m := by
    intro h
    have : (2 : ℕ) = m (0 : Fin 3) := by
      simpa using congrArg (fun f : Fin 3 →₀ ℕ => f (0 : Fin 3)) h
    have : (2 : ℕ) ≤ 1 := by
      simpa [this.symm] using (hm (0 : Fin 3))
    exact Nat.not_succ_le_self 1 this
  have h1 : (fun₀ | (1 : Fin 3) => 2) ≠ m := by
    intro h
    have : (2 : ℕ) = m (1 : Fin 3) := by
      simpa using congrArg (fun f : Fin 3 →₀ ℕ => f (1 : Fin 3)) h
    have : (2 : ℕ) ≤ 1 := by
      simpa [this.symm] using (hm (1 : Fin 3))
    exact Nat.not_succ_le_self 1 this
  have h2 : (fun₀ | (2 : Fin 3) => 2) ≠ m := by
    intro h
    have : (2 : ℕ) = m (2 : Fin 3) := by
      simpa using congrArg (fun f : Fin 3 →₀ ℕ => f (2 : Fin 3)) h
    have : (2 : ℕ) ≤ 1 := by
      simpa [this.symm] using (hm (2 : Fin 3))
    exact Nat.not_succ_le_self 1 this
  -- Expand `q3 = X0^2 + X1^2 + X2^2` and compute coefficients.
  simp [q3, Fin.sum_univ_three, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, h0, h1, h2]

private lemma coeff_q3_eq_zero_of_degree_le_one (m : Fin 3 →₀ ℕ) (hm : m.degree = 1) :
    (MvPolynomial.coeff m q3 : ℂ) = 0 := by
  classical
  -- If `m.degree = 1`, then each coordinate is ≤ 1.
  have hm_le : ∀ i, m i ≤ 1 := by
    intro i
    by_cases hi : i ∈ m.support
    · have hle : m i ≤ m.support.sum m := by
        -- `m i` is one of the summands in `m.support.sum m`.
        simpa [Finsupp.degree] using
          (Finset.single_le_sum (s := m.support) (f := fun j : Fin 3 => m j)
              (by intro j hj; exact Nat.zero_le (m j)) hi)
      have hle' : m i ≤ m.degree := by
        simpa [Finsupp.degree] using hle
      simpa [hm] using hle'
    · have : m i = 0 := by
        exact (Finsupp.notMem_support_iff.1 hi)
      simp [this]
  exact coeff_q3_eq_zero_of_forall_le_one m hm_le

/-- A multiple of `q3` has no coefficient on a squarefree monomial. -/
private lemma coeff_mul_q3_eq_zero_of_forall_le_one (t : MvPolynomial (Fin 3) ℂ)
    (m : Fin 3 →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
    (MvPolynomial.coeff m (t * q3) : ℂ) = 0 := by
  classical
  -- Expand `coeff_mul`; for `a+b=m`, we have `b i ≤ m i ≤ 1`, hence `coeff b q3 = 0`.
  simp [MvPolynomial.coeff_mul]
  refine Finset.sum_eq_zero ?_
  intro ab hab
  have hab' : ab.1 + ab.2 = m :=
    (Finset.HasAntidiagonal.mem_antidiagonal (n := m) (a := ab)).1 hab
  have hle : ∀ i, ab.2 i ≤ 1 := by
    intro i
    have : ab.2 i ≤ m i := by
      have hm' : m i = ab.1 i + ab.2 i := by
        simpa [Finsupp.add_apply] using congrArg (fun f : Fin 3 →₀ ℕ => f i) hab'.symm
      exact hm' ▸ Nat.le_add_left _ _
    exact le_trans this (hm i)
  simp [coeff_q3_eq_zero_of_forall_le_one (m := ab.2) hle]

private lemma homogeneousComponent_mem_I3_deg0_deg1 (p : MvPolynomial (Fin 3) ℂ) (hp : p ∈ I3) :
    MvPolynomial.homogeneousComponent 0 p = 0 ∧ MvPolynomial.homogeneousComponent 1 p = 0 := by
  classical
  rcases (Ideal.mem_span_singleton'.1 hp) with ⟨t, rfl⟩
  constructor
  · -- Degree-0 component is the constant term; `q3` has no constant term.
    have hcoeff0 : (MvPolynomial.coeff 0 (t * q3) : ℂ) = 0 := by
      -- Coefficient of `0` in a product uses only the `(0,0)` term in the antidiagonal.
      simp [MvPolynomial.coeff_mul, Finset.antidiagonal_zero, q3, Fin.sum_univ_three,
        MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow]
    simp [MvPolynomial.homogeneousComponent_zero, hcoeff0]
  · -- Degree-1 component: all degree-1 coefficients vanish.
    ext m
    by_cases hm : m.degree = 1
    · -- `coeff m (q3*t) = 0` for `m.degree = 1` since `q3` has no coefficients in degree ≤ 1.
      have hcoeff : (MvPolynomial.coeff m (t * q3) : ℂ) = 0 := by
        -- Expand `coeff_mul` and observe every term has `coeff _ q3 = 0`.
        classical
        rw [MvPolynomial.coeff_mul]
        refine Finset.sum_eq_zero ?_
        intro a ha
        have ha' : a.1 + a.2 = m := (Finset.mem_antidiagonal.1 ha)
        -- `a.1 i ≤ m i` for all `i`, hence `a.1.degree ≤ 1` and `coeff a.1 q3 = 0`.
        have hle_one : ∀ i, a.1 i ≤ 1 := by
          intro i
          have hle_m : a.1 i ≤ m i := by
            have : a.1 i + a.2 i = m i := by
              simpa [Finsupp.add_apply] using congrArg (fun f : Fin 3 →₀ ℕ => f i) ha'
            exact this ▸ Nat.le_add_right _ _
          -- bound `m i ≤ 1` from `m.degree = 1`
          have hm_le : m i ≤ 1 := by
            -- `m i ≤ m.degree = 1`
            by_cases hi : i ∈ m.support
            · have hle : m i ≤ m.support.sum m := by
                simpa [Finsupp.degree] using
                  (Finset.single_le_sum (s := m.support) (f := fun j : Fin 3 => m j)
                      (by intro j hj; exact Nat.zero_le (m j)) hi)
              have hle' : m i ≤ m.degree := by
                simpa [Finsupp.degree] using hle
              simpa [hm] using hle'
            · have : m i = 0 := by
                exact (Finsupp.notMem_support_iff.1 hi)
              simp [this]
          exact le_trans hle_m hm_le
        have hq : (MvPolynomial.coeff a.2 q3 : ℂ) = 0 :=
          coeff_q3_eq_zero_of_forall_le_one a.2 (by
            intro i
            have hle_m : a.2 i ≤ m i := by
              have : a.1 i + a.2 i = m i := by
                simpa [Finsupp.add_apply] using congrArg (fun f : Fin 3 →₀ ℕ => f i) ha'
              -- `a.2 i ≤ a.1 i + a.2 i`
              exact this ▸ Nat.le_add_left _ _
            -- as above, `m i ≤ 1`
            have hm_le : m i ≤ 1 := by
              by_cases hi : i ∈ m.support
              · have hle : m i ≤ m.support.sum m := by
                  simpa [Finsupp.degree] using
                    (Finset.single_le_sum (s := m.support) (f := fun j : Fin 3 => m j)
                        (by intro j hj; exact Nat.zero_le (m j)) hi)
                have hle' : m i ≤ m.degree := by
                  simpa [Finsupp.degree] using hle
                simpa [hm] using hle'
              · have : m i = 0 := by
                  exact (Finsupp.notMem_support_iff.1 hi)
                simp [this]
            exact le_trans hle_m hm_le)
        simp [hq]
      -- Coefficients of `homogeneousComponent 1` are those of degree-1 monomials.
      simp [MvPolynomial.coeff_homogeneousComponent, hm, hcoeff]
    · simp [MvPolynomial.coeff_homogeneousComponent, hm]

/-
Basic homogeneous-component computations for the linear form
`U = X₀ + i*X₁` in `S = ℂ[X₀,X₁,X₂]`.
-/

private lemma homogeneousComponent_one_X (i : Fin 3) :
    MvPolynomial.homogeneousComponent 1 (X i : MvPolynomial (Fin 3) ℂ) = X i := by
  classical
  ext d
  by_cases hd : d.degree = 1
  · simp [MvPolynomial.coeff_homogeneousComponent, hd]
  ·
    have hne : (Finsupp.single i 1 : Fin 3 →₀ ℕ) ≠ d := by
      intro h
      subst h
      exact hd (by simp)
    simp [MvPolynomial.coeff_homogeneousComponent, hd, MvPolynomial.coeff_X', hne]

private lemma homogeneousComponent_two_X (i : Fin 3) :
    MvPolynomial.homogeneousComponent 2 (X i : MvPolynomial (Fin 3) ℂ) = 0 := by
  classical
  ext d
  by_cases hd : d.degree = 2
  ·
    have hne : (Finsupp.single i 1 : Fin 3 →₀ ℕ) ≠ d := by
      intro h
      subst h
      -- `degree (single i 1) = 1`, contradiction.
      have : (Finsupp.single i 1 : Fin 3 →₀ ℕ).degree ≠ 2 := by simp
      exact this hd
    simp [MvPolynomial.coeff_homogeneousComponent, hd, MvPolynomial.coeff_X', hne]
  · simp [MvPolynomial.coeff_homogeneousComponent, hd]

private lemma homogeneousComponent_U_0_1_2 :
    let U : MvPolynomial (Fin 3) ℂ := X 0 + C Complex.I * X 1
    MvPolynomial.homogeneousComponent 0 U = 0 ∧
      MvPolynomial.homogeneousComponent 1 U = U ∧
        MvPolynomial.homogeneousComponent 2 U = 0 := by
  classical
  intro U
  constructor
  · simp [U]
  constructor
  ·
    -- `U` is linear, so its degree-1 component is itself.
    simp [U, homogeneousComponent_one_X, MvPolynomial.homogeneousComponent_C_mul, map_add]
  ·
    -- `U` has no quadratic part.
    simp [U, homogeneousComponent_two_X, MvPolynomial.homogeneousComponent_C_mul, map_add]

/-
A convenient degree-1 coefficient formula in `S = ℂ[X₀,X₁,X₂]`.
-/
private lemma coeff_mul_degree_one_single (i : Fin 3) (p q : MvPolynomial (Fin 3) ℂ) :
    MvPolynomial.coeff (Finsupp.single i 1) (p * q) =
      MvPolynomial.coeff 0 p * MvPolynomial.coeff (Finsupp.single i 1) q +
        MvPolynomial.coeff (Finsupp.single i 1) p * MvPolynomial.coeff 0 q := by
  classical
  -- Expand `coeff_mul` and simplify the antidiagonal of a single variable monomial.
  simp [MvPolynomial.coeff_mul, Finsupp.antidiagonal_single, Finset.Nat.antidiagonal_succ]

set_option maxHeartbeats 1000000 in
private lemma squarefree_u3 : Squarefree u3 := by
  classical
  -- We unfold `Squarefree` and start extracting the degree-0/1 consequences of `x*x ∣ u3`.
  intro x hx
  rcases hx with ⟨y, hy⟩
  -- Lift the equation to the polynomial ring `S := ℂ[X₀,X₁,X₂]` and record the resulting
  -- ideal-membership statement in `(q3)`.
  rcases (Ideal.Quotient.mk_surjective (I := I3) x) with ⟨px, rfl⟩
  rcases (Ideal.Quotient.mk_surjective (I := I3) y) with ⟨py, rfl⟩
  let mk : MvPolynomial (Fin 3) ℂ →+* R3 := Ideal.Quotient.mk I3
  let U : MvPolynomial (Fin 3) ℂ := X 0 + C Complex.I * X 1
  have hU : (mk U : R3) = u3 := by
    simp [mk, U, u3, x3, I3c]
  have hy' : (mk U : R3) = mk (px * px * py) := by
    -- Rewrite `u3` as the image of `U`, and use that `mk` is a ring homomorphism.
    have : (mk U : R3) = mk px * mk px * mk py := by
      simpa [hU, mk, mul_assoc] using hy
    calc
      (mk U : R3) = mk px * mk px * mk py := this
      _ = mk (px * px) * mk py := by simp [mul_assoc]
      _ = mk ((px * px) * py) := by simp [mk, map_mul]
      _ = mk (px * px * py) := by simp [mul_assoc]
  have hmem : U - px * px * py ∈ I3 := (Ideal.Quotient.eq).1 hy'
  rcases (Ideal.mem_span_singleton'.1 hmem) with ⟨t, ht⟩
  have hUeq : U = px * px * py + t * q3 := by
    have := congrArg (fun z => z + (px * px * py)) ht
    -- `U - px^2*py = t*q3` rearranged.
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this.symm
  have hcoeff_squarefree (m : Fin 3 →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
      (MvPolynomial.coeff m (px * px * py) : ℂ) = (MvPolynomial.coeff m U : ℂ) := by
    have := congrArg (fun p => (MvPolynomial.coeff m p : ℂ)) hUeq
    -- The error term `t*q3` has no squarefree coefficients.
    simpa [MvPolynomial.coeff_add,
      coeff_mul_q3_eq_zero_of_forall_le_one (t := t) (m := m) hm] using this.symm
  have hhc :
      MvPolynomial.homogeneousComponent 0 (U - px * px * py) = 0 ∧
        MvPolynomial.homogeneousComponent 1 (U - px * px * py) = 0 :=
    homogeneousComponent_mem_I3_deg0_deg1 (p := U - px * px * py) hmem
  have hhc0 : MvPolynomial.homogeneousComponent 0 (U - px * px * py) = 0 := hhc.1
  have hhc1 : MvPolynomial.homogeneousComponent 1 (U - px * px * py) = 0 := hhc.2
  -- The remaining work is a degree argument in the quotient: from `hhc0`/`hhc1` one can
  -- extract constraints on the constant/linear parts of `px` and `py`, and then use a
  -- degree-2 normal form argument to conclude `mk px` is a unit.
  have hUhc : MvPolynomial.homogeneousComponent 0 U = 0 ∧
      MvPolynomial.homogeneousComponent 1 U = U ∧ MvPolynomial.homogeneousComponent 2 U = 0 := by
    simpa [U] using homogeneousComponent_U_0_1_2
  have hhc0' : MvPolynomial.homogeneousComponent 0 (px * px * py) = 0 := by
    have h : MvPolynomial.homogeneousComponent 0 U -
        MvPolynomial.homogeneousComponent 0 (px * px * py) = 0 := by
      simpa [map_sub] using hhc0
    have hEq : MvPolynomial.homogeneousComponent 0 U =
        MvPolynomial.homogeneousComponent 0 (px * px * py) := sub_eq_zero.mp h
    calc
      MvPolynomial.homogeneousComponent 0 (px * px * py) =
          MvPolynomial.homogeneousComponent 0 U := hEq.symm
      _ = 0 := hUhc.1
  have hhc1' : MvPolynomial.homogeneousComponent 1 (px * px * py) = U := by
    have h : MvPolynomial.homogeneousComponent 1 U -
        MvPolynomial.homogeneousComponent 1 (px * px * py) = 0 := by
      simpa [map_sub] using hhc1
    have hEq : MvPolynomial.homogeneousComponent 1 U =
        MvPolynomial.homogeneousComponent 1 (px * px * py) := sub_eq_zero.mp h
    simpa [hUhc.2.1] using hEq.symm

  -- From the degree-1 equality, `px` must have nonzero constant term (otherwise `px^2*py` has
  -- zero coefficient at `X 0`).
  have hcoeff0_px : (MvPolynomial.coeff 0 px : ℂ) ≠ 0 := by
    intro h0
    have hpxpx0 : (MvPolynomial.coeff 0 (px * px) : ℂ) = 0 := by
      simp [MvPolynomial.coeff_mul, Finset.antidiagonal_zero, h0]
    have hpxpxX0 : (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) (px * px) : ℂ) = 0 := by
      -- degree-1 coefficients of `px*px` depend only on `coeff 0 px`.
      simp [coeff_mul_degree_one_single, h0]
    have hprodX0 : (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) (px * px * py) : ℂ) = 0 := by
      -- Use the degree-1 coefficient formula for `(px*px)*py`.
      have := (coeff_mul_degree_one_single (i := (0 : Fin 3)) (p := (px * px)) (q := py))
      -- Rewrite `px*px*py` as `(px*px)*py`.
      simpa [mul_assoc, hpxpx0, hpxpxX0] using this
    have hUcoeff : (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) U : ℂ) = 1 := by
      simp [U]
    -- Take the coefficient of `X 0` in `hhc1' : hc1(prod) = U`.
    have hcoeff_hc1 :
        (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1)
          (MvPolynomial.homogeneousComponent 1 (px * px * py)) : ℂ) =
          (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) U : ℂ) := by
      exact congrArg (fun p =>
        (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) p : ℂ)) hhc1'
    -- But `coeff` of the degree-1 homogeneous component is the original coefficient.
    have hhc1coeff :
        (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1)
            (MvPolynomial.homogeneousComponent 1 (px * px * py)) : ℂ) =
          (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) (px * px * py) : ℂ) := by
      simp [MvPolynomial.coeff_homogeneousComponent]
    -- Contradiction.
    have : (1 : ℂ) = 0 := by
      calc
        (1 : ℂ) = (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) U : ℂ) := hUcoeff.symm
        _ = (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1)
                (MvPolynomial.homogeneousComponent 1 (px * px * py)) : ℂ) := by
              exact hcoeff_hc1.symm
        _ = (MvPolynomial.coeff (Finsupp.single (0 : Fin 3) 1) (px * px * py) : ℂ) := hhc1coeff
        _ = 0 := hprodX0
    exact one_ne_zero this

  -- Degree-0 equation forces `coeff 0 py = 0`.
  have hcoeff0_py : (MvPolynomial.coeff 0 py : ℂ) = 0 := by
    have h0prod : (MvPolynomial.coeff 0 (px * px * py) : ℂ) = 0 := by
      simpa [MvPolynomial.homogeneousComponent_zero] using congrArg (MvPolynomial.coeff 0) hhc0'
    have h0prod' : (MvPolynomial.coeff 0 px : ℂ) * (MvPolynomial.coeff 0 px : ℂ) *
        (MvPolynomial.coeff 0 py : ℂ) = 0 := by
      simpa [mul_assoc, MvPolynomial.coeff_mul, Finset.antidiagonal_zero] using h0prod
    have hx2 : (MvPolynomial.coeff 0 px : ℂ) * (MvPolynomial.coeff 0 px : ℂ) ≠ 0 :=
      mul_ne_zero hcoeff0_px hcoeff0_px
    exact mul_eq_zero.mp (by simpa [mul_assoc] using h0prod') |>.resolve_left hx2

  classical
  -- Transport `R3` to a quadratic extension `A[α]/(α^2 + f)` where `α` corresponds to `X 2`.
  let fA : MvPolynomial (Fin 2) ℂ :=
    (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 2 + (X (1 : Fin 2) : MvPolynomial (Fin 2) ℂ) ^ 2
  let pA : Polynomial (MvPolynomial (Fin 2) ℂ) := Polynomial.X ^ 2 + Polynomial.C fA
  let J : Ideal (Polynomial (MvPolynomial (Fin 2) ℂ)) :=
    Ideal.span ({pA} : Set (Polynomial (MvPolynomial (Fin 2) ℂ)))
  let B : Type := AdjoinRoot pA
  letI : CommRing B := by
    dsimp [B]
    infer_instance

  -- `Fin 3 ≃ Option (Fin 2)` picking `2` as the distinguished variable.
  let fin3 : Fin 3 ≃ Option (Fin 2) :=
    { toFun := fun i =>
        match (i : Fin 3) with
        | 0 => some 0
        | 1 => some 1
        | 2 => none
      invFun := fun o =>
        match o with
        | none => 2
        | some j => Fin.castLT j (lt_trans j.isLt (by decide : (2 : ℕ) < 3))
      left_inv := by
        intro i; fin_cases i <;> rfl
      right_inv := by
        intro o
        cases o with
        | none => rfl
        | some j =>
            fin_cases j <;> rfl }

  -- Identify `S = ℂ[X0,X1,X2]` with `A[α]` where `α` corresponds to `X 2`.
  let e : MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 2) ℂ) :=
    (MvPolynomial.renameEquiv ℂ fin3).trans (MvPolynomial.optionEquivLeft ℂ (Fin 2))

  have e_q3 : e q3 = pA := by
    classical
    have e_X0 :
        e (X (0 : Fin 3) : MvPolynomial (Fin 3) ℂ) =
          (Polynomial.C (X (0 : Fin 2)) : Polynomial (MvPolynomial (Fin 2) ℂ)) := by
      simpa [e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, fin3] using
        (MvPolynomial.optionEquivLeft_X_some (R := ℂ) (S₁ := Fin 2) (x := (0 : Fin 2)))
    have e_X1 :
        e (X (1 : Fin 3) : MvPolynomial (Fin 3) ℂ) =
          (Polynomial.C (X (1 : Fin 2)) : Polynomial (MvPolynomial (Fin 2) ℂ)) := by
      simpa [e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, fin3] using
        (MvPolynomial.optionEquivLeft_X_some (R := ℂ) (S₁ := Fin 2) (x := (1 : Fin 2)))
    have e_X2 :
        e (X (2 : Fin 3) : MvPolynomial (Fin 3) ℂ) =
          (Polynomial.X : Polynomial (MvPolynomial (Fin 2) ℂ)) := by
      simpa [e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, fin3] using
        (MvPolynomial.optionEquivLeft_X_none (R := ℂ) (S₁ := Fin 2))
    -- Expand `q3 = X0^2 + X1^2 + X2^2` and rewrite each variable.
    simp [q3, Fin.sum_univ_three, e_X0, e_X1, e_X2, pA, fA, pow_two, add_assoc, add_comm,
      add_left_comm]

  have hJ : J = Ideal.map (RingHomClass.toRingHom e) I3 := by
    classical
    -- Transport the principal ideal `(q3)` along `e`.
    have hm :
        Ideal.map (RingHomClass.toRingHom e) I3 =
          Ideal.span ({e q3} : Set (Polynomial (MvPolynomial (Fin 2) ℂ))) := by
      simpa [I3] using (Ideal.map_span (RingHomClass.toRingHom e) ({q3} : Set _))
    -- Rewrite `e q3 = pA`.
    calc
      J = Ideal.span ({pA} : Set (Polynomial (MvPolynomial (Fin 2) ℂ))) := rfl
      _ = Ideal.span ({e q3} : Set (Polynomial (MvPolynomial (Fin 2) ℂ))) := by simp [e_q3]
      _ = Ideal.map (RingHomClass.toRingHom e) I3 := by simp [hm]

  -- The induced equivalence on quotients.
  let φ : R3 ≃ₐ[ℂ] (Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J) :=
    Ideal.quotientEquivAlg (I := I3) (J := J) e hJ

  -- Rewrite the divisibility equation in the quadratic extension.
  have hxR : (mk U : R3) = (mk px) * (mk px) * (mk py) := by
    calc
      (mk U : R3) = u3 := hU
      _ = (mk px) * (mk px) * (mk py) := hy
  have hxB :
      (φ (mk U) : Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J) =
        (φ (mk px)) * (φ (mk px)) * (φ (mk py)) := by
    simpa [map_mul, mul_assoc] using
      congrArg (fun z : R3 => (φ z : Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J)) hxR

  -- Work in `B = AdjoinRoot pA` (definitionally the same quotient).
  have hxB' :
      (φ (mk U) : B) = (φ (mk px)) * (φ (mk px)) * (φ (mk py)) := by
    simpa using hxB

  -- Conjugation on `B`: send `α ↦ -α` and fix `A`.
  let α : B := AdjoinRoot.root pA
  let ofA : MvPolynomial (Fin 2) ℂ →+* B := AdjoinRoot.of pA
  let uA : MvPolynomial (Fin 2) ℂ :=
    (X (0 : Fin 2) : MvPolynomial (Fin 2) ℂ) + C Complex.I * X (1 : Fin 2)
  have hα : Polynomial.eval₂ ofA α pA = 0 := by
    dsimp [ofA, α]
    exact AdjoinRoot.eval₂_root pA
  have hα' : (α ^ 2 : B) + ofA fA = 0 := by
    -- Expand `eval₂` at `α` for `pA = X^2 + C fA`.
    have hα1 : Polynomial.eval₂ ofA α (Polynomial.X ^ 2 + Polynomial.C fA) = 0 := by
      simpa [pA] using hα
    have hα2 :
        Polynomial.eval₂ ofA α (Polynomial.X ^ 2) +
            Polynomial.eval₂ ofA α (Polynomial.C fA) =
          (0 : B) := by
      simpa [Polynomial.eval₂_add] using hα1
    have hX :
        Polynomial.eval₂ ofA α (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℂ)) =
          (α ^ 2 : B) := by
      simp [pow_two]
    have hC :
        Polynomial.eval₂ ofA α (Polynomial.C fA : Polynomial (MvPolynomial (Fin 2) ℂ)) = ofA fA := by
      simp
    simpa [hX, hC] using hα2
  have hαneg : Polynomial.eval₂ ofA (-α) pA = 0 := by
    have hsq : (α ^ 2 : B) = (-α : B) ^ 2 := by
      simp
    have hαneg' : ((-α : B) ^ 2) + ofA fA = 0 := by
      -- Rewrite the relation for `α` using `(-α)^2 = α^2`.
      rw [← hsq]
      exact hα'
    have hx :
        Polynomial.eval₂ ofA (-α) (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℂ)) =
          ((-α : B) ^ 2) := by
      simp [pow_two]
    have hc :
        Polynomial.eval₂ ofA (-α) (Polynomial.C fA : Polynomial (MvPolynomial (Fin 2) ℂ)) = ofA fA := by
      simp
    have h1 : Polynomial.eval₂ ofA (-α) (Polynomial.X ^ 2 + Polynomial.C fA) = 0 := by
      simpa [Polynomial.eval₂_add, hx, hc] using hαneg'
    simpa [pA] using h1

  let σ : B →+* B := AdjoinRoot.lift (i := ofA) (x := (-α : B)) hαneg
  have hσ_of (a : MvPolynomial (Fin 2) ℂ) : σ (ofA a) = ofA a := by
    dsimp [σ, ofA]
    exact AdjoinRoot.lift_of (h := hαneg) (i := AdjoinRoot.of pA) (a := (-α : B)) (x := a)
  have hσα : σ α = -α := by
    dsimp [σ, α]
    exact AdjoinRoot.lift_root (h := hαneg) (i := AdjoinRoot.of pA) (a := (-α : B))

  -- A helper: `N(z) = z * σ z` lies in the image of `A`.
  have norm_exists (z : B) : ∃ n : MvPolynomial (Fin 2) ℂ, (ofA n : B) = z * σ z := by
    classical
    refine AdjoinRoot.induction_on pA z ?_
    intro q
    -- Reduce to a representative of degree < 2.
    let r : Polynomial (MvPolynomial (Fin 2) ℂ) := q %ₘ pA
    have hr : (AdjoinRoot.mk pA q : B) = AdjoinRoot.mk pA r := by
      apply (Ideal.Quotient.eq).2
      have hpmonic : pA.Monic := by
        simpa [pA] using
          (Polynomial.monic_X_pow_add_C (R := MvPolynomial (Fin 2) ℂ) (a := fA) (n := 2) (by decide))
      have hmod : r = q - pA * (q /ₘ pA) := by
        simpa [r] using (Polynomial.modByMonic_eq_sub_mul_div (p := q) (q := pA) hpmonic)
      have hqr : q - r = pA * (q /ₘ pA) := by
        calc
          q - r = q - (q - pA * (q /ₘ pA)) := by simp [hmod]
          _ = pA * (q /ₘ pA) := by simp
      refine Ideal.mem_span_singleton'.2 ?_
      refine ⟨q /ₘ pA, ?_⟩
      simpa [mul_comm] using hqr.symm
    have hrdeg : r.natDegree < 2 := by
      have hpmonic : pA.Monic := by
        simpa [pA] using
          (Polynomial.monic_X_pow_add_C (R := MvPolynomial (Fin 2) ℂ) (a := fA) (n := 2) (by decide))
      have hpNatDeg : pA.natDegree = 2 := by
        simp [pA]
      have hpne : pA ≠ 1 := by
        intro h
        have hnd : pA.natDegree = (1 : Polynomial (MvPolynomial (Fin 2) ℂ)).natDegree :=
          congrArg Polynomial.natDegree h
        have : (2 : ℕ) = 0 := by
          rw [hpNatDeg] at hnd
          simp at hnd
        exact (by decide : (2 : ℕ) ≠ 0) this
      have hlt := Polynomial.natDegree_modByMonic_lt (p := q) (q := pA) hpmonic hpne
      simpa [r, hpNatDeg] using hlt
    have hrle : r.natDegree ≤ 1 := by
      -- `r.natDegree < 2` means `r` has degree ≤ 1.
      exact (Nat.lt_succ_iff.mp (by simpa using hrdeg))
    rcases Polynomial.exists_eq_X_add_C_of_natDegree_le_one (R := MvPolynomial (Fin 2) ℂ) (p := r) hrle with
      ⟨b, a, hrX⟩
    have hr_lin : r = Polynomial.C a + Polynomial.C b * Polynomial.X := by
      -- `hrX` is `r = C b * X + C a`.
      simpa [add_comm, add_left_comm, add_assoc] using hrX
    refine ⟨a ^ 2 + b ^ 2 * fA, ?_⟩
    have hz : (AdjoinRoot.mk pA r : B) = ofA a + ofA b * α := by
      calc
        (AdjoinRoot.mk pA r : B) =
            AdjoinRoot.mk pA (Polynomial.C a + Polynomial.C b * Polynomial.X) := by
              simp [hr_lin]
        _ = (AdjoinRoot.mk pA (Polynomial.C a) : B) + AdjoinRoot.mk pA (Polynomial.C b * Polynomial.X) := by
              exact (AdjoinRoot.mk pA).map_add (Polynomial.C a) (Polynomial.C b * Polynomial.X)
        _ = ofA a + ofA b * α := by
              -- `mk` sends `C` to `of` and `X` to the root.
              dsimp [ofA, α]
              -- Second summand.
              rw [map_mul]
              rw [AdjoinRoot.mk_X (f := pA)]
              rfl
    have hσz : σ (AdjoinRoot.mk pA r : B) = ofA a - ofA b * α := by
      -- Expand `σ` on `ofA a + ofA b * α` and use `σ α = -α`.
      rw [hz]
      -- Expand `σ` using ring-hom properties, then use `σ` fixes `A` and sends `α ↦ -α`.
      rw [σ.map_add, σ.map_mul]
      rw [hσ_of a, hσ_of b, hσα]
      have h1 : ofA a + ofA b * -α = ofA a + -(ofA b * α) := by
        exact congrArg (fun t => ofA a + t) (mul_neg (ofA b) α)
      exact h1.trans (sub_eq_add_neg (ofA a) (ofA b * α)).symm
    have hαsq : α ^ 2 = -(ofA fA : B) := by
      exact eq_neg_of_add_eq_zero_left hα'
    have hnorm_r :
        (ofA (a ^ 2 + b ^ 2 * fA) : B) = (AdjoinRoot.mk pA r : B) * σ (AdjoinRoot.mk pA r : B) := by
      -- Avoid `ring_nf`: compute the norm of a linear element by hand.
      have hmul :
          (ofA a + ofA b * α) * (ofA a - ofA b * α) =
            ofA a * ofA a - (ofA b * α) * (ofA b * α) := by
        ring
      have hyy :
          (ofA b * α) * (ofA b * α) = -(ofA (b ^ 2 * fA) : B) := by
        calc
          (ofA b * α) * (ofA b * α) = (ofA b * ofA b) * (α * α) := by
            simp [mul_assoc, mul_left_comm, mul_comm]
          _ = (ofA b * ofA b) * (α ^ 2) := by
            simp [pow_two, mul_assoc]
          _ = (ofA b * ofA b) * (-(ofA fA : B)) := by
            simpa using congrArg (fun t => (ofA b * ofA b) * t) hαsq
          _ = -((ofA b * ofA b) * (ofA fA : B)) := by
            simp
          _ = -(ofA (b ^ 2 * fA) : B) := by
            simp [pow_two, ofA, map_mul, mul_assoc, mul_left_comm, mul_comm]
      have hprod :
          (ofA a + ofA b * α) * (ofA a - ofA b * α) = (ofA (a ^ 2 + b ^ 2 * fA) : B) := by
        calc
          (ofA a + ofA b * α) * (ofA a - ofA b * α)
              = ofA a * ofA a - (ofA b * α) * (ofA b * α) := hmul
          _ = (ofA (a ^ 2) : B) - (-(ofA (b ^ 2 * fA) : B)) := by
            simp [pow_two, ofA, map_mul, mul_assoc, hyy]
          _ = (ofA (a ^ 2) : B) + (ofA (b ^ 2 * fA) : B) := by
            simp [sub_eq_add_neg]
          _ = (ofA (a ^ 2 + b ^ 2 * fA) : B) := by
            simp [ofA, map_add]
      calc
        (ofA (a ^ 2 + b ^ 2 * fA) : B) =
            (ofA a + ofA b * α) * (ofA a - ofA b * α) := by
          simpa using hprod.symm
        _ = (AdjoinRoot.mk pA r : B) * σ (AdjoinRoot.mk pA r : B) := by
          rw [hσz, hz]
    refine hnorm_r.trans ?_
    simp [hr]

  -- Apply the norm trick to `xB := φ(mk px)`.
  let xB : B := (φ (mk px) : Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J)
  let yB : B := (φ (mk py) : Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J)
  let uB : B := (φ (mk U) : Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J)
  have huB : uB = xB * xB * yB := by
    simpa [uB, xB, yB] using hxB'
  rcases norm_exists xB with ⟨nX, hnX⟩
  rcases norm_exists yB with ⟨nY, hnY⟩

  have huB_uA : uB = ofA uA := by
    have huB' : uB = (Ideal.Quotient.mk J) (e U) := by
      simp [uB, mk, φ]
    have heU : e U = Polynomial.C uA := by
      -- `U` only involves the variables `X 0, X 1`, hence becomes a constant polynomial under `e`.
      simp [e, fin3, U, uA, optionEquivLeft_X_some, optionEquivLeft_C]
    -- `Ideal.Quotient.mk J (Polynomial.C uA)` is definitionally the embedding `ofA uA`.
    rw [huB', heU]
    dsimp [B, J, ofA]
    exact AdjoinRoot.mk_C (f := pA) uA

  -- `uB` is fixed by `σ` since it comes from `A` (it involves only `X 0, X 1`).
  have hσ_uB : σ uB = uB := by
    -- Now `uB = ofA uA`, and `σ` fixes the image of `ofA`.
    rw [huB_uA]
    simpa using (hσ_of uA)

  -- Multiply the equation by its conjugate to get a divisibility in `A`.
  have hnorm : uB ^ 2 = (ofA (nX ^ 2) : B) * ofA nY := by
    -- `uB = xB^2 * yB`, so `uB^2 = N(xB)^2 * N(yB)`.
    calc
      uB ^ 2 = uB * σ uB := by
        simp [hσ_uB, pow_two]
      _ = (xB * σ xB) ^ 2 * (yB * σ yB) := by
        -- Expand `uB = xB^2 * yB`, expand `σ` on products, then use commutativity.
        rw [huB]
        simp [pow_two, map_mul, mul_assoc]
        ac_rfl
      _ = (ofA nX : B) ^ 2 * (ofA nY : B) := by
        -- Replace the norms by the chosen `nX, nY`.
        rw [← hnX, ← hnY]
      _ = (ofA (nX ^ 2) : B) * ofA nY := by
        -- Pull the square back through `ofA`.
        rw [(map_pow ofA nX 2).symm]

  -- Injectivity of `ofA` lets us pull back to `A`.
  have hof_inj : Function.Injective ofA := by
    -- `pA` is not constant, so `ofA` is injective.
    have hdeg : (pA.degree : WithBot ℕ) ≠ 0 := by
      have hlt :
          (Polynomial.C fA : Polynomial (MvPolynomial (Fin 2) ℂ)).degree <
            (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℂ)).degree := by
        simpa using (lt_of_le_of_lt (Polynomial.degree_C_le) (by simp))
      have : pA.degree = (Polynomial.X ^ 2 : Polynomial (MvPolynomial (Fin 2) ℂ)).degree := by
        simpa [pA, add_comm] using (Polynomial.degree_add_eq_left_of_degree_lt hlt)
      simp [this]
    -- `A = ℂ[X₀,X₁]` is a domain, so `ofA` is injective as soon as `pA.degree ≠ 0`.
    simpa [ofA] using
      (AdjoinRoot.of.injective_of_degree_ne_zero
        (R := MvPolynomial (Fin 2) ℂ) (f := pA) hdeg)

  have hnX_dvd_u : nX ∣ uA ^ 2 := by
    -- From `uB^2 = ofA(nX^2) * ofA nY` and injectivity.
    have : ofA (uA ^ 2) = (ofA (nX ^ 2) : B) * ofA nY := by
      have hnorm' : (ofA uA : B) ^ 2 = (ofA (nX ^ 2) : B) * ofA nY := by
        simpa [huB_uA] using hnorm
      exact (map_pow ofA uA 2).trans hnorm'
    have : uA ^ 2 = nX ^ 2 * nY := by
      apply hof_inj
      simpa [ofA, map_mul, map_pow, pow_two, mul_assoc] using this
    refine ⟨nX * nY, ?_⟩
    -- `uA^2 = nX^2*nY = nX*(nX*nY)`.
    simpa [pow_two, mul_assoc] using this

  -- `uA = X0 + i*X1` is prime in `A` (a linear polynomial).
  have huA_prime : Prime (uA : MvPolynomial (Fin 2) ℂ) := by
    let fin2 : Fin 2 ≃ Option (Fin 1) :=
      { toFun := fun i =>
          match (i : Fin 2) with
          | 0 => none
          | 1 => some 0
        invFun := fun o =>
          match o with
          | none => 0
          | some _ => 1
        left_inv := by intro i; fin_cases i <;> rfl
        right_inv := by
          intro o
          cases o with
          | none => rfl
          | some j =>
              fin_cases j
              rfl }
    let e2 : MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] Polynomial (MvPolynomial (Fin 1) ℂ) :=
      (MvPolynomial.renameEquiv ℂ fin2).trans (MvPolynomial.optionEquivLeft ℂ (Fin 1))
    have hu2 : Irreducible (e2 uA) := by
      have : e2 uA =
          (Polynomial.X -
            Polynomial.C (-(C Complex.I : MvPolynomial (Fin 1) ℂ) * X (0 : Fin 1))) := by
        simp [e2, fin2, uA, MvPolynomial.optionEquivLeft, sub_eq_add_neg]
      -- Reduce to `Polynomial.irreducible_X_sub_C`.
      rw [this]
      exact
        Polynomial.irreducible_X_sub_C
          (R := MvPolynomial (Fin 1) ℂ)
          (r := (-(C Complex.I : MvPolynomial (Fin 1) ℂ) * X (0 : Fin 1)))
    have hu : Irreducible (uA : MvPolynomial (Fin 2) ℂ) := (MulEquiv.irreducible_iff e2).1 hu2
    exact hu.prime

  -- Show `uA ∤ nX` by evaluating at the origin (where `uA` vanishes but `nX` does not).
  let εA : MvPolynomial (Fin 2) ℂ →+* ℂ :=
    MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun _ : Fin 2 => (0 : ℂ))
  have hε_uA : εA uA = 0 := by simp [εA, uA]
  have hε_pA : Polynomial.eval₂ εA (0 : ℂ) pA = 0 := by
    simp [pA, fA, εA, pow_two]
  let εB : B →+* ℂ :=
    AdjoinRoot.lift (i := (εA : MvPolynomial (Fin 2) ℂ →+* ℂ)) (x := (0 : ℂ))
      hε_pA
  have hεB_of (a : MvPolynomial (Fin 2) ℂ) : εB (ofA a) = εA a := by
    dsimp [εB, ofA]
    exact AdjoinRoot.lift_of (h := hε_pA) (i := εA) (a := (0 : ℂ)) (x := a)
  have hεB_σ (z : B) : εB (σ z) = εB z := by
    -- `σ` changes `α` to `-α`, but `εB` sends `α` to `0`.
    have hεBα : εB α = 0 := by
      dsimp [εB, α]
      exact AdjoinRoot.lift_root (f := pA) (i := εA) (a := (0 : ℂ)) (h := hε_pA)
    have hεB_comp_ofA : εB.comp ofA = εA := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [RingHom.comp_apply, hεB_of]
      · intro i
        simpa [RingHom.comp_apply] using (hεB_of (X i))
    refine AdjoinRoot.induction_on pA z ?_
    intro q
    dsimp [σ]
    rw [AdjoinRoot.lift_mk (h := hαneg) (i := ofA) (a := (-α : B)) q]
    -- Move `εB` inside the `eval₂`.
    rw [Polynomial.hom_eval₂ (p := q) (f := ofA) (g := εB) (x := (-α : B))]
    -- Evaluate `εB` on coefficients and on `-α`.
    simp [hεB_comp_ofA, hεBα]
    -- Finally, compute `εB` on `mk q`.
    dsimp [εB]
    rw [AdjoinRoot.lift_mk (h := hε_pA) (i := εA) (a := (0 : ℂ)) q]
    -- Evaluate at `0` picks out the constant coefficient.
    simp [Polynomial.eval₂_at_zero]
  have hεB_xB : εB xB = (MvPolynomial.coeff 0 px : ℂ) := by
    -- `xB` is represented by `e px` and evaluation at the origin extracts `coeff 0 px`.
    have h_eval_e (p : MvPolynomial (Fin 3) ℂ) :
        Polynomial.eval₂ εA (0 : ℂ) (e p) = (MvPolynomial.coeff 0 p : ℂ) := by
      let ψ : MvPolynomial (Fin 3) ℂ →+* ℂ :=
        (Polynomial.eval₂RingHom εA (0 : ℂ)).comp (e.toRingHom)
      let ε3 : MvPolynomial (Fin 3) ℂ →+* ℂ :=
        MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun _ : Fin 3 => (0 : ℂ))
      have e_X0 :
          e (X (0 : Fin 3) : MvPolynomial (Fin 3) ℂ) =
            (Polynomial.C (X (0 : Fin 2)) : Polynomial (MvPolynomial (Fin 2) ℂ)) := by
        simpa [e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, fin3] using
          (MvPolynomial.optionEquivLeft_X_some (R := ℂ) (S₁ := Fin 2) (x := (0 : Fin 2)))
      have e_X1 :
          e (X (1 : Fin 3) : MvPolynomial (Fin 3) ℂ) =
            (Polynomial.C (X (1 : Fin 2)) : Polynomial (MvPolynomial (Fin 2) ℂ)) := by
        simpa [e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, fin3] using
          (MvPolynomial.optionEquivLeft_X_some (R := ℂ) (S₁ := Fin 2) (x := (1 : Fin 2)))
      have e_X2 :
          e (X (2 : Fin 3) : MvPolynomial (Fin 3) ℂ) =
            (Polynomial.X : Polynomial (MvPolynomial (Fin 2) ℂ)) := by
        simpa [e, MvPolynomial.renameEquiv, MvPolynomial.rename_X, fin3] using
          (MvPolynomial.optionEquivLeft_X_none (R := ℂ) (S₁ := Fin 2))
      have hψε : ψ = ε3 := by
        apply MvPolynomial.ringHom_ext
        · intro r
          simp [ψ, ε3, e, fin3, εA, MvPolynomial.optionEquivLeft_C]
        · intro i
          fin_cases i
          · simp [ψ, ε3, e_X0, εA]
          · simp [ψ, ε3, e_X1, εA]
          · simp [ψ, ε3, e_X2, εA]
      have : ψ p = ε3 p := congrArg (fun f => f p) hψε
      simpa [ψ, ε3, MvPolynomial.constantCoeff_eq] using this
    have hxB_repr : xB = (AdjoinRoot.mk pA) (e px) := by
      have hxB' :
          (xB : B) = (Ideal.Quotient.mk J) (e px) := by
        simp [xB, mk, φ]
      simpa [B, J] using hxB'
    -- Evaluate using `lift_mk`.
    rw [hxB_repr]
    dsimp [εB]
    rw [AdjoinRoot.lift_mk (h := hε_pA) (i := εA) (a := (0 : ℂ)) (g := e px)]
    exact h_eval_e px
  have hnX_not_dvd : ¬ uA ∣ nX := by
    intro hdiv
    rcases hdiv with ⟨t, rfl⟩
    have hεut : εA (uA * t) = 0 := by
      simp [map_mul, hε_uA]
    have hεut_ne : εA (uA * t) ≠ 0 := by
      have : εA (uA * t) = (εB xB) * (εB xB) := by
        calc
          εA (uA * t) = εB (ofA (uA * t)) := by simpa using (hεB_of (uA * t)).symm
          _ = εB (xB * σ xB) := by simpa using congrArg εB hnX
          _ = (εB xB) * (εB xB) := by simp [map_mul, hεB_σ]
      have hx0 : εB xB ≠ 0 := by simpa [hεB_xB] using hcoeff0_px
      simpa [this] using mul_ne_zero hx0 hx0
    exact hεut_ne hεut

  have hnX_isUnit : IsUnit (nX : MvPolynomial (Fin 2) ℂ) := by
    -- Since `nX ∣ uA^2` and `uA` is prime, either `nX` is a unit or `uA ∣ nX`.
    rcases (dvd_prime_pow huA_prime (q := (nX : MvPolynomial (Fin 2) ℂ)) (n := 2)).1 hnX_dvd_u with
      ⟨i, hi, hassoc⟩
    cases i with
    | zero =>
        exact (hassoc.isUnit_iff).2 (by simp)
    | succ i =>
        have : uA ∣ nX := by
          have : uA ∣ uA ^ Nat.succ i := dvd_pow_self _ (Nat.succ_ne_zero i)
          exact (hassoc.dvd_iff_dvd_right).2 this
        exact (hnX_not_dvd this).elim

  -- Conclude `xB` is a unit from `IsUnit (xB * σ xB)`.
  have hxB_unit : IsUnit xB := by
    have : IsUnit (xB * σ xB) := by
      have : IsUnit (ofA nX : B) := hnX_isUnit.map ofA
      simpa [hnX, mul_assoc] using this
    exact isUnit_of_mul_isUnit_left this

  -- Transport the unit back along `φ`.
  have : IsUnit (mk px : R3) := by
    have : IsUnit (φ.symm xB) :=
      hxB_unit.map (φ.symm : (Polynomial (MvPolynomial (Fin 2) ℂ) ⧸ J) →* R3)
    simpa [xB] using this
  simpa [mk] using this

/-- Non-UFD for the quadric in three variables. -/
lemma not_UFD_R3 [IsDomain (R 3)] : ¬ UniqueFactorizationMonoid (R 3) := by
  classical
  -- Use the standard fact: in a `UniqueFactorizationMonoid`, squarefree elements satisfy
  -- `x ∣ y^n ↔ x ∣ y` for `n ≠ 0`.
  intro hufm
  haveI : UniqueFactorizationMonoid R3 := by
    -- `R3` is definitionally `R 3`.
    simpa [R3] using hufm
  have hx2 : u3 ∣ (x3 2) ^ 2 := u3_dvd_x3_2_sq
  have hx2' : u3 ∣ x3 2 := by
    -- `Squarefree.dvd_pow_iff_dvd` needs only `DecompositionMonoid`, which follows from UFM.
    simpa using (squarefree_u3.dvd_pow_iff_dvd (y := x3 2) (n := 2) (by decide)).1 hx2
  exact u3_not_dvd_x3_2 hx2'

/- Non-UFD for the quadric in four variables. -/
set_option maxHeartbeats 1000000 in
lemma not_UFD_R4 [IsDomain (R 4)] : ¬ UniqueFactorizationMonoid (R 4) := by
  classical
  -- Work in `R4 = ℂ[X₀,X₁,X₂,X₃]/(X₀²+X₁²+X₂²+X₃²)`.
  let R4 : Type := R 4
  let q4 : MvPolynomial (Fin 4) ℂ := ∑ i : Fin 4, X i ^ 2
  let I4 : Ideal (MvPolynomial (Fin 4) ℂ) := Ideal.span ({q4} : Set (MvPolynomial (Fin 4) ℂ))
  let x4 (i : Fin 4) : R4 := Ideal.Quotient.mk I4 (X i)
  let I4c (z : ℂ) : R4 := Ideal.Quotient.mk I4 (C z)
  let u : R4 := x4 0 + I4c Complex.I * x4 1
  let v : R4 := x4 0 - I4c Complex.I * x4 1
  let c : R4 := x4 2 + I4c Complex.I * x4 3
  let d : R4 := x4 2 - I4c Complex.I * x4 3

  have quadric_relation_R4 :
      (x4 0) ^ 2 + (x4 1) ^ 2 + (x4 2) ^ 2 + (x4 3) ^ 2 = 0 := by
    have hq : (Ideal.Quotient.mk I4 q4 : R4) = 0 := by
      simp [I4]
    have hq' : (∑ i : Fin 4, (x4 i) ^ 2 : R4) = 0 := by
      simpa [q4, x4] using hq
    simpa [Fin.sum_univ_four] using hq'

  have u_mul_v_eq_neg_c_mul_d : u * v = -(c * d) := by
    have hI2 : (I4c Complex.I : R4) * I4c Complex.I = (-1 : R4) := by
      calc
        (I4c Complex.I : R4) * I4c Complex.I =
            (Ideal.Quotient.mk I4 ((C Complex.I : MvPolynomial (Fin 4) ℂ) * C Complex.I) : R4) := by
              simp [I4c]
        _ = (Ideal.Quotient.mk I4 (C (Complex.I * Complex.I)) : R4) := by
          have hC :
              (C Complex.I : MvPolynomial (Fin 4) ℂ) * C Complex.I = C (Complex.I * Complex.I) := by
            simpa using
              (MvPolynomial.C_mul (σ := Fin 4) (a := Complex.I) (a' := Complex.I)).symm
          simp [hC]
        _ = (-1 : R4) := by
          simp [Complex.I_mul_I]
    set i : R4 := I4c Complex.I
    have hi2 : i ^ 2 = (-1 : R4) := by
      have hi2' : i * i = (-1 : R4) := by simpa [i] using hI2
      simp [pow_two, hi2']
    have huv : u * v = (x4 0) ^ 2 + (x4 1) ^ 2 := by
      calc
        u * v = (x4 0 + i * x4 1) * (x4 0 - i * x4 1) := by simp [u, v, i]
        _ = (x4 0) ^ 2 - (i ^ 2) * (x4 1) ^ 2 := by
          ring
        _ = (x4 0) ^ 2 - (-1 : R4) * (x4 1) ^ 2 := by simp [hi2]
        _ = (x4 0) ^ 2 + (x4 1) ^ 2 := by
          ring
    have hcd : c * d = (x4 2) ^ 2 + (x4 3) ^ 2 := by
      calc
        c * d = (x4 2 + i * x4 3) * (x4 2 - i * x4 3) := by simp [c, d, i]
        _ = (x4 2) ^ 2 - (i ^ 2) * (x4 3) ^ 2 := by
          ring
        _ = (x4 2) ^ 2 - (-1 : R4) * (x4 3) ^ 2 := by simp [hi2]
        _ = (x4 2) ^ 2 + (x4 3) ^ 2 := by
          ring
    have hrel : (x4 0) ^ 2 + (x4 1) ^ 2 = -((x4 2) ^ 2 + (x4 3) ^ 2) := by
      have h := quadric_relation_R4
      have h' : ((x4 0) ^ 2 + (x4 1) ^ 2) + ((x4 2) ^ 2 + (x4 3) ^ 2) = 0 := by
        simpa [add_assoc] using h
      exact eq_neg_of_add_eq_zero_left h'
    -- Combine the expansions with the quadric relation.
    simpa [huv, hcd] using hrel

  have u_dvd_c_mul_d : u ∣ c * d := by
    refine ⟨-v, ?_⟩
    have hneg : -(u * v) = c * d := by
      -- Negate `u*v = -(c*d)` and simplify.
      rw [u_mul_v_eq_neg_c_mul_d]
      exact neg_neg (c * d)
    have : u * (-v) = c * d := (mul_neg u v).trans hneg
    exact this.symm

  -- A single evaluation map used to show `u ∤ c` and `u ∤ d`.
  let S1 : Type := MvPolynomial (Fin 1) ℂ
  let x : S1 := X 0
  let J : Ideal S1 := Ideal.span ({x ^ 2} : Set S1)
  let T : Type := S1 ⧸ J
  let evalS : MvPolynomial (Fin 4) ℂ →+* T :=
    MvPolynomial.eval₂Hom (algebraMap ℂ T) (fun i : Fin 4 =>
      match (i : Fin 4) with
      | 0 => 0
      | 1 => 0
      | 2 => Ideal.Quotient.mk J x
      | 3 => 0)
  have hq : evalS q4 = 0 := by
    have hx2 : (Ideal.Quotient.mk J (x ^ 2) : T) = 0 := by
      simp [J]
    have hx2' : (Ideal.Quotient.mk J x : T) ^ 2 = 0 := by
      have hmap : (Ideal.Quotient.mk J (x ^ 2) : T) = (Ideal.Quotient.mk J x : T) ^ 2 := by
        exact (Ideal.Quotient.mk J).map_pow x 2
      simpa [hmap] using hx2
    simp [q4, evalS, Fin.sum_univ_four, hx2', x, J]
  let φ : R4 →+* T :=
    Ideal.Quotient.lift I4 evalS <| by
      intro a ha
      rcases (Ideal.mem_span_singleton'.1 ha) with ⟨t, rfl⟩
      simp [map_mul, hq]
  have hφ_mk (p : MvPolynomial (Fin 4) ℂ) : φ ((Ideal.Quotient.mk I4) p) = evalS p := by
    rfl
  have hφx0 : φ (x4 0) = 0 := by
    dsimp [x4]
    calc
      φ ((Ideal.Quotient.mk I4) (X (0 : Fin 4))) = evalS (X (0 : Fin 4)) := hφ_mk _
      _ = 0 := by simp [evalS]
  have hφx1 : φ (x4 1) = 0 := by
    dsimp [x4]
    calc
      φ ((Ideal.Quotient.mk I4) (X (1 : Fin 4))) = evalS (X (1 : Fin 4)) := hφ_mk _
      _ = 0 := by simp [evalS]
  have hφx2 : φ (x4 2) = Ideal.Quotient.mk J x := by
    dsimp [x4]
    calc
      φ ((Ideal.Quotient.mk I4) (X (2 : Fin 4))) = evalS (X (2 : Fin 4)) := hφ_mk _
      _ = Ideal.Quotient.mk J x := by simp [evalS]
  have hφx3 : φ (x4 3) = 0 := by
    dsimp [x4]
    calc
      φ ((Ideal.Quotient.mk I4) (X (3 : Fin 4))) = evalS (X (3 : Fin 4)) := hφ_mk _
      _ = 0 := by simp [evalS]
  have hφi : φ (I4c Complex.I) = algebraMap ℂ T Complex.I := by
    dsimp [I4c]
    calc
      φ ((Ideal.Quotient.mk I4) (C Complex.I)) = evalS (C Complex.I) := hφ_mk _
      _ = algebraMap ℂ T Complex.I := by simp [evalS]
  have hφu : φ u = 0 := by
    -- `u ↦ 0`.
    dsimp [u]
    rw [map_add φ (x4 0) (I4c Complex.I * x4 1), hφx0]
    simp
    rw [hφx1]
    simp
  have hφc : φ c = Ideal.Quotient.mk J x := by
    -- `c ↦ x̄`.
    dsimp [c]
    rw [map_add φ (x4 2) (I4c Complex.I * x4 3), hφx2]
    have : φ (I4c Complex.I * x4 3) = 0 := by
      rw [map_mul φ (I4c Complex.I) (x4 3), hφx3]
      simp
    simp [this]
  have hφd : φ d = Ideal.Quotient.mk J x := by
    -- `d ↦ x̄`.
    dsimp [d]
    rw [map_sub φ (x4 2) (I4c Complex.I * x4 3), hφx2]
    have : φ (I4c Complex.I * x4 3) = 0 := by
      rw [map_mul φ (I4c Complex.I) (x4 3), hφx3]
      simp
    simp [this]

  have hxbar_ne : (Ideal.Quotient.mk J x : T) ≠ 0 := by
    -- If `x̄ = 0` in `ℂ[x]/(x^2)`, then `x^2 ∣ x`, forcing `x` to be a unit.
    have hx0 : (Ideal.Quotient.mk J x : T) = 0 ↔ x ^ 2 ∣ x := by
      simpa [J] using (Ideal.Quotient.eq_zero_iff_dvd (x := x ^ 2) (y := x))
    intro hx
    have hxdiv : x ^ 2 ∣ x := (hx0.mp hx)
    rcases hxdiv with ⟨t, ht⟩
    have hx_ne : x ≠ (0 : S1) := X_ne_zero (R := ℂ) (s := (0 : Fin 1))
    have hx_isUnit : IsUnit x := by
      have ht' : x = x * (x * t) := by
        simpa [pow_two, mul_assoc] using ht
      have h1 : (1 : S1) = x * t := by
        apply mul_left_cancel₀ hx_ne
        calc
          x * 1 = x := by simp
          _ = x * (x * t) := by simpa [mul_assoc] using ht'
      refine ⟨⟨x, t, ?_, ?_⟩, rfl⟩
      · exact h1.symm
      ·
        calc
          t * x = x * t := by simp [mul_comm]
          _ = 1 := h1.symm
    -- But `x` evaluates to `0` at the origin, so it is not a unit.
    let ev0 : S1 →+* ℂ :=
      MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun _ : Fin 1 => (0 : ℂ))
    have hx0' : ev0 x = (0 : ℂ) := by
      dsimp [ev0, x]
      exact
        (MvPolynomial.eval₂Hom_X' (f := RingHom.id ℂ) (g := fun _ : Fin 1 => (0 : ℂ))
          (i := (0 : Fin 1)))
    have h0 : IsUnit (0 : ℂ) := by
      simpa [hx0'] using (hx_isUnit.map ev0)
    exact not_isUnit_zero h0

  have u_not_dvd_c : ¬ u ∣ c := by
    intro hu
    rcases hu with ⟨t, ht⟩
    have hdiv : φ u ∣ φ c := by
      refine ⟨φ t, ?_⟩
      simp [map_mul, ht]
    have : (Ideal.Quotient.mk J x : T) = 0 := by
      rcases hdiv with ⟨w, hw⟩
      have : φ c = 0 := by simpa [hφu] using hw
      simpa [hφc] using this
    exact hxbar_ne this

  have u_not_dvd_d : ¬ u ∣ d := by
    intro hu
    rcases hu with ⟨t, ht⟩
    have hdiv : φ u ∣ φ d := by
      refine ⟨φ t, ?_⟩
      simp [map_mul, ht]
    have : (Ideal.Quotient.mk J x : T) = 0 := by
      rcases hdiv with ⟨w, hw⟩
      have : φ d = 0 := by simpa [hφu] using hw
      simpa [hφd] using this
    exact hxbar_ne this

  /-
  Coefficient bookkeeping for the 4-variable quadric:
  multiples of `q4 = ∑ i, X i ^ 2` have no coefficients on squarefree monomials
  (i.e. monomials where all exponents are ≤ 1).
  -/

  have coeff_q4_eq_zero_of_forall_le_one (m : Fin 4 →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
      (MvPolynomial.coeff m q4 : ℂ) = 0 := by
    classical
    have h0 : (fun₀ | (0 : Fin 4) => 2) ≠ m := by
      intro h
      have : (2 : ℕ) = m (0 : Fin 4) := by
        simpa using congrArg (fun f : Fin 4 →₀ ℕ => f (0 : Fin 4)) h
      have : (2 : ℕ) ≤ 1 := by
        simpa [this.symm] using (hm (0 : Fin 4))
      exact Nat.not_succ_le_self 1 this
    have h1 : (fun₀ | (1 : Fin 4) => 2) ≠ m := by
      intro h
      have : (2 : ℕ) = m (1 : Fin 4) := by
        simpa using congrArg (fun f : Fin 4 →₀ ℕ => f (1 : Fin 4)) h
      have : (2 : ℕ) ≤ 1 := by
        simpa [this.symm] using (hm (1 : Fin 4))
      exact Nat.not_succ_le_self 1 this
    have h2 : (fun₀ | (2 : Fin 4) => 2) ≠ m := by
      intro h
      have : (2 : ℕ) = m (2 : Fin 4) := by
        simpa using congrArg (fun f : Fin 4 →₀ ℕ => f (2 : Fin 4)) h
      have : (2 : ℕ) ≤ 1 := by
        simpa [this.symm] using (hm (2 : Fin 4))
      exact Nat.not_succ_le_self 1 this
    have h3 : (fun₀ | (3 : Fin 4) => 2) ≠ m := by
      intro h
      have : (2 : ℕ) = m (3 : Fin 4) := by
        simpa using congrArg (fun f : Fin 4 →₀ ℕ => f (3 : Fin 4)) h
      have : (2 : ℕ) ≤ 1 := by
        simpa [this.symm] using (hm (3 : Fin 4))
      exact Nat.not_succ_le_self 1 this
    simp [q4, Fin.sum_univ_four, MvPolynomial.coeff_add, MvPolynomial.coeff_X_pow, h0, h1, h2, h3]

  have coeff_mul_q4_eq_zero_of_forall_le_one (t : MvPolynomial (Fin 4) ℂ)
      (m : Fin 4 →₀ ℕ) (hm : ∀ i, m i ≤ 1) :
      (MvPolynomial.coeff m (t * q4) : ℂ) = 0 := by
    classical
    simp [MvPolynomial.coeff_mul]
    refine Finset.sum_eq_zero ?_
    intro ab hab
    have hab' : ab.1 + ab.2 = m :=
      (Finset.HasAntidiagonal.mem_antidiagonal (n := m) (a := ab)).1 hab
    have hle : ∀ i, ab.2 i ≤ 1 := by
      intro i
      have : ab.2 i ≤ m i := by
        have hm' : m i = ab.1 i + ab.2 i := by
          simpa [Finsupp.add_apply] using congrArg (fun f : Fin 4 →₀ ℕ => f i) hab'.symm
        exact hm' ▸ Nat.le_add_left _ _
      exact le_trans this (hm i)
    simp [coeff_q4_eq_zero_of_forall_le_one (m := ab.2) hle]

  intro hufm
  haveI : UniqueFactorizationMonoid R4 := by
    simpa [R4] using hufm
  have hu_irred : Irreducible u := by
    classical
    haveI : IsDomain R4 := by
      -- `R4` is definitionally `R 4`.
      simpa [R4] using (inferInstance : IsDomain (R 4))

    -- `u` is not a unit since `φ u = 0` in a nontrivial ring.
    haveI : Nontrivial T := ⟨⟨(Ideal.Quotient.mk J x : T), 0, hxbar_ne⟩⟩
    have hu_not_isUnit : ¬ IsUnit u := by
      intro hu
      have hunit : IsUnit (φ u) := hu.map φ
      rw [hφu] at hunit
      exact not_isUnit_zero hunit

    -- `u ≠ 0`: otherwise `c*d = 0`, contradicting `φ c = x̄ ≠ 0` and `φ d = x̄ ≠ 0`.
    have hc_ne0 : c ≠ 0 := by
      intro hc
      have : (Ideal.Quotient.mk J x : T) = 0 := by
        have := congrArg φ hc
        simpa [hφc] using this
      exact hxbar_ne this
    have hd_ne0 : d ≠ 0 := by
      intro hd
      have : (Ideal.Quotient.mk J x : T) = 0 := by
        have := congrArg φ hd
        simpa [hφd] using this
      exact hxbar_ne this
    have hu_ne0 : u ≠ 0 := by
      intro hu0
      rcases u_dvd_c_mul_d with ⟨t, ht⟩
      have hcd0 : c * d = 0 := by simpa [hu0] using ht
      rcases mul_eq_zero.mp hcd0 with hc0 | hd0
      · exact hc_ne0 hc0
      · exact hd_ne0 hd0

    -- The “scaling” homomorphism `R4 → R4[X]` sending each variable `xᵢ` to `X * xᵢ`.
    -- It remembers the total degree: a factorization of a degree-1 element forces
    -- one factor to be degree-0, hence a (nonzero) scalar unit.
    let f : MvPolynomial (Fin 4) ℂ →+* Polynomial R4 :=
      MvPolynomial.eval₂Hom (algebraMap ℂ (Polynomial R4))
        (fun i : Fin 4 => Polynomial.X * Polynomial.C (x4 i))
    have hf_q4 : f q4 = 0 := by
      -- Use `∑ xᵢ^2 = 0` in `R4` to show the substituted polynomial is zero.
      have hxsum : (∑ i : Fin 4, (x4 i) ^ 2 : R4) = 0 := by
        simpa [Fin.sum_univ_four] using quadric_relation_R4
      calc
        f q4 = ∑ i : Fin 4, (Polynomial.X * Polynomial.C (x4 i)) ^ 2 := by
          simp [f, q4, map_sum]
        _ = ∑ i : Fin 4, (Polynomial.X ^ 2) * (Polynomial.C (x4 i) ^ 2) := by
          classical
          refine Finset.sum_congr rfl ?_
          intro i hi
          -- `(X * C a)^2 = X^2 * (C a)^2`
          simp [pow_two]
          ring
        _ = (Polynomial.X ^ 2) * ∑ i : Fin 4, (Polynomial.C (x4 i) ^ 2) := by
          classical
          -- Factor out the scalar multiplier.
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin 4))) (a := (Polynomial.X ^ 2))
              (f := fun i : Fin 4 => (Polynomial.C (x4 i) ^ 2))).symm
        _ = (Polynomial.X ^ 2) * Polynomial.C (∑ i : Fin 4, (x4 i) ^ 2) := by
          classical
          simp [map_sum, map_pow]
        _ = 0 := by
          simp [hxsum]
    let τ : R4 →+* Polynomial R4 :=
      Ideal.Quotient.lift I4 f <| by
        intro a ha
        rcases (Ideal.mem_span_singleton'.1 ha) with ⟨t, rfl⟩
        calc
          f (t * q4) = f t * f q4 := by simp [map_mul]
          _ = f t * 0 := by simp [hf_q4]
          _ = 0 := by simp
    have hτ_mk (p : MvPolynomial (Fin 4) ℂ) : τ ((Ideal.Quotient.mk I4) p) = f p := by
      rfl

    let ev0 : Polynomial R4 →+* R4 := Polynomial.eval₂RingHom (RingHom.id R4) 0
    let ev1 : Polynomial R4 →+* R4 := Polynomial.eval₂RingHom (RingHom.id R4) 1

    have hev1_f : (ev1.comp f) = (Ideal.Quotient.mk I4) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        -- `algebraMap` into the quotient is `mk` composed with `C`.
        have halg :
            (algebraMap ℂ R4) r = (Ideal.Quotient.mk I4) (C r) := by
          simpa [MvPolynomial.algebraMap_eq] using
            (congrArg (fun g : ℂ →+* R4 => g r)
              (Ideal.Quotient.mk_comp_algebraMap ℂ (A := MvPolynomial (Fin 4) ℂ) (I := I4))).symm
        -- Evaluate the constant polynomial.
        simpa [f, ev1, Polynomial.algebraMap_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
          halg]
      · intro i
        -- Evaluate at `X = 1`.
        calc
          (ev1.comp f) (X i) = ev1 (f (X i)) := rfl
          _ = ev1 (Polynomial.X * Polynomial.C (x4 i)) := by simp [f]
          _ = (1 : R4) * x4 i := by
            simp [ev1, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_X,
              Polynomial.eval₂_C]
          _ = x4 i := by simp
          _ = (Ideal.Quotient.mk I4) (X i) := by simp [x4]
    have hev0_f :
        (ev0.comp f) =
          (MvPolynomial.eval₂Hom (algebraMap ℂ R4) (fun _ : Fin 4 => (0 : R4))) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [f, ev0, Polynomial.algebraMap_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      · intro i
        -- Evaluate at `X = 0`.
        -- both sides are `0`, since variables are sent to `0`.
        simp [f, ev0, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_X,
          Polynomial.eval₂_C]

    have hev1_τ (z : R4) : ev1 (τ z) = z := by
      rcases (Ideal.Quotient.mk_surjective (I := I4) z) with ⟨p, rfl⟩
      simpa [τ, hτ_mk] using congrArg (fun g : MvPolynomial (Fin 4) ℂ →+* R4 => g p) hev1_f
    have hev0_τ_mk (p : MvPolynomial (Fin 4) ℂ) :
        ev0 (τ ((Ideal.Quotient.mk I4) p)) = I4c (MvPolynomial.constantCoeff p) := by
      -- Evaluate `f` at `X=0` (variables go to `0`), giving the constant coefficient.
      have hcomp := congrArg (fun g : MvPolynomial (Fin 4) ℂ →+* R4 => g p) hev0_f
      have :
          ev0 (f p) = (algebraMap ℂ R4) (MvPolynomial.constantCoeff p) := by
        have h' :
            ev0 (f p) =
              (MvPolynomial.eval₂Hom (algebraMap ℂ R4) (fun _ : Fin 4 => (0 : R4))) p := by
          simpa [RingHom.comp_apply] using hcomp
        have hzero :
            (MvPolynomial.eval₂Hom (algebraMap ℂ R4) (fun _ : Fin 4 => (0 : R4))) p =
              (algebraMap ℂ R4) (MvPolynomial.constantCoeff p) := by
          simp
        exact h'.trans hzero
      -- Convert `algebraMap` to the local notation `I4c`.
      have halg :
          (algebraMap ℂ R4) (MvPolynomial.constantCoeff p) =
            I4c (MvPolynomial.constantCoeff p) := by
        -- `algebraMap` into the quotient is `mk` composed with `C`.
        have halg' :
            (algebraMap ℂ R4) (MvPolynomial.constantCoeff p) =
              (Ideal.Quotient.mk I4) (C (MvPolynomial.constantCoeff p)) := by
          simpa [MvPolynomial.algebraMap_eq] using
            (congrArg (fun g : ℂ →+* R4 => g (MvPolynomial.constantCoeff p))
              (Ideal.Quotient.mk_comp_algebraMap ℂ (A := MvPolynomial (Fin 4) ℂ) (I := I4))).symm
        simpa [I4c] using halg'
      simp [hτ_mk, this, halg]

    -- `τ` sends the linear form `u` to `X * C(u)`, hence has `natDegree = 1`.
    have hτu : τ u = Polynomial.X * Polynomial.C u := by
      -- Reduce to the computation on generators.
      have hτx (i : Fin 4) : τ (x4 i) = Polynomial.X * Polynomial.C (x4 i) := by
        simp [x4, hτ_mk, f]
      have hτc (z : ℂ) : τ (I4c z) = Polynomial.C (I4c z) := by
        -- `f (C z)` is a constant polynomial.
        dsimp [I4c]
        have halg :
            (algebraMap ℂ R4) z = (Ideal.Quotient.mk I4) (C z) := by
          simpa [MvPolynomial.algebraMap_eq] using
            (congrArg (fun g : ℂ →+* R4 => g z)
              (Ideal.Quotient.mk_comp_algebraMap ℂ (A := MvPolynomial (Fin 4) ℂ) (I := I4))).symm
        simp [hτ_mk, f, Polynomial.algebraMap_apply, halg]
      dsimp [u]
      -- Linearity computation, factoring out `X`.
      calc
        τ (x4 0 + I4c Complex.I * x4 1) =
            τ (x4 0) + τ (I4c Complex.I) * τ (x4 1) := by simp [map_add, map_mul]
        _ = Polynomial.X * Polynomial.C (x4 0) +
              (Polynomial.C (I4c Complex.I) * (Polynomial.X * Polynomial.C (x4 1))) := by
              simp [hτx, hτc]
        _ = Polynomial.X * Polynomial.C (x4 0) +
              Polynomial.X * (Polynomial.C (I4c Complex.I) * Polynomial.C (x4 1)) := by
              ring
        _ = Polynomial.X * (Polynomial.C (x4 0) + Polynomial.C (I4c Complex.I) * Polynomial.C (x4 1)) := by
              ring
        _ = Polynomial.X * Polynomial.C (x4 0 + I4c Complex.I * x4 1) := by
              simp [map_add, map_mul]
    have hτu_ne0 : (τ u) ≠ 0 := by
      intro h0
      have : u = 0 := by simpa [hev1_τ u] using congrArg ev1 h0
      exact hu_ne0 this
    have hCu_ne0 : (Polynomial.C u : Polynomial R4) ≠ 0 := by
      simpa [Polynomial.C_eq_zero] using hu_ne0
    have hτu_natDegree : (τ u).natDegree = 1 := by
      -- `natDegree (X * C u) = 1`.
      have := Polynomial.natDegree_X_mul (p := (Polynomial.C u : Polynomial R4)) hCu_ne0
      simpa [hτu, Polynomial.natDegree_C] using this

    have isUnit_of_natDegree_τ_eq_zero {z : R4} (hz : (τ z).natDegree = 0) (hz0 : z ≠ 0) :
        IsUnit z := by
      rcases (Ideal.Quotient.mk_surjective (I := I4) z) with ⟨p, rfl⟩
      -- `τ (mk p)` is a constant polynomial.
      rcases (Polynomial.natDegree_eq_zero).1 hz with ⟨r, hr⟩
      have ev0_C (s : R4) : ev0 (Polynomial.C s) = s := by
        simp [ev0, Polynomial.coe_eval₂RingHom]
      have ev1_C (s : R4) : ev1 (Polynomial.C s) = s := by
        simp [ev1, Polynomial.coe_eval₂RingHom]
      have hr1 : r = (Ideal.Quotient.mk I4) p := by
        have := congrArg ev1 hr
        simpa [ev1_C, hev1_τ] using this
      have hscalar : (Ideal.Quotient.mk I4) p = I4c (MvPolynomial.constantCoeff p) := by
        have := congrArg ev0 hr
        -- Left side gives `r`, right side gives constant-coefficient evaluation.
        simpa [ev0_C, hr1, hev0_τ_mk] using this
      have hcc_ne0 : MvPolynomial.constantCoeff p ≠ 0 := by
        intro h0
        apply hz0
        simp [hscalar, h0, I4c]
      have hunit_cc : IsUnit (MvPolynomial.constantCoeff p) := (isUnit_iff_ne_zero).2 hcc_ne0
      have hunit_scalar : IsUnit (I4c (MvPolynomial.constantCoeff p)) := by
        -- Map the unit from `ℂ` through `C` and then to the quotient.
        have : IsUnit (C (MvPolynomial.constantCoeff p) : MvPolynomial (Fin 4) ℂ) :=
          hunit_cc.map (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 4) ℂ)
        have : IsUnit ((Ideal.Quotient.mk I4) (C (MvPolynomial.constantCoeff p)) : R4) :=
          this.map (Ideal.Quotient.mk I4 : MvPolynomial (Fin 4) ℂ →+* R4)
        simpa [I4c] using this
      simpa [hscalar] using hunit_scalar

    refine ⟨hu_not_isUnit, ?_⟩
    intro a b hab
    have habτ : τ u = τ a * τ b := by simpa [map_mul] using congrArg τ hab
    have ha0 : τ a ≠ 0 := by
      intro ha0
      have : a = 0 := by simpa [hev1_τ a] using congrArg ev1 ha0
      exact hu_ne0 (by simpa [this] using hab)
    have hb0 : τ b ≠ 0 := by
      intro hb0
      have : b = 0 := by simpa [hev1_τ b] using congrArg ev1 hb0
      exact hu_ne0 (by simpa [this] using hab)
    have hdeg :
        (τ a).natDegree + (τ b).natDegree = 1 := by
      have hmul :
          (τ a * τ b).natDegree = (τ a).natDegree + (τ b).natDegree :=
        (Polynomial.natDegree_mul ha0 hb0)
      have hdeg' : (τ u).natDegree = (τ a * τ b).natDegree := congrArg Polynomial.natDegree habτ
      calc
        (τ a).natDegree + (τ b).natDegree = (τ a * τ b).natDegree := by
          exact hmul.symm
        _ = (τ u).natDegree := by
          exact hdeg'.symm
        _ = 1 := hτu_natDegree
    rcases (Nat.add_eq_one_iff).1 hdeg with h | h
    · left
      exact isUnit_of_natDegree_τ_eq_zero h.1 (by
        intro ha
        exact hu_ne0 (by simpa [ha] using hab))
    · right
      exact isUnit_of_natDegree_τ_eq_zero h.2 (by
        intro hb
        exact hu_ne0 (by simpa [hb] using hab))
  have hu_prime : Prime u := (UniqueFactorizationMonoid.irreducible_iff_prime).1 hu_irred
  have : u ∣ c ∨ u ∣ d := hu_prime.dvd_or_dvd u_dvd_c_mul_d
  exact this.elim u_not_dvd_c u_not_dvd_d

/--
Let \( R = \mathbb{C}[x_1, \dots, x_n]/(x_1^2 + x_2^2 + \dots + x_n^2) \).
Then \( R \) is not a unique factorization domain for \( n = 3 \) or \( 4 \).-/
theorem not_UFD_of_3_or_4 (n : ℕ) (h : n = 3 ∨ n = 4) [IsDomain (R n)] :
    ¬ UniqueFactorizationMonoid (R n) := by
  rcases h with rfl | rfl
  · simpa using (not_UFD_R3)
  · simpa using (not_UFD_R4)

end
end Quadric

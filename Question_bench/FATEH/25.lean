import Mathlib

open Polynomial

/-- Multiples of `X` inside `ℚ[X]`. -/
def XMultiples : Set ℚ[X] := {f | ∃ h : ℚ[X], f = X * h}

abbrev R : Subalgebra ℤ ℚ[X] := Algebra.adjoin ℤ XMultiples

/-- Elements of `R` have integer constant coefficient. -/
lemma constantCoeff_mem_int {p : ℚ[X]} (hp : p ∈ R) :
    ∃ z : ℤ, constantCoeff p = (z : ℚ) := by
  classical
  refine Algebra.adjoin_induction (s := XMultiples)
      (p := fun x _ => ∃ z : ℤ, constantCoeff x = (z : ℚ)) ?mem ?alg ?add ?mul hp
  · intro x hx
    rcases hx with ⟨h, rfl⟩
    refine ⟨0, ?_⟩
    simp [Polynomial.constantCoeff, coeff_X]
  · intro r
    refine ⟨r, ?_⟩
    simp [Polynomial.constantCoeff]
  · intro x y hx hy hx' hy'
    rcases hx' with ⟨zx, hx'⟩
    rcases hy' with ⟨zy, hy'⟩
    refine ⟨zx + zy, ?_⟩
    calc
      constantCoeff (x + y) = constantCoeff x + constantCoeff y := by
        simp [Polynomial.constantCoeff]
      _ = (zx : ℚ) + (zy : ℚ) := by
        simp [hx', hy']
      _ = ((zx + zy : ℤ) : ℚ) := by
        simp [Int.cast_add]
  · intro x y hx hy hx' hy'
    rcases hx' with ⟨zx, hx'⟩
    rcases hy' with ⟨zy, hy'⟩
    refine ⟨zx * zy, ?_⟩
    calc
      constantCoeff (x * y) = constantCoeff x * constantCoeff y := by
        simp [Polynomial.constantCoeff]
      _ = (zx : ℚ) * (zy : ℚ) := by
        simp [hx', hy']
      _ = ((zx * zy : ℤ) : ℚ) := by
        simp [Int.cast_mul]

/-- No integer equals `1/2` in `ℚ`. -/
lemma int_cast_ne_half (z : ℤ) : (z : ℚ) ≠ (1 / 2 : ℚ) := by
  intro hz
  have hz' : (2 * (z : ℚ)) = (1 : ℚ) := by
    nlinarith [hz]
  have hz'' : (2 * z : ℤ) = 1 := by
    exact_mod_cast hz'
  have hdiv : (2 : ℤ) ∣ 1 := by
    refine ⟨z, ?_⟩
    simpa using hz''.symm
  have hnot : ¬ (2 : ℤ) ∣ 1 := by
    decide
  exact hnot hdiv

/-- `2` is not a unit in `R` since its inverse would have constant term `1/2`. -/
lemma two_not_unit : ¬ IsUnit (2 : R) := by
  intro hunit
  rcases IsUnit.exists_right_inv hunit with ⟨u, hu⟩
  obtain ⟨z, hz⟩ := constantCoeff_mem_int (p := (u : ℚ[X])) u.property
  have hu' : (2 : ℚ[X]) * (u : ℚ[X]) = 1 := by
    simpa using congrArg Subtype.val hu
  have hmul : (2 : ℚ) * constantCoeff (u : ℚ[X]) = 1 := by
    calc
      (2 : ℚ) * constantCoeff (u : ℚ[X])
          = constantCoeff (2 : ℚ[X]) * constantCoeff (u : ℚ[X]) := by
              simp [Polynomial.constantCoeff]
      _ = constantCoeff ((2 : ℚ[X]) * (u : ℚ[X])) := by
              exact
                (RingHom.map_mul (Polynomial.constantCoeff) (2 : ℚ[X]) (u : ℚ[X])).symm
      _ = constantCoeff (1 : ℚ[X]) := by
              simpa using congrArg (constantCoeff : ℚ[X] → ℚ) hu'
      _ = 1 := by
              simp [Polynomial.constantCoeff]
  have hconst : constantCoeff (u : ℚ[X]) = (1 / 2 : ℚ) := by
    nlinarith [hmul]
  have : (z : ℚ) = (1 / 2 : ℚ) := by
    simpa [hz] using hconst
  exact int_cast_ne_half z this

/-- Powers of two are nonzero in `ℚ`, hence `1 / 2^n ≠ 0`. -/
lemma one_div_pow_two_ne_zero (n : ℕ) : (1 / (2^n : ℚ)) ≠ 0 := by
  have hpow : (2^n : ℚ) ≠ 0 := by
    exact pow_ne_zero _ (by norm_num)
  exact one_div_ne_zero hpow

/-- The polynomial `X * C a` is nonzero when `a ≠ 0`. -/
lemma X_mul_C_ne_zero {a : ℚ} (ha : a ≠ 0) : (X * C a : ℚ[X]) ≠ 0 := by
  have hx : (X : ℚ[X]) ≠ 0 := by
    exact (X_ne_zero : (X : ℚ[X]) ≠ 0)
  have hc : (C a : ℚ[X]) ≠ 0 := by
    simpa [Polynomial.C_eq_zero] using ha
  exact mul_ne_zero hx hc

/-- The chain element `X / 2^n` inside `R`. -/
noncomputable def f (n : ℕ) : R := by
  refine ⟨X * C (1 / (2^n : ℚ)), ?_⟩
  refine Algebra.subset_adjoin ?_
  exact ⟨C (1 / (2^n : ℚ)), rfl⟩

/-- A handy normal form for `f n` as a scalar multiple of `X`. -/
lemma f_eq_smul_X (n : ℕ) : (f n : ℚ[X]) = (1 / (2^n : ℚ)) • X := by
  dsimp [f]
  rw [X_mul_C]
  simpa using (Polynomial.C_mul' (R:=ℚ) (1 / (2^n : ℚ)) X)

/-- Arithmetic step: `2 * (1 / 2^(n+1)) = 1 / 2^n`. -/
lemma two_mul_one_div_pow_succ (n : ℕ) :
    (2 : ℚ) * (1 / (2^(n + 1) : ℚ)) = (1 / (2^n : ℚ)) := by
  field_simp [pow_succ]
  simp [pow_succ, mul_comm]

/-- Scalar multiplication by `2` is multiplication by the constant polynomial `2`. -/
lemma smul_two_eq_mul (p : ℚ[X]) : (2 : ℚ) • p = p * (2 : ℚ[X]) := by
  calc
    (2 : ℚ) • p = (C (2 : ℚ) : ℚ[X]) * p := by
      symm
      simpa using (Polynomial.C_mul' (R:=ℚ) (2 : ℚ) p)
    _ = p * (2 : ℚ[X]) := by
      have h : (C (2 : ℚ) : ℚ[X]) * p = p * C (2 : ℚ) := by
        simpa using (mul_comm (C (2 : ℚ) : ℚ[X]) p)
      simpa using h

/-- `f n` is never zero in `R`. -/
lemma f_ne_zero (n : ℕ) : (f n : R) ≠ 0 := by
  intro hzero
  have hpoly : (X * C (1 / (2^n : ℚ)) : ℚ[X]) = 0 := by
    simpa [f] using congrArg Subtype.val hzero
  have hnonzero : (X * C (1 / (2^n : ℚ)) : ℚ[X]) ≠ 0 := by
    exact X_mul_C_ne_zero (one_div_pow_two_ne_zero n)
  exact hnonzero hpoly

/-- Multiplication by `2` steps down the chain: `f n = f (n+1) * 2`. -/
lemma f_eq_mul_two (n : ℕ) : (f n : R) = f (n + 1) * (2 : R) := by
  apply Subtype.ext
  calc
    (f n : ℚ[X])
        = (1 / (2^n : ℚ)) • X := f_eq_smul_X n
    _ = ((2 : ℚ) * (1 / (2^(n + 1) : ℚ))) • X := by
        congr 1
        simpa using (two_mul_one_div_pow_succ n).symm
    _ = (2 : ℚ) • (f (n + 1) : ℚ[X]) := by
        symm
        simp [f_eq_smul_X, smul_smul]
    _ = (f (n + 1) : ℚ[X]) * (2 : ℚ[X]) := by
        simpa using (smul_two_eq_mul (f (n + 1) : ℚ[X]))

/-- The chain witnesses strict divisibility by a nonunit. -/
lemma chain_dvdNotUnit (n : ℕ) : DvdNotUnit (f (n + 1)) (f n) := by
  refine ⟨f_ne_zero (n + 1), ?_⟩
  refine ⟨(2 : R), two_not_unit, ?_⟩
  exact f_eq_mul_two n

/-- The divisibility relation `DvdNotUnit` on `R` is not well-founded. -/
lemma not_wfDvdMonoid : ¬ IsWellFounded R DvdNotUnit := by
  intro h
  let S : Set R := {x | ∃ n, x = f n}
  have hnonempty : S.Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  obtain ⟨a, haS, hmin⟩ := h.wf.has_min S hnonempty
  rcases haS with ⟨n, rfl⟩
  have hrel : DvdNotUnit (f (n + 1)) (f n) := chain_dvdNotUnit n
  have : ¬ DvdNotUnit (f (n + 1)) (f n) := by
    apply hmin
    exact ⟨n + 1, rfl⟩
  exact this hrel

/--Let $R=\mathbb{Z}+x\mathbb{Q}[x]\subset \mathbb{Q}[x]$be the set of polynomials in x with rational coefficients
whose constant term is an integer. Prove that $R$ is not a U.F.D.-/
theorem not_uniqueFactorizationMonoid_adjoin_int : ¬ UniqueFactorizationMonoid
    (Algebra.adjoin ℤ ({f | ∃ h : ℚ[X], f = X * h} : Set ℚ[X])) := by
  classical
  change ¬ UniqueFactorizationMonoid R
  intro hufd
  haveI : UniqueFactorizationMonoid R := hufd
  have hWF : IsWellFounded R DvdNotUnit := by
    infer_instance
  exact not_wfDvdMonoid hWF

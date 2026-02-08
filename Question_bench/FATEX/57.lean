import Mathlib

open scoped Polynomial

/--
Let \( A \) be a domain and \( K \) its field of fractions.
\( x \in K \) is called almost integral if there exists an element \( r\in A, r \ne 0 \) such that \( rx^n \in A \) for all \( n \ge 0 \).
-/
def IsAlmostIntegral {A : Type} [CommRing A] [IsDomain A] (x : FractionRing A) : Prop :=
  ∃ r : A, r ≠ 0 ∧ ∀ n : ℕ, ∃ y : A, r • (x ^ n) = algebraMap A (FractionRing A) y

/--
\( A \) is called \textit{completely integrally closed} if every almost integral element of \( K \) is contained in \( A \).
-/
def IsCompletelyIntegrallyClosed (A : Type) [CommRing A] [IsDomain A] : Prop :=
  ∀ x : FractionRing A, IsAlmostIntegral x → ∃ y : A, x = algebraMap A (FractionRing A) y

/-- Almost-integral elements remain almost integral after mapping along an injective map of domains. -/
lemma IsAlmostIntegral.map_fractionRing_map {A B : Type} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] (j : A →+* B) (hj : Function.Injective j)
    {x : FractionRing A}
    (hx : IsAlmostIntegral (A := A) x) :
    IsAlmostIntegral (A := B)
      (x :=
        (IsFractionRing.map (A := A) (B := B) (K := FractionRing A) (L := FractionRing B) hj)
          x) := by
  classical
  rcases hx with ⟨r, hrne, hxn⟩
  refine ⟨j r, ?_, ?_⟩
  · intro hzero
    apply hrne
    apply hj
    simpa using hzero
  · intro n
    rcases hxn n with ⟨y, hy⟩
    refine ⟨j y, ?_⟩
    set φ :=
      (IsFractionRing.map (A := A) (B := B) (K := FractionRing A) (L := FractionRing B) hj)
    have hy' : φ (r • x ^ n) = φ (algebraMap A (FractionRing A) y) :=
      congrArg (fun z => φ z) hy
    have hy'' :
        algebraMap B (FractionRing B) (j r) * (φ x) ^ n =
          algebraMap B (FractionRing B) (j y) := by
      simpa [φ, Algebra.smul_def, IsFractionRing.map] using hy'
    simpa [Algebra.smul_def, φ] using hy''

/-- If the witness `r` is a unit, an almost integral element lies in the base ring. -/
lemma almostIntegral_eq_algebraMap_of_unit {A : Type} [CommRing A] [IsDomain A]
    {x : FractionRing A} {r : A}
    (hxn : ∀ n : ℕ, ∃ y : A, r • (x ^ n) = algebraMap A (FractionRing A) y)
    (hrunit : IsUnit r) :
    ∃ y : A, x = algebraMap A (FractionRing A) y := by
  classical
  rcases hrunit with ⟨u, rfl⟩
  rcases hxn 1 with ⟨y1, hy1⟩
  refine ⟨↑(u⁻¹) * y1, ?_⟩
  have hy1' :
      (algebraMap A (FractionRing A) (↑u)) * x =
        algebraMap A (FractionRing A) y1 := by
    simpa [Algebra.smul_def] using hy1
  have hu :
      IsUnit (algebraMap A (FractionRing A) (↑u)) := by
    exact IsUnit.map (algebraMap A (FractionRing A)) u.isUnit
  have hne :
      (algebraMap A (FractionRing A) (↑u)) ≠ 0 :=
    hu.ne_zero
  apply mul_left_cancel₀ (a := algebraMap A (FractionRing A) (↑u)) hne
  simpa [hy1', map_mul, mul_assoc, mul_left_comm, mul_comm] using
    (rfl :
      (algebraMap A (FractionRing A) (↑u)) * x =
        (algebraMap A (FractionRing A) (↑u)) * x)

/-- If `r * f^n` always lies in the image of `Polynomial.mapRingHom`, then the leading coefficient
is almost integral over the base ring. -/
lemma leadingCoeff_isAlmostIntegral_of_mul_pow_eq_map {A : Type} [CommRing A] [IsDomain A]
    {r : Polynomial A} {f : Polynomial (FractionRing A)}
    (hr : r ≠ 0)
    (hxn :
      ∀ n : ℕ,
        ∃ y : Polynomial A,
          (Polynomial.mapRingHom (algebraMap A (FractionRing A)) r) * f ^ n =
            Polynomial.mapRingHom (algebraMap A (FractionRing A)) y) :
    IsAlmostIntegral (A := A) (f.leadingCoeff : FractionRing A) := by
  classical
  refine ⟨r.leadingCoeff, ?_, ?_⟩
  · exact Polynomial.leadingCoeff_ne_zero.mpr hr
  · intro n
    rcases hxn n with ⟨y, hy⟩
    have hy' :
        (Polynomial.mapRingHom (algebraMap A (FractionRing A)) r).leadingCoeff *
            (f ^ n).leadingCoeff =
          (Polynomial.mapRingHom (algebraMap A (FractionRing A)) y).leadingCoeff := by
      simpa [Polynomial.leadingCoeff_mul] using
        congrArg Polynomial.leadingCoeff hy
    refine ⟨y.leadingCoeff, ?_⟩
    have hmap_r :
        (Polynomial.map (algebraMap A (FractionRing A)) r).leadingCoeff =
          algebraMap A (FractionRing A) r.leadingCoeff := by
      simpa using
        (Polynomial.leadingCoeff_map_of_injective (f := algebraMap A (FractionRing A))
          (IsFractionRing.injective A (FractionRing A)) (p := r))
    have hmap_y :
        (Polynomial.map (algebraMap A (FractionRing A)) y).leadingCoeff =
          algebraMap A (FractionRing A) y.leadingCoeff := by
      simpa using
        (Polynomial.leadingCoeff_map_of_injective (f := algebraMap A (FractionRing A))
          (IsFractionRing.injective A (FractionRing A)) (p := y))
    have hy'' :
        algebraMap A (FractionRing A) r.leadingCoeff * (f.leadingCoeff ^ n) =
          algebraMap A (FractionRing A) y.leadingCoeff := by
      simpa [Polynomial.mapRingHom, hmap_r, hmap_y, Polynomial.leadingCoeff_pow] using hy'
    simpa [Algebra.smul_def] using hy''

/-- Fixed-denominator almost-integrality is stable under subtracting a polynomial in the base ring. -/
lemma almostIntegralOverMap_sub {A : Type} [CommRing A] [IsDomain A]
    {r : Polynomial A} {f : Polynomial (FractionRing A)}
    (hxn :
      ∀ n : ℕ,
        ∃ y : Polynomial A,
          (Polynomial.mapRingHom (algebraMap A (FractionRing A)) r) * f ^ n =
            Polynomial.mapRingHom (algebraMap A (FractionRing A)) y)
    (p : Polynomial A) :
    ∀ n : ℕ,
      ∃ y : Polynomial A,
        (Polynomial.mapRingHom (algebraMap A (FractionRing A)) r) *
              (f - Polynomial.mapRingHom (algebraMap A (FractionRing A)) p) ^ n =
            Polynomial.mapRingHom (algebraMap A (FractionRing A)) y := by
  classical
  let j : Polynomial A →+* Polynomial (FractionRing A) :=
    Polynomial.mapRingHom (algebraMap A (FractionRing A))
  classical
  choose y hy using hxn
  intro n
  refine ⟨Finset.sum (Finset.range (n + 1))
      (fun k => (Nat.choose n k) • (y k * (-p) ^ (n - k))), ?_⟩
  have hpow :
      (f - j p) ^ n =
        Finset.sum (Finset.range (n + 1))
          (fun k => f ^ k * (-j p) ^ (n - k) * (Nat.choose n k)) := by
    simpa [sub_eq_add_neg] using (add_pow f (-j p) n)
  calc
    j r * (f - j p) ^ n
        = Finset.sum (Finset.range (n + 1))
            (fun k => j r * (f ^ k * (-j p) ^ (n - k) * (Nat.choose n k))) := by
          simp [hpow, Finset.mul_sum, mul_assoc]
    _ = Finset.sum (Finset.range (n + 1))
          (fun k => (Nat.choose n k) • ((j r * f ^ k) * (-j p) ^ (n - k))) := by
          simp [nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = Finset.sum (Finset.range (n + 1))
          (fun k => (Nat.choose n k) • (j (y k) * (j (-p)) ^ (n - k))) := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hyk : j r * f ^ k = j (y k) := hy k
          simp [hyk, map_neg]
    _ = j (Finset.sum (Finset.range (n + 1))
          (fun k => (Nat.choose n k) • (y k * (-p) ^ (n - k)))) := by
          simp [j, map_sum, map_mul, map_pow, map_neg, mul_comm, mul_left_comm, mul_assoc]

/-- The induced map on fraction rings sends `algebraMap` to `algebraMap`. -/
lemma fractionRing_map_algebraMap {A B K L : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [CommRing K] [Algebra A K] [IsFractionRing A K]
    [CommRing L] [Algebra B L] [IsFractionRing B L]
    (j : A →+* B) (hj : Function.Injective j) (a : A) :
    (IsFractionRing.map (A := A) (B := B) (K := K) (L := L) hj) (algebraMap A K a) =
      algebraMap B L (j a) := by
  classical
  have h1 :
      algebraMap A K a =
        IsLocalization.mk' K a (1 : nonZeroDivisors A) := by
    simp [IsLocalization.mk'_one]
  -- Rewrite using `IsLocalization.map_mk'`.
  rw [h1]
  dsimp [IsFractionRing.map]
  simp [IsLocalization.mk'_one]

/-- A fixed-denominator almost-integral polynomial over the fraction field descends to the base. -/
lemma polynomial_mem_map_of_almostIntegral_over_fractionRing {A : Type} [CommRing A] [IsDomain A]
    (h : IsCompletelyIntegrallyClosed A)
    {f : Polynomial (FractionRing A)}
    (hf :
      ∃ r : Polynomial A, r ≠ 0 ∧
        ∀ n : ℕ,
          ∃ y : Polynomial A,
            (Polynomial.mapRingHom (algebraMap A (FractionRing A)) r) * f ^ n =
              Polynomial.mapRingHom (algebraMap A (FractionRing A)) y) :
    ∃ g : Polynomial A,
      Polynomial.mapRingHom (algebraMap A (FractionRing A)) g = f := by
  classical
  let j : Polynomial A →+* Polynomial (FractionRing A) :=
    Polynomial.mapRingHom (algebraMap A (FractionRing A))
  let P : ℕ → Prop := fun n =>
    ∀ f : Polynomial (FractionRing A),
      f.natDegree = n →
      (∃ r : Polynomial A, r ≠ 0 ∧ ∀ n : ℕ, ∃ y : Polynomial A, j r * f ^ n = j y) →
      ∃ g : Polynomial A, j g = f
  have hP : ∀ n : ℕ, P n := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih f hfdeg hfprop
    by_cases hf0 : f = 0
    · refine ⟨0, ?_⟩
      simp [hf0, j]
    rcases hfprop with ⟨r, hrne, hxn⟩
    have hxn' : ∀ n : ℕ, ∃ y : Polynomial A, j r * f ^ n = j y := by
      simpa [j] using hxn
    have hlead :
        IsAlmostIntegral (A := A) (f.leadingCoeff : FractionRing A) :=
      leadingCoeff_isAlmostIntegral_of_mul_pow_eq_map (A := A) (r := r) (f := f) hrne hxn'
    rcases h (f.leadingCoeff) hlead with ⟨a, ha⟩
    let p : Polynomial A := Polynomial.monomial f.natDegree a
    let f' : Polynomial (FractionRing A) := f - j p
    have hcoeff_d : (f' ).coeff f.natDegree = 0 := by
      simp [f', j, p, ha, Polynomial.coeff_sub, Polynomial.coeff_natDegree]
    by_cases hf'0 : f' = 0
    · refine ⟨p, ?_⟩
      have hf'0' : f = j p := by
        simpa [f'] using (sub_eq_zero.mp hf'0)
      simpa [hf'0', j] using (rfl : j p = j p)
    · have hdeg' : f'.natDegree < f.natDegree := by
        refine (Polynomial.natDegree_lt_iff_degree_lt hf'0).2 ?_
        refine (Polynomial.degree_lt_iff_coeff_zero f' _).2 ?_
        intro m hm
        by_cases hmd : m = f.natDegree
        · subst hmd
          simpa using hcoeff_d
        · have hmgt : f.natDegree < m := lt_of_le_of_ne hm (Ne.symm hmd)
          have hfcoeff : f.coeff m = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt hmgt
          have hpcoeff : (j p).coeff m = 0 := by
            have hmd' : f.natDegree ≠ m := Ne.symm hmd
            simp [j, p, Polynomial.coeff_monomial, hmd']
          simp [f', Polynomial.coeff_sub, hfcoeff, hpcoeff]
      have hxn'' :
          ∀ n : ℕ, ∃ y : Polynomial A, j r * f' ^ n = j y := by
        simpa [j, f'] using (almostIntegralOverMap_sub (A := A) (r := r) (f := f) hxn' p)
      have ih' : ∃ g : Polynomial A, j g = f' := by
        have hdeg'' : f'.natDegree < n := by
          simpa [hfdeg] using hdeg'
        have := ih f'.natDegree hdeg'' f' rfl ⟨r, hrne, hxn''⟩
        exact this
      rcases ih' with ⟨g', hg'⟩
      refine ⟨g' + p, ?_⟩
      calc
        j (g' + p) = j g' + j p := by simp [j]
        _ = f' + j p := by simpa [hg']
        _ = f := by
          simp [f']
  have := hP f.natDegree f rfl ?_
  · exact this
  · rcases hf with ⟨r, hrne, hxn⟩
    exact ⟨r, hrne, by simpa [j] using hxn⟩

/-- Over a field, the polynomial ring is completely integrally closed. -/
lemma completelyIntegrallyClosed_polynomial_over_field {K : Type} [Field K] :
    IsCompletelyIntegrallyClosed (Polynomial K) := by
  intro x hx
  classical
  rcases hx with ⟨r, hrne, hxn⟩
  let ψ : FractionRing K[X] →+* RatFunc K :=
    (RatFunc.toFractionRingRingEquiv K).symm.toRingHom
  let y : RatFunc K := ψ x
  have hxn' :
      ∀ n : ℕ, ∃ s : K[X],
        algebraMap K[X] (RatFunc K) r * y ^ n = algebraMap K[X] (RatFunc K) s := by
    intro n
    rcases hxn n with ⟨s, hs⟩
    have hs' :
        algebraMap K[X] (FractionRing K[X]) r * x ^ n =
          algebraMap K[X] (FractionRing K[X]) s := by
      simpa [Algebra.smul_def] using hs
    have hs'' : ψ (algebraMap K[X] (FractionRing K[X]) r * x ^ n) =
        ψ (algebraMap K[X] (FractionRing K[X]) s) := by
      simpa using congrArg ψ hs'
    refine ⟨s, ?_⟩
    simpa [ψ, y, map_mul, map_pow, RatFunc.ofFractionRing_algebraMap] using hs''
  let num : K[X] := RatFunc.num y
  let denom : K[X] := RatFunc.denom y
  have hdenom_dvd : ∀ n : ℕ, denom ^ n ∣ r := by
    intro n
    cases n with
    | zero =>
        simpa using (one_dvd r)
    | succ n =>
        rcases hxn' (Nat.succ n) with ⟨s, hs⟩
        have hy_pow :
            y ^ (Nat.succ n) =
              algebraMap K[X] (RatFunc K) (num ^ (Nat.succ n)) /
                algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) := by
          have hy :
              algebraMap K[X] (RatFunc K) num / algebraMap K[X] (RatFunc K) denom = y :=
            RatFunc.num_div_denom y
          calc
            y ^ (Nat.succ n) =
                (algebraMap K[X] (RatFunc K) num /
                  algebraMap K[X] (RatFunc K) denom) ^ (Nat.succ n) := by
                    simpa [hy.symm]
            _ =
                algebraMap K[X] (RatFunc K) (num ^ (Nat.succ n)) /
                  algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) := by
                    simp [div_pow, map_pow]
        have hs' :
            algebraMap K[X] (RatFunc K) r *
                (algebraMap K[X] (RatFunc K) (num ^ (Nat.succ n)) /
                  algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n))) =
              algebraMap K[X] (RatFunc K) s := by
          simpa [hy_pow] using hs
        have hs'' :
            (algebraMap K[X] (RatFunc K) (r * num ^ (Nat.succ n))) /
                algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) =
              algebraMap K[X] (RatFunc K) s := by
          simpa [mul_div_assoc, map_mul, map_pow, mul_comm, mul_left_comm, mul_assoc] using hs'
        have hs''' :
            algebraMap K[X] (RatFunc K) s =
              (algebraMap K[X] (RatFunc K) (r * num ^ (Nat.succ n))) /
                algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) := hs''.symm
        have hdenom_ne :
            algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) ≠ 0 := by
          intro hzero
          have hzero' : denom ^ (Nat.succ n) = 0 := by
            apply (IsFractionRing.injective (Polynomial K) (RatFunc K))
            calc
              algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) = 0 := hzero
              _ = algebraMap K[X] (RatFunc K) (0 : K[X]) := by
                    exact (map_zero (algebraMap K[X] (RatFunc K))).symm
          exact (pow_ne_zero (Nat.succ n) (RatFunc.denom_ne_zero y)) hzero'
        have hclear :
            algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)) *
                algebraMap K[X] (RatFunc K) s =
              algebraMap K[X] (RatFunc K) (r * num ^ (Nat.succ n)) := by
          have h :=
            (eq_div_iff (a := algebraMap K[X] (RatFunc K) (r * num ^ (Nat.succ n)))
                (b := algebraMap K[X] (RatFunc K) (denom ^ (Nat.succ n)))
                (c := algebraMap K[X] (RatFunc K) s) hdenom_ne).1 hs'''
          simpa [mul_comm, mul_left_comm, mul_assoc] using h
        have hclear' :
            denom ^ (Nat.succ n) * s = r * num ^ (Nat.succ n) := by
          apply (IsFractionRing.injective (Polynomial K) (RatFunc K))
          simpa [map_mul, map_pow, mul_comm, mul_left_comm, mul_assoc] using hclear
        have hdiv : denom ^ (Nat.succ n) ∣ r * num ^ (Nat.succ n) :=
          ⟨s, by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hclear'.symm⟩
        have hcop :
            IsCoprime (denom ^ (Nat.succ n)) (num ^ (Nat.succ n)) := by
          have hbase : IsCoprime num denom := RatFunc.isCoprime_num_denom y
          have hpow :
              IsCoprime (num ^ (Nat.succ n)) (denom ^ (Nat.succ n)) :=
            (IsCoprime.pow_iff (x := num) (y := denom) (hm := Nat.succ_pos n)
              (hn := Nat.succ_pos n)).2 hbase
          simpa [isCoprime_comm] using hpow.symm
        exact IsCoprime.dvd_of_dvd_mul_right hcop hdiv
  have hdeg_denom : denom.natDegree = 0 := by
    by_contra hpos
    have hpos' : 0 < denom.natDegree := Nat.pos_of_ne_zero hpos
    have hdiv := hdenom_dvd (r.natDegree + 1)
    have hdeg_le : (denom ^ (r.natDegree + 1)).natDegree ≤ r.natDegree :=
      Polynomial.natDegree_le_of_dvd hdiv (by simpa using hrne)
    have hdeg_eq :
        (denom ^ (r.natDegree + 1)).natDegree =
          (r.natDegree + 1) * denom.natDegree := by
      simpa using (RatFunc.monic_denom y).natDegree_pow (r.natDegree + 1)
    have hmul :
        r.natDegree + 1 ≤ (r.natDegree + 1) * denom.natDegree :=
      by
        have hmul' :
            (r.natDegree + 1) * 1 ≤ (r.natDegree + 1) * denom.natDegree :=
          Nat.mul_le_mul_left (r.natDegree + 1) (Nat.succ_le_iff.mpr hpos')
        simpa [Nat.mul_one] using hmul'
    have hlt : r.natDegree < (r.natDegree + 1) * denom.natDegree :=
      lt_of_lt_of_le (Nat.lt_succ_self _) hmul
    exact (lt_irrefl _ (lt_of_le_of_lt hdeg_le (by simpa [hdeg_eq] using hlt)))
  have hdenom_eq : denom = 1 :=
    Polynomial.eq_one_of_monic_natDegree_zero (RatFunc.monic_denom y) hdeg_denom
  have hy_alg : y = algebraMap K[X] (RatFunc K) num := by
    calc
      y =
          algebraMap K[X] (RatFunc K) num /
            algebraMap K[X] (RatFunc K) denom := by
              exact (RatFunc.num_div_denom y).symm
      _ = algebraMap K[X] (RatFunc K) num := by
            simp [hdenom_eq]
  refine ⟨num, ?_⟩
  have hx' : RatFunc.toFractionRing y = x := by
    dsimp [y, ψ]
    exact (RatFunc.toFractionRingRingEquiv K).apply_symm_apply x
  have hy' : RatFunc.toFractionRing y = algebraMap K[X] (FractionRing K[X]) num := by
    have hmap :
        RatFunc.toFractionRing (algebraMap K[X] (RatFunc K) num) =
          algebraMap K[X] (FractionRing K[X]) num := by
      exact (RatFunc.toFractionRingAlgEquiv (K := K) (R := K[X])).commutes num
    simpa [hy_alg] using hmap
  simpa [hx'] using hy'

/--
Let \( A \) be a domain. Show that if \( A \) is completely integrally closed, so is \( A[X] \). -/
theorem completely_integrally_closed_polynomial_ring {A : Type} [CommRing A] [IsDomain A]
    (h : IsCompletelyIntegrallyClosed A) : IsCompletelyIntegrallyClosed (Polynomial A) := by
  intro x hx
  classical
  rcases hx with ⟨r, hrne, hxn⟩
  by_cases hrunit : IsUnit r
  ·
    exact
      almostIntegral_eq_algebraMap_of_unit (A := Polynomial A) (x := x) (r := r) hxn hrunit
  ·
    classical
    let K := FractionRing A
    let j : Polynomial A →+* Polynomial K :=
      Polynomial.mapRingHom (algebraMap A K)
    have hj : Function.Injective j := by
      intro p q hpq
      apply Polynomial.map_injective (f := algebraMap A K)
        (IsFractionRing.injective A K)
      simpa [j] using hpq
    let φ :=
      (IsFractionRing.map (A := Polynomial A) (B := Polynomial K)
        (K := FractionRing (Polynomial A)) (L := FractionRing (Polynomial K)) hj)
    have hx' :
        IsAlmostIntegral (A := Polynomial K) (x := φ x) := by
      simpa [j, φ] using
        (IsAlmostIntegral.map_fractionRing_map (A := Polynomial A) (B := Polynomial K) j hj
          ⟨r, hrne, hxn⟩)
    obtain ⟨f, hf⟩ :=
      (completelyIntegrallyClosed_polynomial_over_field (K := K)) (x := φ x) hx'
    have hxnK : ∀ n : ℕ, ∃ y : Polynomial A, j r * f ^ n = j y := by
      intro n
      rcases hxn n with ⟨y, hy⟩
      have hy' :
          φ (algebraMap (Polynomial A) (FractionRing (Polynomial A)) r * x ^ n) =
            φ (algebraMap (Polynomial A) (FractionRing (Polynomial A)) y) := by
        simpa [Algebra.smul_def] using congrArg φ hy
      have hy'' :
          algebraMap (Polynomial K) (FractionRing (Polynomial K)) (j r) * (φ x) ^ n =
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) (j y) := by
        simpa [φ, fractionRing_map_algebraMap, map_mul, map_pow] using hy'
      have hy''' :
          algebraMap (Polynomial K) (FractionRing (Polynomial K)) (j r) *
              (algebraMap (Polynomial K) (FractionRing (Polynomial K)) f) ^ n =
            algebraMap (Polynomial K) (FractionRing (Polynomial K)) (j y) := by
        simpa [hf] using hy''
      have hy'''' : j r * f ^ n = j y := by
        apply (IsFractionRing.injective (Polynomial K) (FractionRing (Polynomial K)))
        simpa [map_mul, map_pow] using hy'''
      exact ⟨y, hy''''⟩
    have hdesc :
        ∃ g : Polynomial A, j g = f := by
      exact
        polynomial_mem_map_of_almostIntegral_over_fractionRing (A := A) h
          (f := f) ⟨r, hrne, hxnK⟩
    rcases hdesc with ⟨g, hg⟩
    have hφinj : Function.Injective φ := by
      -- use injectivity of the localization map
      simpa [φ] using
        (IsLocalization.map_injective_of_injective'
          (M := nonZeroDivisors (Polynomial A))
          (S := Polynomial K)
          (Rₘ := FractionRing (Polynomial A))
          (Sₘ := FractionRing (Polynomial K))
          (N := nonZeroDivisors (Polynomial K))
          (hf := nonZeroDivisors_le_comap_nonZeroDivisors_of_injective j hj)
          (hN := by
            simpa using (zero_not_mem_nonZeroDivisors (R := Polynomial K)))
          hj)
    refine ⟨g, ?_⟩
    apply hφinj
    have hmapg :
        φ (algebraMap (Polynomial A) (FractionRing (Polynomial A)) g) =
          algebraMap (Polynomial K) (FractionRing (Polynomial K)) (j g) := by
      simpa [φ] using
        (fractionRing_map_algebraMap (A := Polynomial A) (B := Polynomial K)
          (K := FractionRing (Polynomial A)) (L := FractionRing (Polynomial K)) j hj g)
    calc
      φ x = algebraMap (Polynomial K) (FractionRing (Polynomial K)) f := hf
      _ = algebraMap (Polynomial K) (FractionRing (Polynomial K)) (j g) := by
            simpa [hg]
      _ = φ (algebraMap (Polynomial A) (FractionRing (Polynomial A)) g) := by
            simpa [hmapg]

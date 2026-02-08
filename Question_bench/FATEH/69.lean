import Mathlib

open Polynomial

-- Rational numbers are algebraic over ℤ via the linear polynomial `den * X - num`.
lemma algebraic_int_rat : Algebra.IsAlgebraic ℤ ℚ := by
  classical
  refine ⟨?_⟩
  intro q
  refine ⟨Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num, ?_, ?_⟩
  · intro h
    have h1 : (Polynomial.C (q.den : ℤ) * Polynomial.X : ℤ[X]).coeff 1 = (q.den : ℤ) := by
      simp
    have h2 : (Polynomial.C q.num : ℤ[X]).coeff 1 = 0 := by
      simpa using (Polynomial.coeff_C (a := (q.num : ℤ)) (n := 1))
    have : (q.den : ℤ) = 0 := by
      have hcoeff' :
          (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num : ℤ[X]).coeff 1 = 0 := by
        simpa using congrArg (fun p => p.coeff 1) h
      rw [Polynomial.coeff_sub, h1, h2] at hcoeff'
      exact sub_eq_zero.mp hcoeff'
    exact (Rat.den_ne_zero q) ((Int.ofNat_eq_zero).1 this)
  · simp

-- Number fields are algebraic over ℤ by transitivity.
lemma algebraic_int_K {K : Type} [Field K] [NumberField K] : Algebra.IsAlgebraic ℤ K := by
  classical
  haveI : Algebra.IsAlgebraic ℤ ℚ := algebraic_int_rat
  haveI : Algebra.IsAlgebraic ℚ K := NumberField.isAlgebraic (K := K)
  exact Algebra.IsAlgebraic.trans ℤ ℚ K

-- A finite family in a number field has a common integral multiple.
lemma exists_int_mul_integral_range {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ i, IsIntegral ℤ (d • x i) := by
  classical
  haveI : Algebra.IsAlgebraic ℤ K := algebraic_int_K
  let s : Finset K := Finset.univ.image x
  obtain ⟨d, hd0, hd⟩ :=
    (Algebra.IsAlgebraic.exists_integral_multiples (R := ℤ) (A := K) (s := s))
  refine ⟨d, hd0, ?_⟩
  intro i
  have hi : x i ∈ s := by
    simp [s]
  exact hd (x i) hi

-- The induced map `ℤ[d⁻¹] → K` when `d ≠ 0`.
noncomputable def awayMapInt {K : Type} [Field K] [CharZero K] [Algebra ℤ K]
    (d : ℤ) (hd : d ≠ 0) : Localization.Away d →+* K := by
  have hdK : (algebraMap ℤ K d) ≠ 0 := by
    simpa using (Int.cast_ne_zero (α := K) (n := d)).2 hd
  exact Localization.awayLift (algebraMap ℤ K) d ((isUnit_iff_ne_zero).2 hdK)

-- `ℤ[d⁻¹]` is not a field when `d ≠ 0`.
lemma localization_away_not_field (d : ℤ) (hd : d ≠ 0) :
    ¬ IsField (Localization.Away d) := by
  classical
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes (d.natAbs + 1)
  have hp_gt : d.natAbs < p := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hp_ge
  have hpos : 0 < d.natAbs := (Int.natAbs_pos.mpr hd)
  have hnot_dvd : ∀ n : ℕ, ¬ (p : ℤ) ∣ d ^ n := by
    intro n hdiv
    have hdiv' : p ∣ d.natAbs ^ n := by
      have hdiv' : (p : ℤ) ∣ (d ^ n).natAbs := (Int.dvd_natAbs).2 hdiv
      have hdiv'' : p ∣ (d ^ n).natAbs := (Int.natCast_dvd_natCast).1 hdiv'
      simpa [Int.natAbs_pow] using hdiv''
    have hpd : p ∣ d.natAbs := hp_prime.dvd_of_dvd_pow hdiv'
    exact (Nat.not_dvd_of_pos_of_lt hpos hp_gt) hpd
  have hnot_unit : ¬ IsUnit (algebraMap ℤ (Localization.Away d) (p : ℤ)) := by
    intro hunit
    rcases
        (IsLocalization.Away.algebraMap_isUnit_iff (S := Localization.Away d) (x := d)
            (y := (p : ℤ))).1 hunit with ⟨n, hdiv⟩
    exact (hnot_dvd n) hdiv
  have hinj : Function.Injective (algebraMap ℤ (Localization.Away d)) := by
    exact IsLocalization.injective (S := Localization.Away d)
      (powers_le_nonZeroDivisors_of_noZeroDivisors (x := d) hd)
  have hp_ne_zero : (algebraMap ℤ (Localization.Away d) (p : ℤ)) ≠ 0 := by
    have hpz : (p : ℤ) ≠ 0 := (Int.ofNat_eq_zero).not.mpr hp_prime.ne_zero
    intro hzero
    have hzero' :
        (algebraMap ℤ (Localization.Away d) (p : ℤ)) = algebraMap ℤ (Localization.Away d) 0 := by
      simpa using hzero
    exact hpz (hinj hzero')
  intro hfield
  letI := hfield.toField
  exact hnot_unit ((isUnit_iff_ne_zero).2 hp_ne_zero)

/-- Prove that if $K$ is a field of finite degree over $\mathbb{Q}$ and $x_1, \dots, x_n$ are
finitely many elements of $K$, then the subring $\mathbb{Z}[x_1, \dots, x_n]$ they generate over
$\mathbb{Z}$ is not equal to $K$. -/
theorem int_adjoin_range_ne_top {K : Type} [Field K] [NumberField K] {n : ℕ} (x : Fin n → K) :
    Algebra.adjoin ℤ (Set.range x) ≠ ⊤ := by
  classical
  intro htop
  obtain ⟨d, hd0, hd⟩ := exists_int_mul_integral_range x
  let R := Localization.Away d
  let f : R →+* K := awayMapInt (K := K) d hd0
  letI : Algebra R K := f.toAlgebra
  haveI : IsScalarTower R R K := by
    refine ⟨?_⟩
    intro r s x
    simpa [smul_eq_mul] using (smul_smul r s x).symm
  have hcomp : (algebraMap R K).comp (algebraMap ℤ R) = algebraMap ℤ K := by
    ext z
    simp
  have hcomp' :
      (algebraMap R K).comp (algebraMap ℤ R) = (RingHom.id K).comp (algebraMap ℤ K) := by
    simpa [RingHom.comp_id] using hcomp
  have hmap_int : ∀ {y : K}, IsIntegral ℤ y → IsIntegral R y := by
    intro y hy
    simpa using
      (IsIntegral.map_of_comp_eq (φ := algebraMap ℤ R) (ψ := RingHom.id K) hcomp' hy)
  have hmapd : algebraMap ℤ K d = algebraMap R K (algebraMap ℤ R d) := by
    exact (congrArg (fun g => g d) hcomp).symm
  have hunitR : IsUnit (algebraMap ℤ R d) :=
    IsLocalization.Away.algebraMap_isUnit (x := d)
  rcases hunitR with ⟨u, hu⟩
  have hx_int : ∀ i, IsIntegral R (x i) := by
    intro i
    have hxR : IsIntegral R (d • x i) := hmap_int (hd i)
    have hsmul : (d : ℤ) • x i = (algebraMap ℤ R d) • x i := by
      simp [Algebra.smul_def]
    have hsmul_u : (d : ℤ) • x i = (↑u : R) • x i := by
      simpa [hu] using hsmul
    have hx' : IsIntegral R ((↑(u⁻¹) : R) • ((↑u : R) • x i)) := by
      simpa [hsmul_u] using (IsIntegral.smul (R := R) (S := R) (↑(u⁻¹) : R) hxR)
    have hx_eq : (↑(u⁻¹) : R) • ((↑u : R) • x i) = x i := by
      have hmul : ((↑(u⁻¹) : R) * (↑u : R)) = (1 : R) := by
        simp
      calc
        (↑(u⁻¹) : R) • ((↑u : R) • x i)
            = ((↑(u⁻¹) : R) * (↑u : R)) • x i := by
                exact smul_smul (↑(u⁻¹) : R) (↑u : R) (x i)
        _ = (1 : R) • x i := by
              simp [hmul]
        _ = x i := by
              exact one_smul R (x i)
    simpa [hx_eq] using hx'
  have hIntAdjoin :
      Algebra.IsIntegral R (Algebra.adjoin R (Set.range x)) :=
    Algebra.IsIntegral.adjoin (R := R) (A := K) (S := Set.range x) <| by
      intro y hy
      rcases hy with ⟨i, rfl⟩
      exact hx_int i
  let S : Subalgebra ℤ K :=
    { carrier := (Algebra.adjoin R (Set.range x) : Set K)
      zero_mem' := (Algebra.adjoin R (Set.range x)).zero_mem
      one_mem' := (Algebra.adjoin R (Set.range x)).one_mem
      add_mem' := (Algebra.adjoin R (Set.range x)).add_mem
      mul_mem' := (Algebra.adjoin R (Set.range x)).mul_mem
      algebraMap_mem' := by
        intro z
        have hz : algebraMap ℤ K z = algebraMap R K (algebraMap ℤ R z) := by
          exact (congrArg (fun g => g z) hcomp).symm
        have hz' :
            algebraMap R K (algebraMap ℤ R z) ∈ Algebra.adjoin R (Set.range x) :=
          (Algebra.adjoin R (Set.range x)).algebraMap_mem (algebraMap ℤ R z)
        rw [hz]
        exact hz' }
  have hle : Algebra.adjoin ℤ (Set.range x) ≤ S := by
    refine (Algebra.adjoin_le_iff).2 ?_
    intro y hy
    have : y ∈ Algebra.adjoin R (Set.range x) := by
      exact (Algebra.subset_adjoin (R := R) (s := Set.range x) hy)
    simpa [S] using this
  have htop_le : (⊤ : Subalgebra ℤ K) ≤ S := by
    simpa [htop] using hle
  have hS : S = ⊤ := (top_le_iff.mp htop_le)
  have hRtop : Algebra.adjoin R (Set.range x) = ⊤ := by
    apply (top_le_iff.mp ?_)
    intro y hy
    have hcarrier : (Algebra.adjoin R (Set.range x) : Set K) = Set.univ := by
      have := congrArg (fun T : Subalgebra ℤ K => (T : Set K)) hS
      simpa [S] using this
    change y ∈ (Algebra.adjoin R (Set.range x) : Set K)
    rw [hcarrier]
    simp
  have hInt_mem :
      ∀ y ∈ Algebra.adjoin R (Set.range x), IsIntegral R y := by
    exact (Subalgebra.isIntegral_iff (S := Algebra.adjoin R (Set.range x))).1 hIntAdjoin
  have hIntK : Algebra.IsIntegral R K := by
    refine ⟨?_⟩
    intro y
    have hy : y ∈ Algebra.adjoin R (Set.range x) := by
      simp [hRtop]
    exact hInt_mem y hy
  have h_inj : Function.Injective (algebraMap R K) := by
    refine IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers d) (S := R) (T := K) (f := algebraMap R K) ?_
    intro z hz
    have hcomp_z :
        (algebraMap R K) (algebraMap ℤ R z) = algebraMap ℤ K z := by
      exact congrArg (fun g => g z) hcomp
    have hz' : (algebraMap ℤ K z) = 0 := by
      simpa [hcomp_z] using hz
    have hz0 : z = 0 := by
      exact (Int.cast_eq_zero (α := K) (n := z)).1 (by simpa using hz')
    simp [hz0]
  have hfieldR : IsField R :=
    isField_of_isIntegral_of_isField (R := R) (S := K) h_inj (Field.toIsField K)
  exact (localization_away_not_field d hd0) hfieldR

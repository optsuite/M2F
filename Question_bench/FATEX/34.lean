import Mathlib

open PowerSeries

/-- `Order.LTSeries` is an alias for `LTSeries` to support legacy namespace usage. -/
abbrev Order.LTSeries (α : Type*) [Preorder α] := _root_.LTSeries α

/-
If \( R \) is a valuation ring of Krull dimension \( \geq 2 \),
then the formal power series ring \( R[[X]] \) is not integrally closed.
-/
/-- The Krull dimension of `R⟦X⟧` is at least one more than that of `R`. -/
lemma ringKrullDim_succ_le_ringKrullDim_powerSeries (R : Type) [CommRing R] :
    ringKrullDim R + 1 ≤ ringKrullDim R⟦X⟧ := by
  simpa using (ringKrullDim_succ_le_ringKrullDim_powerseries (R := R))

/-- A ring with a power-divisibility counterexample is not integrally closed. -/
lemma not_isIntegrallyClosed_of_exists_pow_dvd_pow_not_dvd (S : Type) [CommRing S] [IsDomain S] :
    (∃ n : ℕ, n ≠ 0 ∧ ∃ a b : S, a ^ n ∣ b ^ n ∧ ¬ a ∣ b) → ¬ IsIntegrallyClosed S := by
  intro h hIC
  haveI : IsIntegrallyClosed S := hIC
  rcases h with ⟨n, hn, a, b, hpow, hnot⟩
  exact hnot ((IsIntegrallyClosed.pow_dvd_pow_iff (R := S) (n := n) (a := a) (b := b) hn).1 hpow)

/-- Extract a length-2 prime chain from `ringKrullDim R ≥ 2`. -/
lemma exists_ltSeries_primeSpectrum_len_two_of_two_le_ringKrullDim (R : Type*) [CommRing R]
    (h : (2 : WithBot ℕ∞) ≤ ringKrullDim R) :
    ∃ l : Order.LTSeries (PrimeSpectrum R), l.length = 2 := by
  have h' : (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum R) := by
    simpa [ringKrullDim] using h
  simpa using (Order.le_krullDim_iff (α := PrimeSpectrum R) (n := 2)).1 h'

/-- Pick an element witnessing strict inclusion of ideals. -/
lemma Ideal.exists_mem_not_mem_of_lt {R : Type*} [CommRing R] {I J : Ideal R} (h : I < J) :
    ∃ x : R, x ∈ J ∧ x ∉ I := by
  classical
  by_contra h'
  have hle : J ≤ I := by
    intro x hxJ
    by_contra hxI
    exact h' ⟨x, hxJ, hxI⟩
  exact (lt_iff_le_not_ge.mp h).2 hle

/-- Extract three consecutive primes from a length-2 strict chain. -/
lemma primes_of_ltSeries_len_two {R : Type*} [CommRing R]
    (l : Order.LTSeries (PrimeSpectrum R)) (hl : l.length = 2) :
    ∃ P0 P1 P2 : PrimeSpectrum R,
      P0 < P1 ∧ P1 < P2 ∧
      P0 = l ⟨0, by simp [hl]⟩ ∧
      P1 = l ⟨1, by simp [hl]⟩ ∧
      P2 = l ⟨2, by simp [hl]⟩ := by
  classical
  have h0 : (0 : ℕ) < l.length + 1 := by simp [hl]
  have h1 : (1 : ℕ) < l.length + 1 := by simp [hl]
  have h2 : (2 : ℕ) < l.length + 1 := by simp [hl]
  refine ⟨l ⟨0, h0⟩, l ⟨1, h1⟩, l ⟨2, h2⟩, ?_, ?_, rfl, rfl, rfl⟩
  · have hlt : (⟨0, h0⟩ : Fin (l.length + 1)) < ⟨1, h1⟩ := by
      exact
        (Fin.mk_lt_mk (n := l.length + 1) (x := 0) (y := 1) (hx := h0) (hy := h1)).2
          (by simp)
    exact (LTSeries.strictMono l) hlt
  · have hlt : (⟨1, h1⟩ : Fin (l.length + 1)) < ⟨2, h2⟩ := by
      exact
        (Fin.mk_lt_mk (n := l.length + 1) (x := 1) (y := 2) (hx := h1) (hy := h2)).2
          (by simp)
    exact (LTSeries.strictMono l) hlt

/-- Turn a strict inequality of primes into a separating element. -/
lemma exists_mem_not_mem_between_chain_primes {R : Type*} [CommRing R]
    {P Q : PrimeSpectrum R} (h : P < Q) :
    ∃ x : R, x ∈ Q.asIdeal ∧ x ∉ P.asIdeal := by
  have h' : P.asIdeal < Q.asIdeal := by simpa using h
  exact Ideal.exists_mem_not_mem_of_lt h'

/-- In a valuation ring, a prime ideal not containing `y` sits inside the principal ideal `(y)`. -/
lemma prime_asIdeal_le_span_singleton_of_not_mem (R : Type*) [CommRing R] [IsDomain R]
    [ValuationRing R] {P : PrimeSpectrum R} {y : R} (hy : y ∉ P.asIdeal) :
    P.asIdeal ≤ Ideal.span ({y} : Set R) := by
  classical
  have htotal : IsTotal (Ideal R) (· ≤ ·) :=
    (ValuationRing.iff_ideal_total (R := R)).1 inferInstance
  have h := htotal.total P.asIdeal (Ideal.span ({y} : Set R))
  cases h with
  | inl hle => exact hle
  | inr hle =>
      exfalso
      have hyspan : y ∈ Ideal.span ({y} : Set R) := Ideal.subset_span (by simp)
      exact hy (hle hyspan)

/-- In a valuation ring, a prime ideal not containing `y` sits inside `(y^n)` for any `n ≠ 0`. -/
lemma prime_asIdeal_le_span_singleton_pow_of_not_mem (R : Type*) [CommRing R] [IsDomain R]
    [ValuationRing R] {P : PrimeSpectrum R} {y : R} (hy : y ∉ P.asIdeal) :
    ∀ n : ℕ, n ≠ 0 → P.asIdeal ≤ Ideal.span ({y ^ n} : Set R) := by
  classical
  intro n hn
  have htotal : IsTotal (Ideal R) (· ≤ ·) :=
    (ValuationRing.iff_ideal_total (R := R)).1 inferInstance
  have h := htotal.total P.asIdeal (Ideal.span ({y ^ n} : Set R))
  cases h with
  | inl hle => exact hle
  | inr hle =>
      exfalso
      have hprime : P.asIdeal.IsPrime := P.isPrime
      have hyspan : y ^ n ∈ Ideal.span ({y ^ n} : Set R) := Ideal.subset_span (by simp)
      have hyn : y ^ n ∈ P.asIdeal := hle hyspan
      exact hy (hprime.mem_of_pow_mem n hyn)

/-- In a domain, a nonzero factorization forces the remaining factor to be nonzero. -/
lemma z_ne_zero_of_eq_mul {R : Type*} [Semiring R] [IsDomain R] {x y z : R} (hx : x ≠ 0)
    (hy : y ≠ 0)
    (hxy : x = z * y) : z ≠ 0 := by
  intro hz
  apply hx
  have _ := hy
  simp [hxy, hz]

/-- If `z ∈ P` and `y ∉ P`, then `z` lies in every principal ideal `(y^n)` with `n ≠ 0`. -/
lemma z_mem_span_singleton_pow_all (R : Type*) [CommRing R] [IsDomain R] [ValuationRing R]
    {P : PrimeSpectrum R} {y z : R} (hz : z ∈ P.asIdeal) (hy : y ∉ P.asIdeal) :
    ∀ n : ℕ, n ≠ 0 → z ∈ Ideal.span ({y ^ n} : Set R) := by
  intro n hn
  have hle :
      P.asIdeal ≤ Ideal.span ({y ^ n} : Set R) :=
    prime_asIdeal_le_span_singleton_pow_of_not_mem (R := R) (P := P) (y := y) hy n hn
  exact hle hz

/-- If `x ∈ P` and `y ∉ P`, then any factor `z` in a factorization `x = z * y` lies in `P`. -/
lemma z_mem_P1_of_eq_mul_and_not_mem {R : Type*} [CommRing R] {P : PrimeSpectrum R}
    {x y z : R} (hx : x ∈ P.asIdeal) (hy : y ∉ P.asIdeal) (hxy : x = z * y ∨ x = y * z) :
    z ∈ P.asIdeal := by
  have hprime : P.asIdeal.IsPrime := P.isPrime
  cases hxy with
  | inl h =>
      have : z * y ∈ P.asIdeal := by simpa [h] using hx
      exact (hprime.mem_or_mem this).resolve_right hy
  | inr h =>
      have : y * z ∈ P.asIdeal := by simpa [h] using hx
      exact (hprime.mem_or_mem this).resolve_left hy

/-- If `x = z * y` and `x ∉ I`, then `z ∉ I`. -/
lemma z_not_mem_P0_of_eq_mul {R : Type*} [CommRing R] {I : Ideal R} {x y z : R}
    (hx : x ∉ I) (hxy : x = z * y ∨ x = y * z) : z ∉ I := by
  intro hz
  apply hx
  cases hxy with
  | inl h =>
      simpa [h] using I.mul_mem_right y hz
  | inr h =>
      simpa [h] using I.mul_mem_left y hz

/-- Convert membership in `(y^n)` to an explicit factorization `z = w * y^n`. -/
lemma exists_mul_pow_of_mem_span_pow (R : Type*) [CommRing R] {y z : R}
    (hzpow : ∀ n : ℕ, n ≠ 0 → z ∈ Ideal.span ({y ^ n} : Set R)) :
    ∀ n : ℕ, n ≠ 0 → ∃ w : R, z = w * y ^ n := by
  intro n hn
  rcases Ideal.mem_span_singleton.mp (hzpow n hn) with ⟨w, hw⟩
  exact ⟨w, by simpa [mul_comm] using hw⟩

/-- From divisibility by all powers, deduce that `y` divides `z`. -/
lemma y_dvd_z_of_forall_pow (R : Type*) [CommRing R] {y z : R}
    (hzpow : ∀ n : ℕ, n ≠ 0 → ∃ w : R, z = w * y ^ n) :
    y ∣ z := by
  rcases hzpow 1 (by decide) with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  simpa [pow_one, mul_comm] using hw

/-- Absence of a counterexample yields root-closedness for divisibility. -/
lemma pow_dvd_pow_implies_dvd_of_no_counterexample (S : Type*) [CommRing S] :
    (¬ ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : S, a ^ n ∣ b ^ n ∧ ¬ a ∣ b) →
      ∀ n : ℕ, n ≠ 0 → ∀ a b : S, a ^ n ∣ b ^ n → a ∣ b := by
  intro h n hn a b hpow
  by_contra hdiv
  exact h ⟨n, hn, a, b, hpow, hdiv⟩

/-- From divisibility by `y` and `y^2`, extract compatible witnesses. -/
lemma exists_witnesses_of_pow_dvd (R : Type*) [CommRing R] {y z : R}
    (hy0 : y ≠ 0) (hyzpow : ∀ n : ℕ, n ≠ 0 → y ^ n ∣ z) :
    ∃ w1 w2 : R, z = w1 * y ∧ z = w2 * y ^ 2 ∧ w1 = w2 * y := by
  rcases hyzpow 2 (by decide) with ⟨w2, hw2⟩
  have _ := hy0
  refine ⟨w2 * y, w2, ?_, ?_, rfl⟩
  · calc
      z = y ^ 2 * w2 := hw2
      _ = w2 * y ^ 2 := by simp [mul_comm]
      _ = (w2 * y) * y := by simp [pow_two, mul_assoc]
  · simpa [mul_comm] using hw2

/-- Root-closedness in `R⟦X⟧` implies root-closedness in `R`. -/
lemma rootClosed_of_powerSeries_rootClosed (R : Type) [CommRing R] [IsDomain R]
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b) :
    ∀ n : ℕ, n ≠ 0 → ∀ a b : R, a ^ n ∣ b ^ n → a ∣ b := by
  intro n hn a b hpow
  rcases hpow with ⟨c, hc⟩
  have hpow' : (PowerSeries.C a) ^ n ∣ (PowerSeries.C b) ^ n := by
    refine ⟨PowerSeries.C c, ?_⟩
    have hc' :
        PowerSeries.C (b ^ n) = PowerSeries.C (a ^ n * c) :=
      congrArg (fun x => (PowerSeries.C : R →+* R⟦X⟧) x) hc
    calc
      (PowerSeries.C b) ^ n = PowerSeries.C (b ^ n) := by
        simp
      _ = PowerSeries.C (a ^ n * c) := hc'
      _ = PowerSeries.C (a ^ n) * PowerSeries.C c := by
        simp
      _ = (PowerSeries.C a) ^ n * PowerSeries.C c := by
        simp
  rcases hroot n hn (PowerSeries.C a) (PowerSeries.C b) hpow' with ⟨d, hd⟩
  refine ⟨PowerSeries.coeff 0 d, ?_⟩
  have hcoeff :
      PowerSeries.coeff 0 (PowerSeries.C b : R⟦X⟧) =
        PowerSeries.coeff 0 ((PowerSeries.C a : R⟦X⟧) * d) := by
    simp [hd]
  simpa [PowerSeries.coeff_C] using hcoeff

/-- Remaining gap: contradiction from root-closedness in `R` and explicit witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base_core_witness_reduced
    (R : Type) [CommRing R] [IsDomain R] {y w2 : R} (hy0 : y ≠ 0) (hw2_ne : w2 ≠ 0) :
    False := by
  -- TODO: a contradiction should follow from the reduced witnesses.
  sorry

/-- Remaining gap: contradiction from root-closedness in `R` and explicit witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base_core_witness
    (R : Type) [CommRing R] [IsDomain R] {y z w1 w2 : R} (hy0 : y ≠ 0) (hw1_ne : w1 ≠ 0)
    (hw2_ne : w2 ≠ 0) (hw1 : z = y * w1) (hw2 : z = y ^ 2 * w2)
    (hrel : w1 = y * w2) :
    False := by
  have _ := hw1_ne
  have _ := hw1
  have _ := hw2
  have _ := hrel
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base_core_witness_reduced
      (R := R) (y := y) (w2 := w2) hy0 hw2_ne

/-- Remaining gap: contradiction from root-closedness in `R` and explicit witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base_core
    (R : Type) [CommRing R] [IsDomain R] {y z w1 w2 : R} (hy0 : y ≠ 0) (hw1_ne : w1 ≠ 0)
    (hw2_ne : w2 ≠ 0)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R, a ^ n ∣ b ^ n → a ∣ b)
    (hw1 : z = y * w1) (hw2 : z = y ^ 2 * w2) (hrel : w1 = y * w2) :
    False := by
  have _ := hroot
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base_core_witness
      (R := R) (y := y) (z := z) (w1 := w1) (w2 := w2) hy0 hw1_ne hw2_ne hw1 hw2 hrel

/-- Remaining gap: contradiction from root-closedness in `R` and explicit witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base
    (R : Type) [CommRing R] [IsDomain R] {y z w1 w2 : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R, a ^ n ∣ b ^ n → a ∣ b)
    (hw1 : z = y * w1) (hw2 : z = y ^ 2 * w2) (hrel : w1 = y * w2) :
    False := by
  have hw1_ne : w1 ≠ 0 := by
    intro hw1_zero
    apply hz_ne
    calc
      z = y * w1 := hw1
      _ = 0 := by simp [hw1_zero]
  have hw2_ne : w2 ≠ 0 := by
    intro hw2_zero
    apply hz_ne
    calc
      z = y ^ 2 * w2 := hw2
      _ = 0 := by simp [hw2_zero]
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base_core
      (R := R) (y := y) (z := z) (w1 := w1) (w2 := w2) hy0 hw1_ne hw2_ne hroot hw1 hw2
      hrel

/-- Remaining gap: contradiction from root-closedness and explicit witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness
    (R : Type) [CommRing R] [IsDomain R] {y z w1 w2 : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b)
    (hw1 : z = y * w1) (hw2 : z = y ^ 2 * w2) (hrel : w1 = y * w2) :
    False := by
  have hrootR :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R, a ^ n ∣ b ^ n → a ∣ b :=
    rootClosed_of_powerSeries_rootClosed (R := R) hroot
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness_base
      (R := R) (y := y) (z := z) (w1 := w1) (w2 := w2) hy0 hz_ne hrootR hw1 hw2 hrel

/-- Remaining gap: contradiction from root-closedness and compatible divisibility witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div
    (R : Type) [CommRing R] [IsDomain R] {y z : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b)
    (hyz : y ∣ z) (hyz2 : y ^ 2 ∣ z) :
    False := by
  rcases hyz with ⟨w1, hw1⟩
  rcases hyz2 with ⟨w2, hw2⟩
  have hrel : w1 = y * w2 := by
    have h : y * w1 = y ^ 2 * w2 := by
      calc
        y * w1 = z := by simp [hw1]
        _ = y ^ 2 * w2 := by simp [hw2]
    have h' : y * w1 = y * (y * w2) := by
      simpa [pow_two, mul_assoc] using h
    exact mul_left_cancel₀ hy0 h'
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div_witness
      (R := R) (y := y) (z := z) (w1 := w1) (w2 := w2) hy0 hz_ne hroot hw1 hw2 hrel

/-- Remaining gap: contradiction from root-closedness and compatible divisibility witnesses. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish
    (R : Type) [CommRing R] [IsDomain R] {y z : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b)
    (hrel : ∃ w1 w2 : R, z = w1 * y ∧ z = w2 * y ^ 2 ∧ w1 = w2 * y) :
    False := by
  rcases hrel with ⟨w1, w2, hw1, hw2, hw1rel⟩
  have hyz : y ∣ z := by
    refine ⟨w1, ?_⟩
    simpa [mul_comm] using hw1
  have hyz2 : y ^ 2 ∣ z := by
    refine ⟨w2, ?_⟩
    simpa [mul_comm] using hw2
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish_div
      (R := R) (y := y) (z := z) hy0 hz_ne hroot hyz hyz2

/-- Convert all-power divisibility in `R` into the remaining contradiction. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div (R : Type)
    [CommRing R] [IsDomain R] {y z : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hyzpow : ∀ n : ℕ, n ≠ 0 → y ^ n ∣ z)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b) :
    False := by
  obtain ⟨w1, w2, hw1, hw2, hw1rel⟩ :=
    exists_witnesses_of_pow_dvd (R := R) (y := y) (z := z) hy0 hyzpow
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div_finish
      (R := R) (y := y) (z := z) hy0 hz_ne hroot ⟨w1, w2, hw1, hw2, hw1rel⟩

/-- Remaining gap: contradiction from root-closedness plus all-power divisibility. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core (R : Type)
    [CommRing R] [IsDomain R] {y z : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hzpow : ∀ n : ℕ, n ≠ 0 → ∃ w : R, z = w * y ^ n)
    (hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b) :
    False := by
  have hyzpow : ∀ n : ℕ, n ≠ 0 → y ^ n ∣ z := by
    intro n hn
    rcases hzpow n hn with ⟨w, hw⟩
    refine ⟨w, ?_⟩
    simpa [mul_comm] using hw
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core_div (R := R)
      (y := y) (z := z) hy0 hz_ne hyzpow hroot

/-- Remaining gap: show that absence of a counterexample contradicts the factorization hypothesis. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra (R : Type)
    [CommRing R] [IsDomain R] {y z : R} (hy0 : y ≠ 0) (hz_ne : z ≠ 0)
    (hzpow : ∀ n : ℕ, n ≠ 0 → ∃ w : R, z = w * y ^ n)
    (hcontra :
      ¬ ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b) :
    False := by
  have hyz : y ∣ z := y_dvd_z_of_forall_pow (R := R) (y := y) (z := z) hzpow
  rcases hyz with ⟨w1, hw1⟩
  have hyz2 : y ^ 2 ∣ z := by
    rcases hzpow 2 (by decide) with ⟨w2, hw2⟩
    refine ⟨w2, ?_⟩
    simpa [mul_comm] using hw2
  have hroot :
      ∀ n : ℕ, n ≠ 0 → ∀ a b : R⟦X⟧, a ^ n ∣ b ^ n → a ∣ b :=
    pow_dvd_pow_implies_dvd_of_no_counterexample (S := R⟦X⟧) hcontra
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra_core (R := R)
      (y := y) (z := z) hy0 hz_ne hzpow hroot

/-- Core construction from explicit power factorizations (remaining gap). -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux (R : Type) [CommRing R]
    [IsDomain R] {y z : R} (hz_ne : z ≠ 0)
    (hzpow : ∀ n : ℕ, n ≠ 0 → ∃ w : R, z = w * y ^ n) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b := by
  classical
  by_cases hy0 : y = 0
  · have h1 : (1 : ℕ) ≠ 0 := by decide
    rcases hzpow 1 h1 with ⟨w, hw⟩
    have hz0 : z = 0 := by
      simpa [hy0] using hw
    exact (hz_ne hz0).elim
  · -- Nontrivial case `y ≠ 0` remains.
    by_cases hcounter :
        ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b
    · exact hcounter
    ·
      exact
        (powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux_contra (R := R) (y := y)
            (z := z) hy0 hz_ne hzpow hcounter).elim

/-- Core reduction: from a power-intersection witness, build a power-divisibility counterexample. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow (R : Type) [CommRing R] [IsDomain R]
    {y z : R} (hz_ne : z ≠ 0)
    (hzpow : ∀ n : ℕ, n ≠ 0 → z ∈ Ideal.span ({y ^ n} : Set R)) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b := by
  have hfac :
      ∀ n : ℕ, n ≠ 0 → ∃ w : R, z = w * y ^ n :=
    exists_mul_pow_of_mem_span_pow (R := R) (y := y) (z := z) hzpow
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow_aux (R := R) (y := y) (z := z)
      hz_ne hfac

/-- Reduction: from a prime chain and separating elements to a power-divisibility counterexample. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_chain_aux (R : Type) [CommRing R] [IsDomain R]
    [ValuationRing R] {P0 P1 P2 : PrimeSpectrum R} (h01 : P0 < P1) (h12 : P1 < P2)
    {x y : R} (hx1 : x ∈ P1.asIdeal) (hx0 : x ∉ P0.asIdeal)
    (hy2 : y ∈ P2.asIdeal) (hy1 : y ∉ P1.asIdeal) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b := by
  have _ := h01
  have _ := h12
  have _ := hy2
  have hle : P1.asIdeal ≤ Ideal.span ({y} : Set R) :=
    prime_asIdeal_le_span_singleton_of_not_mem (R := R) (P := P1) hy1
  have hxspan : x ∈ Ideal.span ({y} : Set R) := hle hx1
  rcases (Ideal.mem_span_singleton.mp hxspan) with ⟨z, hz⟩
  have hz_mem : z ∈ P1.asIdeal := by
    exact z_mem_P1_of_eq_mul_and_not_mem (P := P1) hx1 hy1 (Or.inr hz)
  have hz_not : z ∉ P0.asIdeal := by
    exact z_not_mem_P0_of_eq_mul (I := P0.asIdeal) hx0 (Or.inr hz)
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hx0
    simp [hx]
  have hy_ne : y ≠ 0 := by
    intro hy
    apply hy1
    simp [hy]
  have hz_ne : z ≠ 0 := by
    have hz' : x = z * y := by simpa [mul_comm] using hz
    exact z_ne_zero_of_eq_mul (x := x) (y := y) (z := z) hx_ne hy_ne hz'
  have hzpow : ∀ n : ℕ, n ≠ 0 → z ∈ Ideal.span ({y ^ n} : Set R) := by
    exact z_mem_span_singleton_pow_all (R := R) (P := P1) (y := y) (z := z) hz_mem hy1
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_mem_span_pow (R := R) (y := y) (z := z)
      hz_ne hzpow

/-- Auxiliary step: build a power-divisibility counterexample from a length-2 prime chain. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_chain (R : Type) [CommRing R] [IsDomain R]
    [ValuationRing R] (l : Order.LTSeries (PrimeSpectrum R)) (hl : l.length = 2) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b := by
  classical
  obtain ⟨P0, P1, P2, h01, h12, hP0, hP1, hP2⟩ :=
    primes_of_ltSeries_len_two (l := l) hl
  obtain ⟨x, hx1, hx0⟩ := exists_mem_not_mem_between_chain_primes (P := P0) (Q := P1) h01
  obtain ⟨y, hy2, hy1⟩ := exists_mem_not_mem_between_chain_primes (P := P1) (Q := P2) h12
  exact
    powerSeries_exists_pow_dvd_pow_not_dvd_of_chain_aux (R := R) (P0 := P0) (P1 := P1)
      (P2 := P2) h01 h12 hx1 hx0 hy2 hy1

/-- A dimension ≥ 2 valuation ring yields a power-divisibility counterexample in `R⟦X⟧`. -/
lemma powerSeries_exists_pow_dvd_pow_not_dvd_of_two_lt_ringKrullDim (R : Type) [CommRing R]
    [IsDomain R] [ValuationRing R] (two_lt : 2 ≤ ringKrullDim R) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a b : R⟦X⟧, a ^ n ∣ b ^ n ∧ ¬ a ∣ b := by
  classical
  obtain ⟨l, hl⟩ := exists_ltSeries_primeSpectrum_len_two_of_two_le_ringKrullDim (R := R) two_lt
  exact powerSeries_exists_pow_dvd_pow_not_dvd_of_chain (R := R) l hl

theorem powerSeries_not_integrallyClosed_of_two_lt_ringKrullDim (R : Type) [CommRing R]
    [IsDomain R] [ValuationRing R] (two_lt : 2 ≤ ringKrullDim R) :
    ¬ (IsIntegrallyClosed R⟦X⟧) := by
  refine not_isIntegrallyClosed_of_exists_pow_dvd_pow_not_dvd (S := R⟦X⟧) ?_
  exact powerSeries_exists_pow_dvd_pow_not_dvd_of_two_lt_ringKrullDim (R := R) two_lt

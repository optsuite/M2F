import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The ideal `(P^k)` in `K[X]`. -/
abbrev polynomialPowerIdeal (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) :
    Ideal (Polynomial K) :=
  Ideal.span ({P ^ k} : Set (Polynomial K))

/-- The quotient ring `K[X]/(P^k)`. -/
abbrev polynomialPowerQuotient (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) :=
  (Polynomial K) ⧸ polynomialPowerIdeal K P k

/-- The class of `P` in the quotient ring `K[X]/(P^k)`. -/
abbrev polynomialPowerQuotientP (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) :
    polynomialPowerQuotient K P k :=
  Ideal.Quotient.mk (polynomialPowerIdeal K P k) P

/-- The class of `X` in the quotient ring `K[X]/(P^k)`. -/
abbrev polynomialPowerQuotientX (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) :
    polynomialPowerQuotient K P k :=
  Ideal.Quotient.mk (polynomialPowerIdeal K P k) Polynomial.X

/-- Helper for n000008: a multiple of `P̄^n` lies in the ideal `(P̄)` when `1 ≤ n`. -/
lemma helperForN000008_mul_pow_mem_span_P
    (K : Type*) [Field K] (P : Polynomial K) (k n : ℕ)
    (hn1 : 1 ≤ n) (c : polynomialPowerQuotient K P k) :
    c * (polynomialPowerQuotientP K P k) ^ n ∈
      Ideal.span ({polynomialPowerQuotientP K P k} :
        Set (polynomialPowerQuotient K P k)) := by
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hn1)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine Ideal.mem_span_singleton'.2 ?_
  refine ⟨c * (polynomialPowerQuotientP K P k) ^ m, ?_⟩
  simp [pow_succ, mul_assoc]

/-- Helper for n000008: the square of `c * P̄^n` lies in the ideal `(P̄^(n+1))`. -/
lemma helperForN000008_sq_mul_pow_mem_span_succ
    (K : Type*) [Field K] (P : Polynomial K) (k n : ℕ)
    (hn1 : 1 ≤ n) (c : polynomialPowerQuotient K P k) :
    (c * (polynomialPowerQuotientP K P k) ^ n) ^ 2 ∈
      Ideal.span ({(polynomialPowerQuotientP K P k) ^ (n + 1)} :
        Set (polynomialPowerQuotient K P k)) := by
  have hn0 : n ≠ 0 := by
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) hn1)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  refine Ideal.mem_span_singleton'.2 ?_
  refine ⟨c ^ 2 * (polynomialPowerQuotientP K P k) ^ m, ?_⟩
  calc
    (c ^ 2 * (polynomialPowerQuotientP K P k) ^ m) *
        (polynomialPowerQuotientP K P k) ^ (m + 2)
        =
        c ^ 2 *
          ((polynomialPowerQuotientP K P k) ^ m *
            (polynomialPowerQuotientP K P k) ^ (m + 2)) := by
          simp [mul_assoc]
    _ =
        c ^ 2 *
          (polynomialPowerQuotientP K P k) ^ (m + (m + 2)) := by
          rw [← pow_add]
    _ = c ^ 2 * (polynomialPowerQuotientP K P k) ^ (2 * (m + 1)) := by
          have hmn : m + (m + 2) = 2 * (m + 1) := by
            simp [two_mul, Nat.add_left_comm, Nat.add_comm]
          simp [hmn]
    _ = c ^ 2 * (polynomialPowerQuotientP K P k) ^ ((m + 1) * 2) := by
          simp [Nat.mul_comm]
    _ = c ^ 2 * ((polynomialPowerQuotientP K P k) ^ (m + 1)) ^ 2 := by
          simp [pow_mul]
    _ = (c * (polynomialPowerQuotientP K P k) ^ (m + 1)) ^ 2 := by
          symm
          simp [mul_pow]

/-- Helper for n000008: choose `c` to cancel `a` using a unit `d`. -/
lemma helperForN000008_cancel_choice {R : Type*} [CommRing R] (a d : R) (hd : IsUnit d) :
    ∃ c : R, a + c * d = 0 := by
  rcases hd with ⟨u, rfl⟩
  refine ⟨-a * (u⁻¹ : Units R), ?_⟩
  simp [mul_assoc, Units.inv_mul]

/-- Helper for n000008: factor a right multiplier in a simple sum. -/
lemma helperForN000008_factor_right {R : Type*} [CommRing R] (a b c x : R) :
    a * x + b * (c * x) = (a + c * b) * x := by
  calc
    a * x + b * (c * x) = a * x + (b * c) * x := by
      rw [← mul_assoc]
    _ = (a + b * c) * x := by
      symm
      rw [add_mul]
    _ = (a + c * b) * x := by
      simp [mul_comm]

set_option maxHeartbeats 400000 in
/-- n000008: (One-step lifting) Let `K` be a field, `P ∈ K[X]`, `k ≥ 2`,
`R = K[X]/(P^k)`, and write again `P` for its class in `R`. Fix `n` with
`1 ≤ n < k`. If `y ∈ R` satisfies `y ≡ x (mod (P))` and `P(y) ∈ (P^n)` and if
`P'(y)` is a unit in `R`, then there exists `c ∈ R` such that
`z := y + c * P^n` satisfies `z ≡ y (mod (P))` and `P(z) ∈ (P^{n+1})`. -/
theorem one_step_lifting
    (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) (hk : 2 ≤ k)
    (n : ℕ) (hn1 : 1 ≤ n) (hnk : n < k)
    (y : polynomialPowerQuotient K P k)
    (hyx :
      y - polynomialPowerQuotientX K P k ∈
        Ideal.span ({polynomialPowerQuotientP K P k} :
          Set (polynomialPowerQuotient K P k)))
    (hyP :
      Polynomial.eval₂ (algebraMap K (polynomialPowerQuotient K P k)) y P ∈
        Ideal.span ({(polynomialPowerQuotientP K P k) ^ n} :
          Set (polynomialPowerQuotient K P k)))
    (hunit :
      IsUnit
        (Polynomial.eval₂ (algebraMap K (polynomialPowerQuotient K P k)) y
          (Polynomial.derivative P))) :
    ∃ c : polynomialPowerQuotient K P k,
      let z : polynomialPowerQuotient K P k :=
        y + c * (polynomialPowerQuotientP K P k) ^ n
      z - y ∈
          Ideal.span ({polynomialPowerQuotientP K P k} :
            Set (polynomialPowerQuotient K P k)) ∧
        Polynomial.eval₂ (algebraMap K (polynomialPowerQuotient K P k)) z P ∈
          Ideal.span ({(polynomialPowerQuotientP K P k) ^ (n + 1)} :
            Set (polynomialPowerQuotient K P k)) :=
  by
    classical
    have _ := hk
    have _ := hnk
    have _ := hyx
    let Pbar : polynomialPowerQuotient K P k := polynomialPowerQuotientP K P k
    have hyP' :
        Polynomial.aeval y P ∈
          Ideal.span ({Pbar ^ n} : Set (polynomialPowerQuotient K P k)) := by
      simpa [Polynomial.aeval_def, Pbar] using hyP
    have hunit' :
        IsUnit (Polynomial.aeval y (Polynomial.derivative P)) := by
      simpa [Polynomial.aeval_def] using hunit
    obtain ⟨a, ha⟩ := (Ideal.mem_span_singleton'.1 hyP')
    have ha' : Polynomial.aeval y P = a * Pbar ^ n := by
      exact ha.symm
    obtain ⟨c, hc⟩ :=
      helperForN000008_cancel_choice a
        (Polynomial.aeval y (Polynomial.derivative P)) hunit'
    refine ⟨c, ?_⟩
    dsimp
    constructor
    · have hmem :
          c * Pbar ^ n ∈
            Ideal.span ({Pbar} : Set (polynomialPowerQuotient K P k)) :=
        helperForN000008_mul_pow_mem_span_P K P k n hn1 c
      have hz : (y + c * Pbar ^ n) - y = c * Pbar ^ n := by
        simp [add_sub_cancel_left]
      simpa [hz, Pbar] using hmem
    · let I : Ideal (polynomialPowerQuotient K P k) :=
        Ideal.span ({Pbar ^ (n + 1)} : Set (polynomialPowerQuotient K P k))
      let S := (polynomialPowerQuotient K P k) ⧸ I
      let π : (polynomialPowerQuotient K P k) →ₐ[K] S :=
        Ideal.Quotient.mkₐ K I
      have hmemsq : (c * Pbar ^ n) ^ 2 ∈ I := by
        have h :=
          helperForN000008_sq_mul_pow_mem_span_succ K P k n hn1 c
        simpa [I, Pbar] using h
      have hsq : (π (c * Pbar ^ n)) ^ 2 = 0 := by
        have hzero : π ((c * Pbar ^ n) ^ 2) = 0 := by
          change (Ideal.Quotient.mk I ((c * Pbar ^ n) ^ 2) = 0)
          exact (Ideal.Quotient.eq_zero_iff_mem).2 hmemsq
        calc
          (π (c * Pbar ^ n)) ^ 2 = π ((c * Pbar ^ n) ^ 2) := by
            symm
            exact map_pow π (c * Pbar ^ n) 2
          _ = 0 := hzero
      have h :=
        Polynomial.aeval_add_of_sq_eq_zero (p := P) (x := π y)
          (y := π (c * Pbar ^ n)) hsq
      have hzπ : π (y + c * Pbar ^ n) = π y + π (c * Pbar ^ n) := by
        exact
          (π : polynomialPowerQuotient K P k →+* S).map_add y (c * Pbar ^ n)
      have hTaylor' :
          π (Polynomial.aeval (y + c * Pbar ^ n) P) =
            π (Polynomial.aeval y P) +
              π (Polynomial.aeval y (Polynomial.derivative P)) * π (c * Pbar ^ n) := by
        have h0 := h
        rw [← hzπ] at h0
        rw [Polynomial.aeval_algHom_apply π (y + c * Pbar ^ n) P] at h0
        rw [Polynomial.aeval_algHom_apply π y P] at h0
        rw [Polynomial.aeval_algHom_apply π y (Polynomial.derivative P)] at h0
        exact h0
      have hsum :
          a * Pbar ^ n +
            Polynomial.aeval y (Polynomial.derivative P) * (c * Pbar ^ n) = 0 := by
        have hfac :=
          helperForN000008_factor_right a
            (Polynomial.aeval y (Polynomial.derivative P)) c (Pbar ^ n)
        rw [hfac, hc]
        simp
      have hzero :
          π (a * Pbar ^ n +
            Polynomial.aeval y (Polynomial.derivative P) * (c * Pbar ^ n)) = 0 := by
        rw [hsum]
        simp
      have hzero' : π (Polynomial.aeval (y + c * Pbar ^ n) P) = 0 := by
        calc
          π (Polynomial.aeval (y + c * Pbar ^ n) P) =
              π (Polynomial.aeval y P) +
                π (Polynomial.aeval y (Polynomial.derivative P)) * π (c * Pbar ^ n) := hTaylor'
          _ = π (a * Pbar ^ n) +
              π (Polynomial.aeval y (Polynomial.derivative P)) * π (c * Pbar ^ n) := by
                simp [ha']
          _ = π (a * Pbar ^ n +
                Polynomial.aeval y (Polynomial.derivative P) * (c * Pbar ^ n)) := by
                symm
                calc
                  π (a * Pbar ^ n +
                      Polynomial.aeval y (Polynomial.derivative P) * (c * Pbar ^ n)) =
                      π (a * Pbar ^ n) +
                        π (Polynomial.aeval y (Polynomial.derivative P) * (c * Pbar ^ n)) := by
                    exact
                      (π : polynomialPowerQuotient K P k →+* S).map_add
                        (a * Pbar ^ n)
                        (Polynomial.aeval y (Polynomial.derivative P) * (c * Pbar ^ n))
                  _ = π (a * Pbar ^ n) +
                      π (Polynomial.aeval y (Polynomial.derivative P)) * π (c * Pbar ^ n) := by
                    have hmul :=
                      (π : polynomialPowerQuotient K P k →+* S).map_mul
                        (Polynomial.aeval y (Polynomial.derivative P))
                        (c * Pbar ^ n)
                    exact congrArg (fun t => π (a * Pbar ^ n) + t) hmul
          _ = 0 := hzero
      have hmem :
          Polynomial.aeval (y + c * Pbar ^ n) P ∈ I := by
        have hzero'' :
            Ideal.Quotient.mk I (Polynomial.aeval (y + c * Pbar ^ n) P) = 0 := by
          have hzero'' := hzero'
          rw [Ideal.Quotient.mkₐ_eq_mk] at hzero''
          exact hzero''
        exact (Ideal.Quotient.eq_zero_iff_mem).1 hzero''
      have hmem' :
          Polynomial.aeval (y + c * Pbar ^ n) P ∈
            Ideal.span ({Pbar ^ (n + 1)} : Set (polynomialPowerQuotient K P k)) := by
        simpa [I] using hmem
      simpa [Polynomial.aeval_def, Pbar] using hmem'

end

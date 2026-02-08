import Mathlib

open scoped BigOperators

/--
Let \( R \) be a Dedekind domain. Show the following:

If \( P_1, \dots, P_n \in \operatorname{Spec}(R) \) are pairwise distinct, non-zero prime ideals
and \( e_1, \dots, e_n \) are non-negative integers, there exists
\( a \in R \setminus \{0\} \) such that
\[
(a) = P_1^{e_1} \cdots P_n^{e_n} \cdot J,
\]
with \( J \subseteq R \) an ideal in whose factorization none of the \( P_i \) appear.
-/
-- A finite-inf membership lemma used to pass from componentwise membership to the product.
lemma mem_finset_inf {R ι : Type} [CommRing R] (s : Finset ι) (f : ι → Ideal R) {a : R}
    (ha : ∀ i ∈ s, a ∈ f i) : a ∈ s.inf f := by
  classical
  revert ha
  refine Finset.induction_on s ?_ ?_
  · intro _; simp
  · intro i s hi ih ha
    have hi_mem : a ∈ f i := ha i (by simp [hi])
    have hs_mem : a ∈ s.inf f := ih (fun j hj => ha j (by simp [hj]))
    have : a ∈ f i ⊓ s.inf f := (Ideal.mem_inf).2 ⟨hi_mem, hs_mem⟩
    simpa [Finset.inf_insert, hi] using this

-- Each nonzero prime ideal power contains an element of exact `p`-adic order.
lemma exists_mem_pow_notMem_pow_succ (R : Type) [CommRing R] [IsDedekindDomain R]
    {n : ℕ} (p : Fin n → PrimeSpectrum R) (h_nonzero : ∀ i, (p i).asIdeal ≠ ⊥)
    (e : Fin n → ℕ) :
    ∀ i, ∃ x : R, x ∈ (p i).1 ^ (e i) ∧ x ∉ (p i).1 ^ (e i + 1) := by
  intro i
  have hne_top : (p i).1 ≠ ⊤ := (Ideal.IsPrime.ne_top (p i).isPrime)
  simpa using
    (Ideal.exists_mem_pow_notMem_pow_succ (I := (p i).1) (hI0 := h_nonzero i) (hI1 := hne_top)
      (e := e i))

-- Chinese remainder for prime powers: build `a` with exact `p_i`-adic orders.
lemma exists_element_exact_powers (R : Type) [CommRing R] [IsDedekindDomain R]
    {n : ℕ} (p : Fin n → PrimeSpectrum R) (h_nonzero : ∀ i, (p i).asIdeal ≠ ⊥)
    (h_inj : Function.Injective p) (e : Fin n → ℕ) :
    ∃ a : R, (∀ i, a ∈ (p i).1 ^ (e i)) ∧ (∀ i, a ∉ (p i).1 ^ (e i + 1)) := by
  classical
  have hx :
      ∀ i, ∃ x : R, x ∈ (p i).1 ^ (e i) ∧ x ∉ (p i).1 ^ (e i + 1) :=
    exists_mem_pow_notMem_pow_succ R p h_nonzero e
  choose x hx_mem hx_notmem using hx
  have hprime :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), Prime ((p i).1) := by
    intro i _hi
    exact Ideal.prime_of_isPrime (h_nonzero i) (p i).isPrime
  have hcoprime :
      ∀ᵉ (i ∈ (Finset.univ : Finset (Fin n))) (j ∈ (Finset.univ : Finset (Fin n))),
        i ≠ j → (p i).1 ≠ (p j).1 := by
    intro i _hi j _hj hij hEq
    apply hij
    apply h_inj
    exact PrimeSpectrum.ext hEq
  obtain ⟨a, ha⟩ :=
    IsDedekindDomain.exists_forall_sub_mem_ideal (R := R) (s := Finset.univ)
      (P := fun i => (p i).1) (e := fun i => e i + 1) hprime hcoprime (fun i => x i)
  refine ⟨a, ?_, ?_⟩
  · intro i
    have hsub : a - x i ∈ (p i).1 ^ (e i + 1) := by
      simpa using ha i (by simp)
    have hsub' : a - x i ∈ (p i).1 ^ (e i) := by
      exact (Ideal.pow_le_pow_right (I := (p i).1) (Nat.le_succ _)) hsub
    have hsum :
        a - x i + x i ∈ (p i).1 ^ (e i) :=
      ((p i).1 ^ (e i)).add_mem hsub' (hx_mem i)
    simpa [sub_add_cancel] using hsum
  · intro i ha_mem
    have hsub : a - x i ∈ (p i).1 ^ (e i + 1) := by
      simpa using ha i (by simp)
    have hx' : x i ∈ (p i).1 ^ (e i + 1) := by
      have hdiff :
          a - (a - x i) ∈ (p i).1 ^ (e i + 1) :=
        ((p i).1 ^ (e i + 1)).sub_mem ha_mem hsub
      simpa [sub_sub_cancel] using hdiff
    exact hx_notmem i hx'

-- Membership in each prime power implies membership in their product (Dedekind domain).
lemma mem_prod_of_mem_each (R : Type) [CommRing R] [IsDedekindDomain R] {n : ℕ}
    (p : Fin n → PrimeSpectrum R) (h_nonzero : ∀ i, (p i).asIdeal ≠ ⊥)
    (h_inj : Function.Injective p) (e : Fin n → ℕ) {a : R}
    (ha : ∀ i, a ∈ (p i).1 ^ (e i)) :
    a ∈ ∏ i : Fin n, (p i).1 ^ (e i) := by
  classical
  have hprime :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), Prime ((p i).1) := by
    intro i _hi
    exact Ideal.prime_of_isPrime (h_nonzero i) (p i).isPrime
  have hcoprime :
      ∀ᵉ (i ∈ (Finset.univ : Finset (Fin n))) (j ∈ (Finset.univ : Finset (Fin n))),
        i ≠ j → (p i).1 ≠ (p j).1 := by
    intro i _hi j _hj hij hEq
    apply hij
    apply h_inj
    exact PrimeSpectrum.ext hEq
  have ha_inf :
      a ∈ (Finset.univ.inf fun i => (p i).1 ^ (e i)) :=
    mem_finset_inf (R := R) (s := Finset.univ) (f := fun i => (p i).1 ^ (e i))
      (by intro i _hi; exact ha i)
  have hprod :
      (Finset.univ.inf fun i => (p i).1 ^ (e i)) = ∏ i : Fin n, (p i).1 ^ (e i) :=
    IsDedekindDomain.inf_prime_pow_eq_prod (s := Finset.univ) (f := fun i => (p i).1) (e := e)
      hprime hcoprime
  simpa [hprod] using ha_inf

-- If the cofactor absorbed a prime, the valuation would increase.
lemma cofactor_not_divisible_by_pi (R : Type) [CommRing R] [IsDedekindDomain R] {n : ℕ}
    (p : Fin n → PrimeSpectrum R) (e : Fin n → ℕ) (a : R) (J : Ideal R)
    (hEq : Ideal.span {a} = J * ∏ i : Fin n, (p i).1 ^ (e i))
    (i : Fin n) (ha_notmem : a ∉ (p i).1 ^ (e i + 1)) :
    ¬ ∃ K : Ideal R, J = K * (p i).1 := by
  classical
  intro hK
  rcases hK with ⟨K, hK⟩
  let rest : Ideal R := (Finset.univ.erase i).prod (fun j => (p j).1 ^ (e j))
  have hprod :
      ∏ j : Fin n, (p j).1 ^ (e j) = (p i).1 ^ (e i) * rest := by
    classical
    simpa [rest] using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin n)))
        (f := fun j => (p j).1 ^ (e j)) (a := i) (h := by simp)).symm
  have hdiv : (p i).1 ^ (e i + 1) ∣ Ideal.span {a} := by
    refine ⟨K * rest, ?_⟩
    calc
      Ideal.span {a} = J * ∏ j : Fin n, (p j).1 ^ (e j) := hEq
      _ = (K * (p i).1) * ∏ j : Fin n, (p j).1 ^ (e j) := by simp [hK]
      _ = (K * (p i).1) * ((p i).1 ^ (e i) * rest) := by simp [hprod]
      _ = (p i).1 ^ (e i + 1) * (K * rest) := by
        simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
  have ha_mem : a ∈ (p i).1 ^ (e i + 1) := (Ideal.dvd_span_singleton).1 hdiv
  exact ha_notmem ha_mem

theorem exists_factor_principal_ideal (R : Type) [CommRing R] [IsDedekindDomain R]
    (n : ℕ) (p : (Fin n) → PrimeSpectrum R) (h_nonzero : ∀ i, (p i).asIdeal ≠ ⊥)
    (h_inj : Function.Injective p) (e : (Fin n) → ℕ) :
    ∃ (a : R) (J : Ideal R), a ≠ 0 ∧ Ideal.span {a} = J * ∏ (i : Fin n), (p i).1 ^ (e i) ∧
    (∀ (i : Fin n), ¬ ∃ (K : Ideal R), J = K * (p i).1) := by
  classical
  by_cases hzero : n = 0
  · subst hzero
    refine ⟨1, ⊤, by simp, ?_, ?_⟩
    · simp
    · intro i
      exact (Fin.elim0 i)
  · have hpos : 0 < n := Nat.pos_of_ne_zero hzero
    obtain ⟨a, ha_mem, ha_notmem⟩ :=
      exists_element_exact_powers R p h_nonzero h_inj e
    have ha_prod :
        a ∈ ∏ i : Fin n, (p i).1 ^ (e i) :=
      mem_prod_of_mem_each R p h_nonzero h_inj e ha_mem
    have hle :
        Ideal.span {a} ≤ ∏ i : Fin n, (p i).1 ^ (e i) :=
      (Ideal.span_singleton_le_iff_mem (I := ∏ i : Fin n, (p i).1 ^ (e i))).2 ha_prod
    obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
    have hJ' : Ideal.span {a} = J * ∏ i : Fin n, (p i).1 ^ (e i) := by
      simpa [mul_comm] using hJ
    have ha_ne : a ≠ 0 := by
      intro hzero_a
      let i0 : Fin n := ⟨0, hpos⟩
      have : a ∈ (p i0).1 ^ (e i0 + 1) := by
        simp [hzero_a]
      exact ha_notmem i0 this
    refine ⟨a, J, ha_ne, hJ', ?_⟩
    intro i
    exact cofactor_not_divisible_by_pi R p e a J hJ' i (ha_notmem i)

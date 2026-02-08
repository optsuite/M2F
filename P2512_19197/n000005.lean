import Mathlib

open scoped BigOperators

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for n000005: `eps` lies in the maximal ideal from `hmax`. -/
lemma helperFor_n000005_eps_mem_maximalIdeal
    (K R : Type*) [CommRing K] [CommRing R] [IsLocalRing R]
    (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R)) :
    eps ∈ IsLocalRing.maximalIdeal R := by
  have hmem : eps ∈ Ideal.span ({eps} : Set R) := by
    exact Ideal.subset_span (by simp : eps ∈ ({eps} : Set R))
  simpa [hmax] using hmem

/-- Helper for n000005: compute `Phi.comp` with the quotient map as `aeval`. -/
lemma helperFor_n000005_Phi_comp_mk_eq_aeval
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R]
    (k : ℕ) (eps : R)
    (Phi :
      AlgHom K (Polynomial K ⧸ Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))) R)
    (hPhi : Phi (Ideal.Quotient.mk _ Polynomial.X) = eps) :
    Phi.comp (Ideal.Quotient.mkₐ K (Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))))
      = Polynomial.aeval eps := by
  classical
  ext
  simp [Ideal.Quotient.mkₐ_eq_mk, hPhi]

/-- Helper for n000005: `eps^j` is not in `(eps^(j+1))` for `j < k`. -/
lemma helperFor_n000005_eps_pow_not_mem_span_pow_succ
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (k : ℕ) (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R))
    (hPow_pred : eps ^ (k - 1) ≠ 0) :
    ∀ {j : ℕ}, j < k → eps ^ j ∉ Ideal.span ({eps ^ (j + 1)} : Set R) := by
  classical
  intro j hj hmem
  rcases Ideal.mem_span_singleton'.1 hmem with ⟨r, hr⟩
  have heps_max :
      eps ∈ IsLocalRing.maximalIdeal R :=
    helperFor_n000005_eps_mem_maximalIdeal (K := K) (R := R) (eps := eps) hmax
  have hmem_max : r * eps ∈ IsLocalRing.maximalIdeal R := by
    exact Ideal.mul_mem_left (IsLocalRing.maximalIdeal R) r heps_max
  have hnonunits : r * eps ∈ nonunits R := by
    exact (IsLocalRing.mem_maximalIdeal (R := R) (x := r * eps)).1 hmem_max
  have hunit : IsUnit (1 - r * eps) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (R := R) (a := r * eps) hnonunits
  have hmul : eps ^ j * (r * eps) = r * eps ^ (j + 1) := by
    calc
      eps ^ j * (r * eps) = (eps ^ j * r) * eps := by
        simp [mul_assoc]
      _ = (r * eps ^ j) * eps := by
        simp [mul_comm]
      _ = r * (eps ^ j * eps) := by
        simp [mul_assoc]
      _ = r * eps ^ (j + 1) := by
        simp [pow_succ]
  have hfactor : eps ^ j * (1 - r * eps) = 0 := by
    calc
      eps ^ j * (1 - r * eps) = eps ^ j - eps ^ j * (r * eps) := by
        ring
      _ = eps ^ j - r * eps ^ (j + 1) := by
        simp [hmul]
      _ = 0 := by
        simp [hr]
  have hfactor' : (1 - r * eps) * eps ^ j = 0 := by
    simpa [mul_comm, mul_assoc] using hfactor
  have hmul0 : (1 - r * eps) * eps ^ j = (1 - r * eps) * 0 := by
    simpa [mul_zero] using hfactor'
  have hzero : eps ^ j = 0 :=
    (IsUnit.mul_left_cancel hunit) hmul0
  have hle : j ≤ k - 1 := Nat.le_pred_of_lt hj
  have hzero' : eps ^ (k - 1) = 0 := pow_eq_zero_of_le hle hzero
  exact hPow_pred hzero'

/-- Helper for n000005: a nonzero element of `K` maps to a unit in `R`. -/
lemma helperFor_n000005_isUnit_algebraMap_of_ne_zero
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R) :
    ∀ {a : K}, a ≠ 0 → IsUnit (algebraMap K R a) := by
  intro a ha
  have hnot : (algebraMap K R a) ∉ IsLocalRing.maximalIdeal R := by
    intro hmem
    have hker_mem : (algebraMap K R a) ∈ RingHom.ker pi := by
      simpa [hker] using hmem
    have hzero : pi (algebraMap K R a) = 0 :=
      (RingHom.mem_ker).1 hker_mem
    have : a = 0 := by
      simpa [hpi a] using hzero
    exact ha this
  exact (IsLocalRing.notMem_maximalIdeal (R := R) (x := algebraMap K R a)).1 hnot

/-- Helper for n000005: decomposition of `r` as `algebraMap (pi r) + eps * r'`. -/
lemma helperFor_n000005_exists_eq_algebraMap_add_eps_mul
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R)
    (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R)) :
    ∀ r : R, ∃ r' : R, r = algebraMap K R (pi r) + eps * r' := by
  intro r
  have hker_mem : r - algebraMap K R (pi r) ∈ RingHom.ker pi := by
    apply RingHom.mem_ker.mpr
    calc
      pi (r - algebraMap K R (pi r)) = pi r - pi (algebraMap K R (pi r)) := by
        simp
      _ = pi r - pi r := by
        simp [hpi]
      _ = 0 := by
        simp
  have hmem_max : r - algebraMap K R (pi r) ∈ IsLocalRing.maximalIdeal R := by
    simpa [hker] using hker_mem
  have hmem_span : r - algebraMap K R (pi r) ∈ Ideal.span ({eps} : Set R) := by
    simpa [hmax] using hmem_max
  rcases Ideal.mem_span_singleton'.1 hmem_span with ⟨r', hr'⟩
  refine ⟨r', ?_⟩
  calc
    r = algebraMap K R (pi r) + (r - algebraMap K R (pi r)) := by
      abel
    _ = algebraMap K R (pi r) + r' * eps := by
      simp [hr']
    _ = algebraMap K R (pi r) + eps * r' := by
      simp [mul_comm]

/-- Helper for n000005: iterated decomposition of `r` with respect to `eps`. -/
lemma helperFor_n000005_iterated_decomposition
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R)
    (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R)) :
    ∀ (n : ℕ) (r : R), ∃ (a : ℕ → K) (r' : R),
      r = (∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ i) + eps ^ n * r' := by
  classical
  intro n
  induction' n with n ih
  · intro r
    refine ⟨fun _ => 0, r, ?_⟩
    simp
  · intro r
    rcases helperFor_n000005_exists_eq_algebraMap_add_eps_mul (K := K) (R := R)
        (pi := pi) (hpi := hpi) (hker := hker) (eps := eps) (hmax := hmax) r with ⟨r₁, hr₁⟩
    rcases ih r₁ with ⟨a, r', hr'⟩
    let a' : ℕ → K := fun i => Nat.casesOn i (pi r) (fun j => a j)
    refine ⟨a', r', ?_⟩
    have hsum_shift :
        ∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ (i + 1)
          = eps * (∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ i) := by
      symm
      calc
        eps * (∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ i)
            = ∑ i ∈ Finset.range n, eps * (algebraMap K R (a i) * eps ^ i) := by
                simp [Finset.mul_sum]
        _ = ∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ (i + 1) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [pow_succ, mul_assoc, mul_comm]
    have hsum_head :
        ∑ i ∈ Finset.range (n + 1), algebraMap K R (a' i) * eps ^ i
          = algebraMap K R (pi r) + eps * (∑ i ∈ Finset.range n,
              algebraMap K R (a i) * eps ^ i) := by
      calc
        ∑ i ∈ Finset.range (n + 1), algebraMap K R (a' i) * eps ^ i
            =
              (∑ i ∈ Finset.range n, algebraMap K R (a' (i + 1)) * eps ^ (i + 1)) +
              algebraMap K R (a' 0) * eps ^ 0 := by
              simpa using
                (Finset.sum_range_succ' (f := fun i =>
                  algebraMap K R (a' i) * eps ^ i) n)
        _ =
            (∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ (i + 1)) +
              algebraMap K R (pi r) * eps ^ 0 := by
              simp [a']
        _ = eps * (∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ i) +
              algebraMap K R (pi r) * eps ^ 0 := by
              simp [hsum_shift]
        _ = algebraMap K R (pi r) + eps * (∑ i ∈ Finset.range n,
              algebraMap K R (a i) * eps ^ i) := by
              simp [pow_zero, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
                add_assoc]
    calc
      r = algebraMap K R (pi r) + eps * r₁ := hr₁
      _ = algebraMap K R (pi r) +
            eps * ((∑ i ∈ Finset.range n, algebraMap K R (a i) * eps ^ i) + eps ^ n * r') := by
            simp [hr']
      _ =
          (algebraMap K R (pi r) + eps * (∑ i ∈ Finset.range n,
              algebraMap K R (a i) * eps ^ i)) +
            eps ^ (n + 1) * r' := by
            simp [pow_succ, mul_add, mul_assoc, mul_left_comm, mul_comm, add_assoc]
      _ =
          (∑ i ∈ Finset.range (n + 1), algebraMap K R (a' i) * eps ^ i) +
            eps ^ (n + 1) * r' := by
            simp [hsum_head, add_assoc]

/-- Helper for n000005: if `u` is a unit and `u * x ∈ I`, then `x ∈ I`. -/
lemma helperFor_n000005_mem_of_isUnit_mul_mem
    (R : Type*) [CommRing R] (I : Ideal R) {u x : R} :
    IsUnit u → u * x ∈ I → x ∈ I := by
  intro hu hx
  rcases hu with ⟨u', rfl⟩
  have hx' : (↑(u'⁻¹) : R) * ((↑u' : R) * x) ∈ I :=
    Ideal.mul_mem_left I (↑(u'⁻¹) : R) hx
  simpa [mul_assoc] using hx'

/-- Helper for n000005: surjectivity of `Phi` via the iterated decomposition. -/
lemma helperFor_n000005_surjective_Phi
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (k : ℕ)
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R)
    (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R))
    (hPow : eps ^ k = 0)
    (Phi :
      AlgHom K (Polynomial K ⧸ Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))) R)
    (hPhi : Phi (Ideal.Quotient.mk _ Polynomial.X) = eps) :
    Function.Surjective Phi := by
  classical
  intro r
  rcases helperFor_n000005_iterated_decomposition (K := K) (R := R)
      (pi := pi) (hpi := hpi) (hker := hker) (eps := eps) (hmax := hmax) k r
      with ⟨a, r', hr⟩
  let p : Polynomial K :=
    ∑ i ∈ Finset.range k, Polynomial.C (a i) * Polynomial.X ^ i
  refine ⟨Ideal.Quotient.mk _ p, ?_⟩
  have hcomp :
      Phi.comp (Ideal.Quotient.mkₐ K (Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))))
        = Polynomial.aeval eps :=
    helperFor_n000005_Phi_comp_mk_eq_aeval (K := K) (R := R) (k := k) (eps := eps)
      (Phi := Phi) hPhi
  have hsum :
      Polynomial.aeval eps p =
        ∑ i ∈ Finset.range k, algebraMap K R (a i) * eps ^ i := by
    calc
      Polynomial.aeval eps p
          = ∑ i ∈ Finset.range k,
              Polynomial.aeval eps (Polynomial.C (a i) * Polynomial.X ^ i) := by
              simp [p, map_sum]
      _ = ∑ i ∈ Finset.range k, algebraMap K R (a i) * eps ^ i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.aeval_monomial]
  have hr' :
      r = ∑ i ∈ Finset.range k, algebraMap K R (a i) * eps ^ i := by
    calc
      r =
          (∑ i ∈ Finset.range k, algebraMap K R (a i) * eps ^ i) + eps ^ k * r' := hr
      _ = ∑ i ∈ Finset.range k, algebraMap K R (a i) * eps ^ i := by
          simp [hPow]
  calc
    Phi (Ideal.Quotient.mk _ p)
        = (Phi.comp (Ideal.Quotient.mkₐ K
            (Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))))) p := by
            simp [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    _ = Polynomial.aeval eps p := by
          simpa [hcomp]
    _ = ∑ i ∈ Finset.range k, algebraMap K R (a i) * eps ^ i := hsum
    _ = r := hr'.symm

/-- Helper for n000005: quotient class equals class of the `modByMonic` remainder. -/
lemma helperFor_n000005_mk_eq_mk_modByMonic_X_pow
    (K : Type*) [CommRing K] (k : ℕ) :
    ∀ p : Polynomial K,
      Ideal.Quotient.mk (Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))) p
        = Ideal.Quotient.mk _ (p %ₘ (Polynomial.X ^ k)) := by
  classical
  intro p
  apply Ideal.Quotient.eq.2
  let q : Polynomial K := Polynomial.X ^ k
  have hq : q.Monic := by
    simpa [q] using (Polynomial.monic_X_pow k)
  have hmem : p - p %ₘ q = q * (p /ₘ q) := by
    have h := Polynomial.modByMonic_add_div p hq
    calc
      p - p %ₘ q = (p %ₘ q + q * (p /ₘ q)) - p %ₘ q := by
        simpa [h]
      _ = q * (p /ₘ q) := by
        ring
  refine Ideal.mem_span_singleton'.2 ?_
  refine ⟨p /ₘ q, ?_⟩
  calc
    (p /ₘ q) * q = q * (p /ₘ q) := by
      simp [mul_comm]
    _ = p - p %ₘ q := by
      symm
      exact hmem

/-- Helper for n000005: degree-`< k` polynomials with `aeval` zero are zero. -/
lemma helperFor_n000005_poly_eq_zero_of_natDegree_lt_aeval_eq_zero
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (k : ℕ) (eps : R)
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R))
    (hPow_pred : eps ^ (k - 1) ≠ 0) :
    ∀ p : Polynomial K, p.natDegree < k → Polynomial.aeval eps p = 0 → p = 0 := by
  classical
  intro p hpdeg hzero
  by_contra hpne
  have hex : ∃ j, j < k ∧ p.coeff j ≠ 0 := by
    refine ⟨p.natDegree, hpdeg, ?_⟩
    have hlead : p.leadingCoeff ≠ 0 :=
      (Polynomial.leadingCoeff_ne_zero).2 hpne
    simpa [Polynomial.coeff_natDegree] using hlead
  let j := Nat.find hex
  have hj_lt : j < k := (Nat.find_spec hex).1
  have hj_coeff : p.coeff j ≠ 0 := (Nat.find_spec hex).2
  have hcoeff_lt : ∀ i < j, p.coeff i = 0 := by
    intro i hi
    have hmin : ¬ (i < k ∧ p.coeff i ≠ 0) := by
      intro hPi
      have hle : j ≤ i := Nat.find_min' hex hPi
      exact (not_le_of_gt hi) hle
    by_contra hne
    exact hmin ⟨lt_trans hi hj_lt, hne⟩
  let f : ℕ → R := fun i => algebraMap K R (p.coeff i) * eps ^ i
  have hzero' :
      Polynomial.aeval eps
          (∑ i ∈ Finset.range k, Polynomial.C (p.coeff i) * Polynomial.X ^ i) = 0 := by
    have hzero'' := hzero
    rw [Polynomial.as_sum_range_C_mul_X_pow' p hpdeg] at hzero''
    exact hzero''
  have hsum : (∑ i ∈ Finset.range k, f i) = 0 := by
    have hsum' :
        Polynomial.aeval eps
            (∑ i ∈ Finset.range k, Polynomial.C (p.coeff i) * Polynomial.X ^ i) =
          ∑ i ∈ Finset.range k, f i := by
      calc
        Polynomial.aeval eps
            (∑ i ∈ Finset.range k, Polynomial.C (p.coeff i) * Polynomial.X ^ i)
            =
            ∑ i ∈ Finset.range k,
              Polynomial.aeval eps (Polynomial.C (p.coeff i) * Polynomial.X ^ i) := by
                simp [map_sum]
        _ = ∑ i ∈ Finset.range k, f i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [f, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.aeval_monomial]
    have hsum'' : (∑ i ∈ Finset.range k, f i) = 0 := by
      calc
        ∑ i ∈ Finset.range k, f i
            = Polynomial.aeval eps
                (∑ i ∈ Finset.range k, Polynomial.C (p.coeff i) * Polynomial.X ^ i) := by
                symm
                exact hsum'
        _ = 0 := hzero'
    exact hsum''
  have hsum_before : ∑ i ∈ Finset.range j, f i = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hij : i < j := (Finset.mem_range.1 hi)
    have hcoeffi : p.coeff i = 0 := hcoeff_lt i hij
    simp [f, hcoeffi]
  have hsum_head : ∑ i ∈ Finset.range (j + 1), f i = f j := by
    calc
      ∑ i ∈ Finset.range (j + 1), f i
          = ∑ i ∈ Finset.range j, f i + f j := by
              simpa using (Finset.sum_range_succ f j)
      _ = 0 + f j := by
            simp [hsum_before]
      _ = f j := by
            simp
  have hk' : j + 1 ≤ k := Nat.succ_le_of_lt hj_lt
  have hsum_split :
      ∑ i ∈ Finset.range k, f i =
        (∑ i ∈ Finset.range (j + 1), f i) +
          ∑ i ∈ Finset.range (k - (j + 1)), f (j + 1 + i) := by
    simpa [Nat.add_sub_of_le hk'] using
      (Finset.sum_range_add f (j + 1) (k - (j + 1)))
  let rest : R := ∑ i ∈ Finset.range (k - (j + 1)), f (j + 1 + i)
  have hsum_eq : ∑ i ∈ Finset.range k, f i = f j + rest := by
    calc
      ∑ i ∈ Finset.range k, f i
          = (∑ i ∈ Finset.range (j + 1), f i) + rest := by
              simp [hsum_split, rest]
      _ = f j + rest := by
            simp [hsum_head, add_assoc]
  let I : Ideal R := Ideal.span ({eps ^ (j + 1)} : Set R)
  have hterm_mem : ∀ i : ℕ, f (j + 1 + i) ∈ I := by
    intro i
    refine Ideal.mem_span_singleton'.2 ?_
    refine ⟨algebraMap K R (p.coeff (j + 1 + i)) * eps ^ i, ?_⟩
    calc
      (algebraMap K R (p.coeff (j + 1 + i)) * eps ^ i) * eps ^ (j + 1)
          = algebraMap K R (p.coeff (j + 1 + i)) * eps ^ (j + 1 + i) := by
            simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
      _ = f (j + 1 + i) := by
            simp [f, add_comm, add_left_comm, add_assoc]
  have hmem_rest : rest ∈ I := by
    refine I.sum_mem ?_
    intro i hi
    simpa [rest] using hterm_mem i
  have hsum0 : f j + rest = 0 := by
    calc
      f j + rest = ∑ i ∈ Finset.range k, f i := by
        symm
        exact hsum_eq
      _ = 0 := hsum
  have hfj_eq : f j = -rest :=
    eq_neg_of_add_eq_zero_left hsum0
  have hfj_mem : f j ∈ I := by
    have hneg : -rest ∈ I := I.neg_mem hmem_rest
    simpa [hfj_eq] using hneg
  have hunit : IsUnit (algebraMap K R (p.coeff j)) :=
    helperFor_n000005_isUnit_algebraMap_of_ne_zero (K := K) (R := R) (pi := pi)
      (hpi := hpi) (hker := hker) hj_coeff
  have hmem_eps : eps ^ j ∈ I := by
    have hmem' : (algebraMap K R (p.coeff j)) * eps ^ j ∈ I := by
      simpa [f] using hfj_mem
    exact helperFor_n000005_mem_of_isUnit_mul_mem (R := R) I hunit hmem'
  have hnot :
      eps ^ j ∉ Ideal.span ({eps ^ (j + 1)} : Set R) :=
    helperFor_n000005_eps_pow_not_mem_span_pow_succ (K := K) (R := R) (k := k) (eps := eps)
      (hmax := hmax) (hPow_pred := hPow_pred) hj_lt
  exact hnot hmem_eps

/-- Helper for n000005: injectivity of `Phi` via reduction to degree `< k` polynomials. -/
lemma helperFor_n000005_injective_Phi
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (k : ℕ) (hk : 0 < k)
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R)
    (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R))
    (hPow_pred : eps ^ (k - 1) ≠ 0)
    (Phi :
      AlgHom K (Polynomial K ⧸ Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))) R)
    (hPhi : Phi (Ideal.Quotient.mk _ Polynomial.X) = eps) :
    Function.Injective Phi := by
  classical
  intro q₁ q₂ hq
  obtain ⟨p₁, rfl⟩ := Ideal.Quotient.mk_surjective q₁
  obtain ⟨p₂, rfl⟩ := Ideal.Quotient.mk_surjective q₂
  let I : Ideal (Polynomial K) := Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))
  have hmk₁ :
      Ideal.Quotient.mk I p₁ = Ideal.Quotient.mk I (p₁ %ₘ (Polynomial.X ^ k)) :=
    helperFor_n000005_mk_eq_mk_modByMonic_X_pow (K := K) (k := k) p₁
  have hmk₂ :
      Ideal.Quotient.mk I p₂ = Ideal.Quotient.mk I (p₂ %ₘ (Polynomial.X ^ k)) :=
    helperFor_n000005_mk_eq_mk_modByMonic_X_pow (K := K) (k := k) p₂
  have hq' :
      Phi (Ideal.Quotient.mk I (p₁ %ₘ (Polynomial.X ^ k))) =
        Phi (Ideal.Quotient.mk I (p₂ %ₘ (Polynomial.X ^ k))) := by
    simpa [← hmk₁, ← hmk₂] using hq
  have hcomp :
      Phi.comp (Ideal.Quotient.mkₐ K I) = Polynomial.aeval eps :=
    helperFor_n000005_Phi_comp_mk_eq_aeval (K := K) (R := R) (k := k) (eps := eps)
      (Phi := Phi) hPhi
  have hPhi_aeval :
      Polynomial.aeval eps (p₁ %ₘ (Polynomial.X ^ k)) =
        Polynomial.aeval eps (p₂ %ₘ (Polynomial.X ^ k)) := by
    have hq'' :
        (Phi.comp (Ideal.Quotient.mkₐ K I)) (p₁ %ₘ (Polynomial.X ^ k)) =
          (Phi.comp (Ideal.Quotient.mkₐ K I)) (p₂ %ₘ (Polynomial.X ^ k)) := by
      simpa [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] using hq'
    simpa [hcomp] using hq''
  have hzero_sub :
      Polynomial.aeval eps (p₁ %ₘ (Polynomial.X ^ k) - p₂ %ₘ (Polynomial.X ^ k)) = 0 := by
    simpa [map_sub, hPhi_aeval]
  have hqne : (Polynomial.X ^ k : Polynomial K) ≠ 1 := by
    intro hqeq
    have hcoeff := congrArg (fun q : Polynomial K => q.coeff 0) hqeq
    have hk' : k ≠ 0 := ne_of_gt hk
    have hk'' : (0 : ℕ) ≠ k := by
      simpa [eq_comm] using hk'
    have hcoeff' : (0 : K) = 1 := by
      simpa [Polynomial.coeff_X_pow, Polynomial.coeff_one, hk''] using hcoeff
    have h01 : (0 : K) ≠ 1 := by
      intro h0
      have hR : (0 : R) = 1 := by
        simpa using congrArg (algebraMap K R) h0
      exact (zero_ne_one (α := R)) hR
    exact h01 hcoeff'
  have hdeg₁ :
      (p₁ %ₘ (Polynomial.X ^ k)).natDegree < k := by
    have hlt :
        (p₁ %ₘ (Polynomial.X ^ k)).natDegree < (Polynomial.X ^ k : Polynomial K).natDegree :=
      Polynomial.natDegree_modByMonic_lt p₁ (Polynomial.monic_X_pow k) hqne
    exact lt_of_lt_of_le hlt (Polynomial.natDegree_X_pow_le k)
  have hdeg₂ :
      (p₂ %ₘ (Polynomial.X ^ k)).natDegree < k := by
    have hlt :
        (p₂ %ₘ (Polynomial.X ^ k)).natDegree < (Polynomial.X ^ k : Polynomial K).natDegree :=
      Polynomial.natDegree_modByMonic_lt p₂ (Polynomial.monic_X_pow k) hqne
    exact lt_of_lt_of_le hlt (Polynomial.natDegree_X_pow_le k)
  have hdeg_sub :
      (p₁ %ₘ (Polynomial.X ^ k) - p₂ %ₘ (Polynomial.X ^ k)).natDegree < k := by
    have hle :
        (p₁ %ₘ (Polynomial.X ^ k) - p₂ %ₘ (Polynomial.X ^ k)).natDegree ≤
          max (p₁ %ₘ (Polynomial.X ^ k)).natDegree (p₂ %ₘ (Polynomial.X ^ k)).natDegree :=
      Polynomial.natDegree_sub_le _ _
    have hmax :
        max (p₁ %ₘ (Polynomial.X ^ k)).natDegree
            (p₂ %ₘ (Polynomial.X ^ k)).natDegree < k :=
      (max_lt_iff).2 ⟨hdeg₁, hdeg₂⟩
    exact lt_of_le_of_lt hle hmax
  have hzero_poly :
      p₁ %ₘ (Polynomial.X ^ k) - p₂ %ₘ (Polynomial.X ^ k) = 0 :=
    helperFor_n000005_poly_eq_zero_of_natDegree_lt_aeval_eq_zero (K := K) (R := R)
      (k := k) (eps := eps) (pi := pi) (hpi := hpi) (hker := hker) (hmax := hmax)
      (hPow_pred := hPow_pred) _ hdeg_sub hzero_sub
  have hpeq :
      p₁ %ₘ (Polynomial.X ^ k) = p₂ %ₘ (Polynomial.X ^ k) := by
    simpa using sub_eq_zero.1 hzero_poly
  have hmk₁' :
      Ideal.Quotient.mk I p₁ = Ideal.Quotient.mk I (p₁ %ₘ (Polynomial.X ^ k)) := hmk₁
  have hmk₂' :
      Ideal.Quotient.mk I p₂ = Ideal.Quotient.mk I (p₂ %ₘ (Polynomial.X ^ k)) := hmk₂
  calc
    Ideal.Quotient.mk I p₁
        = Ideal.Quotient.mk I (p₁ %ₘ (Polynomial.X ^ k)) := hmk₁'
    _ = Ideal.Quotient.mk I (p₂ %ₘ (Polynomial.X ^ k)) := by
          simp [hpeq]
    _ = Ideal.Quotient.mk I p₂ := by
          symm
          exact hmk₂'

/-- n000005: (Corrected statement) In the setup of the previous subgoal: `R` is a local `K`-algebra
with a splitting `pi : R → K` of `algebraMap K R`, the maximal ideal is generated by a nilpotent
element `eps` of nilpotence index `k`. Then the induced `K`-algebra homomorphism
`K[X]/(X^k) → R` sending `X̄ ↦ eps` is an isomorphism. -/
theorem truncatedPolynomialAlgHom_isIso
    (K R : Type*) [CommRing K] [CommRing R] [Algebra K R] [IsLocalRing R]
    (k : ℕ) (hk : 0 < k)
    (pi : R →+* K)
    (hpi : ∀ a : K, pi (algebraMap K R a) = a)
    (hker : RingHom.ker pi = IsLocalRing.maximalIdeal R)
    (eps : R)
    (hmax : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R))
    (hPow : eps ^ k = 0)
    (hPow_pred : eps ^ (k - 1) ≠ 0)
    (Phi :
      AlgHom K (Polynomial K ⧸ Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))) R)
    (hPhi : Phi (Ideal.Quotient.mk _ Polynomial.X) = eps) :
    ∃ e :
      AlgEquiv K (Polynomial K ⧸ Ideal.span ({Polynomial.X ^ k} : Set (Polynomial K))) R,
      e.toAlgHom = Phi := by
  classical
  have hsurj :
      Function.Surjective Phi :=
    helperFor_n000005_surjective_Phi (K := K) (R := R) (k := k) (pi := pi) (hpi := hpi)
      (hker := hker) (eps := eps) (hmax := hmax) (hPow := hPow) (Phi := Phi) hPhi
  have hinj :
      Function.Injective Phi :=
    helperFor_n000005_injective_Phi (K := K) (R := R) (k := k) (hk := hk) (pi := pi)
      (hpi := hpi) (hker := hker) (eps := eps) (hmax := hmax) (hPow_pred := hPow_pred)
      (Phi := Phi) hPhi
  have hbij : Function.Bijective Phi := ⟨hinj, hsurj⟩
  refine ⟨AlgEquiv.ofBijective Phi hbij, ?_⟩
  rfl

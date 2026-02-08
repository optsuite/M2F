import Mathlib

open Ideal
open scoped BigOperators Polynomial

/-!
This file proves that the binomial ideal `(x^i - y^j)` is prime in `R[x,y]` (modeled as
`MvPolynomial (Fin 2) R`) when `R` is a domain and `i,j` are positive and coprime.

The proof reduces to the bivariate polynomial ring `R[X][Y]` using the algebra equivalence
`Polynomial.Bivariate.equivMvPolynomial`, then identifies the ideal as the kernel of the
parametrization `X ↦ t^j`, `Y ↦ t^i` into `R[t]`. Kernel ideals in a domain are prime.
-/

/-! ### A small arithmetic lemma for “coprime degree bookkeeping” -/

-- If `i` and `j` are coprime, the representation `i*b + j*a` is unique in the `b`-slot
-- when `b` is restricted to `< j`.
private lemma nat_repr_unique_of_coprime {i j a a' b b' : ℕ}
    (h : Nat.Coprime i j) (hb : b < j) (hb' : b' < j)
    (hEq : i * b + j * a = i * b' + j * a') : b = b' := by
  cases le_total b b' with
  | inl hbb' =>
      have hbdecomp : i * b' = i * b + i * (b' - b) := by
        calc
          i * b' = i * (b + (b' - b)) := by simp [Nat.add_sub_of_le hbb']
          _ = i * b + i * (b' - b) := by simp [Nat.mul_add]
      have hEq' : i * b + j * a = i * b + (i * (b' - b) + j * a') := by
        simpa [hbdecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq
      have hjEq : j * a = i * (b' - b) + j * a' := Nat.add_left_cancel hEq'
      have hjdvd_mul : j ∣ i * (b' - b) := by
        have hsum : j ∣ i * (b' - b) + j * a' := by
          -- Rewrite the goal to `j ∣ j * a` using `hjEq`.
          rw [← hjEq]
          exact Nat.dvd_mul_right j a
        have hsum' : j ∣ j * a' + i * (b' - b) := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
        exact (Nat.dvd_add_iff_right (Nat.dvd_mul_right j a')).2 hsum'
      have hjdvd : j ∣ b' - b := by
        have : j ∣ (b' - b) * i := by simpa [Nat.mul_comm] using hjdvd_mul
        exact (h.symm).dvd_of_dvd_mul_right this
      have hlt : b' - b < j := lt_of_le_of_lt (Nat.sub_le _ _) hb'
      have hbsub0 : b' - b = 0 := Nat.eq_zero_of_dvd_of_lt hjdvd hlt
      have hb'le : b' ≤ b := (Nat.sub_eq_zero_iff_le).1 hbsub0
      exact le_antisymm hbb' hb'le
  | inr hbb' =>
      -- symmetric case
      have hbdecomp : i * b = i * b' + i * (b - b') := by
        calc
          i * b = i * (b' + (b - b')) := by simp [Nat.add_sub_of_le hbb']
          _ = i * b' + i * (b - b') := by simp [Nat.mul_add]
      have hEq' : i * b' + j * a' = i * b' + (i * (b - b') + j * a) := by
        simpa [hbdecomp, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hEq.symm
      have hjEq : j * a' = i * (b - b') + j * a := Nat.add_left_cancel hEq'
      have hjdvd_mul : j ∣ i * (b - b') := by
        have hsum : j ∣ i * (b - b') + j * a := by
          -- Rewrite the goal to `j ∣ j * a'` using `hjEq`.
          rw [← hjEq]
          exact Nat.dvd_mul_right j a'
        have hsum' : j ∣ j * a + i * (b - b') := by
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum
        exact (Nat.dvd_add_iff_right (Nat.dvd_mul_right j a)).2 hsum'
      have hjdvd : j ∣ b - b' := by
        have : j ∣ (b - b') * i := by simpa [Nat.mul_comm] using hjdvd_mul
        exact (h.symm).dvd_of_dvd_mul_right this
      have hlt : b - b' < j := lt_of_le_of_lt (Nat.sub_le _ _) hb
      have hbsub0 : b - b' = 0 := Nat.eq_zero_of_dvd_of_lt hjdvd hlt
      have hble : b ≤ b' := (Nat.sub_eq_zero_iff_le).1 hbsub0
      exact le_antisymm hble hbb'

/-! ### Injectivity on “reduced” bivariate polynomials under the parametrization -/

-- If `r : R[X][Y]` has `Y`-degree `< j`, then evaluating `X ↦ t^j`, `Y ↦ t^i` is injective
-- (coprimeness prevents degree collisions between distinct `Y`-exponents).
private lemma bivariate_eval₂_eq_zero_of_natDegree_lt {R : Type*} [CommRing R] {i j : ℕ}
    (hj : 0 < j) (hcop : Nat.Coprime i j) {r : Polynomial (R[X])} (hr : r.natDegree < j)
    (hEval :
      Polynomial.eval₂ (f := ((Polynomial.expand R j : R[X] →ₐ[R] R[X]) : R[X] →+* R[X]))
        (x := (Polynomial.X : R[X]) ^ i) r = 0) :
    r = 0 := by
  classical
  -- Show each coefficient `r.coeff b` vanishes for `b < j` by looking at coefficients in `R[t]`
  -- at degrees `a*j + i*b`.
  have hcoeff_reduced :
      ∀ (a b : ℕ), b < j →
        ((Polynomial.eval₂
            (f := ((Polynomial.expand R j : R[X] →ₐ[R] R[X]) : R[X] →+* R[X]))
            (x := (Polynomial.X : R[X]) ^ i) r).coeff (a * j + i * b) = (r.coeff b).coeff a) := by
    intro a b hb
    let φ : R[X] →+* R[X] := ((Polynomial.expand R j : R[X] →ₐ[R] R[X]) : R[X] →+* R[X])
    let x : R[X] := (Polynomial.X : R[X]) ^ i
    have hbmem : b ∈ Finset.range j := Finset.mem_range.2 hb
    have hsum :
        Polynomial.eval₂ (f := φ) (x := x) r =
          ∑ k ∈ Finset.range j, φ (r.coeff k) * x ^ k := by
      simp [Polynomial.eval₂_eq_sum_range' (f := φ) (p := r) (hn := hr) (x := x)]
    -- Take coefficients at `a*j + i*b` in the sum and isolate the unique contributing term.
    have hcoeff_sum :
        (Polynomial.eval₂ (f := φ) (x := x) r).coeff (a * j + i * b) =
          ∑ k ∈ Finset.range j, (φ (r.coeff k) * x ^ k).coeff (a * j + i * b) := by
      calc
        (Polynomial.eval₂ (f := φ) (x := x) r).coeff (a * j + i * b) =
            (∑ k ∈ Finset.range j, φ (r.coeff k) * x ^ k).coeff (a * j + i * b) := by
              exact congrArg (fun p : R[X] => p.coeff (a * j + i * b)) hsum
        _ = ∑ k ∈ Finset.range j, (φ (r.coeff k) * x ^ k).coeff (a * j + i * b) := by
              rw [Polynomial.finset_sum_coeff]
    -- Reduce the RHS sum to the single index `k = b`.
    have hsingle :
        (∑ k ∈ Finset.range j, (φ (r.coeff k) * x ^ k).coeff (a * j + i * b)) =
          (φ (r.coeff b) * x ^ b).coeff (a * j + i * b) := by
      refine Finset.sum_eq_single b ?_ ?_
      · intro k hk hkne
        have hklt : k < j := (Finset.mem_range.mp hk)
        -- Show the coefficient vanishes for `k ≠ b`.
        by_cases hik : i * k ≤ a * j + i * b
        · -- In this case the coefficient comes from `φ (r.coeff k)` at degree `a*j + i*b - i*k`,
          -- and coprimeness implies this degree is not a multiple of `j`.
          have hkcoeff :
              (φ (r.coeff k) * x ^ k).coeff (a * j + i * b) =
                (φ (r.coeff k)).coeff (a * j + i * b - i * k) := by
            -- rewrite `x ^ k` as a pure `X`-power and shift coefficients
            have : x ^ k = (Polynomial.X : R[X]) ^ (i * k) := by
              simp [x, pow_mul]
            -- use the general coefficient shift lemma
            simp [this, Polynomial.coeff_mul_X_pow', hik]
          have hnotdvd : ¬ j ∣ (a * j + i * b - i * k) := by
            intro hdvd
            rcases hdvd with ⟨t, ht⟩
            have hdecomp :
                a * j + i * b = i * k + j * t := by
              -- since `i*k ≤ ...`, we may undo the subtraction
              have : i * k + (a * j + i * b - i * k) = a * j + i * b := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  (Nat.sub_add_cancel hik)
              -- replace the difference by `j*t`
              have h1 : a * j + i * b = i * k + (a * j + i * b - i * k) := by
                simpa using this.symm
              simpa [ht] using h1
            have hdecomp' :
                i * b + j * a = i * k + j * t := by
              simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hdecomp
            have := nat_repr_unique_of_coprime (i := i) (j := j) (a := a) (a' := t)
              hcop hb hklt hdecomp'
            exact hkne this.symm
          -- `expand` has coefficients only in degrees divisible by `j`.
          have : (φ (r.coeff k)).coeff (a * j + i * b - i * k) = 0 := by
            -- unfold `φ` into `expand` and use the explicit coefficient formula
            simp [φ, Polynomial.coeff_expand hj, hnotdvd]
          simp [hkcoeff, this]
        · -- If `i*k` is too large, the shifted coefficient is zero.
          have : (φ (r.coeff k) * x ^ k).coeff (a * j + i * b) = 0 := by
            have : x ^ k = (Polynomial.X : R[X]) ^ (i * k) := by
              simp [x, pow_mul]
            simp [this, Polynomial.coeff_mul_X_pow', hik]
          simp [this]
      · intro hbnot
        exfalso
        exact hbnot hbmem
    -- Now compute the surviving coefficient at `k = b`.
    have hbcoeff :
        (φ (r.coeff b) * x ^ b).coeff (a * j + i * b) = (r.coeff b).coeff a := by
      have hxpow : x ^ b = (Polynomial.X : R[X]) ^ (i * b) := by
        simp [x, pow_mul]
      -- first shift off the `X^(i*b)` factor, then use the `expand` coefficient formula
      have hshift :
          (φ (r.coeff b) * x ^ b).coeff (a * j + i * b) = (φ (r.coeff b)).coeff (a * j) := by
        simpa [hxpow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          (Polynomial.coeff_mul_X_pow (p := φ (r.coeff b)) (n := i * b) (d := a * j))
      have hexpand :
          (φ (r.coeff b)).coeff (a * j) = (r.coeff b).coeff a := by
        -- `φ` is `expand` by a factor of `j`
        simpa [φ] using (Polynomial.coeff_expand_mul (R := R) hj (r.coeff b) a)
      simp [hshift, hexpand]
    -- Assemble.
    calc
      (Polynomial.eval₂ (f := φ) (x := x) r).coeff (a * j + i * b) =
          ∑ k ∈ Finset.range j, (φ (r.coeff k) * x ^ k).coeff (a * j + i * b) := hcoeff_sum
      _ = (φ (r.coeff b) * x ^ b).coeff (a * j + i * b) := by simp [hsingle]
      _ = (r.coeff b).coeff a := hbcoeff
  -- Conclude `r = 0` by coefficient-extensionality in `Y`.
  ext b : 1
  by_cases hb : b < j
  · -- coefficients for `b < j` vanish by the computation above (and `hEval`)
    -- show `r.coeff b = 0` by extensionality in `X`
    ext a
    have := congrArg (fun p : R[X] => p.coeff (a * j + i * b)) hEval
    -- rewrite the coefficient using `hcoeff_reduced`
    simpa [hcoeff_reduced a b hb] using this
  · -- coefficients for `b ≥ j` vanish since `natDegree r < j`
    have hb' : r.natDegree < b := lt_of_lt_of_le hr (le_of_not_gt hb)
    simpa using (Polynomial.coeff_eq_zero_of_natDegree_lt hb')

/- Let \( R \) be an integral domain and let \( i, j \) be relatively prime integers. Prove that the
ideal \( (x^i - y^j) \) is a prime ideal in \( R[x, y] \). -/
theorem span_pow_sub_pow_isPrime_of_coprime {R : Type} [CommRing R] [IsDomain R] {i j : ℕ}
    (hi : i > 0) (hj : j > 0) (h : Nat.Coprime i j) :
    (span {(MvPolynomial.X (0 : Fin 2) ^ i - MvPolynomial.X (1 : Fin 2) ^ j :
      MvPolynomial (Fin 2) R)}).IsPrime := by
  classical
  have hi0 : i ≠ 0 := Nat.ne_of_gt hi
  -- Move to `R[X][Y]` via the standard algebra equivalence.
  let e : Polynomial (R[X]) ≃ₐ[R] MvPolynomial (Fin 2) R := Polynomial.Bivariate.equivMvPolynomial R
  -- In `R[X][Y]`, the generator is `(C X)^i - X^j`.
  let g : Polynomial (R[X]) :=
    (Polynomial.C (Polynomial.X : R[X]) : Polynomial (R[X])) ^ i - (Polynomial.X : Polynomial (R[X])) ^ j
  let J : Ideal (Polynomial (R[X])) := Ideal.span ({g} : Set (Polynomial (R[X])))
  -- Define the parametrization `X ↦ t^j`, `Y ↦ t^i` as a ring hom `R[X][Y] → R[t]`.
  let ψ : Polynomial (R[X]) →+* R[X] :=
    Polynomial.eval₂RingHom
      ((Polynomial.expand R j : R[X] →ₐ[R] R[X]) : R[X] →+* R[X])
      ((Polynomial.X : R[X]) ^ i)
  have hψg : ψ g = 0 := by
    -- `ψ` sends `C X` to `X^j` and `X` to `X^i`.
    simp [ψ, g, map_sub, map_pow, Polynomial.expand_X]
    rw [← pow_mul, ← pow_mul]
    simp [Nat.mul_comm]
  have hJker : J = RingHom.ker ψ := by
    -- `J ≤ ker ψ` is immediate from `ψ g = 0`.
    have hle : J ≤ RingHom.ker ψ := by
      refine Ideal.span_le.2 ?_
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      simpa [RingHom.mem_ker] using hψg
    -- For the reverse inclusion, use division by the monic polynomial `X^j - (C X)^i`.
    have hge : RingHom.ker ψ ≤ J := by
      intro p hp
      -- Let `m := X^j - (C X)^i`, a monic associate of `g`.
      let m : Polynomial (R[X]) :=
        (Polynomial.X : Polynomial (R[X])) ^ j - (Polynomial.C (Polynomial.X : R[X]) : Polynomial (R[X])) ^ i
      have hm_monic : m.Monic := by
        -- rewrite to `X^j - C ((X:R[X])^i)`
        have : m = (Polynomial.X : Polynomial (R[X])) ^ j - Polynomial.C ((Polynomial.X : R[X]) ^ i) := by
          simp [m, map_pow]
        -- apply the standard monicity lemma
        simpa [this] using (Polynomial.monic_X_pow_sub_C (R := R[X]) ((Polynomial.X : R[X]) ^ i) (hj.ne'))
      have hm_natDegree : m.natDegree = j := by
        have : m = (Polynomial.X : Polynomial (R[X])) ^ j - Polynomial.C ((Polynomial.X : R[X]) ^ i) := by
          simp [m, map_pow]
        simpa [this] using (Polynomial.natDegree_X_pow_sub_C (R := R[X]) (n := j) (r := (Polynomial.X : R[X]) ^ i))
      -- Show the remainder `p %ₘ m` is zero by injectivity on reduced representatives.
      have hrem_eval :
          Polynomial.eval₂
              (f := ((Polynomial.expand R j : R[X] →ₐ[R] R[X]) : R[X] →+* R[X]))
              (x := (Polynomial.X : R[X]) ^ i) (p %ₘ m) = 0 := by
        -- Map the division identity through `ψ`.
        have hdiv : (p %ₘ m) + m * (p /ₘ m) = p := by
          simpa [Polynomial.modByMonic, Polynomial.divByMonic] using (Polynomial.modByMonic_add_div (p := p) hm_monic)
        have := congrArg ψ hdiv
        -- `ψ m = 0`, so `ψ (p %ₘ m) = ψ p = 0`.
        have hψm : ψ m = 0 := by
          -- `m = -(g)` under our `g`, so this is the same calculation as `hψg`.
          simp [ψ, m, map_sub, map_pow, Polynomial.expand_X]
          rw [← pow_mul, ← pow_mul]
          simp [Nat.mul_comm]
        -- rearrange
        simpa [map_add, map_mul, hψm, RingHom.mem_ker.mp hp] using this
      have hrem_lt : (p %ₘ m).natDegree < j := by
        have hm_ne_one : m ≠ 1 := by
          intro hm1
          have hnd : m.natDegree = 0 := by
            simp [hm1]
          have : j = 0 := by
            simpa [hm_natDegree] using hnd
          exact (Nat.ne_of_gt hj) this
        have := Polynomial.natDegree_modByMonic_lt (p := p) (q := m) hm_monic hm_ne_one
        -- rewrite `m.natDegree = j`
        simpa [hm_natDegree] using this
      have hrem0 : p %ₘ m = 0 := by
        -- apply the injectivity lemma
        exact bivariate_eval₂_eq_zero_of_natDegree_lt (R := R) (i := i) (j := j) (hj := hj) (hcop := h)
          (r := p %ₘ m) hrem_lt hrem_eval
      have hmdvd : m ∣ p := (Polynomial.modByMonic_eq_zero_iff_dvd (p := p) (q := m) hm_monic).1 hrem0
      have hp_mem_m : p ∈ Ideal.span ({m} : Set (Polynomial (R[X]))) := by
        -- `Ideal.span {m}` corresponds to divisibility by `m`.
        simpa [Ideal.mem_span_singleton] using hmdvd
      -- Since `m = -g`, the principal ideals coincide.
      have hspan_eq : Ideal.span ({m} : Set (Polynomial (R[X]))) = J := by
        apply le_antisymm
        · -- `span {m} ≤ span {g}` since `g ∣ m`
          have : g ∣ m := by
            refine ⟨-1, ?_⟩
            ring
          simpa [J] using (Ideal.span_singleton_le_span_singleton (x := m) (y := g)).2 this
        · -- `span {g} ≤ span {m}` since `m ∣ g`
          have : m ∣ g := by
            refine ⟨-1, ?_⟩
            ring
          simpa [J] using (Ideal.span_singleton_le_span_singleton (x := g) (y := m)).2 this
      exact hspan_eq ▸ hp_mem_m
    exact le_antisymm hle hge
  -- `J` is prime because it is the kernel of a map into the domain `R[t]`.
  have hJprime : J.IsPrime := by
    -- `⊥` is prime in a domain, and primes pull back along ring homs.
    letI : (⊥ : Ideal R[X]).IsPrime := Ideal.bot_prime
    have hkerPrime : (RingHom.ker ψ).IsPrime := by
      simpa [RingHom.ker] using (Ideal.comap_isPrime (f := ψ) (K := (⊥ : Ideal R[X])))
    simpa [hJker] using hkerPrime
  -- Transfer primeness back to `MvPolynomial (Fin 2) R` via `e`.
  let f : Polynomial (R[X]) →+* MvPolynomial (Fin 2) R := e.toRingEquiv.toRingHom
  have hf : Function.Surjective f := by
    intro y
    refine ⟨e.symm y, ?_⟩
    simp [f]
  -- The target ideal is the image of `J` under the equivalence `e`.
  have hmap : Ideal.map f J =
      Ideal.span
        ({(MvPolynomial.X (0 : Fin 2) ^ i - MvPolynomial.X (1 : Fin 2) ^ j :
          MvPolynomial (Fin 2) R)} : Set (MvPolynomial (Fin 2) R)) := by
    -- `e` sends `(C X)^i - X^j` to `X 0 ^ i - X 1 ^ j`.
    simp [J, f, g, e, Ideal.map_span]
  -- Map of a prime ideal under a surjective map is prime (kernel condition is trivial here).
  letI : J.IsPrime := hJprime
  have hk : RingHom.ker f ≤ J := by
    have hf_inj : Function.Injective f := by
      simpa [f] using (e.toRingEquiv.injective)
    have hker : RingHom.ker f = ⊥ := (RingHom.injective_iff_ker_eq_bot f).1 hf_inj
    rw [hker]
    exact bot_le
  have hmapPrime : (Ideal.map f J).IsPrime :=
    Ideal.map_isPrime_of_surjective (f := f) hf (I := J) hk
  simpa [hmap] using hmapPrime

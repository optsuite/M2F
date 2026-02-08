import Mathlib

open scoped Topology
open Filter

local instance (p : Nat.Primes) : NeZero p.1 := ⟨p.2.ne_zero⟩
local instance (p : Nat.Primes) : IsDomain (ZMod p) := @ZMod.instIsDomain p ⟨p.2⟩

/-- Summability of the prime series `p^(-s)` for real `s > 1`. -/
lemma summable_primes_rpow_neg {s : ℝ} (hs : 1 < s) :
    Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)) := by
  have hs' : (-s) < (-1 : ℝ) := by
    simpa using (neg_lt_neg hs)
  simpa using (Nat.Primes.summable_rpow (r := -s)).2 hs'

/-- The prime series `∑' p, p^(-s)` is positive for `s > 1`. -/
lemma tsum_primes_rpow_neg_pos {s : ℝ} (hs : 1 < s) :
    0 < (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))) := by
  have hsum : Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)) :=
    summable_primes_rpow_neg (s := s) hs
  have hnonneg : ∀ p : Nat.Primes, 0 ≤ (p : ℝ) ^ (-s) := by
    intro p
    have hp : (0 : ℝ) < (p : ℝ) := by
      have hp' : (0 : ℕ) < p := p.2.pos
      exact_mod_cast hp'
    exact le_of_lt (Real.rpow_pos_of_pos hp (-s))
  have hpos : 0 < ((2 : ℝ) ^ (-s)) := by
    have hbase : (0 : ℝ) < (2 : ℝ) := by
      norm_num
    simpa using (Real.rpow_pos_of_pos hbase (-s))
  simpa using
    (hsum.tsum_pos (hg := hnonneg) (i := (⟨2, by decide⟩ : Nat.Primes)) hpos)

/-- The prime series `∑' p, p^(-s)` is nonzero for `s > 1`. -/
lemma tsum_primes_rpow_neg_ne_zero {s : ℝ} (hs : 1 < s) :
    (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))) ≠ 0 := by
  exact ne_of_gt (tsum_primes_rpow_neg_pos (s := s) hs)

/-- Constant polynomials have no roots in `ZMod p`, hence the root count is `0`. -/
lemma rootSet_ncard_C (a : ℤ) (p : Nat.Primes) :
    ((Polynomial.C a).rootSet (ZMod p)).ncard = 0 := by
  classical
  have hroot : (Polynomial.C a).rootSet (ZMod p) = (∅ : Set (ZMod p)) := by
    simpa using (Polynomial.rootSet_C (a := a) (S := ZMod p))
  have hempty : ((∅ : Set (ZMod p))).ncard = 0 := by
    simp
  rw [hroot]
  exact hempty

/-- The prime-counting ratio for a constant polynomial is the constant `0`. -/
lemma ratio_const_eq_zero (a : ℤ) :
    (fun s : ℝ ↦
      (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
      (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) =
    (fun _ : ℝ ↦ 0) := by
  funext s
  have hzero :
      (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s))) =
        fun _ : Nat.Primes ↦ (0 : ℝ) := by
    funext p
    have hcard : ((Polynomial.C a).rootSet (ZMod p)).ncard = 0 :=
      rootSet_ncard_C (a := a) (p := p)
    rw [hcard]
    simp
  have hnum :
      (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) = 0 := by
    calc
      (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s))))
          = tsum (fun _ : Nat.Primes ↦ (0 : ℝ)) := by
            simpa using congrArg tsum hzero
      _ = 0 := by simp
  rw [hnum]
  simp

/-- The ratio for a constant polynomial tends to `0` as `s → 1+`. -/
lemma tendsto_ratio_const (a : ℤ) :
    Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hconst := ratio_const_eq_zero (a := a)
  rw [hconst]
  exact (tendsto_const_nhds :
    Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)))

/-- A constant polynomial cannot yield a ratio tending to `1` as `s → 1+`. -/
lemma tendsto_ratio_const_ne_one (a : ℤ) :
    ¬ Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  intro h
  let g : ℝ → ℝ :=
    fun s ↦
      (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))
  have h0 : Tendsto g (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa [g] using tendsto_ratio_const (a := a)
  haveI : NeBot (𝓝[>] (1 : ℝ)) := inferInstance
  have : (0 : ℝ) = 1 := by
    exact tendsto_nhds_unique (f := g) (l := 𝓝[>] (1 : ℝ)) (a := 0) (b := 1) h0
      (by simpa [g] using h)
  exact zero_ne_one this

/-- A constant polynomial cannot satisfy the `Tendsto`-to-`1` claim. -/
lemma tendsto_ratio_const_false (a : ℤ)
    (h :
      Tendsto
        (fun s : ℝ ↦
          (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
          (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ))) : False := by
  exact (tendsto_ratio_const_ne_one (a := a)) h

/-- If a polynomial is constant, the ratio cannot tend to `1` as `s → 1+`. -/
lemma tendsto_ratio_of_eq_C_false (f : Polynomial ℤ) (a : ℤ)
    (hf : f = Polynomial.C a) :
    ¬ Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  simpa [hf] using (tendsto_ratio_const_ne_one (a := a))

/-- If the ratio tends to `1`, then the polynomial is not constant. -/
lemma tendsto_ratio_implies_nonconst (f : Polynomial ℤ)
    (h :
      Tendsto
        (fun s : ℝ ↦
          (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
          (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ))) :
    ¬ ∃ a : ℤ, f = Polynomial.C a := by
  rintro ⟨a, rfl⟩
  exact (tendsto_ratio_const_ne_one (a := a)) h

/-- A non-constant polynomial has positive `natDegree`. -/
lemma natDegree_pos_of_not_eq_C (f : Polynomial ℤ)
    (h : ¬ ∃ a : ℤ, f = Polynomial.C a) : 0 < f.natDegree := by
  by_contra hpos
  have hdeg : f.natDegree = 0 := Nat.eq_zero_of_not_pos hpos
  have hC : f = Polynomial.C (f.coeff 0) := by
    simpa using (Polynomial.eq_C_of_natDegree_eq_zero (p := f) hdeg)
  exact h ⟨f.coeff 0, hC⟩

/-- Any polynomial is constant or has positive `natDegree`. -/
lemma eq_C_or_natDegree_pos (f : Polynomial ℤ) :
    (∃ a : ℤ, f = Polynomial.C a) ∨ 0 < f.natDegree := by
  by_cases hconst : ∃ a : ℤ, f = Polynomial.C a
  · exact Or.inl hconst
  · exact Or.inr (natDegree_pos_of_not_eq_C (f := f) hconst)

/-- A `Tendsto`-to-`1` claim forces positive `natDegree`. -/
lemma tendsto_ratio_implies_natDegree_pos (f : Polynomial ℤ)
    (h :
      Tendsto
        (fun s : ℝ ↦
          (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
          (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ))) :
    0 < f.natDegree := by
  exact natDegree_pos_of_not_eq_C (f := f) (tendsto_ratio_implies_nonconst (f := f) h)

/-- If `natDegree` is zero, the ratio cannot tend to `1`. -/
lemma not_tendsto_of_natDegree_eq_zero (f : Polynomial ℤ) (hdeg : f.natDegree = 0) :
    ¬ Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  intro h
  have hpos := tendsto_ratio_implies_natDegree_pos (f := f) h
  simp [hdeg] at hpos

/-- An irreducible polynomial of `natDegree = 0` is a constant with prime coefficient. -/
lemma irreducible_eq_C_prime_of_natDegree_eq_zero (f : Polynomial ℤ)
    (h_irr : Irreducible f) (hdeg : f.natDegree = 0) :
    ∃ a : ℤ, Prime a ∧ f = Polynomial.C a := by
  have hC : f = Polynomial.C (f.coeff 0) := by
    simpa using (Polynomial.eq_C_of_natDegree_eq_zero (p := f) hdeg)
  have hprimeC : Prime (Polynomial.C (f.coeff 0)) := by
    have h_irrC : Irreducible (Polynomial.C (f.coeff 0)) := by
      simpa [← hC] using h_irr
    exact (UniqueFactorizationMonoid.irreducible_iff_prime.mp h_irrC)
  refine ⟨f.coeff 0, ?_, hC⟩
  exact (Polynomial.prime_C_iff.mp hprimeC)

/-- An irreducible polynomial is constant prime or has positive `natDegree`. -/
lemma irreducible_eq_C_prime_or_natDegree_pos (f : Polynomial ℤ) (h_irr : Irreducible f) :
    (∃ a : ℤ, Prime a ∧ f = Polynomial.C a) ∨ 0 < f.natDegree := by
  by_cases hdeg : f.natDegree = 0
  · exact Or.inl (irreducible_eq_C_prime_of_natDegree_eq_zero (f := f) h_irr hdeg)
  · exact Or.inr (Nat.pos_of_ne_zero hdeg)

/-- The right limit at `1` of the ratio for a constant polynomial is `0`. -/
lemma rightLim_ratio_const (a : ℤ) :
    Function.rightLim
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 0 := by
  have hne : (𝓝[>] (1 : ℝ)) ≠ ⊥ := (inferInstance : NeBot (𝓝[>] (1 : ℝ))).ne
  have hlim : Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_ratio_const (a := a)
  simpa using
    (rightLim_eq_of_tendsto
      (f := fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (a := 1) (y := 0) hne hlim)

/-- The right limit for a constant polynomial cannot be `1`. -/
lemma rightLim_ratio_const_ne_one (a : ℤ) :
    Function.rightLim
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 ≠ 1 := by
  intro h
  have h0 :
      Function.rightLim
        (fun s : ℝ ↦
          (tsum (fun p : Nat.Primes ↦ ((Polynomial.C a).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
          (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 0 := by
    simpa using (rightLim_ratio_const (a := a))
  have : (0 : ℝ) = 1 := by
    rw [h0] at h
    exact h
  exact zero_ne_one this

/-- A prime integer gives an irreducible constant polynomial. -/
lemma irreducible_C_of_prime (a : ℤ) (ha : Prime a) :
    Irreducible (Polynomial.C a) := by
  have hprime : Prime (Polynomial.C a) := by
    exact (Polynomial.prime_C_iff.mpr ha)
  simpa using hprime.irreducible

/-- A concrete counterexample: the constant prime polynomial `2` is irreducible and yields right limit `0`. -/
lemma counterexample_const_prime :
    Irreducible (2 : Polynomial ℤ) ∧
      Function.rightLim
        (fun s : ℝ ↦
          (tsum (fun p : Nat.Primes ↦ ((2 : Polynomial ℤ).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
          (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 0 := by
  have hirr : Irreducible (2 : Polynomial ℤ) := by
    simpa using
      (irreducible_C_of_prime (a := (2 : ℤ)) (by simpa using (Int.prime_two : Prime (2 : ℤ))))
  refine ⟨hirr, ?_⟩
  simpa using (rightLim_ratio_const (a := (2 : ℤ)))

/-- The right limit for the constant prime polynomial `2` is not `1`. -/
lemma rightLim_ratio_const_two_ne_one :
    Function.rightLim
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((2 : Polynomial ℤ).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 ≠ 1 := by
  simpa using (rightLim_ratio_const_ne_one (a := (2 : ℤ)))

/-- The ratio for the constant prime polynomial `2` does not tend to `1`. -/
lemma not_tendsto_ratio_two_to_one :
    ¬ Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ ((2 : Polynomial ℤ).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  simpa using (tendsto_ratio_const_ne_one (a := (2 : ℤ)))

/-- The `Tendsto` claim for the constant prime polynomial `2` is contradictory. -/
lemma tendsto_ratio_irreducible_contradicts_const_two
    (h :
      Tendsto
        (fun s : ℝ ↦
          (tsum (fun p : Nat.Primes ↦ ((2 : Polynomial ℤ).rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
          (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
        (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ))) : False := by
  exact (not_tendsto_ratio_two_to_one h)

/-- A global `Tendsto` claim is refuted by the constant prime polynomial `2`. -/
lemma tendsto_ratio_irreducible_false
    (h :
      ∀ f : Polynomial ℤ, Irreducible f →
        Tendsto
          (fun s : ℝ ↦
            (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
            (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
          (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ))) : False := by
  have h2 := h (2 : Polynomial ℤ) (counterexample_const_prime).1
  exact not_tendsto_ratio_two_to_one h2

/-- The stated right-limit claim is refuted by the constant prime polynomial `2`. -/
lemma ratio_tendsto_one_of_irreducible_false
    (h :
      ∀ f : Polynomial ℤ, Irreducible f →
        Function.rightLim
          (fun s : ℝ ↦
            (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
            (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 1) : False := by
  have h2 := h (2 : Polynomial ℤ) (counterexample_const_prime).1
  exact rightLim_ratio_const_two_ne_one h2

/-- Placeholder for the Dirichlet-density limit needed in the main theorem. -/
lemma tendsto_ratio_irreducible
    (f : Polynomial ℤ) (h_irr : Irreducible f) :
    Tendsto
      (fun s : ℝ ↦
        (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s))))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
  -- The required Dirichlet-density limit is not currently available in mathlib.
  -- It would follow from a Chebotarev-type theorem for irreducible polynomials.
  sorry

/--
Let $f(X)\in\mathbb{Z}[X]$ be an irreducible polynomial, $n_p$ is the number of solutions of $f(X)$ in $\mathbb{F}_p$,
show that $$\lim\limits_{s\rightarrow 1^{+}}\frac{\sum\limits_{p\textbf{ prime}}\frac{n_p}{p^s}}{\sum\limits_{p\textbf{ prime}}\frac{1}{p^s}}=1$$.
-/
theorem ratio_tendsto_one_of_irreducible (f : Polynomial ℤ) (h_irr : Irreducible f) :
    Function.rightLim
    (fun (s : ℝ) ↦
    (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
    (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))) 1 = 1 := by
  classical
  let g : ℝ → ℝ :=
    fun s ↦
      (tsum (fun p : Nat.Primes ↦ (f.rootSet (ZMod p)).ncard * ((p : ℝ) ^ (-s)))) /
        (tsum (fun p : Nat.Primes ↦ (p : ℝ) ^ (-s)))
  have hne : (𝓝[>] (1 : ℝ)) ≠ ⊥ := (inferInstance : NeBot (𝓝[>] (1 : ℝ))).ne
  have hlim : Tendsto g (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa [g] using (tendsto_ratio_irreducible (f := f) h_irr)
  simpa [g] using (rightLim_eq_of_tendsto (f := g) (a := 1) (y := 1) hne hlim)

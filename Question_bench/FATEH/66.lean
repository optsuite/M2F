import Mathlib

open Polynomial
/-- The low-degree tail does not affect the leading term once `n > 0`. -/
lemma natDegree_X_pow_two_pow_add_X_add_C_one {n : ℕ} (hn : n ≠ 0) :
    (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X]).natDegree = 2 ^ n := by
  have hpow : 1 < 2 ^ n := Nat.one_lt_pow (n := n) (a := 2) hn (by decide)
  have hdeg_xc : (X + C 1 : (ZMod 2)[X]).natDegree = 1 := by
    simpa using (natDegree_X_add_C (R := ZMod 2) (x := (1 : ZMod 2)))
  have hdeg_pow : (X ^ 2 ^ n : (ZMod 2)[X]).natDegree = 2 ^ n := by
    simp
  have hlt : (X + C 1 : (ZMod 2)[X]).natDegree < (X ^ 2 ^ n : (ZMod 2)[X]).natDegree := by
    rw [hdeg_xc, hdeg_pow]
    exact hpow
  have hdeg :
      (X ^ 2 ^ n + (X + C 1) : (ZMod 2)[X]).natDegree =
        (X ^ 2 ^ n : (ZMod 2)[X]).natDegree :=
    natDegree_add_eq_left_of_natDegree_lt hlt
  simpa [add_assoc, hdeg_pow] using hdeg

/-- The leading term dominates, so the polynomial is monic for `n > 0`. -/
lemma monic_X_pow_two_pow_add_X_add_C_one {n : ℕ} (hn : n ≠ 0) :
    (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X]).Monic := by
  have hpow : 1 < 2 ^ n := Nat.one_lt_pow (n := n) (a := 2) hn (by decide)
  have hdeg : degree (X + C 1 : (ZMod 2)[X]) = 1 := by
    simpa using (degree_X_add_C (R := ZMod 2) (a := (1 : ZMod 2)))
  have hlt : degree (X + C 1 : (ZMod 2)[X]) < (2 ^ n : ℕ) := by
    rw [hdeg]
    exact WithBot.coe_lt_coe.mpr hpow
  have hmonic : (X ^ 2 ^ n + (X + C 1) : (ZMod 2)[X]).Monic :=
    monic_X_pow_add (p := (X + C 1 : (ZMod 2)[X])) hlt
  simpa [add_assoc] using hmonic

/-- Mapped version still has positive degree for `n > 0`. -/
lemma degree_map_X_pow_two_pow_add_X_add_C_one_ne_zero {n : ℕ} (hn : n ≠ 0)
    (K : Type*) [Field K] [Algebra (ZMod 2) K] :
    (Polynomial.map (algebraMap (ZMod 2) K)
        (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X])).degree ≠ 0 := by
  let f : (ZMod 2)[X] := X ^ 2 ^ n + X + C 1
  have hf0 : f ≠ 0 := (monic_X_pow_two_pow_add_X_add_C_one hn).ne_zero
  have hdeg_f_nat : f.natDegree = 2 ^ n := by
    change (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X]).natDegree = 2 ^ n
    exact natDegree_X_pow_two_pow_add_X_add_C_one hn
  have hdeg_f' : f.degree = (2 ^ n : ℕ) := by
    have hdeg_f'' : (f.natDegree : WithBot ℕ) = (2 ^ n : WithBot ℕ) := by
      exact_mod_cast hdeg_f_nat
    exact (Polynomial.degree_eq_natDegree hf0).trans hdeg_f''
  have hdeg_map' : (f.map (algebraMap (ZMod 2) K)).degree = (2 ^ n : ℕ) := by
    calc
      (f.map (algebraMap (ZMod 2) K)).degree = f.degree :=
        Polynomial.degree_map (p := f) (f := algebraMap (ZMod 2) K)
      _ = (2 ^ n : ℕ) := hdeg_f'
  have hne : (2 ^ n : ℕ) ≠ 0 := pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)
  intro hdeg0
  have hdeg_map'' : (2 ^ n : WithBot ℕ) = 0 := hdeg_map'.symm.trans hdeg0
  have hzero : (2 ^ n : ℕ) = 0 := by
    exact_mod_cast hdeg_map''
  exact hne hzero

/-- Powers of two dominate linear growth for `n ≥ 3`. -/
lemma two_mul_lt_pow_two {n : ℕ} (hn : n ≥ 3) : 2 * n < 2 ^ n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction k with
  | zero => decide
  | succ k ih =>
      have hm0 : (3 + k : ℕ) ≠ 0 := by
        simp
      have hpow : 1 < 2 ^ (3 + k) :=
        Nat.one_lt_pow (n := 3 + k) (a := 2) hm0 (by decide)
      have htwo : 2 ≤ 2 ^ (3 + k) := (Nat.succ_le_iff.mpr hpow)
      calc
        2 * (3 + k + 1) = 2 * (3 + k) + 2 := by
          simp [Nat.mul_add, add_comm]
        _ < 2 ^ (3 + k) + 2 := by
          exact Nat.add_lt_add_right ih _
        _ ≤ 2 ^ (3 + k) + 2 ^ (3 + k) := by
          exact Nat.add_le_add_left htwo _
        _ = 2 ^ (3 + k + 1) := by
          calc
            2 ^ (3 + k) + 2 ^ (3 + k) = 2 * 2 ^ (3 + k) := by simp [two_mul]
            _ = 2 ^ (3 + k + 1) := by simp [pow_succ, mul_comm]
/-- Prove that, if $n \geq 3$, then $x^{2^n}+x+1$ is \emph{reducible} in $\mathbb{F}_2$. -/
theorem not_irreducible_X_pow_two_pow_add_X_add_C_one {n : ℕ} (hn : n ≥ 3) :
    ¬ Irreducible (X ^ 2 ^ n + X + C 1 : (ZMod 2)[X]) := by
  classical
  intro hI
  have hn0 : n ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hn)
  set f : (ZMod 2)[X] := X ^ 2 ^ n + X + C 1
  set g : (ZMod 2)[X] := X ^ (2 ^ (2 * n)) - X
  have hmonic : f.Monic := by
    simpa [f] using (monic_X_pow_two_pow_add_X_add_C_one (n := n) hn0)
  have hdeg_f : f.natDegree = 2 ^ n := by
    simpa [f] using (natDegree_X_pow_two_pow_add_X_add_C_one (n := n) hn0)
  -- Roots in the algebraic closure satisfy a Frobenius relation.
  let K := AlgebraicClosure (ZMod 2)
  have hdeg_map_K :
      (f.map (algebraMap (ZMod 2) K)).degree ≠ 0 := by
    simpa [f] using
      (degree_map_X_pow_two_pow_add_X_add_C_one_ne_zero (n := n) hn0 (K := K))
  obtain ⟨α, hαroot⟩ :=
    IsAlgClosed.exists_root (k := K) (p := f.map (algebraMap (ZMod 2) K)) hdeg_map_K
  have hα : aeval α f = 0 := by
    simpa [Polynomial.IsRoot.def, Polynomial.aeval_def] using hαroot
  have hα_eq : α ^ (2 ^ n) = α + 1 := by
    have hα' : α ^ (2 ^ n) + (α + 1) = 0 := by
      simpa [f, add_assoc] using hα
    have hneg : -(α + 1) = α + 1 := by
      exact (neg_eq_iff_add_eq_zero).2 (CharTwo.add_self_eq_zero (α + 1))
    have h1 : α ^ (2 ^ n) = -(α + 1) := eq_neg_of_add_eq_zero_left hα'
    simpa [hneg] using h1
  have hα_frob : α ^ (2 ^ (2 * n)) = α := by
    calc
      α ^ (2 ^ (2 * n)) = (α ^ (2 ^ n)) ^ (2 ^ n) := by
        have hpow : 2 ^ (2 * n) = 2 ^ n * 2 ^ n := by
          simpa [two_mul] using (pow_add 2 n n)
        calc
          α ^ (2 ^ (2 * n)) = α ^ (2 ^ n * 2 ^ n) := by simp [hpow]
          _ = (α ^ (2 ^ n)) ^ (2 ^ n) := by
            simpa using (pow_mul α (2 ^ n) (2 ^ n))
      _ = (α + 1) ^ (2 ^ n) := by simp [hα_eq]
      _ = α ^ (2 ^ n) + 1 := by
        simpa using (add_pow_char_pow (p := 2) (x := α) (y := (1 : K)) (n := n))
      _ = (α + 1) + 1 := by simp [hα_eq]
      _ = α := by
        simpa using (CharTwo.add_cancel_right (a := α) (b := (1 : K)))
  have hα_g : aeval α g = 0 := by
    simp [g, hα_frob]
  have hminpoly : f = minpoly (ZMod 2) α := by
    exact minpoly.eq_of_irreducible_of_monic hI hα hmonic
  have hdiv : f ∣ g := by
    have hdiv' : minpoly (ZMod 2) α ∣ g := minpoly.dvd (ZMod 2) α hα_g
    simpa [hminpoly] using hdiv'
  -- Use the splitting field of `g` to get a finite root.
  let L := GaloisField 2 (2 * n)
  have hg0 : g ≠ 0 := by
    have hne : (2 * n) ≠ 0 := Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hn0
    simpa [g] using
      (FiniteField.X_pow_card_pow_sub_X_ne_zero (K' := ZMod 2) (p := 2) (n := 2 * n) hne
        (by decide : 1 < 2))
  have hsplit_g : (g.map (algebraMap (ZMod 2) L)).Splits := by
    simpa [GaloisField, g] using (SplittingField.splits (g : (ZMod 2)[X]))
  have hdiv_map :
      f.map (algebraMap (ZMod 2) L) ∣ g.map (algebraMap (ZMod 2) L) :=
    Polynomial.map_dvd (algebraMap (ZMod 2) L) hdiv
  have hg0_map : g.map (algebraMap (ZMod 2) L) ≠ 0 :=
    Polynomial.map_ne_zero (f := algebraMap (ZMod 2) L) hg0
  have hsplit_f : (f.map (algebraMap (ZMod 2) L)).Splits :=
    hsplit_g.splits_of_dvd hg0_map hdiv_map
  have hdeg_map_L :
      (f.map (algebraMap (ZMod 2) L)).degree ≠ 0 := by
    simpa [f] using
      (degree_map_X_pow_two_pow_add_X_add_C_one_ne_zero (n := n) hn0 (K := L))
  obtain ⟨β, hβeval⟩ := hsplit_f.exists_eval_eq_zero hdeg_map_L
  have hβ : aeval β f = 0 := by
    simpa [Polynomial.aeval_def] using hβeval
  have hminpolyβ : f = minpoly (ZMod 2) β := by
    exact minpoly.eq_of_irreducible_of_monic hI hβ hmonic
  have hdeg_dvd :
      f.natDegree ∣ Module.finrank (ZMod 2) L := by
    have hβint : IsIntegral (ZMod 2) β :=
      IsIntegral.of_finite (R := ZMod 2) (B := L) β
    have hdeg_dvd' : (minpoly (ZMod 2) β).natDegree ∣ Module.finrank (ZMod 2) L :=
      minpoly.degree_dvd (K := ZMod 2) (x := β) hβint
    simpa [hminpolyβ] using hdeg_dvd'
  have hfinrank : Module.finrank (ZMod 2) L = 2 * n := by
    have hne : (2 * n) ≠ 0 := Nat.mul_ne_zero (by decide : (2 : ℕ) ≠ 0) hn0
    simpa [L] using (GaloisField.finrank (p := 2) (n := 2 * n) hne)
  have hdiv_nat : 2 ^ n ∣ 2 * n := by
    simpa [hdeg_f, hfinrank] using hdeg_dvd
  have hpos : 0 < 2 * n :=
    Nat.mul_pos (by decide : (0 : ℕ) < 2) (lt_of_lt_of_le (by decide : (0 : ℕ) < 3) hn)
  have hlt : 2 * n < 2 ^ n := two_mul_lt_pow_two hn
  exact (Nat.not_dvd_of_pos_of_lt hpos hlt) hdiv_nat

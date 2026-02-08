import Mathlib

open Polynomial

noncomputable section

private abbrev K12 : Type := ((.X ^ 7 - 12 : Polynomial ℚ).SplittingField)

/-!
This file proves that `X^7 - 11` has no root in the splitting field of `X^7 - 12` over `ℚ`.

The key input is a Kummer-style descent to the cyclotomic subfield `ℚ(ζ₇)` inside the splitting
field of `X^7 - 12`, plus a norm argument using `finrank = 6` for `ℚ(ζ₇)/ℚ`.
-/

private lemma rat_not_seventhPower_12 : ¬ ∃ q : ℚ, q ^ (7 : ℕ) = (12 : ℚ) := by
  intro h
  rcases h with ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    intro hq0
    have : (0 : ℚ) = (12 : ℚ) := by simpa [hq0] using hq
    norm_num at this
  have hval := congrArg (fun r : ℚ => padicValRat 3 r) hq
  -- `padicValRat 3 (q^7)` is a multiple of `7`, but `padicValRat 3 12 = 1`.
  have h3_4 : padicValRat 3 (4 : ℚ) = (0 : ℤ) := by
    have hnat : padicValNat 3 4 = 0 :=
      padicValNat.eq_zero_of_not_dvd (p := 3) (n := 4) (by decide : ¬ 3 ∣ 4)
    have : padicValRat 3 (4 : ℚ) = (padicValNat 3 4 : ℤ) := by
      simpa using (padicValRat.of_nat (p := 3) (n := 4))
    calc
      padicValRat 3 (4 : ℚ) = (padicValNat 3 4 : ℤ) := this
      _ = (0 : ℤ) := by simpa [hnat]
  have h3_12 : padicValRat 3 (12 : ℚ) = (1 : ℤ) := by
    have hmul : padicValRat 3 ((3 : ℚ) * 4) = padicValRat 3 (3 : ℚ) + padicValRat 3 (4 : ℚ) := by
      have h3 : (3 : ℚ) ≠ 0 := by norm_num
      have h4 : (4 : ℚ) ≠ 0 := by norm_num
      simpa [mul_assoc] using (padicValRat.mul (p := 3) (q := (3 : ℚ)) (r := (4 : ℚ)) h3 h4)
    have h3_3 : padicValRat 3 (3 : ℚ) = (1 : ℤ) := by
      simpa using (padicValRat.self (p := 3) (by decide : (1 : ℕ) < 3))
    simpa [show ((3 : ℚ) * 4) = (12 : ℚ) by norm_num, h3_3, h3_4] using hmul
  have : (7 : ℤ) ∣ (1 : ℤ) := by
    refine ⟨padicValRat 3 q, ?_⟩
    -- use `padicValRat.pow` on the left hand side
    have hpow : padicValRat 3 (q ^ (7 : ℕ)) = (7 : ℕ) * padicValRat 3 q := by
      simpa using (padicValRat.pow (p := 3) (q := q) hq0 (k := 7))
    -- combine with `padicValRat 3 12 = 1`
    simpa [h3_12, hpow] using hval.symm
  exact (by decide : ¬ (7 : ℤ) ∣ (1 : ℤ)) this

private lemma rat_not_seventhPower_11_div_12_pow (t : ℕ) :
    ¬ ∃ q : ℚ, q ^ (7 : ℕ) = (11 : ℚ) / (12 : ℚ) ^ t := by
  intro h
  rcases h with ⟨q, hq⟩
  have hRHS0 : (11 : ℚ) / (12 : ℚ) ^ t ≠ 0 := by
    refine div_ne_zero (by norm_num) ?_
    exact pow_ne_zero _ (by norm_num)
  have hq0 : q ≠ 0 := by
    intro hq0
    have : (0 : ℚ) = (11 : ℚ) / (12 : ℚ) ^ t := by simpa [hq0] using hq
    exact hRHS0 (this.symm)
  have hval := congrArg (fun r : ℚ => padicValRat 11 r) hq
  -- `padicValRat 11 (q^7)` is a multiple of `7`, but `padicValRat 11 (11 / 12^t) = 1`.
  have hp11 : Fact (Nat.Prime 11) := ⟨by decide⟩
  have h11_12 : padicValRat 11 (12 : ℚ) = (0 : ℤ) := by
    have hnat : padicValNat 11 12 = 0 :=
      padicValNat.eq_zero_of_not_dvd (p := 11) (n := 12) (by decide : ¬ 11 ∣ 12)
    have : padicValRat 11 (12 : ℚ) = (padicValNat 11 12 : ℤ) := by
      simpa using (padicValRat.of_nat (p := 11) (n := 12))
    calc
      padicValRat 11 (12 : ℚ) = (padicValNat 11 12 : ℤ) := this
      _ = (0 : ℤ) := by simpa [hnat]
  have h11_11 : padicValRat 11 (11 : ℚ) = (1 : ℤ) := by
    simpa using (padicValRat.self (p := 11) (by decide : (1 : ℕ) < 11))
  have h11_12pow : padicValRat 11 ((12 : ℚ) ^ t) = (0 : ℤ) := by
    simpa [h11_12] using (padicValRat.pow (p := 11) (q := (12 : ℚ)) (by norm_num) (k := t))
  have h11_rhs : padicValRat 11 ((11 : ℚ) / (12 : ℚ) ^ t) = (1 : ℤ) := by
    have hdiv :
        padicValRat 11 ((11 : ℚ) / (12 : ℚ) ^ t) =
          padicValRat 11 (11 : ℚ) - padicValRat 11 ((12 : ℚ) ^ t) := by
      have h11 : (11 : ℚ) ≠ 0 := by norm_num
      have h12t : (12 : ℚ) ^ t ≠ 0 := pow_ne_zero _ (by norm_num)
      simpa using (padicValRat.div (p := 11) (q := (11 : ℚ)) (r := (12 : ℚ) ^ t) h11 h12t)
    simpa [h11_11, h11_12pow] using hdiv
  have : (7 : ℤ) ∣ (1 : ℤ) := by
    refine ⟨padicValRat 11 q, ?_⟩
    have hpow : padicValRat 11 (q ^ (7 : ℕ)) = (7 : ℕ) * padicValRat 11 q := by
      simpa using (padicValRat.pow (p := 11) (q := q) hq0 (k := 7))
    -- `padicValRat 11 (q^7) = padicValRat 11 (11/12^t) = 1`
    simpa [h11_rhs, hpow] using hval.symm
  exact (by decide : ¬ (7 : ℤ) ∣ (1 : ℤ)) this

private lemma exists_primitiveRoot7_in_splittingField_X7_sub_C12 :
    ∃ ζ : ((.X ^ 7 - 12 : Polynomial ℚ).SplittingField), IsPrimitiveRoot ζ 7 := by
  classical
  let f : Polynomial ℚ := X ^ (7 : ℕ) - C (12 : ℚ)
  let K := f.SplittingField
  have hf0 : f ≠ 0 := by
    -- `X^7 - 12`
    simpa [f, sub_eq_add_neg] using
      (X_pow_sub_C_ne_zero (R := ℚ) (n := 7) (a := (12 : ℚ)) (by decide))
  have hsep : f.Separable := by
    -- `ℚ` has characteristic `0`, so `7 ≠ 0` in `ℚ`.
    simpa [f] using
      (separable_X_pow_sub_C (F := ℚ) (n := 7) (a := (12 : ℚ)) (by norm_num) (by norm_num))
  have hsplit : (f.map (algebraMap ℚ K)).Splits := SplittingField.splits (f := f)
  have hcard : Fintype.card (f.rootSet K) = 7 := by
    simpa [f, natDegree_X_pow_sub_C] using
      (card_rootSet_eq_natDegree (K := K) (p := f) hsep hsplit)
  have hone : 1 < Fintype.card (f.rootSet K) := by simpa [hcard]
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := f.rootSet K) hone
  have haeval : aeval a.1 f = 0 :=
    (mem_rootSet_of_ne (p := f) (S := K) hf0).1 a.property
  have hbeval : aeval b.1 f = 0 :=
    (mem_rootSet_of_ne (p := f) (S := K) hf0).1 b.property
  have ha7 : a.1 ^ (7 : ℕ) = (12 : K) := by
    have : aeval a.1 (X ^ (7 : ℕ) - C (12 : ℚ)) = 0 := by simpa [f] using haeval
    exact sub_eq_zero.mp (by simpa [aeval_def] using this)
  have hb7 : b.1 ^ (7 : ℕ) = (12 : K) := by
    have : aeval b.1 (X ^ (7 : ℕ) - C (12 : ℚ)) = 0 := by simpa [f] using hbeval
    exact sub_eq_zero.mp (by simpa [aeval_def] using this)
  have ha0 : a.1 ≠ 0 := by
    intro ha0
    have : (0 : K) = (12 : K) := by simpa [ha0] using ha7
    norm_num at this
  let ζ : K := b.1 / a.1
  have hζpow : ζ ^ (7 : ℕ) = (1 : K) := by
    have h12 : (12 : K) ≠ 0 := by norm_num
    calc
      ζ ^ (7 : ℕ) = (b.1 ^ (7 : ℕ)) / (a.1 ^ (7 : ℕ)) := by simp [ζ, div_pow]
      _ = (12 : K) / (12 : K) := by simp [hb7, ha7]
      _ = (1 : K) := by simp [h12]
  have hζne : ζ ≠ (1 : K) := by
    intro hζ1
    have hb_eq : b.1 = a.1 := by
      -- `b / a = 1` implies `b = a` since `a ≠ 0`.
      exact (div_eq_one_iff_eq ha0).1 hζ1
    exact hab (Subtype.ext hb_eq.symm)
  have horder : orderOf ζ = 7 := by
    have hprime : Nat.Prime 7 := by decide
    have hdvd : orderOf ζ ∣ 7 := orderOf_dvd_of_pow_eq_one hζpow
    have hne1 : orderOf ζ ≠ 1 := by
      intro h1
      apply hζne
      simpa [orderOf_eq_one_iff] using h1
    rcases (Nat.dvd_prime hprime).1 hdvd with (h1 | h7)
    · exact (hne1 h1).elim
    · exact h7
  exact ⟨ζ, (IsPrimitiveRoot.iff_orderOf).2 horder⟩

/--
Show that \( x^7 - 11 \) has no root in the splitting field of \(x^7 - 12\) over \(\mathbb{Q}\).
-/
theorem rootSet_isEmpty_in_splittingField :
    (.X ^ 7 - 11 : Polynomial ℚ).rootSet ((.X ^ 7 - 12 : Polynomial ℚ).SplittingField) = ⊥ := by
  classical
  let f12 : Polynomial ℚ := (.X ^ 7 - 12 : Polynomial ℚ)
  change (.X ^ 7 - 11 : Polynomial ℚ).rootSet K12 = ⊥
  -- Choose a primitive 7th root of unity inside `K` by taking a ratio of two roots of `X^7 - 12`.
  obtain ⟨ζ0, hζ0⟩ : ∃ ζ : K12, IsPrimitiveRoot ζ 7 := by
    simpa [K12] using exists_primitiveRoot7_in_splittingField_X7_sub_C12
  have hζ0' : IsPrimitiveRoot (ζ0 : K12) 7 := hζ0
  let F : IntermediateField ℚ K12 := IntermediateField.adjoin ℚ ({ζ0} : Set K12)
  let ζF : F := by
    refine ⟨ζ0, ?_⟩
    change ζ0 ∈ IntermediateField.adjoin ℚ ({ζ0} : Set K12)
    exact (IntermediateField.subset_adjoin ℚ ({ζ0} : Set K12)) (by simp)

  -- `F = ℚ(ζ₇)` is a cyclotomic extension, so `finrank ℚ F = φ(7) = 6`.
  haveI : Algebra.IsIntegral ℚ K12 := by
    -- `K/ℚ` is algebraic since it is a splitting field over `ℚ`.
    infer_instance
  haveI : IsCyclotomicExtension {7} ℚ (↥F) := by
    -- unfold `F`
    simpa [F] using
      (IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := ℚ) (L := K12)
        (ζ := (ζ0 : K12)) hζ0')
  have hfinrankF : Module.finrank ℚ (↥F) = 6 := by
    have hφ :
        Module.finrank ℚ (↥F) = (Nat.totient 7) := by
      simpa using
        (IsCyclotomicExtension.finrank (K := ℚ) (n := 7) (L := (↥F))
          (cyclotomic.irreducible_rat (n := 7) (hpos := by decide)))
    have hprime : Nat.Prime 7 := by decide
    simpa [Nat.totient_prime hprime] using hφ

  -- Norm obstruction: if `y ∈ F` and `y^7` is rational, then that rational is a 7th power in `ℚ`.
  have rat_isSeventhPower_of_pow_eq_algebraMap :
      ∀ {y : (↥F)} {r : ℚ},
        y ^ (7 : ℕ) = algebraMap ℚ (↥F) r → r ∈ Set.range (fun q : ℚ => q ^ (7 : ℕ)) := by
    intro y r hy
    have hnorm := congrArg (Algebra.norm ℚ) hy
    have hnorm' : (Algebra.norm ℚ y) ^ (7 : ℕ) = r ^ (6 : ℕ) := by
      -- Use `norm(y^7) = norm(y)^7` and `norm(algebraMap r) = r^6`.
      have hnorm1 :
          (Algebra.norm ℚ y) ^ (7 : ℕ) = Algebra.norm ℚ (algebraMap ℚ (↥F) r) := by
        simpa [map_pow] using hnorm
      have hnorm2 : Algebra.norm ℚ (algebraMap ℚ (↥F) r) = r ^ (6 : ℕ) := by
        simpa [hfinrankF] using (Algebra.norm_algebraMap (K := ℚ) (L := (↥F)) r)
      exact hnorm1.trans hnorm2
    have hr6 : r ^ (6 : ℕ) ∈ Set.range (fun q : ℚ => q ^ (7 : ℕ)) := by
      refine ⟨Algebra.norm ℚ y, hnorm'⟩
    have hcop : (6 : ℕ).Coprime 7 := by decide
    exact (pow_mem_range_pow_of_coprime (α := ℚ) (m := 6) (n := 7) hcop r).1 hr6

  -- Over `F`, `12` is not a 7th power, hence `X^7 - 12` is irreducible.
  have h12_not7 : ∀ b : (↥F), b ^ (7 : ℕ) ≠ (12 : (↥F)) := by
    intro b hb
    have : (12 : ℚ) ∈ Set.range (fun q : ℚ => q ^ (7 : ℕ)) := by
      have hb' : b ^ (7 : ℕ) = algebraMap ℚ (↥F) (12 : ℚ) := by simpa using hb
      simpa using rat_isSeventhPower_of_pow_eq_algebraMap (y := b) (r := (12 : ℚ)) hb'
    rcases this with ⟨q, hq⟩
    exact rat_not_seventhPower_12 ⟨q, hq⟩
  have hirr : Irreducible (X ^ (7 : ℕ) - C (12 : (↥F))) := by
    have hprime : Nat.Prime 7 := by decide
    exact X_pow_sub_C_irreducible_of_prime (K := (↥F)) hprime h12_not7

  -- View `K` as a splitting field over `F` via scalar tower.
  haveI : Polynomial.IsSplittingField ℚ K12 f12 := by
    dsimp [K12, f12]
    infer_instance
  haveI : IsScalarTower ℚ (↥F) K12 := IntermediateField.isScalarTower_mid' (S := F)
  -- Use `IsSplittingField.map` along the scalar tower `ℚ → F → K`.
  haveI : Polynomial.IsSplittingField (↥F) K12 (f12.map (algebraMap ℚ (↥F))) :=
    Polynomial.IsSplittingField.map (L := K12) (K := (↥F)) (F := ℚ) f12
  haveI : Polynomial.IsSplittingField (↥F) K12 (X ^ (7 : ℕ) - C (12 : (↥F))) := by
    simpa [f12] using
      (inferInstance : Polynomial.IsSplittingField (↥F) K12 (f12.map (algebraMap ℚ (↥F))))

  -- A chosen 7th root of `12` in `K`.
  let β : K12 :=
    rootOfSplitsXPowSubC (K := (↥F)) (n := 7) (hn := by decide) (12 : (↥F)) K12
  have hβ : β ^ (7 : ℕ) = algebraMap (↥F) K12 (12 : (↥F)) := by
    have hβ' : β ^ (7 : ℕ) = algebraMap (↥F) K12 (12 : (↥F)) := by
      simpa [β] using (rootOfSplitsXPowSubC_pow (K := (↥F)) (n := 7) (a := (12 : (↥F))) (L := K12))
    simpa using hβ'

  -- Compute the Galois group action on `β` using `autEquivZmod`.
  have hζK : IsPrimitiveRoot (algebraMap (↥F) K12 ζF) 7 := by
    -- `algebraMap (↥F) K ζF = ζ0` since the `algebraMap` from an intermediate field is inclusion.
    have hmap : algebraMap (↥F) K12 ζF = (ζ0 : K12) := by
      -- Avoid `simp` rewriting the goal to `True`.
      have hmap' : algebraMap (↥F) K12 ζF = (ζF.1 : K12) :=
        IntermediateField.algebraMap_apply (S := F) (x := ζF)
      -- Unfold `ζF` to turn `ζF.1` into `ζ0`.
      simpa [ζF] using hmap'
    simpa [hmap] using hζ0'
  have hζF : IsPrimitiveRoot ζF 7 :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (↥F) K12) hζK (algebraMap (↥F) K12).injective

  -- Now show that there is no `x : K` with `x^7 = 11`.
  have no_root : ∀ x : K12, x ^ (7 : ℕ) ≠ (11 : K12) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hx0
      have : (0 : K12) = (11 : K12) := by simpa [hx0] using hx
      norm_num at this
    have hβ0 : β ≠ 0 := by
      intro hβ0
      have h12F0 : (12 : (↥F)) ≠ 0 := by norm_num
      have h12K0 : algebraMap (↥F) K12 (12 : (↥F)) ≠ 0 :=
        (map_ne_zero_iff (f := algebraMap (↥F) K12) (algebraMap (↥F) K12).injective).2 h12F0
      have : (0 : K12) = algebraMap (↥F) K12 (12 : (↥F)) := by simpa [hβ0] using hβ
      exact h12K0 this.symm
    -- pick the distinguished generator `σ` of the cyclic Galois group `Gal(K/F) ≃ ZMod 7`
    let e : Gal(K12/F) ≃* Multiplicative (ZMod 7) := autEquivZmod (H := hirr) (L := K12) hζF
    let σ : Gal(K12/F) := e.symm (Multiplicative.ofAdd (1 : ZMod 7))
    have hσβ : σ β = algebraMap (↥F) K12 ζF * β := by
      -- `σ(β) = ζ • β`, then rewrite scalar multiplication using `Algebra.smul_def`.
      have hα : β ^ (7 : ℕ) = algebraMap (↥F) K12 (12 : (↥F)) := hβ
      simpa [σ, e, β, Algebra.smul_def] using
        (autEquivZmod_symm_apply_natCast (H := hirr) (L := K12) (α := β) hα hζF 1)
    -- `σ(x)/x` is a 7th root of unity; express it as a power of `ζ`.
    let ξ : K12 := σ x / x
    have hξpow : ξ ^ (7 : ℕ) = (1 : K12) := by
      have hσ11 : σ (11 : K12) = (11 : K12) := by
        simpa using (map_natCast (σ : K12 →+* K12) 11)
      have hσx7 : (σ x) ^ (7 : ℕ) = (11 : K12) := by
        have := congrArg (fun z : K12 => σ z) hx
        have h' : (σ x) ^ (7 : ℕ) = σ (11 : K12) := by
          simpa [map_pow] using this
        simpa [hσ11] using h'
      calc
        ξ ^ (7 : ℕ) = (σ x) ^ (7 : ℕ) / x ^ (7 : ℕ) := by simp [ξ, div_pow]
        _ = (11 : K12) / (11 : K12) := by simp [hσx7, hx]
        _ = (1 : K12) := by
          have : (11 : K12) ≠ 0 := by norm_num
          simp [this]
    obtain ⟨t, ht7, ht⟩ := hζK.eq_pow_of_pow_eq_one hξpow
    -- set `y := x / β^t`; it is fixed by `σ`
    let y : K12 := x / (β ^ t)
    have hσx : σ x = (algebraMap (↥F) K12 ζF) ^ t * x := by
      -- from `ζ^t = σ x / x`, multiply by `x`
      have hζeq : (algebraMap (↥F) K12 ζF) ^ t = σ x / x := by simpa [ξ] using ht
      have hxmul : (σ x / x) * x = σ x := by
        simp [div_eq_mul_inv, hx0, mul_assoc]
      have : (algebraMap (↥F) K12 ζF) ^ t * x = σ x := by
        simpa [hζeq.symm] using hxmul
      simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
    have hσy : σ y = y := by
      have hσβt : σ (β ^ t) = (algebraMap (↥F) K12 ζF) ^ t * (β ^ t) := by
        calc
          σ (β ^ t) = (σ β) ^ t := by simpa using (map_pow σ β t)
          _ = (algebraMap (↥F) K12 ζF * β) ^ t := by simpa [hσβ]
          _ = (algebraMap (↥F) K12 ζF) ^ t * (β ^ t) := by
            simpa [mul_pow] using (mul_pow (algebraMap (↥F) K12 ζF) β t)
      -- `σ(x/β^t) = (ζ^t•x) / (ζ^t•β^t) = x/β^t`
      have hζt0 : (algebraMap (↥F) K12 ζF) ^ t ≠ 0 := by
        have : algebraMap (↥F) K12 ζF ≠ 0 := by
          have hζF0 : (ζF : (↥F)) ≠ 0 := hζF.ne_zero (by decide : (7 : ℕ) ≠ 0)
          exact
            (map_ne_zero_iff (f := algebraMap (↥F) K12) (algebraMap (↥F) K12).injective).2 hζF0
        exact pow_ne_zero _ this
      calc
        σ y = σ x / σ (β ^ t) := by
          -- `σ` respects division
          simpa [y] using (map_div₀ σ x (β ^ t))
        _ =
            ((algebraMap (↥F) K12 ζF) ^ t * x) /
              ((algebraMap (↥F) K12 ζF) ^ t * (β ^ t)) := by
          simp [hσx, hσβt]
        _ = x / (β ^ t) := by
          -- cancel the common nonzero factor `algebraMap F K (ζF^t)`
          have hζt0' : ((ζF : K12) ^ t) ≠ 0 := by
            simpa using hζt0
          simpa [mul_div_mul_left, hζt0']
        _ = y := rfl

    -- Since `Gal(K/F)` has prime order `7` and `σ ≠ 1`, it generates, so `y ∈ F`.
    haveI : IsGalois (↥F) K12 :=
      isGalois_of_isSplittingField_X_pow_sub_C (K := (↥F)) (L := K12) ⟨ζF, by
        -- `ζF` is in `primitiveRoots`
        have hn : (0 : ℕ) < 7 := by decide
        exact (mem_primitiveRoots hn).2 hζF⟩ hirr
    have hcardGal : Nat.card (Gal(K12/F)) = 7 := by
      -- `|Gal(K/F)| = [K:F] = 7`
      have hfin : Module.finrank (↥F) K12 = 7 :=
        finrank_of_isSplittingField_X_pow_sub_C (K := (↥F)) (L := K12) ⟨ζF, by
          have hn : (0 : ℕ) < 7 := by decide
          exact (mem_primitiveRoots hn).2 hζF⟩ hirr
      simpa [hfin] using (IsGalois.card_aut_eq_finrank (F := (↥F)) (E := K12))
    have hσne1 : σ ≠ 1 := by
      intro h
      have hmul : (Multiplicative.ofAdd (1 : ZMod 7) : Multiplicative (ZMod 7)) = 1 := by
        simpa [σ] using congrArg (fun g => e g) h
      have hadd : (1 : ZMod 7) = 0 := by
        simpa using congrArg Multiplicative.toAdd hmul
      exact (by decide : (1 : ZMod 7) ≠ 0) hadd

    let stab : Subgroup (Gal(K12/F)) := MulAction.stabilizer (Gal(K12/F)) y
    have hσmem : σ ∈ stab := (MulAction.mem_stabilizer_iff).2 (by simpa using hσy)
    have hzpow_le : Subgroup.zpowers σ ≤ stab := (Subgroup.zpowers_le).2 hσmem
    have hzpow_top : Subgroup.zpowers σ = ⊤ := by
      have hp7 : Fact (Nat.Prime 7) := ⟨by decide⟩
      exact zpowers_eq_top_of_prime_card (G := Gal(K12/F)) (p := 7) hcardGal hσne1
    have hstab : stab = ⊤ := by
      refine le_antisymm le_top ?_
      have : (⊤ : Subgroup (Gal(K12/F))) ≤ stab := by simpa [hzpow_top] using hzpow_le
      simpa using this
    have hy_fixed : ∀ f : Gal(K12/F), f y = y := by
      intro f
      have hfmem : f ∈ stab := by simpa [hstab] using (show f ∈ (⊤ : Subgroup (Gal(K12/F))) by simp)
      exact (MulAction.mem_stabilizer_iff).1 hfmem
    have hy_mem : y ∈ Set.range (algebraMap (↥F) K12) :=
      (IsGalois.mem_range_algebraMap_iff_fixed (F := (↥F)) (E := K12) y).2 hy_fixed
    rcases hy_mem with ⟨y0, hy0⟩
    -- show `y0^7 = 11 / 12^t` in `F`, hence `11/12^t` is a 7th power in `ℚ`, contradiction.
    have hy0pow :
        (y0 ^ (7 : ℕ)) = algebraMap ℚ (↥F) ((11 : ℚ) / (12 : ℚ) ^ t) := by
      -- apply `algebraMap F K` and simplify in `K`
      apply (algebraMap (↥F) K12).injective
      -- left side
      -- rewrite `y` via `y0`
      have hy0' : algebraMap (↥F) K12 y0 = y := hy0
      have hβt : (β ^ t) ^ (7 : ℕ) = (algebraMap (↥F) K12 (12 : (↥F))) ^ t := by
        calc
          (β ^ t) ^ (7 : ℕ) = β ^ (t * 7) := by simp [pow_mul]
          _ = β ^ (7 * t) := by simp [Nat.mul_comm]
          _ = (β ^ (7 : ℕ)) ^ t := by simp [pow_mul]
          _ = (algebraMap (↥F) K12 (12 : (↥F))) ^ t := by simpa [hβ]
      -- Now compute in `K12` and use `hβt` to rewrite the denominator.
      simp [map_pow, hy0', y, hx, hβt, IsScalarTower.algebraMap_eq ℚ (↥F) K12, div_pow]
      -- remaining goal: `11 = (↑(11 : (↥F)) : K12)`
      simpa using (map_natCast (algebraMap (↥F) K12) 11).symm
    have : ((11 : ℚ) / (12 : ℚ) ^ t) ∈ Set.range (fun q : ℚ => q ^ (7 : ℕ)) :=
      rat_isSeventhPower_of_pow_eq_algebraMap (y := y0) (r := (11 : ℚ) / (12 : ℚ) ^ t) hy0pow
    rcases this with ⟨q, hq⟩
    exact rat_not_seventhPower_11_div_12_pow t ⟨q, hq⟩

  -- Finally, translate the contradiction into `rootSet = ⊥`.
  ext x
  constructor
  · intro hxmem
    have hf11 : (.X ^ 7 - 11 : Polynomial ℚ) ≠ 0 := by
      simpa [sub_eq_add_neg] using
        (X_pow_sub_C_ne_zero (R := ℚ) (n := 7) (a := (11 : ℚ)) (by decide))
    have hx0 : aeval x (X ^ (7 : ℕ) - C (11 : ℚ)) = 0 :=
      (mem_rootSet_of_ne (p := (X ^ (7 : ℕ) - C (11 : ℚ) : Polynomial ℚ)) (S := K12) hf11).1 hxmem
    have hx7 : x ^ (7 : ℕ) = (11 : K12) := by
      exact sub_eq_zero.mp (by simpa [aeval_def] using hx0)
    exact (no_root x hx7).elim
  · intro hxbot
    simpa using hxbot

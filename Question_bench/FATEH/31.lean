import Mathlib

open Polynomial
open scoped BigOperators

/-! Helper lemmas to reduce the basis statement to linear independence. -/

-- The primitive roots in the cyclotomic field have cardinality `phi n`.
lemma primitiveRoots_card_eq_totient {n : ℕ+} :
    Fintype.card {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =
      Nat.totient (n : ℕ) := by
  classical
  simpa using
    (IsPrimitiveRoot.card_primitiveRoots
      (R := CyclotomicField n ℚ)
      (k := (n : ℕ))
      (ζ := IsCyclotomicExtension.zeta (n : ℕ) ℚ (CyclotomicField n ℚ))
      (IsCyclotomicExtension.zeta_spec (n : ℕ) ℚ (CyclotomicField n ℚ)))

-- The cyclotomic field has degree `phi n` over `ℚ`.
lemma finrank_cyclotomicField_eq_totient {n : ℕ+} :
    Module.finrank ℚ (CyclotomicField n ℚ) = Nat.totient (n : ℕ) := by
  classical
  simpa using
    (IsCyclotomicExtension.finrank (K := ℚ) (L := CyclotomicField n ℚ) (n := (n : ℕ))
      (cyclotomic.irreducible_rat (n.pos)))

-- There is always at least one primitive root in the cyclotomic field.
lemma primitiveRoots_nonempty {n : ℕ+} :
    Nonempty
      {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} := by
  classical
  refine ⟨⟨IsCyclotomicExtension.zeta (n : ℕ) ℚ (CyclotomicField n ℚ), ?_⟩⟩
  have hζ := IsCyclotomicExtension.zeta_spec (n : ℕ) ℚ (CyclotomicField n ℚ)
  exact (mem_primitiveRoots (n.pos)).2 hζ

-- A linearly independent family of all primitive roots yields the requested basis.
lemma basis_of_linearIndependent_primitiveRoots {n : ℕ+}
    (hlin :
      LinearIndependent ℚ
        (fun ζ :
          {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
          (ζ : CyclotomicField n ℚ))) :
    ∃ b :
      Module.Basis ({ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)})
        ℚ (CyclotomicField n ℚ),
      (b : _ → _) =
        fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
          (ζ : CyclotomicField n ℚ) := by
  classical
  haveI :
      Nonempty
        {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} :=
    primitiveRoots_nonempty (n := n)
  have hcard :
      Fintype.card
          {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =
        Module.finrank ℚ (CyclotomicField n ℚ) := by
    simp [primitiveRoots_card_eq_totient (n := n), finrank_cyclotomicField_eq_totient (n := n)]
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hlin hcard, ?_⟩
  exact
    (coe_basisOfLinearIndependentOfCardEqFinrank
      (K := ℚ) (V := CyclotomicField n ℚ)
      (b := fun ζ :
        {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
        (ζ : CyclotomicField n ℚ)) hlin hcard)

-- Helper: every power of `ζ` lies in the span of primitive roots when `n` is squarefree.
lemma pow_mem_span_primitiveRoots_of_squarefree {n : ℕ+} (hn : Squarefree (n : ℕ)) :
    let ζ := IsCyclotomicExtension.zeta (n : ℕ) ℚ (CyclotomicField n ℚ)
    let S :
        Submodule ℚ (CyclotomicField n ℚ) :=
        Submodule.span ℚ
          (Set.range fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
            (ζ : CyclotomicField n ℚ))
    ∀ k : ℕ, ζ ^ k ∈ S := by
  classical
  let nNat : ℕ := (n : ℕ)
  let ζ := IsCyclotomicExtension.zeta nNat ℚ (CyclotomicField n ℚ)
  let S :
      Submodule ℚ (CyclotomicField n ℚ) :=
      Submodule.span ℚ
        (Set.range fun ζ :
          {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots nNat (CyclotomicField n ℚ)} =>
          (ζ : CyclotomicField n ℚ))
  have hζ : IsPrimitiveRoot ζ nNat :=
    IsCyclotomicExtension.zeta_spec nNat ℚ (CyclotomicField n ℚ)
  let P : Finset ℕ := nNat.primeFactors
  let bad : ℕ → Finset ℕ := fun k => P.filter fun p => p ∣ k
  have hprime : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors hp
  have hdivn : ∀ p ∈ P, p ∣ nNat := by
    intro p hp
    exact Nat.dvd_of_mem_primeFactors hp
  have hne0 : nNat ≠ 0 := by
    exact ne_of_gt n.pos
  have hrec :
      ∀ m : ℕ, ∀ k : ℕ, (bad k).card ≤ m → ζ ^ k ∈ S := by
    refine Nat.rec ?base ?step
    · intro k hk
      have hcard : (bad k).card = 0 := by
        exact Nat.le_antisymm hk (Nat.zero_le _)
      have hbad : bad k = ∅ := by
        exact Finset.card_eq_zero.mp hcard
      have hcop : Nat.Coprime k nNat := by
        by_contra hnc
        rcases (Nat.Prime.not_coprime_iff_dvd).1 hnc with ⟨p, hpprime, hpk, hpn⟩
        have hpP : p ∈ P := (Nat.mem_primeFactors_of_ne_zero hne0).2 ⟨hpprime, hpn⟩
        have hpbad : p ∈ bad k := by
          simp [bad, hpP, hpk]
        simp [hbad] at hpbad
      have hprim : IsPrimitiveRoot (ζ ^ k) nNat := (hζ.pow_iff_coprime n.pos k).2 hcop
      have hk : ζ ^ k ∈ primitiveRoots nNat (CyclotomicField n ℚ) :=
        (mem_primitiveRoots n.pos).2 hprim
      exact
        Submodule.subset_span
          ⟨⟨ζ ^ k, hk⟩, rfl⟩
    · intro m ih k hk
      by_cases hle : (bad k).card ≤ m
      · exact ih k hle
      · have hgt : m < (bad k).card := Nat.lt_of_not_ge hle
        have hcard : (bad k).card = m + 1 :=
          Nat.le_antisymm hk (Nat.succ_le_iff.mpr hgt)
        have hbad_ne : bad k ≠ ∅ := by
          intro h
          have hzero : (bad k).card = 0 := by
            exact Finset.card_eq_zero.mpr h
          simp [hcard] at hzero
        rcases (Finset.nonempty_iff_ne_empty.2 hbad_ne) with ⟨p, hpbad⟩
        have hpP : p ∈ P := (Finset.mem_filter.mp hpbad).1
        have hpk : p ∣ k := (Finset.mem_filter.mp hpbad).2
        have hpprime : Nat.Prime p := hprime p hpP
        have hpn : p ∣ nNat := hdivn p hpP
        let m' : ℕ := nNat / p
        have hmul : nNat = m' * p := by
          simpa [m', Nat.mul_comm] using (Nat.mul_div_cancel' hpn).symm
        have hnot_dvd_m' : ¬ p ∣ m' := by
          intro hpm
          have hp2 : p * p ∣ nNat := by
            rcases hpm with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            calc
              nNat = m' * p := hmul
              _ = (p * t) * p := by simp [m', ht]
              _ = p * p * t := by ac_rfl
          have hsq := (Nat.squarefree_iff_prime_squarefree (n := nNat)).1 hn
          exact (hsq p hpprime) hp2
        have hβ : IsPrimitiveRoot (ζ ^ m') p :=
          hζ.pow n.pos hmul
        have hsum :
            ∑ j ∈ Finset.range p, ζ ^ (k + m' * j) = 0 := by
          have hsum' :
              ∑ j ∈ Finset.range p, (ζ ^ m') ^ j = 0 :=
            hβ.geom_sum_eq_zero (by exact hpprime.one_lt)
          have hsum'' := congrArg (fun x => ζ ^ k * x) hsum'
          -- push multiplication inside the sum
          have hsum''' :
              ∑ j ∈ Finset.range p, ζ ^ k * (ζ ^ m') ^ j = 0 := by
            simpa [Finset.mul_sum] using hsum''
          -- rewrite to powers of `ζ`
          have hsum_eq :
              (∑ j ∈ Finset.range p, ζ ^ k * (ζ ^ m') ^ j) =
                ∑ j ∈ Finset.range p, ζ ^ (k + m' * j) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              ζ ^ k * (ζ ^ m') ^ j = ζ ^ k * ζ ^ (m' * j) := by
                rw [← pow_mul]
              _ = ζ ^ (k + m' * j) := by
                symm
                rw [pow_add]
          simpa [hsum_eq] using hsum'''
        have hsum_split :
            ζ ^ k +
              ∑ j ∈ Finset.range (p - 1), ζ ^ (k + m' * (j + 1)) = 0 := by
          have hp1 : 1 ≤ p := Nat.succ_le_of_lt hpprime.pos
          have hp' : p = (p - 1) + 1 := (Nat.sub_add_cancel hp1).symm
          have hsum' :
              (∑ j ∈ Finset.range ((p - 1) + 1), ζ ^ (k + m' * j)) = 0 := by
            have hsum' := hsum
            rw [hp'] at hsum'
            exact hsum'
          have hsum'' :
              (∑ j ∈ Finset.range (p - 1), ζ ^ (k + m' * (j + 1))) +
                  ζ ^ (k + m' * 0) = 0 := by
            have hsum'' := hsum'
            rw [Finset.sum_range_succ' (f := fun j => ζ ^ (k + m' * j)) (n := p - 1)] at hsum''
            exact hsum''
          -- reorder and simplify the `j = 0` term
          simpa [add_comm, Nat.mul_zero, Nat.add_zero] using hsum''
        have hsum_eq :
            ζ ^ k =
              -∑ j ∈ Finset.range (p - 1), ζ ^ (k + m' * (j + 1)) :=
          (eq_neg_iff_add_eq_zero).2 hsum_split
        have hsubset :
            ∀ j ∈ Finset.range (p - 1),
              bad (k + m' * (j + 1)) ⊆ (bad k).erase p := by
          intro j hj q hq
          have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
          have hqdiv : q ∣ k + m' * (j + 1) := (Finset.mem_filter.mp hq).2
          have hqprime : Nat.Prime q := hprime q hqP
          have hqdivn : q ∣ nNat := hdivn q hqP
          have hqne : q ≠ p := by
            intro hqp
            subst q
            -- show `p ∤ k + m' * (j + 1)`
            have hjpos : 0 < j + 1 := Nat.succ_pos _
            have hlt : j + 1 < p := by
              have hjlt : j < p - 1 := Finset.mem_range.mp hj
              have hp' : (p - 1) + 1 = p := by
                simpa [Nat.succ_eq_add_one] using Nat.succ_pred_eq_of_pos hpprime.pos
              simpa [hp', Nat.succ_eq_add_one] using (Nat.succ_lt_succ_iff.mpr hjlt)
            have hdiv' : p ∣ m' * (j + 1) := by
              have := (Nat.dvd_add_iff_left hpk).2 (by simpa [add_comm, add_left_comm, add_assoc] using hqdiv)
              simpa [mul_comm] using this
            rcases hpprime.dvd_or_dvd hdiv' with hpm' | hpj
            · exact (hnot_dvd_m' hpm').elim
            · have hle : p ≤ j + 1 := Nat.le_of_dvd hjpos hpj
              exact (not_le_of_gt hlt) hle
          have hqnot_dvd_p : ¬ q ∣ p := by
            intro hqp
            have := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).1 hqp
            exact hqne this
          have hqdivm' : q ∣ m' := by
            have hqmul : q ∣ m' * p := by
              simpa [hmul, mul_comm, mul_left_comm, mul_assoc] using hqdivn
            rcases hqprime.dvd_or_dvd hqmul with hqdivm' | hqdivp
            · exact hqdivm'
            · exact (hqnot_dvd_p hqdivp).elim
          have hqk : q ∣ k := by
            have hqmul' : q ∣ m' * (j + 1) := dvd_mul_of_dvd_left hqdivm' _
            have hqk' := (Nat.dvd_add_iff_left hqmul').2
              (by simpa [add_comm, add_left_comm, add_assoc] using hqdiv)
            simpa using hqk'
          exact Finset.mem_erase.mpr ⟨hqne, by simp [bad, hqP, hqk]⟩
        have hcard_erase : ((bad k).erase p).card = m := by
          have hcard' : (bad k).card = m + 1 := hcard
          have hcard_erase' : ((bad k).erase p).card = (bad k).card - 1 :=
            Finset.card_erase_of_mem hpbad
          simpa [hcard', Nat.succ_eq_add_one] using hcard_erase'
        have hsum_mem :
            ∑ j ∈ Finset.range (p - 1), ζ ^ (k + m' * (j + 1)) ∈ S := by
          refine S.sum_mem ?_
          intro j hj
          have hsub := hsubset j hj
          have hcard_le : (bad (k + m' * (j + 1))).card ≤ m := by
            have hcard_le' := Finset.card_le_card hsub
            simpa [hcard_erase] using hcard_le'
          exact ih (k + m' * (j + 1)) hcard_le
        have hneg_mem :
            -∑ j ∈ Finset.range (p - 1), ζ ^ (k + m' * (j + 1)) ∈ S :=
          Submodule.neg_mem _ hsum_mem
        simpa [hsum_eq] using hneg_mem
  simpa [nNat, ζ, S] using (fun k : ℕ => hrec (bad k).card k (le_rfl))

-- Squarefree case: primitive roots span the cyclotomic field.
lemma primitiveRoots_span_eq_top_of_squarefree {n : ℕ+} (hn : Squarefree (n : ℕ)) :
    Submodule.span ℚ
      (Set.range fun ζ :
        {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
        (ζ : CyclotomicField n ℚ)) = ⊤ := by
  classical
  let ζ := IsCyclotomicExtension.zeta (n : ℕ) ℚ (CyclotomicField n ℚ)
  let S :
      Submodule ℚ (CyclotomicField n ℚ) :=
      Submodule.span ℚ
        (Set.range fun ζ :
          {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
          (ζ : CyclotomicField n ℚ))
  have hζ : IsPrimitiveRoot ζ (n : ℕ) :=
    IsCyclotomicExtension.zeta_spec (n : ℕ) ℚ (CyclotomicField n ℚ)
  let pb := hζ.powerBasis ℚ
  have hmem : Set.range pb.basis ⊆ (S : Set (CyclotomicField n ℚ)) := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    have hpow : ζ ^ (i : ℕ) ∈ S := by
      simpa [ζ, S] using
        (pow_mem_span_primitiveRoots_of_squarefree (n := n) hn (k := (i : ℕ)))
    simpa [pb.basis_eq_pow] using hpow
  have hspan_le : Submodule.span ℚ (Set.range pb.basis) ≤ S :=
    Submodule.span_le.2 hmem
  have htop : (⊤ : Submodule ℚ (CyclotomicField n ℚ)) ≤ S := by
    have htopEq :
        (⊤ : Submodule ℚ (CyclotomicField n ℚ)) =
          Submodule.span ℚ (Set.range pb.basis) := by
      simpa using (pb.basis.span_eq (R := ℚ)).symm
    rw [htopEq]
    exact hspan_le
  exact top_le_iff.mp htop

-- Core arithmetic input: primitive roots are linearly independent iff `n` is squarefree.
lemma linearIndependent_primitiveRoots_iff_squarefree {n : ℕ+} :
    LinearIndependent ℚ
        (fun ζ :
          {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
          (ζ : CyclotomicField n ℚ)) ↔
      Squarefree (n : ℕ) := by
  classical
  constructor
  · intro hlin
    by_contra hn
    -- build a nontrivial linear dependence from a square factor
    have hnot :
        ¬LinearIndependent ℚ
          (fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
            (ζ : CyclotomicField n ℚ)) := by
      -- produce a prime square dividing `n`
      have hsq :
          ∃ p : ℕ, Nat.Prime p ∧ p * p ∣ (n : ℕ) := by
        by_contra h
        have hforall : ∀ p, Nat.Prime p → ¬p * p ∣ (n : ℕ) := by
          intro p hp
          by_contra hpp
          exact h ⟨p, hp, hpp⟩
        exact hn ((Nat.squarefree_iff_prime_squarefree (n := (n : ℕ))).2 hforall)
      rcases hsq with ⟨p, hpprime, hp2⟩
      let ζ := IsCyclotomicExtension.zeta (n : ℕ) ℚ (CyclotomicField n ℚ)
      have hζ : IsPrimitiveRoot ζ (n : ℕ) :=
        IsCyclotomicExtension.zeta_spec (n : ℕ) ℚ (CyclotomicField n ℚ)
      have hpdiv : p ∣ (n : ℕ) := (dvd_trans (dvd_mul_left p p) hp2)
      let m : ℕ := (n : ℕ) / p
      have hmul : (n : ℕ) = m * p := by
        simpa [m, Nat.mul_comm] using (Nat.mul_div_cancel' hpdiv).symm
      have hβ : IsPrimitiveRoot (ζ ^ m) p :=
        hζ.pow n.pos hmul
      have hsum :
          ∑ j ∈ Finset.range p, ζ * (ζ ^ m) ^ j = 0 := by
        have hsum' :
            ∑ j ∈ Finset.range p, (ζ ^ m) ^ j = 0 :=
          hβ.geom_sum_eq_zero (by exact hpprime.one_lt)
        have hsum'' := congrArg (fun x => ζ * x) hsum'
        simpa [Finset.mul_sum] using hsum''
      -- show the corresponding subfamily is linearly dependent
      have hdep :
          ¬LinearIndependent ℚ (fun j : Fin p => ζ * (ζ ^ m) ^ (j : ℕ)) := by
        classical
        refine (Fintype.not_linearIndependent_iff (R := ℚ)
          (v := fun j : Fin p => ζ * (ζ ^ m) ^ (j : ℕ))).2 ?_
        refine ⟨fun _ => (1 : ℚ), ?_, ?_⟩
        · -- the sum over all indices is zero
          have hsumFin :
              (∑ j : Fin p, ζ * (ζ ^ m) ^ (j : ℕ)) =
                ∑ j ∈ Finset.range p, ζ * (ζ ^ m) ^ j := by
            simpa using
              (Fin.sum_univ_eq_sum_range (f := fun j : ℕ => ζ * (ζ ^ m) ^ j) (n := p))
          have : (∑ j : Fin p, ζ * (ζ ^ m) ^ (j : ℕ)) = 0 := by
            rw [hsumFin]
            exact hsum
          simpa [one_smul] using this
        · refine ⟨⟨0, hpprime.pos⟩, by simp⟩
      -- show each `ζ * (ζ^m)^j` is a primitive root
      have hmem :
          ∀ j : Fin p,
            (ζ * (ζ ^ m) ^ (j : ℕ)) ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ) := by
        intro j
        have hcop :
            Nat.Coprime (1 + j * ((n : ℕ) / p)) (n : ℕ) := by
          -- every prime factor of `n` divides `(n / p)`, so none divides the sum
          by_contra hnc
          rcases (Nat.Prime.not_coprime_iff_dvd).1 hnc with ⟨q, hqprime, hq1, hqn⟩
          have hqdiv : q ∣ (n : ℕ) / p := by
            by_cases hqeq : q = p
            · subst q
              have hpdiv : p ∣ (n : ℕ) := (dvd_trans (dvd_mul_left p p) hp2)
              have hmul' : p * ((n : ℕ) / p) = (n : ℕ) := Nat.mul_div_cancel' hpdiv
              have hp2' : p * p ∣ p * ((n : ℕ) / p) := by
                simpa [hmul'] using hp2
              exact Nat.dvd_of_mul_dvd_mul_left hpprime.pos hp2'
            ·
              have hqnot : ¬ q ∣ p := by
                intro hq
                have hqp := (Nat.prime_dvd_prime_iff_eq hqprime hpprime).1 hq
                exact hqeq hqp
              have hqmul : q ∣ (m * p) := by
                simpa [hmul] using hqn
              have hqcop : Nat.Coprime q p :=
                (hqprime.coprime_iff_not_dvd).2 hqnot
              exact hqcop.dvd_of_dvd_mul_right hqmul
          have hqmul : q ∣ (j : ℕ) * ((n : ℕ) / p) :=
            dvd_mul_of_dvd_right hqdiv _
          have hqdiv' : q ∣ (1 : ℕ) := by
            exact (Nat.dvd_add_iff_left hqmul).2 hq1
          exact hqprime.not_dvd_one hqdiv'
        have hprim :
            IsPrimitiveRoot (ζ ^ (1 + j * ((n : ℕ) / p))) (n : ℕ) :=
          (hζ.pow_iff_coprime n.pos _).2 hcop
        have hpow :
            ζ * (ζ ^ m) ^ (j : ℕ) = ζ ^ (1 + j * ((n : ℕ) / p)) := by
          calc
            ζ * (ζ ^ m) ^ (j : ℕ) = ζ * ζ ^ (m * (j : ℕ)) := by
              rw [← pow_mul]
            _ = ζ ^ (1 + m * (j : ℕ)) := by
              symm
              simpa using (pow_add ζ 1 (m * (j : ℕ)))
            _ = ζ ^ (1 + j * ((n : ℕ) / p)) := by
              simp [m, mul_comm]
        simpa [hpow] using (mem_primitiveRoots n.pos).2 hprim
      -- transport the dependence to the primitive roots family
      intro hlin'
      have hf :
          Function.Injective
            (fun j : Fin p =>
              (⟨ζ * (ζ ^ m) ^ (j : ℕ), hmem j⟩ :
                {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)})) := by
        intro i j hij
        have hne : (ζ : CyclotomicField n ℚ) ≠ 0 := by
          intro hz
          have : (0 : CyclotomicField n ℚ) = 1 := by
            simpa [hz] using hζ.pow_eq_one
          exact zero_ne_one this
        have hβinj :
            (ζ ^ m) ^ (i : ℕ) = (ζ ^ m) ^ (j : ℕ) := by
          have hij' :
              (ζ : CyclotomicField n ℚ) * (ζ ^ m) ^ (i : ℕ) =
                (ζ : CyclotomicField n ℚ) * (ζ ^ m) ^ (j : ℕ) := by
            simpa using congrArg Subtype.val hij
          have := congrArg (fun x => (ζ : CyclotomicField n ℚ)⁻¹ * x) hij'
          simpa [hne, mul_assoc, mul_left_comm, mul_comm] using this
        have hi : (i : ℕ) < p := i.is_lt
        have hj : (j : ℕ) < p := j.is_lt
        have := hβ.pow_inj hi hj hβinj
        exact Fin.ext this
      have hlin_sub :
          LinearIndependent ℚ (fun j : Fin p => ζ * (ζ ^ m) ^ (j : ℕ)) := by
        simpa using
          hlin'.comp
            (fun j : Fin p =>
              (⟨ζ * (ζ ^ m) ^ (j : ℕ), hmem j⟩ :
                {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)}))
            hf
      exact hdep hlin_sub
    exact hnot hlin
  · intro hn
    -- squarefree implies spanning; use cardinality to conclude linear independence
    have hspan :
        Submodule.span ℚ
          (Set.range fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
            (ζ : CyclotomicField n ℚ)) = ⊤ :=
      primitiveRoots_span_eq_top_of_squarefree (n := n) hn
    have hcard :
        Fintype.card
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =
          Module.finrank ℚ (CyclotomicField n ℚ) := by
      simp [primitiveRoots_card_eq_totient (n := n), finrank_cyclotomicField_eq_totient (n := n)]
    have hcard' :
        Fintype.card
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =
          Set.finrank ℚ
            (Set.range fun ζ :
              {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
              (ζ : CyclotomicField n ℚ)) := by
      -- rewrite `Set.finrank` via the span (which is `⊤` by `hspan`)
      calc
        Fintype.card
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =
            Module.finrank ℚ (CyclotomicField n ℚ) := hcard
        _ = Module.finrank ℚ (↥(⊤ : Submodule ℚ (CyclotomicField n ℚ))) := by
          exact (finrank_top (R := ℚ) (M := CyclotomicField n ℚ)).symm
        _ = Module.finrank ℚ
            (↥(Submodule.span ℚ
              (Set.range fun ζ :
                {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
                (ζ : CyclotomicField n ℚ)))) := by
          simpa using
            (congrArg
              (fun U : Submodule ℚ (CyclotomicField n ℚ) => Module.finrank ℚ (↥U)) hspan).symm
        _ = Set.finrank ℚ
            (Set.range fun ζ :
              {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
              (ζ : CyclotomicField n ℚ)) := by
          simpa using
            (Set.finrank.eq_1 (R := ℚ)
              (s := Set.range fun ζ :
                {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
                (ζ : CyclotomicField n ℚ))).symm
    exact
      (linearIndependent_iff_card_eq_finrank_span (b := fun ζ :
        {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
        (ζ : CyclotomicField n ℚ))).2 hcard'

/- Prove that the primitive $n^{\textrm{th}}$ roots of unity form a basis over $\mathbb{Q}$ for
the cyclotomic field of $n^{\textrm{th}}$ roots of unity if and only if $n$ is squarefree.-/
theorem exists_basis_primitiveRoots_iff_squarefree {n : ℕ+} :
    (∃ b :
      Module.Basis ({ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)})
        ℚ (CyclotomicField n ℚ),
      (b : _ → _) =
        fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
          (ζ : CyclotomicField n ℚ)) ↔ Squarefree (n : ℕ) := by
  classical
  constructor
  · rintro ⟨b, hb⟩
    have hlin :
        LinearIndependent ℚ
          (fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
            (ζ : CyclotomicField n ℚ)) := by
      simpa [hb] using b.linearIndependent
    exact (linearIndependent_primitiveRoots_iff_squarefree (n := n)).1 hlin
  · intro hn
    have hlin :
        LinearIndependent ℚ
          (fun ζ :
            {ζ : CyclotomicField n ℚ // ζ ∈ primitiveRoots (n : ℕ) (CyclotomicField n ℚ)} =>
            (ζ : CyclotomicField n ℚ)) :=
      (linearIndependent_primitiveRoots_iff_squarefree (n := n)).2 hn
    exact basis_of_linearIndependent_primitiveRoots (n := n) hlin

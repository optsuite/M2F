import Mathlib

/-- Prove that if $\#G = 1053$ then $G$ is not simple. -/
-- Small arithmetic lemmas to pin down Sylow counts.
private lemma nat_eq_one_or_twentyseven_of_dvd_81_of_modEq_one (n : ℕ) (hn : n ∣ 81)
    (hmod : n ≡ 1 [MOD 13]) : n = 1 ∨ n = 27 := by
  have hn_mem : n ∈ (81 : ℕ).divisors := (Nat.mem_divisors).2 ⟨hn, by decide⟩
  have hdiv : (81 : ℕ).divisors = ({1, 3, 9, 27, 81} : Finset ℕ) := by
    native_decide
  have hn_cases : n = 1 ∨ n = 3 ∨ n = 9 ∨ n = 27 ∨ n = 81 := by
    have : n ∈ ({1, 3, 9, 27, 81} : Finset ℕ) := by simpa [hdiv] using hn_mem
    simpa using this
  rcases hn_cases with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exfalso
    exact (by decide : ¬ ((3 : ℕ) ≡ 1 [MOD 13])) (by simpa using hmod)
  · exfalso
    exact (by decide : ¬ ((9 : ℕ) ≡ 1 [MOD 13])) (by simpa using hmod)
  · exact Or.inr rfl
  · exfalso
    exact (by decide : ¬ ((81 : ℕ) ≡ 1 [MOD 13])) (by simpa using hmod)

private lemma nat_eq_one_or_thirteen_of_dvd_13_of_modEq_one (n : ℕ) (hn : n ∣ 13)
    (hmod : n ≡ 1 [MOD 3]) : n = 1 ∨ n = 13 := by
  have hn_mem : n ∈ (13 : ℕ).divisors := (Nat.mem_divisors).2 ⟨hn, by decide⟩
  have hdiv : (13 : ℕ).divisors = ({1, 13} : Finset ℕ) := by
    native_decide
  have hn_cases : n = 1 ∨ n = 13 := by
    have : n ∈ ({1, 13} : Finset ℕ) := by simpa [hdiv] using hn_mem
    simpa using this
  rcases hn_cases with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem not_isSimpleGroup_of_card_eq_1053 (G : Type) [Group G]
    [Finite G] (h_card : Nat.card G = 1053) : ¬ IsSimpleGroup G := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 13) := ⟨by decide⟩
  haveI : Finite (Sylow 3 G) := by infer_instance
  haveI : Finite (Sylow 13 G) := by infer_instance

  -- Fix Sylow subgroups for 3 and 13.
  let P : Sylow 3 G := Classical.choice (inferInstance : Nonempty (Sylow 3 G))
  let Q13 : Sylow 13 G := Classical.choice (inferInstance : Nonempty (Sylow 13 G))
  have hfac3 : Nat.factorization 1053 3 = 4 := by native_decide
  have hfac13 : Nat.factorization 1053 13 = 1 := by native_decide
  have hcardP : Nat.card (P : Subgroup G) = 81 := by
    have h := Sylow.card_eq_multiplicity (G := G) (p := 3) P
    rw [h_card] at h
    simpa [hfac3] using h
  have hcardQ13 : Nat.card (Q13 : Subgroup G) = 13 := by
    have h := Sylow.card_eq_multiplicity (G := G) (p := 13) Q13
    rw [h_card] at h
    simpa [hfac13] using h
  have hindexP : (P : Subgroup G).index = 13 := by
    have hmul : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
      (P : Subgroup G).card_mul_index
    have hmul' : 81 * (P : Subgroup G).index = 1053 := by
      have hmul' := hmul
      rw [hcardP, h_card] at hmul'
      simpa using hmul'
    have hmul'' : 81 * (P : Subgroup G).index = 81 * 13 := by
      simpa using hmul'.trans (by decide : (1053 : ℕ) = 81 * 13)
    exact Nat.mul_left_cancel (by decide : 0 < 81) hmul''
  have hindexQ13 : (Q13 : Subgroup G).index = 81 := by
    have hmul : Nat.card (Q13 : Subgroup G) * (Q13 : Subgroup G).index = Nat.card G :=
      (Q13 : Subgroup G).card_mul_index
    have hmul' : 13 * (Q13 : Subgroup G).index = 1053 := by
      have hmul' := hmul
      rw [hcardQ13, h_card] at hmul'
      simpa using hmul'
    have hmul'' : 13 * (Q13 : Subgroup G).index = 13 * 81 := by
      simpa using hmul'.trans (by decide : (1053 : ℕ) = 13 * 81)
    exact Nat.mul_left_cancel (by decide : 0 < 13) hmul''

  -- Sylow counts.
  let n3 : ℕ := Nat.card (Sylow 3 G)
  let n13 : ℕ := Nat.card (Sylow 13 G)
  have hn3_dvd : n3 ∣ 13 := by
    have : n3 ∣ (P : Subgroup G).index := by
      simpa [n3] using (Sylow.card_dvd_index (p := 3) (G := G) P)
    simpa [hindexP] using this
  have hn3_mod : n3 ≡ 1 [MOD 3] := by
    simpa [n3] using (card_sylow_modEq_one (p := 3) (G := G))
  have hn3_cases : n3 = 1 ∨ n3 = 13 :=
    nat_eq_one_or_thirteen_of_dvd_13_of_modEq_one n3 hn3_dvd hn3_mod
  have hn13_dvd : n13 ∣ 81 := by
    have : n13 ∣ (Q13 : Subgroup G).index := by
      simpa [n13] using (Sylow.card_dvd_index (p := 13) (G := G) Q13)
    simpa [hindexQ13] using this
  have hn13_mod : n13 ≡ 1 [MOD 13] := by
    simpa [n13] using (card_sylow_modEq_one (p := 13) (G := G))
  have hn13_cases : n13 = 1 ∨ n13 = 27 :=
    nat_eq_one_or_twentyseven_of_dvd_81_of_modEq_one n13 hn13_dvd hn13_mod

  intro hS
  have hS' := (isSimpleGroup_iff G).1 hS
  have hsimple : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ := hS'.2

  rcases hn13_cases with hn13_eq1 | hn13_eq27
  · -- Unique Sylow-13 subgroup is normal.
    haveI : Subsingleton (Sylow 13 G) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa [n13] using hn13_eq1)).1
    have hQnormal : (Q13 : Subgroup G).Normal := by
      simpa using (Sylow.normal_of_subsingleton (P := Q13))
    rcases hsimple (Q13 : Subgroup G) hQnormal with hbot | htop
    · have hcardQ' : (1 : ℕ) = 13 := by
        have hcardQ' := hcardQ13
        simp [hbot] at hcardQ'
      exact (by decide : (1 : ℕ) ≠ 13) hcardQ'
    · have htop' := hcardQ13
      rw [htop] at htop'
      have hG13 : Nat.card G = 13 := (Subgroup.card_top (G := G)).symm.trans htop'
      rw [h_card] at hG13
      exact (by decide : (1053 : ℕ) ≠ 13) hG13
  · -- Now `n₁₃ = 27`; if `n₃ = 1` then the Sylow-3 subgroup is normal, else use the action.
    rcases hn3_cases with hn3_eq1 | hn3_eq13
    · haveI : Subsingleton (Sylow 3 G) :=
        (Nat.card_eq_one_iff_unique.mp (by simpa [n3] using hn3_eq1)).1
      have hPnormal : (P : Subgroup G).Normal := by
        simpa using (Sylow.normal_of_subsingleton (P := P))
      rcases hsimple (P : Subgroup G) hPnormal with hbot | htop
      · have hcardP' : (1 : ℕ) = 81 := by
          have hcardP' := hcardP
          simp [hbot] at hcardP'
        exact (by decide : (1 : ℕ) ≠ 81) hcardP'
      · have htop' := hcardP
        rw [htop] at htop'
        have hG81 : Nat.card G = 81 := (Subgroup.card_top (G := G)).symm.trans htop'
        rw [h_card] at hG81
        exact (by decide : (1053 : ℕ) ≠ 81) hG81
    · -- The hard case: `n₃ = 13` and `n₁₃ = 27`.
      have hn3_eq13' : Nat.card (Sylow 3 G) = 13 := by
        simpa [n3] using hn3_eq13

      -- All Sylow-3 subgroups have order 81.
      have hcard_sylow3 : ∀ Q : Sylow 3 G, Nat.card (Q : Subgroup G) = 81 := by
        intro Q
        have h := Sylow.card_eq_multiplicity (G := G) (p := 3) Q
        rw [h_card] at h
        simpa [hfac3] using h

      -- Each Sylow-3 subgroup is self-normalizing.
      have hself_norm : ∀ Q : Sylow 3 G, (Q : Subgroup G).normalizer = (Q : Subgroup G) := by
        intro Q
        have hindex : (Q : Subgroup G).normalizer.index = 13 := by
          have h := Sylow.card_eq_index_normalizer (p := 3) (G := G) Q
          exact h.symm.trans hn3_eq13'
        have hcard_norm : Nat.card ((Q : Subgroup G).normalizer) = 81 := by
          have hmul :
              Nat.card ((Q : Subgroup G).normalizer) * ((Q : Subgroup G).normalizer).index =
                Nat.card G :=
            ((Q : Subgroup G).normalizer).card_mul_index
          have hmul' : Nat.card ((Q : Subgroup G).normalizer) * 13 = 1053 := by
            have hmul' := hmul
            rw [hindex, h_card] at hmul'
            simpa using hmul'
          have hmul'' : Nat.card ((Q : Subgroup G).normalizer) * 13 = 81 * 13 := by
            simpa using hmul'.trans (by decide : (1053 : ℕ) = 81 * 13)
          exact Nat.mul_right_cancel (by decide : 0 < 13) hmul''
        have hle : (Q : Subgroup G) ≤ (Q : Subgroup G).normalizer := Subgroup.le_normalizer
        have hcard_le : Nat.card ((Q : Subgroup G).normalizer) ≤ Nat.card (Q : Subgroup G) := by
          exact le_of_eq (hcard_norm.trans (hcard_sylow3 Q).symm)
        exact
          (Subgroup.eq_of_le_of_card_ge (H := (Q : Subgroup G)) (K := (Q : Subgroup G).normalizer)
              hle hcard_le).symm

      -- Fixed points for the `P`-action on Sylow-3 subgroups are exactly `{P}`.
      have hfixed :
          MulAction.fixedPoints (↥(P : Subgroup G)) (Sylow 3 G) = {P} := by
        ext Q
        constructor
        · intro hQ
          have hle : (P : Subgroup G) ≤ (Q : Subgroup G).normalizer := by
            simpa using
              (Subgroup.sylow_mem_fixedPoints_iff (H := (P : Subgroup G)) (P := Q)).1 hQ
          have hPQ : (P : Subgroup G) ≤ (Q : Subgroup G) := by
            simpa [hself_norm Q] using hle
          have hcard_le : Nat.card (Q : Subgroup G) ≤ Nat.card (P : Subgroup G) := by
            exact le_of_eq ((hcard_sylow3 Q).trans (hcard_sylow3 P).symm)
          have hPQ' : (P : Subgroup G) = (Q : Subgroup G) :=
            Subgroup.eq_of_le_of_card_ge hPQ hcard_le
          have hQP : Q = P := (Sylow.ext hPQ'.symm)
          simp [hQP]
        · intro hQ
          have hQ' : Q = P := by
            simpa using hQ
          have hle : (P : Subgroup G) ≤ (P : Subgroup G).normalizer := Subgroup.le_normalizer
          have hPfixed :
              P ∈ MulAction.fixedPoints (↥(P : Subgroup G)) (Sylow 3 G) := by
            simpa using
              (Subgroup.sylow_mem_fixedPoints_iff (H := (P : Subgroup G)) (P := P)).2 hle
          simpa [hQ'] using hPfixed

      -- Decompose the Sylow-3 subgroups into `P`-orbits.
      let Ω := Quotient (MulAction.orbitRel (↥(P : Subgroup G)) (Sylow 3 G))
      let orbitSize : Ω → ℕ :=
        fun ω =>
          Fintype.card
            (MulAction.orbitRel.Quotient.orbit (G := (↥(P : Subgroup G))) (α := Sylow 3 G) ω).Elem
      have hsum : Fintype.card (Sylow 3 G) = ∑ ω : Ω, orbitSize ω := by
        classical
        simpa [orbitSize, Fintype.card_sigma] using
          (Fintype.card_congr
            (MulAction.selfEquivSigmaOrbits' (G := (↥(P : Subgroup G))) (α := (Sylow 3 G))))

      have hPgroup : IsPGroup 3 (↥(P : Subgroup G)) := by
        refine IsPGroup.of_card (p := 3) (G := (↥(P : Subgroup G))) (n := 4) ?_
        -- `P` has order `3^4`.
        have hcardP' : Nat.card (↥(P : Subgroup G)) = 81 := by
          simpa using hcardP
        calc
          Nat.card (↥(P : Subgroup G)) = 81 := hcardP'
          _ = 3 ^ 4 := by decide

      have horbit_pow : ∀ ω : Ω, ∃ n : ℕ, orbitSize ω = 3 ^ n := by
        intro ω
        rcases
            (IsPGroup.card_orbit (p := 3) (G := (↥(P : Subgroup G))) hPgroup
              (α := Sylow 3 G) (a := ω.out))
          with ⟨n, hn⟩
        refine ⟨n, ?_⟩
        have horbit_eq :
            MulAction.orbitRel.Quotient.orbit (G := (↥(P : Subgroup G))) (α := Sylow 3 G) ω =
              MulAction.orbit (↥(P : Subgroup G)) ω.out := by
          simpa using
            (MulAction.orbitRel.Quotient.orbit_eq_orbit_out (G := (↥(P : Subgroup G)))
              (α := Sylow 3 G) (x := ω) Quotient.out_eq')
        simpa [orbitSize, horbit_eq, Nat.card_eq_fintype_card] using hn

      let ω0 : Ω := Quotient.mk'' P
      have horbitP : orbitSize ω0 = 1 := by
        have hfix : P ∈ MulAction.fixedPoints (↥(P : Subgroup G)) (Sylow 3 G) := by
          simp [hfixed]
        have hfix_orbit :=
          (MulAction.mem_fixedPoints_iff_card_orbit_eq_one (M := (↥(P : Subgroup G))) (a := P)).1
            hfix
        simpa [orbitSize, ω0] using hfix_orbit

      have horbit_one_iff : ∀ ω : Ω, orbitSize ω = 1 → ω = ω0 := by
        intro ω hω
        have hfix : ω.out ∈ MulAction.fixedPoints (↥(P : Subgroup G)) (Sylow 3 G) := by
          have hfix_orbit :
              Fintype.card (MulAction.orbit (↥(P : Subgroup G)) ω.out).Elem = 1 := by
            have horbit_eq :
                MulAction.orbitRel.Quotient.orbit (G := (↥(P : Subgroup G))) (α := Sylow 3 G) ω =
                  MulAction.orbit (↥(P : Subgroup G)) ω.out := by
              simpa using
                (MulAction.orbitRel.Quotient.orbit_eq_orbit_out (G := (↥(P : Subgroup G)))
                  (α := Sylow 3 G) (x := ω) Quotient.out_eq')
            simpa [orbitSize, horbit_eq] using hω
          exact
            (MulAction.mem_fixedPoints_iff_card_orbit_eq_one (M := (↥(P : Subgroup G))) (a := ω.out)).2
              hfix_orbit
        have hfix' : ω.out ∈ ({P} : Set (Sylow 3 G)) := by
          simpa [hfixed] using hfix
        have hωout : ω.out = P := by simpa using hfix'
        have hωeq : ω = Quotient.mk'' ω.out := by
          symm
          simp
        simpa [ω0, hωout] using hωeq

      -- There exists an orbit of size 3.
      have h_orbit3 : ∃ ω : Ω, orbitSize ω = 3 := by
        classical
        by_contra hno
        have hdiv9 : ∀ ω : Ω, ω ≠ ω0 → orbitSize ω ≡ 0 [MOD 9] := by
          intro ω hne
          rcases horbit_pow ω with ⟨n, hn⟩
          cases n with
          | zero =>
              have hω1 : orbitSize ω = 1 := by simpa using hn
              exact (hne (horbit_one_iff ω hω1)).elim
          | succ n =>
              cases n with
              | zero =>
                  have hω3 : orbitSize ω = 3 := by simpa using hn
                  exact (hno ⟨ω, hω3⟩).elim
              | succ n =>
                  have hdiv : 9 ∣ orbitSize ω := by
                    have hpow : orbitSize ω = 3 ^ (Nat.succ (Nat.succ n)) := by
                      simpa using hn
                    have hpow' : 3 ^ (Nat.succ (Nat.succ n)) = 3 ^ n * 9 := by
                      calc
                        3 ^ (Nat.succ (Nat.succ n)) = 3 ^ (n + 2) := by
                          simp [Nat.succ_eq_add_one, Nat.add_assoc]
                        _ = 3 ^ n * 3 ^ 2 := by
                          simpa using (pow_add 3 n 2)
                        _ = 3 ^ n * 9 := by simp
                    rw [hpow, hpow']
                    exact dvd_mul_left 9 (3 ^ n)
                  exact (Nat.modEq_zero_iff_dvd).2 hdiv
        have hsum_mod : (∑ ω : Ω, orbitSize ω) ≡ orbitSize ω0 [MOD 9] := by
          classical
          have ha : ω0 ∉ (Finset.univ : Finset Ω) → orbitSize ω0 ≡ 0 [MOD 9] := by
            intro h
            simp at h
          have hf : ∀ ω ∈ (Finset.univ : Finset Ω), ω ≠ ω0 → orbitSize ω ≡ 0 [MOD 9] := by
            intro ω hω hne
            exact hdiv9 ω hne
          have hsum_mod' :=
            Nat.sum_modEq_single (s := (Finset.univ : Finset Ω)) (a := ω0) (f := orbitSize) (n := 9)
              ha hf
          simpa using hsum_mod'
        have hsum_mod' : (∑ ω : Ω, orbitSize ω) ≡ 1 [MOD 9] := by
          simpa [horbitP] using hsum_mod
        have hcard_sylow3' : Fintype.card (Sylow 3 G) = 13 := by
          simpa [Nat.card_eq_fintype_card] using hn3_eq13'
        have hcontr : (13 : ℕ) ≡ 1 [MOD 9] := by
          have hsum' : ∑ ω : Ω, orbitSize ω = Fintype.card (Sylow 3 G) := hsum.symm
          simpa [hsum', hcard_sylow3'] using hsum_mod'
        exact (by decide : ¬ ((13 : ℕ) ≡ 1 [MOD 9])) hcontr

      -- Choose `Q` from the orbit of size 3 and set `I = P ⊓ Q`.
      rcases h_orbit3 with ⟨ω, hω⟩
      let Q : Sylow 3 G := ω.out
      have hQorbit :
          Fintype.card (MulAction.orbit (↥(P : Subgroup G)) Q).Elem = 3 := by
        have horbit_eq :
            MulAction.orbitRel.Quotient.orbit (G := (↥(P : Subgroup G))) (α := Sylow 3 G) ω =
              MulAction.orbit (↥(P : Subgroup G)) ω.out := by
          simpa using
            (MulAction.orbitRel.Quotient.orbit_eq_orbit_out (G := (↥(P : Subgroup G)))
              (α := Sylow 3 G) (x := ω) Quotient.out_eq')
        simpa [orbitSize, horbit_eq, Q] using hω
      let I : Subgroup G := (P : Subgroup G) ⊓ (Q : Subgroup G)
      -- The stabilizer of `Q` in `P` is `I`, giving index 3.
      have hstab :
          (MulAction.stabilizer (↥(P : Subgroup G)) Q) =
            (I.subgroupOf (P : Subgroup G)) := by
        ext g
        constructor
        · intro hg
          -- Use the stabilizer characterization and self-normalizing property.
          have hg' :
              ((g : ↥(P : Subgroup G)) : G) ∈ (Q : Subgroup G).normalizer := by
            -- `g` stabilizes `Q`, so it normalizes `Q`.
            have := (MulAction.mem_stabilizer_iff (G := (↥(P : Subgroup G))) (a := Q) (g := g)).1 hg
            -- `Sylow.smul_eq_iff_mem_normalizer` relates the action to the normalizer.
            simpa using (Sylow.smul_eq_iff_mem_normalizer (g := (g : G)) (P := Q)).1 this
          have hgP : (g : G) ∈ (P : Subgroup G) := g.property
          have hgQ : (g : G) ∈ (Q : Subgroup G) := by
            simpa [hself_norm Q] using hg'
          exact ⟨hgP, hgQ⟩
        · intro hg
          have hgQ : (g : G) ∈ (Q : Subgroup G) := hg.2
          -- Elements of `I` normalize `Q`, hence fix `Q`.
          have hg' : ((g : ↥(P : Subgroup G)) : G) ∈ (Q : Subgroup G).normalizer := by
            simpa [hself_norm Q] using hgQ
          have hfix :
              (g : ↥(P : Subgroup G)) • Q = Q := by
            simpa using (Sylow.smul_eq_iff_mem_normalizer (g := (g : G)) (P := Q)).2 hg'
          exact (MulAction.mem_stabilizer_iff (G := (↥(P : Subgroup G))) (a := Q) (g := g)).2 hfix

      have hindexI : (I.subgroupOf (P : Subgroup G)).index = 3 := by
        have hindex_orbit :
            (MulAction.stabilizer (↥(P : Subgroup G)) Q).index =
              Fintype.card (MulAction.orbit (↥(P : Subgroup G)) Q).Elem := by
          have h :=
            Nat.card_congr
              (MulAction.orbitEquivQuotientStabilizer (α := (↥(P : Subgroup G))) (b := Q))
          have h' :
              Nat.card (MulAction.orbit (↥(P : Subgroup G)) Q).Elem =
                (MulAction.stabilizer (↥(P : Subgroup G)) Q).index := by
            simpa [Subgroup.index] using h
          simpa [Nat.card_eq_fintype_card] using h'.symm
        -- Rewrite the stabilizer to `I`, then use the orbit size.
        have hindex_orbit' :
            (I.subgroupOf (P : Subgroup G)).index =
              Fintype.card (MulAction.orbit (↥(P : Subgroup G)) Q).Elem := by
          simpa [hstab] using hindex_orbit
        simpa [hQorbit] using hindex_orbit'

      -- Compute `|I| = 27`.
      have hcardI_sub : Nat.card (I.subgroupOf (P : Subgroup G)) = 27 := by
        have hmul :
            Nat.card (I.subgroupOf (P : Subgroup G)) * (I.subgroupOf (P : Subgroup G)).index =
              Nat.card (P : Subgroup G) :=
          (I.subgroupOf (P : Subgroup G)).card_mul_index
        have hmul' : Nat.card (I.subgroupOf (P : Subgroup G)) * 3 = 81 := by
          have hmul' := hmul
          rw [hindexI, hcardP] at hmul'
          simpa using hmul'
        have hmul'' : Nat.card (I.subgroupOf (P : Subgroup G)) * 3 = 27 * 3 := by
          simpa using hmul'.trans (by decide : (81 : ℕ) = 27 * 3)
        exact Nat.mul_right_cancel (by decide : 0 < 3) hmul''

      have hcardI : Nat.card I = 27 := by
        have hle : I ≤ (P : Subgroup G) := by
          intro x hx
          exact hx.1
        have hcard_eq :
            Nat.card (I.subgroupOf (P : Subgroup G)) = Nat.card I := by
          classical
          simpa [Nat.card_eq_fintype_card] using
            (Fintype.card_congr (Subgroup.subgroupOfEquivOfLe hle))
        exact hcard_eq ▸ hcardI_sub

      -- `I` is normal in `P` and in `Q`, hence normal in `G`.
      have hI_normal_P : (I.subgroupOf (P : Subgroup G)).Normal := by
        have hminfac : (Fintype.card (↥(P : Subgroup G))).minFac = 3 := by
          -- `|P| = 3^4` so the minimal prime factor is 3.
          have hcardP' : Fintype.card (↥(P : Subgroup G)) = 81 := by
            simpa [Nat.card_eq_fintype_card] using hcardP
          simpa [hcardP'] using (by native_decide : (81 : ℕ).minFac = 3)
        have hindex' : (I.subgroupOf (P : Subgroup G)).index = (Nat.card (↥(P : Subgroup G))).minFac := by
          simpa [Nat.card_eq_fintype_card, hminfac] using hindexI
        exact Subgroup.normal_of_index_eq_minFac_card hindex'

      have hP_le_norm : (P : Subgroup G) ≤ I.normalizer := by
        have hle : I ≤ (P : Subgroup G) := by
          intro x hx
          exact hx.1
        have hnorm :
            (I.subgroupOf (P : Subgroup G)).Normal := hI_normal_P
        simpa using
          (Subgroup.normal_subgroupOf_iff_le_normalizer (H := I) (K := (P : Subgroup G)) hle).1
            hnorm

      have hI_normal_Q : (I.subgroupOf (Q : Subgroup G)).Normal := by
        have hle : I ≤ (Q : Subgroup G) := by
          intro x hx
          exact hx.2
        have hcardI_Q : Nat.card (I.subgroupOf (Q : Subgroup G)) = 27 := by
          have hcard_eq :
              Nat.card (I.subgroupOf (Q : Subgroup G)) = Nat.card I := by
            classical
            simpa using (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv)
          calc
            Nat.card (I.subgroupOf (Q : Subgroup G)) = Nat.card I := hcard_eq
            _ = 27 := hcardI
        have hindexQ : (I.subgroupOf (Q : Subgroup G)).index = 3 := by
          have hmul :
              Nat.card (I.subgroupOf (Q : Subgroup G)) * (I.subgroupOf (Q : Subgroup G)).index =
                Nat.card (Q : Subgroup G) :=
            (I.subgroupOf (Q : Subgroup G)).card_mul_index
          have hmul' : 27 * (I.subgroupOf (Q : Subgroup G)).index = 81 := by
            have hmul' := hmul
            rw [hcardI_Q, hcard_sylow3 Q] at hmul'
            simpa using hmul'
          have hmul'' : 27 * (I.subgroupOf (Q : Subgroup G)).index = 27 * 3 := by
            simpa using hmul'.trans (by decide : (81 : ℕ) = 27 * 3)
          exact Nat.mul_left_cancel (by decide : 0 < 27) hmul''
        have hminfac : (Nat.card (↥(Q : Subgroup G))).minFac = 3 := by
          have hcardQ' : Nat.card (↥(Q : Subgroup G)) = 81 := by
            simpa using hcard_sylow3 Q
          rw [hcardQ']
          exact (by native_decide : (81 : ℕ).minFac = 3)
        have hindex' : (I.subgroupOf (Q : Subgroup G)).index = (Nat.card (↥(Q : Subgroup G))).minFac := by
          exact hindexQ.trans hminfac.symm
        exact Subgroup.normal_of_index_eq_minFac_card hindex'

      have hQ_le_norm : (Q : Subgroup G) ≤ I.normalizer := by
        have hle : I ≤ (Q : Subgroup G) := by
          intro x hx
          exact hx.2
        have hnorm :
            (I.subgroupOf (Q : Subgroup G)).Normal := hI_normal_Q
        simpa using
          (Subgroup.normal_subgroupOf_iff_le_normalizer (H := I) (K := (Q : Subgroup G)) hle).1
            hnorm

      have hsup_eq_top : (P : Subgroup G) ⊔ (Q : Subgroup G) = ⊤ := by
        -- First note that `Q ≠ P` since its orbit has size 3.
        have hQ_ne_P : Q ≠ P := by
          intro hQP
          have hPorbit :
              Fintype.card (MulAction.orbit (↥(P : Subgroup G)) P).Elem = 1 := by
            simpa [orbitSize, ω0] using horbitP
          have hQorbit' :
              Fintype.card (MulAction.orbit (↥(P : Subgroup G)) P).Elem = 3 := by
            simpa [hQP] using hQorbit
          exact (by decide : (1 : ℕ) ≠ 3) (hPorbit.symm.trans hQorbit')

        -- Let `H = P ⊔ Q`; its order is a multiple of `81` dividing `1053`.
        let H : Subgroup G := (P : Subgroup G) ⊔ (Q : Subgroup G)
        have hcardH_dvd : Nat.card H ∣ Nat.card G :=
          Subgroup.card_subgroup_dvd_card H
        have hcardP_dvd : Nat.card (P : Subgroup G) ∣ Nat.card H := by
          exact Subgroup.card_dvd_of_le (show (P : Subgroup G) ≤ H from le_sup_left)
        rcases hcardP_dvd with ⟨d, hd⟩
        have hdvd : d ∣ 13 := by
          have hdiv' := hcardH_dvd
          rw [h_card] at hdiv'
          have h1053 : (1053 : ℕ) = 81 * 13 := by decide
          rw [h1053] at hdiv'
          rw [hd, hcardP] at hdiv'
          exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 81) hdiv'
        rcases (Nat.dvd_prime (by decide : Nat.Prime 13)).1 hdvd with rfl | rfl
        · -- If `d = 1`, then `H` has order 81, hence equals `P`, contradicting `Q ≠ P`.
          have hHcard : Nat.card H = 81 := by
            calc
              Nat.card H = Nat.card (P : Subgroup G) * 1 := hd
              _ = Nat.card (P : Subgroup G) := by simp
              _ = 81 := hcardP
          have hle : (P : Subgroup G) ≤ H := le_sup_left
          have hcard_le : Nat.card H ≤ Nat.card (P : Subgroup G) := by
            exact le_of_eq (hHcard.trans hcardP.symm)
          have hH_eq : (P : Subgroup G) = H :=
            Subgroup.eq_of_le_of_card_ge hle hcard_le
          have hQle : (Q : Subgroup G) ≤ (P : Subgroup G) := by
            have hQleH : (Q : Subgroup G) ≤ H := le_sup_right
            rw [← hH_eq] at hQleH
            exact hQleH
          have hQP : (Q : Subgroup G) = (P : Subgroup G) :=
            Subgroup.eq_of_le_of_card_ge hQle (by
              exact le_of_eq (hcardP.trans (hcard_sylow3 Q).symm))
          exact (hQ_ne_P (Sylow.ext hQP)).elim
        · -- If `d = 13`, then `H` has order 1053 and hence equals `⊤`.
          have hHcard : Nat.card H = 1053 := by
            calc
              Nat.card H = Nat.card (P : Subgroup G) * 13 := hd
              _ = 81 * 13 := by
                rw [hcardP]
              _ = 1053 := by decide
          have hHcard' : Nat.card H = Nat.card G := by
            rw [h_card]
            exact hHcard
          exact (Subgroup.card_eq_iff_eq_top (H := H)).1 hHcard'

      have hnorm_top : I.normalizer = ⊤ := by
        have hsup_le : (P : Subgroup G) ⊔ (Q : Subgroup G) ≤ I.normalizer :=
          sup_le hP_le_norm hQ_le_norm
        simpa [hsup_eq_top] using hsup_le

      have hInormal : I.Normal := by
        -- `normalizer = ⊤` is equivalent to normality.
        exact (Subgroup.normalizer_eq_top_iff).1 hnorm_top

      -- `I` is a proper nontrivial normal subgroup of order 27.
      rcases hsimple I hInormal with hbot | htop
      · have hcardI' : (1 : ℕ) = 27 := by
          have hcardI' := hcardI
          simp [hbot] at hcardI'
        exact (by decide : (1 : ℕ) ≠ 27) hcardI'
      · have htop' := hcardI
        rw [htop] at htop'
        have hG27 : Nat.card G = 27 := (Subgroup.card_top (G := G)).symm.trans htop'
        rw [h_card] at hG27
        exact (by decide : (1053 : ℕ) ≠ 27) hG27

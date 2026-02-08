import Mathlib

/-!
This file contains a small-group-theory exercise: no group of order `56 = 2^3 * 7` is simple.

We use Sylow counting to reduce to two cases for the number of Sylow-7 subgroups; in the
`n₇ = 8` case we apply Burnside's transfer (normal `p`-complement) theorem from mathlib.
-/

/-- If `n ∣ 8` and `n ≡ 1 [MOD 7]`, then `n = 1` or `n = 8`. -/
private lemma nat_eq_one_or_eight_of_dvd_eight_of_modEq_one (n : ℕ) (hn : n ∣ 8)
    (hmod : n ≡ 1 [MOD 7]) : n = 1 ∨ n = 8 := by
  have hn_pos : 1 ≤ n := by
    have hn0 : n ≠ 0 := by
      intro hn0
      have : (0 : ℕ) ≡ 1 [MOD 7] := by simpa [hn0] using hmod
      simp [Nat.ModEq] at this
    exact Nat.one_le_iff_ne_zero.mpr hn0
  have hdiv : 7 ∣ n - 1 := (Nat.modEq_iff_dvd' hn_pos).1 hmod.symm
  have hn_le8 : n ≤ 8 := Nat.le_of_dvd (by decide : 0 < 8) hn
  have hsub_le7 : n - 1 ≤ 7 := by
    simpa using Nat.sub_le_sub_right hn_le8 1
  rcases hdiv with ⟨k, hk⟩
  have hk_lt2 : k < 2 := by
    have h7k_le7 : 7 * k ≤ 7 := by simpa [hk] using hsub_le7
    by_contra hkge
    have hkge' : 2 ≤ k := le_of_not_gt hkge
    have h14_le_7k : 14 ≤ 7 * k := by
      have h := Nat.mul_le_mul_left 7 hkge'
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
    have : 14 ≤ 7 := le_trans h14_le_7k h7k_le7
    exact (by decide : ¬ (14 ≤ 7)) this
  have hk_le1 : k ≤ 1 := (Nat.lt_succ_iff).1 (by simpa using hk_lt2)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk_le1 with rfl | rfl
  · left
    calc
      n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
      _ = 0 + 1 := by simp [hk]
      _ = 1 := by simp
  · right
    calc
      n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
      _ = 7 + 1 := by simp [hk]
      _ = 8 := by decide

/- Prove that if $\#G = 56$ then $G$ is not simple.-/
theorem not_isSimpleGroup_of_card_eq_56 {G : Type} [Group G] (hG : Nat.card G = 56) :
    ¬ IsSimpleGroup G := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by simp [hG])
  letI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
  haveI : Finite (Sylow 7 G) := by
    classical
    refine
      Finite.of_injective
        (fun P : Sylow 7 G => ((P : Subgroup G) : Set G).toFinset) ?_
    intro P Q hPQ
    apply Sylow.ext
    ext g
    have : g ∈ (((P : Subgroup G) : Set G).toFinset) ↔ g ∈ (((Q : Subgroup G) : Set G).toFinset) := by
      simp [hPQ]
    simpa [Set.mem_toFinset] using this

  -- Fix a Sylow-7 subgroup `P`.
  let P : Sylow 7 G := Classical.choice (inferInstance : Nonempty (Sylow 7 G))
  have hfac : Nat.factorization 56 7 = 1 := by native_decide
  have hcardP : Nat.card (P : Subgroup G) = 7 := by
    have h := Sylow.card_eq_multiplicity (G := G) (p := 7) P
    -- Avoid rewriting `Nat.card` to `Fintype.card` too early by first rewriting `Nat.card G`.
    rw [hG] at h
    -- Now `simp` can finish the arithmetic.
    simpa [hfac] using h
  have hindexP : (P : Subgroup G).index = 8 := by
    have hmul : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
      (P : Subgroup G).card_mul_index
    have hmul' : 7 * (P : Subgroup G).index = 56 := by
      -- Rewrite `Nat.card` goals directly to avoid fighting simp-normal forms.
      have hmul' := hmul
      rw [hcardP, hG] at hmul'
      simpa using hmul'
    have hmul'' : 7 * (P : Subgroup G).index = 7 * 8 := by
      simpa using hmul'.trans (by decide : 56 = 7 * 8)
    exact Nat.mul_left_cancel (by decide : 0 < 7) hmul''

  -- Let `n₇` be the number of Sylow-7 subgroups. Sylow III gives `n₇ ∣ 8` and `n₇ ≡ 1 [MOD 7]`.
  let n7 : ℕ := Nat.card (Sylow 7 G)
  have hn7_dvd : n7 ∣ 8 := by
    have : n7 ∣ (P : Subgroup G).index := by
      simpa [n7] using (Sylow.card_dvd_index (p := 7) (G := G) P)
    simpa [hindexP] using this
  have hn7_mod : n7 ≡ 1 [MOD 7] := by
    simpa [n7] using (card_sylow_modEq_one (p := 7) (G := G))
  have hn7_cases : n7 = 1 ∨ n7 = 8 :=
    nat_eq_one_or_eight_of_dvd_eight_of_modEq_one n7 hn7_dvd hn7_mod

  intro hS
  have hS' := (isSimpleGroup_iff G).1 hS
  have hsimple :
      ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ :=
    hS'.2

  rcases hn7_cases with hn7_eq1 | hn7_eq8
  · -- If there is a unique Sylow-7 subgroup, it is normal and nontrivial/proper.
    haveI : Subsingleton (Sylow 7 G) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa [n7] using hn7_eq1)).1
    have hPnormal : (P : Subgroup G).Normal := by
      simpa using (Sylow.normal_of_subsingleton (P := P))
    rcases hsimple (P : Subgroup G) hPnormal with hbot | htop
    · have hcardP' := hcardP
      simp [hbot] at hcardP'
    · have htop' := hcardP
      rw [htop] at htop'
      have hG7 : Nat.card G = 7 := (Subgroup.card_top (G := G)).symm.trans htop'
      rw [hG] at hG7
      exact (by decide : (56 : ℕ) ≠ 7) hG7
  · -- If `n₇ = 8`, then `P` is self-normalizing and Burnside transfer gives a normal 7-complement.
    have hnormIndex : (P : Subgroup G).normalizer.index = 8 := by
      have hn7_eq8' : Nat.card (Sylow 7 G) = 8 := by simpa [n7] using hn7_eq8
      exact (Sylow.card_eq_index_normalizer (p := 7) (G := G) P).symm.trans hn7_eq8'
    have hnormCard : Nat.card ((P : Subgroup G).normalizer) = 7 := by
      have hmul :
          Nat.card ((P : Subgroup G).normalizer) * ((P : Subgroup G).normalizer).index =
            Nat.card G :=
        ((P : Subgroup G).normalizer).card_mul_index
      have hmul' : Nat.card ((P : Subgroup G).normalizer) * 8 = 56 := by
        have hmul' := hmul
        rw [hnormIndex, hG] at hmul'
        simpa using hmul'
      have hmul'' : Nat.card ((P : Subgroup G).normalizer) * 8 = 7 * 8 := by
        simpa using hmul'.trans (by decide : 56 = 7 * 8)
      exact Nat.mul_right_cancel (by decide : 0 < 8) hmul''
    have hP_le_norm : (P : Subgroup G) ≤ (P : Subgroup G).normalizer := Subgroup.le_normalizer
    have hnorm_le : Nat.card ((P : Subgroup G).normalizer) ≤ Nat.card (P : Subgroup G) := by
      -- Both sides are `7`.
      exact le_of_eq (hnormCard.trans hcardP.symm)
    have hP_eq_norm : (P : Subgroup G) = (P : Subgroup G).normalizer :=
      Subgroup.eq_of_le_of_card_ge hP_le_norm hnorm_le
    have hnorm_eq : (P : Subgroup G).normalizer = (P : Subgroup G) := hP_eq_norm.symm
    haveI : IsCyclic (P : Subgroup G) :=
      isCyclic_of_prime_card (α := (P : Subgroup G)) (p := 7) hcardP
    have hnorm_le_central :
        (P : Subgroup G).normalizer ≤ Subgroup.centralizer (P : Set G) := by
      have hle : (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) :=
        Subgroup.le_centralizer (H := (P : Subgroup G))
      simpa [hnorm_eq] using hle

    let f : G →* (P : Subgroup G) := MonoidHom.transferSylow (p := 7) P hnorm_le_central
    let K : Subgroup G := f.ker
    have hcomp : Subgroup.IsComplement' K (P : Subgroup G) := by
      simpa [f, K] using (MonoidHom.ker_transferSylow_isComplement' (p := 7) P hnorm_le_central)
    have hKnormal : K.Normal := by
      -- kernels are normal
      simpa [K, f] using (inferInstance : f.ker.Normal)
    have hindexK : K.index = 7 := by
      have hindexK' : K.index = Nat.card (P : Subgroup G) := (hcomp.symm).index_eq_card
      rw [hcardP] at hindexK'
      simpa using hindexK'
    have hcardK : Nat.card K = 8 := by
      have hmul : Nat.card K * K.index = Nat.card G := K.card_mul_index
      have hmul' : Nat.card K * 7 = 56 := by
        have hmul' := hmul
        rw [hindexK, hG] at hmul'
        simpa using hmul'
      have hmul'' : Nat.card K * 7 = 8 * 7 := by
        simpa using hmul'.trans (by decide : 56 = 8 * 7)
      exact Nat.mul_right_cancel (by decide : 0 < 7) hmul''
    rcases hsimple K hKnormal with hbot | htop
    · have hcardK' := hcardK
      simp [hbot] at hcardK'
    · have htop' := hcardK
      rw [htop] at htop'
      have hG8 : Nat.card G = 8 := (Subgroup.card_top (G := G)).symm.trans htop'
      rw [hG] at hG8
      exact (by decide : (56 : ℕ) ≠ 8) hG8

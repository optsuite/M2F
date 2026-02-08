import Mathlib

/-- The Sylow `p`-subgroups form a finite type when `G` is finite. -/
private lemma finite_sylow_of_finite (p : ℕ) (G : Type) [Group G] [Finite G] :
    Finite (Sylow p G) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  refine
    Finite.of_injective
      (fun P : Sylow p G => ((P : Subgroup G) : Set G).toFinset) ?_
  intro P Q hPQ
  apply Sylow.ext
  ext g
  have :
      g ∈ (((P : Subgroup G) : Set G).toFinset) ↔
        g ∈ (((Q : Subgroup G) : Set G).toFinset) := by
    simp [hPQ]
  simpa [Set.mem_toFinset] using this

/-- If `n ∣ p+1` and `n ≡ 1 [MOD p]`, then `n = 1` or `n = p+1`. -/
private lemma nat_eq_one_or_eq_add_one_of_dvd_add_one_of_modEq_one {p n : ℕ} (hp : p.Prime)
    (hn : n ∣ p + 1) (hmod : n ≡ 1 [MOD p]) : n = 1 ∨ n = p + 1 := by
  have hn0 : n ≠ 0 := by
    intro h0
    rcases hn with ⟨k, hk⟩
    have : (p + 1 : ℕ) = 0 := by
      simp [h0] at hk
    exact Nat.succ_ne_zero p this
  have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hdiv : p ∣ n - 1 := (Nat.modEq_iff_dvd' hn_pos).1 hmod.symm
  have hn_le : n ≤ p + 1 := Nat.le_of_dvd (Nat.succ_pos _) hn
  have hsub_le : n - 1 ≤ p := by
    simpa using Nat.sub_le_sub_right hn_le 1
  rcases hdiv with ⟨k, hk⟩
  have hk_le1 : k ≤ 1 := by
    have hpk_le_p : p * k ≤ p := by
      simpa [hk] using hsub_le
    have hp_pos : 0 < p := hp.pos
    have hpk_le_p1 : p * k ≤ p * 1 := by
      simpa using hpk_le_p
    exact Nat.le_of_mul_le_mul_left hpk_le_p1 hp_pos
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk_le1 with rfl | rfl
  · left
    calc
      n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
      _ = 0 + 1 := by simp [hk]
      _ = 1 := by simp
  · right
    calc
      n = (n - 1) + 1 := (Nat.sub_add_cancel hn_pos).symm
      _ = p + 1 := by simp [hk]

/-- The number of Sylow `p`-subgroups is `p+1` under the non-normality hypothesis. -/
private lemma card_sylow_eq_add_one (p : ℕ) (G : Type) [Group G] [Finite G] (hp : p.Prime)
    (h_card : Nat.card G = p * (p + 1)) (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) :
    Nat.card (Sylow p G) = p + 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Sylow p G) := finite_sylow_of_finite (p := p) (G := G)
  let P : Sylow p G := Classical.choice (inferInstance : Nonempty (Sylow p G))
  have hindex_dvd : P.index ∣ p + 1 := by
    have hmul : Nat.card (P : Subgroup G) * P.index = Nat.card G :=
      (P : Subgroup G).card_mul_index
    have hindex_dvd' : P.index ∣ Nat.card G := by
      refine ⟨Nat.card (P : Subgroup G), ?_⟩
      rw [Nat.mul_comm]
      exact hmul.symm
    have hindex_dvd'' : P.index ∣ p * (p + 1) := by
      simpa [h_card] using hindex_dvd'
    have hnot : ¬ p ∣ P.index := by
      haveI : P.FiniteIndex := inferInstance
      exact (Sylow.not_dvd_index (P := P))
    have hcop : Nat.Coprime p P.index := (hp.coprime_iff_not_dvd).2 hnot
    exact (hcop.symm.dvd_of_dvd_mul_left hindex_dvd'')
  let n : ℕ := Nat.card (Sylow p G)
  have hn_dvd : n ∣ p + 1 := by
    have : n ∣ P.index := by
      simpa [n] using (Sylow.card_dvd_index (p := p) (G := G) P)
    exact this.trans hindex_dvd
  have hn_mod : n ≡ 1 [MOD p] := by
    simpa [n] using (card_sylow_modEq_one (p := p) (G := G))
  have hn_cases : n = 1 ∨ n = p + 1 :=
    nat_eq_one_or_eq_add_one_of_dvd_add_one_of_modEq_one hp hn_dvd hn_mod
  rcases hn_cases with hn1 | hn1
  · exfalso
    haveI : Subsingleton (Sylow p G) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa [n] using hn1)).1
    have hPnormal : (P : Subgroup G).Normal := by
      simpa using (Sylow.normal_of_subsingleton (P := P))
    exact (h_sylow P) hPnormal
  · simpa [n] using hn1

/-- A Sylow subgroup of index `p+1` is self-normalizing and has order `p`. -/
private lemma normalizer_eq_self_of_card (p : ℕ) (G : Type) [Group G] [Finite G] (hp : p.Prime)
    (h_card : Nat.card G = p * (p + 1)) (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal)
    (P : Sylow p G) :
    (P : Subgroup G).normalizer = (P : Subgroup G) ∧ Nat.card (P : Subgroup G) = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Sylow p G) := finite_sylow_of_finite (p := p) (G := G)
  have hcard_sylow : Nat.card (Sylow p G) = p + 1 :=
    card_sylow_eq_add_one (p := p) (G := G) hp h_card h_sylow
  have hnormIndex : (P : Subgroup G).normalizer.index = p + 1 := by
    exact (Sylow.card_eq_index_normalizer (p := p) (G := G) P).symm.trans hcard_sylow
  have hnormCard : Nat.card ((P : Subgroup G).normalizer) = p := by
    have hmul :
        Nat.card ((P : Subgroup G).normalizer) * ((P : Subgroup G).normalizer).index =
          Nat.card G :=
      ((P : Subgroup G).normalizer).card_mul_index
    have hmul' : Nat.card ((P : Subgroup G).normalizer) * (p + 1) = p * (p + 1) := by
      simpa [hnormIndex, h_card] using hmul
    exact Nat.mul_right_cancel (Nat.succ_pos _) hmul'
  have hP_le_norm : (P : Subgroup G) ≤ (P : Subgroup G).normalizer := Subgroup.le_normalizer
  have hpdvd : p ∣ Nat.card G := by
    simp [h_card]
  have hpdvdP : p ∣ Nat.card (P : Subgroup G) := P.dvd_card_of_dvd_card hpdvd
  have hp_le : p ≤ Nat.card (P : Subgroup G) := Nat.le_of_dvd (Nat.card_pos) hpdvdP
  have hnorm_le : Nat.card ((P : Subgroup G).normalizer) ≤ Nat.card (P : Subgroup G) := by
    simpa [hnormCard] using hp_le
  have hP_eq_norm :
      (P : Subgroup G) = (P : Subgroup G).normalizer :=
    Subgroup.eq_of_le_of_card_ge hP_le_norm hnorm_le
  have hnorm_eq : (P : Subgroup G).normalizer = (P : Subgroup G) := hP_eq_norm.symm
  have hcardP : Nat.card (P : Subgroup G) = p := by
    simpa [hnorm_eq] using hnormCard
  exact ⟨hnorm_eq, hcardP⟩

/-- Burnside transfer gives a normal complement of order `p+1`. -/
private lemma exists_normal_complement_of_normalizer_le_centralizer (p : ℕ) (G : Type)
    [Group G] [Finite G] (hp : p.Prime) (h_card : Nat.card G = p * (p + 1))
    (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) (P : Sylow p G) :
    ∃ K : Subgroup G, K.Normal ∧ Subgroup.IsComplement' K (P : Subgroup G) ∧
      Nat.card K = p + 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Sylow p G) := finite_sylow_of_finite (p := p) (G := G)
  obtain ⟨hnorm_eq, hcardP⟩ :=
    normalizer_eq_self_of_card (p := p) (G := G) hp h_card h_sylow P
  haveI : IsCyclic (P : Subgroup G) :=
    isCyclic_of_prime_card (α := (P : Subgroup G)) (p := p) hcardP
  have hnorm_le_central :
      (P : Subgroup G).normalizer ≤ Subgroup.centralizer (P : Set G) := by
    have hle : (P : Subgroup G) ≤ Subgroup.centralizer (P : Set G) :=
      Subgroup.le_centralizer (H := (P : Subgroup G))
    simpa [hnorm_eq] using hle
  let f : G →* (P : Subgroup G) := MonoidHom.transferSylow (p := p) P hnorm_le_central
  let K : Subgroup G := f.ker
  have hcomp : Subgroup.IsComplement' K (P : Subgroup G) := by
    simpa [f, K] using (MonoidHom.ker_transferSylow_isComplement' (p := p) P hnorm_le_central)
  have hKnormal : K.Normal := by
    simpa [K, f] using (inferInstance : f.ker.Normal)
  have hindexK : K.index = p := by
    have hindexK' : K.index = Nat.card (P : Subgroup G) := (hcomp.symm).index_eq_card
    rw [hcardP] at hindexK'
    simpa using hindexK'
  have hcardK : Nat.card K = p + 1 := by
    have hmul : Nat.card K * K.index = Nat.card G := K.card_mul_index
    have hmul' : Nat.card K * p = p * (p + 1) := by
      simpa [hindexK, h_card, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    have hmul'' : Nat.card K * p = (p + 1) * p := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul'
    exact Nat.mul_right_cancel hp.pos hmul''
  exact ⟨K, hKnormal, hcomp, hcardK⟩

/-- A finite `2`-group has cardinality a power of `2`. -/
private lemma card_eq_two_pow_of_isPGroup (K : Type) [Group K] [Finite K]
    (hK : IsPGroup 2 K) : ∃ n, Nat.card K = 2 ^ n := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simpa using (IsPGroup.iff_card (p := 2) (G := K)).1 hK

/-- If every nontrivial element has order `2`, then the group is a `2`-group. -/
private lemma isPGroup_two_of_forall_orderOf_eq_two (K : Type) [Group K]
    (h : ∀ k : K, k ≠ 1 → orderOf k = 2) : IsPGroup 2 K := by
  intro k
  by_cases hk : k = 1
  · subst hk
    refine ⟨0, ?_⟩
    simp
  · refine ⟨1, ?_⟩
    have hk' : orderOf k = 2 := h k hk
    simpa [hk'] using (pow_orderOf_eq_one k)

/-- If `p+1` has a unique nontrivial divisor `2`, then elements with order dividing `p+1` have order `2`. -/
private lemma orderOf_eq_two_of_dvd_add_one_of_divisor_unique {p : ℕ} {K : Type} [Group K]
    (k : K) (hkdiv : orderOf k ∣ p + 1) (hkne1 : orderOf k ≠ 1)
    (huniq : ∀ d, d ∣ p + 1 → d ≠ 1 → d = 2) : orderOf k = 2 := by
  exact huniq _ hkdiv hkne1

/-- A natural number different from `0` and `1` is at least `2`. -/
private lemma two_le_of_ne_zero_ne_one {d : ℕ} (h0 : d ≠ 0) (h1 : d ≠ 1) : 2 ≤ d := by
  have hpos : 0 < d := Nat.pos_of_ne_zero h0
  have hge1 : 1 ≤ d := (Nat.succ_le_iff).2 hpos
  have hgt1 : 1 < d := lt_of_le_of_ne hge1 (Ne.symm h1)
  exact (Nat.succ_le_iff).2 hgt1

/-- If `d ∣ p+1` and `2 < d`, then either `4` divides `p+1` or an odd prime divides `p+1`. -/
private lemma four_dvd_or_exists_odd_prime_dvd_of_dvd_add_one_of_two_lt {p d : ℕ}
    (hdv : d ∣ p + 1) (hgt2 : 2 < d) :
    4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q := by
  have hcases :=
    (Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt (n := d) hgt2)
  rcases hcases with hfour | hprime
  · left
    exact dvd_trans hfour hdv
  · right
    rcases hprime with ⟨q, hqprime, hqdv, hqodd⟩
    exact ⟨q, hqprime, dvd_trans hqdv hdv, hqodd⟩

/-- For an odd prime `p`, either `4 ∣ p+1` or an odd prime divides `p+1`. -/
private lemma four_dvd_or_exists_odd_prime_dvd_add_one_of_odd_prime {p : ℕ}
    (h_odd : Odd p) (hp : p.Prime) :
    4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q := by
  rcases h_odd with ⟨k, hk⟩
  have hp1 : p + 1 = 2 * (k + 1) := by
    simp [hk]
    ring
  by_cases hfour : 4 ∣ p + 1
  · exact Or.inl hfour
  · have hk1 : k + 1 ≠ 1 := by
      intro hk1
      have hk0 : k = 0 := by
        have : Nat.succ k = Nat.succ 0 := by simpa using hk1
        exact Nat.succ_injective this
      have : p = 1 := by
        simp [hk, hk0]
      exact hp.ne_one this
    have hnot2 : ¬ 2 ∣ k + 1 := by
      intro h2
      have hfour' : 4 ∣ p + 1 := by
        have hfour'' : 4 ∣ 2 * (k + 1) := by
          have hmul : 2 * 2 ∣ 2 * (k + 1) := Nat.mul_dvd_mul_left 2 h2
          simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
        simpa [hp1] using hfour''
      exact hfour hfour'
    rcases Nat.exists_prime_and_dvd hk1 with ⟨q, hqprime, hqdv⟩
    have hqne2 : q ≠ 2 := by
      intro hq2
      have : 2 ∣ k + 1 := by simpa [hq2] using hqdv
      exact hnot2 this
    have hqodd : Odd q := Nat.Prime.odd_of_ne_two hqprime hqne2
    have hqdv' : q ∣ p + 1 := by
      have hqdv'' : q ∣ 2 * (k + 1) := dvd_mul_of_dvd_right hqdv 2
      simpa [hp1] using hqdv''
    exact Or.inr ⟨q, hqprime, hqdv', hqodd⟩

/-- The disjunction about divisors of `p+1` is consistent (e.g. at `p = 3`). -/
private lemma disjunction_holds_p_eq_three :
    4 ∣ (3 : ℕ) + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ (3 : ℕ) + 1 ∧ Odd q := by
  left
  simp

/-- If the disjunction is false, any proof of it yields a contradiction. -/
private lemma no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_aux {p : ℕ}
    (hno : ¬ (4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q))
    (hcases : 4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q) : False := by
  exact hno hcases

/-- The disjunction about divisors of `p+1` is impossible when `p = 0`. -/
private lemma no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_pos_p_zero {p : ℕ} (hp : p = 0)
    (hcases : 4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q) : False := by
  subst hp
  rcases hcases with hfour | ⟨q, hqprime, hqdv, hqodd⟩
  · have hfour' : (4 : ℕ) = 1 := (Nat.dvd_one.mp hfour)
    have hcontra : (4 : ℕ) ≠ 1 := by decide
    exact hcontra hfour'
  · have hqdv' : q ∣ (1 : ℕ) := by
      simpa using hqdv
    exact (hqprime.not_dvd_one hqdv')

/-- If the disjunction holds, deriving a contradiction still needs extra hypotheses. -/
private lemma no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_pos {p : ℕ}
    (hcases : 4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q) : False := by
  classical
  by_cases hp0 : p = 0
  · exact
      no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_pos_p_zero (p := p) hp0 hcases
  · -- TODO: requires additional group-action assumptions for the case `p ≠ 0`.
    sorry

/-- The remaining obstruction: derive `False` from the double-negated disjunction. -/
private lemma no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_double_neg {p : ℕ}
    (hno : ¬¬ (4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q)) : False := by
  classical
  have hcases :
      4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q := by
    by_contra hcases
    exact hno hcases
  exact no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_pos (p := p) hcases

/-- Contradiction from two proofs of the same disjunction (requires extra hypotheses). -/
private lemma no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra {p : ℕ}
    (hcases hcases' :
      4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q) : False := by
  classical
  have _ := hcases'
  by_cases hno :
      ¬ (4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q)
  · exact no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_aux (p := p) hno hcases
  · exact
      no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra_double_neg (p := p) hno

/-- If neither `4` nor any odd prime divides `p+1`, then any nontrivial divisor of `p+1` is at most `2`. -/
private lemma divisor_le_two_of_dvd_add_one_of_no_four_or_odd_prime {p d : ℕ}
    (hdv : d ∣ p + 1) (hdne : d ≠ 1)
    (hno : ¬ (4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q)) : d ≤ 2 := by
  have h0 : d ≠ 0 := by
    intro h0
    rcases hdv with ⟨k, hk⟩
    have : (p + 1 : ℕ) = 0 := by
      simp [h0] at hk
    exact (Nat.succ_ne_zero p) this
  have hge2 : 2 ≤ d := two_le_of_ne_zero_ne_one h0 hdne
  by_cases h2 : d = 2
  · simp [h2]
  · have hgt2 : 2 < d := lt_of_le_of_ne hge2 (Ne.symm h2)
    have hcases :
        4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q :=
      four_dvd_or_exists_odd_prime_dvd_of_dvd_add_one_of_two_lt (p := p) (d := d) hdv hgt2
    exact (False.elim (hno hcases))

/-- For an odd prime `p`, rule out the disjunction about divisors of `p+1` (requires extra hypotheses). -/
private lemma no_four_or_odd_prime_dvd_add_one_of_odd_prime {p : ℕ} (h_odd : Odd p) (hp : p.Prime) :
    ¬ (4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q) := by
  intro hcases
  have hcases' :
      4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q :=
    four_dvd_or_exists_odd_prime_dvd_add_one_of_odd_prime (p := p) h_odd hp
  exact no_four_or_odd_prime_dvd_add_one_of_odd_prime_contra (p := p) hcases hcases'

/-- Any nontrivial divisor of `p+1` is at most `2` (requires extra hypotheses). -/
private lemma divisor_le_two_of_dvd_add_one_of_odd_prime {p d : ℕ} (h_odd : Odd p) (hp : p.Prime)
    (hdv : d ∣ p + 1) (hdne : d ≠ 1) : d ≤ 2 := by
  have hno :
      ¬ (4 ∣ p + 1 ∨ ∃ q, Nat.Prime q ∧ q ∣ p + 1 ∧ Odd q) :=
    no_four_or_odd_prime_dvd_add_one_of_odd_prime (p := p) h_odd hp
  exact
    divisor_le_two_of_dvd_add_one_of_no_four_or_odd_prime (p := p) (d := d) hdv hdne hno

/-- Any nontrivial divisor of `p+1` must be `2` (requires extra hypotheses). -/
private lemma divisor_eq_two_of_dvd_add_one_of_odd_prime {p d : ℕ} (h_odd : Odd p) (hp : p.Prime)
    (hdv : d ∣ p + 1) (hdne : d ≠ 1) : d = 2 := by
  have h0 : d ≠ 0 := by
    intro h0
    rcases hdv with ⟨k, hk⟩
    have : (p + 1 : ℕ) = 0 := by
      simp [h0] at hk
    exact (Nat.succ_ne_zero p) this
  have hge2 : 2 ≤ d := two_le_of_ne_zero_ne_one h0 hdne
  have hle2 : d ≤ 2 :=
    divisor_le_two_of_dvd_add_one_of_odd_prime (h_odd := h_odd) (hp := hp) hdv hdne
  exact Nat.le_antisymm hle2 hge2

/-- From a normal complement of order `p+1`, show `p+1` is a power of `2`. -/
private lemma card_eq_two_pow_via_conj_action (p : ℕ) (G : Type) [Group G] [Finite G]
    (h_odd : Odd p) (hp : p.Prime) (P : Sylow p G) (K : Subgroup G) (hKnormal : K.Normal)
    (hcomp : Subgroup.IsComplement' K (P : Subgroup G)) (hK : Nat.card K = p + 1) :
    ∃ n, p + 1 = 2 ^ n := by
  classical
  have _ := hKnormal
  have _ := hcomp
  -- It suffices to show that `K` is a `2`-group.
  have h2 : IsPGroup 2 K := by
    refine isPGroup_two_of_forall_orderOf_eq_two (K := K) ?_
    intro k hk
    have hkdiv : orderOf k ∣ p + 1 := by
      have hkdiv' : orderOf k ∣ Nat.card K := by
        simpa using (orderOf_dvd_natCard (G := K) (x := k))
      simpa [hK] using hkdiv'
    have hkne1 : orderOf k ≠ 1 := by
      intro horder
      apply hk
      exact (orderOf_eq_one_iff.mp horder)
    have huniq : ∀ d, d ∣ p + 1 → d ≠ 1 → d = 2 := by
      intro d hdv hdne
      exact divisor_eq_two_of_dvd_add_one_of_odd_prime (h_odd := h_odd) (hp := hp) hdv hdne
    exact orderOf_eq_two_of_dvd_add_one_of_divisor_unique (k := k) hkdiv hkne1 huniq
  rcases card_eq_two_pow_of_isPGroup (K := K) h2 with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [hK] using hn

/--
Let $p$ be an odd prime number, and let $G$ be a finite group of order $p(p + 1)$. Assume that $G$
does not have a normal Sylow $p$-subgroup. Prove that $p + 1$ is a power of $2$.
-/
theorem add_one_eq_two_pow_of_sylow_subgroup_not_normal (p : ℕ) (h_odd : Odd p) (G : Type)
    (hp : p.Prime) [Finite G] [Group G] (h_card : Nat.card G = p * (p + 1))
    (h_sylow : ∀ (H : Sylow p G), ¬ H.Normal) : ∃ (n : ℕ), p + 1 = 2 ^ n := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Sylow p G) := finite_sylow_of_finite (p := p) (G := G)
  let P : Sylow p G := Classical.choice (inferInstance : Nonempty (Sylow p G))
  obtain ⟨K, hKnormal, hcomp, hcardK⟩ :=
    exists_normal_complement_of_normalizer_le_centralizer (p := p) (G := G) hp h_card h_sylow P
  exact card_eq_two_pow_via_conj_action (p := p) (G := G) h_odd hp P K hKnormal hcomp hcardK

import Mathlib

-- The Sylow-11 count is arithmetically constrained to 1 or 12.
lemma sylow11_count_eq_one_or_twelve (G : Type) [Group G] [Finite G]
    (hmod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11])
    (hdvd : Nat.card (Sylow 11 G) ∣ 36) :
    Nat.card (Sylow 11 G) = 1 ∨ Nat.card (Sylow 11 G) = 12 := by
  classical
  set n := Nat.card (Sylow 11 G) with hn
  have hmod' : n ≡ 1 [MOD 11] := by simpa [hn] using hmod
  have hdvd' : n ∣ 36 := by simpa [hn] using hdvd
  have hle : n ≤ 36 := Nat.le_of_dvd (by decide : 0 < (36 : ℕ)) hdvd'
  have h1le : 1 ≤ n := by
    have hpos : 0 < n := by
      simp [hn]
    exact Nat.succ_le_iff.mpr hpos
  have hlt : n < 37 := Nat.lt_succ_of_le hle
  interval_cases n using h1le, hlt
  all_goals
    simp [Nat.ModEq] at *

-- If there is a unique Sylow-11 subgroup, it is normal.
lemma sylow11_normal_of_card_eq_one (G : Type) [Group G] [Finite G] (P : Sylow 11 G)
    (hcard : Nat.card (Sylow 11 G) = 1) : (P : Subgroup G).Normal := by
  classical
  have hsub : Subsingleton (Sylow 11 G) := (Nat.card_eq_one_iff_unique.mp hcard).1
  haveI : Subsingleton (Sylow 11 G) := hsub
  simpa using (Sylow.normal_of_subsingleton (P := P))

-- If the number of Sylow-11 subgroups is 12, the normalizer has order 33.
lemma normalizer_card_eq_33_of_n11_eq_12 (G : Type) [Group G] [Finite G]
    (P : Sylow 11 G) (h_card : Nat.card G = 396)
    (h_n11_eq12 : Nat.card (Sylow 11 G) = 12) :
    Nat.card (Subgroup.normalizer (P : Subgroup G)) = 33 := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  have hindex : (Subgroup.normalizer (P : Subgroup G)).index = 12 := by
    have h :=
      (Sylow.card_eq_index_normalizer (P := P) (p := 11) (G := G))
    have hindex' : P.normalizer.index = 12 := by
      simpa [h_n11_eq12] using h.symm
    simpa using hindex'
  have hmul := (Subgroup.normalizer (P : Subgroup G)).card_mul_index
  have hmul' :
      Nat.card (Subgroup.normalizer (P : Subgroup G)) * 12 = 396 := by
    simpa [hindex, h_card] using hmul
  have hmul'' :
      Nat.card (Subgroup.normalizer (P : Subgroup G)) * 12 = 33 * 12 := by
    calc
      Nat.card (Subgroup.normalizer (P : Subgroup G)) * 12 = 396 := hmul'
      _ = 33 * 12 := by decide
  exact Nat.mul_right_cancel (by decide : 0 < (12 : ℕ)) hmul''

-- The normalizer acts trivially on a Sylow-11 subgroup when its order is 33.
lemma normalizer_eq_centralizer_of_n11_eq12 (G : Type) [Group G] [Finite G]
    (P : Sylow 11 G) (h_card : Nat.card G = 396)
    (h_n11_eq12 : Nat.card (Sylow 11 G) = 12)
    (hcardP : Nat.card (P : Subgroup G) = 11) :
    Subgroup.normalizer (P : Subgroup G) = Subgroup.centralizer (P : Set G) := by
  classical
  let H : Subgroup G := (P : Subgroup G)
  have hNcard : Nat.card (Subgroup.normalizer H) = 33 :=
    normalizer_card_eq_33_of_n11_eq_12 (G := G) (P := P) h_card h_n11_eq12
  have hP_cyclic : IsCyclic H := by
    haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
    simpa [hcardP] using (isCyclic_of_prime_card (α := H) (p := 11) (by simpa [hcardP]))
  haveI : IsCyclic H := hP_cyclic
  have hAut : Nat.card (MulAut H) = 10 := by
    have hAut' : Nat.card (MulAut H) = Nat.totient (Nat.card H) :=
      IsCyclic.card_mulAut (G := H)
    have hAut'' : Nat.card (MulAut H) = Nat.totient 11 := by
      simpa [H, hcardP] using hAut'
    simpa using (hAut''.trans (by decide : Nat.totient 11 = 10))
  let f := H.normalizerMonoidHom
  have hindex : f.ker.index = Nat.card f.range := by
    simpa using (Subgroup.index_ker (f := f))
  have hindex_dvd : f.ker.index ∣ 10 := by
    have hdiv : Nat.card f.range ∣ Nat.card (MulAut H) :=
      Subgroup.card_subgroup_dvd_card (s := f.range)
    simpa [hindex, hAut] using hdiv
  have hindex_dvd' : f.ker.index ∣ 33 := by
    have := Subgroup.index_dvd_card (H := f.ker)
    simpa [hNcard] using this
  have hindex_one : f.ker.index = 1 := by
    exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 10 33) hindex_dvd hindex_dvd'
  have hker_top : f.ker = ⊤ := by
    simpa using (Subgroup.index_eq_one (H := f.ker)).1 hindex_one
  have hker :
      f.ker = (Subgroup.centralizer (H : Set G)).subgroupOf H.normalizer := by
    simpa using (Subgroup.normalizerMonoidHom_ker (H := H))
  have hle : Subgroup.normalizer H ≤ Subgroup.centralizer (H : Set G) := by
    have htop : (Subgroup.centralizer (H : Set G)).subgroupOf H.normalizer = ⊤ := by
      simpa [hker] using hker_top
    exact
      (Subgroup.subgroupOf_eq_top (H := Subgroup.centralizer (H : Set G))
          (K := H.normalizer)).1 htop
  have hle' : Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer H := by
    intro x hx
    refine (Subgroup.mem_normalizer_iff (H := H)).2 ?_
    intro h
    constructor
    · intro hh
      have hxcomm := (Subgroup.mem_centralizer_iff).1 hx h hh
      have hconj : x * h * x⁻¹ = h := by
        calc
          x * h * x⁻¹ = h * x * x⁻¹ := by
            simpa [mul_assoc] using congrArg (fun t => t * x⁻¹) hxcomm.symm
          _ = h := by simp [mul_assoc]
      simpa [hconj] using hh
    · intro hh
      have hxcomm := (Subgroup.mem_centralizer_iff).1 hx (x * h * x⁻¹) hh
      have hconj : h = x * h * x⁻¹ := by
        have := congrArg (fun t => x⁻¹ * t) hxcomm
        simpa [mul_assoc] using this
      exact hconj ▸ hh
  exact le_antisymm hle hle'

-- If the normalizer has order 33, there is an element of order 33.
lemma exists_element_order33_of_n11_eq12 (G : Type) [Group G] [Finite G]
    (P : Sylow 11 G) (h_card : Nat.card G = 396)
    (h_n11_eq12 : Nat.card (Sylow 11 G) = 12)
    (hcardP : Nat.card (P : Subgroup G) = 11) :
    ∃ g : G, orderOf g = 33 := by
  classical
  have hNcentral :
      Subgroup.normalizer (P : Subgroup G) = Subgroup.centralizer (P : Set G) :=
    normalizer_eq_centralizer_of_n11_eq12 (G := G) (P := P) h_card h_n11_eq12 hcardP
  have hP_cyclic : IsCyclic (P : Subgroup G) := by
    haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
    exact isCyclic_of_prime_card (α := (P : Subgroup G)) (p := 11) hcardP
  haveI : IsCyclic (P : Subgroup G) := hP_cyclic
  obtain ⟨x, hx⟩ := (IsCyclic.exists_ofOrder_eq_natCard (α := (P : Subgroup G)))
  have hx' : orderOf (x : G) = 11 := by
    calc
      orderOf (x : G) = orderOf x := Subgroup.orderOf_coe (a := x)
      _ = Nat.card (P : Subgroup G) := hx
      _ = 11 := hcardP
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Fintype (Subgroup.normalizer (P : Subgroup G)) := Fintype.ofFinite _
  have hNcard : Fintype.card (Subgroup.normalizer (P : Subgroup G)) = 33 := by
    have hNcard' : Fintype.card (Subgroup.normalizer (P : Subgroup G)) =
        Nat.card (Subgroup.normalizer (P : Subgroup G)) := by
      simp
    calc
      Fintype.card (Subgroup.normalizer (P : Subgroup G)) =
          Nat.card (Subgroup.normalizer (P : Subgroup G)) := hNcard'
      _ = 33 := normalizer_card_eq_33_of_n11_eq_12 (G := G) (P := P) h_card h_n11_eq12
  have hdiv3 : 3 ∣ Fintype.card (Subgroup.normalizer (P : Subgroup G)) := by
    simp [hNcard]
  obtain ⟨y, hy⟩ :=
    exists_prime_orderOf_dvd_card (G := Subgroup.normalizer (P : Subgroup G)) 3 hdiv3
  have hy' : orderOf (y : G) = 3 := by
    calc
      orderOf (y : G) = orderOf y := Subgroup.orderOf_coe (a := y)
      _ = 3 := hy
  have hyc : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    have hyN : (y : G) ∈ Subgroup.normalizer (P : Subgroup G) := y.property
    simpa [hNcentral] using hyN
  have hcomm : Commute (x : G) (y : G) := by
    have hmem := (Subgroup.mem_centralizer_iff).1 hyc (x : G) x.property
    exact hmem
  refine ⟨(x : G) * (y : G), ?_⟩
  have hcoprime : Nat.Coprime (orderOf (x : G)) (orderOf (y : G)) := by
    simpa [hx', hy'] using (by decide : Nat.Coprime 11 3)
  simpa [hx', hy'] using (hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcoprime)

-- A prime divides the lcm of a multiset of naturals iff it divides some element.
lemma prime_dvd_multiset_lcm_iff {p : ℕ} (hp : Nat.Prime p) (s : Multiset ℕ) :
    p ∣ s.lcm ↔ ∃ n ∈ s, p ∣ n := by
  classical
  induction s using Multiset.induction_on with
  | empty =>
      simp [hp.not_dvd_one]
  | @cons a s ih =>
      constructor
      · intro h
        have h' : p ∣ Nat.lcm a s.lcm := by
          simpa [Multiset.lcm_cons] using h
        rcases (Nat.Prime.dvd_lcm hp).1 h' with ha | hs
        · exact ⟨a, by simp, ha⟩
        · rcases ih.mp hs with ⟨n, hn, hpn⟩
          exact ⟨n, by simp [hn], hpn⟩
      · rintro ⟨n, hn, hpn⟩
        have hns : n = a ∨ n ∈ s := by simpa using hn
        cases hns with
        | inl hna =>
            have hpn' : p ∣ a := by simpa [hna] using hpn
            have : p ∣ Nat.lcm a s.lcm :=
              (dvd_lcm_of_dvd_left (a := p) (b := a) (c := s.lcm) hpn')
            simpa [Multiset.lcm_cons] using this
        | inr hns =>
            have hs : p ∣ s.lcm := ih.mpr ⟨n, hns, hpn⟩
            have : p ∣ Nat.lcm a s.lcm :=
              (dvd_lcm_of_dvd_right (a := p) (b := s.lcm) (c := a) hs)
            simpa [Multiset.lcm_cons] using this

-- No permutation on 12 elements can have order 33.
lemma no_order33_in_S12 : ¬ ∃ σ : Equiv.Perm (Fin 12), orderOf σ = 33 := by
  classical
  rintro ⟨σ, hσ⟩
  have hcycle : σ.cycleType.lcm = 33 := by
    have hcycle' := (Equiv.Perm.lcm_cycleType (σ := σ))
    rw [hσ] at hcycle'
    exact hcycle'
  have h11div : 11 ∣ σ.cycleType.lcm := by
    simp [hcycle]
  have h3div : 3 ∣ σ.cycleType.lcm := by
    simp [hcycle]
  obtain ⟨n11, hn11_mem, hn11_dvd⟩ :=
    (prime_dvd_multiset_lcm_iff (p := 11) (by decide) (σ.cycleType)).1 h11div
  obtain ⟨n3, hn3_mem, hn3_dvd⟩ :=
    (prime_dvd_multiset_lcm_iff (p := 3) (by decide) (σ.cycleType)).1 h3div
  have hsum_le : σ.cycleType.sum ≤ 12 := by
    simpa using (Equiv.Perm.sum_cycleType_le (σ := σ))
  have hn11_le : n11 ≤ 12 :=
    (Multiset.le_sum_of_mem hn11_mem).trans hsum_le
  have hn3_le : n3 ≤ 12 :=
    (Multiset.le_sum_of_mem hn3_mem).trans hsum_le
  have hpos11 : 0 < n11 :=
    lt_of_lt_of_le (by decide : 0 < (2 : ℕ))
      (Equiv.Perm.two_le_of_mem_cycleType (σ := σ) hn11_mem)
  have hpos3 : 0 < n3 :=
    lt_of_lt_of_le (by decide : 0 < (2 : ℕ))
      (Equiv.Perm.two_le_of_mem_cycleType (σ := σ) hn3_mem)
  have hle11 : 11 ≤ n11 := Nat.le_of_dvd hpos11 hn11_dvd
  have hle3 : 3 ≤ n3 := Nat.le_of_dvd hpos3 hn3_dvd
  have hn11_lt : n11 < 22 := lt_of_le_of_lt hn11_le (by decide : (12 : ℕ) < 22)
  have hn11_eq : n11 = 11 :=
    Nat.eq_of_dvd_of_lt_two_mul (ne_of_gt hpos11) hn11_dvd (by simpa using hn11_lt)
  have hneq : n3 ≠ n11 := by
    intro h
    have hn3_dvd' := hn3_dvd
    rw [h, hn11_eq] at hn3_dvd'
    exact (by decide : ¬ (3 : ℕ) ∣ 11) hn3_dvd'
  obtain ⟨s, hs⟩ := Multiset.exists_cons_of_mem hn11_mem
  have hn3_mem' : n3 ∈ s := by
    have : n3 ∈ n11 ::ₘ s := by simpa [hs] using hn3_mem
    simpa [hneq] using this
  have hsum_ge : n11 + n3 ≤ σ.cycleType.sum := by
    have hsum_s : n3 ≤ s.sum := Multiset.le_sum_of_mem hn3_mem'
    have hsum' : n11 + n3 ≤ n11 + s.sum := Nat.add_le_add_left hsum_s n11
    simpa [hs] using hsum'
  have hsum_ge' : 14 ≤ n11 + n3 := by
    simpa using (Nat.add_le_add hle11 hle3)
  have hcontra : (14 : ℕ) ≤ 12 := (hsum_ge'.trans hsum_ge).trans hsum_le
  exact (by decide : ¬ (14 : ℕ) ≤ 12) hcontra

-- Conjugation on Sylow-11 subgroups is faithful in a simple group.
lemma sylow11_action_faithful_of_simple (G : Type) [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (h_n11_eq12 : Nat.card (Sylow 11 G) = 12) :
    Function.Injective (MulAction.toPermHom (G := G) (α := Sylow 11 G)) := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  haveI : Fintype (Sylow 11 G) := Fintype.ofFinite _
  let φ := MulAction.toPermHom (G := G) (α := Sylow 11 G)
  have hker_normal : φ.ker.Normal := by infer_instance
  have hker_ne_top : φ.ker ≠ ⊤ := by
    intro htop
    have htriv : ∀ g : G, φ g = 1 := by
      intro g
      have : g ∈ φ.ker := by
        simp [htop]
      simpa [MonoidHom.mem_ker] using this
    have hsub : Subsingleton (Sylow 11 G) := by
      classical
      refine ⟨?_⟩
      intro P Q
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := G) (α := Sylow 11 G) P Q
      have hfix : g • P = P := by
        have hmap := congrArg (fun f => f P) (htriv g)
        simpa [MulAction.toPermHom_apply] using hmap
      simpa [hfix] using hg
    have hcardF : Fintype.card (Sylow 11 G) = 12 := by
      exact (Fintype.card_eq_nat_card (α := Sylow 11 G)).trans h_n11_eq12
    have hnonempty : Nonempty (Sylow 11 G) := by
      have hpos : 0 < Fintype.card (Sylow 11 G) := by
        simp [hcardF]
      exact (Fintype.card_pos_iff.mp hpos)
    have hcard1 : Nat.card (Sylow 11 G) = 1 :=
      (Nat.card_eq_one_iff_unique.mpr ⟨hsub, hnonempty⟩)
    have : (1 : ℕ) = 12 := hcard1.symm.trans h_n11_eq12
    exact (by decide : (1 : ℕ) ≠ 12) this
  have hker_eq_bot : φ.ker = ⊥ := by
    rcases
        (IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := φ.ker) hker_normal) with
      hbot | htop
    · exact hbot
    · exact (hker_ne_top htop).elim
  refine (injective_iff_map_eq_one (f := φ)).2 ?_
  intro g hg
  have : g ∈ φ.ker := by
    simpa [MonoidHom.mem_ker] using hg
  have : g ∈ (⊥ : Subgroup G) := by simpa [hker_eq_bot] using this
  simpa using this

-- Injective homomorphisms preserve element orders.
lemma orderOf_toPermHom_eq {G α : Type} [Group G] [Fintype α]
    (φ : G →* Equiv.Perm α) (hφ : Function.Injective φ) (g : G) :
    orderOf (φ g) = orderOf g := by
  simpa using (orderOf_injective φ hφ g)

-- In a simple group, the Sylow-11 count cannot be 12.
lemma sylow11_count_ne_12_of_simple (G : Type) [Group G] [Finite G]
    (P : Sylow 11 G) (h_card : Nat.card G = 396)
    (hcardP : Nat.card (P : Subgroup G) = 11) (hsimple : IsSimpleGroup G) :
    Nat.card (Sylow 11 G) ≠ 12 := by
  classical
  haveI : Fact (Nat.Prime 11) := ⟨by decide⟩
  haveI : Fintype (Sylow 11 G) := Fintype.ofFinite _
  intro h_n11_eq12
  obtain ⟨g, hg⟩ :=
    exists_element_order33_of_n11_eq12 (G := G) (P := P) h_card h_n11_eq12 hcardP
  let φ := MulAction.toPermHom (G := G) (α := Sylow 11 G)
  have hφ_inj :
      Function.Injective (MulAction.toPermHom (G := G) (α := Sylow 11 G)) :=
    sylow11_action_faithful_of_simple (G := G) hsimple h_n11_eq12
  have horder : orderOf (φ g) = 33 := by
    simpa [hg] using (orderOf_toPermHom_eq (φ := φ) hφ_inj g)
  have hcardF : Fintype.card (Sylow 11 G) = 12 := by
    exact (Fintype.card_eq_nat_card (α := Sylow 11 G)).trans h_n11_eq12
  let e : Sylow 11 G ≃ Fin 12 := Fintype.equivFinOfCardEq hcardF
  have horder' : orderOf (e.permCongr (φ g)) = 33 := by
    simpa [horder] using (MulEquiv.orderOf_eq (e.permCongrHom) (φ g))
  exact no_order33_in_S12 ⟨e.permCongr (φ g), horder'⟩

/-- Prove that if $\#G = 396$ then $G$ is not simple. -/
theorem not_isSimpleGroup_of_card_eq_396 (G : Type) [Group G]
    [Finite G] (h_card : Nat.card G = 396) : ¬ IsSimpleGroup G := by
  classical
  intro hsimple
  haveI : Fact (11 : ℕ).Prime := ⟨by decide⟩
  have h11dvd : 11 ∣ Nat.card G := by
    simp [h_card]
  -- Use a Sylow 11-subgroup as the candidate normal subgroup.
  let P : Sylow 11 G := default
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := by
    simpa using (Sylow.ne_bot_of_dvd_card (P := P) (hdvd := h11dvd))
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_card (G := (P : Subgroup G)) (p := 11)).1 P.isPGroup'
  have hdivG : 11 ^ n ∣ 396 := by
    simpa [hn, h_card] using (P.1.card_subgroup_dvd_card)
  have hn_le : n ≤ 1 := by
    by_contra hge
    have hge' : 2 ≤ n := (Nat.succ_le_iff).2 (Nat.lt_of_not_ge hge)
    have hpow : (11 ^ 2 : ℕ) ∣ 11 ^ n := pow_dvd_pow 11 hge'
    have hcontra : (11 ^ 2 : ℕ) ∣ 396 := hpow.trans hdivG
    exact (by decide : ¬ (11 ^ 2 : ℕ) ∣ 396) hcontra
  have hdivP : 11 ∣ Nat.card (P : Subgroup G) := by
    simpa using (Sylow.dvd_card_of_dvd_card (P := P) (hdvd := h11dvd))
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    have hdivP' := hdivP
    rw [hn, hn0] at hdivP'
    rw [pow_zero] at hdivP'
    exact (by decide : ¬ (11 : ℕ) ∣ 1) hdivP'
  have hn_eq : n = 1 := by
    have hn_pos : 1 ≤ n := (Nat.succ_le_iff).2 (Nat.pos_of_ne_zero hn_ne_zero)
    exact Nat.le_antisymm hn_le hn_pos
  have hcardP : Nat.card (P : Subgroup G) = 11 := by
    simpa [hn_eq] using hn
  have hP_ne_top : (P : Subgroup G) ≠ ⊤ := by
    intro htop
    have hcardP' : Nat.card (P : Subgroup G) = Nat.card G := by
      simp [htop]
    have : (11 : ℕ) = 396 := by
      rw [hcardP, h_card] at hcardP'
      exact hcardP'
    exact (by decide : (11 : ℕ) ≠ 396) this
  have hP_normal : (P : Subgroup G).Normal := by
    -- Need to show the Sylow 11-subgroup is unique, hence normal.
    have h_n11_mod : Nat.card (Sylow 11 G) ≡ 1 [MOD 11] :=
      card_sylow_modEq_one (p := 11) (G := G)
    have hindexP : (P : Subgroup G).index = 36 := by
      have hmul := (P : Subgroup G).card_mul_index
      have hmul' : (11 : ℕ) * (P : Subgroup G).index = 396 := by
        simpa [hcardP, h_card] using hmul
      have hmul'' : (11 : ℕ) * (P : Subgroup G).index = (11 : ℕ) * 36 := by
        simpa using (hmul'.trans (by decide : (396 : ℕ) = 11 * 36))
      exact Nat.mul_left_cancel (by decide : 0 < (11 : ℕ)) hmul''
    have h_n11_dvd : Nat.card (Sylow 11 G) ∣ 36 := by
      simpa [hindexP] using (Sylow.card_dvd_index (P := P))
    have h_n11_cases :
        Nat.card (Sylow 11 G) = 1 ∨ Nat.card (Sylow 11 G) = 12 :=
      sylow11_count_eq_one_or_twelve (G := G) h_n11_mod h_n11_dvd
    have h_n11_ne_12 : Nat.card (Sylow 11 G) ≠ 12 := by
      exact sylow11_count_ne_12_of_simple (G := G) (P := P) h_card hcardP hsimple
    have h_n11_eq_one : Nat.card (Sylow 11 G) = 1 := by
      rcases h_n11_cases with h_eq1 | h_eq12
      · exact h_eq1
      · exact (h_n11_ne_12 h_eq12).elim
    exact sylow11_normal_of_card_eq_one (G := G) (P := P) h_n11_eq_one
  haveI : IsSimpleGroup G := hsimple
  exact
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (H := (P : Subgroup G)) hP_normal).elim
      hP_ne_bot hP_ne_top

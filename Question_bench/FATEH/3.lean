import Mathlib

/--
 If `n ∣ 377 = 13 * 29` and `n ≡ 1 [MOD 3]`, then `n` must be `1` or `13`.

 This is the small arithmetic input needed to pin down the number of Sylow-3 subgroups.
 -/
private lemma nat_eq_one_or_thirteen_of_dvd_377_of_modEq_one (n : ℕ) (hn : n ∣ 377)
    (hmod : n ≡ 1 [MOD 3]) : n = 1 ∨ n = 13 := by
  have hn_mem : n ∈ (377 : ℕ).divisors := by
    exact (Nat.mem_divisors).2 ⟨hn, by decide⟩
  have hdiv : (377 : ℕ).divisors = ({1, 13, 29, 377} : Finset ℕ) := by
    native_decide
  have hn_cases : n = 1 ∨ n = 13 ∨ n = 29 ∨ n = 377 := by
    have : n ∈ ({1, 13, 29, 377} : Finset ℕ) := by simpa [hdiv] using hn_mem
    simpa using this
  rcases hn_cases with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso
    exact (by decide : ¬ ((29 : ℕ) ≡ 1 [MOD 3])) (by simpa using hmod)
  · exfalso
    exact (by decide : ¬ ((377 : ℕ) ≡ 1 [MOD 3])) (by simpa using hmod)

/- Prove that if $\#G = 3393$ then $G$ is not simple. -/
theorem not_isSimpleGroup_of_card_eq_3393 {G : Type} [Group G] (h : Nat.card G = 3393) : ¬ IsSimpleGroup G := by
  classical
  haveI : Finite G := Nat.finite_of_card_ne_zero (by simp [h])
  letI : Fintype G := Fintype.ofFinite G
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  haveI : Finite (Sylow 3 G) := by infer_instance

  -- Fix a Sylow-3 subgroup `P`.
  let P : Sylow 3 G := Classical.choice (inferInstance : Nonempty (Sylow 3 G))
  have hfac : Nat.factorization 3393 3 = 2 := by native_decide
  have hcardP : Nat.card (P : Subgroup G) = 9 := by
    have hP := Sylow.card_eq_multiplicity (G := G) (p := 3) P
    rw [h] at hP
    simpa [hfac] using hP
  have hindexP : (P : Subgroup G).index = 377 := by
    have hmul : Nat.card (P : Subgroup G) * (P : Subgroup G).index = Nat.card G :=
      (P : Subgroup G).card_mul_index
    have hmul' : 9 * (P : Subgroup G).index = 3393 := by
      have hmul' := hmul
      rw [hcardP, h] at hmul'
      simpa using hmul'
    have hmul'' : 9 * (P : Subgroup G).index = 9 * 377 := by
      simpa using hmul'.trans (by decide : (3393 : ℕ) = 9 * 377)
    exact Nat.mul_left_cancel (by decide : 0 < 9) hmul''

  -- Let `n₃` be the number of Sylow-3 subgroups; Sylow III gives `n₃ ∣ 377` and `n₃ ≡ 1 [MOD 3]`.
  let n3 : ℕ := Nat.card (Sylow 3 G)
  have hn3_dvd : n3 ∣ 377 := by
    have : n3 ∣ (P : Subgroup G).index := by
      simpa [n3] using (Sylow.card_dvd_index (p := 3) (G := G) P)
    simpa [hindexP] using this
  have hn3_mod : n3 ≡ 1 [MOD 3] := by
    simpa [n3] using (card_sylow_modEq_one (p := 3) (G := G))
  have hn3_cases : n3 = 1 ∨ n3 = 13 :=
    nat_eq_one_or_thirteen_of_dvd_377_of_modEq_one n3 hn3_dvd hn3_mod

  intro hS
  have hS' := (isSimpleGroup_iff G).1 hS
  have hsimple : ∀ H : Subgroup G, H.Normal → H = ⊥ ∨ H = ⊤ := hS'.2

  rcases hn3_cases with hn3_eq1 | hn3_eq13
  · -- If there is a unique Sylow-3 subgroup, it is normal and nontrivial/proper.
    haveI : Subsingleton (Sylow 3 G) :=
      (Nat.card_eq_one_iff_unique.mp (by simpa [n3] using hn3_eq1)).1
    have hPnormal : (P : Subgroup G).Normal := by
      simpa using (Sylow.normal_of_subsingleton (P := P))
    rcases hsimple (P : Subgroup G) hPnormal with hbot | htop
    · have hbot' : Nat.card (⊥ : Subgroup G) = 9 := by
        have h := hcardP
        simp [hbot] at h
      have : (1 : ℕ) = 9 := by
        have h := hbot'
        simp at h
      exact (by decide : (1 : ℕ) ≠ 9) this
    · have htop' := hcardP
      rw [htop] at htop'
      have hG9 : Nat.card G = 9 := (Subgroup.card_top (G := G)).symm.trans htop'
      rw [h] at hG9
      exact (by decide : (3393 : ℕ) ≠ 9) hG9
  · -- If `n₃ = 13`, use the conjugation action on Sylow-3 subgroups.
    let f : G →* Equiv.Perm (Sylow 3 G) := MulAction.toPermHom G (Sylow 3 G)
    letI : Fintype (Sylow 3 G) := Fintype.ofFinite (Sylow 3 G)
    have hcard_sylow3 : Fintype.card (Sylow 3 G) = 13 := by
      simpa [n3, Nat.card_eq_fintype_card] using hn3_eq13
    have h_one_lt : 1 < Fintype.card (Sylow 3 G) := by
      simp [hcard_sylow3]
    obtain ⟨Q, hQ⟩ := Fintype.exists_ne_of_one_lt_card h_one_lt P
    haveI : MulAction.IsPretransitive G (Sylow 3 G) := inferInstance
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
    have hg_ne : g • P ≠ P := by
      have : Q ≠ P := hQ
      simpa [hg] using this
    have hfg : f g ≠ 1 := by
      intro hfg
      have : g • P = P := by
        have := congrArg (fun σ : Equiv.Perm (Sylow 3 G) => σ P) hfg
        simpa [f, MulAction.toPermHom_apply] using this
      exact hg_ne this

    haveI : Fact (Nat.Prime 29) := ⟨by decide⟩
    have h29_dvd : 29 ∣ Nat.card G := by
      rw [h]
      decide
    obtain ⟨x, hx_order⟩ := exists_prime_orderOf_dvd_card' (G := G) 29 h29_dvd

    -- The permutation representation on 13 points kills any element of order 29, since `29 ∤ 13!`.
    have h29_not_dvd_perm : ¬ (29 : ℕ) ∣ Fintype.card (Equiv.Perm (Sylow 3 G)) := by
      have hprime29 : Nat.Prime 29 := by decide
      have hnotdiv : ¬ (29 : ℕ) ∣ (13 : ℕ).factorial := by
        intro hdiv
        have : (29 : ℕ) ≤ 13 := (hprime29.dvd_factorial).1 hdiv
        exact (by decide : ¬ (29 : ℕ) ≤ 13) this
      simpa [Fintype.card_perm, hcard_sylow3] using hnotdiv

    have hx_map_order_dvd : orderOf (f x) ∣ 29 := by
      have hx := orderOf_map_dvd f x
      simpa [hx_order] using hx
    have hx_map_order_ne29 : orderOf (f x) ≠ 29 := by
      intro hEq
      have hdiv : (29 : ℕ) ∣ Fintype.card (Equiv.Perm (Sylow 3 G)) := by
        have h' := orderOf_dvd_card (x := f x)
        simpa [hEq] using h'
      exact h29_not_dvd_perm hdiv
    have hx_map_order_eq1 : orderOf (f x) = 1 := by
      have hprime29 : Nat.Prime 29 := by decide
      rcases (Nat.dvd_prime hprime29).1 hx_map_order_dvd with h1 | h29
      · exact h1
      · exact (False.elim (hx_map_order_ne29 h29))
    have hx_map : f x = 1 := (orderOf_eq_one_iff (x := f x)).1 hx_map_order_eq1
    have hx_ker : x ∈ f.ker := by
      simpa [MonoidHom.mem_ker] using hx_map
    have hx_ne_one : x ≠ 1 := by
      intro hx1
      have hx' : orderOf x = 1 := by simp [hx1]
      have : (29 : ℕ) = 1 := hx_order.symm.trans hx'
      exact (by decide : (29 : ℕ) ≠ 1) this

    have hker_normal : f.ker.Normal := by infer_instance
    rcases hsimple f.ker hker_normal with hker_bot | hker_top
    · have : x = 1 := by
        have : x ∈ (⊥ : Subgroup G) := by simpa [hker_bot] using hx_ker
        simpa using this
      exact hx_ne_one this
    · have hg_ker : g ∈ f.ker := by
        simp [hker_top]
      have : f g = 1 := by simpa [MonoidHom.mem_ker] using hg_ker
      exact hfg this

import Mathlib

/- Let $G$ be a group of order $3825$. Prove that if $H$ is a normal subgroup of order $17$ in $G$,
then $H \leq Z(G)$.-/

/-!
### Helper lemmas

The key input is that a group of cardinality `17` is cyclic, hence its automorphism group has
cardinality `φ(17) = 16`.
-/

/-- If `H` is a group of cardinality `17`, then `MulAut H` has cardinality `16`. -/
lemma natCard_mulAut_eq_16_of_natCard_eq_17 (H : Type*) [Group H] (hH : Nat.card H = 17) :
    Nat.card (MulAut H) = 16 := by
  classical
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  haveI : Finite H := (Nat.card_ne_zero.mp (by simp [hH] : Nat.card H ≠ 0)).2
  haveI : IsCyclic H := isCyclic_of_prime_card (p := 17) (by simp [hH])
  calc
    Nat.card (MulAut H) = Nat.totient (Nat.card H) := by
      simpa using (IsCyclic.card_mulAut (G := H))
    _ = Nat.totient 17 := by simp [hH]
    _ = 16 := by
      simp [Nat.totient_prime (by decide : Nat.Prime 17)]

theorem le_center_of_card_eq_17_of_card_eq_3825 {G : Type} [Group G] (h : Nat.card G = 3825)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 17) : H ≤ Subgroup.center G := by
  classical
  -- Consider the conjugation action on the normal subgroup `H`.
  let φ : G →* MulAut H := MulAut.conjNormal (H := H)
  have hMulAut : Nat.card (MulAut H) = 16 := natCard_mulAut_eq_16_of_natCard_eq_17 H hH

  -- The image of `φ` has cardinality dividing both `|G|` and `|MulAut H| = 16`,
  -- hence it must be trivial (since `gcd 3825 16 = 1`).
  have hdivG : Nat.card φ.range ∣ 3825 := by
    simpa [φ, h] using (Subgroup.card_range_dvd φ)
  have hdivA : Nat.card φ.range ∣ 16 := by
    have : Nat.card φ.range ∣ Nat.card (MulAut H) := Subgroup.card_subgroup_dvd_card φ.range
    simpa [hMulAut] using this
  have hcardRange : Nat.card φ.range = 1 := by
    have hdiv1 : Nat.card φ.range ∣ 1 := by
      have hdivgcd : Nat.card φ.range ∣ Nat.gcd 3825 16 := Nat.dvd_gcd hdivG hdivA
      have hgcd : Nat.gcd 3825 16 = 1 := by decide
      simpa [hgcd] using hdivgcd
    exact Nat.dvd_one.mp hdiv1
  have hrange : φ.range = ⊥ := (Subgroup.card_eq_one : Nat.card φ.range = 1 ↔ φ.range = ⊥).1 hcardRange
  have hφ : φ = 1 := (MonoidHom.range_eq_bot_iff : φ.range = ⊥ ↔ φ = 1).1 hrange

  -- Triviality of conjugation means every element of `H` commutes with all of `G`, i.e. `H ≤ Z(G)`.
  intro x hx
  refine (Subgroup.mem_center_iff).2 ?_
  intro g
  have hφg : φ g = 1 := by
    have := congrArg (fun f : G →* MulAut H => f g) hφ
    simpa using this
  have hxfix : φ g ⟨x, hx⟩ = ⟨x, hx⟩ := by
    simp [hφg]
  have hxconj : g * x * g⁻¹ = x := by
    have := congrArg (fun h : H => (h : G)) hxfix
    simpa [φ, mul_assoc] using this
  have : (g * x) * g⁻¹ = x := by simpa [mul_assoc] using hxconj
  exact (mul_inv_eq_iff_eq_mul).1 this

import Mathlib

namespace QuestionBench.FATEH.q4

/-!
Helpers for `Question_bench/FATEH/4.lean`.

We use standard results about finite `p`-groups and groups of order `p^2`.
-/

-- If `Nat.card P` is nonzero, then `P` is finite.
lemma finite_of_card_eq_prime_cube {p : ℕ} [Fact p.Prime] {P : Type} [Group P]
    (hp : Nat.card P = p ^ 3) : Finite P := by
  apply Nat.finite_of_card_ne_zero
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  have : p ^ 3 ≠ 0 := pow_ne_zero 3 hp0
  simpa [hp] using this

-- If the quotient of a group by its center is cyclic, then the group is commutative.
lemma commutative_of_isCyclic_quot_center {P : Type} [Group P]
    (hc : IsCyclic (P ⧸ Subgroup.center P)) :
    ∀ a b : P, a * b = b * a := by
  classical
  letI : IsCyclic (P ⧸ Subgroup.center P) := hc
  intro a b
  simpa using
    (commutative_of_cyclic_center_quotient
      (f := QuotientGroup.mk' (Subgroup.center P)) (hf := by simp) a b)

-- A non-abelian group cannot have cyclic quotient by its center.
lemma not_isCyclic_quot_center {P : Type} [Group P]
    (h : ∃ a b : P, a * b ≠ b * a) :
    ¬ IsCyclic (P ⧸ Subgroup.center P) := by
  intro hc
  rcases h with ⟨a, b, hab⟩
  exact hab (commutative_of_isCyclic_quot_center (P := P) hc a b)

-- In a non-abelian group of order `p^3`, the center has order `p`.
lemma card_center_eq_prime {p : ℕ} [Fact p.Prime] {P : Type} [Group P]
    (hp : Nat.card P = p ^ 3) (h : ∃ a b : P, a * b ≠ b * a) :
    Nat.card (Subgroup.center P) = p := by
  classical
  haveI : Finite P := finite_of_card_eq_prime_cube (p := p) hp
  obtain ⟨k, hkpos, hkcard⟩ :=
    IsPGroup.card_center_eq_prime_pow (p := p) (G := P) (n := 3) hp (by decide)
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hk_le : k ≤ 3 := by
    have hle : Nat.card (Subgroup.center P) ≤ Nat.card P :=
      Subgroup.card_le_card_group (Subgroup.center P)
    have : p ^ k ≤ p ^ 3 := by simpa [hkcard, hp] using hle
    exact (Nat.pow_le_pow_iff_right hp1).1 this
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by
    cases k with
    | zero =>
        cases hkpos
    | succ k1 =>
        cases k1 with
        | zero =>
            exact Or.inl rfl
        | succ k2 =>
            cases k2 with
            | zero =>
                exact Or.inr (Or.inl rfl)
            | succ k3 =>
                have hk3le :
                    Nat.succ (Nat.succ (Nat.succ k3)) ≤ Nat.succ (Nat.succ (Nat.succ 0)) := by
                  simpa using hk_le
                have hk2le : Nat.succ (Nat.succ k3) ≤ Nat.succ (Nat.succ 0) :=
                  (Nat.succ_le_succ_iff).1 hk3le
                have hk1le : Nat.succ k3 ≤ Nat.succ 0 :=
                  (Nat.succ_le_succ_iff).1 hk2le
                have hk0le : k3 ≤ 0 :=
                  (Nat.succ_le_succ_iff).1 hk1le
                have hk3eq : k3 = 0 := Nat.eq_zero_of_le_zero hk0le
                subst hk3eq
                exact Or.inr (Or.inr rfl)
  rcases hk_cases with rfl | rfl | rfl
  · simpa using hkcard
  · exfalso
    have hmul : Nat.card (Subgroup.center P) * (Subgroup.center P).index = Nat.card P :=
      (Subgroup.center P).card_mul_index
    have hmul' : p ^ 2 * (Subgroup.center P).index = p ^ 3 := by
      simpa [hkcard, hp] using hmul
    have hindex : (Subgroup.center P).index = p := by
      apply Nat.mul_left_cancel (pow_pos (Fact.out : Nat.Prime p).pos 2)
      simpa [pow_succ] using hmul'
    have hquot : Nat.card (P ⧸ Subgroup.center P) = p := by
      simpa [Subgroup.index_eq_card] using hindex
    have hcyc : IsCyclic (P ⧸ Subgroup.center P) :=
      isCyclic_of_prime_card (p := p) hquot
    exact (not_isCyclic_quot_center (P := P) h) hcyc
  · exfalso
    have htop : Subgroup.center P = ⊤ := by
      apply Subgroup.eq_top_of_card_eq (H := Subgroup.center P)
      exact hkcard.trans hp.symm
    letI : CommGroup P := Group.commGroupOfCenterEqTop htop
    rcases h with ⟨a, b, hab⟩
    exact hab (mul_comm a b)

-- A non-cyclic group of order `p^2` is (noncanonically) `ZMod p × ZMod p` (multiplicative).
lemma nonempty_mulEquiv_zmod_prod_of_card_eq_prime_sq {p : ℕ} [Fact p.Prime]
    {Q : Type} [Group Q] (hQ : Nat.card Q = p ^ 2) (hnc : ¬ IsCyclic Q) :
    Nonempty (Q ≃* Multiplicative ((ZMod p) × (ZMod p))) := by
  classical
  haveI : Finite Q := by
    apply Nat.finite_of_card_ne_zero
    have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
    have : p ^ 2 ≠ 0 := pow_ne_zero 2 hp0
    simpa [hQ] using this
  haveI : Fintype Q := Fintype.ofFinite Q
  letI : CommGroup Q := IsPGroup.commGroupOfCardEqPrimeSq (p := p) (G := Q) hQ
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  haveI : Nontrivial Q :=
    (Finite.one_lt_card_iff_nontrivial).1 (by
      have hp2 : 1 < p ^ 2 := Nat.one_lt_pow (by decide : (2 : ℕ) ≠ 0) hp1
      have hQ' : Fintype.card Q = p ^ 2 := by
        simpa [Nat.card_eq_fintype_card] using hQ
      simpa [hQ'] using hp2)

  have orderOf_eq_p_of_ne_one : ∀ {x : Q}, x ≠ 1 → orderOf x = p := by
    intro x hx1
    have hx_dvd : orderOf x ∣ p ^ 2 := by
      have hx_dvd' : orderOf x ∣ Fintype.card Q := orderOf_dvd_card (x := x)
      have hQ' : Fintype.card Q = p ^ 2 := by
        simpa [Nat.card_eq_fintype_card] using hQ
      simpa [hQ'] using hx_dvd'
    obtain ⟨k, hk_le, hk⟩ :=
      (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 hx_dvd
    cases k with
    | zero =>
        have : orderOf x = 1 := by simpa using hk
        exact (hx1 ((orderOf_eq_one_iff).1 this)).elim
    | succ k1 =>
        cases k1 with
        | zero =>
            simpa using hk
        | succ k2 =>
            have hk2le : k2 ≤ 0 := by
              have hk' : Nat.succ (Nat.succ k2) ≤ Nat.succ (Nat.succ 0) := by
                simpa using hk_le
              have hk'' : Nat.succ k2 ≤ Nat.succ 0 := (Nat.succ_le_succ_iff).1 hk'
              exact (Nat.succ_le_succ_iff).1 hk''
            have hk2eq : k2 = 0 := Nat.eq_zero_of_le_zero hk2le
            subst hk2eq
            have hx_cyc : IsCyclic Q := by
              have hQ' : Fintype.card Q = p ^ 2 := by
                simpa [Nat.card_eq_fintype_card] using hQ
              have hzcard' : Fintype.card (Subgroup.zpowers x) = Fintype.card Q := by
                calc
                  Fintype.card (Subgroup.zpowers x) = orderOf x := by
                    simpa using (Fintype.card_zpowers (x := x))
                  _ = p ^ 2 := by
                    simpa using hk
                  _ = Fintype.card Q := by
                    simpa using hQ'.symm
              have hzcard : Nat.card (Subgroup.zpowers x) = Nat.card Q := by
                simpa [Nat.card_eq_fintype_card] using hzcard'
              have hztop : Subgroup.zpowers x = ⊤ :=
                Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers x) hzcard
              exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨x, hztop⟩
            exact (hnc hx_cyc).elim

  obtain ⟨a, ha1⟩ := exists_ne (1 : Q)
  have hza : Subgroup.zpowers a ≠ ⊤ := by
    intro htop
    apply hnc
    exact (isCyclic_iff_exists_zpowers_eq_top).2 ⟨a, htop⟩
  obtain ⟨b, hbH⟩ := SetLike.exists_not_mem_of_ne_top (Subgroup.zpowers a) hza
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hbH
    simp [hb1]

  let H : Subgroup Q := Subgroup.zpowers a
  let K : Subgroup Q := Subgroup.zpowers b
  have hcardH : Nat.card H = p := by
    have : orderOf a = p := orderOf_eq_p_of_ne_one ha1
    simp [Nat.card_eq_fintype_card, H, Fintype.card_zpowers, this]
  have hcardK : Nat.card K = p := by
    have : orderOf b = p := orderOf_eq_p_of_ne_one hb1
    simp [Nat.card_eq_fintype_card, K, Fintype.card_zpowers, this]

  have hdisj : Disjoint H K := by
    have hbH' : b ∉ H := by simpa [H] using hbH
    have hcardHf : Fintype.card H = p := by
      simpa [Nat.card_eq_fintype_card] using hcardH
    have hdiv : Fintype.card (H ⊓ K : Subgroup Q) ∣ p := by
      have hdiv' : Nat.card (H ⊓ K : Subgroup Q) ∣ Nat.card H :=
        Subgroup.card_dvd_of_le (show H ⊓ K ≤ H from inf_le_left)
      have hdiv'' : Fintype.card (H ⊓ K : Subgroup Q) ∣ Fintype.card H := by
        simpa [Nat.card_eq_fintype_card] using hdiv'
      simpa [hcardHf] using hdiv''
    have hcard_inf :
        Fintype.card (H ⊓ K : Subgroup Q) = 1 ∨ Fintype.card (H ⊓ K : Subgroup Q) = p :=
      (Nat.dvd_prime (Fact.out : Nat.Prime p)).1 hdiv
    have hinf : H ⊓ K = ⊥ := by
      cases hcard_inf with
      | inl h1 =>
          have : Nat.card (H ⊓ K : Subgroup Q) = 1 := by
            simpa [Nat.card_eq_fintype_card] using h1
          exact Subgroup.eq_bot_of_card_eq (H := H ⊓ K) this
      | inr hp' =>
          exfalso
          have hp_nat : Nat.card (H ⊓ K : Subgroup Q) = p := by
            simpa [Nat.card_eq_fintype_card] using hp'
          have hEq1 : H ⊓ K = H := by
            apply Subgroup.eq_of_le_of_card_ge (H := H ⊓ K) (K := H) inf_le_left
            exact le_of_eq (by
              calc
                Nat.card H = p := hcardH
                _ = Nat.card (H ⊓ K : Subgroup Q) := by simpa using hp_nat.symm)
          have hHK : H ≤ K := (inf_eq_left).1 hEq1
          have hEq2 : H = K := by
            apply Subgroup.eq_of_le_of_card_ge (H := H) (K := K) hHK
            exact le_of_eq (by
              calc
                Nat.card K = p := hcardK
                _ = Nat.card H := by simpa using hcardH.symm)
          have hbK : b ∈ K := by
            simp [K]
          have : b ∈ H := by simpa [hEq2] using hbK
          exact hbH' this
    exact disjoint_iff.2 hinf

  have hcard_mul : Nat.card H * Nat.card K = Nat.card Q := by
    have hcardH' : Fintype.card H = p := by
      simpa [Nat.card_eq_fintype_card] using hcardH
    have hcardK' : Fintype.card K = p := by
      simpa [Nat.card_eq_fintype_card] using hcardK
    have hQ' : Fintype.card Q = p ^ 2 := by
      simpa [Nat.card_eq_fintype_card] using hQ
    have hcard_mul' : Fintype.card H * Fintype.card K = Fintype.card Q := by
      simp [hcardH', hcardK', hQ', pow_two]
    simpa [Nat.card_eq_fintype_card] using hcard_mul'

  have hcomp : Subgroup.IsComplement' H K :=
    Subgroup.isComplement'_of_card_mul_and_disjoint (H := H) (K := K) hcard_mul hdisj

  let mulHom : H × K →* Q :=
    { toFun := fun x => (x.1 : Q) * (x.2 : Q)
      map_one' := by simp
      map_mul' := by
        intro x y
        simp [mul_left_comm, mul_comm] }
  have mulHom_bij : Function.Bijective mulHom := by
    simpa [Subgroup.IsComplement', Subgroup.IsComplement, mulHom] using hcomp
  let eHK : (H × K) ≃* Q := MulEquiv.ofBijective mulHom mulHom_bij

  have hcardZ : Nat.card (Multiplicative (ZMod p)) = p := by
    simp
  let eH : H ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (G := H) (G' := Multiplicative (ZMod p)) (p := p) hcardH hcardZ
  let eK : K ≃* Multiplicative (ZMod p) :=
    mulEquivOfPrimeCardEq (G := K) (G' := Multiplicative (ZMod p)) (p := p) hcardK hcardZ
  let eProd : H × K ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p) :=
    MulEquiv.prodCongr eH eK

  refine ⟨(eHK.symm.trans eProd).trans
    (MulEquiv.prodMultiplicative (G := ZMod p) (H := ZMod p)).symm⟩

end QuestionBench.FATEH.q4

/- Prove that if $p$ is a prime and $P$ is a non-abelian group of order $p^3$, then $|Z(P)| = p$
and $P/Z(P) \cong \mathbb{Z}/p\mathbb{Z} \times \mathbb{Z}/p\mathbb{Z}$.-/
theorem nonempty_mulEquiv_zMod_prod_zMod {p : ℕ} [Fact p.Prime] {P : Type} [Group P] (hp : Nat.card P = p ^ 3)
    (h : ∃ (a b : P), a * b ≠ b * a) : Nat.card (Subgroup.center P) = p ∧
    Nonempty ((P ⧸ Subgroup.center P) ≃* Multiplicative ((ZMod p) × (ZMod p))) := by
  classical
  haveI : Finite P := QuestionBench.FATEH.q4.finite_of_card_eq_prime_cube (p := p) hp
  have hZ : Nat.card (Subgroup.center P) = p :=
    QuestionBench.FATEH.q4.card_center_eq_prime (p := p) hp h
  have hquot : Nat.card (P ⧸ Subgroup.center P) = p ^ 2 := by
    have hmul : Nat.card (Subgroup.center P) * (Subgroup.center P).index = Nat.card P :=
      (Subgroup.center P).card_mul_index
    have hmul' : p * (Subgroup.center P).index = p ^ 3 := by
      simpa [hZ, hp] using hmul
    have hp3 : p ^ 3 = p * p ^ 2 := by
      calc
        p ^ 3 = p ^ 2 * p := by simp [pow_succ]
        _ = p * p ^ 2 := by ac_rfl
    have hindex : (Subgroup.center P).index = p ^ 2 := by
      apply Nat.mul_left_cancel (Fact.out : Nat.Prime p).pos
      simpa [hp3] using hmul'
    simpa [Subgroup.index_eq_card] using hindex
  have hnc : ¬ IsCyclic (P ⧸ Subgroup.center P) :=
    QuestionBench.FATEH.q4.not_isCyclic_quot_center (P := P) h
  refine ⟨hZ, ?_⟩
  exact QuestionBench.FATEH.q4.nonempty_mulEquiv_zmod_prod_of_card_eq_prime_sq
    (p := p) (Q := P ⧸ Subgroup.center P) hquot hnc

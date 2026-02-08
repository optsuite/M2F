import Mathlib

open Subgroup

/-!
Helpers for `exists_index_two_of_sylow_two_isCyclic`.

The main proof follows the standard Burnside transfer approach:
build a surjective hom `G →* P ⧸ Q` onto a quotient of order `2`, and take its kernel.
-/

-- A nontrivial Sylow `2`-subgroup has even order.
private lemma two_dvd_card_sylow_two_of_ne_bot {G : Type} [Group G] [Finite G] (P : Sylow 2 G)
    (hP : (P : Subgroup G) ≠ ⊥) : 2 ∣ Nat.card P := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard_ne_one : Nat.card P ≠ 1 := by
    have : (P : Subgroup G) = ⊥ ↔ Nat.card P = 1 := by
      exact (Subgroup.eq_bot_iff_card (H := (P : Subgroup G)))
    exact fun h => hP (this.2 h)
  rcases (P.2.card_eq_or_dvd (p := 2) (G := P)) with h | h
  · exact (hcard_ne_one h).elim
  · exact h

-- If `2 ∣ |G|`, then `2` is the smallest prime factor of `|G|`.
private lemma minFac_card_eq_two_of_sylow_two_ne_bot {G : Type} [Group G] [Finite G]
    (P : Sylow 2 G) (hP : (P : Subgroup G) ≠ ⊥) : (Nat.card G).minFac = 2 := by
  classical
  have htwoP : 2 ∣ Nat.card P := two_dvd_card_sylow_two_of_ne_bot P hP
  have hcard_dvd : Nat.card P ∣ Nat.card G := by
    simpa [Nat.card_eq_fintype_card] using (card_subgroup_dvd_card (P : Subgroup G))
  exact (Nat.minFac_eq_two_iff (Nat.card G)).2 (htwoP.trans hcard_dvd)

-- For a cyclic Sylow `2`-subgroup, Burnside's transfer map `G →* P` is surjective.
private lemma transferSylow_surjective_of_isCyclic {G : Type} [Group G] [Finite G] (P : Sylow 2 G)
    (hp : (Nat.card G).minFac = 2) [IsCyclic P] :
    Function.Surjective
      (MonoidHom.transferSylow P ((inferInstance : IsCyclic P).normalizer_le_centralizer hp)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hnorm : (P : Subgroup G).normalizer ≤ centralizer (P : Set G) :=
    (inferInstance : IsCyclic P).normalizer_le_centralizer hp
  let τ : G →* (P : Subgroup G) := MonoidHom.transferSylow P hnorm
  have hbij : Function.Bijective (τ.restrict (P : Subgroup G)) := by
    simpa [τ] using
      ((MonoidHom.transferSylow_restrict_eq_pow (P := P) (hP := hnorm)).symm ▸
        (P.2.powEquiv' P.not_dvd_index).bijective)
  intro y
  rcases hbij.2 y with ⟨x, hx⟩
  refine ⟨(x : G), ?_⟩
  simpa [τ] using hx

-- A finite cyclic group of even order admits a subgroup of index `2`.
private lemma exists_index_two_subgroup_of_even_cyclic {G : Type} [Group G] [Finite G] [IsCyclic G]
    (hG : 2 ∣ Nat.card G) : ∃ Q : Subgroup G, Q.index = 2 := by
  classical
  let n : ℕ := Nat.card G
  have hnpos : 0 < n := by
    dsimp [n]
    exact (Nat.card_pos (α := G))
  haveI : NeZero n := ⟨hnpos.ne'⟩
  let e : Multiplicative (ZMod n) ≃* G :=
    zmodCyclicMulEquiv (G := G) (inferInstance : IsCyclic G)
  let Q0 : Subgroup (Multiplicative (ZMod n)) :=
    (powMonoidHom 2 : Multiplicative (ZMod n) →* Multiplicative (ZMod n)).range
  have hQ0 : Q0.index = 2 := by
    have hcard : Nat.card (Multiplicative (ZMod n)) = n := by
      simp [Nat.card_eq_fintype_card]
    have htwo : 2 ∣ Nat.card (Multiplicative (ZMod n)) := by
      simpa [hcard, n] using hG
    have hgcd : (Nat.card (Multiplicative (ZMod n))).gcd 2 = 2 :=
      Nat.gcd_eq_right_iff_dvd.2 htwo
    calc
      Q0.index = (Nat.card (Multiplicative (ZMod n))).gcd 2 := by
        simpa [Q0] using
          (IsCyclic.index_powMonoidHom_range (G := Multiplicative (ZMod n)) (d := 2))
      _ = 2 := hgcd
  refine ⟨Subgroup.map (e : Multiplicative (ZMod n) →* G) Q0, ?_⟩
  -- Index is invariant under a group equivalence.
  exact (Subgroup.index_map_equiv (H := Q0) e).trans hQ0

/-- Show that if a Sylow $2$-subgroup of $G$ is nontrivial and cyclic, then $G$ has a subgroup $H$
with $[G:H] =2$. -/
theorem exists_index_two_of_sylow_two_isCyclic {G : Type} [Group G] [Finite G] (P : Sylow 2 G)
    (h1 : P.toSubgroup ≠ ⊥) [IsCyclic P] : ∃ H : Subgroup G, H.index = 2 := by
  classical
  have hPne : (P : Subgroup G) ≠ ⊥ := by simpa using h1
  have hp : (Nat.card G).minFac = 2 := minFac_card_eq_two_of_sylow_two_ne_bot P hPne

  -- Burnside transfer `G →* P` and its quotient by the subgroup of squares.
  set τ : G →* (P : Subgroup G) :=
    MonoidHom.transferSylow P ((inferInstance : IsCyclic P).normalizer_le_centralizer hp)
  have hτ_surj : Function.Surjective τ := by
    simpa [τ] using transferSylow_surjective_of_isCyclic (P := P) hp

  have htwoP : 2 ∣ Nat.card (P : Subgroup G) := by
    simpa using two_dvd_card_sylow_two_of_ne_bot P hPne
  obtain ⟨Q, hQ⟩ :=
    exists_index_two_subgroup_of_even_cyclic (G := (P : Subgroup G)) htwoP

  let π : (P : Subgroup G) →* (P : Subgroup G) ⧸ Q := QuotientGroup.mk' Q
  let φ : G →* (P : Subgroup G) ⧸ Q := π.comp τ
  refine ⟨φ.ker, ?_⟩

  have hφ_surj : Function.Surjective φ := (QuotientGroup.mk'_surjective Q).comp (by
    simpa [φ] using hτ_surj)
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.2 hφ_surj

  calc
    φ.ker.index = Nat.card φ.range := Subgroup.index_ker φ
    _ = Nat.card ((P : Subgroup G) ⧸ Q) := by simp [hrange]
    _ = Q.index := by
      simpa using (Subgroup.index_eq_card (G := (P : Subgroup G)) (H := Q)).symm
    _ = 2 := hQ

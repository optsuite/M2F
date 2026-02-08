import Mathlib

open Polynomial IntermediateField
open scoped Nat

namespace FATEH36

noncomputable section

abbrev poly36 : ℚ[X] := X ^ 4 - X ^ 2 - 1

-- A direct Bezout identity shows `poly36` is coprime to `X`.
lemma poly36_coprime_X : IsCoprime (poly36 : ℚ[X]) X := by
  classical
  refine ⟨(-1 : ℚ[X]), (X ^ 3 - X), ?_⟩
  ring

-- A Bezout identity for `poly36` and `2*X^2-1`, using a unit adjustment by `5`.
lemma poly36_coprime_quad : IsCoprime (poly36 : ℚ[X]) (2 * X ^ 2 - 1) := by
  classical
  let f : ℚ[X] := poly36
  let g : ℚ[X] := 2 * X ^ 2 - 1
  have h : (-4 : ℚ[X]) * f + g ^ 2 = 5 := by
    simp [f, g, poly36]
    ring
  have h5 : IsUnit (5 : ℚ[X]) := by
    have h5' : IsUnit (5 : ℚ) := by
      simp [isUnit_iff_ne_zero]
    exact (Polynomial.isUnit_C (x := (5 : ℚ))).2 h5'
  rcases h5 with ⟨u, hu⟩
  have h' : (-(4 * f) + g ^ 2) = 5 := by
    simpa using h
  refine ⟨(↑(u⁻¹) : ℚ[X]) * (-4 : ℚ[X]), (↑(u⁻¹) : ℚ[X]) * g, ?_⟩
  calc
    (↑(u⁻¹) : ℚ[X]) * (-4 : ℚ[X]) * f + (↑(u⁻¹) : ℚ[X]) * g * g
        = (↑(u⁻¹) : ℚ[X]) * (-(4 * f) + g ^ 2) := by
          simp [mul_add, mul_assoc, mul_left_comm, mul_comm, pow_two]
    _ = (↑(u⁻¹) : ℚ[X]) * 5 := by
          simp [h']
    _ = 1 := by
          simp [hu]

-- Normalize the derivative into a product of the obvious coprime factors.
lemma poly36_derivative : derivative (poly36 : ℚ[X]) = (2 : ℚ[X]) * X * (2 * X ^ 2 - 1) := by
  have h4 : (C (3 : ℚ) + 1 : ℚ[X]) = (4 : ℚ[X]) := by
    calc
      (C (3 : ℚ) + 1 : ℚ[X]) = C ((3 : ℚ) + 1) := by
        simp [C_add]
      _ = (C (4 : ℚ) : ℚ[X]) := by
        norm_num
      _ = (4 : ℚ[X]) := by
        rfl
  have h2 : ((1 : ℚ[X]) + 1) = (2 : ℚ[X]) := by
    calc
      (1 : ℚ[X]) + 1 = C ((1 : ℚ) + 1) := by
        simp [C_add]
      _ = (C (2 : ℚ) : ℚ[X]) := by
        norm_num
      _ = (2 : ℚ[X]) := by
        rfl
  have hderiv : derivative (poly36 : ℚ[X]) = (4 : ℚ[X]) * X ^ 3 - (2 : ℚ[X]) * X := by
    simp [poly36, h4, h2]
  calc
    derivative (poly36 : ℚ[X]) = (4 : ℚ[X]) * X ^ 3 - (2 : ℚ[X]) * X := hderiv
    _ = (2 : ℚ[X]) * X * (2 * X ^ 2 - 1) := by
      ring

lemma poly36_separable : (poly36 : ℚ[X]).Separable := by
  classical
  refine (Polynomial.separable_def (f := (poly36 : ℚ[X]))).2 ?_
  have hX : IsCoprime (poly36 : ℚ[X]) X := poly36_coprime_X
  have hquad : IsCoprime (poly36 : ℚ[X]) (2 * X ^ 2 - 1) := poly36_coprime_quad
  have hprod : IsCoprime (poly36 : ℚ[X]) (X * (2 * X ^ 2 - 1)) :=
    IsCoprime.mul_right hX hquad
  have h2unit : IsUnit (2 : ℚ[X]) := by
    have h2' : IsUnit (2 : ℚ) := by
      simp [isUnit_iff_ne_zero]
    exact (Polynomial.isUnit_C (x := (2 : ℚ))).2 h2'
  have hderiv' : IsCoprime (poly36 : ℚ[X]) ((X * (2 * X ^ 2 - 1)) * (2 : ℚ[X])) :=
    (isCoprime_mul_unit_right_right (x := (2 : ℚ[X])) (y := (poly36 : ℚ[X]))
      (z := (X * (2 * X ^ 2 - 1))) h2unit).mpr hprod
  have hderiv_eq : (X * (2 * X ^ 2 - 1)) * (2 : ℚ[X]) = derivative (poly36 : ℚ[X]) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (poly36_derivative.symm)
  simpa [hderiv_eq] using hderiv'

-- `poly36` is a genuine quartic; we use this to produce roots in its splitting field later.
lemma poly36_natDegree : (poly36 : ℚ[X]).natDegree = 4 := by
  have hp : ((X : ℚ[X]) ^ 4 - 1).natDegree = 4 := by
    simpa using (Polynomial.natDegree_X_pow_sub_C (n := 4) (r := (1 : ℚ)))
  have hq : (-(X : ℚ[X]) ^ 2).natDegree = 2 := by
    simp
  have hlt : (-(X : ℚ[X]) ^ 2).natDegree < ((X : ℚ[X]) ^ 4 - 1).natDegree := by
    simp [hp, hq]
  have hpoly : (poly36 : ℚ[X]) = ((X : ℚ[X]) ^ 4 - 1) + (-(X : ℚ[X]) ^ 2) := by
    ring
  calc
    (poly36 : ℚ[X]).natDegree =
        (((X : ℚ[X]) ^ 4 - 1) + (-(X : ℚ[X]) ^ 2)).natDegree := by
          simp [hpoly]
    _ = ((X : ℚ[X]) ^ 4 - 1).natDegree := by
          simpa using
            (Polynomial.natDegree_add_eq_left_of_natDegree_lt
              (p := (X : ℚ[X]) ^ 4 - 1) (q := (-(X : ℚ[X]) ^ 2)) hlt)
    _ = 4 := hp

-- The root set of `poly36` in its splitting field has cardinality 4.
lemma poly36_rootSet_card :
    Fintype.card (poly36.rootSet poly36.SplittingField) = 4 := by
  classical
  have hsep : (poly36 : ℚ[X]).Separable := poly36_separable
  have hcard :
      Fintype.card (poly36.rootSet poly36.SplittingField) = (poly36 : ℚ[X]).natDegree := by
    simpa using
      (Polynomial.card_rootSet_eq_natDegree (K := poly36.SplittingField) hsep
        (SplittingField.splits (poly36)))
  simpa [poly36_natDegree] using hcard

lemma poly36_ne_zero : (poly36 : ℚ[X]) ≠ 0 := by
  intro h
  have h' : (0 : ℕ) = 4 := by
    simpa [h] using poly36_natDegree
  have h0 : (0 : ℕ) ≠ 4 := by decide
  exact h0 h'

lemma poly36_aeval_neg {K : Type*} [Field K] [Algebra ℚ K] (x : K) :
    aeval (-x) (poly36 : ℚ[X]) = aeval x (poly36 : ℚ[X]) := by
  simp [poly36]
  ring

-- Negation preserves the root set of `poly36` in any field extension.
lemma poly36_rootSet_neg_mem {K : Type*} [Field K] [Algebra ℚ K] {x : K} :
    x ∈ poly36.rootSet K → -x ∈ poly36.rootSet K := by
  classical
  intro hx
  have hx' : aeval x (poly36 : ℚ[X]) = 0 :=
    (mem_rootSet_of_ne (p := poly36) (S := K) poly36_ne_zero).1 hx
  have hxneg : aeval (-x) (poly36 : ℚ[X]) = 0 := by
    calc
      aeval (-x) (poly36 : ℚ[X]) = aeval x (poly36 : ℚ[X]) := poly36_aeval_neg (x := x)
      _ = 0 := hx'
  exact (mem_rootSet_of_ne (p := poly36) (S := K) poly36_ne_zero).2 hxneg

-- Negation gives an involutive permutation of the root set.
def negPerm_rootSet (K : Type*) [Field K] [Algebra ℚ K] :
    Equiv.Perm (poly36.rootSet K) :=
  { toFun := fun x => ⟨-x.1, poly36_rootSet_neg_mem (K := K) x.property⟩
    invFun := fun x => ⟨-x.1, poly36_rootSet_neg_mem (K := K) x.property⟩
    left_inv := by
      intro x
      ext
      simp
    right_inv := by
      intro x
      ext
      simp }

-- The Galois action on the root set commutes with negation.
lemma galActionHom_comm_negPerm_rootSet
    (K : Type*) [Field K] [Algebra ℚ K]
    [Fact ((poly36.map (algebraMap ℚ K)).Splits)] :
    let s₀ := negPerm_rootSet (K := K)
    ∀ g : poly36.Gal,
      (Polynomial.Gal.galActionHom poly36 K g) * s₀ =
        s₀ * (Polynomial.Gal.galActionHom poly36 K g) := by
  classical
  intro s₀ g
  ext x
  set r := Gal.rootsEquivRoots poly36 K
  have hneg_r :
      ∀ y : poly36.rootSet poly36.SplittingField,
        (r ⟨-y.1, poly36_rootSet_neg_mem (K := poly36.SplittingField) y.property⟩ : K) =
          -(r y : K) := by
    intro y
    simp [r, Gal.rootsEquivRoots, Gal.mapRoots]
  have hsymm :
      r.symm ⟨-↑x, poly36_rootSet_neg_mem (K := K) x.property⟩ =
        ⟨-(r.symm x).1,
          poly36_rootSet_neg_mem (K := poly36.SplittingField) (r.symm x).property⟩ := by
    apply (Equiv.injective r)
    apply Subtype.ext
    simp [hneg_r, r]
  have hsmul_neg :
      g • (⟨-((r.symm x).1),
        poly36_rootSet_neg_mem (K := poly36.SplittingField) (r.symm x).property⟩ :
          poly36.rootSet poly36.SplittingField) =
        (⟨-((g • r.symm x).1),
          poly36_rootSet_neg_mem (K := poly36.SplittingField) (g • r.symm x).property⟩ :
            poly36.rootSet poly36.SplittingField) := by
    ext
    change g (-((r.symm x).1)) = -g (r.symm x).1
    exact map_neg (g : poly36.SplittingField →+* poly36.SplittingField) (r.symm x).1
  have hneg_r' :
      (r (g • (⟨-((r.symm x).1),
        poly36_rootSet_neg_mem (K := poly36.SplittingField) (r.symm x).property⟩ :
          poly36.rootSet poly36.SplittingField)) : K) =
        - (r (g • r.symm x) : K) := by
    simpa [hsmul_neg] using (hneg_r (y := g • r.symm x))
  simpa [s₀, negPerm_rootSet, Equiv.Perm.mul_apply, Polynomial.Gal.galActionHom,
    MulAction.toPermHom, MulAction.toPerm, Polynomial.Gal.smul_def, hsymm, r] using hneg_r'

lemma natCard_intermediateField_eq_natCard_subgroup_galois
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K] :
    Nat.card (IntermediateField ℚ K) = Nat.card (Subgroup Gal(K/ℚ)) := by
  classical
  simpa using
    (Nat.card_congr (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := K)).toEquiv)

-- Transport subgroup counts along a group isomorphism.
lemma natCard_subgroup_congr_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (Subgroup G) = Nat.card (Subgroup H) := by
  classical
  simpa using (Nat.card_congr (MulEquiv.mapSubgroup e).toEquiv)

-- If a group is isomorphic to one with 10 subgroups, then it also has 10 subgroups.
lemma natCard_subgroup_eq_ten_of_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (hH : Nat.card (Subgroup H) = 10) :
    Nat.card (Subgroup G) = 10 := by
  classical
  calc
    Nat.card (Subgroup G) = Nat.card (Subgroup H) := natCard_subgroup_congr_mulEquiv e
    _ = 10 := hH

lemma dihedralGroup_four_card : Nat.card (DihedralGroup 4) = 8 := by
  simpa using (DihedralGroup.nat_card (n := 4))

lemma dihedralGroup_four_orderOf_r_one :
    orderOf (DihedralGroup.r (1 : ZMod 4) : DihedralGroup 4) = 4 := by
  exact (DihedralGroup.orderOf_r_one (n := 4))

lemma dihedralGroup_four_orderOf_r_two :
    orderOf (DihedralGroup.r (2 : ZMod 4) : DihedralGroup 4) = 2 := by
  simpa using (DihedralGroup.orderOf_r (n := 4) (i := (2 : ZMod 4)))

lemma dihedralGroup_four_orderOf_sr (i : ZMod 4) :
    orderOf (DihedralGroup.sr i : DihedralGroup 4) = 2 := by
  exact (DihedralGroup.orderOf_sr (n := 4) i)

section FinsetSubgroup

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

-- A computable subgroup predicate on finsets.
def isSubgroupFinset (s : Finset G) : Prop :=
  (1 ∈ s) ∧
    (s.product s).image (fun x => x.1 * x.2) ⊆ s ∧
    s.image (fun x => x⁻¹) ⊆ s

instance (s : Finset G) : Decidable (isSubgroupFinset (G := G) s) := by
  unfold isSubgroupFinset
  infer_instance

-- Map a subgroup to its element finset (via filtering univ).
def subgroupToFinset (H : Subgroup G) : Finset G := by
  classical
  exact Finset.univ.filter (fun x => x ∈ H)

omit [DecidableEq G] in
lemma mem_subgroupToFinset {H : Subgroup G} {x : G} :
    x ∈ subgroupToFinset (G := G) H ↔ x ∈ H := by
  classical
  simp [subgroupToFinset]

lemma isSubgroupFinset_subgroupToFinset (H : Subgroup G) :
    isSubgroupFinset (G := G) (subgroupToFinset (G := G) H) := by
  classical
  refine ⟨?one, ?mul, ?inv⟩
  · simp [mem_subgroupToFinset, H.one_mem]
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    rcases Finset.mem_product.mp hp with ⟨ha, hb⟩
    have ha' : p.1 ∈ H := (mem_subgroupToFinset (G := G) (H := H)).1 ha
    have hb' : p.2 ∈ H := (mem_subgroupToFinset (G := G) (H := H)).1 hb
    have : p.1 * p.2 ∈ H := H.mul_mem ha' hb'
    exact (mem_subgroupToFinset (G := G) (H := H)).2 this
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨a, ha, rfl⟩
    have ha' : a ∈ H := (mem_subgroupToFinset (G := G) (H := H)).1 ha
    have : a⁻¹ ∈ H := H.inv_mem ha'
    exact (mem_subgroupToFinset (G := G) (H := H)).2 this

-- Build a subgroup from a finset satisfying the subgroup conditions.
def subgroupOfFinset (s : Finset G) (hs : isSubgroupFinset (G := G) s) : Subgroup G :=
  { carrier := {x | x ∈ s}
    one_mem' := by
      simpa using hs.1
    mul_mem' := by
      intro a b ha hb
      have hmem : (a, b) ∈ s.product s := by
        exact Finset.mem_product.mpr ⟨ha, hb⟩
      have : a * b ∈ (s.product s).image (fun x => x.1 * x.2) :=
        Finset.mem_image.mpr ⟨(a, b), hmem, rfl⟩
      exact hs.2.1 this
    inv_mem' := by
      intro a ha
      have : a⁻¹ ∈ s.image (fun x => x⁻¹) :=
        Finset.mem_image.mpr ⟨a, ha, rfl⟩
      exact hs.2.2 this }

lemma subgroupToFinset_subgroupOfFinset (s : Finset G) (hs : isSubgroupFinset (G := G) s) :
    subgroupToFinset (G := G) (subgroupOfFinset (G := G) s hs) = s := by
  classical
  ext x
  simp [subgroupToFinset, subgroupOfFinset]

lemma subgroupOfFinset_subgroupToFinset (H : Subgroup G) :
    subgroupOfFinset (G := G) (subgroupToFinset (G := G) H)
      (isSubgroupFinset_subgroupToFinset (G := G) H) = H := by
  classical
  ext x
  simp [subgroupToFinset, subgroupOfFinset]

-- Subgroups correspond to finsets satisfying the subgroup predicate.
def subgroupEquivFinset : Subgroup G ≃ {s : Finset G // isSubgroupFinset (G := G) s} :=
  { toFun := fun H =>
      ⟨subgroupToFinset (G := G) H, isSubgroupFinset_subgroupToFinset (G := G) H⟩
    invFun := fun s => subgroupOfFinset (G := G) s.1 s.2
    left_inv := by
      intro H
      simpa using (subgroupOfFinset_subgroupToFinset (G := G) H)
    right_inv := by
      intro s
      apply Subtype.ext
      simpa using (subgroupToFinset_subgroupOfFinset (G := G) s.1 s.2) }

end FinsetSubgroup

lemma natCard_subgroup_dihedralGroup_four : Nat.card (Subgroup (DihedralGroup 4)) = 10 := by
  classical
  have h :
      Nat.card (Subgroup (DihedralGroup 4)) =
        Nat.card {s : Finset (DihedralGroup 4) // isSubgroupFinset (G := DihedralGroup 4) s} := by
    simpa using
      (Nat.card_congr (subgroupEquivFinset (G := DihedralGroup 4)))
  have hcard :
      Nat.card {s : Finset (DihedralGroup 4) // isSubgroupFinset (G := DihedralGroup 4) s} = 10 := by
    simpa [Nat.card_eq_fintype_card] using
      (by native_decide :
        Fintype.card {s : Finset (DihedralGroup 4) // isSubgroupFinset (G := DihedralGroup 4) s} = 10)
  exact h.trans hcard

-- The centralizer of a fixed-point-free involution in `S₄` has order 8.
lemma natCard_centralizer_eq_eight_of_fixedPointFree_involution_fin4
    (s : Equiv.Perm (Fin 4)) (hs : s * s = 1) (hsfix : ∀ i, s i ≠ i) :
    Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) = 8 := by
  classical
  have hs_ne : s ≠ 1 := by
    intro h
    have h0 := hsfix (0 : Fin 4)
    apply h0
    simp [h]
  have hs_pow : s ^ 2 = 1 := by
    simpa [pow_two] using hs
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hs_order : orderOf s = 2 := by
    simpa using (orderOf_eq_prime (x := s) (p := 2) hs_pow hs_ne)
  have hprime : (orderOf s).Prime := by
    simpa [hs_order] using (show Nat.Prime 2 from by decide)
  rcases Equiv.Perm.cycleType_prime_order (σ := s) hprime with ⟨n, hcycle⟩
  have hfixed : Fintype.card (Function.fixedPoints s) = 0 := by
    refine (Fintype.card_eq_zero_iff).2 ?_
    refine ⟨?_⟩
    intro x
    exact (hsfix x.1) x.2
  have hsum_ge : 4 ≤ s.cycleType.sum := by
    have hcard' : 4 - s.cycleType.sum = 0 := by
      have hcard : 0 = 4 - s.cycleType.sum := by
        simpa [hfixed] using (Equiv.Perm.card_fixedPoints (σ := s))
      exact hcard.symm
    exact (Nat.sub_eq_zero_iff_le).1 hcard'
  have hsum_le : s.cycleType.sum ≤ 4 := by
    simpa using (Equiv.Perm.sum_cycleType_le (σ := s))
  have hsum : s.cycleType.sum = 4 := Nat.le_antisymm hsum_le hsum_ge
  have hsum' : s.cycleType.sum = 2 * (n + 1) := by
    rw [hcycle, Multiset.sum_replicate]
    simp [hs_order, Nat.mul_comm]
  have hlen : n + 1 = 2 := by
    apply Nat.mul_left_cancel (by decide : 0 < (2 : ℕ))
    calc
      2 * (n + 1) = s.cycleType.sum := by symm; exact hsum'
      _ = 4 := hsum
      _ = 2 * 2 := by simp
  have hcycle' : s.cycleType = Multiset.replicate 2 2 := by
    simpa [hs_order, hlen] using hcycle
  have hcard :
      Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) =
        (4 - s.cycleType.sum)! * s.cycleType.prod *
          (∏ n ∈ s.cycleType.toFinset, (s.cycleType.count n)!) := by
    simpa using (Equiv.Perm.nat_card_centralizer (g := s))
  have hprod : s.cycleType.prod = 4 := by
    simp [hcycle']
  have htoFinset : s.cycleType.toFinset = {2} := by
    ext n
    simp [hcycle']
  have hcount : s.cycleType.count 2 = 2 := by
    simp [hcycle']
  have hprodcount :
      (∏ n ∈ s.cycleType.toFinset, (s.cycleType.count n)!) = 2 := by
    simp [htoFinset, hcount]
  calc
    Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) =
        (4 - s.cycleType.sum)! * s.cycleType.prod *
          (∏ n ∈ s.cycleType.toFinset, (s.cycleType.count n)!) := hcard
    _ = (4 - 4)! * 4 * 2 := by simp [hsum, hprod, hprodcount]
    _ = 8 := by simp

-- Fixed-point-free involutions in `S₄` all have cycle type `2,2`.
lemma cycleType_eq_two_two_of_fixedPointFree_involution_fin4
    (s : Equiv.Perm (Fin 4)) (hs : s * s = 1) (hsfix : ∀ i, s i ≠ i) :
    s.cycleType = Multiset.replicate 2 2 := by
  classical
  have hs_ne : s ≠ 1 := by
    intro h
    have h0 := hsfix (0 : Fin 4)
    apply h0
    simp [h]
  have hs_pow : s ^ 2 = 1 := by
    simpa [pow_two] using hs
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hs_order : orderOf s = 2 := by
    simpa using (orderOf_eq_prime (x := s) (p := 2) hs_pow hs_ne)
  have hprime : (orderOf s).Prime := by
    simpa [hs_order] using (show Nat.Prime 2 from by decide)
  rcases Equiv.Perm.cycleType_prime_order (σ := s) hprime with ⟨n, hcycle⟩
  have hfixed : Fintype.card (Function.fixedPoints s) = 0 := by
    refine (Fintype.card_eq_zero_iff).2 ?_
    refine ⟨?_⟩
    intro x
    exact (hsfix x.1) x.2
  have hsum_ge : 4 ≤ s.cycleType.sum := by
    have hcard' : 4 - s.cycleType.sum = 0 := by
      have hcard : 0 = 4 - s.cycleType.sum := by
        simpa [hfixed] using (Equiv.Perm.card_fixedPoints (σ := s))
      exact hcard.symm
    exact (Nat.sub_eq_zero_iff_le).1 hcard'
  have hsum_le : s.cycleType.sum ≤ 4 := by
    simpa using (Equiv.Perm.sum_cycleType_le (σ := s))
  have hsum : s.cycleType.sum = 4 := Nat.le_antisymm hsum_le hsum_ge
  have hsum' : s.cycleType.sum = 2 * (n + 1) := by
    rw [hcycle, Multiset.sum_replicate]
    simp [hs_order, Nat.mul_comm]
  have hlen : n + 1 = 2 := by
    apply Nat.mul_left_cancel (by decide : 0 < (2 : ℕ))
    calc
      2 * (n + 1) = s.cycleType.sum := by symm; exact hsum'
      _ = 4 := hsum
      _ = 2 * 2 := by simp
  simpa [hs_order, hlen] using hcycle

-- A faithful dihedral action on the square, encoded on `ZMod 4`.
noncomputable def dihedralPerm : DihedralGroup 4 → Equiv.Perm (ZMod 4)
  | DihedralGroup.r i => Equiv.addLeft (-i)
  | DihedralGroup.sr i => Equiv.subLeft i

noncomputable def dihedralPermHom : DihedralGroup 4 →* Equiv.Perm (ZMod 4) where
  toFun := dihedralPerm
  map_one' := by
    ext x
    change dihedralPerm (DihedralGroup.r 0) x = x
    simp [dihedralPerm]
  map_mul' := by
    intro a b
    cases a <;> cases b <;>
      ext x <;> simp [dihedralPerm, add_assoc, add_comm, add_left_comm, sub_eq_add_neg]

-- The dihedral action on `ZMod 4` is faithful.
lemma dihedralPermHom_injective : Function.Injective dihedralPermHom := by
  intro a b h
  cases a <;> cases b
  ·
    have h0 := congrArg (fun f => f 0) h
    simp [dihedralPermHom, dihedralPerm] at h0
    simp [h0]
  ·
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp [dihedralPermHom, dihedralPerm, sub_eq_add_neg] at h0 h1
    have h1' := h1
    simp [h0] at h1'
    have h1'' : (1 : ZMod 4) = -1 := by
      simpa [eq_comm] using h1'
    exfalso
    exact (by decide : (1 : ZMod 4) ≠ -1) h1''
  ·
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp [dihedralPermHom, dihedralPerm, sub_eq_add_neg] at h0 h1
    have h1' := h1
    simp [h0] at h1'
    have h1'' : (1 : ZMod 4) = -1 := by
      simpa [eq_comm] using h1'
    exfalso
    exact (by decide : (1 : ZMod 4) ≠ -1) h1''
  ·
    have h0 := congrArg (fun f => f 0) h
    simp [dihedralPermHom, dihedralPerm, sub_eq_add_neg] at h0
    simp [h0]

-- A fixed choice of the standard double transposition in `S₄`.
noncomputable def eStd : ZMod 4 ≃ Fin 4 := Fintype.equivFinOfCardEq (by simp)
noncomputable def sStd : Equiv.Perm (Fin 4) :=
  eStd.permCongr (Equiv.addLeft (2 : ZMod 4))

lemma sStd_mul_self : sStd * sStd = 1 := by
  classical
  have h :
      (Equiv.addLeft (2 : ZMod 4)) * (Equiv.addLeft (2 : ZMod 4)) = 1 := by
    ext x
    have h2 : (2 : ZMod 4) + 2 = 0 := by decide
    change (2 : ZMod 4) + (2 + x) = x
    calc
      (2 : ZMod 4) + (2 + x) = (2 + 2) + x := by ac_rfl
      _ = x := by simp [h2]
  have h1 : eStd.permCongr (1 : Equiv.Perm (ZMod 4)) = (1 : Equiv.Perm (Fin 4)) := by
    ext i
    simp [Equiv.permCongr_apply]
  simpa [sStd, Equiv.permCongr_mul, h1] using
    congrArg (fun t => eStd.permCongr t) h

lemma sStd_no_fixed : ∀ i : Fin 4, sStd i ≠ i := by
  classical
  intro i hi
  have hi' :
      (Equiv.addLeft (2 : ZMod 4)) (eStd.symm i) = eStd.symm i := by
    apply eStd.injective
    simpa [sStd, Equiv.permCongr_apply] using hi
  have htwo : (2 : ZMod 4) = 0 := by
    have := congrArg (fun t => t - eStd.symm i) hi'
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
  exact (by decide : (2 : ZMod 4) ≠ 0) htwo

-- The centralizer of the standard double transposition is dihedral.
lemma centralizer_std_mulEquiv_dihedralGroup_four :
    Nonempty (Subgroup.centralizer ({sStd} : Set (Equiv.Perm (Fin 4))) ≃* DihedralGroup 4) := by
  classical
  let g : DihedralGroup 4 →* Equiv.Perm (Fin 4) :=
    (eStd.permCongrHom.toMonoidHom).comp dihedralPermHom
  have hcomm :
      ∀ a, g a * sStd = sStd * g a := by
    intro a
    -- Work in `ZMod 4`, then transport via `permCongr`.
    have hcomm_zmod :
        dihedralPermHom a * (Equiv.addLeft (2 : ZMod 4)) =
          (Equiv.addLeft (2 : ZMod 4)) * dihedralPermHom a := by
      cases a with
      | r i =>
          ext x
          simp [dihedralPermHom, dihedralPerm, Equiv.addLeft, add_assoc, add_comm, add_left_comm]
        | sr i =>
            ext x
            have h2 : (-2 : ZMod 4) = 2 := by decide
            simp [dihedralPermHom, dihedralPerm, Equiv.addLeft, Equiv.subLeft, sub_eq_add_neg,
            add_assoc, add_comm, h2]
    simpa [g, sStd, Equiv.permCongr_mul] using
      congrArg (fun t => eStd.permCongr t) hcomm_zmod
  let g' :
      DihedralGroup 4 →* Subgroup.centralizer ({sStd} : Set (Equiv.Perm (Fin 4))) :=
    g.codRestrict _ (by
      intro a
      exact (Subgroup.mem_centralizer_singleton_iff).2 (hcomm a))
  have hg_inj : Function.Injective g' := by
    intro a b hab
    apply dihedralPermHom_injective
    have hab' :
        eStd.permCongrHom (dihedralPermHom a) = eStd.permCongrHom (dihedralPermHom b) := by
      have hab'' := congrArg Subtype.val hab
      simpa [g, g'] using hab''
    exact eStd.permCongrHom.injective hab'
  have hcard :
      Fintype.card (DihedralGroup 4) =
        Fintype.card (Subgroup.centralizer ({sStd} : Set (Equiv.Perm (Fin 4)))) := by
    have h1 : Nat.card (DihedralGroup 4) = 8 := dihedralGroup_four_card
    have h2 :
        Nat.card (Subgroup.centralizer ({sStd} : Set (Equiv.Perm (Fin 4)))) = 8 := by
      exact natCard_centralizer_eq_eight_of_fixedPointFree_involution_fin4
        sStd sStd_mul_self sStd_no_fixed
    have h1' : Fintype.card (DihedralGroup 4) = 8 := by
      simpa [Nat.card_eq_fintype_card] using h1
    have h2' :
        Fintype.card (Subgroup.centralizer ({sStd} : Set (Equiv.Perm (Fin 4)))) = 8 := by
      simpa [Nat.card_eq_fintype_card] using h2
    simp [h1', h2']
  have hbij : Function.Bijective g' := by
    exact (Fintype.bijective_iff_injective_and_card _).2 ⟨hg_inj, hcard⟩
  exact ⟨(MulEquiv.ofBijective g' hbij).symm⟩

-- Any fixed-point-free involution has centralizer `D₄` via conjugation.
lemma nonempty_centralizer_mulEquiv_dihedralGroup_four_fin4
    (s : Equiv.Perm (Fin 4)) (hs : s * s = 1) (hsfix : ∀ i, s i ≠ i) :
    Nonempty (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4))) ≃* DihedralGroup 4) := by
  classical
  have hcycle_s :
      s.cycleType = Multiset.replicate 2 2 :=
    cycleType_eq_two_two_of_fixedPointFree_involution_fin4 s hs hsfix
  have hcycle_std :
      sStd.cycleType = Multiset.replicate 2 2 :=
    cycleType_eq_two_two_of_fixedPointFree_involution_fin4 sStd sStd_mul_self sStd_no_fixed
  have hconj : IsConj s sStd := by
    refine (Equiv.Perm.isConj_iff_cycleType_eq).2 ?_
    simp [hcycle_s, hcycle_std]
  rcases hconj with ⟨c, hc⟩
  have hc' : (c : Equiv.Perm (Fin 4)) * s * (c : Equiv.Perm (Fin 4))⁻¹ = sStd := by
    have hc'' : (c : Equiv.Perm (Fin 4)) * s = sStd * (c : Equiv.Perm (Fin 4)) := by
      have hc' := hc
      simp [SemiconjBy] at hc'
      exact hc'
    calc
      (c : Equiv.Perm (Fin 4)) * s * (c : Equiv.Perm (Fin 4))⁻¹
          = (sStd * (c : Equiv.Perm (Fin 4))) * (c : Equiv.Perm (Fin 4))⁻¹ := by
              simp [hc'', mul_assoc]
      _ = sStd := by simp [mul_assoc]
  -- Conjugation transports centralizers.
  let conj :
      Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4))) ≃*
        Subgroup.centralizer ({sStd} : Set (Equiv.Perm (Fin 4))) :=
    { toFun := fun g => ⟨c * g.1 * c⁻¹, by
        have hg : g.1 * s = s * g.1 :=
          (Subgroup.mem_centralizer_singleton_iff).1 g.property
        -- Use `hc : c * s * c⁻¹ = sStd`.
        refine (Subgroup.mem_centralizer_singleton_iff).2 ?_
        calc
          (c * g.1 * c⁻¹) * sStd
              = c * g.1 * c⁻¹ * (c * s * c⁻¹) := by simp [hc', mul_assoc]
          _ = c * g.1 * s * c⁻¹ := by
                simp [mul_assoc]
          _ = c * s * g.1 * c⁻¹ := by
                simp [hg, mul_assoc]
          _ = (c * s * c⁻¹) * (c * g.1 * c⁻¹) := by
                simp [mul_assoc]
          _ = sStd * (c * g.1 * c⁻¹) := by simp [hc', mul_assoc] ⟩
      invFun := fun g => ⟨c⁻¹ * g.1 * c, by
        have hg : g.1 * sStd = sStd * g.1 :=
          (Subgroup.mem_centralizer_singleton_iff).1 g.property
        have hs' : s = (c : Equiv.Perm (Fin 4))⁻¹ * sStd * (c : Equiv.Perm (Fin 4)) := by
          have := congrArg
            (fun t => (c : Equiv.Perm (Fin 4))⁻¹ * t * (c : Equiv.Perm (Fin 4))) hc'
          simp [mul_assoc] at this
          exact this
        refine (Subgroup.mem_centralizer_singleton_iff).2 ?_
        calc
          (c⁻¹ * g.1 * c) * s
              = (c⁻¹ * g.1 * c) * ((c : Equiv.Perm (Fin 4))⁻¹ * sStd * (c : Equiv.Perm (Fin 4))) := by
                  simp [hs']
          _ = c⁻¹ * g.1 * sStd * c := by
                simp [mul_assoc]
          _ = c⁻¹ * sStd * g.1 * c := by
                simp [hg, mul_assoc]
          _ = ((c : Equiv.Perm (Fin 4))⁻¹ * sStd * (c : Equiv.Perm (Fin 4))) *
                (c⁻¹ * g.1 * c) := by
                  simp [mul_assoc]
          _ = s * (c⁻¹ * g.1 * c) := by
                simp [hs'] ⟩
      left_inv := by
        intro g
        ext
        simp [mul_assoc]
      right_inv := by
        intro g
        ext
        simp [mul_assoc]
      map_mul' := by
        intro g h
        ext
        simp [mul_assoc] }
  rcases centralizer_std_mulEquiv_dihedralGroup_four with ⟨e⟩
  exact ⟨conj.trans e⟩

-- A quadratic tower `ℚ ⊂ ℚ(√5) ⊂ ℚ(√5, √u) ⊂ ℚ(√5, √u, i)` of degree 8.
noncomputable abbrev aux_q : ℚ[X] := X ^ 2 - X - 1
abbrev aux_F : Type := AdjoinRoot aux_q
noncomputable abbrev aux_u : aux_F := AdjoinRoot.root aux_q
noncomputable abbrev aux_r : aux_F[X] := X ^ 2 - C aux_u
abbrev aux_K : Type := AdjoinRoot aux_r
noncomputable abbrev aux_a : aux_K := AdjoinRoot.root aux_r
noncomputable abbrev aux_s : aux_K[X] := X ^ 2 - C (-1 : aux_K)
abbrev aux_E : Type := AdjoinRoot aux_s
noncomputable abbrev aux_i : aux_E := AdjoinRoot.root aux_s

-- Basic facts about `aux_q`, used to control norms and irreducibility.
lemma aux_q_monic : aux_q.Monic := by
  have hdeg : (X + 1 : ℚ[X]).degree < (2 : ℕ) := by
    have hdeg : (X + 1 : ℚ[X]).degree = 1 := by
      simpa using (degree_X_add_C (a := (1 : ℚ)))
    simp [hdeg]
  have hmonic : (X ^ 2 - (X + 1) : ℚ[X]).Monic := by
    simpa using (monic_X_pow_sub (p := (X + 1 : ℚ[X])) (n := 2) hdeg)
  have haux : (aux_q : ℚ[X]) = X ^ 2 - (X + 1) := by
    ring
  simpa [haux] using hmonic

lemma aux_q_natDegree : aux_q.natDegree = 2 := by
  simpa [aux_q, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (Polynomial.natDegree_quadratic
      (a := (1 : ℚ)) (b := (-1 : ℚ)) (c := (-1 : ℚ)) (ha := one_ne_zero))

lemma aux_q_irreducible : Irreducible aux_q := by
  simpa [aux_q] using
    (X_pow_sub_X_sub_one_irreducible_rat (n := 2) (by decide : (2 : ℕ) ≠ 1))

-- The norm of `aux_u` over ℚ is `-1`, so `aux_u` is not a square in `aux_F`.
lemma aux_u_norm : Algebra.norm ℚ (S := aux_F) aux_u = (-1 : ℚ) := by
  classical
  have hq0 : aux_q ≠ 0 := aux_q_monic.ne_zero
  let pb := AdjoinRoot.powerBasis (K := ℚ) (f := aux_q) hq0
  have hmin : minpoly ℚ pb.gen = aux_q := by
    have hmonic : aux_q.Monic := aux_q_monic
    simpa [pb] using (AdjoinRoot.minpoly_powerBasis_gen_of_monic (K := ℚ) (f := aux_q) hmonic)
  have hmin' : minpoly ℚ aux_u = aux_q := by
    simpa [pb] using hmin
  have hnorm := (Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (R := ℚ) (S := aux_F) pb)
  have hnorm' :
      Algebra.norm ℚ (S := aux_F) aux_u =
        (-1 : ℚ) ^ aux_q.natDegree * (minpoly ℚ aux_u).coeff 0 := by
    simpa [pb] using hnorm
  calc
    Algebra.norm ℚ (S := aux_F) aux_u = -(-1 : ℚ) ^ aux_q.natDegree := by
      simpa [hmin', aux_q] using hnorm'
    _ = (-1 : ℚ) := by
      simp [aux_q_natDegree]

lemma aux_r_irreducible : Irreducible aux_r := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  letI : Field aux_F := by infer_instance
  have hnosq : ∀ b : aux_F, b ^ 2 ≠ (aux_u : aux_F) := by
    intro b hb
    have hnorm_sq :
        Algebra.norm ℚ (S := aux_F) (b ^ 2) =
          (Algebra.norm ℚ (S := aux_F) b) ^ 2 := by
      simp [map_pow]
    have hnorm_eq : (Algebra.norm ℚ (S := aux_F) b) ^ 2 = (-1 : ℚ) := by
      calc
        (Algebra.norm ℚ (S := aux_F) b) ^ 2 = Algebra.norm ℚ (S := aux_F) (b ^ 2) := by
          symm; exact hnorm_sq
        _ = Algebra.norm ℚ (S := aux_F) aux_u := by
          simp [hb]
        _ = (-1 : ℚ) := aux_u_norm
    have hnonneg : (0 : ℚ) ≤ (Algebra.norm ℚ (S := aux_F) b) ^ 2 := by nlinarith
    have : (0 : ℚ) ≤ (-1 : ℚ) := by
      have hnonneg' := hnonneg
      simp [hnorm_eq] at hnonneg'
      exact hnonneg'
    nlinarith
  have hprime : (2 : ℕ).Prime := by decide
  simpa [aux_r] using
    (X_pow_sub_C_irreducible_of_prime (K := aux_F) (p := 2) hprime (a := aux_u) hnosq)

-- A concrete real embedding for the quadratic tower.
set_option linter.deprecated false in
noncomputable def aux_F_to_real : aux_F →ₐ[ℚ] ℝ :=
  AdjoinRoot.liftHom (f := aux_q) ((1 + Real.sqrt 5) / 2) (by simp [aux_q])

set_option linter.deprecated false in
lemma aux_F_to_real_aux_u : aux_F_to_real aux_u = (1 + Real.sqrt 5) / 2 := by
  simp [aux_F_to_real, aux_u, AdjoinRoot.liftHom_root]

noncomputable def aux_K_to_real : aux_K →ₐ[ℚ] ℝ := by
  let uR : ℝ := aux_F_to_real aux_u
  let aR : ℝ := Real.sqrt uR
  have hnonneg : 0 ≤ uR := by
    dsimp [uR]
    rw [aux_F_to_real_aux_u]
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  have hsqrt : aR ^ 2 = uR := by
    simpa [aR, pow_two] using (Real.mul_self_sqrt hnonneg)
  refine AdjoinRoot.liftAlgHom (p := aux_r) (S := ℚ) (i := aux_F_to_real) aR ?_
  calc
    eval₂ aux_F_to_real aR aux_r = aR ^ 2 - aux_F_to_real aux_u := by
      simp [aux_r]
    _ = uR - uR := by
      simp [uR, hsqrt]
    _ = 0 := by ring

lemma aux_K_no_sq_neg_one : ∀ b : aux_K, b ^ 2 ≠ (-1 : aux_K) := by
  intro b hb
  let phi : aux_K →ₐ[ℚ] ℝ := aux_K_to_real
  have hmap : (phi b) ^ 2 = (-1 : ℝ) := by
    have h := congrArg phi hb
    simpa using h
  have hnonneg : (0 : ℝ) ≤ (phi b) ^ 2 := by nlinarith
  have : (0 : ℝ) ≤ (-1 : ℝ) := by
    simpa [hmap] using hnonneg
  nlinarith

-- `aux_s = X^2 + 1` is irreducible over `aux_K`, so `aux_E` is a field.
lemma aux_s_irreducible : Irreducible aux_s := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  letI : Field aux_F := by infer_instance
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  letI : Field aux_K := by infer_instance
  have hprime : (2 : ℕ).Prime := by decide
  simpa [aux_s] using
    (X_pow_sub_C_irreducible_of_prime (K := aux_K) (p := 2) hprime (a := (-1 : aux_K))
      aux_K_no_sq_neg_one)

instance aux_F_field : Field aux_F := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  infer_instance

instance aux_K_field : Field aux_K := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  letI : Field aux_F := by infer_instance
  infer_instance

instance aux_E_field : Field aux_E := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  letI : Field aux_F := by infer_instance
  letI : Field aux_K := by infer_instance
  infer_instance

instance aux_F_algebra : Algebra ℚ aux_F := by
  classical
  infer_instance

instance aux_K_algebra : Algebra ℚ aux_K := by
  classical
  letI : Algebra ℚ aux_F := by infer_instance
  exact (AdjoinRoot.instAlgebra (R := aux_F) (S := ℚ) (f := aux_r))

instance aux_E_algebra : Algebra ℚ aux_E := by
  classical
  letI : Algebra ℚ aux_K := by infer_instance
  exact (AdjoinRoot.instAlgebra (R := aux_K) (S := ℚ) (f := aux_s))

-- The defining relation for `aux_u` gives `aux_u * (1 - aux_u) = -1`.
lemma aux_u_mul_one_sub_aux_u : (aux_u : aux_F) * (1 - aux_u) = (-1 : aux_F) := by
  have h' : aux_u ^ 2 - aux_u - 1 = (0 : aux_F) := by
    simpa [aux_q, aux_u, eval₂_X_pow, eval₂_X, eval₂_C, eval₂_add, eval₂_mul, eval₂_sub] using
      (AdjoinRoot.eval₂_root (f := aux_q))
  have h'' : aux_u ^ 2 = aux_u + 1 := by
    have h''' : aux_u ^ 2 - (aux_u + 1) = (0 : aux_F) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    exact sub_eq_zero.mp h'''
  calc
    (aux_u : aux_F) * (1 - aux_u) = aux_u - aux_u ^ 2 := by ring
    _ = aux_u - (aux_u + 1) := by simp [h'']
    _ = (-1 : aux_F) := by ring

-- The explicit quadratic tower has total degree 8 over ℚ.
set_option maxHeartbeats 400000 in
lemma auxField_finrank_eq_8 : Module.finrank ℚ aux_E = 8 := by
  classical
  have hqdeg : aux_q.natDegree = 2 := by
    simpa [aux_q, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (Polynomial.natDegree_quadratic
        (a := (1 : ℚ)) (b := (-1 : ℚ)) (c := (-1 : ℚ)) (ha := one_ne_zero))
  have hq0 : aux_q ≠ 0 := by
    intro hq
    have hqdeg' : (0 : ℕ) = 2 := by
      simp [aux_q, hq] at hqdeg
    exact (by decide : (0 : ℕ) ≠ 2) hqdeg'
  have hdeg_q : (aux_q : ℚ[X]).degree ≠ 0 := by
    simp [degree_eq_natDegree hq0, hqdeg]
  haveI : Nontrivial aux_F := AdjoinRoot.nontrivial (R := ℚ) (f := aux_q) hdeg_q
  have hF : Module.finrank ℚ aux_F = 2 := by
    simpa [AdjoinRoot.powerBasis, hqdeg] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis (K := ℚ) (f := aux_q) hq0))
  have hrdeg : aux_r.natDegree = 2 := by
    simp [aux_r]
  have hmonic_r : aux_r.Monic := by
    simpa [aux_r] using (monic_X_pow_sub_C (R := aux_F) (a := aux_u) (n := 2) (by decide))
  have hnotunit_r : ¬ IsUnit aux_r := by
    intro hunit
    have h1 : aux_r = 1 := (Monic.isUnit_iff hmonic_r).1 hunit
    have hdeg1 :
        aux_r.natDegree = 0 := by
      simp [h1]
    have hdeg1' : (2 : ℕ) = 0 := by
      simp at hdeg1
    exact (by decide : (2 : ℕ) ≠ 0) hdeg1'
  have hspan_r : (Ideal.span ({aux_r} : Set aux_F[X])) ≠ ⊤ := by
    intro htop
    exact hnotunit_r ((Ideal.span_singleton_eq_top).1 htop)
  haveI : Nontrivial aux_K := by
    simpa [aux_K, AdjoinRoot] using
      (Ideal.Quotient.nontrivial_iff (R := aux_F[X])
        (I := Ideal.span ({aux_r} : Set aux_F[X]))).2 hspan_r
  have hK : Module.finrank aux_F aux_K = 2 := by
    simpa [AdjoinRoot.powerBasis', hrdeg] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis' (R := aux_F) (g := aux_r) hmonic_r))
  have hsdeg : aux_s.natDegree = 2 := by
    simpa [aux_s] using (natDegree_X_pow_sub_C (R := aux_K) (n := 2) (r := (-1 : aux_K)))
  have hmonic_s : aux_s.Monic := by
    simpa [aux_s] using
      (monic_X_pow_sub_C (R := aux_K) (a := (-1 : aux_K)) (n := 2) (by decide))
  have hE : Module.finrank aux_K aux_E = 2 := by
    simpa [AdjoinRoot.powerBasis', hsdeg] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis' (R := aux_K) (g := aux_s) hmonic_s))
  haveI : Module.Free ℚ aux_F :=
    Module.Free.of_basis (AdjoinRoot.powerBasis (K := ℚ) (f := aux_q) hq0).basis
  haveI : Module.Free aux_F aux_K :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (R := aux_F) (g := aux_r) hmonic_r).basis
  haveI : Module.Free aux_K aux_E :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (R := aux_K) (g := aux_s) hmonic_s).basis
  have hFK : Module.finrank ℚ aux_K = 4 := by
    have h := (Module.finrank_mul_finrank (F := ℚ) (K := aux_F) (A := aux_K))
    have h' : (2 : ℕ) * 2 = Module.finrank ℚ aux_K := by
      simpa [hF, hK] using h
    simpa using h'.symm
  have hFE : Module.finrank ℚ aux_E = 8 := by
    have h := (Module.finrank_mul_finrank (F := ℚ) (K := aux_K) (A := aux_E))
    have h' :
        (Module.finrank ℚ aux_K) * (Module.finrank aux_K aux_E) =
          Module.finrank ℚ aux_E := by
      simpa using h
    have h'' : (4 : ℕ) * 2 = Module.finrank ℚ aux_E := by
      simpa [hFK, hE] using h'
    simpa using h''.symm
  exact hFE

lemma aux_a_sq_aux_E : (aux_a : aux_E)^2 = algebraMap aux_F aux_E aux_u := by
  have h : aeval aux_a aux_r = (0 : aux_K) := by
    simpa [aux_r] using (AdjoinRoot.aeval_eq (f := aux_r) (p := aux_r))
  have h' : (aux_a : aux_K)^2 - (algebraMap aux_F aux_K aux_u) = 0 := by
    simpa [aux_r] using h
  have h'' : (aux_a : aux_K)^2 = algebraMap aux_F aux_K aux_u := sub_eq_zero.mp h'
  have hmap := congrArg (algebraMap aux_K aux_E) h''
  simpa using hmap

lemma aux_i_sq_aux_E : (aux_i : aux_E)^2 = (-1 : aux_E) := by
  have h : aeval aux_i aux_s = (0 : aux_E) := by
    simpa using (AdjoinRoot.aeval_eq (f := aux_s) (p := aux_s))
  have h' : (aux_i : aux_E)^2 - (-1 : aux_E) = 0 := by
    simpa [aux_s] using h
  exact sub_eq_zero.mp h'

lemma aux_u_mul_one_sub_aux_u_aux_E :
    (algebraMap aux_F aux_E aux_u) * (1 - algebraMap aux_F aux_E aux_u) = (-1 : aux_E) := by
  classical
  letI : Algebra aux_F aux_K := by infer_instance
  letI : Algebra aux_F aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := aux_F) (f := aux_s))
  let f : aux_F →+* aux_E := algebraMap aux_F aux_E
  have h : f (aux_u * (1 - aux_u)) = f (-1) :=
    congrArg f aux_u_mul_one_sub_aux_u
  simpa [RingHom.map_mul, RingHom.map_sub, RingHom.map_neg, RingHom.map_one] using h

-- The polynomial `poly36` splits over the quadratic tower `aux_E`.
set_option maxHeartbeats 400000 in
lemma poly36_splits_aux_E : (poly36.map (algebraMap ℚ aux_E)).Splits := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  letI : Field aux_F := by infer_instance
  letI : Field aux_K := by infer_instance
  letI : Field aux_E := by infer_instance
  letI : Algebra ℚ aux_K := by infer_instance
  letI : Algebra ℚ aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := ℚ) (f := aux_s))
  letI : Algebra aux_F aux_K := by infer_instance
  letI : Algebra aux_F aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := aux_F) (f := aux_s))
  letI : Algebra aux_K aux_E := by infer_instance
  let uE : aux_E := algebraMap aux_F aux_E aux_u
  let aE : aux_E := algebraMap aux_K aux_E aux_a
  have ha_sq : aE ^ 2 = uE := by
    simpa [aE, uE] using aux_a_sq_aux_E
  have hi_sq : (aux_i : aux_E) ^ 2 = (-1 : aux_E) := aux_i_sq_aux_E
  have hu_mul : uE * (1 - uE) = (-1 : aux_E) := by
    dsimp [uE]
    exact aux_u_mul_one_sub_aux_u_aux_E
  have hu_ne : uE ≠ 0 := by
    intro h0
    have hneg : (-1 : aux_E) ≠ 0 := by
      intro h
      have h1 : (1 : aux_E) = 0 := by
        exact (neg_eq_zero.mp h)
      exact one_ne_zero h1
    have hzero : (-1 : aux_E) = 0 := by
      have : uE * (1 - uE) = 0 := by simp [h0]
      calc
        (-1 : aux_E) = uE * (1 - uE) := by simpa using hu_mul.symm
        _ = 0 := this
    exact hneg hzero
  have ha_ne : aE ≠ 0 := by
    intro h0
    apply hu_ne
    have : uE = 0 := by
      simpa [h0] using ha_sq.symm
    exact this
  have hb_sq : (aux_i * aE⁻¹) ^ 2 = 1 - uE := by
    have h1 : (-1 : aux_E) * uE⁻¹ = 1 - uE := by
      apply (mul_right_cancel₀ hu_ne)
      calc
        (-1 : aux_E) * uE⁻¹ * uE = (-1 : aux_E) := by
          simp [hu_ne]
        _ = uE * (1 - uE) := by
          simpa using hu_mul.symm
        _ = (1 - uE) * uE := by
          ac_rfl
    calc
      (aux_i * aE⁻¹) ^ 2 = (aux_i : aux_E) ^ 2 * (aE⁻¹) ^ 2 := by
        simpa using (mul_pow aux_i aE⁻¹ 2)
      _ = (-1 : aux_E) * (aE ^ 2)⁻¹ := by
        simp [hi_sq, inv_pow]
      _ = (-1 : aux_E) * uE⁻¹ := by
        simp [ha_sq]
      _ = 1 - uE := h1
  have hfactor :
      (poly36.map (algebraMap ℚ aux_E)) =
        (X ^ 2 - C uE) * (X ^ 2 - C (1 - uE)) := by
    have hpoly' :
        (X ^ 2 - C uE) * (X ^ 2 - C (1 - uE)) =
          (X ^ 4 - X ^ 2 + (C uE * C (1 - uE)) : aux_E[X]) := by
      have hC : (C (1 - uE) : aux_E[X]) = 1 - C uE := by
        calc
          (C (1 - uE) : aux_E[X]) = C (1 + (-uE)) := by
            rw [sub_eq_add_neg]
          _ = C (1 : aux_E) + C (-uE) := by
            rw [C_add]
          _ = 1 - C uE := by
            rw [C_1, C_neg, sub_eq_add_neg]
      calc
        (X ^ 2 - C uE) * (X ^ 2 - C (1 - uE)) =
            (X ^ 2 - C uE) * (X ^ 2 - (1 - C uE)) := by
              rw [hC]
        _ = (X ^ 4 - X ^ 2 + (C uE * (1 - C uE)) : aux_E[X]) := by
              ring
        _ = (X ^ 4 - X ^ 2 + (C uE * C (1 - uE)) : aux_E[X]) := by
              rw [hC.symm]
    have hpoly :
        (X ^ 2 - C uE) * (X ^ 2 - C (1 - uE)) =
          (X ^ 4 - X ^ 2 + C (uE * (1 - uE)) : aux_E[X]) := by
      simpa [C_mul] using hpoly'
    calc
      (poly36.map (algebraMap ℚ aux_E)) =
          (X ^ 4 - X ^ 2 - 1 : aux_E[X]) := by
            simp [poly36]
      _ = (X ^ 4 - X ^ 2 + C (uE * (1 - uE)) : aux_E[X]) := by
            rw [hu_mul, C_neg, C_1]
            ring
      _ = (X ^ 2 - C uE) * (X ^ 2 - C (1 - uE)) := by
            simpa [hpoly] using hpoly.symm
  have hsplit1 : (X ^ 2 - C uE : aux_E[X]).Splits := by
    have hdeg : (X ^ 2 - C uE : aux_E[X]).natDegree = 2 := by
      simp
    have hroot : eval₂ (RingHom.id aux_E) aE (X ^ 2 - C uE : aux_E[X]) = 0 := by
      simp [ha_sq]
    simpa using
      (splits_of_natDegree_eq_two (i := RingHom.id aux_E) (f := X ^ 2 - C uE)
        (x := aE) hdeg hroot)
  have hsplit2 : (X ^ 2 - C (1 - uE) : aux_E[X]).Splits := by
    have hdeg : (X ^ 2 - C (1 - uE) : aux_E[X]).natDegree = 2 := by
      simpa using (natDegree_X_pow_sub_C (R := aux_E) (n := 2) (r := (1 - uE)))
    have hroot :
        eval₂ (RingHom.id aux_E) (aux_i * aE⁻¹) (X ^ 2 - C (1 - uE) : aux_E[X]) = 0 := by
      simp [hb_sq]
    simpa using
      (splits_of_natDegree_eq_two (i := RingHom.id aux_E) (f := X ^ 2 - C (1 - uE))
        (x := (aux_i * aE⁻¹)) hdeg hroot)
  have hsplit : ((X ^ 2 - C uE) * (X ^ 2 - C (1 - uE)) : aux_E[X]).Splits :=
    hsplit1.mul hsplit2
  simpa [hfactor] using hsplit

-- The roots of `poly36` generate the full tower `aux_E`.
set_option maxHeartbeats 400000 in
lemma auxE_adjoin_rootSet_eq_top :
    Algebra.adjoin ℚ (poly36.rootSet aux_E : Set aux_E) = ⊤ := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  letI : Field aux_F := by infer_instance
  letI : Field aux_K := by infer_instance
  letI : Field aux_E := by infer_instance
  letI : Algebra ℚ aux_K := by infer_instance
  letI : Algebra ℚ aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := ℚ) (f := aux_s))
  letI : Algebra aux_F aux_K := by infer_instance
  letI : Algebra aux_F aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := aux_F) (f := aux_s))
  letI : Algebra aux_K aux_E := by infer_instance
  let S : Set aux_E := poly36.rootSet aux_E
  let uE : aux_E := algebraMap aux_F aux_E aux_u
  let aE : aux_E := algebraMap aux_K aux_E aux_a
  let bE : aux_E := aux_i * aE⁻¹
  have ha_sq : aE ^ 2 = uE := by
    simpa [aE, uE] using aux_a_sq_aux_E
  have hi_sq : (aux_i : aux_E) ^ 2 = (-1 : aux_E) := aux_i_sq_aux_E
  have hu_mul : uE * (1 - uE) = (-1 : aux_E) := by
    simpa [uE] using aux_u_mul_one_sub_aux_u_aux_E
  have hu_poly : uE ^ 2 - uE - 1 = 0 := by
    have h1 : uE - uE ^ 2 = (-1 : aux_E) := by
      simpa [mul_sub, pow_two] using hu_mul
    have h2 : uE ^ 2 - uE = (1 : aux_E) := by
      have h1' : -(uE - uE ^ 2) = (1 : aux_E) := by
        simpa using congrArg Neg.neg h1
      calc
        uE ^ 2 - uE = -(uE - uE ^ 2) := by ring
        _ = (1 : aux_E) := h1'
    calc
      uE ^ 2 - uE - 1 = (uE ^ 2 - uE) - 1 := by ring
      _ = (1 : aux_E) - 1 := by simp [h2]
      _ = 0 := by ring
  have hu_ne : uE ≠ 0 := by
    intro h0
    have hneg : (-1 : aux_E) = 0 := by
      simpa [h0] using hu_mul.symm
    have h1 : (1 : aux_E) = 0 := by simpa using (neg_eq_zero.mp hneg)
    exact one_ne_zero h1
  have ha_ne : aE ≠ 0 := by
    intro h0
    apply hu_ne
    have : uE = 0 := by
      simpa [h0] using ha_sq.symm
    exact this
  have hb_sq : bE ^ 2 = 1 - uE := by
    have h1 : (-1 : aux_E) * uE⁻¹ = 1 - uE := by
      apply (mul_right_cancel₀ hu_ne)
      calc
        (-1 : aux_E) * uE⁻¹ * uE = (-1 : aux_E) := by
          simp [hu_ne]
        _ = uE * (1 - uE) := by
          simpa using hu_mul.symm
        _ = (1 - uE) * uE := by
          ac_rfl
    calc
      bE ^ 2 = (aux_i : aux_E) ^ 2 * (aE⁻¹) ^ 2 := by
        simpa [bE] using (mul_pow aux_i aE⁻¹ 2)
      _ = (-1 : aux_E) * (aE ^ 2)⁻¹ := by
        simp [hi_sq, inv_pow]
      _ = (-1 : aux_E) * uE⁻¹ := by
        simp [ha_sq]
      _ = 1 - uE := h1
  have hroot_a : aE ∈ poly36.rootSet aux_E := by
    refine (mem_rootSet_of_ne (p := poly36) (S := aux_E) poly36_ne_zero).2 ?_
    calc
      aeval aE (poly36 : ℚ[X]) = aE ^ 4 - aE ^ 2 - 1 := by
        simp [poly36]
      _ = (aE ^ 2) ^ 2 - aE ^ 2 - 1 := by ring
      _ = uE ^ 2 - uE - 1 := by simp [ha_sq]
      _ = 0 := hu_poly
  have hroot_b : bE ∈ poly36.rootSet aux_E := by
    refine (mem_rootSet_of_ne (p := poly36) (S := aux_E) poly36_ne_zero).2 ?_
    calc
      aeval bE (poly36 : ℚ[X]) = bE ^ 4 - bE ^ 2 - 1 := by
        simp [poly36]
      _ = (bE ^ 2) ^ 2 - bE ^ 2 - 1 := by ring
      _ = (1 - uE) ^ 2 - (1 - uE) - 1 := by simp [hb_sq]
      _ = uE ^ 2 - uE - 1 := by ring
      _ = 0 := hu_poly
  have ha_mem : aE ∈ Algebra.adjoin ℚ S := by
    exact Algebra.subset_adjoin hroot_a
  have hb_mem : bE ∈ Algebra.adjoin ℚ S := by
    exact Algebra.subset_adjoin hroot_b
  have hi_mem : (aux_i : aux_E) ∈ Algebra.adjoin ℚ S := by
    have hmul : aE * bE ∈ Algebra.adjoin ℚ S :=
      (Algebra.adjoin ℚ S).mul_mem ha_mem hb_mem
    have hmul' : aE * bE = (aux_i : aux_E) := by
      calc
        aE * bE = aE * (aux_i * aE⁻¹) := by simp [bE]
        _ = aux_i * (aE * aE⁻¹) := by
          ac_rfl
        _ = aux_i := by simp [ha_ne]
    simpa [hmul'] using hmul
  have hu_mem : uE ∈ Algebra.adjoin ℚ S := by
    have hmul : aE * aE ∈ Algebra.adjoin ℚ S :=
      (Algebra.adjoin ℚ S).mul_mem ha_mem ha_mem
    have hmul' : aE ^ 2 ∈ Algebra.adjoin ℚ S := by
      simpa [pow_two] using hmul
    simpa [ha_sq] using hmul'
  have hF : Algebra.adjoin ℚ ({aux_u} : Set aux_F) = ⊤ := by
    simpa [aux_F, aux_u] using (AdjoinRoot.adjoinRoot_eq_top (f := aux_q))
  have hK : Algebra.adjoin aux_F ({aux_a} : Set aux_K) = ⊤ := by
    simpa [aux_K, aux_a] using (AdjoinRoot.adjoinRoot_eq_top (f := aux_r))
  have hK' :
      Algebra.adjoin ℚ
        (algebraMap aux_F aux_K '' ({aux_u} : Set aux_F) ∪ ({aux_a} : Set aux_K)) = ⊤ := by
    have h :=
      (Algebra.adjoin_eq_adjoin_union (R := ℚ) (A := aux_F) (B := aux_K)
        (s := ({aux_u} : Set aux_F)) (t := ({aux_a} : Set aux_K)) hF)
    simpa [hK] using h.symm
  have hE :
      Algebra.adjoin ℚ
        ((algebraMap aux_K aux_E ''
            (algebraMap aux_F aux_K '' ({aux_u} : Set aux_F) ∪ ({aux_a} : Set aux_K))) ∪
          ({aux_i} : Set aux_E)) = ⊤ := by
    have h :=
      (Algebra.adjoin_eq_adjoin_union (R := ℚ) (A := aux_K) (B := aux_E)
        (s := (algebraMap aux_F aux_K '' ({aux_u} : Set aux_F) ∪ ({aux_a} : Set aux_K)))
        (t := ({aux_i} : Set aux_E)) hK')
    have hEi : Algebra.adjoin aux_K ({aux_i} : Set aux_E) = ⊤ := by
      simpa [aux_E, aux_i] using (AdjoinRoot.adjoinRoot_eq_top (f := aux_s))
    simpa [hEi] using h.symm
  have hsubset :
      ((algebraMap aux_K aux_E ''
          (algebraMap aux_F aux_K '' ({aux_u} : Set aux_F) ∪ ({aux_a} : Set aux_K))) ∪
        ({aux_i} : Set aux_E)) ⊆ Algebra.adjoin ℚ S := by
    intro x hx
    rcases hx with hx | hx
    · rcases hx with ⟨y, hy, rfl⟩
      rcases hy with hy | hy
      · rcases hy with ⟨z, hz, rfl⟩
        have hz' : z = aux_u := by
          simpa [Set.mem_singleton_iff] using hz
        subst hz'
        simpa [uE] using hu_mem
      · have hy' : y = aux_a := by
          simpa [Set.mem_singleton_iff] using hy
        subst hy'
        simpa [aE] using ha_mem
    · have hx' : x = aux_i := by
        simpa [Set.mem_singleton_iff] using hx
      subst hx'
      exact hi_mem
  have hle :
      Algebra.adjoin ℚ
        ((algebraMap aux_K aux_E ''
            (algebraMap aux_F aux_K '' ({aux_u} : Set aux_F) ∪ ({aux_a} : Set aux_K))) ∪
          ({aux_i} : Set aux_E)) ≤ Algebra.adjoin ℚ S := by
    exact Algebra.adjoin_le hsubset
  have hle' : (⊤ : Subalgebra ℚ aux_E) ≤ Algebra.adjoin ℚ S := by
    rw [← hE]
    exact hle
  exact le_antisymm le_top hle'

lemma auxE_isSplittingField_poly36 : Polynomial.IsSplittingField ℚ aux_E poly36 := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  letI : Field aux_F := by infer_instance
  letI : Field aux_K := by infer_instance
  letI : Field aux_E := by infer_instance
  letI : Algebra ℚ aux_K := by infer_instance
  letI : Algebra ℚ aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := ℚ) (f := aux_s))
  exact ⟨poly36_splits_aux_E, auxE_adjoin_rootSet_eq_top⟩

-- The splitting field of `poly36` has degree 8 over ℚ.
lemma finrank_splittingField_poly36_eq_eight :
    Module.finrank ℚ (poly36.SplittingField) = 8 := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  letI : Field aux_F := by infer_instance
  letI : Field aux_K := by infer_instance
  letI : Field aux_E := by infer_instance
  letI : Algebra ℚ aux_K := by infer_instance
  letI : Algebra ℚ aux_E := (AdjoinRoot.instAlgebra (R := aux_K) (S := ℚ) (f := aux_s))
  haveI : Polynomial.IsSplittingField ℚ aux_E poly36 := auxE_isSplittingField_poly36
  let e := Polynomial.IsSplittingField.algEquiv (K := ℚ) (L := aux_E) poly36
  have h :
      Module.finrank ℚ aux_E = Module.finrank ℚ (poly36.SplittingField) := by
    simpa using (LinearEquiv.finrank_eq (e.toLinearEquiv))
  simpa [h] using auxField_finrank_eq_8

lemma natCard_galoisGroup_poly36_eq_eight :
    Nat.card (Gal(poly36.SplittingField/ℚ)) = 8 := by
  classical
  let K := poly36.SplittingField
  have hgal : IsGalois ℚ K := by
    simpa [K] using
      (IsGalois.of_separable_splitting_field (F := ℚ) (E := K) (p := poly36) poly36_separable)
  have hfin : Module.finrank ℚ K = 8 := by
    simpa [K] using finrank_splittingField_poly36_eq_eight
  simpa [hfin] using (IsGalois.card_aut_eq_finrank (F := ℚ) (E := K))

-- The Galois action on the 4-element root set embeds into `S₄` after a `Fin 4` labeling.
lemma galActionHom_to_perm_fin4_injective
    (K : Type*) [Field K] [Algebra ℚ K]
    (hcard : Fintype.card (poly36.rootSet K) = 4)
    [Fact ((poly36.map (algebraMap ℚ K)).Splits)] :
    Function.Injective
      (((Fintype.equivFinOfCardEq hcard).permCongrHom.toMonoidHom).comp
        (Polynomial.Gal.galActionHom poly36 K)) := by
  classical
  intro x y hxy
  have h' :
      (Polynomial.Gal.galActionHom poly36 K) x =
        (Polynomial.Gal.galActionHom poly36 K) y := by
    apply (Fintype.equivFinOfCardEq hcard).permCongrHom.injective
    simpa using hxy
  exact (Polynomial.Gal.galActionHom_injective (p := poly36) (E := K)) h'

-- A dedicated lemma for the missing Galois-group identification.
lemma nonempty_galois_mulEquiv_dihedralGroup_four_poly36 :
    Nonempty (Gal(poly36.SplittingField/ℚ) ≃* DihedralGroup 4) := by
  classical
  let K := poly36.SplittingField
  have hsep : (poly36 : ℚ[X]).Separable := poly36_separable
  have hgal : IsGalois ℚ K := by
    simpa [K] using
      (IsGalois.of_separable_splitting_field (F := ℚ) (E := K) (p := poly36) hsep)
  have hrootcard : Fintype.card (poly36.rootSet K) = 4 := by
    simpa [K] using poly36_rootSet_card
  haveI hsplit : Fact ((poly36.map (algebraMap ℚ K)).Splits) := by
    refine ⟨?_⟩
    simpa [K] using (SplittingField.splits (poly36 : ℚ[X]))
  let f : Gal(K/ℚ) →* Equiv.Perm (Fin 4) :=
    ((Fintype.equivFinOfCardEq hrootcard).permCongrHom.toMonoidHom).comp
      (Polynomial.Gal.galActionHom poly36 K)
  have hf_inj : Function.Injective f := by
    simpa [f] using (galActionHom_to_perm_fin4_injective (K := K) hrootcard)
  -- The negation map permutes the roots of `poly36`, giving a fixed-point-free involution.
  let s₀ : Equiv.Perm (poly36.rootSet K) := negPerm_rootSet (K := K)
  have hs₀_sq : s₀ * s₀ = 1 := by
    ext x
    change (-(-x.1)) = x.1
    exact neg_neg x.1
  let s : Equiv.Perm (Fin 4) :=
    (Equiv.permCongr (Fintype.equivFinOfCardEq hrootcard)) s₀
  -- Negation has no fixed points on the root set because `0` is not a root.
  have hs₀_no_fixed : ∀ x : poly36.rootSet K, s₀ x ≠ x := by
    intro x hx
    have hx' : (-x.1 : K) = x.1 := by
      have hx'' := congrArg Subtype.val hx
      simp [s₀, negPerm_rootSet] at hx''
      exact hx''
    have hsum : x.1 + x.1 = 0 := by
      calc
        x.1 + x.1 = (-x.1) + x.1 := by simp [hx']
        _ = 0 := by simp
    have hmul : (2 : K) * x.1 = 0 := by
      simpa [two_mul] using hsum
    have hx0 : x.1 = 0 := by
      have htwo : (2 : K) ≠ 0 := by exact two_ne_zero
      exact (mul_eq_zero.mp hmul).resolve_left htwo
    have hroot : (0 : K) ∈ poly36.rootSet K := by
      simpa [hx0] using x.property
    have h0 : aeval (0 : K) (poly36 : ℚ[X]) = 0 :=
      (mem_rootSet_of_ne (p := poly36) (S := K) poly36_ne_zero).1 hroot
    have h1 : (1 : K) = 0 := by
      have hneg : (-1 : K) = 0 := by
        simp [poly36, aeval_def] at h0
      simpa using (neg_eq_zero.mp hneg)
    exact one_ne_zero h1
  -- Transport involution data to `Fin 4`.
  have hs : s * s = 1 := by
    -- `permCongr` is a group hom, so involutions are preserved.
    have h1 :
        (Fintype.equivFinOfCardEq hrootcard).permCongr
            (1 : Equiv.Perm (poly36.rootSet K)) = (1 : Equiv.Perm (Fin 4)) := by
      ext i
      simp [Equiv.permCongr_apply]
    simpa [s, Equiv.permCongr_mul, h1] using
      congrArg (fun t => (Fintype.equivFinOfCardEq hrootcard).permCongr t) hs₀_sq
  have hs_no_fixed : ∀ i : Fin 4, s i ≠ i := by
    intro i hi
    have hi' :
        s₀ ((Fintype.equivFinOfCardEq hrootcard).symm i) =
          (Fintype.equivFinOfCardEq hrootcard).symm i := by
      apply (Fintype.equivFinOfCardEq hrootcard).injective
      simpa [s, Equiv.permCongr_apply] using hi
    exact (hs₀_no_fixed _ hi')
  -- Every Galois automorphism commutes with negation on the root set.
  have h_range :
      MonoidHom.range f ≤ Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4))) := by
    classical
    intro x hx
    rcases hx with ⟨g, rfl⟩
    refine (Subgroup.mem_centralizer_singleton_iff).2 ?_
    have hcomm :
        (Polynomial.Gal.galActionHom poly36 K g) * s₀ =
          s₀ * (Polynomial.Gal.galActionHom poly36 K g) := by
      simpa [s₀] using (galActionHom_comm_negPerm_rootSet (K := K) (g := g))
    have hcomm' :=
      congrArg (fun t => (Fintype.equivFinOfCardEq hrootcard).permCongr t) hcomm
    simpa [f, s, Equiv.permCongr_mul] using hcomm'
  have hcentralizer_card :
      Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) = 8 := by
    exact natCard_centralizer_eq_eight_of_fixedPointFree_involution_fin4 s hs hs_no_fixed
  -- Compare cardinalities to identify the image with the centralizer, then transport to `D₄`.
  have e_range : Gal(K/ℚ) ≃* MonoidHom.range f := MonoidHom.ofInjective hf_inj
  have hcard_range : Nat.card (MonoidHom.range f) = Nat.card (Gal(K/ℚ)) := by
    classical
    simpa using (Nat.card_congr e_range.toEquiv).symm
  have hmain :
      Nat.card (Gal(K/ℚ)) = 8 ∧
        Nonempty (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4))) ≃* DihedralGroup 4) := by
    refine ⟨natCard_galoisGroup_poly36_eq_eight, ?_⟩
    exact nonempty_centralizer_mulEquiv_dihedralGroup_four_fin4 s hs hs_no_fixed
  rcases hmain with ⟨hgal_card, hcentralizer_equiv⟩
  have hcard_range' : Nat.card (MonoidHom.range f) = 8 := by
    calc
      Nat.card (MonoidHom.range f) = Nat.card (Gal(K/ℚ)) := hcard_range
      _ = 8 := hgal_card
  have h_range_eq :
      MonoidHom.range f = Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4))) := by
    refine Subgroup.eq_of_le_of_card_ge h_range ?_
    have : Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) ≤
        Nat.card (MonoidHom.range f) := by
      have hcard_eq :
          Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) =
            Nat.card (MonoidHom.range f) := by
        calc
          Nat.card (Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 4)))) = 8 := hcentralizer_card
          _ = Nat.card (MonoidHom.range f) := by symm; exact hcard_range'
      exact le_of_eq hcard_eq
    exact this
  rcases hcentralizer_equiv with ⟨e_cent⟩
  refine ⟨(e_range.trans (MulEquiv.subgroupCongr h_range_eq)).trans e_cent⟩

-- The final Galois group identification and subgroup count packaged together.
lemma exists_mulEquiv_dihedralGroup_four_and_subgroup_count :
    ∃ _e : Gal(poly36.SplittingField/ℚ) ≃* DihedralGroup 4,
      Nat.card (Subgroup (DihedralGroup 4)) = 10 := by
  classical
  refine ⟨Classical.choice nonempty_galois_mulEquiv_dihedralGroup_four_poly36,
    natCard_subgroup_dihedralGroup_four⟩

end

end FATEH36

/-- Let $f(X)=X^4-X^2-1\in \mathbb{Q}[X]$, $K$ is the splitting field of $f$ over $\mathbb{Q}$,
prove that the number of intermediate fields of $K/\mathbb{Q}$ is 10. -/
theorem card_intermediateField_splittingField_eq_ten :
    Nat.card (IntermediateField ℚ (X ^ 4 - X ^ 2 - 1 : ℚ[X]).SplittingField) = 10 := by
  classical
  let f : ℚ[X] := FATEH36.poly36
  have hsep : (f : ℚ[X]).Separable := FATEH36.poly36_separable
  have hgal : IsGalois ℚ f.SplittingField := by
    simpa using (IsGalois.of_separable_splitting_field (F := ℚ)
      (E := f.SplittingField) (p := f) hsep)
  -- Galois correspondence reduces the count to subgroups of the Galois group.
  have hcard :
      Nat.card (IntermediateField ℚ f.SplittingField) = Nat.card (Subgroup Gal(f.SplittingField/ℚ)) :=
    FATEH36.natCard_intermediateField_eq_natCard_subgroup_galois (K := f.SplittingField)
  -- TODO: identify `Gal(f/ℚ)` with `DihedralGroup 4` and count subgroups.
  -- This is the remaining blocker.
  have hsub : Nat.card (Subgroup Gal(f.SplittingField/ℚ)) = 10 := by
    -- TODO: provide the D4 identification and subgroup count.
    have h :
        ∃ e : Gal(f.SplittingField/ℚ) ≃* DihedralGroup 4,
          Nat.card (Subgroup (DihedralGroup 4)) = 10 := by
      simpa [f, FATEH36.poly36] using
        (FATEH36.exists_mulEquiv_dihedralGroup_four_and_subgroup_count)
    rcases h with ⟨e, hD4⟩
    exact FATEH36.natCard_subgroup_eq_ten_of_mulEquiv e hD4
  calc
    Nat.card (IntermediateField ℚ f.SplittingField) =
        Nat.card (Subgroup Gal(f.SplittingField/ℚ)) := hcard
    _ = 10 := hsub

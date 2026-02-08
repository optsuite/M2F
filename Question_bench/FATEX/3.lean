import Mathlib

open scoped Pointwise
open scoped Finset
open scoped BigOperators

noncomputable section

local instance (α : Type*) : DecidableEq α := Classical.decEq _
local instance (α : Type*) (p : α → Prop) : DecidablePred p := Classical.decPred p

noncomputable instance (G : Type*) [Group G] (H : Subgroup G) [H.FiniteIndex] :
    Fintype (Quotient (QuotientGroup.rightRel H)) := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  exact Fintype.ofEquiv (G ⧸ H) (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm

/-- If `S` is a left complement of `H`, then `S⁻¹` is a right complement of `H`. -/
lemma Subgroup.isComplement_right_inv_of_left {G : Type*} [Group G] {H : Subgroup G}
    {S : Set G} (h : Subgroup.IsComplement S H) :
    Subgroup.IsComplement H (S⁻¹) := by
  classical
  -- Unfold the complement conditions and transport across inversion.
  let Sinv : Set G := {g : G | g⁻¹ ∈ S}
  let m : S × H → G := fun x => x.1.1 * x.2.1
  let m' : H × Sinv → G := fun x => x.1.1 * x.2.1
  have hm : Function.Bijective m := h
  let ψ : H × Sinv → S × H := fun x =>
    ⟨⟨(x.2 : G)⁻¹, by
        exact x.2.property
      ⟩, ⟨(x.1 : G)⁻¹, H.inv_mem x.1.property⟩⟩
  let ψinv : S × H → H × Sinv := fun x =>
    ⟨⟨(x.2 : G)⁻¹, H.inv_mem x.2.property⟩, ⟨(x.1 : G)⁻¹, by
        change ((x.1 : G)⁻¹)⁻¹ ∈ S
        simp [x.1.property]
      ⟩⟩
  have hψ_left : Function.LeftInverse ψinv ψ := by
    intro x
    ext <;> simp [ψ, ψinv]
  have hψ_right : Function.RightInverse ψinv ψ := by
    intro x
    ext <;> simp [ψ, ψinv]
  have hψ : Function.Bijective ψ := ⟨hψ_left.injective, hψ_right.surjective⟩
  have hinv : Function.Bijective (fun g : G => g⁻¹) := by
    refine ⟨inv_injective, ?_⟩
    intro g
    exact ⟨g⁻¹, by simp⟩
  have hcomp : Function.Bijective (fun x => (m (ψ x))⁻¹) :=
    hinv.comp (hm.comp hψ)
  have hcomp' : (fun x => (m (ψ x))⁻¹) = m' := by
    funext x
    simp [m, m', ψ, mul_inv_rev]
  simpa [hcomp'] using hcomp

-- A representative function inducing a bijection to right cosets gives a bitransversal.
lemma range_of_s_is_bitransversal {G : Type*} [Group G] {H : Subgroup G}
    (s : G ⧸ H → G) (hs : ∀ q, (QuotientGroup.mk (s q) = q))
    (hbij :
      Function.Bijective (fun q => (Quotient.mk'' (s q) :
        Quotient (QuotientGroup.rightRel H)))) :
    Subgroup.IsComplement (Set.range s) H ∧ Subgroup.IsComplement H (Set.range s) := by
  classical
  have hleft : Subgroup.IsComplement (Set.range s) H :=
    Subgroup.isComplement_range_left (H := H) (f := s) hs
  let r : G ⧸ H → Quotient (QuotientGroup.rightRel H) := fun q => Quotient.mk'' (s q)
  let e : (G ⧸ H) ≃ Quotient (QuotientGroup.rightRel H) := Equiv.ofBijective r hbij
  let t : Quotient (QuotientGroup.rightRel H) → G := fun q => s (e.symm q)
  have ht : ∀ q, Quotient.mk'' (t q) = q := by
    intro q
    change r (e.symm q) = q
    exact e.apply_symm_apply q
  have hright : Subgroup.IsComplement H (Set.range t) :=
    Subgroup.isComplement_range_right (H := H) (f := t) ht
  have hrange : Set.range t = Set.range s := by
    ext g
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨e.symm q, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨e q, by simp [t]⟩
  exact ⟨hleft, hrange ▸ hright⟩

-- Relation between left and right cosets via a shared representative.
def leftRightRel {G : Type*} [Group G] (H : Subgroup G) :
    (G ⧸ H) → Quotient (QuotientGroup.rightRel H) → Prop :=
  fun q r => ∃ g : G, QuotientGroup.mk g = q ∧ Quotient.mk'' g = r

-- If a left and right coset are represented by elements in the same double coset, they are related.
lemma leftRightRel_of_doubleCoset_reps {G : Type*} [Group G] {H : Subgroup G} (g : G)
    (h₁ h₂ : H) :
    leftRightRel H (QuotientGroup.mk (h₁ * g)) (Quotient.mk'' (g * h₂)) := by
  refine ⟨h₁ * g * h₂, ?_, ?_⟩
  · simpa [mul_assoc] using
      (QuotientGroup.mk_mul_of_mem (s := H) (a := h₁ * g) (b := h₂) h₂.property)
  · apply Quotient.sound
    -- Show the representatives are equivalent for the right coset relation.
    have hcalc : (g * h₂) * (h₁ * g * h₂)⁻¹ = (h₁ : G)⁻¹ := by
      simp [mul_assoc, mul_inv_rev]
    -- Convert to membership in `H`.
    have hmem : (g * h₂) * (h₁ * g * h₂)⁻¹ ∈ H := by
      exact hcalc ▸ (H.inv_mem h₁.property)
    exact (QuotientGroup.rightRel_apply).2 hmem

-- Map a left coset to its double coset.
noncomputable def dcL {G : Type*} [Group G] (H : Subgroup G) :
    (G ⧸ H) → DoubleCoset.Quotient (H : Set G) (H : Set G) :=
  Quotient.lift (fun g => DoubleCoset.mk H H g) (by
    intro a b h
    apply (DoubleCoset.eq H H a b).2
    have hmem : a⁻¹ * b ∈ H := (QuotientGroup.leftRel_apply).1 h
    refine ⟨1, H.one_mem, a⁻¹ * b, hmem, ?_⟩
    simp
  )

-- Map a right coset to its double coset.
noncomputable def dcR {G : Type*} [Group G] (H : Subgroup G) :
    Quotient (QuotientGroup.rightRel H) → DoubleCoset.Quotient (H : Set G) (H : Set G) :=
  Quotient.lift (fun g => DoubleCoset.mk H H g) (by
    intro a b h
    apply (DoubleCoset.eq H H a b).2
    have hmem : b * a⁻¹ ∈ H := (QuotientGroup.rightRel_apply).1 h
    refine ⟨b * a⁻¹, hmem, 1, H.one_mem, ?_⟩
    simp
  )

-- If a left coset and a right coset lie in the same double coset, they are related.
lemma leftRightRel_of_same_doubleCoset {G : Type*} [Group G] (H : Subgroup G)
    (q : G ⧸ H) (r : Quotient (QuotientGroup.rightRel H))
    (h : dcL H q = dcR H r) : leftRightRel H q r := by
  classical
  revert r h
  refine Quot.induction_on q ?_
  intro g r h
  revert h
  refine Quot.induction_on r ?_
  intro g' h
  have h' : DoubleCoset.mk H H g = DoubleCoset.mk H H g' := by
    simpa [dcL, dcR, Quotient.lift_mk] using h
  obtain ⟨h₁, h₁mem, h₂, h₂mem, hg'⟩ := (DoubleCoset.eq H H g g').1 h'
  refine ⟨g * h₂, ?_, ?_⟩
  · simpa using
      (QuotientGroup.mk_mul_of_mem (s := H) (a := g) (b := h₂) h₂mem)
  · apply Quotient.sound
    have hmem : g' * (g * h₂)⁻¹ ∈ H := by
      simpa [hg', mul_assoc, mul_inv_rev] using h₁mem
    exact (QuotientGroup.rightRel_apply).2 hmem

-- If `A` meets a double coset `D`, then every right coset in `D` is related to some `q ∈ A`.
lemma neighbors_contains_right_fiber {G : Type*} [Group G] (H : Subgroup G)
    {A : Finset (G ⧸ H)} {D : DoubleCoset.Quotient (H : Set G) (H : Set G)}
    (hD : ∃ q ∈ A, dcL H q = D) :
    {r | dcR H r = D} ⊆ {r | ∃ q ∈ A, leftRightRel H q r} := by
  intro r hr
  rcases hD with ⟨q, hqA, hqD⟩
  have hr' : dcR H r = D := by
    simpa using hr
  refine ⟨q, hqA, ?_⟩
  exact leftRightRel_of_same_doubleCoset (H := H) q r (by simp [hqD, hr'])

-- Express the size of `A` as a sum of the sizes of its `dcL` fibers.
lemma Finset.card_eq_sum_fibers_dcL {G : Type*} [Group G] (H : Subgroup G)
    (A : Finset (G ⧸ H)) :
    #A = (A.image (dcL H)).sum (fun D => #{q ∈ A | dcL H q = D}) := by
  classical
  simpa using (Finset.card_eq_sum_card_image (dcL H) A)

/-- Left and right fibers over a double coset have the same cardinality. -/
lemma card_dcL_eq_card_dcR {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    [Fintype (G ⧸ H)]
    (D : DoubleCoset.Quotient (H : Set G) (H : Set G)) :
    Fintype.card {q // dcL H q = D} = Fintype.card {r // dcR H r = D} := by
  classical
  let g : G := D.out
  have hD : DoubleCoset.mk H H g = D := by
    simp [g]
  let K1 : Subgroup G := H ⊓ H.map (MulAut.conj g).toMonoidHom
  let K2 : Subgroup G := H ⊓ H.map (MulAut.conj g⁻¹).toMonoidHom
  have hK1_le : K1 ≤ H := by
    intro x hx
    exact hx.1
  have hK2_le : K2 ≤ H := by
    intro x hx
    exact hx.1
  -- Right multiplication action of `H` on right cosets.
  letI : MulAction H (Quotient (QuotientGroup.rightRel H)) :=
  { smul := fun h r =>
      Quotient.liftOn r (fun g => Quotient.mk'' (g * (h : G)⁻¹)) (by
        intro g₁ g₂ hg
        apply Quotient.sound
        apply (QuotientGroup.rightRel_apply).2
        have hg' : g₂ * g₁⁻¹ ∈ H := (QuotientGroup.rightRel_apply).1 hg
        simpa [mul_assoc, mul_inv_rev] using hg')
    one_smul := by
      intro r
      refine Quotient.inductionOn r ?_
      intro g
      change Quotient.mk'' (g * (1 : H)⁻¹) = Quotient.mk'' g
      simp
    mul_smul := by
      intro h₁ h₂ r
      refine Quotient.inductionOn r ?_
      intro g
      change
        Quotient.mk'' (g * ((h₁ * h₂ : H) : G)⁻¹) =
          Quotient.mk'' ((g * (h₂ : G)⁻¹) * (h₁ : G)⁻¹)
      simp [mul_assoc, mul_inv_rev] }
  -- Left fiber as an orbit under left multiplication.
  have hleft_set :
      {q | dcL H q = D} = MulAction.orbit H (QuotientGroup.mk g : G ⧸ H) := by
    ext q
    constructor
    · intro hq
      revert hq
      refine Quotient.inductionOn q ?_
      intro g' hq'
      have hq'' : DoubleCoset.mk H H g = DoubleCoset.mk H H g' := by
        have hq''' : DoubleCoset.mk H H g' = D := by
          simpa [dcL, Quotient.lift_mk] using hq'
        calc
          DoubleCoset.mk H H g = D := hD
          _ = DoubleCoset.mk H H g' := hq'''.symm
      obtain ⟨h1, h1mem, h2, h2mem, hg'⟩ := (DoubleCoset.eq H H g g').1 hq''
      have hq1 :
          (QuotientGroup.mk g' : G ⧸ H) = QuotientGroup.mk (h1 * g) := by
        have hq1' :
            (QuotientGroup.mk (h1 * g * h2) : G ⧸ H) =
              QuotientGroup.mk (h1 * g) := by
          simpa using
            (QuotientGroup.mk_mul_of_mem (s := H) (a := h1 * g) (b := h2) h2mem)
        simpa [hg'] using hq1'
      refine ⟨⟨h1, h1mem⟩, ?_⟩
      calc
        (⟨h1, h1mem⟩ : H) • (QuotientGroup.mk g : G ⧸ H)
            = QuotientGroup.mk (h1 * g) := rfl
        _ = QuotientGroup.mk g' := hq1.symm
    · intro hq
      rcases hq with ⟨h, rfl⟩
      have hmk : DoubleCoset.mk H H g = DoubleCoset.mk H H (h * g) := by
        apply (DoubleCoset.eq H H g (h * g)).2
        refine ⟨h, h.property, 1, H.one_mem, ?_⟩
        simp
      have hmk' : DoubleCoset.mk H H (h * g) = D := by
        simpa [hD] using hmk.symm
      simpa using hmk'
  -- Right fiber as an orbit under right multiplication.
  have hright_set :
      {r | dcR H r = D} = MulAction.orbit H (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)) := by
    ext r
    constructor
    · intro hr
      revert hr
      refine Quotient.inductionOn r ?_
      intro g' hr'
      have hr'' : DoubleCoset.mk H H g = DoubleCoset.mk H H g' := by
        have hr''' : DoubleCoset.mk H H g' = D := by
          simpa [dcR, Quotient.lift_mk] using hr'
        calc
          DoubleCoset.mk H H g = D := hD
          _ = DoubleCoset.mk H H g' := hr'''.symm
      obtain ⟨h1, h1mem, h2, h2mem, hg'⟩ := (DoubleCoset.eq H H g g').1 hr''
      have hr1 :
          (Quotient.mk'' g' : Quotient (QuotientGroup.rightRel H)) =
            Quotient.mk'' (g * h2) := by
        have hr1' :
            (Quotient.mk'' (h1 * g * h2) : Quotient (QuotientGroup.rightRel H)) =
              Quotient.mk'' (g * h2) := by
          apply Quotient.sound
          have hmem : (g * h2) * (h1 * g * h2)⁻¹ ∈ H := by
            simpa [mul_assoc, mul_inv_rev] using h1mem
          exact (QuotientGroup.rightRel_apply).2 hmem
        simpa [hg'] using hr1'
      have h2mem' : h2⁻¹ ∈ H := H.inv_mem h2mem
      refine ⟨⟨h2⁻¹, h2mem'⟩, ?_⟩
      calc
        (⟨h2⁻¹, h2mem'⟩ : H) • (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))
            = Quotient.mk'' (g * h2) := by
                change Quotient.mk'' (g * (h2⁻¹ : G)⁻¹) = Quotient.mk'' (g * h2)
                simp
        _ = Quotient.mk'' g' := hr1.symm
    · intro hr
      rcases hr with ⟨h, rfl⟩
      have hmk : DoubleCoset.mk H H g = DoubleCoset.mk H H (g * h⁻¹) := by
        apply (DoubleCoset.eq H H g (g * h⁻¹)).2
        refine ⟨1, H.one_mem, h⁻¹, H.inv_mem h.property, ?_⟩
        simp
      have hmk' : DoubleCoset.mk H H (g * h⁻¹) = D := by
        simpa [hD] using hmk.symm
      simpa using hmk'
  -- Stabilizers for the two actions.
  have hstab_left :
      MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H) = K1.subgroupOf H := by
    ext h
    constructor
    · intro hh
      have hq : (QuotientGroup.mk (h.1 * g) : G ⧸ H) = QuotientGroup.mk g := by
        simpa using hh
      have hmem' : g⁻¹ * h.1 * g ∈ H := by
        have := (QuotientGroup.eq).1 hq.symm
        simpa [mul_assoc] using this
      have hmem'' : h.1 ∈ H.map (MulAut.conj g).toMonoidHom := by
        refine ⟨g⁻¹ * h.1 * g, hmem', ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
      exact ⟨h.property, hmem''⟩
    · intro hh
      have hmem : (h.1 : G) ∈ H.map (MulAut.conj g).toMonoidHom := hh.2
      rcases hmem with ⟨x, hx, hx_eq⟩
      have hmem' : g⁻¹ * h.1 * g ∈ H := by
        have hx_eq' : h.1 = g * x * g⁻¹ := by
          simpa [MulAut.conj_apply] using hx_eq.symm
        simpa [hx_eq', mul_assoc] using hx
      have hq :
          (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk (h.1 * g) := by
        apply (QuotientGroup.eq).2
        simpa [mul_assoc] using hmem'
      simpa using hq.symm
  have hstab_right :
      MulAction.stabilizer H (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)) =
        K2.subgroupOf H := by
    ext h
    constructor
    · intro hh
      have hq :
          (Quotient.mk'' (g * h.1⁻¹) : Quotient (QuotientGroup.rightRel H)) =
            Quotient.mk'' g := by
        simpa using hh
      have hmem' : g * h.1 * g⁻¹ ∈ H := by
        have := (Quotient.eq'').1 hq
        simpa [QuotientGroup.rightRel_apply, mul_assoc, mul_inv_rev] using this
      have hmem'' : h.1 ∈ H.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine ⟨g * h.1 * g⁻¹, hmem', ?_⟩
        simp [mul_assoc]
      exact ⟨h.property, hmem''⟩
    · intro hh
      have hmem : (h.1 : G) ∈ H.map (MulAut.conj g⁻¹).toMonoidHom := hh.2
      rcases hmem with ⟨x, hx, hx_eq⟩
      have hmem' : g * h.1 * g⁻¹ ∈ H := by
        have hx_eq' : h.1 = g⁻¹ * x * g := by
          simpa [MulAut.conj_apply] using hx_eq.symm
        simpa [hx_eq', mul_assoc] using hx
      have hq :
          (Quotient.mk'' (g * h.1⁻¹) : Quotient (QuotientGroup.rightRel H)) =
            Quotient.mk'' g := by
        apply (Quotient.eq'').2
        simpa [QuotientGroup.rightRel_apply, mul_assoc, mul_inv_rev] using hmem'
      simpa using hq
  -- Convert the orbit descriptions to cardinalities.
  have hleft_card :
      Fintype.card {q // dcL H q = D} = K1.relIndex H := by
    have hleft_equiv :
        {q // dcL H q = D} ≃ MulAction.orbit H (QuotientGroup.mk g : G ⧸ H) := by
      simpa using (Equiv.setCongr hleft_set)
    haveI :
        Finite (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H)) :=
      Finite.of_equiv (MulAction.orbit H (QuotientGroup.mk g : G ⧸ H))
        (MulAction.orbitEquivQuotientStabilizer H
          (QuotientGroup.mk g : G ⧸ H))
    letI := Fintype.ofFinite
      (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H))
    have horbit :
        Fintype.card (MulAction.orbit H (QuotientGroup.mk g : G ⧸ H)) =
          Fintype.card (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H)) := by
      exact
        (Fintype.card_congr (MulAction.orbitEquivQuotientStabilizer H
          (QuotientGroup.mk g : G ⧸ H)))
    have hquot :
        Fintype.card (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H)) = K1.relIndex H := by
      calc
        Fintype.card (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H)) =
            Nat.card (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H)) := by
              exact
                (Nat.card_eq_fintype_card
                  (α := H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H))).symm
        _ = Nat.card (H ⧸ K1.subgroupOf H) := by
              simp [hstab_left]
        _ = K1.relIndex H := by
              simp [Subgroup.relIndex, Subgroup.index]
    calc
      Fintype.card {q // dcL H q = D}
          = Fintype.card (MulAction.orbit H (QuotientGroup.mk g : G ⧸ H)) := by
              exact Fintype.card_congr hleft_equiv
      _ = Fintype.card (H ⧸ MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H)) := horbit
      _ = K1.relIndex H := hquot
  have hright_card :
      Fintype.card {r // dcR H r = D} = K2.relIndex H := by
    have hright_equiv :
        {r // dcR H r = D} ≃
          MulAction.orbit H (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)) := by
      simpa using (Equiv.setCongr hright_set)
    haveI :
        Finite (H ⧸ MulAction.stabilizer H
          (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) :=
      Finite.of_equiv (MulAction.orbit H
        (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)))
        (MulAction.orbitEquivQuotientStabilizer H
          (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)))
    letI := Fintype.ofFinite
      (H ⧸ MulAction.stabilizer H
        (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)))
    have horbit :
        Fintype.card (MulAction.orbit H
          (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) =
          Fintype.card (H ⧸ MulAction.stabilizer H
            (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) := by
      exact
        (Fintype.card_congr (MulAction.orbitEquivQuotientStabilizer H
          (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))))
    have hquot :
        Fintype.card (H ⧸ MulAction.stabilizer H
          (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) = K2.relIndex H := by
      calc
        Fintype.card (H ⧸ MulAction.stabilizer H
            (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) =
            Nat.card (H ⧸ MulAction.stabilizer H
              (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) := by
              exact
                (Nat.card_eq_fintype_card
                  (α := H ⧸ MulAction.stabilizer H
                    (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H)))).symm
        _ = Nat.card (H ⧸ K2.subgroupOf H) := by
              simp [hstab_right]
        _ = K2.relIndex H := by
              simp [Subgroup.relIndex, Subgroup.index]
    calc
      Fintype.card {r // dcR H r = D}
          = Fintype.card (MulAction.orbit H
              (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) := by
              exact Fintype.card_congr hright_equiv
      _ = Fintype.card (H ⧸ MulAction.stabilizer H
            (Quotient.mk'' g : Quotient (QuotientGroup.rightRel H))) := horbit
      _ = K2.relIndex H := hquot
  -- Compare relative indices via indices in `G`.
  have hK2 :
      K1.map (MulAut.conj g⁻¹).toMonoidHom = K2 := by
    have h_inj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom :=
      (MulAut.conj g⁻¹).injective
    calc
      K1.map (MulAut.conj g⁻¹).toMonoidHom
          = (H.map (MulAut.conj g⁻¹).toMonoidHom) ⊓
              (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := by
                simpa [K1] using
                  (Subgroup.map_inf H (H.map (MulAut.conj g).toMonoidHom)
                    (MulAut.conj g⁻¹).toMonoidHom h_inj)
      _ = H.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H := by
            -- simplify the conjugation composition
            have hcomp :
                (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
                  MonoidHom.id G := by
              ext x
              simp [MulAut.conj_apply, MonoidHom.comp_apply, mul_assoc]
            have hmap :
                (H.map (MulAut.conj g).toMonoidHom).map
                    (MulAut.conj g⁻¹).toMonoidHom =
                  H.map ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
              simp [Subgroup.map_map]
            calc
              (H.map (MulAut.conj g⁻¹).toMonoidHom) ⊓
                  (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom
                  =
                  H.map (MulAut.conj g⁻¹).toMonoidHom ⊓
                    H.map ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
                      rw [hmap]
              _ = H.map (MulAut.conj g⁻¹).toMonoidHom ⊓ H := by
                    rw [hcomp]
                    simp [Subgroup.map_id]
      _ = K2 := by
            simp [K2, inf_comm]
  have hindex_eq : K1.index = K2.index := by
    -- conjugate subgroups have equal index
    have hindex_eq' :
        (K1.map (MulAut.conj g⁻¹).toMonoidHom).index = K1.index := by
      exact (Subgroup.index_map_equiv (e := MulAut.conj g⁻¹) (H := K1))
    have hindex_eq'' : K2.index = K1.index := by
      have hindex_eq'' := hindex_eq'
      rw [hK2] at hindex_eq''
      exact hindex_eq''
    exact hindex_eq''.symm
  have hrel : K1.relIndex H = K2.relIndex H := by
    have hmul :
        K1.relIndex H * H.index = K2.relIndex H * H.index := by
      calc
        K1.relIndex H * H.index = K1.index := Subgroup.relIndex_mul_index hK1_le
        _ = K2.index := hindex_eq
        _ = K2.relIndex H * H.index := (Subgroup.relIndex_mul_index hK2_le).symm
    have hpos : 0 < H.index := by
      exact Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))
    exact Nat.mul_right_cancel hpos hmul
  -- Finish.
  calc
    Fintype.card {q // dcL H q = D} = K1.relIndex H := hleft_card
    _ = K2.relIndex H := hrel
    _ = Fintype.card {r // dcR H r = D} := hright_card.symm

-- Reduce the Hall condition to the nonempty case.
lemma hall_condition_left_right_cosets_nonempty {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] {A : Finset (G ⧸ H)} (hA : A.Nonempty) :
    #A ≤ #{r | ∃ q ∈ A, leftRightRel H q r} := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  let I : Finset (DoubleCoset.Quotient (H : Set G) (H : Set G)) := A.image (dcL H)
  have _ := hA
  -- The neighbor set is exactly the preimage of `I` under `dcR`.
  have hneighbors_eq :
      {r | ∃ q ∈ A, leftRightRel H q r} = {r | dcR H r ∈ I} := by
    ext r
    constructor
    · rintro ⟨q, hqA, hrel⟩
      rcases hrel with ⟨g, hgq, hgr⟩
      have hqD : dcL H q = DoubleCoset.mk H H g := by
        rw [← hgq]
        simp [dcL, Quotient.lift_mk]
      have hrD : dcR H r = DoubleCoset.mk H H g := by
        rw [← hgr]
        simp [dcR, Quotient.lift_mk]
      have hI : dcL H q ∈ I := by
        refine Finset.mem_image.2 ?_
        exact ⟨q, hqA, rfl⟩
      simpa [hqD, hrD] using hI
    · intro hr
      rcases Finset.mem_image.1 hr with ⟨q, hqA, hqD⟩
      refine ⟨q, hqA, ?_⟩
      exact leftRightRel_of_same_doubleCoset (H := H) q r (by simp [hqD])
  have hneighbors :
      ∀ D ∈ I, {r | dcR H r = D} ⊆ {r | ∃ q ∈ A, leftRightRel H q r} := by
    intro D hD
    refine neighbors_contains_right_fiber (H := H) (A := A) ?_
    rcases Finset.mem_image.1 hD with ⟨q, hqA, rfl⟩
    exact ⟨q, hqA, rfl⟩
  have hcardA :
      #A = I.sum (fun D => #{q ∈ A | dcL H q = D}) := by
    simpa [I] using (Finset.card_eq_sum_fibers_dcL (H := H) A)
  -- TODO: double-coset counting in the nonempty case.
  -- Bound the fiber-card sum by the neighbor set, using the `hneighbors` inclusions.
  have hle :
      I.sum (fun D => #{q ∈ A | dcL H q = D}) ≤ #{r | dcR H r ∈ I} := by
    classical
    -- First compare each fiber to the corresponding right-coset fiber.
    have hle_sum :
        I.sum (fun D => #{q ∈ A | dcL H q = D}) ≤
          I.sum (fun D => #{r | dcR H r = D}) := by
      refine Finset.sum_le_sum ?_
      intro D hD
      -- Rewrite the left fiber as a subtype card and drop the `q ∈ A` condition.
      have hleft_eq :
          #{q ∈ A | dcL H q = D} = Fintype.card {q // q ∈ A ∧ dcL H q = D} := by
        have hset :
            (A.filter fun q => dcL H q = D) =
              (Finset.univ.filter fun q => q ∈ A ∧ dcL H q = D) := by
          ext q
          simp [Finset.mem_filter]
        calc
          #{q ∈ A | dcL H q = D}
              = #{q | q ∈ A ∧ dcL H q = D} := by
                  simp [hset]
          _ = Fintype.card {q // q ∈ A ∧ dcL H q = D} := by
              symm
              simp [Fintype.card_subtype]
      have hsub :
          Fintype.card {q // q ∈ A ∧ dcL H q = D} ≤
            Fintype.card {q // dcL H q = D} := by
        refine Fintype.card_subtype_mono (p := fun q => q ∈ A ∧ dcL H q = D)
          (q := fun q => dcL H q = D) ?_
        intro q hq
        exact hq.2
      -- Left and right fibers over a double coset have the same cardinality.
      have hfiber_eq :
          Fintype.card {q // dcL H q = D} =
            Fintype.card {r // dcR H r = D} := by
        simpa using (card_dcL_eq_card_dcR (H := H) D)
      have hle_fiber :
          Fintype.card {q // dcL H q = D} ≤
            Fintype.card {r // dcR H r = D} := by
        exact le_of_eq hfiber_eq
      -- Combine and rewrite back to `Finset.card`.
      have hright_eq :
          #{r | dcR H r = D} = Fintype.card {r // dcR H r = D} := by
        symm
        simp [Fintype.card_subtype]
      have hleft_le_right :
          #{q ∈ A | dcL H q = D} ≤ #{r | dcR H r = D} := by
        calc
          #{q ∈ A | dcL H q = D}
              = Fintype.card {q // q ∈ A ∧ dcL H q = D} := hleft_eq
          _ ≤ Fintype.card {q // dcL H q = D} := hsub
          _ ≤ Fintype.card {r // dcR H r = D} := hle_fiber
          _ = #{r | dcR H r = D} := by simp [hright_eq]
      exact hleft_le_right
    -- The right-hand sum is the cardinality of the `dcR`-preimage of `I`.
    have hright_sum :
        I.sum (fun D => #{r | dcR H r = D}) = #{r | dcR H r ∈ I} := by
      classical
      let s : Finset (Quotient (QuotientGroup.rightRel H)) :=
        Finset.univ.filter fun r => dcR H r ∈ I
      have hsum := (Finset.card_eq_sum_card_image (dcR H) s)
      have hcard : s.card = #{r | dcR H r ∈ I} := by
        simp [s]
      have himage : s.image (dcR H) = I := by
        ext D
        constructor
        · intro hD
          rcases Finset.mem_image.1 hD with ⟨r, hr, rfl⟩
          simpa [s, Finset.mem_filter] using hr
        · intro hD
          refine Finset.mem_image.2 ?_
          refine ⟨Quotient.mk'' D.out, ?_, ?_⟩
          · have hDcR : dcR H (Quotient.mk'' D.out) = D := by
              simp [dcR, Quotient.lift_mk]
            simp [s, Finset.mem_filter, hDcR, hD]
          · simp [dcR, Quotient.lift_mk]
      have hfiber :
          ∀ D ∈ I,
            #{r ∈ s | dcR H r = D} = #{r | dcR H r = D} := by
        intro D hD
        classical
        have hpred :
            (fun r => dcR H r ∈ I ∧ dcR H r = D) = fun r => dcR H r = D := by
          funext r
          apply propext
          constructor
          · intro h
            exact h.2
          · intro h
            refine ⟨?_, h⟩
            simpa [h] using hD
        simp [s, Finset.filter_filter, hpred]
      have hsum' :
          s.card = I.sum (fun D => #{r | dcR H r = D}) := by
        classical
        have hsum1 : s.card = I.sum (fun D => #{r ∈ s | dcR H r = D}) := by
          simpa [himage] using hsum
        have hsum2 :
            I.sum (fun D => #{r ∈ s | dcR H r = D}) =
              I.sum (fun D => #{r | dcR H r = D}) := by
          refine Finset.sum_congr rfl ?_
          intro D hD
          exact hfiber D hD
        exact hsum1.trans hsum2
      calc
        I.sum (fun D => #{r | dcR H r = D}) = s.card := hsum'.symm
        _ = #{r | dcR H r ∈ I} := hcard
    exact hle_sum.trans (by simp [hright_sum])
  -- Rewrite the neighbor set using the fiber description.
  have hneighbors_eq' :
      (fun r => ∃ q ∈ A, leftRightRel H q r) = fun r => dcR H r ∈ I := by
    funext r
    have := congrArg (fun s => r ∈ s) hneighbors_eq
    simpa using this
  simpa [hneighbors_eq'] using hcardA.le.trans hle

-- Hall condition for the left/right coset relation.
lemma hall_condition_left_right_cosets {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] :
    ∀ A : Finset (G ⧸ H),
      #A ≤ #{r | ∃ q ∈ A, leftRightRel H q r} := by
  classical
  -- TODO: prove the Hall condition for the left/right coset relation.
  -- This is isolated so the main statement no longer uses `sorry`.
  have :
      ∀ A : Finset (G ⧸ H),
        #A ≤ #{r | ∃ q ∈ A, leftRightRel H q r} := by
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    · have hA' : A.Nonempty := Finset.nonempty_iff_ne_empty.2 hA
      exact hall_condition_left_right_cosets_nonempty (H := H) hA'
  simpa using this

-- Hall's theorem gives an injective matching from left cosets to right cosets.
lemma exists_matching_left_to_right {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃ f : (G ⧸ H) → Quotient (QuotientGroup.rightRel H),
      Function.Injective f ∧ ∀ q, leftRightRel H q (f q) := by
  classical
  have hhall := hall_condition_left_right_cosets (H := H)
  simpa using
    (Fintype.all_card_le_filter_rel_iff_exists_injective (r := leftRightRel H)).1 hhall

-- Upgrade an injective matching to a bijection using the left/right coset equivalence.
lemma matching_bijective {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {f : (G ⧸ H) → Quotient (QuotientGroup.rightRel H)} (hf : Function.Injective f) :
    Function.Bijective f := by
  classical
  letI := H.fintypeQuotientOfFiniteIndex
  have hsurj :
      Function.Surjective f :=
    (Function.Injective.surjective_of_fintype
      (e := (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm) hf)
  exact ⟨hf, hsurj⟩

-- Existence of a representative system that is bijective to right cosets.
lemma exists_bitransversal_representatives {G : Type*} [Group G] (H : Subgroup G)
    [H.FiniteIndex] :
    ∃ s : (G ⧸ H) → G, (∀ q, QuotientGroup.mk (s q) = q) ∧
      Function.Bijective (fun q =>
        (Quotient.mk'' (s q) : Quotient (QuotientGroup.rightRel H))) := by
  classical
  obtain ⟨f, hf_inj, hf_rel⟩ := exists_matching_left_to_right (H := H)
  have hf_bij : Function.Bijective f := matching_bijective (H := H) hf_inj
  let s : (G ⧸ H) → G := fun q => Classical.choose (hf_rel q)
  have hs : ∀ q, QuotientGroup.mk (s q) = q := by
    intro q
    exact (Classical.choose_spec (hf_rel q)).1
  have hs' : ∀ q, Quotient.mk'' (s q) = f q := by
    intro q
    exact (Classical.choose_spec (hf_rel q)).2
  refine ⟨s, hs, ?_⟩
  have hEq : (fun q => Quotient.mk'' (s q)) = f := by
    funext q
    exact hs' q
  simpa [hEq] using hf_bij

/--
Let $H$ be a subgroup of finite index of a group $G$. Show that there exists a subset $S$ of
$G$, such that $S$ is both a set of representatives of the left and the right cosets of $H$
in $G$.
-/
theorem exists_leftCoset_rightCoset_representative
    (G : Type) [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃ S : Set G, Subgroup.IsComplement S H ∧ Subgroup.IsComplement H S := by
  classical
  obtain ⟨s, hs, hbij⟩ := exists_bitransversal_representatives (G := G) (H := H)
  refine ⟨Set.range s, ?_, ?_⟩
  · exact (range_of_s_is_bitransversal (H := H) s hs hbij).1
  · exact (range_of_s_is_bitransversal (H := H) s hs hbij).2

end

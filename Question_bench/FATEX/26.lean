import Mathlib

/-
Let $K/\mathbb{Q}$ be a finite extension.
Let $H$ be a closed subgroup of the absolute Galois group $G(K)$ of $K$.
If $H$ is finite, then the cardinality of $H$ is either one or two.
-/
/-- A natural number bounded by two and nonzero is one or two. -/
lemma nat_eq_one_or_eq_two_of_le_two_of_ne_zero {n : ℕ} (hn : n ≤ 2) (hne : n ≠ 0) :
    n = 1 ∨ n = 2 := by
  cases n with
  | zero =>
      exact (hne rfl).elim
  | succ n =>
      cases n with
      | zero =>
          exact Or.inl rfl
      | succ n =>
          have h1 : n.succ ≤ 1 := Nat.succ_le_succ_iff.mp hn
          have h2 : n ≤ 0 := Nat.succ_le_succ_iff.mp h1
          have h0 : n = 0 := Nat.le_zero.mp h2
          right
          simp [h0]

/-- A finite cyclic subgroup whose elements all have order at most two has cardinality ≤ 2. -/
lemma Subgroup.natCard_le_two_of_isCyclic_of_orderOf_le_two {G : Type*} [Group G]
    (H : Subgroup G) (h_fin : Finite H) (hcyc : IsCyclic H)
    (horder : ∀ h : H, orderOf h ≤ 2) : Nat.card H ≤ 2 := by
  classical
  haveI : Finite H := h_fin
  obtain ⟨g, hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := H)).1 hcyc
  simpa [hg] using (horder g)

/-- A finite group of cardinality at most two is cyclic and has all elements of order ≤ 2. -/
lemma isCyclic_and_orderOf_le_two_of_natCard_le_two {G : Type*} [Group G]
    (h_fin : Finite G) (hcard : Nat.card G ≤ 2) :
    IsCyclic G ∧ (∀ g : G, orderOf g ≤ 2) := by
  classical
  haveI : Finite G := h_fin
  have hne : Nat.card G ≠ 0 :=
    (Nat.card_ne_zero.2 ⟨⟨1⟩, h_fin⟩)
  have hcases : Nat.card G = 1 ∨ Nat.card G = 2 :=
    nat_eq_one_or_eq_two_of_le_two_of_ne_zero hcard hne
  refine ⟨?_, ?_⟩
  · cases hcases with
    | inl h1 =>
        have hsub : Subsingleton G := (Nat.card_eq_one_iff_unique.mp h1).1
        let _ := hsub
        exact (inferInstance : IsCyclic G)
    | inr h2 =>
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card (α := G) (p := 2) h2
  · intro g
    have hle : orderOf g ≤ Nat.card G := orderOf_le_card
    exact hle.trans hcard

/-- The algebraic closure of `K` is an algebraic closure of any intermediate field `L`. -/
lemma isAlgClosure_intermediateField
    (K : Type) [Field K] (L : IntermediateField K (AlgebraicClosure K)) :
    IsAlgClosure L (AlgebraicClosure K) := by
  classical
  -- Avoid a typeclass-search timeout for `NoZeroSMulDivisors`.
  haveI : NoZeroSMulDivisors L (AlgebraicClosure K) :=
    (GroupWithZero.toNoZeroSMulDivisors : NoZeroSMulDivisors L (AlgebraicClosure K))
  refine { isAlgClosed := ?_, isAlgebraic := ?_ }
  · infer_instance
  · infer_instance

/-- A finite Galois group over an algebraic closure gives a finite-dimensional extension. -/
lemma finiteDimensional_of_finite_gal_algClosure
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (L : IntermediateField K (AlgebraicClosure K))
    (h_fin : Finite (Gal(AlgebraicClosure K/L))) :
    FiniteDimensional L (AlgebraicClosure K) := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : IsAlgClosure L (AlgebraicClosure K) :=
    isAlgClosure_intermediateField (K := K) L
  haveI : Finite (Gal(AlgebraicClosure K/L)) := h_fin
  haveI : IsGalois L (AlgebraicClosure K) :=
    IsAlgClosure.isGalois (k := L) (K := AlgebraicClosure K)
  exact IsGalois.finiteDimensional_of_finite (F := L) (E := AlgebraicClosure K)

/-- Rewrite the Galois group cardinality as a finrank. -/
lemma natCard_gal_eq_finrank
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (Gal(E/F)) = Module.finrank F E := by
  simpa using (IsGalois.card_aut_eq_finrank (F := F) (E := E))

/-- A primitive element has minpoly degree equal to the finrank. -/
lemma minpoly_natDegree_eq_finrank_of_primitive
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    {α : E} (hα : F⟮α⟯ = ⊤) :
    (minpoly F α).natDegree = Module.finrank F E := by
  exact (Field.primitive_element_iff_minpoly_natDegree_eq (F := F) (E := E) α).1 hα

/-- Artin–Schreier input: a finite-dimensional algebraic closure has Galois group of order ≤ 2. -/
lemma IsAlgClosure.gal_card_le_two_of_finiteDimensional
    (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosure F E]
    [CharZero F] [FiniteDimensional F E] :
    Nat.card (Gal(E/F)) ≤ 2 := by
  -- TODO: missing arithmetic input (Artin–Schreier) about finite-dimensional algebraic closures.
  sorry

/-- Finite-dimensional algebraic closures have degree at most two. -/
lemma finrank_algClosure_le_two_of_finiteDimensional
    (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosure F E]
    [CharZero F] [FiniteDimensional F E] :
    Module.finrank F E ≤ 2 := by
  classical
  haveI : IsGalois F E := IsAlgClosure.isGalois (k := F) (K := E)
  have hcard : Nat.card (Gal(E/F)) = Module.finrank F E :=
    natCard_gal_eq_finrank (F := F) (E := E)
  have hle : Nat.card (Gal(E/F)) ≤ 2 :=
    IsAlgClosure.gal_card_le_two_of_finiteDimensional (F := F) (E := E)
  simpa [hcard] using hle

/-- A primitive element in a finite-dimensional algebraic closure has minpoly degree at most two. -/
lemma minpoly_natDegree_le_two_of_isAlgClosure_finiteDimensional
    (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosure F E]
    [CharZero F] [FiniteDimensional F E] {α : E} (hα : F⟮α⟯ = ⊤) :
    (minpoly F α).natDegree ≤ 2 := by
  have hfinrank : Module.finrank F E ≤ 2 :=
    finrank_algClosure_le_two_of_finiteDimensional (F := F) (E := E)
  have hdeg : (minpoly F α).natDegree = Module.finrank F E :=
    minpoly_natDegree_eq_finrank_of_primitive (F := F) (E := E) hα
  simpa [hdeg] using hfinrank

/-- Arithmetic input: a finite closed subgroup has order at most two. -/
lemma natCard_gal_algClosure_le_two_of_finite
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (L : IntermediateField K (AlgebraicClosure K))
    (h_fin : Finite (Gal(AlgebraicClosure K/L))) :
    Nat.card (Gal(AlgebraicClosure K/L)) ≤ 2 := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  haveI : IsAlgClosure L (AlgebraicClosure K) :=
    isAlgClosure_intermediateField (K := K) L
  haveI : Finite (Gal(AlgebraicClosure K/L)) := h_fin
  haveI : FiniteDimensional L (AlgebraicClosure K) :=
    finiteDimensional_of_finite_gal_algClosure (K := K) (L := L) h_fin
  haveI : IsGalois L (AlgebraicClosure K) :=
    IsAlgClosure.isGalois (k := L) (K := AlgebraicClosure K)
  have hcard : Nat.card (Gal(AlgebraicClosure K/L)) =
      Module.finrank L (AlgebraicClosure K) :=
    natCard_gal_eq_finrank (F := L) (E := AlgebraicClosure K)
  have hle : Module.finrank L (AlgebraicClosure K) ≤ 2 :=
    finrank_algClosure_le_two_of_finiteDimensional (F := L) (E := AlgebraicClosure K)
  have hle' : Nat.card (Gal(AlgebraicClosure K/L)) ≤ 2 := by
    calc
      Nat.card (Gal(AlgebraicClosure K/L)) = Module.finrank L (AlgebraicClosure K) := hcard
      _ ≤ 2 := hle
  exact hle'

/-- Arithmetic input: a finite closed subgroup has order at most two. -/
lemma absoluteGaloisGroup_natCard_le_two_of_finite_closed
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : Nat.card H ≤ 2 := by
  classical
  let E := AlgebraicClosure K
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  let Hc : ClosedSubgroup (Gal(E/K)) := ⟨H, h_closed⟩
  let L : IntermediateField K E := IntermediateField.fixedField Hc
  have hfix : L.fixingSubgroup = H := by
    simpa [Hc, L] using
      (InfiniteGalois.fixingSubgroup_fixedField (k := K) (K := E) Hc)
  have h_equiv : H ≃* Gal(E/L) :=
    (MulEquiv.subgroupCongr hfix.symm).trans (IntermediateField.fixingSubgroupEquiv (K := L))
  have hcard : Nat.card H = Nat.card (Gal(E/L)) :=
    Nat.card_congr h_equiv.toEquiv
  haveI : Finite H := h_fin
  haveI : Finite (Gal(E/L)) :=
    Finite.of_injective (fun g : Gal(E/L) => (h_equiv.symm g)) (h_equiv.symm.injective)
  have hle : Nat.card (Gal(E/L)) ≤ 2 :=
    natCard_gal_algClosure_le_two_of_finite (K := K) (L := L) (h_fin := inferInstance)
  simpa [hcard] using hle

/-- Number-theoretic input: finite closed subgroups are cyclic and 2-torsion. -/
lemma absoluteGaloisGroup_isCyclic_and_orderOf_le_two_of_finite_closed
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : IsCyclic H ∧ (∀ h : H, orderOf h ≤ 2) := by
  classical
  have hcard : Nat.card H ≤ 2 :=
    absoluteGaloisGroup_natCard_le_two_of_finite_closed K H h_closed h_fin
  exact isCyclic_and_orderOf_le_two_of_natCard_le_two (G := H) h_fin hcard

/-- Arithmetic input: finite closed subgroups are cyclic with all elements of order at most two. -/
lemma absoluteGaloisGroup_isCyclic_and_orderOf_le_two
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : IsCyclic H ∧ (∀ h : H, orderOf h ≤ 2) := by
  exact absoluteGaloisGroup_isCyclic_and_orderOf_le_two_of_finite_closed
    K H h_closed h_fin

/-- Arithmetic input: a finite closed subgroup has order at most two. -/
lemma card_le_two_of_finite_closed_subgroup_of_absoluteGaloisGroup
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : Nat.card H ≤ 2 := by
  exact absoluteGaloisGroup_natCard_le_two_of_finite_closed K H h_closed h_fin

theorem card_one_or_two_of_finite_closed_subgroup_of_absoluteGaloisGroup
    (K : Type) [Field K] [Algebra ℚ K] [Module.Finite ℚ K]
    (H : Subgroup (Field.absoluteGaloisGroup K))
    (h_closed : IsClosed (H : Set (Field.absoluteGaloisGroup K)))
    (h_fin : Finite H) : Nat.card H = 1 ∨ Nat.card H = 2 := by
  classical
  have hne : Nonempty H := ⟨⟨1, H.one_mem⟩⟩
  have hcard_ne : Nat.card H ≠ 0 := (Nat.card_ne_zero.2 ⟨hne, h_fin⟩)
  have hle : Nat.card H ≤ 2 :=
    card_le_two_of_finite_closed_subgroup_of_absoluteGaloisGroup K H h_closed h_fin
  exact nat_eq_one_or_eq_two_of_le_two_of_ne_zero hle hcard_ne

import Mathlib

open Order

/-- The overring order of a valuation subring has the same Krull dimension as the ring. -/
lemma krullDim_overring_eq {K : Type*} [Field K] (A : ValuationSubring K) :
    Order.krullDim {S // A ≤ S} = ringKrullDim A := by
  calc
    Order.krullDim {S // A ≤ S} = Order.krullDim ((PrimeSpectrum A)ᵒᵈ) := by
      simpa using (Order.krullDim_eq_of_orderIso (ValuationSubring.primeSpectrumOrderEquiv A)).symm
    _ = Order.krullDim (PrimeSpectrum A) := by
      simp
    _ = ringKrullDim A := by
      simp [ringKrullDim]

/-- In the overring order, Krull dimension ≤ 1 forces bottom or top. -/
lemma overring_eq_bot_or_top {K : Type*} [Field K] (A : ValuationSubring K)
    (h : Order.krullDim {S // A ≤ S} ≤ 1) (S : {S // A ≤ S}) :
    S = ⟨A, le_rfl⟩ ∨ S = ⟨⊤, A.le_top⟩ := by
  have hminmax : IsMin S ∨ IsMax S :=
    (Order.krullDim_le_one_iff (α := {S // A ≤ S})).1 h S
  refine hminmax.elim ?_ ?_
  · intro hmin
    left
    apply Subtype.ext
    have hle : (⟨A, le_rfl⟩ : {S // A ≤ S}) ≤ S := S.property
    have hge : S ≤ (⟨A, le_rfl⟩ : {S // A ≤ S}) := hmin hle
    exact le_antisymm hge hle
  · intro hmax
    right
    apply Subtype.ext
    have hle : S ≤ (⟨⊤, A.le_top⟩ : {S // A ≤ S}) := by
      exact (ValuationSubring.le_top (A := S.1))
    have hge : (⟨⊤, A.le_top⟩ : {S // A ≤ S}) ≤ S := hmax hle
    exact le_antisymm hle hge

/-- If $R$ is a valuation ring of Krull dimension 1 and $K$ its field of fractions, then there do
not exist any rings intermediate between $R$ and $K$. -/
theorem eq_bot_or_eq_top_of_ringKrullDim_eq_one {R K : Type} [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] [ValuationRing R] (hD : ringKrullDim R = 1)
    (S : Subalgebra R K) : S = ⊥ ∨ S = ⊤ := by
  classical
  let R₀ : ValuationSubring K := (ValuationRing.valuation R K).valuationSubring
  have hR₀ : ringKrullDim R₀ = 1 := by
    have hEquiv :=
      (ValuationRing.equivInteger (A := R) (K := K)).ringKrullDim
    have hR₀' : ringKrullDim ((ValuationRing.valuation R K).integer) = 1 := by
      calc
        ringKrullDim ((ValuationRing.valuation R K).integer)
            = ringKrullDim R := by simpa using hEquiv.symm
        _ = 1 := hD
    simpa [R₀] using hR₀'
  have hDim : Order.krullDim {S // R₀ ≤ S} ≤ 1 := by
    simpa [krullDim_overring_eq] using (le_of_eq hR₀)
  have hR₀S : R₀.toSubring ≤ S.toSubring := by
    intro x hx
    have hx' :
        x ∈ (ValuationRing.valuation R K).integer := by
      simpa [R₀] using hx
    obtain ⟨r, rfl⟩ := (ValuationRing.mem_integer_iff (A := R) (K := K) x).1 hx'
    exact Subalgebra.mem_toSubring.mpr (by simp)
  let S₀ : ValuationSubring K := ValuationSubring.ofLE R₀ S.toSubring hR₀S
  have hS₀ : R₀ ≤ S₀ := by
    intro x hx
    have hx' : x ∈ S.toSubring := hR₀S hx
    simpa [S₀] using hx'
  let hS₀' : {S // R₀ ≤ S} := ⟨S₀, hS₀⟩
  have hS₀eq := overring_eq_bot_or_top (A := R₀) hDim hS₀'
  refine hS₀eq.elim ?_ ?_
  · intro hEq
    left
    have hS₀val : S₀ = R₀ := by
      simpa [hS₀'] using congrArg Subtype.val hEq
    have hSubring : S.toSubring = (⊥ : Subalgebra R K).toSubring := by
      have h' := congrArg ValuationSubring.toSubring hS₀val
      have hR₀range : R₀.toSubring = (algebraMap R K).range := by
        simpa [R₀] using (ValuationRing.range_algebraMap_eq (A := R) (K := K))
      dsimp [S₀] at h'
      calc
        S.toSubring = R₀.toSubring := h'
        _ = (algebraMap R K).range := hR₀range
        _ = (⊥ : Subalgebra R K).toSubring := rfl
    exact (Subalgebra.toSubring_inj (S := S) (U := ⊥)).1 hSubring
  · intro hEq
    right
    have hS₀val : S₀ = ⊤ := by
      simpa [hS₀'] using congrArg Subtype.val hEq
    have hSubring : S.toSubring = (⊤ : Subalgebra R K).toSubring := by
      have h' := congrArg ValuationSubring.toSubring hS₀val
      dsimp [S₀] at h'
      exact h'
    exact (Subalgebra.toSubring_inj (S := S) (U := ⊤)).1 hSubring

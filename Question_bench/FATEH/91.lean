import Mathlib

/-- A maximal proper subring of a field is the underlying subring of a valuation subring. -/
lemma exists_valuationSubring_of_isCoatom {K : Type} [Field K] (R : Subring K)
    (h : IsCoatom R) (hR : ¬ IsField R) :
    ∃ V : ValuationSubring K, V.toSubring = R := by
  classical
  obtain ⟨p, hp_ne_bot, hp_prime⟩ := (Ring.not_isField_iff_exists_prime (R := R)).1 hR
  let A : LocalSubring K := LocalSubring.ofPrime R p
  have hA_le : R ≤ A.toSubring := LocalSubring.le_ofPrime (A := R) (P := p)
  have hA_ne_top : (A.toSubring : Subring K) ≠ ⊤ := by
    intro htop
    have hp_lt : (⊥ : Ideal R) < p := bot_lt_iff_ne_bot.mpr hp_ne_bot
    obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt hp_lt
    have hx_mem : (algebraMap R A.toSubring x) ∈ IsLocalRing.maximalIdeal A.toSubring := by
      have hx' := (IsLocalization.AtPrime.to_map_mem_maximal_iff (S := A.toSubring) (I := p) x)
      exact (hx').2 hx
    have hx_nonunit : ¬ IsUnit (algebraMap R A.toSubring x) := by
      exact (IsLocalRing.mem_maximalIdeal _).1 hx_mem
    have hx_unit : IsUnit (algebraMap R A.toSubring x) := by
      have hx_inv_mem : (x⁻¹ : K) ∈ A.toSubring := by
        simp [htop]
      refine isUnit_iff_exists_inv.mpr ?_
      refine ⟨⟨x⁻¹, hx_inv_mem⟩, ?_⟩
      ext
      have hx0' : (x : K) ≠ 0 := by
        simpa using hx0
      change (x : K) * (x : K)⁻¹ = (1 : K)
      simp [hx0']
    exact (hx_nonunit hx_unit)
  have hA_eq : A.toSubring = R := by
    rcases (IsCoatom.le_iff h).1 hA_le with htop' | hEq
    · exact (hA_ne_top htop').elim
    · simp [hEq]
  let Rloc : LocalSubring K := A
  have hRloc : Rloc.toSubring = R := by
    simp [Rloc, hA_eq]
  have hmax : IsMax Rloc := by
    intro S hS
    have hRS : R ≤ S.toSubring := by
      simpa [hRloc, Rloc] using hS.1
    rcases (IsCoatom.le_iff h).1 hRS with htop' | hEq
    · haveI : IsLocalHom (Subring.inclusion hS.1) := hS.2
      have hfieldRloc : IsField Rloc.toSubring := by
        refine ⟨⟨0, 1, by simp⟩, ?_, ?_⟩
        · intro x y
          simpa using mul_comm x y
        · intro a ha
          have hunit_map : IsUnit (Subring.inclusion hS.1 a) := by
            have ha_inv_mem : (a⁻¹ : K) ∈ S.toSubring := by
              simp [htop']
            refine isUnit_iff_exists_inv.mpr ?_
            refine ⟨⟨a⁻¹, ha_inv_mem⟩, ?_⟩
            ext
            have ha0' : (a : K) ≠ 0 := by
              simpa using ha
            change (a : K) * (a : K)⁻¹ = (1 : K)
            simp [ha0']
          have hunit : IsUnit a :=
            isUnit_of_map_unit (f := Subring.inclusion hS.1) a hunit_map
          rcases hunit with ⟨u, rfl⟩
          refine ⟨(u⁻¹ : Units Rloc.toSubring), ?_⟩
          simp
      have hfieldR : IsField R := by
        exact (hRloc ▸ hfieldRloc)
      exact (hR hfieldR).elim
    · have : S = Rloc := by
        apply LocalSubring.toSubring_injective
        simp [Rloc, hRloc, hEq]
      simp [this]
  obtain ⟨V, hV⟩ := LocalSubring.exists_valuationRing_of_isMax (R := Rloc) hmax
  refine ⟨V, ?_⟩
  have := congrArg LocalSubring.toSubring hV
  simpa [hRloc] using this

/-- If a ring \( R \), not a field, is a maximal proper subring of a field \( K \), show \( R \)
is a valuation ring of Krull dimension 1. -/
theorem exists_toSubring_eq_and_ringKrullDim_eq_one {K : Type} [Field K] (R : Subring K)
    (h : IsCoatom R) (hR : ¬ IsField R) :
    (∃ V : ValuationSubring K, V.toSubring = R) ∧ ringKrullDim R = 1 := by
  classical
  obtain ⟨V, hV⟩ := exists_valuationSubring_of_isCoatom (R := R) h hR
  -- Build a bounded order on valuation overrings of `V`.
  letI : BoundedOrder {S // V ≤ S} :=
    { top := ⟨⊤, V.le_top⟩
      le_top := by
        intro S
        exact ValuationSubring.le_top (A := S.1)
      bot := ⟨V, le_rfl⟩
      bot_le := by
        intro S
        exact S.property }
  -- Show the overring order of `V` is simple.
  have hVne : V ≠ ⊤ := by
    intro hVtop
    have hVtop' : V.toSubring = ⊤ := by
      simpa using congrArg ValuationSubring.toSubring hVtop
    have hRtop : R = ⊤ := by
      exact hV.symm.trans hVtop'
    have hfieldTop : IsField (⊤ : Subring K) := by
      simpa using (MulEquiv.isField (A := (⊤ : Subring K)) (B := K)
        (Field.toIsField K) (Subring.topEquiv.toMulEquiv))
    exact hR (hRtop ▸ hfieldTop)
  have hbotne : (⟨V, le_rfl⟩ : {S // V ≤ S}) ≠ ⟨⊤, V.le_top⟩ := by
    intro hEq
    apply hVne
    have hEq' : (V : ValuationSubring K) = (⊤ : ValuationSubring K) := by
      simpa using congrArg Subtype.val hEq
    exact hEq'
  haveI : Nontrivial {S // V ≤ S} := ⟨⟨⟨V, le_rfl⟩, ⟨⊤, V.le_top⟩, hbotne⟩⟩
  have hsimple : IsSimpleOrder {S // V ≤ S} := by
    refine IsSimpleOrder.of_forall_eq_top ?_
    intro S hne
    have hSsub' : V.toSubring ≤ S.1.toSubring := by
      intro x hx
      exact S.property hx
    have hSsub : R ≤ S.1.toSubring := by
      simpa [hV] using hSsub'
    rcases (IsCoatom.le_iff h).1 hSsub with htop' | hEq'
    · -- `S` is the top element.
      apply Subtype.ext
      apply ValuationSubring.toSubring_injective
      simpa using htop'
    · -- `S` would be bottom, contradicting `hne`.
      have hSval : S.1 = V := by
        apply ValuationSubring.toSubring_injective
        simpa [hV] using hEq'
      exact (hne (Subtype.ext hSval)).elim
  haveI := hsimple
  have hdim_over : Order.krullDim {S // V ≤ S} = 1 := by
    simp
  have hdim_val : ringKrullDim V = 1 := by
    -- Identify `ringKrullDim V` with the overring order.
    have hkrull : Order.krullDim {S // V ≤ S} = ringKrullDim V := by
      calc
        Order.krullDim {S // V ≤ S}
            = Order.krullDim ((PrimeSpectrum V)ᵒᵈ) := by
                simpa using
                  (Order.krullDim_eq_of_orderIso (ValuationSubring.primeSpectrumOrderEquiv V)).symm
        _ = Order.krullDim (PrimeSpectrum V) := by
            simp
        _ = ringKrullDim V := by
            simp [ringKrullDim]
    calc
      ringKrullDim V = Order.krullDim {S // V ≤ S} := by
        symm
        exact hkrull
      _ = 1 := hdim_over
  have hdim_R : ringKrullDim R = 1 := by
    -- Rewrite via `hV`.
    have hdim_Vsub : ringKrullDim V.toSubring = 1 := by
      simpa using hdim_val
    exact (hV ▸ hdim_Vsub)
  exact ⟨⟨V, hV⟩, hdim_R⟩

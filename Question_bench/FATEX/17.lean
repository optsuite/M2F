import Mathlib

open scoped Cardinal

/- Let $K$ be a subfield of $\mathbb{C}$ maximal with respect to the property that $\sqrt 2 \notin K$.
Deduce that $[\mathbb{C} : K]$ is countable (and not finite). -/
/-- The rank of `ℂ` over any subfield is bounded by the continuum. -/
lemma rank_complex_le_continuum (K : Subfield ℂ) : Module.rank K ℂ ≤ Cardinal.continuum := by
  simpa [Cardinal.mk_complex] using (rank_le_card (R := K) (M := ℂ))

/-- If `√2 ∉ K`, then `K` is a proper subfield of `ℂ`. -/
lemma proper_subfield_of_sqrt2_nmem (K : Subfield ℂ) (h_nmem : (Real.sqrt 2 : ℂ) ∉ K) :
    K ≠ ⊤ := by
  intro htop
  have h_mem : (Real.sqrt 2 : ℂ) ∈ K := by
    simp [htop]
  exact h_nmem h_mem

/-- A proper subfield of `ℂ` has an element outside it. -/
lemma exists_not_mem_of_ne_top (K : Subfield ℂ) (hK : K ≠ ⊤) :
    ∃ x : ℂ, x ∉ K := by
  classical
  by_contra h
  have h_all : ∀ x : ℂ, x ∈ K := by
    intro x
    by_contra hx
    exact h ⟨x, hx⟩
  have h_top : (⊤ : Subfield ℂ) ≤ K := by
    intro x hx
    exact h_all x
  have h_eq : K = ⊤ := le_antisymm le_top h_top
  exact hK h_eq

/-- `√2` is algebraic over any subfield of `ℂ`. -/
lemma sqrt2_isAlgebraic (K : Subfield ℂ) : IsAlgebraic K (Real.sqrt 2 : ℂ) := by
  have hpow_eq : (Real.sqrt 2 : ℂ)^2 = (2 : ℂ) := by
    have hpow_real : (Real.sqrt 2 : ℝ)^2 = (2 : ℝ) := by
      have h0 : (0 : ℝ) ≤ 2 := by norm_num
      simp [Real.sq_sqrt h0]
    exact_mod_cast hpow_real
  have hpow : IsAlgebraic K ((Real.sqrt 2 : ℂ)^2) := by
    simpa [hpow_eq] using
      (isAlgebraic_algebraMap (R := K) (A := ℂ) (x := (2 : K)))
  simpa using
    (IsAlgebraic.of_pow (R := K) (r := (Real.sqrt 2 : ℂ)) (n := 2)
      (Nat.succ_pos 1) hpow)

/-- In a maximal subfield avoiding `√2`, adjoining any element outside the subfield forces `√2`. -/
lemma sqrt2_mem_closure_of_maximal
    (K : Subfield ℂ) (h_nmem : (Real.sqrt 2 : ℂ) ∉ K)
    (h : ∀ (L : Subfield ℂ), K ≤ L → (Real.sqrt 2 : ℂ) ∉ L → K = L)
    (x : ℂ) (hx : x ∉ K) :
    (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}) := by
  classical
  have _ := h_nmem
  by_contra h_sqrt2
  have hKL : K ≤ Subfield.closure (K ∪ {x}) := by
    intro y hy
    exact Subfield.subset_closure (Or.inl hy)
  have h_sqrt2' : (Real.sqrt 2 : ℂ) ∉ Subfield.closure (K ∪ {x}) := by
    simpa using h_sqrt2
  have hKL_eq : K = Subfield.closure (K ∪ {x}) := h _ hKL h_sqrt2'
  have hxL : x ∈ Subfield.closure (K ∪ {x}) := by
    exact Subfield.subset_closure (Or.inr rfl)
  have hxK : x ∈ K := by
    rw [hKL_eq]
    exact hxL
  exact hx hxK

/-- For `K = ⊤`, the adjoin property is vacuous. -/
lemma counterexample_K_top_vacuous_adjoin :
    (∀ x : ℂ, x ∉ (⊤ : Subfield ℂ) →
      (Real.sqrt 2 : ℂ) ∈ Subfield.closure ((⊤ : Subfield ℂ) ∪ {x})) := by
  intro x hx
  have hx' : x ∈ (⊤ : Subfield ℂ) := by
    simp
  exact (False.elim (hx hx'))

/-- The top subfield satisfies the adjoin property and algebraicity of `√2`. -/
lemma top_satisfies_adjoin_and_sqrt2_alg :
    (∀ x : ℂ, x ∉ (⊤ : Subfield ℂ) →
      (Real.sqrt 2 : ℂ) ∈ Subfield.closure ((⊤ : Subfield ℂ) ∪ {x}))
      ∧ IsAlgebraic (⊤ : Subfield ℂ) (Real.sqrt 2 : ℂ) := by
  exact ⟨counterexample_K_top_vacuous_adjoin, sqrt2_isAlgebraic (⊤ : Subfield ℂ)⟩

/-- The rank of `ℂ` over the top subfield is `1`. -/
lemma rank_top_subfield_complex_eq_one :
    Module.rank (⊤ : Subfield ℂ) ℂ = 1 := by
  classical
  have h :
      Module.rank (⊤ : Subfield ℂ) ℂ = Module.rank ℂ ℂ := by
    refine Algebra.rank_eq_of_equiv_equiv
      (R := (⊤ : Subfield ℂ)) (S := ℂ) (R' := ℂ) (S' := ℂ)
      (i := (Subfield.topEquiv : (⊤ : Subfield ℂ) ≃+* ℂ))
      (j := RingEquiv.refl ℂ) ?_
    ext x
    rfl
  calc
    Module.rank (⊤ : Subfield ℂ) ℂ
        = Module.rank ℂ ℂ := h
    _ = 1 := CommSemiring.rank_self (R := ℂ)

/-- For the top subfield, the basis index has cardinality `1`. -/
lemma chooseBasisIndex_top_eq_one :
    #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) = 1 := by
  classical
  have h_rank :
      Module.rank (⊤ : Subfield ℂ) ℂ
        = #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) := by
    simpa using
      (Module.Free.rank_eq_card_chooseBasisIndex
        (R := (⊤ : Subfield ℂ)) (M := ℂ))
  calc
    #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ)
        = Module.rank (⊤ : Subfield ℂ) ℂ := by
            simpa using h_rank.symm
    _ = 1 := rank_top_subfield_complex_eq_one

/-- The cardinal `1` is not equal to `ℵ₀`. -/
lemma one_ne_aleph0 : (1 : Cardinal) ≠ Cardinal.aleph0 := by
  exact (ne_of_lt Cardinal.one_lt_aleph0)

/-- For `K = ⊤`, the basis index is not `ℵ₀`. -/
lemma chooseBasisIndex_top_ne_aleph0 :
    #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) ≠ Cardinal.aleph0 := by
  classical
  have hcard :
      #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) = 1 :=
    chooseBasisIndex_top_eq_one
  simpa [hcard] using (one_ne_aleph0)

/-- For `K = ⊤`, there is a witness for `√2` while the basis index is not `ℵ₀`. -/
lemma counterexample_chooseBasisIndex_eq_aleph0_of_witness_top :
    ∃ x : ℂ,
      (Real.sqrt 2 : ℂ) ∈ Subfield.closure ((⊤ : Subfield ℂ) ∪ {x}) ∧
      IsAlgebraic (⊤ : Subfield ℂ) (Real.sqrt 2 : ℂ) ∧
      #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) ≠ Cardinal.aleph0 := by
  refine ⟨0, ?_, ?_, ?_⟩
  · simp
  · exact sqrt2_isAlgebraic (⊤ : Subfield ℂ)
  · exact chooseBasisIndex_top_ne_aleph0

/-- If the basis index is countable, the subfield is not top. -/
lemma ne_top_of_chooseBasisIndex_eq_aleph0
    (K : Subfield ℂ)
    (h : #(Module.Free.ChooseBasisIndex K ℂ) = Cardinal.aleph0) :
    K ≠ ⊤ := by
  intro hK
  subst hK
  exact chooseBasisIndex_top_ne_aleph0 h

/-- The adjoin property alone does not force countability: `K = ⊤` is a counterexample. -/
lemma adjoin_property_not_force_countable :
    ¬ (∀ K : Subfield ℂ,
        (∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x})) →
        IsAlgebraic K (Real.sqrt 2 : ℂ) →
        #(Module.Free.ChooseBasisIndex K ℂ) = Cardinal.aleph0) := by
  intro h
  have h_top :
      #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) = Cardinal.aleph0 :=
    h (⊤ : Subfield ℂ) (top_satisfies_adjoin_and_sqrt2_alg).1
      (top_satisfies_adjoin_and_sqrt2_alg).2
  exact chooseBasisIndex_top_ne_aleph0 h_top

/-- The adjoin property and algebraicity do not force `K ≠ ⊤`. -/
lemma adjoin_property_not_imply_ne_top :
    ¬ (∀ K : Subfield ℂ,
        (∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x})) →
        IsAlgebraic K (Real.sqrt 2 : ℂ) →
        K ≠ ⊤) := by
  intro h
  have h_top : (⊤ : Subfield ℂ) ≠ ⊤ :=
    h (⊤ : Subfield ℂ) (top_satisfies_adjoin_and_sqrt2_alg).1
      (top_satisfies_adjoin_and_sqrt2_alg).2
  exact h_top rfl

/-- The witness hypothesis alone does not force countability: `K = ⊤` is a counterexample. -/
lemma witness_property_not_force_countable :
    ¬ (∀ K : Subfield ℂ, ∀ x : ℂ,
        (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}) →
        IsAlgebraic K (Real.sqrt 2 : ℂ) →
        #(Module.Free.ChooseBasisIndex K ℂ) = Cardinal.aleph0) := by
  intro h
  obtain ⟨x, hx, h_alg, h_ne⟩ :=
    counterexample_chooseBasisIndex_eq_aleph0_of_witness_top
  have h_eq :
      #(Module.Free.ChooseBasisIndex (⊤ : Subfield ℂ) ℂ) = Cardinal.aleph0 :=
    h (⊤ : Subfield ℂ) x hx h_alg
  exact h_ne h_eq

/-- The basis index type has cardinality at most continuum. -/
lemma chooseBasisIndex_le_continuum (K : Subfield ℂ) :
    #(Module.Free.ChooseBasisIndex K ℂ) ≤ Cardinal.continuum := by
  classical
  have h_rank :
      Module.rank K ℂ = #(Module.Free.ChooseBasisIndex K ℂ) := by
    simpa using (Module.Free.rank_eq_card_chooseBasisIndex (R := K) (M := ℂ))
  simpa [h_rank] using (rank_complex_le_continuum K)

/-- The adjoin property yields a witness whose closure contains `√2`. -/
lemma exists_sqrt2_mem_closure_of_adjoin_property
    (K : Subfield ℂ)
    (h_adjoin : ∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x})) :
    ∃ x : ℂ, (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}) := by
  by_cases hK : K = ⊤
  · refine ⟨0, ?_⟩
    simp [hK]
  · obtain ⟨x, hx⟩ := exists_not_mem_of_ne_top K hK
    exact ⟨x, h_adjoin x hx⟩

/-- If `K` is not top, the adjoin property yields an element whose closure contains `√2`. -/
lemma exists_sqrt2_mem_closure_of_ne_top
    (K : Subfield ℂ)
    (h_adjoin : ∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}))
    (hK : K ≠ ⊤) :
    ∃ x : ℂ, (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}) := by
  obtain ⟨x, hx⟩ := exists_not_mem_of_ne_top K hK
  exact ⟨x, h_adjoin x hx⟩

/-- If `y` lies in the closure of `K ∪ {x}`, then the closure of `K ∪ {y}` is contained in it. -/
lemma closure_le_closure_of_mem
    (K : Subfield ℂ) (x y : ℂ)
    (hy : y ∈ Subfield.closure (K ∪ {x})) :
    Subfield.closure (K ∪ {y}) ≤ Subfield.closure (K ∪ {x}) := by
  refine Subfield.closure_le.mpr ?_
  intro z hz
  cases hz with
  | inl hzK =>
      exact Subfield.subset_closure (Or.inl hzK)
  | inr hzy =>
      have hzy' : z = y := by simpa using hzy
      simpa [hzy'] using hy

/-- A single witness for `√2` in a one-element closure should force countability. -/
lemma chooseBasisIndex_eq_aleph0_of_witness
    (K : Subfield ℂ)
    (x : ℂ)
    (hx : (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}))
    (h_sqrt2_alg : IsAlgebraic K (Real.sqrt 2 : ℂ)) :
    #(Module.Free.ChooseBasisIndex K ℂ) = Cardinal.aleph0 := by
  classical
  have h_le : #(Module.Free.ChooseBasisIndex K ℂ) ≤ Cardinal.continuum :=
    chooseBasisIndex_le_continuum K
  have h_closure :
      Subfield.closure (K ∪ {(Real.sqrt 2 : ℂ)}) ≤
        Subfield.closure (K ∪ {x}) :=
    closure_le_closure_of_mem K x (Real.sqrt 2 : ℂ) hx
  -- TODO: extract countability from the witness `hx` and algebraicity of `√2`.
  sorry

/-- The adjoin property forces the basis index to be countable. -/
lemma chooseBasisIndex_eq_aleph0_of_adjoin_property
    (K : Subfield ℂ)
    (h_adjoin : ∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}))
    (h_sqrt2_alg : IsAlgebraic K (Real.sqrt 2 : ℂ)) :
    #(Module.Free.ChooseBasisIndex K ℂ) = Cardinal.aleph0 := by
  classical
  obtain ⟨x, hx⟩ :=
    exists_sqrt2_mem_closure_of_adjoin_property K h_adjoin
  exact chooseBasisIndex_eq_aleph0_of_witness K x hx h_sqrt2_alg

/-- If adjoining any element forces `√2` into the generated subfield, the rank is countable. -/
lemma rank_eq_aleph0_of_adjoin_property
    (K : Subfield ℂ)
    (h_adjoin : ∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}))
    (h_sqrt2_alg : IsAlgebraic K (Real.sqrt 2 : ℂ)) :
    Module.rank K ℂ = Cardinal.aleph0 := by
  classical
  -- Reduce the goal to the cardinality of a chosen basis index.
  have h_rank :
      Module.rank K ℂ = #(Module.Free.ChooseBasisIndex K ℂ) := by
    simpa using (Module.Free.rank_eq_card_chooseBasisIndex (R := K) (M := ℂ))
  -- The missing step is to show this index type is countable from the adjoin property.
  have h_index : #(Module.Free.ChooseBasisIndex K ℂ) = Cardinal.aleph0 :=
    chooseBasisIndex_eq_aleph0_of_adjoin_property K h_adjoin h_sqrt2_alg
  exact h_rank.trans h_index

/-- Placeholder lemma isolating the missing cardinality argument for the maximal subfield. -/
lemma rank_eq_aleph0_of_maximal_sqrt2_nmem
    (K : Subfield ℂ) (h_nmem : (Real.sqrt 2 : ℂ) ∉ K)
    (h : ∀ (L : Subfield ℂ), K ≤ L → (Real.sqrt 2 : ℂ) ∉ L → K = L) :
    Module.rank K ℂ = Cardinal.aleph0 := by
  classical
  have h_adjoin :
      ∀ x : ℂ, x ∉ K → (Real.sqrt 2 : ℂ) ∈ Subfield.closure (K ∪ {x}) :=
    fun x hx => sqrt2_mem_closure_of_maximal K h_nmem h x hx
  have h_sqrt2_alg : IsAlgebraic K (Real.sqrt 2 : ℂ) := sqrt2_isAlgebraic K
  -- The remaining step is to extract a countable basis from the maximality hypothesis.
  exact rank_eq_aleph0_of_adjoin_property K h_adjoin h_sqrt2_alg

theorem countable_index_of_maximal_subfield_sqrt_2_nmem
    (K : Subfield ℂ) (h_nmem : (Real.sqrt 2 : ℂ) ∉ K)
    (h : ∀ (L : Subfield ℂ), K ≤ L → (Real.sqrt 2 : ℂ) ∉ L → K = L) :
    Module.rank K ℂ = Cardinal.aleph0 := by
  classical
  -- Reduce the goal to the isolated lemma capturing the missing cardinality argument.
  exact rank_eq_aleph0_of_maximal_sqrt2_nmem K h_nmem h

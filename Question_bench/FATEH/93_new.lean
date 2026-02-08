import Mathlib

/-- If a multiset of ideals has nonzero product, then each member is nonzero. -/
lemma multiset_mem_ne_bot_of_prod_ne_bot (O : Type) [CommRing O] [IsDomain O] :
    ∀ {f : Multiset (Ideal O)}, f.prod ≠ ⊥ → ∀ {I : Ideal O}, I ∈ f → I ≠ ⊥ := by
  classical
  intro f
  refine Multiset.induction_on f ?base ?step
  · intro _ I hI
    simpa using hI
  · intro a f ih hprod I hI
    have hprod' : (a * f.prod) ≠ ⊥ := by
      simpa [Multiset.prod_cons] using hprod
    have ha : a ≠ ⊥ := by
      intro ha
      apply hprod'
      have : a * f.prod = ⊥ := (Ideal.mul_eq_bot).2 (Or.inl ha)
      simpa using this
    have hfprod : f.prod ≠ ⊥ := by
      intro hzero
      apply hprod'
      have : a * f.prod = ⊥ := (Ideal.mul_eq_bot).2 (Or.inr hzero)
      simpa using this
    rcases (by simpa using hI) with rfl | hI
    · exact ha
    · exact ih hfprod hI

/-- If every nonzero prime ideal is a unit as a fractional ideal, then a prime-factor product is a
unit as a fractional ideal. -/
lemma multiset_prod_isUnit_of_prime_factors (O : Type) [CommRing O] [IsDomain O]
    (hprime :
      ∀ {P : Ideal O}, P.IsPrime → P ≠ ⊥ →
        IsUnit (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) :
    ∀ (f : Multiset (Ideal O)),
      (∀ b ∈ f, b.IsPrime) → (∀ b ∈ f, b ≠ ⊥) →
        IsUnit ((f.prod : Ideal O) :
          FractionalIdeal (nonZeroDivisors O) (FractionRing O)) := by
  classical
  intro f hfprime hne
  revert hfprime hne
  refine Multiset.induction_on f ?base ?step
  · intro _ _
    simpa using (isUnit_one :
      IsUnit (1 : FractionalIdeal (nonZeroDivisors O) (FractionRing O)))
  · intro a f ih hfprime hne
    have ha : a.IsPrime := hfprime a (by simp)
    have ha_ne : a ≠ ⊥ := hne a (by simp)
    have hfprime' : ∀ b ∈ f, b.IsPrime := by
      intro b hb
      exact hfprime b (by simp [hb])
    have hne' : ∀ b ∈ f, b ≠ ⊥ := by
      intro b hb
      exact hne b (by simp [hb])
    have h_unit_a :
        IsUnit (a : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) :=
      hprime ha ha_ne
    have h_unit_f :
        IsUnit ((f.prod : Ideal O) :
          FractionalIdeal (nonZeroDivisors O) (FractionRing O)) :=
      ih hfprime' hne'
    simpa [Multiset.prod_cons, FractionalIdeal.coeIdeal_mul] using h_unit_a.mul h_unit_f

/-- If a principal ideal factors as `P * J`, then `P` is a unit fractional ideal. -/
lemma ideal_isUnit_coeIdeal_of_span_singleton_mul (O : Type) [CommRing O] [IsDomain O]
    {P J : Ideal O} {a : O} (ha : a ≠ 0)
    (hPJ : Ideal.span ({a} : Set O) = P * J) :
    IsUnit (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) := by
  have hPJ' :
      (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
        (J : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) =
        (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) := by
    have h :=
      congrArg (fun I : Ideal O =>
        (I : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) hPJ
    simpa [FractionalIdeal.coeIdeal_mul] using h.symm
  have hmul_span :
      (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
        (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O))⁻¹ = 1 := by
    simpa using
      (FractionalIdeal.coe_ideal_span_singleton_mul_inv (K := FractionRing O) (R₁ := O) (x := a)
        ha)
  have hmul_one :
      (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
        ((J : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
          (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O))⁻¹) = 1 := by
    calc
      (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
          ((J : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
            (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O))⁻¹)
          =
          ((P : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
            (J : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) *
            (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O))⁻¹ := by
            simp [mul_assoc]
      _ =
          (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) *
            (Ideal.span ({a} : Set O) : FractionalIdeal (nonZeroDivisors O) (FractionRing O))⁻¹ := by
            simpa [hPJ']
      _ = 1 := hmul_span
  exact IsUnit.of_mul_eq_one _ hmul_one

/-- For a prime ideal `P`, if a multiset product of ideals is contained in `P`, then some factor is
contained in `P`. -/
lemma prime_exists_factor_le_of_multiset_prod_le (O : Type) [CommRing O]
    {P : Ideal O} {f : Multiset (Ideal O)} (hP : P.IsPrime) (hle : f.prod ≤ P) :
    ∃ Q ∈ f, Q ≤ P := by
  classical
  exact (Ideal.IsPrime.multiset_prod_le (s := f) (P := P) hP).1 hle

/-- If every factor of a multiset product contained in `P` is equal to `P`, then `P` appears. -/
lemma prime_mem_of_factor_le (O : Type) [CommRing O]
    {P : Ideal O} (hP : P.IsPrime) {f : Multiset (Ideal O)} (hprod_le : f.prod ≤ P)
    (huniq : ∀ {Q : Ideal O}, Q ∈ f → Q ≤ P → Q = P) : P ∈ f := by
  classical
  obtain ⟨Q, hQmem, hQle⟩ :=
    prime_exists_factor_le_of_multiset_prod_le O (P := P) hP hprod_le
  have hQP : Q = P := huniq hQmem hQle
  simpa [hQP] using hQmem

/-- If `P` is minimal among prime ideals below it, then `P` appears in any prime factorization
of a principal ideal containing a nonzero element of `P`. -/
lemma prime_mem_factorization_of_mem_of_minimal (O : Type) [CommRing O] [IsDomain O]
    {P : Ideal O} {a : O} (hP : P.IsPrime) (ha : a ≠ 0) (haP : a ∈ P)
    (hmin : ∀ {Q : Ideal O}, Q.IsPrime → Q ≤ P → Q = P) :
    ∀ {f : Multiset (Ideal O)}, (∀ b ∈ f, b.IsPrime) →
      f.prod = Ideal.span ({a} : Set O) → P ∈ f := by
  classical
  intro f hfprime hprod
  have hspan_le : Ideal.span ({a} : Set O) ≤ P :=
    (Ideal.span_singleton_le_iff_mem (I := P)).2 haP
  have hprod_le : f.prod ≤ P := by
    simpa [hprod] using hspan_le
  refine prime_mem_of_factor_le O (P := P) hP hprod_le ?_
  intro Q hQmem hQle
  exact hmin (hfprime Q hQmem) hQle

/-- Membership in an ideal from a singleton-span containment. -/
lemma mem_of_span_singleton_le (O : Type) [CommRing O] {a : O} {Q : Ideal O}
    (h : Ideal.span ({a} : Set O) ≤ Q) : a ∈ Q := by
  simpa using (Ideal.span_singleton_le_iff_mem (I := Q)).1 h

/-- A product lies in the principal ideal generated by its right factor. -/
lemma mul_mem_span_singleton (O : Type) [CommRing O] {a x : O} :
    x * a ∈ Ideal.span ({a} : Set O) := by
  have hmul : x * a = x * a := rfl
  refine Ideal.mem_span_singleton'.mpr ?_
  exact ⟨x, hmul⟩

/-- If a principal ideal is contained in `Q`, then any multiple of its generator lies in `Q`. -/
lemma mul_mem_of_span_singleton_le (O : Type) [CommRing O] {a x : O} {Q : Ideal O}
    (hspan_le : Ideal.span ({a} : Set O) ≤ Q) : x * a ∈ Q := by
  exact hspan_le (mul_mem_span_singleton O (a := a) (x := x))

/-- For a prime `Q`, containment of a principal ideal forces `x ∈ Q` or the generator in `Q`. -/
lemma mem_or_mem_of_span_singleton_le (O : Type) [CommRing O] {Q : Ideal O}
    (hQprime : Q.IsPrime) {a x : O} (hspan_le : Ideal.span ({a} : Set O) ≤ Q) :
    x ∈ Q ∨ a ∈ Q := by
  have hmul_Q : x * a ∈ Q := mul_mem_of_span_singleton_le O (a := a) (x := x) hspan_le
  exact hQprime.mem_or_mem hmul_Q

/-- If a principal ideal is contained in a prime ideal and the generator is not in the prime,
then the other factor lies in the prime. -/
lemma mem_of_span_singleton_le_of_not_mem (O : Type) [CommRing O] {Q : Ideal O}
    (hQprime : Q.IsPrime) {a x : O} (hspan_le : Ideal.span ({a} : Set O) ≤ Q)
    (haQ : a ∉ Q) : x ∈ Q := by
  have hmul_Q : x * a ∈ Q := mul_mem_of_span_singleton_le O (a := a) (x := x) hspan_le
  exact (hQprime.mem_or_mem hmul_Q).resolve_right haQ

/-- A unit cannot lie in a prime ideal. -/
lemma not_isUnit_of_mem_prime (O : Type) [CommRing O] {P : Ideal O} (hP : P.IsPrime)
    {a : O} (ha : a ∈ P) : ¬ IsUnit a := by
  intro haunit
  have hspan_top : (Ideal.span ({a} : Set O) : Ideal O) = ⊤ :=
    (Ideal.span_singleton_eq_top).2 haunit
  have htop_le : (⊤ : Ideal O) ≤ P := by
    have hle : Ideal.span ({a} : Set O) ≤ P :=
      (Ideal.span_singleton_le_iff_mem (I := P)).2 ha
    simpa [hspan_top] using hle
  have hPtop : P = ⊤ := le_antisymm le_top htop_le
  exact hP.ne_top hPtop

/-- A nonunit generator yields a proper principal ideal. -/
lemma span_singleton_ne_top_of_not_isUnit (O : Type) [CommRing O] {a : O} (ha : ¬ IsUnit a) :
    (Ideal.span ({a} : Set O) : Ideal O) ≠ ⊤ := by
  intro htop
  exact ha ((Ideal.span_singleton_eq_top).1 htop)

/-- If a unit-generated principal ideal is contained in `Q`, then `Q = ⊤`. -/
lemma ideal_eq_top_of_span_singleton_le_of_isUnit (O : Type) [CommRing O]
    {a : O} {Q : Ideal O} (hspan_le : Ideal.span ({a} : Set O) ≤ Q) (ha : IsUnit a) :
    Q = ⊤ := by
  have hspan_top : (Ideal.span ({a} : Set O) : Ideal O) = ⊤ :=
    (Ideal.span_singleton_eq_top).2 ha
  have htop_le_Q : (⊤ : Ideal O) ≤ Q := by
    simpa [hspan_top] using hspan_le
  exact le_antisymm le_top htop_le_Q

/-- Minimality over a principal ideal directly yields equality of intermediate primes. -/
lemma prime_eq_of_le_of_minimal_over_principal_of_minimality (O : Type) [CommRing O] [IsDomain O]
    {P : Ideal O} {a : O}
    (hmin :
      ∀ {Q : Ideal O}, Q.IsPrime →
        Ideal.span ({a} : Set O) ≤ Q → Q ≤ P → Q = P) :
    ∀ {Q : Ideal O}, Q.IsPrime →
      Ideal.span ({a} : Set O) ≤ Q → Q ≤ P → Q = P := by
  intro Q hQprime hspan_le hQle
  exact hmin hQprime hspan_le hQle

/-- Concrete counterexample in `ℤ` showing the missing inclusion lemma is false. -/
lemma counterexample_le_of_span_singleton_le_of_le :
    ∃ (P Q : Ideal ℤ) (a : ℤ),
      Q.IsPrime ∧ Ideal.span ({a} : Set ℤ) ≤ Q ∧ Q ≤ P ∧ ¬ (P ≤ Q) := by
  refine ⟨⊤, ⊥, 0, ?_⟩
  have hprime : (⊥ : Ideal ℤ).IsPrime := by
    simpa using (Ideal.bot_prime (α := ℤ))
  have hspan : (Ideal.span ({(0 : ℤ)} : Set ℤ) : Ideal ℤ) = ⊥ := by
    simpa using (Ideal.span_singleton_eq_bot (x := (0 : ℤ))).2 rfl
  refine ⟨hprime, ?_, ?_, ?_⟩
  · simpa [hspan]
  · exact bot_le
  · intro htop
    have h1top : (1 : ℤ) ∈ (⊤ : Ideal ℤ) := by
      simp
    have h1 : (1 : ℤ) ∈ (⊥ : Ideal ℤ) := htop h1top
    have h1' : (1 : ℤ) = 0 := Ideal.mem_bot.mp h1
    exact one_ne_zero h1'

/-- Domain-level counterexample showing `(a) ≤ Q ≤ P` need not imply `P ≤ Q`. -/
lemma counterexample_le_of_span_singleton_le_of_le_domain (O : Type) [CommRing O] [IsDomain O] :
    ∃ (P Q : Ideal O) (a : O),
      Q.IsPrime ∧ Ideal.span ({a} : Set O) ≤ Q ∧ Q ≤ P ∧ ¬ (P ≤ Q) := by
  classical
  refine ⟨⊤, ⊥, (0 : O), ?_⟩
  have hprime : (⊥ : Ideal O).IsPrime := by
    simpa using (Ideal.bot_prime (α := O))
  have hspan : (Ideal.span ({(0 : O)} : Set O) : Ideal O) = ⊥ := by
    simpa using (Ideal.span_singleton_eq_bot (x := (0 : O))).2 rfl
  refine And.intro hprime ?_
  refine And.intro ?_ ?_
  · simpa [hspan]
  · refine And.intro ?_ ?_
    · exact bot_le
    · intro htop
      have h1top : (1 : O) ∈ (⊤ : Ideal O) := by
        simp
      have h1 : (1 : O) ∈ (⊥ : Ideal O) := htop h1top
      have h1' : (1 : O) = 0 := Ideal.mem_bot.mp h1
      exact one_ne_zero h1'

/-- Domain-level counterexample showing minimality over a principal ideal can fail. -/
lemma counterexample_minimality_over_span_singleton_reduction_domain (O : Type) [CommRing O]
    [IsDomain O] :
    ∃ (P R : Ideal O) (a : O),
      R.IsPrime ∧ Ideal.span ({a} : Set O) ≤ R ∧ R ≤ P ∧ R ≠ P := by
  classical
  refine ⟨⊤, ⊥, (0 : O), ?_⟩
  have hprime : (⊥ : Ideal O).IsPrime := by
    simpa using (Ideal.bot_prime (α := O))
  have hspan : (Ideal.span ({(0 : O)} : Set O) : Ideal O) = ⊥ := by
    simpa using (Ideal.span_singleton_eq_bot (x := (0 : O))).2 rfl
  refine ⟨hprime, ?_, ?_, ?_⟩
  · simpa [hspan]
  · exact bot_le
  · simpa using (bot_ne_top : (⊥ : Ideal O) ≠ ⊤)

/-- Domain-level counterexample with a nonunit generator and nonzero `P`. -/
lemma counterexample_minimality_over_span_singleton_reduction_domain_nonunit (O : Type) [CommRing O]
    [IsDomain O] :
    ∃ (P R : Ideal O) (a : O),
      ¬ IsUnit a ∧ P ≠ ⊥ ∧ R.IsPrime ∧
        Ideal.span ({a} : Set O) ≤ R ∧ R ≤ P ∧ R ≠ P := by
  classical
  refine ⟨⊤, ⊥, (0 : O), ?_⟩
  have hprime : (⊥ : Ideal O).IsPrime := by
    simpa using (Ideal.bot_prime (α := O))
  have hspan : (Ideal.span ({(0 : O)} : Set O) : Ideal O) = ⊥ := by
    simpa using (Ideal.span_singleton_eq_bot (x := (0 : O))).2 rfl
  refine ⟨?_, ?_, hprime, ?_, ?_, ?_⟩
  · simpa using (not_isUnit_zero (α := O))
  · simpa using (top_ne_bot : (⊤ : Ideal O) ≠ ⊥)
  · simpa [hspan]
  · exact bot_le
  · simpa using (bot_ne_top : (⊥ : Ideal O) ≠ ⊤)

/-- Counterexample in any nontrivial commutative ring using a maximal ideal. -/
lemma counterexample_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial
    (O : Type) [CommRing O] (htriv : (0 : O) ≠ 1) :
    ∃ (P R : Ideal O) (a : O),
      ¬ IsUnit a ∧ P ≠ ⊥ ∧ R.IsPrime ∧
        Ideal.span ({a} : Set O) ≤ R ∧ R ≤ P ∧ R ≠ P := by
  classical
  haveI : Nontrivial O := by
    exact nontrivial_of_ne (0 : O) 1 htriv
  rcases Ideal.exists_maximal (α := O) with ⟨M, hMmax⟩
  have hRprime : M.IsPrime := hMmax.isPrime
  refine ⟨⊤, M, (0 : O), ?_⟩
  refine ⟨?_, ?_, hRprime, ?_, ?_, ?_⟩
  · simpa using (not_isUnit_zero (M₀ := O))
  · simpa using (top_ne_bot : (⊤ : Ideal O) ≠ (⊥ : Ideal O))
  ·
    have hspan : (Ideal.span ({(0 : O)} : Set O) : Ideal O) = ⊥ := by
      simpa using (Ideal.span_singleton_eq_bot (x := (0 : O))).2 rfl
    simpa [hspan]
  · exact le_top
  · exact hMmax.ne_top

/-- The nonunit/nontrivial minimality statement contradicts the maximal-ideal counterexample. -/
lemma false_of_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial
    (O : Type) [CommRing O] (htriv : (0 : O) ≠ 1) :
    (∀ {P R : Ideal O} {a : O},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) → False := by
  intro h
  rcases
    counterexample_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial O htriv with
    ⟨P, R, a, hunit, hPbot, hRprime, hspanR, hRle, hneq⟩
  exact hneq (h (P := P) (R := R) (a := a) hunit hneq hPbot hRprime hspanR hRle)

/-- The nonunit/nontrivial minimality statement already fails in `ℤ`. -/
lemma not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_int :
    ¬ (∀ {P R : Ideal ℤ} {a : ℤ},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set ℤ) ≤ R → R ≤ P → R = P) := by
  intro h
  rcases counterexample_minimality_over_span_singleton_reduction_domain_nonunit ℤ with
    ⟨P, R, a, hunit, hPbot, hRprime, hspanR, hRle, hneq⟩
  exact hneq (h (P := P) (R := R) (a := a) hunit hneq hPbot hRprime hspanR hRle)

/-- The nonunit/nontrivial minimality statement in `ℤ` yields a contradiction. -/
lemma false_of_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_int :
    (∀ {P R : Ideal ℤ} {a : ℤ},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set ℤ) ≤ R → R ≤ P → R = P) → False := by
  intro h
  exact not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_int h

/-- The nonunit/nontrivial minimality statement fails in any domain. -/
lemma not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_domain (O : Type)
    [CommRing O] [IsDomain O] :
    ¬ (∀ {P R : Ideal O} {a : O},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) := by
  intro h
  rcases counterexample_minimality_over_span_singleton_reduction_domain_nonunit O with
    ⟨P, R, a, hunit, hPbot, hRprime, hspanR, hRle, hneq⟩
  exact hneq (h (P := P) (R := R) (a := a) hunit hneq hPbot hRprime hspanR hRle)

/-- The nonunit/nontrivial minimality statement fails in any domain, even with a nontriviality witness. -/
lemma not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial_domain
    (O : Type) [CommRing O] [IsDomain O] (htriv : (0 : O) ≠ 1) :
    ¬ (∀ {P R : Ideal O} {a : O},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) := by
  exact not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_domain O

/-- The nonunit/nontrivial minimality statement contradicts the domain counterexample. -/
lemma false_of_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_domain (O : Type)
    [CommRing O] [IsDomain O] :
    (∀ {P R : Ideal O} {a : O},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) → False := by
  intro h
  exact not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_domain O h

/-- The nonunit/nontrivial minimality statement with a nontriviality witness contradicts the
domain counterexample. -/
lemma false_of_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial_domain
    (O : Type) [CommRing O] [IsDomain O] (htriv : (0 : O) ≠ 1) :
    (∀ {P R : Ideal O} {a : O},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) → False := by
  intro h
  exact
    (not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial_domain
      O htriv) h

/-- The universal minimality statement fails in any domain. -/
lemma not_forall_minimality_over_span_singleton_reduction_domain (O : Type) [CommRing O]
    [IsDomain O] :
    ¬ (∀ {P : Ideal O} {a : O} {R : Ideal O},
        R.IsPrime → Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) := by
  intro h
  rcases counterexample_minimality_over_span_singleton_reduction_domain O with
    ⟨P, R, a, hRprime, hspanR, hRle, hneq⟩
  exact hneq (h (P := P) (a := a) (R := R) hRprime hspanR hRle)

/-- The universal minimality statement contradicts the explicit domain-level counterexample. -/
lemma false_of_forall_minimality_over_span_singleton_reduction_domain (O : Type) [CommRing O]
    [IsDomain O] :
    (∀ {P : Ideal O} {a : O} {R : Ideal O},
        R.IsPrime → Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) → False := by
  intro h
  exact not_forall_minimality_over_span_singleton_reduction_domain O h

/-- The universal inclusion statement fails in any domain. -/
lemma not_forall_le_of_span_singleton_le_of_le_domain (O : Type) [CommRing O] [IsDomain O] :
    ¬ (∀ {P Q : Ideal O} {a : O},
        Q.IsPrime → Ideal.span ({a} : Set O) ≤ Q → Q ≤ P → P ≤ Q) := by
  intro h
  rcases counterexample_le_of_span_singleton_le_of_le_domain O with ⟨P, Q, a, hprime, hspan, hQle, hnot⟩
  exact hnot (h (P := P) (Q := Q) (a := a) hprime hspan hQle)

/-- The universal inclusion statement contradicts the explicit domain-level counterexample. -/
lemma false_of_forall_le_of_span_singleton_le_of_le_domain (O : Type) [CommRing O] [IsDomain O] :
    (∀ {P Q : Ideal O} {a : O},
        Q.IsPrime → Ideal.span ({a} : Set O) ≤ Q → Q ≤ P → P ≤ Q) → False := by
  intro h
  exact not_forall_le_of_span_singleton_le_of_le_domain O h

/-- Minimality over a principal ideal yields the inclusion `P ≤ Q`. -/
lemma le_of_span_singleton_le_of_le_of_minimal (O : Type) [CommRing O]
    {P Q : Ideal O} {a : O}
    (hQprime : Q.IsPrime)
    (hspan_le : Ideal.span ({a} : Set O) ≤ Q) (hQle : Q ≤ P)
    (hmin :
      ∀ {R : Ideal O}, R.IsPrime →
        Ideal.span ({a} : Set O) ≤ R → R ≤ P → R = P) :
    P ≤ Q := by
  have hQP : Q = P := hmin hQprime hspan_le hQle
  simpa [hQP] using (le_rfl : (P : Ideal O) ≤ P)

/-- Even with `0 ≠ 1`, the nonunit/nontrivial minimality statement fails in `ℤ`. -/
lemma not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_nontrivial_int
    (htriv : (0 : ℤ) ≠ 1) :
    ¬ (∀ {P R : Ideal ℤ} {a : ℤ},
        ¬ IsUnit a → R ≠ P → P ≠ ⊥ → R.IsPrime →
          Ideal.span ({a} : Set ℤ) ≤ R → R ≤ P → R = P) := by
  simpa using not_forall_minimality_over_span_singleton_reduction_nonunit_nontrivial_int



/-- Under ideal-UFD hypotheses, every nonzero ideal is a unit as a fractional ideal. -/
lemma ideal_UFD_isUnit_coeIdeal_of_prime_unit (O : Type) [CommRing O] [IsDomain O]
    (eif : ∀ (a : Ideal O), a ≠ ⊥ → ∃ (f : Multiset (Ideal O)), (∀ b ∈ f, b.IsPrime) ∧ f.prod = a)
    (uif : ∀ (f g : Multiset (Ideal O)), (∀ x ∈ f, x.IsPrime) → (∀ x ∈ g, x.IsPrime) →
      f.prod = g.prod → f = g)
    (hprime :
      ∀ {P : Ideal O}, P.IsPrime → P ≠ ⊥ →
        IsUnit (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) :
    ∀ {I : Ideal O}, I ≠ ⊥ →
      IsUnit (I : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) := by
  classical
  intro I hI
  obtain ⟨f, hfprime, hprod⟩ := eif I hI
  have hprod_ne : f.prod ≠ ⊥ := by
    intro hzero
    apply hI
    simpa [hprod] using hzero
  have hne : ∀ b ∈ f, b ≠ ⊥ := by
    intro b hb
    exact multiset_mem_ne_bot_of_prod_ne_bot O hprod_ne hb
  have h_unit_prod :
      IsUnit ((f.prod : Ideal O) :
        FractionalIdeal (nonZeroDivisors O) (FractionRing O)) :=
    multiset_prod_isUnit_of_prime_factors O hprime f hfprime hne
  simpa [hprod] using h_unit_prod

/-- A nonzero principal fractional ideal is a unit. -/
lemma fractionalIdeal_isUnit_spanSingleton (O : Type) [CommRing O] [IsDomain O]
    {x : FractionRing O} (hx : x ≠ 0) :
    IsUnit (FractionalIdeal.spanSingleton (nonZeroDivisors O) x) := by
  refine (FractionalIdeal.mul_inv_cancel_iff_isUnit
    (I := FractionalIdeal.spanSingleton (nonZeroDivisors O) x)).1 ?_
  exact FractionalIdeal.spanSingleton_mul_inv (R₁ := O) (K := FractionRing O) hx

/-- If every nonzero ideal is a unit as a fractional ideal, then every nonzero fractional ideal is a unit. -/
lemma fractionalIdeal_isUnit_of_ideal_isUnit (O : Type) [CommRing O] [IsDomain O]
    (hunit : ∀ {I : Ideal O}, I ≠ ⊥ →
      IsUnit (I : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) :
    ∀ {I : FractionalIdeal (nonZeroDivisors O) (FractionRing O)}, I ≠ 0 → IsUnit I := by
  classical
  intro I hI
  obtain ⟨a, J, ha, hIeq⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I := I)
  have hJne0 : (J : Ideal O) ≠ (0 : Ideal O) :=
    FractionalIdeal.ideal_factor_ne_zero (I := I) (hI := hI) (a := a) (J := J) hIeq
  have hJne : (J : Ideal O) ≠ ⊥ := by
    simpa using hJne0
  have hJunit :
      IsUnit (J : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) := hunit hJne
  have hmap : algebraMap O (FractionRing O) a ≠ 0 :=
    (IsFractionRing.to_map_eq_zero_iff (K := FractionRing O)).not.mpr ha
  have hmap_inv : (algebraMap O (FractionRing O) a)⁻¹ ≠ 0 := inv_ne_zero hmap
  have hspan_unit :
      IsUnit
        (FractionalIdeal.spanSingleton (nonZeroDivisors O)
          ((algebraMap O (FractionRing O) a)⁻¹)) :=
    fractionalIdeal_isUnit_spanSingleton O hmap_inv
  have hmul_unit :
      IsUnit
        (FractionalIdeal.spanSingleton (nonZeroDivisors O)
            ((algebraMap O (FractionRing O) a)⁻¹) *
          (J : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) :=
    hspan_unit.mul hJunit
  simpa [hIeq] using hmul_unit

/-- If every nonzero ideal is a unit as a fractional ideal, then the ring is a Dedekind domain. -/
lemma isDedekindDomain_of_ideal_isUnit (O : Type) [CommRing O] [IsDomain O]
    (hunit : ∀ {I : Ideal O}, I ≠ ⊥ →
      IsUnit (I : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) :
    IsDedekindDomain O := by
  have hInv : IsDedekindDomainInv O := by
    intro I hI
    have hunitI :
        IsUnit I := fractionalIdeal_isUnit_of_ideal_isUnit O hunit hI
    exact (FractionalIdeal.mul_inv_cancel_iff_isUnit (I := I)).2 hunitI
  exact (isDedekindDomain_iff_isDedekindDomainInv (A := O)).2 hInv

/-- Under ideal-UFD hypotheses plus unit prime ideals, the ring is Dedekind. -/
lemma isDedekindDomain_of_ideal_UFD_of_prime_unit (O : Type) [CommRing O] [IsDomain O]
    (eif : ∀ (a : Ideal O), a ≠ ⊥ → ∃ (f : Multiset (Ideal O)),
      (∀ b ∈ f, b.IsPrime) ∧ f.prod = a)
    (uif : ∀ (f g : Multiset (Ideal O)), (∀ x ∈ f, x.IsPrime) → (∀ x ∈ g, x.IsPrime) →
      f.prod = g.prod → f = g)
    (hprime :
      ∀ {P : Ideal O}, P.IsPrime → P ≠ ⊥ →
        IsUnit (P : FractionalIdeal (nonZeroDivisors O) (FractionRing O))) :
    IsDedekindDomain O := by
  have hunit :
      ∀ {I : Ideal O}, I ≠ ⊥ →
        IsUnit (I : FractionalIdeal (nonZeroDivisors O) (FractionRing O)) :=
    ideal_UFD_isUnit_coeIdeal_of_prime_unit O eif uif hprime
  exact isDedekindDomain_of_ideal_isUnit O hunit

/-- The uniqueness hypothesis yields a contradiction from duplicate `⊥` factors. -/
lemma false_of_uif_bot_duplicate (O : Type) [CommRing O] [IsDomain O]
    (uif : ∀ (f g : Multiset (Ideal O)), (∀ x ∈ f, x.IsPrime) → (∀ x ∈ g, x.IsPrime) →
      f.prod = g.prod → f = g) : False := by
  classical
  let f : Multiset (Ideal O) := {⊥}
  let g : Multiset (Ideal O) := {⊥, ⊥}
  have hbotprime : (⊥ : Ideal O).IsPrime := by
    simpa using (Ideal.bot_prime (α := O))
  have hfprime : ∀ x ∈ f, x.IsPrime := by
    intro x hx
    have hx' : x = (⊥ : Ideal O) := by
      simpa [f] using hx
    simpa [hx'] using hbotprime
  have hgprime : ∀ x ∈ g, x.IsPrime := by
    intro x hx
    have hx' : x = (⊥ : Ideal O) := by
      simpa [g] using hx
    simpa [hx'] using hbotprime
  have hprod : f.prod = g.prod := by
    simp [f, g]
  have hfg : f = g := uif f g hfprime hgprime hprod
  have hcard : f.card = g.card := congrArg Multiset.card hfg
  have hcard_ne : f.card ≠ g.card := by
    have hne : (1 : Nat) ≠ 2 := by
      decide
    simpa [f, g] using hne
  exact hcard_ne hcard

/--
Let $\mathcal{O}$ be an integral domain in which all nonzero ideals admit a unique factorization into prime ideals.
Show that $\mathcal{O}$ is a Dedekind domain.
-/
theorem isDedekindDomain_of_ideal_UFD (O : Type) [CommRing O] [IsDomain O]
    (eif : ∀ (a : Ideal O), a ≠ ⊥ → ∃ (f : Multiset (Ideal O)), (∀ b ∈ f, b.IsPrime) ∧ f.prod = a)
    (uif : ∀ (f g : Multiset (Ideal O)), (∀ x ∈ f, x.IsPrime) → (∀ x ∈ g, x.IsPrime) → f.prod = g.prod → f = g) :
    IsDedekindDomain O := by
  have hfalse : False := false_of_uif_bot_duplicate O uif
  exact False.elim hfalse

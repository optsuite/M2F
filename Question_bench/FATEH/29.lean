import Mathlib

open IntermediateField Polynomial

/- Show that if $F$ has characteristic $p$, then all degree $p$ Galois extension of $F$ is to
adjoin a zero of $x^p-x-a$ for some $a \in F$.-/
-- The next lemmas isolate the group-theoretic reductions used by Artin-Schreier.
lemma gal_card_eq_finrank
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [Field E]
    [Algebra F E] [IsGalois F E] (h_deg : Module.finrank F E = p) :
    Nat.card (Gal(E/F)) = p := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpos : 0 < Module.finrank F E := by simpa [h_deg] using hp
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos hpos
  simpa [h_deg] using (IsGalois.card_aut_eq_finrank (F := F) (E := E))

-- A degree `p` Galois extension has cyclic Galois group.
lemma gal_isCyclic_of_prime_card
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [Field E]
    [Algebra F E] [IsGalois F E] (h_deg : Module.finrank F E = p) :
    IsCyclic (Gal(E/F)) := by
  classical
  refine isCyclic_of_prime_card (α := Gal(E/F)) (p := p) ?_
  exact gal_card_eq_finrank (F := F) (E := E) (p := p) h_deg

-- If a generator fixes an element, then all Galois automorphisms fix it.
lemma fixed_by_generator
    {F E : Type} [Field F] [Field E] [Algebra F E]
    {σ : Gal(E/F)} (hσ : ∀ g : Gal(E/F), g ∈ Subgroup.zpowers σ) {z : E}
    (hz : σ z = z) : ∀ g : Gal(E/F), g z = z := by
  intro g
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hσ g)
  have hzinv : σ⁻¹ z = z := by
    simpa using (congrArg (fun t => σ⁻¹ t) hz).symm
  refine zpow_induction_right (g := σ) (P := fun a => a z = z) ?_ ?_ ?_ n
  · simp
  · intro a ha
    simp [ha, hz]
  · intro a ha
    simp [ha, hzinv]

-- The kernel of `σ - 1` is the one-dimensional subspace spanned by `1`.
lemma ker_sub_eq_span_one
    {F E : Type} [Field F] [Field E] [Algebra F E] [IsGalois F E] [FiniteDimensional F E]
    {σ : Gal(E/F)} (hσ : ∀ g : Gal(E/F), g ∈ Subgroup.zpowers σ) :
    LinearMap.ker (σ.toLinearEquiv.toLinearMap - (LinearMap.id : E →ₗ[F] E)) =
      Submodule.span F ({(1 : E)} : Set E) := by
  classical
  refine le_antisymm ?_ ?_
  · intro x hx
    have hx' : σ x = x := by
      have hx' : (σ.toLinearEquiv.toLinearMap - (LinearMap.id : E →ₗ[F] E)) x = 0 := by
        simpa using (LinearMap.mem_ker.mp hx)
      exact sub_eq_zero.mp (by simpa using hx')
    have hx_fixed : x ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) := by
      refine (IntermediateField.mem_fixedField_iff (H := (⊤ : Subgroup Gal(E/F))) x).2 ?_
      intro g hg
      exact fixed_by_generator (F := F) (E := E) hσ hx' g
    have hx_bot : x ∈ (⊥ : IntermediateField F E) := by
      simpa [InfiniteGalois.fixedField_bot (k := F) (K := E)] using hx_fixed
    rcases (IntermediateField.mem_bot.mp hx_bot) with ⟨a, rfl⟩
    refine Submodule.mem_span_singleton.mpr ?_
    refine ⟨a, ?_⟩
    simp [Algebra.smul_def]
  · intro x hx
    rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
    refine (LinearMap.mem_ker).2 ?_
    simp [Algebra.smul_def]

-- For a generator `σ`, the range of `σ - 1` is the trace-zero subspace.
lemma artin_schreier_range_eq_ker_trace
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [Field E]
    [Algebra F E] [IsGalois F E] (h_deg : Module.finrank F E = p)
    {σ : Gal(E/F)} (hσ : ∀ g : Gal(E/F), g ∈ Subgroup.zpowers σ) :
    LinearMap.range (σ.toLinearEquiv.toLinearMap - (LinearMap.id : E →ₗ[F] E)) =
      LinearMap.ker (Algebra.trace F E) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpos : 0 < Module.finrank F E := by simpa [h_deg] using hp
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos hpos
  let T : E →ₗ[F] E := σ.toLinearEquiv.toLinearMap - (LinearMap.id : E →ₗ[F] E)
  let tr : E →ₗ[F] F := Algebra.trace F E
  have h_range : LinearMap.range T ≤ LinearMap.ker tr := by
    intro x hx
    rcases hx with ⟨y, rfl⟩
    refine (LinearMap.mem_ker).2 ?_
    have htr :
        Algebra.trace F E (σ y) = Algebra.trace F E y :=
      Algebra.trace_eq_of_algEquiv (A := F) (B := E) (C := E) σ y
    calc
      tr (T y) = tr (σ y - y) := by simp [T, tr]
      _ = tr (σ y) - tr y := by simp [tr]
      _ = 0 := by simp [tr, htr]
  have hker_T :
      LinearMap.ker T = Submodule.span F ({(1 : E)} : Set E) := by
    simpa [T] using (ker_sub_eq_span_one (F := F) (E := E) hσ)
  have hker_dim :
      Module.finrank F (LinearMap.ker T) = 1 := by
    rw [hker_T]
    simpa using (finrank_span_singleton (K := F) (v := (1 : E)) one_ne_zero)
  have hrange_dim :
      Module.finrank F (LinearMap.range T) = p - 1 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker T
    have hdim' :
        Module.finrank F (LinearMap.range T) + 1 = p := by
      simpa [hker_dim, h_deg] using hdim
    have hp1 : 1 ≤ p := Nat.succ_le_iff.mpr (Fact.out : p.Prime).pos
    have hdim'' :
        Module.finrank F (LinearMap.range T) + 1 = (p - 1) + 1 := by
      simpa [Nat.sub_add_cancel hp1] using hdim'
    exact Nat.add_right_cancel hdim''
  have htr_surj : Function.Surjective (Algebra.trace F E) :=
    Algebra.trace_surjective (K := F) (L := E)
  have htr_range :
      LinearMap.range tr = ⊤ := by
    exact (LinearMap.range_eq_top).2 htr_surj
  have htr_dim :
      Module.finrank F (LinearMap.ker tr) = p - 1 := by
    have hdim := LinearMap.finrank_range_add_finrank_ker tr
    have hrange_tr :
        Module.finrank F (LinearMap.range tr) = 1 := by
      rw [htr_range]
      simp [finrank_top]
    have hdim' :
        Module.finrank F (LinearMap.ker tr) + 1 = p := by
      have := hdim
      simpa [hrange_tr, h_deg, add_comm] using this
    have hp1 : 1 ≤ p := Nat.succ_le_iff.mpr (Fact.out : p.Prime).pos
    have hdim'' :
        Module.finrank F (LinearMap.ker tr) + 1 = (p - 1) + 1 := by
      simpa [Nat.sub_add_cancel hp1] using hdim'
    exact Nat.add_right_cancel hdim''
  apply Submodule.eq_of_le_of_finrank_eq h_range
  simp [hrange_dim, htr_dim]

-- A generator `σ` yields `y` with `σ y = y + 1`.
lemma artin_schreier_exists_y
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Field E]
    [Algebra F E] [IsGalois F E] (h_deg : Module.finrank F E = p)
    {σ : Gal(E/F)} (hσ : ∀ g : Gal(E/F), g ∈ Subgroup.zpowers σ) :
    ∃ y : E, σ y = y + 1 := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpos : 0 < Module.finrank F E := by simpa [h_deg] using hp
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos hpos
  let T : E →ₗ[F] E := σ.toLinearEquiv.toLinearMap - (LinearMap.id : E →ₗ[F] E)
  let tr : E →ₗ[F] F := Algebra.trace F E
  have h_eq :
      LinearMap.range T = LinearMap.ker tr :=
    artin_schreier_range_eq_ker_trace (F := F) (E := E) (p := p) h_deg hσ
  have htr1 :
      Algebra.trace F E (1 : E) = (p : F) := by
    have hsum :
        algebraMap F E (Algebra.trace F E (1 : E)) =
          (Fintype.card (Gal(E/F)) : E) := by
      simpa using
        (trace_eq_sum_automorphisms (K := F) (L := E) (x := (1 : E)))
    have hcard :
        Fintype.card (Gal(E/F)) = p := by
      simpa [Nat.card_eq_fintype_card] using
        (gal_card_eq_finrank (F := F) (E := E) (p := p) h_deg)
    apply (algebraMap F E).injective
    calc
      algebraMap F E (Algebra.trace F E (1 : E)) =
          (Fintype.card (Gal(E/F)) : E) := hsum
      _ = (p : E) := by simp [hcard]
      _ = algebraMap F E (p : F) := by
        exact (map_natCast (algebraMap F E) p).symm
  have hker1 : (1 : E) ∈ LinearMap.ker tr := by
    refine (LinearMap.mem_ker).2 ?_
    simp [tr, htr1]
  have h1_range : (1 : E) ∈ LinearMap.range T := by
    simpa [h_eq] using hker1
  rcases h1_range with ⟨y, hy⟩
  have hy' : σ y - y = 1 := by
    simpa [T] using hy
  refine ⟨y, ?_⟩
  simpa [add_comm] using (sub_eq_iff_eq_add.mp hy')

-- From `σ y = y + 1`, the element `y^p - y` lies in the base field.
lemma artin_schreier_exists_a
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Field E]
    [Algebra F E] [IsGalois F E] {σ : Gal(E/F)}
    (hσ : ∀ g : Gal(E/F), g ∈ Subgroup.zpowers σ) {y : E} (hy : σ y = y + 1) :
    ∃ a : F, algebraMap F E a = y ^ p - y := by
  classical
  haveI : CharP E p :=
    charP_of_injective_algebraMap (algebraMap F E).injective p
  have hfix : σ (y ^ p - y) = y ^ p - y := by
    have hpow : (y + 1) ^ p = y ^ p + 1 := by
      simp [add_pow_char]
    calc
      σ (y ^ p - y) = (σ y) ^ p - σ y := by simp [map_pow]
      _ = (y + 1) ^ p - (y + 1) := by simp [hy]
      _ = y ^ p + 1 - (y + 1) := by simp [hpow]
      _ = y ^ p - y := by ring
  have hfixed :
      y ^ p - y ∈ IntermediateField.fixedField (⊤ : Subgroup Gal(E/F)) := by
    refine (IntermediateField.mem_fixedField_iff (H := (⊤ : Subgroup Gal(E/F))) (y ^ p - y)).2 ?_
    intro g hg
    exact fixed_by_generator (F := F) (E := E) hσ hfix g
  have hbot :
      y ^ p - y ∈ (⊥ : IntermediateField F E) := by
    simpa [InfiniteGalois.fixedField_bot (k := F) (K := E)] using hfixed
  rcases (IntermediateField.mem_bot.mp hbot) with ⟨a, ha⟩
  exact ⟨a, ha⟩

-- The Artin–Schreier generator has the expected minimal polynomial.
lemma artin_schreier_minpoly_eq
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Field E]
    [Algebra F E] [IsGalois F E] (h_deg : Module.finrank F E = p)
    {σ : Gal(E/F)} (hσ : ∀ g : Gal(E/F), g ∈ Subgroup.zpowers σ)
    {y : E} (hy : σ y = y + 1) {a : F} (ha : algebraMap F E a = y ^ p - y) :
    minpoly F y = (X ^ p - X - C a : F[X]) := by
  classical
  have hσ' : σ ∈ Subgroup.zpowers σ := hσ σ
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpos : 0 < Module.finrank F E := by simpa [h_deg] using hp
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos hpos
  have hyint : IsIntegral F y := IsIntegral.of_finite F y
  have hy_not_mem : y ∉ (⊥ : IntermediateField F E) := by
    intro hy_bot
    rcases (IntermediateField.mem_bot.mp hy_bot) with ⟨b, rfl⟩
    have hfix : σ (algebraMap F E b) = algebraMap F E b := by simp
    have h1 : algebraMap F E b = algebraMap F E b + 1 := by
      calc
        algebraMap F E b = σ (algebraMap F E b) := by
          simp [hfix]
        _ = algebraMap F E b + 1 := by
          simp [hy]
    have h1' : (0 : E) = 1 := by
      have h1'' : algebraMap F E b + 0 = algebraMap F E b + 1 := by
        calc
          algebraMap F E b + 0 = algebraMap F E b := by simp
          _ = algebraMap F E b + 1 := h1
      exact add_left_cancel h1''
    exact zero_ne_one h1'
  have hsimple : IsSimpleOrder (IntermediateField F E) :=
    IntermediateField.isSimpleOrder_of_finrank_prime (F := F) (E := E) <|
      by
        simpa [h_deg] using (Fact.out : p.Prime)
  have hy_top : F⟮y⟯ = ⊤ := by
    have hy_ne_bot : (F⟮y⟯ : IntermediateField F E) ≠ ⊥ := by
      intro h
      apply hy_not_mem
      simpa [h] using (IntermediateField.mem_adjoin_simple_self F y)
    simpa using (hsimple.eq_bot_or_eq_top (F⟮y⟯)).resolve_left hy_ne_bot
  have hfinrank_adjoin : Module.finrank F F⟮y⟯ = p := by
    calc
      Module.finrank F F⟮y⟯ = Module.finrank F (⊤ : IntermediateField F E) := by
        rw [hy_top]
      _ = Module.finrank F E := by
        simp
      _ = p := by simp [h_deg]
  have hmin_deg :
      (minpoly F y).natDegree = p := by
    simpa [hfinrank_adjoin] using
      (IntermediateField.adjoin.finrank (K := F) (L := E) (x := y) hyint).symm
  have hpoly_dvd :
      minpoly F y ∣ (X ^ p - X - C a : F[X]) := by
    apply minpoly.dvd
    simp [ha]
  have hmonic_poly :
      (X ^ p - X - C a : F[X]).Monic := by
    have hp' : (1 : WithBot ℕ) < p := by
      simpa using (show (1 : ℕ) < p from (Fact.out : p.Prime).one_lt)
    have hdeg : degree (X + C a : F[X]) < p := by
      simpa [degree_X_add_C] using hp'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (monic_X_pow_sub (p := (X + C a : F[X])) (n := p) hdeg)
  have hpoly_deg :
      (X ^ p - X - C a : F[X]).natDegree = p := by
    have hdegX : (X : F[X]).natDegree = 1 := by simp
    have hdegP : (X ^ p - C a : F[X]).natDegree = p := by
      simp
    have hlt : (X : F[X]).natDegree < (X ^ p - C a : F[X]).natDegree := by
      simpa [hdegX, hdegP] using (Fact.out : p.Prime).one_lt
    have hdeg' :
        (X ^ p - C a : F[X]) - X = (X ^ p - X - C a : F[X]) := by
      ring
    simpa [hdeg', hdegP] using
      (natDegree_sub_eq_left_of_natDegree_lt (p := (X ^ p - C a : F[X])) (q := X) hlt)
  refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hyint) hmonic_poly hpoly_dvd ?_).symm
  -- `hpoly_deg` and `hmin_deg` give the degree comparison.
  simp [hmin_deg, hpoly_deg]

-- Core Artin-Schreier statement;
lemma artin_schreier_exists_equiv
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Field E]
    [Algebra F E] [IsGalois F E] [IsCyclic (Gal(E/F))]
    (h_deg : Module.finrank F E = p) :
    ∃ a : F, Nonempty (AdjoinRoot (X ^ p - X - C a : F[X]) ≃+* E) := by
  classical
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(E/F))
  obtain ⟨y, hy⟩ :=
    artin_schreier_exists_y (F := F) (E := E) (p := p) h_deg (σ := σ) hσ
  obtain ⟨a, ha⟩ :=
    artin_schreier_exists_a (F := F) (E := E) (p := p) (σ := σ) hσ hy
  have hmin :
      minpoly F y = (X ^ p - X - C a : F[X]) :=
    artin_schreier_minpoly_eq (F := F) (E := E) (p := p) h_deg (σ := σ) hσ hy ha
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hpos : 0 < Module.finrank F E := by simpa [h_deg] using hp
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos hpos
  have hyint : IsIntegral F y := IsIntegral.of_finite F y
  have hy_top : F⟮y⟯ = ⊤ := by
    have hy_not_mem : y ∉ (⊥ : IntermediateField F E) := by
      intro hy_bot
      rcases (IntermediateField.mem_bot.mp hy_bot) with ⟨b, rfl⟩
      have hfix : σ (algebraMap F E b) = algebraMap F E b := by simp
      have h1 : algebraMap F E b = algebraMap F E b + 1 := by
        calc
          algebraMap F E b = σ (algebraMap F E b) := by
            simp [hfix]
          _ = algebraMap F E b + 1 := by
            simp [hy]
      have h1' : (0 : E) = 1 := by
        have h1'' : algebraMap F E b + 0 = algebraMap F E b + 1 := by
          calc
            algebraMap F E b + 0 = algebraMap F E b := by simp
            _ = algebraMap F E b + 1 := h1
        exact add_left_cancel h1''
      exact zero_ne_one h1'
    have hsimple : IsSimpleOrder (IntermediateField F E) :=
      IntermediateField.isSimpleOrder_of_finrank_prime (F := F) (E := E) <|
        by
          simpa [h_deg] using (Fact.out : p.Prime)
    have hy_ne_bot : (F⟮y⟯ : IntermediateField F E) ≠ ⊥ := by
      intro h
      apply hy_not_mem
      simpa [h] using (IntermediateField.mem_adjoin_simple_self F y)
    simpa using (hsimple.eq_bot_or_eq_top (F⟮y⟯)).resolve_left hy_ne_bot
  have h_equiv :
      AdjoinRoot (X ^ p - X - C a : F[X]) ≃ₐ[F] E := by
    have h1 :
        AdjoinRoot (X ^ p - X - C a : F[X]) ≃ₐ[F]
          AdjoinRoot (minpoly F y) :=
      AdjoinRoot.algEquivOfEq F _ _ hmin.symm
    have h2 :
        AdjoinRoot (minpoly F y) ≃ₐ[F] F⟮y⟯ :=
      adjoinRootEquivAdjoin F hyint
    have h3 :
        F⟮y⟯ ≃ₐ[F] E := by
      exact
        (IntermediateField.equivOfEq (F := F) (E := E) hy_top).trans
          (IntermediateField.topEquiv (F := F) (E := E))
    exact h1.trans (h2.trans h3)
  exact ⟨a, ⟨h_equiv.toRingEquiv⟩⟩

theorem exists_nonempty_adjoin_root_X_pow_p_sub_X_sub_C
    {F E : Type} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p] [Field E]
    [Algebra F E] [IsGalois F E] (h_deg : Module.finrank F E = p) :
    ∃ a : F, Nonempty (AdjoinRoot (X ^ p - X - C a : F[X]) ≃+* E) := by
  classical
  haveI hcyc : IsCyclic (Gal(E/F)) :=
    gal_isCyclic_of_prime_card (F := F) (E := E) (p := p) h_deg
  exact artin_schreier_exists_equiv (F := F) (E := E) (p := p) h_deg

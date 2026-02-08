import Mathlib

open scoped Polynomial

/--
Let $F$ be a field and let $f(x) \in F[x]$ be an irreducible polynomial with splitting field $E$ over $F$.
Choose $\alpha \in E$ with $f(\alpha) =0$. Furthermore, for some fixed integer $n \geq 1$,
let $g(x)$ be an irreducible polynomial in $F[x]$ with $g(\alpha^n)=0$. If $\deg(f) / \deg(g) = n$
and if the characteristic of $F$ does not divide $n$, prove that $E$ contains a primitive $n$th root of unity.-/
theorem primitiveRoots_not_empty (E F : Type) [Field E] [Field F] [Algebra F E]
    (f : Polynomial F) (h_f_irr : Irreducible f) (h_splitting_field : f.IsSplittingField F E)
    (a : E) (ha : f.aeval a = 0) (n : ℕ) (hn : n ≥ 1)
    (g : Polynomial F) (h_g_irr : Irreducible g) (h_ga : g.aeval (a ^ n) = 0)
    (h_deg : f.degree = g.degree * n) (h_char : (n : F) ≠ 0) : primitiveRoots n E ≠ ∅ := by
  classical
  have hn0 : n ≠ 0 := by
    intro hn0
    subst hn0
    exact Nat.not_succ_le_zero 0 hn
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : NeZero n := ⟨hn0⟩
  by_cases hn1 : n = 1
  · subst hn1
    simp
  have ha0 : a ≠ 0 := by
    intro ha0
    have hf0' : f.aeval (0 : E) = 0 := by simpa [ha0] using ha
    have hfcoeff0 : f.coeff 0 = 0 := by
      have : algebraMap F E (f.coeff 0) = 0 := by simpa [Polynomial.aeval_def] using hf0'
      have : algebraMap F E (f.coeff 0) = algebraMap F E 0 := by simpa using this
      exact (FaithfulSMul.algebraMap_injective F E) this
    have hXdivf : (Polynomial.X : Polynomial F) ∣ f := (Polynomial.X_dvd_iff).2 hfcoeff0
    have hassoc_f : Associated (Polynomial.X : Polynomial F) f :=
      (Polynomial.irreducible_X).associated_of_dvd h_f_irr hXdivf
    have hfdeg1 : f.degree = 1 := by
      have hdeg := Polynomial.degree_eq_degree_of_associated (R := F) hassoc_f
      simpa using hdeg.symm.trans (by simp)
    have hg0' : g.aeval (0 : E) = 0 := by simpa [ha0, hn0] using h_ga
    have hgcoeff0 : g.coeff 0 = 0 := by
      have : algebraMap F E (g.coeff 0) = 0 := by simpa [Polynomial.aeval_def] using hg0'
      have : algebraMap F E (g.coeff 0) = algebraMap F E 0 := by simpa using this
      exact (FaithfulSMul.algebraMap_injective F E) this
    have hXdivg : (Polynomial.X : Polynomial F) ∣ g := (Polynomial.X_dvd_iff).2 hgcoeff0
    have hassoc_g : Associated (Polynomial.X : Polynomial F) g :=
      (Polynomial.irreducible_X).associated_of_dvd h_g_irr hXdivg
    have hgdeg1 : g.degree = 1 := by
      have hdeg := Polynomial.degree_eq_degree_of_associated (R := F) hassoc_g
      simpa using hdeg.symm.trans (by simp)
    have : (1 : WithBot ℕ) = (n : WithBot ℕ) := by
      simpa [hfdeg1, hgdeg1] using h_deg
    have hn' : n = 1 := by
      exact (WithBot.coe_eq_coe).1 this.symm
    exact hn1 hn'

  have hf_lc_ne : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h_f_irr.ne_zero
  have hg_lc_ne : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr h_g_irr.ne_zero

  have ha_int : IsIntegral F a := by
    refine ⟨f * Polynomial.C f.leadingCoeff⁻¹, ?_, ?_⟩
    · simp [Polynomial.Monic, hf_lc_ne]
    ·
      have ha' : (Polynomial.aeval a) f = 0 := by simpa using ha
      calc
        (Polynomial.aeval a) (f * Polynomial.C f.leadingCoeff⁻¹) =
            (Polynomial.aeval a) f * (Polynomial.aeval a) (Polynomial.C f.leadingCoeff⁻¹) := by
          simp
        _ = 0 := by simp [ha']

  have han_int : IsIntegral F (a ^ n) := by
    refine ⟨g * Polynomial.C g.leadingCoeff⁻¹, ?_, ?_⟩
    · simp [Polynomial.Monic, hg_lc_ne]
    ·
      have h_ga' : (Polynomial.aeval (a ^ n)) g = 0 := by simpa using h_ga
      calc
        (Polynomial.aeval (a ^ n)) (g * Polynomial.C g.leadingCoeff⁻¹) =
            (Polynomial.aeval (a ^ n)) g *
              (Polynomial.aeval (a ^ n)) (Polynomial.C g.leadingCoeff⁻¹) := by
          simp
        _ = 0 := by simp [h_ga']

  have h_deg_nat : f.natDegree = g.natDegree * n := by
    have hf0 : f ≠ 0 := h_f_irr.ne_zero
    have hg0 : g ≠ 0 := h_g_irr.ne_zero
    have h' : (f.natDegree : WithBot ℕ) = (g.natDegree : WithBot ℕ) * n := by
      simpa [Polynomial.degree_eq_natDegree hf0, Polynomial.degree_eq_natDegree hg0] using h_deg
    have h'' : (f.natDegree : WithBot ℕ) = (g.natDegree * n : ℕ) := by simpa using h'
    exact (WithBot.coe_eq_coe).1 h''

  have hfinrank_FKa :
      Module.finrank F (IntermediateField.adjoin F (Set.singleton a)) = f.natDegree := by
    have hminpoly : f * Polynomial.C f.leadingCoeff⁻¹ = minpoly F a :=
      minpoly.eq_of_irreducible h_f_irr ha
    have hminpoly' : minpoly F a = f * Polynomial.C f.leadingCoeff⁻¹ := by
      simpa using hminpoly.symm
    have hf_lc_inv_ne : (f.leadingCoeff⁻¹ : F) ≠ 0 := inv_ne_zero hf_lc_ne
    calc
      Module.finrank F (IntermediateField.adjoin F (Set.singleton a)) = (minpoly F a).natDegree := by
        simpa using (IntermediateField.adjoin.finrank (K := F) (L := E) ha_int)
      _ = f.natDegree := by
        simpa [hminpoly'] using
          (Polynomial.natDegree_mul_C (p := f) (a := f.leadingCoeff⁻¹) hf_lc_inv_ne)

  have hfinrank_FLan :
      Module.finrank F (IntermediateField.adjoin F (Set.singleton (a ^ n))) = g.natDegree := by
    have hminpoly : g * Polynomial.C g.leadingCoeff⁻¹ = minpoly F (a ^ n) :=
      minpoly.eq_of_irreducible h_g_irr h_ga
    have hminpoly' : minpoly F (a ^ n) = g * Polynomial.C g.leadingCoeff⁻¹ := by
      simpa using hminpoly.symm
    have hg_lc_inv_ne : (g.leadingCoeff⁻¹ : F) ≠ 0 := inv_ne_zero hg_lc_ne
    calc
      Module.finrank F (IntermediateField.adjoin F (Set.singleton (a ^ n))) =
          (minpoly F (a ^ n)).natDegree := by
        simpa using (IntermediateField.adjoin.finrank (K := F) (L := E) han_int)
      _ = g.natDegree := by
        simpa [hminpoly'] using
          (Polynomial.natDegree_mul_C (p := g) (a := g.leadingCoeff⁻¹) hg_lc_inv_ne)

  let L : IntermediateField F E := IntermediateField.adjoin F (Set.singleton (a ^ n))
  let K : IntermediateField F E := IntermediateField.adjoin F (Set.singleton a)
  let M : IntermediateField L E := IntermediateField.adjoin L ({a} : Set E)

  have ha_intL : IsIntegral L a := ha_int.tower_top

  -- Finite-dimensionality instances needed for `Module.finrank_mul_finrank`.
  haveI : FiniteDimensional F L := by
    simpa [L] using (IntermediateField.adjoin.finiteDimensional (K := F) (L := E) han_int)
  haveI : FiniteDimensional F K := by
    simpa [K] using (IntermediateField.adjoin.finiteDimensional (K := F) (L := E) ha_int)
  haveI : FiniteDimensional L M := by
    simpa [M] using (IntermediateField.adjoin.finiteDimensional (K := L) (L := E) ha_intL)

  have ha_memK : a ∈ (K : Set E) := by
    simpa [K] using (IntermediateField.mem_adjoin_simple_self F a)

  have hL_le_K : L ≤ K := by
    -- `a ^ n ∈ K`, so `F⟮a ^ n⟯ ≤ F⟮a⟯`.
    have han_memK : a ^ n ∈ (K : Set E) := by
      simpa using (K.pow_mem ha_memK (n : ℤ))
    -- unfold `L` and use the universal property of `IntermediateField.adjoin`.
    change IntermediateField.adjoin F (Set.singleton (a ^ n)) ≤ K
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rcases Set.mem_singleton_iff.mp hx with rfl
    exact han_memK

  have hM_restrict : (M.restrictScalars F) = K := by
    -- Restricting scalars turns `L⟮a⟯` into the `F`-adjoin of `L ∪ {a}`.
    have h1 :
        (M.restrictScalars F) =
          IntermediateField.adjoin F ((L : Set E) ∪ ({a} : Set E)) := by
      simpa [M] using (IntermediateField.restrictScalars_adjoin (F := F) (E := E) L ({a} : Set E))
    -- But `L ≤ K` and `a ∈ K`, so `F(L ∪ {a}) = F⟮a⟯`.
    have h2 : IntermediateField.adjoin F ((L : Set E) ∪ ({a} : Set E)) = K := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        refine Set.union_subset ?_ ?_
        · exact hL_le_K
        · intro x hx
          rcases Set.mem_singleton_iff.mp hx with rfl
          exact ha_memK
      · -- `a ∈ L ∪ {a}` implies `F⟮a⟯ ≤ F(L ∪ {a})`.
        have ha_mem :
            a ∈ IntermediateField.adjoin F ((L : Set E) ∪ ({a} : Set E)) :=
          (IntermediateField.subset_adjoin F ((L : Set E) ∪ ({a} : Set E))) (by simp)
        -- `K = F⟮a⟯` is `adjoin F {a}`.
        change IntermediateField.adjoin F (Set.singleton a) ≤ IntermediateField.adjoin F ((L : Set E) ∪ ({a} : Set E))
        rw [IntermediateField.adjoin_le_iff]
        intro x hx
        rcases Set.mem_singleton_iff.mp hx with rfl
        exact ha_mem
    exact h1.trans h2

  have hfinrank_FM : Module.finrank F M = f.natDegree := by
    -- `M.restrictScalars F = K = F⟮a⟯`, so `[M : F] = [K : F] = deg f`.
    calc
      Module.finrank F M = Module.finrank F (M.restrictScalars F) := by rfl
      _ = Module.finrank F K := by
        simpa using congrArg (fun (T : IntermediateField F E) => Module.finrank F T) hM_restrict
      _ = f.natDegree := by simpa [K] using hfinrank_FKa

  have hfinrank_FL : Module.finrank F L = g.natDegree := by
    simpa [L] using hfinrank_FLan

  have hfinrank_FK_mul : Module.finrank F K = Module.finrank F L * n := by
    -- Use `f.natDegree = g.natDegree * n`, and identify these natDegrees with finranks.
    calc
      Module.finrank F K = f.natDegree := by simpa [K] using hfinrank_FKa
      _ = g.natDegree * n := by simpa [h_deg_nat]
      _ = Module.finrank F L * n := by simpa [hfinrank_FL]

  have hfinrank_LM : Module.finrank L M = n := by
    have hmul := (Module.finrank_mul_finrank F L M)
    have hpos : 0 < Module.finrank F L := Module.finrank_pos
    -- `([L:F] * [M:L]) = [M:F] = [K:F] = [L:F] * n`.
    have hmul' :
        Module.finrank F L * Module.finrank L M = Module.finrank F L * n := by
      have hfNat : f.natDegree = Module.finrank F L * n := by
        calc
          f.natDegree = Module.finrank F K := by simpa [K] using hfinrank_FKa.symm
          _ = Module.finrank F L * n := hfinrank_FK_mul
      calc
        Module.finrank F L * Module.finrank L M = Module.finrank F M := by simpa using hmul
        _ = f.natDegree := hfinrank_FM
        _ = Module.finrank F L * n := hfNat
    exact Nat.mul_left_cancel hpos hmul'

  have hnL : (n : L) ≠ 0 := by
    intro hnL0
    apply h_char
    have : algebraMap F L (n : F) = algebraMap F L 0 := by simpa using hnL0
    exact (FaithfulSMul.algebraMap_injective F L) this

  -- Let `b` be the element of `L = F⟮a^n⟯` corresponding to `a^n`.
  let b : L :=
    ⟨a ^ n, by
      -- `a ^ n ∈ F⟮a ^ n⟯` by construction.
      show a ^ n ∈ (L : Set E)
      simpa [L] using
        (IntermediateField.subset_adjoin F (Set.singleton (a ^ n)) (Set.mem_singleton (a ^ n)))⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    have : (a ^ n : E) = 0 := by
      have : (b : E) = 0 := by simpa [hb0]
      simpa [b] using this
    exact ha0 (eq_zero_of_pow_eq_zero this)

  have hnatDegree_minpoly_L : (minpoly L a).natDegree = n := by
    have hfinrank_adjoin : Module.finrank L M = (minpoly L a).natDegree := by
      simpa [M] using (IntermediateField.adjoin.finrank (K := L) (L := E) ha_intL)
    simpa [hfinrank_LM] using hfinrank_adjoin.symm

  have hminpoly_L : minpoly L a = (Polynomial.X ^ n - Polynomial.C b) := by
    -- `a` is a root of `X^n - b` over `L`, so `minpoly L a` divides that polynomial.
    have hdvd : minpoly L a ∣ (Polynomial.X ^ n - Polynomial.C b) := by
      refine minpoly.dvd (A := L) (x := a) ?_
      simp [b]
    have hq_monic : ((Polynomial.X ^ n - Polynomial.C b) : L[X]).Monic :=
      Polynomial.monic_X_pow_sub_C b hn0
    have hp_monic : (minpoly L a).Monic := minpoly.monic ha_intL
    have hdeg :
        ((Polynomial.X ^ n - Polynomial.C b) : L[X]).natDegree ≤ (minpoly L a).natDegree := by
      simpa [Polynomial.natDegree_X_pow_sub_C, hnatDegree_minpoly_L]
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hp_monic hq_monic hdvd hdeg).symm

  letI : f.IsSplittingField F E := h_splitting_field
  haveI : Normal F E := Normal.of_isSplittingField (p := f)
  haveI : Normal L E := Normal.tower_top_of_normal (F := F) (K := L) (E := E)

  have hsplit :
      ((Polynomial.map (algebraMap L E) ((Polynomial.X ^ n - Polynomial.C b) : L[X]))).Splits := by
    simpa [hminpoly_L] using
      (Normal.splits (F := L) (K := E) (inferInstance : Normal L E) a)

  have hsep : ((Polynomial.X ^ n - Polynomial.C b) : L[X]).Separable :=
    Polynomial.separable_X_pow_sub_C (a := b) hnL hb0

  have hcard_rootSet :
      Fintype.card (((Polynomial.X ^ n - Polynomial.C b) : L[X]).rootSet E) = n := by
    have hcard :=
      Polynomial.card_rootSet_eq_natDegree (F := L) (K := E) (p := (Polynomial.X ^ n - Polynomial.C b)) hsep
        hsplit
    simpa [Polynomial.natDegree_X_pow_sub_C] using hcard

  have hn_le_card :
      n ≤ Fintype.card (rootsOfUnity n E) := by
    let p : L[X] := (Polynomial.X ^ n - Polynomial.C b)
    let φ : p.rootSet E → rootsOfUnity n E := fun r =>
      rootsOfUnity.mkOfPowEq (r.1 / a) (by
        have hr : Polynomial.aeval r.1 p = 0 :=
          Polynomial.aeval_eq_zero_of_mem_rootSet (hx := r.2)
        have hr' : (r.1 : E) ^ n = a ^ n := by
          have : (r.1 : E) ^ n - a ^ n = 0 := by simpa [p, b] using hr
          exact sub_eq_zero.mp this
        calc
          (r.1 / a) ^ n = r.1 ^ n / a ^ n := by simp [div_pow]
          _ = a ^ n / a ^ n := by simpa [hr']
          _ = 1 := by simp [pow_ne_zero n ha0])
    have hφ_inj : Function.Injective φ := by
      intro r s hrs
      apply Subtype.ext
      have hdiv :
          (r.1 / a : E) = (s.1 / a : E) := by
        simpa [φ, rootsOfUnity.coe_mkOfPowEq] using
          congrArg (fun x : rootsOfUnity n E => ((x : Eˣ) : E)) hrs
      have := congrArg (fun t : E => t * a) hdiv
      simpa [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ ha0] using this
    have hcard_le : Fintype.card (p.rootSet E) ≤ Fintype.card (rootsOfUnity n E) :=
      Fintype.card_le_of_injective φ hφ_inj
    -- Rewrite the LHS using the computed cardinality of the root set.
    simpa [p, hcard_rootSet] using hcard_le

  have hEnough : HasEnoughRootsOfUnity E n :=
    HasEnoughRootsOfUnity.of_card_le (R := E) (n := n) hn_le_card
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot E n
  refine (Finset.nonempty_iff_ne_empty).1 ?_
  refine ⟨ζ, (mem_primitiveRoots hnpos).2 hζ⟩

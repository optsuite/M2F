import Mathlib

open IntermediateField

-- A field of characteristic ≠ 2 has a primitive 2nd root of unity.
lemma primitiveRoots_two_nonempty (K : Type) [Field K] (hK : ¬ CharP K 2) :
    (primitiveRoots 2 K).Nonempty := by
  classical
  refine ⟨(-1 : K), ?_⟩
  have hchar : ringChar K ≠ 2 := by
    intro h
    exact hK (ringChar.eq_iff.mp h)
  have hprim : IsPrimitiveRoot (-1 : K) 2 := by
    simpa using (IsPrimitiveRoot.neg_one (R := K) (p := ringChar K) hchar)
  simpa [mem_primitiveRoots two_pos] using hprim

-- In characteristic `≠ 2`, we can freely cancel a factor `2`.
lemma two_ne_zero_of_not_charP_two (K : Type) [Field K] (hK : ¬ CharP K 2) : (2 : K) ≠ 0 := by
  classical
  have hchar : ringChar K ≠ 2 := by
    intro h
    exact hK (ringChar.eq_iff.mp h)
  exact Ring.two_ne_zero (R := K) hchar

-- If `x²` is in `K` and the corresponding `a : Kˣ` is a nonsquare, then `K⟮x⟯/K` is quadratic.
lemma fateh55_finrank_adjoin_simple_eq_two_of_pow_two {K L : Type} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] {a : Kˣ} {x : L}
    (hx : x ^ 2 = algebraMap K L a.1) (ha : ¬ IsSquare a) :
    Module.finrank K K⟮x⟯ = 2 := by
  classical
  have hx_int : IsIntegral K x := IsGalois.integral (F := K) (E := L) x
  have hmin_dvd : minpoly K x ∣ (Polynomial.X ^ (2 : ℕ) - Polynomial.C a.1) := by
    apply minpoly.dvd K x
    simp [hx]
  have hdeg_le : (minpoly K x).natDegree ≤ 2 := by
    have hp0 : (Polynomial.X ^ (2 : ℕ) - Polynomial.C a.1) ≠ 0 :=
      (Polynomial.monic_X_pow_sub_C a.1 (n := 2) (by decide)).ne_zero
    simpa [Polynomial.natDegree_X_pow_sub_C] using Polynomial.natDegree_le_of_dvd hmin_dvd hp0
  have hx_not_mem_bot : x ∉ (⊥ : IntermediateField K L) := by
    intro hx_mem
    have hx_range : x ∈ Set.range (algebraMap K L) := by
      simpa [IntermediateField.mem_bot] using hx_mem
    rcases hx_range with ⟨k, rfl⟩
    have hk_sq : k ^ 2 = a.1 := by
      have : algebraMap K L (k ^ 2) = algebraMap K L a.1 := by
        simpa [pow_two, map_mul] using hx
      exact (RingHom.injective (algebraMap K L)) (by simpa using this)
    have hk0 : (k : K) ≠ 0 := by
      intro hk0
      exact a.ne_zero (by simpa [hk0] using hk_sq.symm)
    have : IsSquare a := by
      refine ⟨Units.mk0 k hk0, ?_⟩
      -- `IsSquare` on units is definitional equality with `r * r`.
      apply Units.ext
      -- Compare values in `K`.
      simpa [Units.val_mk0, Units.val_mul, pow_two] using hk_sq.symm
    exact ha this
  have hdeg_ne_one : (minpoly K x).natDegree ≠ 1 := by
    intro h1
    have : Module.finrank K K⟮x⟯ = 1 := by
      simpa [IntermediateField.adjoin.finrank hx_int, h1]
    have : x ∈ (⊥ : IntermediateField K L) :=
      (IntermediateField.finrank_adjoin_simple_eq_one_iff (F := K) (E := L) (α := x)).1 this
    exact hx_not_mem_bot this
  have hdeg_ge : 2 ≤ (minpoly K x).natDegree := by
    by_contra hlt
    have hlt' : (minpoly K x).natDegree < 2 := lt_of_not_ge hlt
    have hle1 : (minpoly K x).natDegree ≤ 1 := Nat.lt_succ_iff.mp hlt'
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
    · exact (minpoly.natDegree_pos hx_int).ne' (by simpa [h0])
    · exact hdeg_ne_one h1
  have hdeg : (minpoly K x).natDegree = 2 := le_antisymm hdeg_le (by exact hdeg_ge)
  simpa [IntermediateField.adjoin.finrank hx_int, hdeg]

-- If `a/b` is a square in `Kˣ`, then adjoining `√a` or `√b` gives the same quadratic field.
lemma fateh55_adjoin_simple_eq_of_isSquare_div {K L : Type} [Field K] [Field L] [Algebra K L]
    {a b : Kˣ} {x y : L}
    (hx : x ^ 2 = algebraMap K L a.1) (hy : y ^ 2 = algebraMap K L b.1)
    (hsq : IsSquare (a / b)) : K⟮x⟯ = K⟮y⟯ := by
  classical
  rcases hsq with ⟨c, hc⟩
  have hab : a = c * c * b := by
    calc
      a = (a / b) * b := by simp [div_eq_mul_inv, mul_assoc]
      _ = (c * c) * b := by simpa [hc]
      _ = c * c * b := by simp [mul_assoc]
  have ha_val : (a : K) = c.1 * c.1 * b.1 := by
    simpa [hab, Units.val_mul, mul_assoc] using congrArg (fun u : Kˣ => (u : K)) hab
  set z : L := (algebraMap K L c.1) * y
  have hz_sq : z ^ 2 = algebraMap K L a.1 := by
    calc
      z ^ 2 = (algebraMap K L c.1) ^ 2 * y ^ 2 := by
        simpa [z] using (mul_pow (algebraMap K L c.1) y 2)
      _ = (algebraMap K L c.1) ^ 2 * algebraMap K L b.1 := by simp [hy]
      _ = algebraMap K L (c.1 * c.1 * b.1) := by
        simp [pow_two, map_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = algebraMap K L a.1 := by simpa [ha_val]
  have hxz_sq : x ^ 2 = z ^ 2 := by
    calc
      x ^ 2 = algebraMap K L a.1 := hx
      _ = z ^ 2 := by simpa [hz_sq]
  have hx_mem : x ∈ K⟮y⟯ := by
    have hz_mem : z ∈ K⟮y⟯ := by
      refine mul_mem (algebraMap_mem (S := K⟮y⟯) c.1) (mem_adjoin_simple_self K y)
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hxz_sq with hpos | hneg
    · simpa [hpos] using hz_mem
    · simpa [hneg] using (neg_mem hz_mem)
  have hxy : K⟮x⟯ ≤ K⟮y⟯ := (adjoin_simple_le_iff (F := K) (E := L) (α := x)).2 hx_mem

  -- Now use the inverse witness to get the reverse inclusion.
  have hba : b = c⁻¹ * c⁻¹ * a := by
    -- invert `a / b = c*c` and multiply by `a`.
    have hdiv : b / a = c⁻¹ * c⁻¹ := by
      calc
        b / a = (a / b)⁻¹ := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        _ = (c * c)⁻¹ := by simpa [hc]
        _ = c⁻¹ * c⁻¹ := by simp [mul_assoc]
    calc
      b = (b / a) * a := by simp [div_eq_mul_inv, mul_assoc]
      _ = (c⁻¹ * c⁻¹) * a := by simpa [hdiv]
      _ = c⁻¹ * c⁻¹ * a := by simp [mul_assoc]
  have hb_val : (b : K) = (c⁻¹).1 * (c⁻¹).1 * a.1 := by
    simpa [hba, Units.val_mul, mul_assoc] using congrArg (fun u : Kˣ => (u : K)) hba
  set w : L := (algebraMap K L (c⁻¹ : Kˣ).1) * x
  have hw_sq : w ^ 2 = algebraMap K L b.1 := by
    calc
      w ^ 2 = (algebraMap K L (c⁻¹ : Kˣ).1) ^ 2 * x ^ 2 := by
        simpa [w] using (mul_pow (algebraMap K L (c⁻¹ : Kˣ).1) x 2)
      _ = (algebraMap K L (c⁻¹ : Kˣ).1) ^ 2 * algebraMap K L a.1 := by simp [hx]
      _ = algebraMap K L ((c⁻¹ : Kˣ).1 * (c⁻¹ : Kˣ).1 * a.1) := by
        simp [pow_two, map_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = algebraMap K L b.1 := by
        simpa [hb_val, mul_assoc]
  have hyw_sq : y ^ 2 = w ^ 2 := by
    calc
      y ^ 2 = algebraMap K L b.1 := hy
      _ = w ^ 2 := by simpa [hw_sq]
  have hy_mem : y ∈ K⟮x⟯ := by
    have hw_mem : w ∈ K⟮x⟯ := by
      refine mul_mem (algebraMap_mem (S := K⟮x⟯) (c⁻¹ : Kˣ).1) (mem_adjoin_simple_self K x)
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hyw_sq with hpos | hneg
    · simpa [hpos] using hw_mem
    · simpa [hneg] using (neg_mem hw_mem)
  have hyx : K⟮y⟯ ≤ K⟮x⟯ := (adjoin_simple_le_iff (F := K) (E := L) (α := y)).2 hy_mem
  exact le_antisymm hxy hyx

-- In a quadratic extension `K⟮x⟯/K`, any element `y` with `y^2 ∈ K` is either in `K` or a `K`-multiple of `x`.
-- In particular, if additionally `y^2 = b` with `b` a nonsquare, then `a / b` is a square.
lemma fateh55_isSquare_div_of_mem_adjoin_simple {K L : Type} [Field K] [Field L] [Algebra K L]
    [IsGalois K L] (hK : ¬ CharP K 2) {a b : Kˣ} {x y : L}
    (hx : x ^ 2 = algebraMap K L a.1) (hy : y ^ 2 = algebraMap K L b.1)
    (hy_mem : y ∈ K⟮x⟯) (hb : ¬ IsSquare b) : IsSquare (a / b) := by
  classical
  -- First, `y ∉ K`, by the nonsquare hypothesis on `b`.
  have hy_not_bot : y ∉ (⊥ : IntermediateField K L) := by
    intro hy_bot
    have hy_range : y ∈ Set.range (algebraMap K L) := by
      simpa [IntermediateField.mem_bot] using hy_bot
    rcases hy_range with ⟨k, rfl⟩
    have hk_sq : k ^ 2 = b.1 := by
      have : algebraMap K L (k ^ 2) = algebraMap K L b.1 := by
        simpa [pow_two, map_mul] using hy
      exact (RingHom.injective (algebraMap K L)) (by simpa using this)
    have hk0 : (k : K) ≠ 0 := by
      intro hk0
      exact b.ne_zero (by simpa [hk0] using hk_sq.symm)
    have : IsSquare b := by
      refine ⟨Units.mk0 k hk0, ?_⟩
      apply Units.ext
      simpa [Units.val_mk0, Units.val_mul, pow_two] using hk_sq.symm
    exact hb this

  -- Hence `x ∉ K` as well, since otherwise `K⟮x⟯ = ⊥` and `y ∈ K`.
  have hx_not_bot : x ∉ (⊥ : IntermediateField K L) := by
    intro hx_bot
    have hx_adjoin : (K⟮x⟯ : IntermediateField K L) = ⊥ := by
      simpa using (IntermediateField.adjoin_simple_eq_bot_iff (F := K) (E := L) (α := x)).2 hx_bot
    have : y ∈ (⊥ : IntermediateField K L) := by simpa [hx_adjoin] using hy_mem
    exact hy_not_bot this

  -- From `x^2 = a` we deduce `a` is a nonsquare in `Kˣ`.
  have ha : ¬ IsSquare a := by
    intro ha_sq
    rcases ha_sq with ⟨c, hc⟩
    have hc_val : (a : K) = c.1 * c.1 := by
      simpa [hc, Units.val_mul] using congrArg (fun u : Kˣ => (u : K)) hc
    have hx_sq : x ^ 2 = (algebraMap K L c.1) ^ 2 := by
      calc
        x ^ 2 = algebraMap K L a.1 := hx
        _ = algebraMap K L (c.1 * c.1) := by simpa [hc_val, mul_assoc]
        _ = (algebraMap K L c.1) ^ 2 := by simp [pow_two, map_mul, mul_assoc]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hx_sq with hpos | hneg
    · have : x ∈ (⊥ : IntermediateField K L) := by
        refine (IntermediateField.mem_bot).2 ?_
        refine ⟨c.1, ?_⟩
        simpa [hpos]
      exact hx_not_bot this
    · have : x ∈ (⊥ : IntermediateField K L) := by
        refine (IntermediateField.mem_bot).2 ?_
        refine ⟨-c.1, ?_⟩
        simpa [hneg]
      exact hx_not_bot this

  -- Work in the quadratic subextension `E = K⟮x⟯`.
  let E : IntermediateField K L := K⟮x⟯
  have hx_int : IsIntegral K x := IsGalois.integral (F := K) (E := L) x
  have hE2 : Module.finrank K E = 2 :=
    fateh55_finrank_adjoin_simple_eq_two_of_pow_two (K := K) (L := L) hx ha
  haveI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional (K := K) (L := L) hx_int

  -- `E/K` is separable (as a subextension of a separable extension), hence Galois since it is quadratic.
  haveI : Algebra.IsQuadraticExtension K E := { finrank_eq_two' := hE2 }
  haveI : Algebra.IsSeparable K L := (inferInstance : Algebra.IsSeparable K L)
  haveI : Algebra.IsSeparable K E := Algebra.isSeparable_tower_bot_of_isSeparable K E L
  haveI : IsGalois K E := Algebra.IsQuadraticExtension.isGalois (F := K) (K := E)

  -- View `x` and `y` as elements of `E`.
  have hy_mem' : y ∈ (E : Set L) := hy_mem
  let yE : E := ⟨y, hy_mem'⟩
  let xE : E := AdjoinSimple.gen K x
  have hxE : xE ^ 2 = algebraMap K E a.1 := by
    ext
    simpa [xE] using hx
  have hyE : yE ^ 2 = algebraMap K E b.1 := by
    ext
    simpa [yE] using hy

  -- `yE` is not in the base field, again by nonsquareness of `b`.
  have hyE_not_range : yE ∉ Set.range (algebraMap K E) := by
    intro hyE_range
    rcases hyE_range with ⟨k, hk⟩
    have hk_sq : k ^ 2 = b.1 := by
      have : algebraMap K E (k ^ 2) = algebraMap K E b.1 := by
        simpa [hk, pow_two, map_mul] using hyE
      exact (RingHom.injective (algebraMap K E)) (by simpa using this)
    have hk0 : (k : K) ≠ 0 := by
      intro hk0
      exact b.ne_zero (by simpa [hk0] using hk_sq.symm)
    have : IsSquare b := by
      refine ⟨Units.mk0 k hk0, ?_⟩
      apply Units.ext
      simpa [Units.val_mk0, Units.val_mul, pow_two] using hk_sq.symm
    exact hb this

  -- The Galois group `Gal(E/K)` has cardinality `2`, so it has a unique nontrivial element `σ`.
  have hcardGal : Nat.card (Gal(E/K)) = 2 := by
    -- `Nat.card Gal(E/K) = finrank K E = 2`
    simpa [hE2] using (IsGalois.card_aut_eq_finrank (F := K) (E := (E : Type)))
  have huniq : ∃! σ : Gal(E/K), σ ≠ 1 :=
    (Nat.card_eq_two_iff' (x := (1 : Gal(E/K)))).1 hcardGal
  rcases huniq with ⟨σ, hσ_ne, hσ_unique⟩

  -- Show `σ` sends both `xE` and `yE` to their negatives.
  have hxσ : σ xE = -xE := by
    have hx_sq' : (σ xE) ^ 2 = xE ^ 2 := by
      calc
        (σ xE) ^ 2 = σ (xE ^ 2) := by simpa using (map_pow σ xE 2).symm
        _ = xE ^ 2 := by simp [hxE]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hx_sq' with hfix | hneg
    · -- If `σ` fixes `xE`, then `xE` is fixed by all automorphisms (since the group has size 2),
      -- hence `xE ∈ K`, contradicting `x ∉ K`.
      have hx_fixed : ∀ τ : Gal(E/K), τ xE = xE := by
        intro τ
        by_cases hτ : τ = 1
        · simpa [hτ]
        · have : τ = σ := hσ_unique τ hτ
          simpa [this, hfix]
      have hx_range : xE ∈ Set.range (algebraMap K E) :=
        (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := E) xE).2 hx_fixed
      -- Push forward to `L` to contradict `hx_not_bot`.
      rcases hx_range with ⟨k, hk⟩
      have : x ∈ (⊥ : IntermediateField K L) := by
        refine (IntermediateField.mem_bot).2 ⟨k, ?_⟩
        -- Coerce `hk : algebraMap K E k = xE` into `L`.
        have hk' : algebraMap K L k = x := by
          -- Use scalar tower compatibility.
          have : algebraMap K L k = algebraMap E L (algebraMap K E k) := by
            simpa using (IsScalarTower.algebraMap_apply K E L k)
          simpa [xE, hk] using this
        simpa [hk']
      exact (hx_not_bot this).elim
    · simpa [hneg]

  have hyσ : σ yE = -yE := by
    have hy_sq' : (σ yE) ^ 2 = yE ^ 2 := by
      calc
        (σ yE) ^ 2 = σ (yE ^ 2) := by simpa using (map_pow σ yE 2).symm
        _ = yE ^ 2 := by simp [hyE]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hy_sq' with hfix | hneg
    · -- If `σ` fixes `yE`, then `yE ∈ K`, contradicting nonsquareness of `b`.
      have hy_fixed : ∀ τ : Gal(E/K), τ yE = yE := by
        intro τ
        by_cases hτ : τ = 1
        · simpa [hτ]
        · have : τ = σ := hσ_unique τ hτ
          simpa [this, hfix]
      have hy_range : yE ∈ Set.range (algebraMap K E) :=
        (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := E) yE).2 hy_fixed
      exfalso
      exact hyE_not_range hy_range
    · simpa [hneg]

  -- Hence `xE / yE` is fixed by `σ`, so by all of `Gal(E/K)` (since it has order 2), and thus lies in `K`.
  have hxyσ : σ (xE / yE) = xE / yE := by
    simp [div_eq_mul_inv, hxσ, hyσ, mul_assoc]
  have hxy_fixed : ∀ τ : Gal(E/K), τ (xE / yE) = xE / yE := by
    intro τ
    by_cases hτ : τ = 1
    · simpa [hτ]
    · have : τ = σ := hσ_unique τ hτ
      simpa [this, hxyσ]
  have hxy_range : (xE / yE) ∈ Set.range (algebraMap K E) :=
    (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := E) (xE / yE)).2 hxy_fixed
  rcases hxy_range with ⟨c, hc⟩

  -- Clear denominators to get `xE = c * yE`.
  have hyE0 : (yE : E) ≠ 0 := by
    intro hy0
    have h0 : algebraMap K E b.1 = 0 := by
      simpa [hy0] using hyE.symm
    have hb0 : (b : K) = 0 := (RingHom.injective (algebraMap K E)) (by simpa using h0)
    exact b.ne_zero hb0
  have hxy_mul : xE = algebraMap K E c * yE := by
    have := congrArg (fun t : E => t * yE) hc
    -- `(xE / yE) * yE = xE`
    have : algebraMap K E c * yE = xE := by
      simpa [div_eq_mul_inv, mul_assoc, hyE0] using this
    exact this.symm

  -- Compare squares and pull back to `K`.
  have habK : a.1 = c ^ 2 * b.1 := by
    -- Apply `algebraMap K E` injectivity.
    have : algebraMap K E a.1 = algebraMap K E (c ^ 2 * b.1) := by
      calc
        algebraMap K E a.1 = xE ^ 2 := by simpa [hxE]
        _ = (algebraMap K E c * yE) ^ 2 := by simpa [hxy_mul]
        _ = (algebraMap K E c) ^ 2 * yE ^ 2 := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using (mul_pow (algebraMap K E c) yE 2)
        _ = algebraMap K E (c ^ 2) * algebraMap K E b.1 := by simp [hyE, map_pow]
        _ = algebraMap K E (c ^ 2 * b.1) := by simp [map_mul, mul_assoc]
    exact (RingHom.injective (algebraMap K E)) (by simpa using this)

  have hc0 : (c : K) ≠ 0 := by
    intro hc0
    have : (a : K) = 0 := by simpa [habK, hc0] using congrArg (fun t : K => t) habK
    exact a.ne_zero this

  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  -- Show the underlying values agree in `K`.
  have : (a / b : Kˣ).1 = c ^ 2 := by
    -- `a/b = a.1 / b.1` in the base field.
    have hb0 : (b : K) ≠ 0 := b.ne_zero
    -- Multiply the equation `a = c^2 * b` by `b⁻¹`.
    calc
      (a / b : Kˣ).1 = a.1 * (b⁻¹).1 := by simp [div_eq_mul_inv, Units.val_mul]
      _ = a.1 / b.1 := by simp [div_eq_mul_inv]
      _ = (c ^ 2 * b.1) / b.1 := by simpa [habK]
      _ = c ^ 2 := by field_simp [hb0]
  simpa [Units.val_mk0, Units.val_mul, pow_two, this]

/-- A quadratic Galois extension `E/K` (with `char K ≠ 2`) is generated by a square root of a nonsquare unit. -/
lemma fateh55_quadratic_exists_sqrt_unit {K E : Type} [Field K] [Field E] [Algebra K E]
    [IsGalois K E] [FiniteDimensional K E] (hK : ¬ CharP K 2)
    (h2 : Module.finrank K E = 2) :
    ∃ a : Kˣ, ∃ x : E, x ^ 2 = algebraMap K E a.1 ∧ K⟮x⟯ = ⊤ ∧ ¬ IsSquare a := by
  classical
  have hbotne : (⊥ : IntermediateField K E) ≠ (⊤ : IntermediateField K E) := by
    intro h
    have hfr :
        Module.finrank K (⊥ : IntermediateField K E) =
          Module.finrank K (⊤ : IntermediateField K E) := by
      simpa using
        congrArg (fun F : IntermediateField K E => Module.finrank K (F : Type)) h
    have : (1 : Nat) = 2 := by
      simpa [IntermediateField.finrank_bot, IntermediateField.finrank_top', h2] using hfr
    exact (by decide : (1 : Nat) ≠ 2) this
  -- Use Kummer theory (for `n = 2`) to find `x` with `x^2 ∈ K` and `K⟮x⟯ = ⊤`.
  haveI : Algebra.IsQuadraticExtension K E := { finrank_eq_two' := h2 }
  have hζ : (primitiveRoots (Module.finrank K E) K).Nonempty := by
    simpa [h2] using primitiveRoots_two_nonempty K hK
  haveI : IsCyclic Gal(E/K) := Algebra.IsQuadraticExtension.isCyclic (F := K) (K := E)
  rcases (exists_root_adjoin_eq_top_of_isCyclic (K := K) (L := E) hζ) with ⟨x, hx_mem, hx_top⟩
  -- Rewrite `x ^ finrank = x ^ 2`.
  have hx_mem' : x ^ 2 ∈ Set.range (algebraMap K E) := by simpa [h2] using hx_mem
  rcases hx_mem' with ⟨k, hk⟩
  have hk0 : (k : K) ≠ 0 := by
    intro hk0
    have hx2 : x ^ 2 = 0 := by
      simpa [hk0] using hk.symm
    have hx0 : x = 0 := (sq_eq_zero_iff).1 hx2
    have hx_bot : x ∈ (⊥ : IntermediateField K E) := by
      refine (IntermediateField.mem_bot).2 ⟨0, ?_⟩
      simpa [hx0]
    have hx_adjoin : (K⟮x⟯ : IntermediateField K E) = ⊥ :=
      (IntermediateField.adjoin_simple_eq_bot_iff (F := K) (E := E) (α := x)).2 hx_bot
    have : (⊥ : IntermediateField K E) = (⊤ : IntermediateField K E) := by
      simpa [hx_adjoin] using hx_top
    exact hbotne this
  let a : Kˣ := Units.mk0 k hk0
  refine ⟨a, x, ?_, hx_top, ?_⟩
  · -- `x^2 = algebraMap a.1`
    simpa [a] using hk.symm
  · -- If `a` were a square, then `x ∈ K` and `K⟮x⟯ = ⊥`, contradicting `K⟮x⟯ = ⊤`.
    intro ha_sq
    rcases ha_sq with ⟨c, hc⟩
    have hk_sq : c.1 ^ 2 = k := by
      -- Compare the `K`-values in `c^2 = a`.
      simpa [pow_two, a, Units.val_mul] using (congrArg (fun u : Kˣ => u.1) hc).symm
    have hx_sq : x ^ 2 = (algebraMap K E c.1) ^ 2 := by
      calc
        x ^ 2 = algebraMap K E k := by simpa using hk.symm
        _ = algebraMap K E (c.1 ^ 2) := by simpa [hk_sq.symm]
        _ = (algebraMap K E c.1) ^ 2 := by simp [map_pow]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hx_sq with hpos | hneg
    · have hx_bot : x ∈ (⊥ : IntermediateField K E) := by
        refine (IntermediateField.mem_bot).2 ⟨c.1, ?_⟩
        simpa [hpos]
      have hx_adjoin : (K⟮x⟯ : IntermediateField K E) = ⊥ :=
        (IntermediateField.adjoin_simple_eq_bot_iff (F := K) (E := E) (α := x)).2 hx_bot
      have : (⊥ : IntermediateField K E) = (⊤ : IntermediateField K E) := by
        simpa [hx_adjoin] using hx_top
      exact hbotne this
    · have hx_bot : x ∈ (⊥ : IntermediateField K E) := by
        refine (IntermediateField.mem_bot).2 ⟨-c.1, ?_⟩
        simpa [hneg]
      have hx_adjoin : (K⟮x⟯ : IntermediateField K E) = ⊥ :=
        (IntermediateField.adjoin_simple_eq_bot_iff (F := K) (E := E) (α := x)).2 hx_bot
      have : (⊥ : IntermediateField K E) = (⊤ : IntermediateField K E) := by
        simpa [hx_adjoin] using hx_top
      exact hbotne this

-- In a Klein-four group we can choose two distinct order-2 subgroups with trivial intersection.
lemma fateh55_kleinFour_exists_two_order2_subgroups_inf_bot {G : Type*} [Group G] [IsKleinFour G] :
    ∃ H1 H2 : Subgroup G, H1 ≠ H2 ∧ Nat.card H1 = 2 ∧ Nat.card H2 = 2 ∧ H1 ⊓ H2 = ⊥ := by
  classical
  haveI : Finite G := IsKleinFour.instFinite
  let _ : Fintype G := Fintype.ofFinite G
  have hcardG : Fintype.card G = 4 := IsKleinFour.card_four' (G := G)
  have hone_mem : (1 : G) ∈ (Finset.univ : Finset G) := by simp
  -- Pick `g ≠ 1`.
  have hne1 : (Finset.univ.erase (1 : G)).Nonempty := by
    have : (Finset.univ.erase (1 : G)).card = 3 := by
      simpa [Finset.card_univ, hcardG] using Finset.card_erase_of_mem hone_mem
    exact Finset.card_pos.mp (by simpa [this])
  rcases hne1 with ⟨g, hg⟩
  have hg_ne : g ≠ 1 := (Finset.mem_erase.mp hg).1
  -- Pick `h ≠ 1, g`.
  have hne2 : ((Finset.univ.erase (1 : G)).erase g).Nonempty := by
    have hg_mem : g ∈ (Finset.univ.erase (1 : G)) := hg
    have : ((Finset.univ.erase (1 : G)).erase g).card = 2 := by
      simpa using (Finset.card_erase_of_mem hg_mem)
    exact Finset.card_pos.mp (by simpa [this])
  rcases hne2 with ⟨h, hh⟩
  have hh_ne1 : h ≠ 1 := by
    have : h ∈ (Finset.univ.erase (1 : G)) := Finset.mem_of_mem_erase hh
    exact (Finset.mem_erase.mp this).1
  have hh_neg : h ≠ g := (Finset.mem_erase.mp hh).1

  -- The two subgroups generated by `g` and `h`.
  refine ⟨Subgroup.zpowers g, Subgroup.zpowers h, ?_, ?_, ?_, ?_⟩
  · -- distinctness
    intro hEq
    have hg_mem' : g ∈ Subgroup.zpowers h := by
      -- `g ∈ zpowers g`, so transport along equality.
      simpa [hEq] using (Subgroup.mem_zpowers g)
    -- In `zpowers h`, the unique element different from `1` is `h`.
    have hcardH2 : Nat.card (Subgroup.zpowers h) = 2 := by
      have horder : orderOf h = 2 := (orderOf_eq_two_iff (hG := (IsKleinFour.exponent_two (G := G)))).2 hh_ne1
      have hF : Fintype.card (Subgroup.zpowers h) = 2 := by
        simpa [Fintype.card_zpowers, horder] using (rfl : Fintype.card (Subgroup.zpowers h) = Fintype.card (Subgroup.zpowers h))
      exact (Nat.card_eq_fintype_card (α := Subgroup.zpowers h)).trans (by
        simpa [Fintype.card_zpowers, horder] using (Fintype.card_zpowers (x := h)))
    have huniq : ∃! u : Subgroup.zpowers h, u ≠ 1 :=
      (Nat.card_eq_two_iff' (x := (1 : Subgroup.zpowers h))).1 hcardH2
    rcases huniq with ⟨u, hu_ne, hu_unique⟩
    have hh_mem : (⟨h, Subgroup.mem_zpowers h⟩ : Subgroup.zpowers h) ≠ 1 := by
      -- `h ≠ 1`
      intro hh1
      exact hh_ne1 (by
        have := congrArg (fun z : Subgroup.zpowers h => (z : G)) hh1
        simpa using this)
    have hu : u = ⟨h, Subgroup.mem_zpowers h⟩ := (hu_unique _ hh_mem).symm
    have hg_ne1' : (⟨g, hg_mem'⟩ : Subgroup.zpowers h) ≠ 1 := by
      intro hg1
      exact hg_ne (by
        have := congrArg (fun z : Subgroup.zpowers h => (z : G)) hg1
        simpa using this)
    have : (⟨g, hg_mem'⟩ : Subgroup.zpowers h) = ⟨h, Subgroup.mem_zpowers h⟩ :=
      by simpa [hu] using (hu_unique _ hg_ne1')
    exact hh_neg (by
      have := congrArg (fun z : Subgroup.zpowers h => (z : G)) this
      simpa using this.symm)
  · -- `Nat.card (zpowers g) = 2`
    have horder : orderOf g = 2 :=
      (orderOf_eq_two_iff (hG := (IsKleinFour.exponent_two (G := G)))).2 hg_ne
    exact (Nat.card_eq_fintype_card (α := Subgroup.zpowers g)).trans (by
      simpa [Fintype.card_zpowers, horder] using (Fintype.card_zpowers (x := g)))
  · -- `Nat.card (zpowers h) = 2`
    have horder : orderOf h = 2 :=
      (orderOf_eq_two_iff (hG := (IsKleinFour.exponent_two (G := G)))).2 hh_ne1
    exact (Nat.card_eq_fintype_card (α := Subgroup.zpowers h)).trans (by
      simpa [Fintype.card_zpowers, horder] using (Fintype.card_zpowers (x := h)))
  · -- trivial intersection
    have hcardH1 : Nat.card (Subgroup.zpowers g) = 2 := by
      have horder : orderOf g = 2 :=
        (orderOf_eq_two_iff (hG := (IsKleinFour.exponent_two (G := G)))).2 hg_ne
      exact (Nat.card_eq_fintype_card (α := Subgroup.zpowers g)).trans (by
        simpa [Fintype.card_zpowers, horder] using (Fintype.card_zpowers (x := g)))
    have hcardH2 : Nat.card (Subgroup.zpowers h) = 2 := by
      have horder : orderOf h = 2 :=
        (orderOf_eq_two_iff (hG := (IsKleinFour.exponent_two (G := G)))).2 hh_ne1
      exact (Nat.card_eq_fintype_card (α := Subgroup.zpowers h)).trans (by
        simpa [Fintype.card_zpowers, horder] using (Fintype.card_zpowers (x := h)))
    have huniq1 : ∃! u : Subgroup.zpowers g, u ≠ 1 :=
      (Nat.card_eq_two_iff' (x := (1 : Subgroup.zpowers g))).1 hcardH1
    have huniq2 : ∃! u : Subgroup.zpowers h, u ≠ 1 :=
      (Nat.card_eq_two_iff' (x := (1 : Subgroup.zpowers h))).1 hcardH2
    rcases huniq1 with ⟨u1, hu1_ne, hu1_unique⟩
    rcases huniq2 with ⟨u2, hu2_ne, hu2_unique⟩
    have hgU : u1 = ⟨g, Subgroup.mem_zpowers g⟩ := by
      have : (⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g) ≠ 1 := by
        intro hg1
        exact hg_ne (by
          have := congrArg (fun z : Subgroup.zpowers g => (z : G)) hg1
          simpa using this)
      exact (hu1_unique _ this).symm
    have hhU : u2 = ⟨h, Subgroup.mem_zpowers h⟩ := by
      have : (⟨h, Subgroup.mem_zpowers h⟩ : Subgroup.zpowers h) ≠ 1 := by
        intro hh1
        exact hh_ne1 (by
          have := congrArg (fun z : Subgroup.zpowers h => (z : G)) hh1
          simpa using this)
      exact (hu2_unique _ this).symm
    apply le_antisymm
    · intro z hz
      have hz1 : z = 1 := by
        by_contra hz_ne
        have hzH1 : (⟨z, hz.1⟩ : Subgroup.zpowers g) ≠ 1 := by
          intro hz1'
          exact hz_ne (by
            have := congrArg (fun w : Subgroup.zpowers g => (w : G)) hz1'
            simpa using this)
        have hzH2 : (⟨z, hz.2⟩ : Subgroup.zpowers h) ≠ 1 := by
          intro hz1'
          exact hz_ne (by
            have := congrArg (fun w : Subgroup.zpowers h => (w : G)) hz1'
            simpa using this)
        have hz_eq_g : (⟨z, hz.1⟩ : Subgroup.zpowers g) = ⟨g, Subgroup.mem_zpowers g⟩ := by
          simpa [hgU] using (hu1_unique _ hzH1)
        have hz_eq_h : (⟨z, hz.2⟩ : Subgroup.zpowers h) = ⟨h, Subgroup.mem_zpowers h⟩ := by
          simpa [hhU] using (hu2_unique _ hzH2)
        have : g = h := by
          have hz_eq_g' := congrArg (fun w : Subgroup.zpowers g => (w : G)) hz_eq_g
          have hz_eq_h' := congrArg (fun w : Subgroup.zpowers h => (w : G)) hz_eq_h
          -- both say `z = g` and `z = h`
          have hzEqg : z = g := by simpa using hz_eq_g'
          have hzEqh : z = h := by simpa using hz_eq_h'
          exact hzEqg.symm.trans hzEqh
        exact hh_neg this.symm
      simpa [Subgroup.mem_bot, hz1]
    · exact bot_le

/--
Let $K$ be a field with $\operatorname{char}(K) \neq 2$. Consider a Galois extension $L/K$.
Show that $\operatorname{Gal}(L/K) \cong (\mathbb{Z}/2\mathbb{Z})^2$ if and only if
the extensions $L/K$ has the form $L = K(\sqrt{a}, \sqrt{b})$ for $a, b \in K^\times$ such that
$a$, $b$, and $a/b$ are nonsquares in $K^\times$.
-/
-- TODO: replace this with a proof using Galois correspondence and Kummer theory
lemma kleinFour_iff_exists_pow_two_eq_algebraMap_and_adjoin_eq_top {K L : Type} [Field K]
    [Field L] [Algebra K L] [IsGalois K L] (hK : ¬ CharP K 2) :
    IsKleinFour (L ≃ₐ[K] L) ↔
    ∃ a b : Kˣ, ∃ x y : L, x ^ 2 = algebraMap K L a.1 ∧ y ^ 2 = algebraMap K L b.1 ∧
    K⟮x, y⟯ = ⊤ ∧ ¬IsSquare a ∧ ¬IsSquare b ∧ ¬IsSquare (a / b) := by
  classical
  constructor
  · intro hV4
    haveI : IsKleinFour (L ≃ₐ[K] L) := hV4
    haveI : Finite (L ≃ₐ[K] L) := IsKleinFour.instFinite
    have hfd : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite (F := K) (E := L)
    haveI : FiniteDimensional K L := hfd
    have hfinrank : Module.finrank K L = 4 := by
      have hcard : Nat.card (L ≃ₐ[K] L) = 4 := IsKleinFour.card_four (G := L ≃ₐ[K] L)
      have hcard' : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
        simpa using (IsGalois.card_aut_eq_finrank (F := K) (E := L))
      calc
        Module.finrank K L = Nat.card (L ≃ₐ[K] L) := by simpa using hcard'.symm
        _ = 4 := hcard

    -- Choose two distinct order-2 subgroups with trivial intersection.
    rcases fateh55_kleinFour_exists_two_order2_subgroups_inf_bot (G := (L ≃ₐ[K] L)) with
      ⟨H1, H2, hH12, hcard1, hcard2, hinf⟩

    -- Each fixed field `Eᵢ := fixedField Hᵢ` has degree `2` over `K`.
    have hfinrankE (H : Subgroup (L ≃ₐ[K] L)) (hcardH : Nat.card H = 2) :
        Module.finrank K (IntermediateField.fixedField (F := K) (E := L) H) = 2 := by
      classical
      letI : Fintype H := Fintype.ofFinite H
      have hcardH' : Fintype.card H = 2 := by
        simpa [Nat.card_eq_fintype_card] using hcardH
      have hFL : Module.finrank (IntermediateField.fixedField (F := K) (E := L) H) L = 2 := by
        simpa [hcardH'] using
          (IntermediateField.finrank_fixedField_eq_card (F := K) (E := L) (H := H))
      have hmul :=
        Module.finrank_mul_finrank K (IntermediateField.fixedField (F := K) (E := L) H) L
      have : Module.finrank K (IntermediateField.fixedField (F := K) (E := L) H) * 2 = 4 := by
        simpa [hFL, hfinrank] using hmul
      have : Module.finrank K (IntermediateField.fixedField (F := K) (E := L) H) = 2 := by
        have :
            Module.finrank K (IntermediateField.fixedField (F := K) (E := L) H) * 2 = 2 * 2 := by
          simpa using this
        exact Nat.mul_right_cancel (by decide : 0 < 2) this
      exact this

    -- Make the fixed fields Galois over `K` (index 2 subgroups are normal).
    haveI : Subgroup.Normal H1 := by
      haveI : Fintype H1 := Fintype.ofFinite H1
      have hcardH1' : Fintype.card H1 = 2 := by
        simpa [Nat.card_eq_fintype_card] using hcard1
      have hmul : Fintype.card H1 * H1.index = 4 := by
        -- `card_mul_index : Nat.card H1 * index = Nat.card G`, rewritten to `Fintype.card`.
        simpa [Nat.card_eq_fintype_card, IsKleinFour.card_four (G := (L ≃ₐ[K] L))] using
          (Subgroup.card_mul_index (H := H1) : Nat.card H1 * H1.index = Nat.card (L ≃ₐ[K] L))
      have hindex : H1.index = 2 := by
        have : 2 * H1.index = 4 := by simpa [hcardH1'] using hmul
        have : 2 * H1.index = 2 * 2 := by simpa using this
        exact Nat.mul_left_cancel (by decide : 0 < 2) this
      exact Subgroup.normal_of_index_eq_two hindex
    haveI : Subgroup.Normal H2 := by
      haveI : Fintype H2 := Fintype.ofFinite H2
      have hcardH2' : Fintype.card H2 = 2 := by
        simpa [Nat.card_eq_fintype_card] using hcard2
      have hmul : Fintype.card H2 * H2.index = 4 := by
        simpa [Nat.card_eq_fintype_card, IsKleinFour.card_four (G := (L ≃ₐ[K] L))] using
          (Subgroup.card_mul_index (H := H2) : Nat.card H2 * H2.index = Nat.card (L ≃ₐ[K] L))
      have hindex : H2.index = 2 := by
        have : 2 * H2.index = 4 := by simpa [hcardH2'] using hmul
        have : 2 * H2.index = 2 * 2 := by simpa using this
        exact Nat.mul_left_cancel (by decide : 0 < 2) this
      exact Subgroup.normal_of_index_eq_two hindex

    let E1 : IntermediateField K L := IntermediateField.fixedField (F := K) (E := L) H1
    let E2 : IntermediateField K L := IntermediateField.fixedField (F := K) (E := L) H2
    have hE1 : Module.finrank K (E1 : Type) = 2 := hfinrankE H1 hcard1
    have hE2 : Module.finrank K (E2 : Type) = 2 := hfinrankE H2 hcard2

    -- Produce `x` and `y` as square roots generating each quadratic fixed field.
    haveI : IsGalois K (E1 : Type) := by infer_instance
    haveI : IsGalois K (E2 : Type) := by infer_instance
    haveI : FiniteDimensional K (E1 : Type) :=
      (IntermediateField.finiteDimensional_left (K := K) (L := L) (F := E1))
    haveI : FiniteDimensional K (E2 : Type) :=
      (IntermediateField.finiteDimensional_left (K := K) (L := L) (F := E2))

    rcases fateh55_quadratic_exists_sqrt_unit (K := K) (E := (E1 : Type)) hK hE1 with ⟨a, x1, hx1, hx1_top, ha⟩
    rcases fateh55_quadratic_exists_sqrt_unit (K := K) (E := (E2 : Type)) hK hE2 with ⟨b, y1, hy1, hy1_top, hb⟩
    let x : L := (x1 : L)
    let y : L := (y1 : L)
    have hx : x ^ 2 = algebraMap K L a.1 := by
      simpa [x] using congrArg (fun t : E1 => (t : L)) hx1
    have hy : y ^ 2 = algebraMap K L b.1 := by
      simpa [y] using congrArg (fun t : E2 => (t : L)) hy1

    -- Identify `K⟮x⟯` with `E1` and `K⟮y⟯` with `E2` inside `L`.
    have hKx : (K⟮x⟯ : IntermediateField K L) = E1 := by
      have hx_mem : x ∈ E1 := by simpa [x]
      have hx_le : (K⟮x⟯ : IntermediateField K L) ≤ E1 :=
        (IntermediateField.adjoin_simple_le_iff (F := K) (E := L) (α := x)).2 hx_mem
      have hfinx : Module.finrank K (K⟮x⟯ : IntermediateField K L) = 2 :=
        fateh55_finrank_adjoin_simple_eq_two_of_pow_two (K := K) (L := L) hx ha
      exact IntermediateField.eq_of_le_of_finrank_eq (F := (K⟮x⟯ : IntermediateField K L)) (E := E1)
        hx_le (by simpa [hE1] using hfinx)
    have hKy : (K⟮y⟯ : IntermediateField K L) = E2 := by
      have hy_mem : y ∈ E2 := by simpa [y]
      have hy_le : (K⟮y⟯ : IntermediateField K L) ≤ E2 :=
        (IntermediateField.adjoin_simple_le_iff (F := K) (E := L) (α := y)).2 hy_mem
      have hfiny : Module.finrank K (K⟮y⟯ : IntermediateField K L) = 2 :=
        fateh55_finrank_adjoin_simple_eq_two_of_pow_two (K := K) (L := L) hy hb
      exact IntermediateField.eq_of_le_of_finrank_eq (F := (K⟮y⟯ : IntermediateField K L)) (E := E2)
        hy_le (by simpa [hE2] using hfiny)

    -- Show `K⟮x, y⟯ = ⊤` from `H1 ⊓ H2 = ⊥`.
    have hsup : E1 ⊔ E2 = (⊤ : IntermediateField K L) := by
      have hfix :
          (E1 ⊔ E2).fixingSubgroup = H1 ⊓ H2 := by
        -- `fixingSubgroup_sup` and `fixingSubgroup_fixedField`.
        simp [E1, E2, IntermediateField.fixingSubgroup_sup, IntermediateField.fixingSubgroup_fixedField]
      -- Use `fixedField_fixingSubgroup` to identify the intermediate field with `fixedField ⊥ = ⊤`.
      have := (IsGalois.fixedField_fixingSubgroup (F := K) (E := L) (K := (E1 ⊔ E2)))
      -- Rewrite via `hfix` and `hinf`.
      simpa [hfix, hinf] using this.symm

    have hxy : (K⟮x, y⟯ : IntermediateField K L) = ⊤ := by
      -- `K⟮x, y⟯ = K⟮x⟯ ⊔ K⟮y⟯`, then rewrite with `hKx`, `hKy`, and `hsup`.
      have hsupXY :
          (K⟮x, y⟯ : IntermediateField K L) =
            (K⟮x⟯ : IntermediateField K L) ⊔ (K⟮y⟯ : IntermediateField K L) := by
        have hset : ({x} ∪ ({y} : Set L)) = (insert x (Set.singleton y) : Set L) := by
          ext z
          constructor
          · intro hz
            rcases (Set.mem_union z ({x} : Set L) ({y} : Set L)).1 hz with hz | hz
            · have : z = x := by simpa [Set.mem_singleton_iff] using hz
              exact (Set.mem_insert_iff).2 (Or.inl this)
            · exact (Set.mem_insert_iff).2 (Or.inr hz)
          · intro hz
            rcases (Set.mem_insert_iff).1 hz with hz | hz
            · exact (Set.mem_union z ({x} : Set L) ({y} : Set L)).2
                (Or.inl (by simpa [Set.mem_singleton_iff, hz]))
            · exact (Set.mem_union z ({x} : Set L) ({y} : Set L)).2 (Or.inr hz)
        -- `K⟮x, y⟯` expands to `adjoin K (insert x {y})`.
        simpa [hset] using
          (IntermediateField.adjoin_union (F := K) (E := L) (S := ({x} : Set L)) (T := ({y} : Set L)))
      simpa [hsupXY, hKx, hKy, hsup] 

    -- Distinctness of the quadratic fixed fields yields `¬ IsSquare (a / b)`.
    have hab : ¬ IsSquare (a / b) := by
      intro hab_sq
      have : (K⟮x⟯ : IntermediateField K L) = K⟮y⟯ :=
        fateh55_adjoin_simple_eq_of_isSquare_div (K := K) (L := L) (a := a) (b := b) (x := x) (y := y) hx hy hab_sq
      -- Convert to an equality of fixed fields and contradict `H1 ≠ H2`.
      have : E1 = E2 := by simpa [hKx, hKy] using this
      have hH1 : IntermediateField.fixingSubgroup (F := K) (E := L) E1 = H1 := by
        simpa [E1] using (IntermediateField.fixingSubgroup_fixedField (F := K) (E := L) (H := H1))
      have hH2 : IntermediateField.fixingSubgroup (F := K) (E := L) E2 = H2 := by
        simpa [E2] using (IntermediateField.fixingSubgroup_fixedField (F := K) (E := L) (H := H2))
      have : H1 = H2 := by simpa [hH1, hH2] using congrArg (IntermediateField.fixingSubgroup (F := K) (E := L)) this
      exact hH12 this

    refine ⟨a, b, x, y, hx, hy, hxy, ha, hb, hab⟩
  · rintro ⟨a, b, x, y, hx, hy, hxy_top, ha, hb, hab⟩
    -- `L` is finite-dimensional since it is generated by two integral elements.
    have hx_int : IsIntegral K x := IsGalois.integral (F := K) (E := L) x
    have hy_int : IsIntegral K y := IsGalois.integral (F := K) (E := L) y
    have hfdXY : FiniteDimensional K (K⟮x, y⟯ : IntermediateField K L) :=
      IntermediateField.finiteDimensional_adjoin_pair (K := K) (x := x) (y := y) hx_int hy_int
    have hfdTop : FiniteDimensional K (⊤ : IntermediateField K L) :=
      (IntermediateField.equivOfEq (F := K) (E := L) hxy_top).toLinearEquiv.finiteDimensional
    haveI : FiniteDimensional K (⊤ : IntermediateField K L) := hfdTop
    haveI : FiniteDimensional K L :=
      (IntermediateField.topEquiv (F := K) (E := L)).toLinearEquiv.finiteDimensional

    -- Compute `finrank K L = 4` using the quadratic subfield `K⟮x⟯` and the ratio condition.
    have hfinx : Module.finrank K (K⟮x⟯ : IntermediateField K L) = 2 :=
      fateh55_finrank_adjoin_simple_eq_two_of_pow_two (K := K) (L := L) hx ha
    have hfiny : Module.finrank K (K⟮y⟯ : IntermediateField K L) = 2 :=
      fateh55_finrank_adjoin_simple_eq_two_of_pow_two (K := K) (L := L) hy hb

    have hle : Module.finrank K L ≤ 4 := by
      -- `K⟮x,y⟯ = K⟮x⟯ ⊔ K⟮y⟯`, and `finrank_sup_le`.
      have hsup :
          (K⟮x, y⟯ : IntermediateField K L) =
            (K⟮x⟯ : IntermediateField K L) ⊔ (K⟮y⟯ : IntermediateField K L) := by
        -- `K⟮x, y⟯ = adjoin K ({x} ∪ {y}) = K⟮x⟯ ⊔ K⟮y⟯`.
        have hset : ({x} ∪ ({y} : Set L)) = (insert x (Set.singleton y) : Set L) := by
          ext z
          constructor
          · intro hz
            rcases (Set.mem_union z ({x} : Set L) ({y} : Set L)).1 hz with hz | hz
            · have : z = x := by simpa [Set.mem_singleton_iff] using hz
              exact (Set.mem_insert_iff).2 (Or.inl this)
            · exact (Set.mem_insert_iff).2 (Or.inr hz)
          · intro hz
            rcases (Set.mem_insert_iff).1 hz with hz | hz
            · exact (Set.mem_union z ({x} : Set L) ({y} : Set L)).2
                (Or.inl (by simpa [Set.mem_singleton_iff, hz]))
            · exact (Set.mem_union z ({x} : Set L) ({y} : Set L)).2 (Or.inr hz)
        simpa [hset] using
          (IntermediateField.adjoin_union (F := K) (E := L) (S := ({x} : Set L)) (T := ({y} : Set L)))
      have htop : Module.finrank K (⊤ : IntermediateField K L) ≤ 4 := by
        -- First bound the finrank of the compositum `K⟮x⟯ ⊔ K⟮y⟯`.
        let J : IntermediateField K L := (K⟮x⟯ : IntermediateField K L) ⊔ (K⟮y⟯ : IntermediateField K L)
        have hleJ : Module.finrank K (J : IntermediateField K L) ≤ 4 := by
          have hle' :
              Module.finrank K (J : IntermediateField K L) ≤
                Module.finrank K (K⟮x⟯ : IntermediateField K L) * Module.finrank K (K⟮y⟯ : IntermediateField K L) :=
            IntermediateField.finrank_sup_le (K := K) (L := L)
              (E1 := (K⟮x⟯ : IntermediateField K L)) (E2 := (K⟮y⟯ : IntermediateField K L))
          simpa [J, hfinx, hfiny] using hle'
        -- Then transport this bound along the equality `J = ⊤`.
        have hJtop : J = ⊤ := by simpa [J, hsup] using hxy_top
        let e : (J : Type) ≃ₗ[K] (⊤ : IntermediateField K L) :=
          (IntermediateField.equivOfEq (F := K) (E := L) hJtop).toLinearEquiv
        have hfinEq : Module.finrank K (J : IntermediateField K L) = Module.finrank K (⊤ : IntermediateField K L) := by
          simpa [e] using (LinearEquiv.finrank_eq e)
        simpa [hfinEq] using hleJ
      simpa [IntermediateField.finrank_top' (F := K) (E := L)] using htop

    -- Show `K⟮x⟯ < ⊤`, using `¬ IsSquare (a/b)` to rule out `y ∈ K⟮x⟯`.
    have hy_not_mem : y ∉ (K⟮x⟯ : IntermediateField K L) := by
      intro hy_mem
      have : IsSquare (a / b) :=
        fateh55_isSquare_div_of_mem_adjoin_simple (K := K) (L := L) hK hx hy hy_mem hb
      exact hab this
    have hx_lt : (K⟮x⟯ : IntermediateField K L) < ⊤ := by
      refine lt_of_le_of_ne le_top ?_
      intro hx_top
      have : y ∈ (⊤ : IntermediateField K L) := by simp
      -- rewrite `⊤` as `K⟮x⟯` and contradict `hy_not_mem`.
      simpa [hx_top] using hy_not_mem

    have hge : 4 ≤ Module.finrank K L := by
      -- `finrank K L = finrank K K⟮x⟯ * finrank K⟮x⟯ L`, and `finrank K⟮x⟯ L ≥ 2`.
      have hmul := Module.finrank_mul_finrank K (K⟮x⟯ : IntermediateField K L) L
      have hlt' : 1 < Module.finrank (K⟮x⟯ : IntermediateField K L) L := by
        -- `finrank ⊤ L = 1 < finrank K⟮x⟯ L`.
        have hlt := IntermediateField.finrank_lt_of_gt (K := K) (L := L) (F := (K⟮x⟯ : IntermediateField K L))
          (E := (⊤ : IntermediateField K L)) hx_lt
        simpa using hlt
      have hge2 : 2 ≤ Module.finrank (K⟮x⟯ : IntermediateField K L) L :=
        (Nat.succ_le_iff).2 hlt'
      have hmul' : 2 * Module.finrank (K⟮x⟯ : IntermediateField K L) L = Module.finrank K L := by
        -- rewrite `hmul` using `hfinx`.
        simpa [hfinx, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
      have : 4 ≤ 2 * Module.finrank (K⟮x⟯ : IntermediateField K L) L := by
        exact Nat.mul_le_mul_left 2 hge2
      exact hmul' ▸ this

    have hfinrank : Module.finrank K L = 4 := Nat.le_antisymm hle hge
    have hcard : Nat.card (L ≃ₐ[K] L) = 4 := by
      simpa [hfinrank] using (IsGalois.card_aut_eq_finrank (F := K) (E := L))
    have hexp_dvd : Monoid.exponent (L ≃ₐ[K] L) ∣ 2 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
      intro σ
      -- Show `σ^2` fixes `x` and `y`, hence is the identity (since `K⟮x,y⟯ = ⊤`).
      have hx2 : (σ ^ 2) x = x := by
        have hx_sq : (σ x) ^ 2 = x ^ 2 := by
          calc
            (σ x) ^ 2 = σ (x ^ 2) := by simpa using (map_pow σ x 2).symm
            _ = x ^ 2 := by simp [hx]
        rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hx_sq with hpos | hneg
        · simpa [pow_two, hpos]
        · simpa [pow_two, hneg]
      have hy2 : (σ ^ 2) y = y := by
        have hy_sq : (σ y) ^ 2 = y ^ 2 := by
          calc
            (σ y) ^ 2 = σ (y ^ 2) := by simpa using (map_pow σ y 2).symm
            _ = y ^ 2 := by simp [hy]
        rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hy_sq with hpos | hneg
        · simpa [pow_two, hpos]
        · simpa [pow_two, hneg]
      -- Convert `K⟮x, y⟯ = ⊤` into `Algebra.adjoin K {x, y} = ⊤`.
      haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
      have hgen : Algebra.adjoin K ({x, y} : Set L) = (⊤ : Subalgebra K L) := by
        -- Use the equivalence between intermediate-field and algebra adjoin.
        have : (IntermediateField.adjoin K ({x, y} : Set L) : IntermediateField K L) = ⊤ := by
          simpa using hxy_top
        exact (IntermediateField.adjoin_eq_top_iff (F := K) (E := L) (S := ({x, y} : Set L))).1 this
      -- Use `AlgHom.ext_of_adjoin_eq_top` on `{x, y}`.
      have hhom : (σ ^ 2 : L →ₐ[K] L) = 1 := by
        apply AlgHom.ext_of_adjoin_eq_top (h := hgen)
        intro z hz
        rcases hz with rfl | rfl
        · simpa [pow_two] using hx2
        · simpa [pow_two] using hy2
      ext z
      simpa using congrArg (fun f : L →ₐ[K] L => f z) hhom

    -- `exponent ∣ 2` and the group has 4 elements, hence exponent is `2`.
    have hexp : Monoid.exponent (L ≃ₐ[K] L) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hexp_dvd with h1 | h2
      · -- exponent `= 1` would make the group subsingleton, contradicting `Nat.card = 4`.
        have hs : Subsingleton (L ≃ₐ[K] L) :=
          (Monoid.exp_eq_one_iff (G := L ≃ₐ[K] L)).1 h1
        have hcard1 : Nat.card (L ≃ₐ[K] L) = 1 := by
          classical
          letI : Subsingleton (L ≃ₐ[K] L) := hs
          letI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite (L ≃ₐ[K] L)
          have hft : Fintype.card (L ≃ₐ[K] L) = 1 := by
            refine (Fintype.card_eq_one_iff).2 ?_
            refine ⟨(1 : L ≃ₐ[K] L), ?_⟩
            intro σ
            exact Subsingleton.elim σ 1
          calc
            Nat.card (L ≃ₐ[K] L) = Fintype.card (L ≃ₐ[K] L) := Nat.card_eq_fintype_card
            _ = 1 := hft
        have h41 : (4 : Nat) = 1 := hcard.symm.trans hcard1
        exact False.elim ((by decide : (4 : Nat) ≠ 1) h41)
      · exact h2

    exact ⟨hcard, hexp⟩

-- A Klein four Galois group forces the extension to have degree 4.
lemma finiteDimensional_finrank_four_of_isKleinFour {K L : Type} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (h : IsKleinFour (L ≃ₐ[K] L)) :
    FiniteDimensional K L ∧ Module.finrank K L = 4 := by
  classical
  haveI : IsKleinFour (L ≃ₐ[K] L) := h
  haveI : Finite (L ≃ₐ[K] L) := IsKleinFour.instFinite
  have hfd : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite (F := K) (E := L)
  haveI : FiniteDimensional K L := hfd
  have hcard : Nat.card (L ≃ₐ[K] L) = 4 := IsKleinFour.card_four (G := L ≃ₐ[K] L)
  have hcard' : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
    simpa using (IsGalois.card_aut_eq_finrank (F := K) (E := L))
  refine ⟨hfd, ?_⟩
  calc
    Module.finrank K L = Nat.card (L ≃ₐ[K] L) := by simpa using hcard'.symm
    _ = 4 := hcard

theorem exists_pow_two_eq_algebraMap_and_adjoin_eq_top {K L : Type} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] (hK : ¬ CharP K 2) : IsKleinFour (L ≃ₐ[K] L) ↔
    ∃ a b : Kˣ, ∃ x y : L, x ^ 2 = algebraMap K L a.1 ∧ y ^ 2 = algebraMap K L b.1 ∧
    K⟮x, y⟯ = ⊤ ∧ ¬IsSquare a ∧ ¬IsSquare b ∧ ¬IsSquare (a / b) := by
  simpa using kleinFour_iff_exists_pow_two_eq_algebraMap_and_adjoin_eq_top (K := K) (L := L) hK

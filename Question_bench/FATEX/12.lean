import Mathlib

open scoped NumberField

/-- Minkowski bound formula used in `NumberField.ClassNumber`. -/
noncomputable def M (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    ((Nat.factorial (Module.finrank ℚ K)) /
        (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
      Real.sqrt |NumberField.discr K|)

/-- A direct quadratic identity for the generator ω. -/
lemma omega_sq_sub_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; ω^2 - ω = -5 := by
  classical
  dsimp
  ring_nf
  simp [Complex.I_sq]
  have h : (0 : ℝ) ≤ 19 := by norm_num
  have hs : (Real.sqrt 19)^2 = (19 : ℝ) := by
    exact Real.sq_sqrt h
  have hs' : ((Real.sqrt 19)^2 : ℂ) = (19 : ℂ) := by
    exact_mod_cast hs
  simp [hs']
  ring_nf

/-- Numerical bounds for `Real.sqrt 19`. -/
lemma sqrt_19_bounds : (4 : ℝ) < Real.sqrt 19 ∧ Real.sqrt 19 < 5 := by
  have h1 : (4 : ℝ) ^ 2 < (19 : ℝ) := by norm_num
  have h2 : (19 : ℝ) < (5 : ℝ) ^ 2 := by norm_num
  have h1' : (4 : ℝ) < Real.sqrt 19 := by
    exact Real.lt_sqrt_of_sq_lt (by simpa using h1)
  have h2' : Real.sqrt 19 < 5 := by
    have hy : (0 : ℝ) < 5 := by norm_num
    exact (Real.sqrt_lt' hy).2 (by simpa using h2)
  exact ⟨h1', h2'⟩

/-- A sharper upper bound for `Real.sqrt 19`. -/
lemma sqrt_19_lt_9_div_2 : Real.sqrt 19 < (9 / 2 : ℝ) := by
  have hpos : (0 : ℝ) < (9 / 2 : ℝ) := by norm_num
  have h : (19 : ℝ) < (9 / 2 : ℝ) ^ 2 := by norm_num
  exact (Real.sqrt_lt' hpos).2 h

/-- The floor of `(2 / π) * √19` is `2`. -/
lemma floor_two_div_pi_mul_sqrt_19 :
    ⌊(2 / Real.pi) * Real.sqrt 19⌋₊ = 2 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : 0 ≤ (2 / Real.pi) * Real.sqrt 19 := by
    have hdiv : 0 ≤ (2 / Real.pi : ℝ) := by
      exact div_nonneg (by norm_num) (le_of_lt hpi_pos)
    exact mul_nonneg hdiv (Real.sqrt_nonneg _)
  have hdiv_pos : 0 < (2 / Real.pi : ℝ) := by
    exact div_pos (by norm_num) hpi_pos
  have h4_lt : (4 : ℝ) < Real.sqrt 19 := (sqrt_19_bounds).1
  have hmul_lt : (2 / Real.pi : ℝ) * 4 < (2 / Real.pi : ℝ) * Real.sqrt 19 := by
    exact mul_lt_mul_of_pos_left h4_lt hdiv_pos
  have h2_le_8_div_pi : (2 : ℝ) ≤ (8 : ℝ) / Real.pi := by
    have h : (2 : ℝ) * Real.pi ≤ 8 := by nlinarith [Real.pi_lt_four]
    exact (le_div_iff₀ hpi_pos).2 h
  have h2_le_mul : (2 : ℝ) ≤ (2 / Real.pi : ℝ) * 4 := by
    have h' : (2 / Real.pi : ℝ) * 4 = (8 : ℝ) / Real.pi := by
      ring
    simpa [h'] using h2_le_8_div_pi
  have hlower : (2 : ℝ) ≤ (2 / Real.pi : ℝ) * Real.sqrt 19 := by
    exact le_of_lt (lt_of_le_of_lt h2_le_mul hmul_lt)
  have hsq : Real.sqrt 19 < (9 / 2 : ℝ) := sqrt_19_lt_9_div_2
  have hmul' : (2 / Real.pi : ℝ) * Real.sqrt 19 < (2 / Real.pi : ℝ) * (9 / 2 : ℝ) := by
    exact mul_lt_mul_of_pos_left hsq hdiv_pos
  have h3 : (2 / Real.pi : ℝ) * (9 / 2 : ℝ) < 3 := by
    have h : (9 : ℝ) < 3 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h' : (9 : ℝ) / Real.pi < 3 := (div_lt_iff₀ hpi_pos).2 h
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  have hupper' : (2 / Real.pi : ℝ) * Real.sqrt 19 < 3 := lt_trans hmul' h3
  have hupper : (2 / Real.pi : ℝ) * Real.sqrt 19 < (2 : ℝ) + 1 := by
    nlinarith [hupper']
  exact (Nat.floor_eq_iff hpos).2 ⟨hlower, hupper⟩

/-- The quadratic integer ω is a root of `X^2 - X + 5`. -/
lemma omega_isRoot_X2_sub_X_add_5 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)).eval₂
        (algebraMap ℚ ℂ) ω = 0 := by
  classical
  dsimp
  have h :
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
          ((1 + (Real.sqrt 19) * Complex.I) / 2) = -5 := by
    simpa using (omega_sq_sub_omega)
  have h' :
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
          ((1 + (Real.sqrt 19) * Complex.I) / 2) + 5 = 0 := by
    calc
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
          ((1 + (Real.sqrt 19) * Complex.I) / 2) + 5 =
          -5 + 5 := by simp [h]
      _ = 0 := by ring
  simpa using h'

/-- The quadratic polynomial `X^2 - X + 5` is irreducible over `ℚ`. -/
lemma irreducible_X2_sub_X_add_5 :
    Irreducible (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
  classical
  let p : Polynomial ℚ := Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)
  have hp_monic : p.Monic := by
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℚ) * Polynomial.X + Polynomial.C (5 : ℚ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℚ)) (b := (5 : ℚ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic : (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℚ)) (n := 2) hdeg
    simpa [p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  have hp_natDegree : p.natDegree = 2 := by
    have ha : (1 : ℚ) ≠ 0 := by norm_num
    have h :=
      (Polynomial.natDegree_quadratic (a := (1 : ℚ)) (b := (-1 : ℚ)) (c := (5 : ℚ)) ha)
    simpa [p, sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h
  by_contra h
  have h' :=
    (Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff (p := p) hp_monic hp_natDegree).1 h
  rcases h' with ⟨c1, c2, hprod, hsum⟩
  have hprod' : c1 * c2 = (5 : ℚ) := by
    simpa [p] using hprod.symm
  have hsum' : c1 + c2 = (-1 : ℚ) := by
    simpa [p] using hsum.symm
  have hdisc : (c1 - c2)^2 = (-19 : ℚ) := by
    calc
      (c1 - c2)^2 = (c1 + c2)^2 - 4 * c1 * c2 := by ring
      _ = (-1 : ℚ)^2 - 4 * c1 * c2 := by simp [hsum']
      _ = (-1 : ℚ)^2 - 4 * (c1 * c2) := by ring
      _ = (-1 : ℚ)^2 - 4 * 5 := by simp [hprod']
      _ = (-19 : ℚ) := by norm_num
  have hnonneg : (0 : ℚ) ≤ (c1 - c2)^2 := by nlinarith
  have : (0 : ℚ) ≤ (-19 : ℚ) := by simpa [hdisc] using hnonneg
  linarith

/-- The quadratic polynomial `X^2 - X + 5` is irreducible over `ℤ`. -/
lemma irreducible_X2_sub_X_add_5_Z :
    Irreducible (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
  classical
  let p : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)
  have hp_monic : p.Monic := by
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℤ) * Polynomial.X + Polynomial.C (5 : ℤ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℤ)) (b := (5 : ℤ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℤ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic : (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℤ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℤ)) (n := 2) hdeg
    simpa [p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  have hp_primitive : p.IsPrimitive := hp_monic.isPrimitive
  have hp_map : Irreducible (Polynomial.map (Int.castRingHom ℚ) p) := by
    simpa [p] using (irreducible_X2_sub_X_add_5)
  exact
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hp_primitive).2 hp_map

/-- Over `ZMod 2`, the polynomial `X^2 + X + 1` has no root. -/
lemma no_root_X2_add_X_add_one_zmod2 :
    ∀ x : ZMod 2, ¬ Polynomial.IsRoot
      (Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial (ZMod 2))) x := by
  intro x
  fin_cases x
  · simp
  · simp
    decide

/-- Over `ZMod 2`, the polynomial `X^2 + X + 1` is irreducible. -/
lemma irreducible_X2_add_X_add_one_zmod2 :
    Irreducible (Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial (ZMod 2))) := by
  have hdeg :
      (Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial (ZMod 2))).natDegree ∈
        Finset.Icc 1 3 := by
    have ha : (1 : ZMod 2) ≠ 0 := by
      decide
    have hdeg' :
        (Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial (ZMod 2))).natDegree = 2 := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
        mul_comm, mul_left_comm, mul_assoc] using
        (Polynomial.natDegree_quadratic (a := (1 : ZMod 2))
          (b := (1 : ZMod 2)) (c := (1 : ZMod 2)) ha)
    simp [hdeg']
  exact
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot hdeg
      no_root_X2_add_X_add_one_zmod2

/-- The mod-2 reduction of `X^2 - X + 5` is `X^2 + X + 1`. -/
lemma map_X2_sub_X_add_5_zmod2 :
    Polynomial.map (Int.castRingHom (ZMod 2))
      (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) =
      Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial (ZMod 2)) := by
  have h5 : (5 : ZMod 2) = 1 := by decide
  ext n
  cases n with
  | zero =>
      simp [sub_eq_add_neg, Polynomial.coeff_one]
      exact h5
  | succ n =>
      simp [sub_eq_add_neg, Polynomial.coeff_one]

/-- The quadratic integer ω is a root of `X^2 - X + 5` over `ℤ`. -/
lemma omega_isRoot_X2_sub_X_add_5_Z :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)).eval₂
        (algebraMap ℤ ℂ) ω = 0 := by
  classical
  dsimp
  have h :
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
          ((1 + (Real.sqrt 19) * Complex.I) / 2) = -5 := by
    simpa using (omega_sq_sub_omega)
  have h' :
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
          ((1 + (Real.sqrt 19) * Complex.I) / 2) + 5 = 0 := by
    calc
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
          ((1 + (Real.sqrt 19) * Complex.I) / 2) + 5 =
          -5 + 5 := by simp [h]
      _ = 0 := by ring
  simpa using h'

/-- The minimal polynomial of ω over `ℚ` is `X^2 - X + 5`. -/
lemma minpoly_omega_eq_X2_sub_X_add_5 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; minpoly ℚ ω = (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
  classical
  dsimp
  have hroot :
      Polynomial.aeval ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) = 0 := by
    simpa [Polynomial.aeval_def] using (omega_isRoot_X2_sub_X_add_5)
  have hmonic :
      (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)).Monic := by
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℚ) * Polynomial.X + Polynomial.C (5 : ℚ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℚ)) (b := (5 : ℚ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic' :
        (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℚ)) (n := 2) hdeg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic'
  exact
    (minpoly.eq_of_irreducible_of_monic (A := ℚ)
        (x := ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))
        irreducible_X2_sub_X_add_5 hroot hmonic).symm

/-- Local instance: the minimal polynomial of ω is irreducible. -/
local instance fact_irreducible_minpoly_omega_local :
    Fact (Irreducible
      (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) := by
  classical
  refine ⟨?_⟩
  simpa [minpoly_omega_eq_X2_sub_X_add_5] using irreducible_X2_sub_X_add_5

/-- Local instance: ω is integral over `ℤ`. -/
local instance isIntegral_omega_Z_local :
    IsIntegral ℤ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) := by
  classical
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ), ?_, ?_⟩
  ·
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℤ) * Polynomial.X + Polynomial.C (5 : ℤ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℤ)) (b := (5 : ℤ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℤ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic :
        (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℤ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℤ)) (n := 2) hdeg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  ·
    simpa [Polynomial.aeval_def] using (omega_isRoot_X2_sub_X_add_5_Z)

/-- Local instance: the `AdjoinRoot` generator is integral over `ℤ`. -/
local instance isIntegral_adjoinRoot_root_Z_local :
    IsIntegral ℤ
      (AdjoinRoot.root
        (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) := by
  classical
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ), ?_, ?_⟩
  ·
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℤ) * Polynomial.X + Polynomial.C (5 : ℤ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℤ)) (b := (5 : ℤ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℤ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic :
        (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℤ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℤ)) (n := 2) hdeg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  ·
    have hminpoly :
        minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) =
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
      simpa using (minpoly_omega_eq_X2_sub_X_add_5)
    have hrootQ :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) = 0 := by
      simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hrootQ' :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) = 0 := by
      simpa [hminpoly] using hrootQ
    have hmap :
        Polynomial.map (algebraMap ℤ ℚ)
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) =
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
      simp
    have hrootQ'' :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.map (algebraMap ℤ ℚ)
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ))) = 0 := by
      simpa [hmap] using hrootQ'
    have hmap_aeval :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.map (algebraMap ℤ ℚ)
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ))) =
          Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
      exact Polynomial.aeval_map_algebraMap (A := ℚ)
        (x := AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
        (p := (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)))
    calc
      Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) =
          Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
            (Polynomial.map (algebraMap ℤ ℚ)
              (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ))) := by
        symm
        exact hmap_aeval
      _ = 0 := hrootQ''

set_option maxHeartbeats 10000000 in
/-- The minimal polynomial of ω over `ℤ` is `X^2 - X + 5`. -/
lemma minpoly_omega_Z_eq_X2_sub_X_add_5 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; minpoly ℤ ω = (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
  classical
  dsimp
  have hInt :
      IsIntegral ℤ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) := by
    simpa using (isIntegral_omega_Z_local)
  have hmap :
      minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) =
        (minpoly ℤ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)).map (algebraMap ℤ ℚ) := by
    simpa using
      (minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ) (S := ℂ)
        (s := ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) hInt)
  have hmap' :
      Polynomial.map (algebraMap ℤ ℚ)
        (minpoly ℤ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) =
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
    simpa [minpoly_omega_eq_X2_sub_X_add_5] using hmap.symm
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  simpa using hmap'

set_option maxHeartbeats 10000000 in
/-- The minimal polynomial of the `AdjoinRoot` generator over `ℤ` is `X^2 - X + 5`. -/
lemma minpoly_adjoinRoot_root_Z_eq_X2_sub_X_add_5 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; minpoly ℤ (AdjoinRoot.root (minpoly ℚ ω)) =
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
  classical
  dsimp
  have hInt :
      IsIntegral ℤ
        (AdjoinRoot.root (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) := by
    simpa using (isIntegral_adjoinRoot_root_Z_local)
  have hmap :
      minpoly ℚ (AdjoinRoot.root (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) =
        (minpoly ℤ (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))).map (algebraMap ℤ ℚ) := by
    simpa using
      (minpoly.isIntegrallyClosed_eq_field_fractions' (R := ℤ) (K := ℚ)
        (S := AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
        (s := AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) hInt)
  have hrootQ :
      minpoly ℚ (AdjoinRoot.root (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) =
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
    have hroot :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) = 0 := by
      have hroot' :
          Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
            (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) = 0 := by
        simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      simpa [minpoly_omega_eq_X2_sub_X_add_5] using hroot'
    have hmonic :
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)).Monic := by
      have hdeg' :
          Polynomial.degree (Polynomial.C (-1 : ℚ) * Polynomial.X + Polynomial.C (5 : ℚ)) <
            (2 : ℕ) := by
        simpa using (Polynomial.degree_linear_lt (a := (-1 : ℚ)) (b := (5 : ℚ)))
      have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) := by
        simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
      have hmonic' :
          (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))).Monic :=
        Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℚ)) (n := 2) hdeg
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic'
    exact
      (minpoly.eq_of_irreducible_of_monic (A := ℚ)
          (x := AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          irreducible_X2_sub_X_add_5 hroot hmonic).symm
  have hmap' :
      Polynomial.map (algebraMap ℤ ℚ)
        (minpoly ℤ (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))) =
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
    simpa [hrootQ] using hmap.symm
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (IsFractionRing.injective ℤ ℚ)
  simpa using hmap'

/-- The `ℤ`-minpoly of the corresponding algebraic integer in `𝓞 K`. -/
lemma minpoly_ringOfIntegers_adjoinRoot_root_Z_eq_X2_sub_X_add_5 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; let K := AdjoinRoot (minpoly ℚ ω)
    ; let θ : 𝓞 K :=
        ⟨AdjoinRoot.root (minpoly ℚ ω), isIntegral_adjoinRoot_root_Z⟩
    ; minpoly ℤ θ = (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
  classical
  dsimp
  have h :
      minpoly ℤ (AdjoinRoot.root (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) =
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
    simpa using (minpoly_adjoinRoot_root_Z_eq_X2_sub_X_add_5)
  simpa [← NumberField.RingOfIntegers.minpoly_coe] using h

/-- The discriminant of `X^2 - X + 5` over `ℤ` is `-19`. -/
lemma discr_X2_sub_X_add_5_Z :
    Polynomial.discr (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) = (-19 : ℤ) := by
  classical
  set p : Polynomial ℤ := Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)
  have hdeg' : p.natDegree = 2 := by
    have ha : (1 : ℤ) ≠ 0 := by norm_num
    have h :=
      Polynomial.natDegree_quadratic (a := (1 : ℤ)) (b := (-1 : ℤ)) (c := (5 : ℤ)) ha
    simpa [p, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
      mul_assoc] using h
  have hdeg : p.degree = 2 := by
    exact (Polynomial.degree_eq_iff_natDegree_eq_of_pos (p := p) (n := 2) (by decide)).2 hdeg'
  have hdiscr := Polynomial.discr_of_degree_eq_two (f := p) hdeg
  have hx : (Polynomial.X : Polynomial ℤ).coeff 2 = 0 := by
    simpa using (Polynomial.coeff_X_of_ne_one (R := ℤ) (n := 2) (by decide))
  have hcoeff0 : p.coeff 0 = 5 := by
    simp [p, sub_eq_add_neg]
  have hcoeff1 : p.coeff 1 = -1 := by
    simp [p, sub_eq_add_neg]
  have hcoeff2 : p.coeff 2 = 1 := by
    simp [p, sub_eq_add_neg, hx]
  calc
    p.discr = p.coeff 1 ^ 2 - 4 * p.coeff 0 * p.coeff 2 := hdiscr
    _ = (-1 : ℤ)^2 - 4 * (5 : ℤ) * (1 : ℤ) := by simp [hcoeff0, hcoeff1, hcoeff2]
    _ = (-19 : ℤ) := by norm_num

/-- The polynomial `X^2 - X + 5` over `ℚ` has degree `2`. -/
lemma natDegree_X2_sub_X_add_5_Q :
    (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)).natDegree = 2 := by
  have hdeg' :
      Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) := by
    have hdeg'' :
        Polynomial.degree (Polynomial.C (-1 : ℚ) * Polynomial.X + Polynomial.C (5 : ℚ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℚ)) (b := (5 : ℚ)))
    simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg''
  have hdeg_lt :
      Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) <
        Polynomial.degree ((Polynomial.X : Polynomial ℚ) ^ 2) := by
    simpa using (show Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) from hdeg')
  have hdeg :
      Polynomial.degree
          ((Polynomial.X : Polynomial ℚ) ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))) =
        Polynomial.degree ((Polynomial.X : Polynomial ℚ) ^ 2) :=
    Polynomial.degree_add_eq_left_of_degree_lt hdeg_lt
  have hnat :
      ((Polynomial.X : Polynomial ℚ) ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))).natDegree =
        ((Polynomial.X : Polynomial ℚ) ^ 2).natDegree :=
    Polynomial.natDegree_eq_of_degree_eq hdeg
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnat

/-- The field `AdjoinRoot (minpoly ℚ ω)` has degree `2` over `ℚ`. -/
lemma finrank_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Module.finrank ℚ (AdjoinRoot (minpoly ℚ ω)) = 2 := by
  classical
  dsimp
  have hInt :
      IsIntegral ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ), ?_, ?_⟩
    ·
      have hdeg' :
          Polynomial.degree (Polynomial.C (-1 : ℚ) * Polynomial.X + Polynomial.C (5 : ℚ)) <
            (2 : ℕ) := by
        simpa using (Polynomial.degree_linear_lt (a := (-1 : ℚ)) (b := (5 : ℚ)))
      have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) := by
        simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
      have hmonic :
          (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))).Monic :=
        Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℚ)) (n := 2) hdeg
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
    ·
      simpa [Polynomial.aeval_def] using (omega_isRoot_X2_sub_X_add_5)
  have hne :
      minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) ≠ 0 := by
    exact minpoly.ne_zero hInt
  have hfinrank :
      Module.finrank ℚ
          (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) =
        (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)).natDegree := by
    simpa using
      (AdjoinRoot.powerBasis
          (f := minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) hne).finrank
  simpa [minpoly_omega_eq_X2_sub_X_add_5, natDegree_X2_sub_X_add_5_Q] using hfinrank

/-- The polynomial `x^2 - x + 5` has no real roots. -/
lemma no_real_root_X2_sub_X_add_5 (x : ℝ) : x ^ 2 - x + 5 ≠ 0 := by
  have h : x ^ 2 - x + 5 = (x - (1 / 2 : ℝ)) ^ 2 + (19 / 4 : ℝ) := by
    ring
  have hpos : 0 < (x - (1 / 2 : ℝ)) ^ 2 + (19 / 4 : ℝ) := by
    have hsq : 0 ≤ (x - (1 / 2 : ℝ)) ^ 2 := by nlinarith
    linarith
  have hpos' : 0 < x ^ 2 - x + 5 := by
    simpa [h] using hpos
  exact ne_of_gt hpos'

/-- The ω-adjoin field has no real embeddings. -/
lemma no_real_embedding_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; ∀ (φ : AdjoinRoot (minpoly ℚ ω) →+* ℂ),
        ¬ NumberField.ComplexEmbedding.IsReal (K := AdjoinRoot (minpoly ℚ ω)) φ := by
  classical
  dsimp
  intro φ hφ
  let φR : AdjoinRoot (minpoly ℚ
    ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) →+* ℝ :=
    NumberField.ComplexEmbedding.IsReal.embedding
      (K := AdjoinRoot (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) hφ
  let φR_alg : AdjoinRoot (minpoly ℚ
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) →ₐ[ℚ] ℝ :=
    { toRingHom := φR
      commutes' := by
        intro q
        simp }
  have hroot :
      Polynomial.aeval
          (φR_alg (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))
          (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) = 0 := by
    exact
      (AdjoinRoot.aeval_algHom_eq_zero
        (f := minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) φR_alg)
  have hmin :
      minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) =
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
    simpa using (minpoly_omega_eq_X2_sub_X_add_5)
  have hroot' :
      Polynomial.aeval
          (φR_alg (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) = 0 := by
    simpa [hmin] using hroot
  have hroot'' :
      (φR (AdjoinRoot.root (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))) ^ 2 -
        (φR (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))) + 5 = 0 := by
    simpa [Polynomial.aeval_def] using hroot'
  exact
    (no_real_root_X2_sub_X_add_5
        (φR (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))) hroot''

/-- The ω-adjoin field is totally complex. -/
lemma isTotallyComplex_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; NumberField.IsTotallyComplex (AdjoinRoot (minpoly ℚ ω)) := by
  classical
  dsimp
  refine ⟨?isComplex⟩
  intro v
  have hv : ¬ NumberField.InfinitePlace.IsReal v := by
    intro hv
    rcases hv with ⟨φ, hφ, rfl⟩
    exact (no_real_embedding_adjoinRoot_minpoly_omega (φ := φ)) hφ
  exact (NumberField.InfinitePlace.not_isReal_iff_isComplex).1 hv

/-- The number of complex places of the ω-adjoin field is `1`. -/
lemma nrComplexPlaces_adjoinRoot_minpoly_omega_eq_one :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; NumberField.InfinitePlace.nrComplexPlaces (AdjoinRoot (minpoly ℚ ω)) = 1 := by
  classical
  dsimp
  have hfinrank :
      Module.finrank ℚ
          (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) = 2 := by
    simpa using (finrank_adjoinRoot_minpoly_omega)
  haveI :
      NumberField.IsTotallyComplex
        (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) :=
    isTotallyComplex_adjoinRoot_minpoly_omega
  have hcomplex :
      Module.finrank ℚ
          (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) =
        2 * NumberField.InfinitePlace.nrComplexPlaces
            (AdjoinRoot (minpoly ℚ
              ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) := by
    simpa using
      (NumberField.IsTotallyComplex.finrank
        (K := AdjoinRoot (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))
  linarith

/-- The mod-2 reduction of the `ℤ`-minpoly of ω is `X^2 + X + 1`. -/
lemma map_minpoly_omega_Z_mod2 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Polynomial.map (Int.castRingHom (ZMod 2)) (minpoly ℤ ω) =
        Polynomial.X ^ 2 + Polynomial.X + (1 : Polynomial (ZMod 2)) := by
  classical
  dsimp
  simpa [minpoly_omega_Z_eq_X2_sub_X_add_5] using map_X2_sub_X_add_5_zmod2

/-- The mod-2 reduction of the `ℤ`-minpoly of ω is irreducible. -/
lemma irreducible_map_minpoly_omega_Z_mod2 :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Irreducible (Polynomial.map (Int.castRingHom (ZMod 2)) (minpoly ℤ ω)) := by
  classical
  dsimp
  simpa [map_minpoly_omega_Z_mod2] using irreducible_X2_add_X_add_one_zmod2

/-- The quadratic integer ω is integral over `ℚ`. -/
lemma isIntegral_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; IsIntegral ℚ ω := by
  classical
  dsimp
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ), ?_, ?_⟩
  ·
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℚ) * Polynomial.X + Polynomial.C (5 : ℚ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℚ)) (b := (5 : ℚ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℚ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic :
        (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℚ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℚ)) (n := 2) hdeg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  ·
    simpa [Polynomial.aeval_def] using (omega_isRoot_X2_sub_X_add_5)

/-- The quadratic integer ω is integral over `ℤ`. -/
lemma isIntegral_omega_Z :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; IsIntegral ℤ ω := by
  classical
  dsimp
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ), ?_, ?_⟩
  ·
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℤ) * Polynomial.X + Polynomial.C (5 : ℤ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℤ)) (b := (5 : ℤ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℤ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic :
        (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℤ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℤ)) (n := 2) hdeg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  ·
    have h :
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
            ((1 + (Real.sqrt 19) * Complex.I) / 2) = -5 := by
      simpa using (omega_sq_sub_omega)
    have h' :
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
            ((1 + (Real.sqrt 19) * Complex.I) / 2) + 5 = 0 := by
      calc
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)^2 -
            ((1 + (Real.sqrt 19) * Complex.I) / 2) + 5 =
            -5 + 5 := by simp [h]
        _ = 0 := by ring
    simpa [Polynomial.aeval_def] using h'

/-- The `ℤ`-adjoin of ω is integral over `ℤ`. -/
lemma isIntegral_adjoin_omega_Z :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Algebra.IsIntegral ℤ (Algebra.adjoin ℤ {ω}) := by
  classical
  dsimp
  refine Algebra.IsIntegral.adjoin ?_
  intro x hx
  have hx' :
      x = ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) := by
    simpa using hx
  simpa [hx'] using (isIntegral_omega_Z)

/-- The minimal polynomial of ω over `ℚ` is irreducible. -/
lemma irreducible_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Irreducible (minpoly ℚ ω) := by
  classical
  dsimp
  have hInt :
      IsIntegral ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) := by
    simpa using (isIntegral_omega)
  exact minpoly.irreducible hInt

/-- Fact instance: the minimal polynomial of ω is irreducible. -/
instance fact_irreducible_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Fact (Irreducible (minpoly ℚ ω)) := by
  classical
  dsimp
  exact ⟨irreducible_minpoly_omega⟩

/-- The adjoined quadratic integer ring embeds into `ℂ`, so it is a domain. -/
lemma isDomain_adjoin_quadratic_integer_19 :
    IsDomain (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  infer_instance

/-- The adjoin ring is finitely generated as a `ℤ`-algebra (by the singleton generator). -/
lemma fg_adjoin_quadratic_integer_19 :
    (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}).FG := by
  simpa using
    (Subalgebra.fg_adjoin_finset (R := ℤ) (A := ℂ)
      ({(1 + (Real.sqrt 19) * Complex.I) / 2} : Finset ℂ))

/-- The adjoin ring is Noetherian since it is a finitely generated `ℤ`-algebra. -/
lemma isNoetherianRing_adjoin_quadratic_integer_19 :
    IsNoetherianRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  classical
  exact isNoetherianRing_of_fg (R := ℤ) (A := ℂ)
    (S := Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})
    fg_adjoin_quadratic_integer_19

/-- Bézout plus Noetherian implies PID for the adjoin ring. -/
lemma isPrincipalIdealRing_of_isBezout_adjoin_quadratic_integer_19
    (hBezout : IsBezout (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})) :
    IsPrincipalIdealRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  classical
  letI : IsNoetherianRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) :=
    isNoetherianRing_adjoin_quadratic_integer_19
  letI : IsBezout (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := hBezout
  infer_instance

/-- Transport `IsPrincipalIdealRing` across a ring equivalence. -/
lemma isPrincipalIdealRing_of_ringEquiv {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (h : IsPrincipalIdealRing R) : IsPrincipalIdealRing S := by
  classical
  letI : IsPrincipalIdealRing R := h
  exact IsPrincipalIdealRing.of_surjective (f := e.toRingHom) e.surjective

/-- A ring equivalence from a PID yields Bézout on the target ring. -/
lemma isBezout_of_ringEquiv_of_isPrincipalIdealRing {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) (h : IsPrincipalIdealRing R) : IsBezout S := by
  classical
  have hS : IsPrincipalIdealRing S := isPrincipalIdealRing_of_ringEquiv e h
  letI : IsPrincipalIdealRing S := hS
  infer_instance

/-- Reduce Bézout for the adjoin ring to existence of a PID ring equivalence. -/
lemma isBezout_adjoin_quadratic_integer_19_of_exists_pid_equiv
    (h : ∃ (R : Type) (inst : CommRing R),
      (letI : CommRing R := inst
       IsPrincipalIdealRing R ∧
        Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})))) :
    IsBezout (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  classical
  rcases h with ⟨R, instR, hPID⟩
  letI : CommRing R := instR
  rcases hPID with ⟨hPID, ⟨e⟩⟩
  exact isBezout_of_ringEquiv_of_isPrincipalIdealRing e hPID

/-- If there exists a PID ring equivalent to the adjoin ring, then the adjoin ring is a PID. -/
lemma isPrincipalIdealRing_adjoin_quadratic_integer_19_of_exists_pid_equiv
    (h : ∃ (R : Type) (inst : CommRing R),
      (letI : CommRing R := inst
       IsPrincipalIdealRing R ∧
        Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})))) :
    IsPrincipalIdealRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  classical
  rcases h with ⟨R, instR, hPID⟩
  letI : CommRing R := instR
  rcases hPID with ⟨hPID, ⟨e⟩⟩
  exact isPrincipalIdealRing_of_ringEquiv e hPID

/-- Reduce existence of a PID ring equivalent to the adjoin ring to a ring-of-integers witness. -/
lemma exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_ringOfIntegers
    (h :
      ∃ (K : Type) (instK : Field K) (instNF : NumberField K),
        (letI : Field K := instK
         letI : NumberField K := instNF
         IsPrincipalIdealRing (𝓞 K) ∧
          Nonempty ((𝓞 K) ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})))) :
    ∃ (R : Type) (inst : CommRing R),
      (letI : CommRing R := inst
       IsPrincipalIdealRing R ∧
        Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
  classical
  rcases h with ⟨K, instK, instNF, hPID⟩
  letI : Field K := instK
  letI : NumberField K := instNF
  rcases hPID with ⟨hPID, ⟨e⟩⟩
  refine ⟨(𝓞 K), inferInstance, ?_⟩
  dsimp
  refine ⟨hPID, ?_⟩
  exact ⟨e⟩

/-- Algebra equivalence between `ℚ(ω)` and `AdjoinRoot (minpoly ℚ ω)`. -/
lemma fieldEquiv_adjoinQ_omega_adjoinRoot_minpoly :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Nonempty
        ((Algebra.adjoin ℚ ({ω} : Set ℂ)) ≃ₐ[ℚ] AdjoinRoot (minpoly ℚ ω)) := by
  classical
  dsimp
  refine ⟨AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly ℚ
    ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)⟩

/-- Algebra structure from `ℤ[ω]` to the adjoin-root field. -/
noncomputable instance algebra_adjoinZ_omega_to_adjoinRoot_minpoly :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Algebra (Algebra.adjoin ℤ {ω}) (AdjoinRoot (minpoly ℚ ω)) := by
  classical
  dsimp
  let L : Subalgebra ℚ ℂ :=
    Algebra.adjoin ℚ ({((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)} : Set ℂ)
  have hle :
      Algebra.adjoin ℤ ({((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)} : Set ℂ) ≤
        (L.restrictScalars ℤ) := by
    refine Algebra.adjoin_le ?_
    intro x hx
    have hx' :
        (x : ℂ) ∈ L := by
      simpa [L] using
        (Algebra.subset_adjoin (R := ℚ) (A := ℂ)
          (s := ({((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)} : Set ℂ)) hx)
    simpa using hx'
  let f :
      Algebra.adjoin ℤ ({((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)} : Set ℂ) →ₐ[ℤ] L :=
    Subalgebra.inclusion hle
  let e :
      L ≃ₐ[ℚ]
        AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) :=
    AlgEquiv.adjoinSingletonEquivAdjoinRootMinpoly ℚ
      ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)
  let e' :
      L ≃ₐ[ℤ]
        AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) :=
    e.restrictScalars ℤ
  exact (e'.toAlgHom.comp f).toRingHom.toAlgebra

/-- The ω-field is a quadratic extension of `ℚ`. -/
instance isQuadraticExtension_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Algebra.IsQuadraticExtension ℚ (AdjoinRoot (minpoly ℚ ω)) := by
  classical
  dsimp
  refine { toFree := (by infer_instance), finrank_eq_two' := ?_ }
  simpa using (finrank_adjoinRoot_minpoly_omega)

/-- The adjoin-root field is generated by its root over `ℚ`. -/
lemma adjoinRoot_minpoly_omega_eq_top :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Algebra.adjoin ℚ
        ({AdjoinRoot.root (minpoly ℚ ω)} :
          Set (AdjoinRoot (minpoly ℚ ω))) = ⊤ := by
  classical
  dsimp
  simpa using
    (AdjoinRoot.adjoinRoot_eq_top
      (f := minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))

/-- The `AdjoinRoot` generator is integral over `ℤ`, since it satisfies `X^2 - X + 5`. -/
lemma isIntegral_adjoinRoot_root_Z :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; IsIntegral ℤ (AdjoinRoot.root (minpoly ℚ ω)) := by
  classical
  dsimp
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ), ?_, ?_⟩
  ·
    have hdeg' :
        Polynomial.degree (Polynomial.C (-1 : ℤ) * Polynomial.X + Polynomial.C (5 : ℤ)) <
          (2 : ℕ) := by
      simpa using (Polynomial.degree_linear_lt (a := (-1 : ℤ)) (b := (5 : ℤ)))
    have hdeg : Polynomial.degree (-Polynomial.X + (5 : Polynomial ℤ)) < (2 : ℕ) := by
      simpa [sub_eq_add_neg, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hdeg'
    have hmonic :
        (Polynomial.X ^ 2 + (-Polynomial.X + (5 : Polynomial ℤ))).Monic :=
      Polynomial.monic_X_pow_add (p := -Polynomial.X + (5 : Polynomial ℤ)) (n := 2) hdeg
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmonic
  ·
    have hminpoly :
        minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ) =
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
      simpa using (minpoly_omega_eq_X2_sub_X_add_5)
    have hrootQ :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) = 0 := by
      simp [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have hrootQ' :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) = 0 := by
      simpa [hminpoly] using hrootQ
    have hmap :
        Polynomial.map (algebraMap ℤ ℚ)
          (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) =
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
      simp
    have hrootQ'' :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.map (algebraMap ℤ ℚ)
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ))) = 0 := by
      simpa [hmap] using hrootQ'
    have hmap_aeval :
        Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
          (Polynomial.map (algebraMap ℤ ℚ)
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ))) =
          Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
            (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) := by
      exact Polynomial.aeval_map_algebraMap (A := ℚ)
        (x := AdjoinRoot.root (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
        (p := (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)))
    calc
      Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
        ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
        (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ)) =
          Polynomial.aeval (AdjoinRoot.root (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))
            (Polynomial.map (algebraMap ℤ ℚ)
              (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℤ))) := by
        symm
        exact hmap_aeval
      _ = 0 := hrootQ''

/-- The `ℤ`-adjoin of the `AdjoinRoot` generator is integral over `ℤ`. -/
lemma isIntegral_adjoinRoot_root_adjoin_Z :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Algebra.IsIntegral ℤ
        (Algebra.adjoin ℤ
          ({AdjoinRoot.root (minpoly ℚ ω)} :
            Set (AdjoinRoot (minpoly ℚ ω)))) := by
  classical
  dsimp
  refine Algebra.IsIntegral.adjoin ?_
  intro x hx
  have hx' :
      x = AdjoinRoot.root (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)) := by
    simpa using hx
  simpa [hx'] using (isIntegral_adjoinRoot_root_Z)

/-- Minkowski criterion plus integral-closure input for the ω-field. -/
lemma classNumber_and_ringEquiv_adjoinRoot_minpoly_omega_of_arith
    (hPrime :
      let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
      ; ∀ p ∈ Finset.Icc 1 ⌊(M (AdjoinRoot (minpoly ℚ ω)))⌋₊, p.Prime →
          ∀ (P : Ideal (𝓞 (AdjoinRoot (minpoly ℚ ω)))),
            P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (AdjoinRoot (minpoly ℚ ω))) →
              p ^ ((Ideal.span ({↑p} : Set ℤ)).inertiaDeg P) ≤
                ⌊(M (AdjoinRoot (minpoly ℚ ω)))⌋₊ →
              Submodule.IsPrincipal P)
    (hIC :
      let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
      ; IsIntegralClosure (Algebra.adjoin ℤ {ω}) ℤ (AdjoinRoot (minpoly ℚ ω))) :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; NumberField.classNumber (AdjoinRoot (minpoly ℚ ω)) = 1 ∧
        Nonempty
          ((𝓞 (AdjoinRoot (minpoly ℚ ω))) ≃+* (Algebra.adjoin ℤ {ω})) := by
  classical
  dsimp at hPrime hIC ⊢
  set ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
  have hPrime' :
      ∀ p ∈ Finset.Icc 1 ⌊(M (AdjoinRoot (minpoly ℚ ω)))⌋₊, p.Prime →
        ∀ (P : Ideal (𝓞 (AdjoinRoot (minpoly ℚ ω)))),
          P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 (AdjoinRoot (minpoly ℚ ω))) →
            p ^ ((Ideal.span ({↑p} : Set ℤ)).inertiaDeg P) ≤
              ⌊(M (AdjoinRoot (minpoly ℚ ω)))⌋₊ →
            Submodule.IsPrincipal P := by
    simpa [ω] using hPrime
  have hIC' :
      IsIntegralClosure (Algebra.adjoin ℤ {ω}) ℤ (AdjoinRoot (minpoly ℚ ω)) := by
    simpa [ω] using hIC
  let K := AdjoinRoot (minpoly ℚ ω)
  have hPID : IsPrincipalIdealRing (𝓞 K) := by
    exact
      RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
        (K := K) hPrime'
  have hclass : NumberField.classNumber K = 1 :=
    (NumberField.classNumber_eq_one_iff (K := K)).2 hPID
  haveI : IsIntegralClosure (Algebra.adjoin ℤ {ω}) ℤ K := hIC'
  have hEquiv : (𝓞 K) ≃+* (Algebra.adjoin ℤ {ω}) :=
    NumberField.RingOfIntegers.equiv (K := K) (Algebra.adjoin ℤ {ω})
  simpa [K, ω] using ⟨hclass, ⟨hEquiv⟩⟩

/-- If the Minkowski bound floors to `2` and every prime over `2` has inertia degree `2`,
then the Minkowski prime condition is vacuous. -/
lemma minkowski_principal_ideals_of_floor_eq_two_of_inertiaDeg_two
    (K : Type*) [Field K] [NumberField K]
    (hfloor : ⌊(M K)⌋₊ = 2)
    (hinertia :
      ∀ P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K),
        (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P = 2) :
    ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime →
      ∀ (P : Ideal (𝓞 K)),
        P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) →
          p ^ ((Ideal.span ({↑p} : Set ℤ)).inertiaDeg P) ≤ ⌊(M K)⌋₊ →
          Submodule.IsPrincipal P := by
  classical
  intro p hp hprime P hP hpow
  have hp_le : p ≤ 2 := by
    have hp' := (Finset.mem_Icc.mp hp).2
    simpa [hfloor] using hp'
  have hp_ge : 2 ≤ p := by
    exact Nat.Prime.two_le hprime
  have hp_eq : p = 2 := le_antisymm hp_le hp_ge
  have hP2 :
      P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K) := by
    simpa [hp_eq] using hP
  have hdeg :
      (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P = 2 :=
    hinertia P hP2
  have hpow' :
      (2 : ℕ) ^ ((Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P) ≤ 2 := by
    simp [hp_eq, hfloor] at hpow
    exact hpow
  have hpow'' : (4 : ℕ) ≤ 2 := by
    simpa [hdeg] using hpow'
  exact (False.elim ((by decide : ¬ ((4 : ℕ) ≤ 2)) hpow''))

/-- Combined arithmetic input: class number one and ring equivalence for the ω-field. -/
lemma classNumber_and_ringEquiv_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; NumberField.classNumber (AdjoinRoot (minpoly ℚ ω)) = 1 ∧
        Nonempty
          ((𝓞 (AdjoinRoot (minpoly ℚ ω))) ≃+* (Algebra.adjoin ℤ {ω})) := by
  classical
  dsimp
  have hfinrank :
      Module.finrank ℚ
          (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) = 2 := by
    simpa using (finrank_adjoinRoot_minpoly_omega)
  have harith :
      (∀ p ∈ Finset.Icc 1 ⌊(M (AdjoinRoot (minpoly ℚ
          ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))⌋₊, p.Prime →
        ∀ (P :
          Ideal (𝓞 (AdjoinRoot (minpoly ℚ
            ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))),
          P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)})
            (𝓞 (AdjoinRoot (minpoly ℚ
              ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))) →
            p ^ ((Ideal.span ({↑p} : Set ℤ)).inertiaDeg P) ≤
              ⌊(M (AdjoinRoot (minpoly ℚ
                ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))))⌋₊ →
            Submodule.IsPrincipal P) ∧
      IsIntegralClosure (Algebra.adjoin ℤ {((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)}) ℤ
        (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) := by
    let K :=
      AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))
    have harith_inputs :
        (⌊(M K)⌋₊ = 2 ∧
          (∀ P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K),
            (Ideal.span ({(2 : ℤ)} : Set ℤ)).inertiaDeg P = 2)) ∧
        IsIntegralClosure (Algebra.adjoin ℤ {((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)}) ℤ K := by
      sorry
    have hPrime :
        ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime →
          ∀ (P : Ideal (𝓞 K)),
            P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) →
              p ^ ((Ideal.span ({↑p} : Set ℤ)).inertiaDeg P) ≤ ⌊(M K)⌋₊ →
              Submodule.IsPrincipal P := by
      classical
      exact
        minkowski_principal_ideals_of_floor_eq_two_of_inertiaDeg_two
          (K := K) harith_inputs.1.1 harith_inputs.1.2
    have hIC :
        IsIntegralClosure (Algebra.adjoin ℤ {((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)}) ℤ K :=
      harith_inputs.2
    refine ⟨?_, ?_⟩
    · simpa [K] using hPrime
    · simpa [K] using hIC
  rcases harith with ⟨hPrime, hIC⟩
  exact
    classNumber_and_ringEquiv_adjoinRoot_minpoly_omega_of_arith
      (hPrime := hPrime) (hIC := hIC)

/-- Class number one for the quadratic field `AdjoinRoot (minpoly ℚ ω)` (arithmetic input). -/
lemma classNumber_adjoinRoot_minpoly_omega_eq_one :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; NumberField.classNumber (AdjoinRoot (minpoly ℚ ω)) = 1 := by
  classical
  simpa using (classNumber_and_ringEquiv_adjoinRoot_minpoly_omega).1

/-- PID of the ring of integers, deduced from class number one. -/
lemma pid_ringOfIntegers_adjoinRoot_minpoly_omega_aux :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; IsPrincipalIdealRing (𝓞 (AdjoinRoot (minpoly ℚ ω))) := by
  classical
  dsimp
  have hclass :
      NumberField.classNumber
          (AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ))) = 1 := by
    simpa using (classNumber_adjoinRoot_minpoly_omega_eq_one)
  exact (NumberField.classNumber_eq_one_iff
    (K := AdjoinRoot (minpoly ℚ ((1 + (Real.sqrt 19) * Complex.I) / 2 : ℂ)))).1 hclass

/-- Ring of integers equivalence with `ℤ[ω]` (arithmetic input). -/
lemma ringEquiv_ringOfIntegers_adjoinRoot_minpoly_omega_to_adjoin_aux :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Nonempty
        ((𝓞 (AdjoinRoot (minpoly ℚ ω))) ≃+* (Algebra.adjoin ℤ {ω})) := by
  classical
  simpa using (classNumber_and_ringEquiv_adjoinRoot_minpoly_omega).2

/-- Arithmetic input for the field defined by the minimal polynomial of ω. -/
lemma pid_and_ringEquiv_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; IsPrincipalIdealRing (𝓞 (AdjoinRoot (minpoly ℚ ω))) ∧
        Nonempty
          ((𝓞 (AdjoinRoot (minpoly ℚ ω))) ≃+* (Algebra.adjoin ℤ {ω})) := by
  classical
  dsimp
  refine ⟨?hPID, ?hEquiv⟩
  · simpa using (pid_ringOfIntegers_adjoinRoot_minpoly_omega_aux)
  · simpa using (ringEquiv_ringOfIntegers_adjoinRoot_minpoly_omega_to_adjoin_aux)

/-- PID for the ring of integers of `AdjoinRoot (minpoly ℚ ω)` (arithmetic input). -/
lemma pid_ringOfIntegers_adjoinRoot_minpoly_omega :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; IsPrincipalIdealRing (𝓞 (AdjoinRoot (minpoly ℚ ω))) := by
  classical
  simpa using (pid_and_ringEquiv_adjoinRoot_minpoly_omega).1

/-- Ring equivalence between the ring of integers and `ℤ[ω]` (arithmetic input). -/
lemma ringEquiv_ringOfIntegers_adjoinRoot_minpoly_omega_to_adjoin :
    let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
    ; Nonempty
        ((𝓞 (AdjoinRoot (minpoly ℚ ω))) ≃+* (Algebra.adjoin ℤ {ω})) := by
  classical
  simpa using (pid_and_ringEquiv_adjoinRoot_minpoly_omega).2

/-- Arithmetic input for the field `ℚ(√-19)` presented as an adjoin root. -/
lemma pid_and_ringEquiv_adjoinRoot_X2_sub_X_add_5
    [Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)))] :
    IsPrincipalIdealRing
        (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)))) ∧
      Nonempty
        ((𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)))) ≃+*
          (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})) := by
  classical
  let ω : ℂ := (1 + (Real.sqrt 19) * Complex.I) / 2
  let A : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {ω}
  have hmin : minpoly ℚ ω = (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) := by
    simpa [ω] using (minpoly_omega_eq_X2_sub_X_add_5)
  have hpid :
      IsPrincipalIdealRing (𝓞 (AdjoinRoot (minpoly ℚ ω))) ∧
        Nonempty ((𝓞 (AdjoinRoot (minpoly ℚ ω))) ≃+* A) := by
    simpa [ω, A] using (pid_and_ringEquiv_adjoinRoot_minpoly_omega)
  let e :
      AdjoinRoot (minpoly ℚ ω) ≃ₐ[ℚ]
        AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) :=
    AdjoinRoot.algEquivOfEq ℚ (minpoly ℚ ω)
      (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)) hmin
  let eO :
      𝓞 (AdjoinRoot (minpoly ℚ ω)) ≃ₐ[𝓞 ℚ]
        𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ))) :=
    NumberField.RingOfIntegers.mapAlgEquiv e
  have hPID :
      IsPrincipalIdealRing
          (𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)))) :=
    isPrincipalIdealRing_of_ringEquiv eO.toRingEquiv hpid.1
  rcases hpid.2 with ⟨r⟩
  have hEquiv :
      Nonempty
          ((𝓞 (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ)))) ≃+* A) := by
    exact ⟨eO.toRingEquiv.symm.trans r⟩
  exact ⟨hPID, hEquiv⟩

/-- Arithmetic input: a PID ring of integers equivalent to the adjoin ring. -/
lemma exists_pid_ringEquiv_adjoin_quadratic_integer_19_via_ringOfIntegers :
    ∃ (K : Type) (instK : Field K) (instNF : NumberField K),
      (letI : Field K := instK
       letI : NumberField K := instNF
       IsPrincipalIdealRing (𝓞 K) ∧
        Nonempty ((𝓞 K) ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
  classical
  have _ :
      Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ))) :=
    ⟨irreducible_X2_sub_X_add_5⟩
  let K := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.X + (5 : Polynomial ℚ))
  have hK :
      IsPrincipalIdealRing (𝓞 K) ∧
        Nonempty ((𝓞 K) ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})) := by
    simpa [K] using (pid_and_ringEquiv_adjoinRoot_X2_sub_X_add_5)
  refine ⟨K, inferInstance, inferInstance, ?_⟩
  dsimp
  exact hK

/-- The adjoin ring is a PID (arithmetic input to be supplied). -/
lemma isPrincipalIdealRing_adjoin_quadratic_integer_19 :
    IsPrincipalIdealRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  classical
  have h :
      ∃ (R : Type) (inst : CommRing R),
        (letI : CommRing R := inst
         IsPrincipalIdealRing R ∧
          Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
    exact
      exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_ringOfIntegers
        exists_pid_ringEquiv_adjoin_quadratic_integer_19_via_ringOfIntegers
  exact isPrincipalIdealRing_adjoin_quadratic_integer_19_of_exists_pid_equiv h

/-- If the adjoin ring is a PID, it is ring-equivalent to a PID (itself). -/
lemma exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_pid
    (hPID : IsPrincipalIdealRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})) :
    ∃ (R : Type) (inst : CommRing R),
      (letI : CommRing R := inst
       IsPrincipalIdealRing R ∧
        Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
  refine ⟨(Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2} : Type), inferInstance, ?_⟩
  dsimp
  refine ⟨hPID, ?_⟩
  exact ⟨RingEquiv.refl _⟩

/-- The adjoin ring is Bézout (arithmetic input to be supplied). -/
lemma isBezout_adjoin_quadratic_integer_19 :
    IsBezout (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  classical
  have h :
      ∃ (R : Type) (inst : CommRing R),
        (letI : CommRing R := inst
         IsPrincipalIdealRing R ∧
          Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
    exact
      exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_pid
        isPrincipalIdealRing_adjoin_quadratic_integer_19
  exact isBezout_adjoin_quadratic_integer_19_of_exists_pid_equiv h

/-- Bézout implies the PID existence statement for the adjoin ring. -/
lemma exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_isBezout
    (hBezout : IsBezout (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2})) :
    ∃ (R : Type) (inst : CommRing R),
      (letI : CommRing R := inst
       IsPrincipalIdealRing R ∧
        Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
  have hPID :
      IsPrincipalIdealRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) :=
    isPrincipalIdealRing_of_isBezout_adjoin_quadratic_integer_19 hBezout
  exact exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_pid hPID

/-- Existence of a PID ring equivalent to the adjoin ring. -/
lemma exists_pid_ringEquiv_adjoin_quadratic_integer_19 :
    ∃ (R : Type) (inst : CommRing R),
      (letI : CommRing R := inst
       IsPrincipalIdealRing R ∧
        Nonempty (R ≃+* (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}))) := by
  exact
    exists_pid_ringEquiv_adjoin_quadratic_integer_19_of_isBezout
      isBezout_adjoin_quadratic_integer_19

/--
Prove that the ring $\mathbb{Z}[\frac{1+\sqrt{-19}}{2}]$ is a principal ideal domain.
-/
theorem isPrincipalIdealRing_of_quadratic_integer_19 :
    IsPrincipalIdealRing (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) ∧ IsDomain (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) := by
  constructor
  ·
    have hBezout :
        IsBezout (Algebra.adjoin ℤ {(1 + (Real.sqrt 19) * Complex.I) / 2}) :=
      isBezout_adjoin_quadratic_integer_19_of_exists_pid_equiv
        exists_pid_ringEquiv_adjoin_quadratic_integer_19
    exact isPrincipalIdealRing_of_isBezout_adjoin_quadratic_integer_19 hBezout
  · exact isDomain_adjoin_quadratic_integer_19

import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace
set_option linter.style.longLine false

class OriginalProblem where
  n_var : ℕ
  constraints : (Fin n_var → ℝ) → Prop
  objective : (Fin n_var → ℝ) → ℝ

class OptProblem extends OriginalProblem where
  n_eqs : ℕ
  eq_constraints : (Fin n_var → ℝ) → (Fin n_eqs → ℝ)
  n_ieqs : ℕ
  ieq_constraints : (Fin n_var → ℝ) → (Fin n_ieqs → ℝ)
  constraints := fun x => eq_constraints x = 0 ∧ ieq_constraints x ≤ 0
  h_constraints : constraints =  fun x => eq_constraints x = 0 ∧ ieq_constraints x ≤ 0 := by simp

class LP extends OptProblem where
  c : Fin n_var → ℝ
  A_eq : Matrix (Fin n_eqs) (Fin n_var) ℝ
  b_eq : Fin n_eqs → ℝ
  A_ieq : Matrix (Fin n_ieqs) (Fin n_var) ℝ
  b_ieq : Fin n_ieqs → ℝ
  objective := fun x => c ⬝ᵥ x
  eq_constraints := fun x => A_eq *ᵥ x - b_eq
  ieq_constraints := fun x => A_ieq *ᵥ x - b_ieq
  h_objective : objective = fun x => c ⬝ᵥ x := by simp
  h_eq : eq_constraints = fun x => A_eq *ᵥ x - b_eq := by simp
  h_ieq : ieq_constraints = fun x => A_ieq *ᵥ x - b_ieq := by simp

class SDP extends OriginalProblem where
  c : Fin n_var → ℝ
  n_eqs : ℕ
  A_eq : Matrix (Fin n_eqs) (Fin n_var) ℝ
  b_eq : Fin n_eqs → ℝ
  eq_constraints := fun x => A_eq *ᵥ x - b_eq
  n_ieqs : ℕ
  A_sd : Fin n_var → Matrix (Fin n_ieqs) (Fin n_ieqs) ℝ
  B_sd : Matrix (Fin n_ieqs) (Fin n_ieqs) ℝ
  ieq_constraints := fun x => ∑ i, x i • A_sd i + B_sd
  constraints := fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef
  h_constraints : constraints =  fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef := by
simp
  objective := fun x => c ⬝ᵥ x
  h_objective : objective = fun x => c ⬝ᵥ x := by simp

def subequivlance (p q : OriginalProblem) : Prop :=
  ∀ (x : Fin p.n_var → ℝ), (p.constraints x) →
  ∃ (y : Fin q.n_var → ℝ), (q.constraints y) ∧
  q.objective y = p.objective x

def equivalence (p q : OriginalProblem) : Prop :=
  subequivlance p q ∧ subequivlance q p

class DualProblem (p : OptProblem) where
  dual_objective : (Fin p.n_eqs → ℝ) → (Fin p.n_ieqs → ℝ) → EReal
  dual_domain : Set ((Fin p.n_eqs → ℝ) × (Fin p.n_ieqs → ℝ))
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ), ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by
simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp


/-Consider the function $f(x) = x_1^2 + x_2^2$, and the sequence of iterates $x^k = (1+ \frac{1}{2^k}) (\cos k, \sin k)^T$, determine whether the sequence ${ x^{k+1}}$ converges or
not.

-/
noncomputable section

def answer : Bool := false

/-- Sine at `1/2` is positive. -/
lemma num_49_S_E_sin_half_pos : 0 < Real.sin (1 / 2 : ℝ) := by
  have h0 : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
  have h1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  simpa using (Real.sin_pos_of_pos_of_le_one h0 h1)

/-- At least one of `|sin t|` or `|cos t|` is at least `1/2`. -/
lemma num_49_S_E_one_half_le_max_abs_sin_cos (t : ℝ) :
    (1 / 2 : ℝ) ≤ max |Real.sin t| |Real.cos t| := by
  by_contra h
  have hmax : max |Real.sin t| |Real.cos t| < (1 / 2 : ℝ) := lt_of_not_ge h
  have hsin : |Real.sin t| < (1 / 2 : ℝ) := lt_of_le_of_lt (le_max_left _ _) hmax
  have hcos : |Real.cos t| < (1 / 2 : ℝ) := lt_of_le_of_lt (le_max_right _ _) hmax
  have hsin2 : (|Real.sin t|) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    have : (Real.sin t) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      have : |Real.sin t| < |(1 / 2 : ℝ)| := by simpa using hsin
      exact (sq_lt_sq.2 this)
    simpa [sq_abs] using this
  have hcos2 : (|Real.cos t|) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    have : (Real.cos t) ^ 2 < (1 / 2 : ℝ) ^ 2 := by
      have : |Real.cos t| < |(1 / 2 : ℝ)| := by simpa using hcos
      exact (sq_lt_sq.2 this)
    simpa [sq_abs] using this
  have hsq : (|Real.sin t|) ^ 2 + (|Real.cos t|) ^ 2 = (1 : ℝ) := by
    simpa [sq_abs] using (Real.sin_sq_add_cos_sq t)
  nlinarith [hsin2, hcos2, hsq]

/-- Lower bound on the norm of the unit-circle step. -/
lemma num_49_S_E_unit_step_lower_bound (k : ℕ) :
    Real.sin (1 / 2 : ℝ) ≤
      ‖![Real.cos (k + 1), Real.sin (k + 1)] - ![Real.cos k, Real.sin k]‖ := by
  let t : ℝ := ((k + 1 : ℝ) + k) / 2
  have hcos : Real.cos (k + 1) - Real.cos k = -2 * Real.sin t * Real.sin (1 / 2 : ℝ) := by
    simpa [t] using (Real.cos_sub_cos (x := (k + 1 : ℝ)) (y := (k : ℝ)))
  have hsin : Real.sin (k + 1) - Real.sin k = 2 * Real.sin (1 / 2 : ℝ) * Real.cos t := by
    have h := Real.sin_sub_sin (x := (k + 1 : ℝ)) (y := (k : ℝ))
    simpa [t, mul_comm, mul_left_comm, mul_assoc] using h
  have hcos_abs :
      |Real.cos (k + 1) - Real.cos k| = 2 * |Real.sin t| * |Real.sin (1 / 2 : ℝ)| := by
    calc
      |Real.cos (k + 1) - Real.cos k|
          = |(-2) * Real.sin t * Real.sin (1 / 2 : ℝ)| := by simpa [hcos]
      _ = |(2 : ℝ)| * |Real.sin t| * |Real.sin (1 / 2 : ℝ)| := by
        simp [abs_mul, mul_assoc]
      _ = 2 * |Real.sin t| * |Real.sin (1 / 2 : ℝ)| := by simp
  have hsin_abs :
      |Real.sin (k + 1) - Real.sin k| = 2 * |Real.sin (1 / 2 : ℝ)| * |Real.cos t| := by
    calc
      |Real.sin (k + 1) - Real.sin k|
          = |2 * Real.sin (1 / 2 : ℝ) * Real.cos t| := by simpa [hsin]
      _ = |(2 : ℝ)| * |Real.sin (1 / 2 : ℝ)| * |Real.cos t| := by
        simp [abs_mul, mul_assoc]
      _ = 2 * |Real.sin (1 / 2 : ℝ)| * |Real.cos t| := by simp
  have hcase : (1 / 2 : ℝ) ≤ |Real.sin t| ∨ (1 / 2 : ℝ) ≤ |Real.cos t| := by
    simpa [le_max_iff] using (num_49_S_E_one_half_le_max_abs_sin_cos t)
  let d : Fin 2 → ℝ := ![Real.cos (k + 1) - Real.cos k, Real.sin (k + 1) - Real.sin k]
  have hd :
      ![Real.cos (k + 1), Real.sin (k + 1)] - ![Real.cos k, Real.sin k] = d := by
    funext i; fin_cases i <;> simp [d]
  have hnorm0 : |Real.cos (k + 1) - Real.cos k| ≤ ‖d‖ := by
    simpa [d] using (norm_le_pi_norm d (0 : Fin 2))
  have hnorm1 : |Real.sin (k + 1) - Real.sin k| ≤ ‖d‖ := by
    simpa [d] using (norm_le_pi_norm d (1 : Fin 2))
  have habs : |Real.sin (1 / 2 : ℝ)| ≤ ‖d‖ := by
    cases hcase with
    | inl hsin_ge =>
        have h1 : (1 : ℝ) ≤ 2 * |Real.sin t| := by nlinarith [hsin_ge]
        have hpos : 0 ≤ |Real.sin (1 / 2 : ℝ)| := abs_nonneg _
        have hmul : |Real.sin (1 / 2 : ℝ)| ≤ 2 * |Real.sin t| * |Real.sin (1 / 2 : ℝ)| := by
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right h1 hpos)
        have hcos_le : |Real.sin (1 / 2 : ℝ)| ≤ |Real.cos (k + 1) - Real.cos k| := by
          simpa [hcos_abs, mul_assoc, mul_left_comm, mul_comm] using hmul
        exact le_trans hcos_le hnorm0
    | inr hcos_ge =>
        have h1 : (1 : ℝ) ≤ 2 * |Real.cos t| := by nlinarith [hcos_ge]
        have hpos : 0 ≤ |Real.sin (1 / 2 : ℝ)| := abs_nonneg _
        have hmul : |Real.sin (1 / 2 : ℝ)| ≤ 2 * |Real.cos t| * |Real.sin (1 / 2 : ℝ)| := by
          simpa [mul_assoc] using (mul_le_mul_of_nonneg_right h1 hpos)
        have hsin_le : |Real.sin (1 / 2 : ℝ)| ≤ |Real.sin (k + 1) - Real.sin k| := by
          simpa [hsin_abs, mul_assoc, mul_left_comm, mul_comm] using hmul
        exact le_trans hsin_le hnorm1
  have hpos : 0 < Real.sin (1 / 2 : ℝ) := num_49_S_E_sin_half_pos
  have habs' : Real.sin (1 / 2 : ℝ) ≤ ‖d‖ := by
    calc
      Real.sin (1 / 2 : ℝ) = |Real.sin (1 / 2 : ℝ)| := by
        symm; exact abs_of_pos hpos
      _ ≤ ‖d‖ := habs
  simpa [hd] using habs'

/-- The scaled unit-circle vector has norm bounded by the scale. -/
lemma num_49_S_E_scale_norm_le (n : ℕ) :
    ‖(1 / 2 ^ n : Fin 2 → ℝ) * ![Real.cos n, Real.sin n]‖ ≤ (1 / (2 : ℝ) ^ n) := by
  have hpos : 0 ≤ (1 / (2 : ℝ) ^ n) := by positivity
  refine
    (pi_norm_le_iff_of_nonneg
          (x := (1 / 2 ^ n : Fin 2 → ℝ) * ![Real.cos n, Real.sin n])
          (r := (1 / (2 : ℝ) ^ n)) hpos).2 ?_
  intro i
  fin_cases i <;>
    simp [Real.abs_cos_le_one, Real.abs_sin_le_one, hpos, mul_le_mul_of_nonneg_left, mul_comm,
      mul_left_comm, mul_assoc]

/-- Lower bound for the scaled step size. -/
lemma num_49_S_E_scaled_step_lower_bound (k : ℕ) :
    (Real.sin (1 / 2 : ℝ) - (2 / (2 : ℝ) ^ k)) ≤
      ‖(1 + (1 / 2 ^ (k + 1)) : Fin 2 → ℝ) * ![Real.cos (k + 1), Real.sin (k + 1)]
        - (1 + (1 / 2 ^ k) : Fin 2 → ℝ) * ![Real.cos k, Real.sin k]‖ := by
  let v (n : ℕ) : Fin 2 → ℝ := fun i => if i = 0 then Real.cos n else Real.sin n
  have hv (n : ℕ) : v n = ![Real.cos n, Real.sin n] := by
    funext i; fin_cases i <;> simp [v]
  let a : Fin 2 → ℝ := v (k + 1) - v k
  let b : Fin 2 → ℝ := (1 / 2 ^ (k + 1) : Fin 2 → ℝ) * v (k + 1) - (1 / 2 ^ k : Fin 2 → ℝ) * v k
  have hdecomp :
      (1 + (1 / 2 ^ (k + 1)) : Fin 2 → ℝ) * v (k + 1) - (1 + (1 / 2 ^ k) : Fin 2 → ℝ) * v k =
        a + b := by
    funext i
    fin_cases i <;>
      simp [v, a, b, mul_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc]
  have hdecomp' :
      a + b =
        (1 + (1 / 2 ^ (k + 1)) : Fin 2 → ℝ) * v (k + 1) - (1 + (1 / 2 ^ k) : Fin 2 → ℝ) * v k := by
    simpa using hdecomp.symm
  have ha : Real.sin (1 / 2 : ℝ) ≤ ‖a‖ := by
    simpa [a, hv] using (num_49_S_E_unit_step_lower_bound k)
  have hb1 : ‖(1 / 2 ^ (k + 1) : Fin 2 → ℝ) * v (k + 1)‖ ≤ (1 / (2 : ℝ) ^ (k + 1)) := by
    simpa [hv] using (num_49_S_E_scale_norm_le (k + 1))
  have hb2 : ‖(1 / 2 ^ k : Fin 2 → ℝ) * v k‖ ≤ (1 / (2 : ℝ) ^ k) := by
    simpa [hv] using (num_49_S_E_scale_norm_le k)
  have hb' :
      ‖b‖ ≤
        ‖(1 / 2 ^ (k + 1) : Fin 2 → ℝ) * v (k + 1)‖ +
          ‖(1 / 2 ^ k : Fin 2 → ℝ) * v k‖ := by
    simpa [b] using
      (norm_sub_le ((1 / 2 ^ (k + 1) : Fin 2 → ℝ) * v (k + 1)) ((1 / 2 ^ k : Fin 2 → ℝ) * v k))
  have hb'' : ‖b‖ ≤ (1 / (2 : ℝ) ^ (k + 1)) + (1 / (2 : ℝ) ^ k) := by
    exact le_trans hb' (add_le_add hb1 hb2)
  have hmono : (1 / (2 : ℝ) ^ (k + 1)) ≤ (1 / (2 : ℝ) ^ k) := by
    have hpos : 0 < (2 : ℝ) ^ k := by positivity
    have hle : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k * 2 := by
      have h2 : (1 : ℝ) ≤ 2 := by norm_num
      have hnonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_left h2 hnonneg
      simpa using hmul
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using (one_div_le_one_div_of_le hpos hle)
  have hb : ‖b‖ ≤ 2 / (2 : ℝ) ^ k := by
    have hsum : (1 / (2 : ℝ) ^ (k + 1)) + (1 / (2 : ℝ) ^ k) ≤ 2 / (2 : ℝ) ^ k := by
      calc
        (1 / (2 : ℝ) ^ (k + 1)) + (1 / (2 : ℝ) ^ k)
            ≤ (1 / (2 : ℝ) ^ k) + (1 / (2 : ℝ) ^ k) := by gcongr
        _ = 2 / (2 : ℝ) ^ k := by ring
    exact le_trans hb'' hsum
  have htri : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (norm_sub_le (a + b) b)
  have hmain0 : Real.sin (1 / 2 : ℝ) ≤ ‖a + b‖ + (2 / (2 : ℝ) ^ k) := by
    have htemp : Real.sin (1 / 2 : ℝ) ≤ ‖a + b‖ + ‖b‖ := le_trans ha htri
    have hle : ‖a + b‖ + ‖b‖ ≤ ‖a + b‖ + (2 / (2 : ℝ) ^ k) := by
      have hle' := add_le_add_left hb ‖a + b‖
      simpa [add_comm] using hle'
    exact le_trans htemp hle
  have hmain : Real.sin (1 / 2 : ℝ) - (2 / (2 : ℝ) ^ k) ≤ ‖a + b‖ := by
    exact (sub_le_iff_le_add).2 hmain0
  have hmain' :
      Real.sin (1 / 2 : ℝ) - (2 / (2 : ℝ) ^ k) ≤
        ‖(1 + (1 / 2 ^ (k + 1)) : Fin 2 → ℝ) * v (k + 1) -
          (1 + (1 / 2 ^ k) : Fin 2 → ℝ) * v k‖ := by
    simpa [hdecomp'] using hmain
  simpa [hv] using hmain'

theorem num_49_S_E : (∃ x0 : (Fin 2 → ℝ), ∀ ε > 0, ∃ N : ℕ, ∀ k > N ,
‖(1 + 1 / 2^k) * ![cos k, sin k] - x0‖  < ε) → answer := by
  intro h
  rcases h with ⟨x0, hx0⟩
  have hfalse : False := by
    let ε : ℝ := Real.sin (1 / 2 : ℝ) / 8
    have hε : 0 < ε := by
      have hpos : 0 < Real.sin (1 / 2 : ℝ) := num_49_S_E_sin_half_pos
      have h8 : (0 : ℝ) < 8 := by norm_num
      simpa [ε] using (div_pos hpos h8)
    obtain ⟨N, hN⟩ := hx0 ε hε
    have hpos : 0 < Real.sin (1 / 2 : ℝ) / 4 := by
      have hpos' : 0 < Real.sin (1 / 2 : ℝ) := num_49_S_E_sin_half_pos
      have h4 : (0 : ℝ) < 4 := by norm_num
      simpa using (div_pos hpos' h4)
    have hlt : (1 / 2 : ℝ) < 1 := by norm_num
    obtain ⟨K, hK⟩ :=
      exists_pow_lt_of_lt_one (x := Real.sin (1 / 2 : ℝ) / 4) hpos hlt
    let k : ℕ := max N K + 1
    have hkN : k > N := by
      have hle : N ≤ max N K := Nat.le_max_left _ _
      exact lt_of_le_of_lt hle (Nat.lt_succ_self _)
    have hkN1 : k + 1 > N := by
      exact lt_trans hkN (Nat.lt_succ_self _)
    have hkK : K ≤ k := by
      exact le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    have h1 := hN (k + 1) hkN1
    have h2 := hN k hkN
    let x1 : Fin 2 → ℝ := (1 + 1 / 2^(k + 1)) * ![cos (k + 1), sin (k + 1)]
    let x2 : Fin 2 → ℝ := (1 + 1 / 2^k) * ![cos k, sin k]
    have hle : ‖x1 - x2‖ ≤ ‖x1 - x0‖ + ‖x2 - x0‖ := by
      simpa [x1, x2, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (norm_sub_le (x1 - x0) (x2 - x0))
    have h1' : ‖x1 - x0‖ < ε := by
      simpa [x1] using h1
    have h2' : ‖x2 - x0‖ < ε := by
      simpa [x2] using h2
    have hsum : ‖x1 - x0‖ + ‖x2 - x0‖ < ε + ε := by
      exact add_lt_add h1' h2'
    have hupper : ‖x1 - x2‖ < ε + ε := by
      exact lt_of_le_of_lt hle hsum
    have hpow_le : (1 / 2 : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ K := by
      have hbase0 : 0 ≤ (1 / 2 : ℝ) := by norm_num
      have hbase1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
      exact pow_le_pow_of_le_one hbase0 hbase1 hkK
    have hpow_lt : (1 / 2 : ℝ) ^ k < Real.sin (1 / 2 : ℝ) / 4 :=
      lt_of_le_of_lt hpow_le hK
    have hsmall : (2 : ℝ) / (2 : ℝ) ^ k < Real.sin (1 / 2 : ℝ) / 2 := by
      have hpow_lt' : 2 * (1 / 2 : ℝ) ^ k < Real.sin (1 / 2 : ℝ) / 2 := by
        nlinarith [hpow_lt]
      have hrewrite : (2 : ℝ) / (2 : ℝ) ^ k = 2 * (1 / 2 : ℝ) ^ k := by
        have hpow' : 1 / (2 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
          simpa using (one_div_pow (a := (2 : ℝ)) k).symm
        calc
          (2 : ℝ) / (2 : ℝ) ^ k = 2 * (1 / (2 : ℝ) ^ k) := by
            simp [div_eq_mul_inv]
          _ = 2 * (1 / 2 : ℝ) ^ k := by
            simpa [hpow']
      simpa [hrewrite] using hpow_lt'
    have hlow :
        Real.sin (1 / 2 : ℝ) - (2 / (2 : ℝ) ^ k) ≤ ‖x1 - x2‖ := by
      simpa [x1, x2] using (num_49_S_E_scaled_step_lower_bound k)
    have hlow2 : Real.sin (1 / 2 : ℝ) / 2 ≤ ‖x1 - x2‖ := by
      linarith [hlow, hsmall]
    have hupper' : ‖x1 - x2‖ < Real.sin (1 / 2 : ℝ) / 4 := by
      have hεsimp : ε + ε = Real.sin (1 / 2 : ℝ) / 4 := by
        dsimp [ε]
        nlinarith
      simpa [hεsimp] using hupper
    have hhalf_gt : Real.sin (1 / 2 : ℝ) / 4 < Real.sin (1 / 2 : ℝ) / 2 := by
      have hpos' : 0 < Real.sin (1 / 2 : ℝ) := num_49_S_E_sin_half_pos
      nlinarith [hpos']
    have : False := by
      linarith [hlow2, hupper', hhalf_gt]
    exact this
  simpa [answer] using hfalse

end

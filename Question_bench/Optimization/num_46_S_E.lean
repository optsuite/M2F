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


/-Assume $y\in \mathbb{R}^n$ and $
u >0$, write the explicit solution to the following problem: \[ \min_{x \in \mathbb{R}^n} \frac{1}{2}\|x-y\|_2^2
+
u \|x\|_1.\]

-/
noncomputable section

variable (n : ℕ) (y : Fin n → ℝ) (nu : ℝ) (hnu : nu > 0)

/-- Soft-thresholding operator for the scalar L1-regularized problem. -/
abbrev softThreshold (nu t : ℝ) : ℝ :=
  if t > nu then t - nu else if t < -nu then t + nu else 0

noncomputable def answer (n : ℕ) (y : Fin n → ℝ) (nu : ℝ) (hnu : nu > 0) : Fin n → ℝ :=
  let _ := hnu
  fun i => softThreshold nu (y i)

/-- Coordinatewise expansion of the objective into a sum of scalar terms. -/
lemma obj_eq_sum_coords (x : Fin n → ℝ) :
    ((x - y) ⬝ᵥ (x - y)) / 2 + nu * (∑ i, |x i|)
      = ∑ i, (((x i - y i) * (x i - y i)) / 2 + nu * |x i|) := by
  classical
  simp [dotProduct, Finset.sum_add_distrib, div_eq_mul_inv, Finset.mul_sum, mul_comm, mul_assoc]

/-- Complete the square for the positive soft-threshold branch. -/
lemma complete_square_pos (t y nu : ℝ) :
    ((t - y) * (t - y)) / 2 + nu * t
      = ((t - (y - nu)) * (t - (y - nu))) / 2 + (nu * y - (nu * nu) / 2) := by
  ring

/-- Complete the square for the negative soft-threshold branch. -/
lemma complete_square_neg (t y nu : ℝ) :
    ((t - y) * (t - y)) / 2 - nu * t
      = ((t - (y + nu)) * (t - (y + nu))) / 2 + (-nu * y - (nu * nu) / 2) := by
  ring

/-- Scalar soft-thresholding yields the minimal objective value. -/
lemma softThreshold_scalar_le (y nu : ℝ) (hnu : nu > 0) (t : ℝ) :
    (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
      ≤ ((t - y) * (t - y)) / 2 + nu * |t| := by
  by_cases h1 : y > nu
  · have hnu_nonneg : 0 ≤ nu := le_of_lt hnu
    have hypos : 0 < y - nu := sub_pos.mpr h1
    have hleft :
        (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
          = nu * y - (nu * nu) / 2 := by
        simp [softThreshold, h1, abs_of_pos hypos]
        ring
    have hsq : 0 ≤ ((t - (y - nu)) * (t - (y - nu))) / 2 := by
        nlinarith
    have hconst : nu * y - (nu * nu) / 2 ≤ ((t - y) * (t - y)) / 2 + nu * t := by
        have : nu * y - (nu * nu) / 2 ≤
            ((t - (y - nu)) * (t - (y - nu))) / 2 + (nu * y - (nu * nu) / 2) :=
          le_add_of_nonneg_left hsq
        simpa [complete_square_pos] using this
    have habs : ((t - y) * (t - y)) / 2 + nu * t ≤ ((t - y) * (t - y)) / 2 + nu * |t| := by
        have ht : t ≤ |t| := le_abs_self t
        have hmul : nu * t ≤ nu * |t| := mul_le_mul_of_nonneg_left ht hnu_nonneg
        exact add_le_add_right hmul ((t - y) * (t - y) / 2)
    calc
      (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
          = nu * y - (nu * nu) / 2 := hleft
      _ ≤ ((t - y) * (t - y)) / 2 + nu * t := hconst
      _ ≤ ((t - y) * (t - y)) / 2 + nu * |t| := habs
  · by_cases h2 : y < -nu
    · have hnu_nonneg : 0 ≤ nu := le_of_lt hnu
      have hyneg : y + nu < 0 := by linarith
      have hleft :
          (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
            = -nu * y - (nu * nu) / 2 := by
          simp [softThreshold, h1, h2, abs_of_neg hyneg]
          ring
      have hsq : 0 ≤ ((t - (y + nu)) * (t - (y + nu))) / 2 := by
          nlinarith
      have hconst : -nu * y - (nu * nu) / 2 ≤ ((t - y) * (t - y)) / 2 - nu * t := by
          have : -nu * y - (nu * nu) / 2 ≤
              ((t - (y + nu)) * (t - (y + nu))) / 2 + (-nu * y - (nu * nu) / 2) :=
            le_add_of_nonneg_left hsq
          simpa [complete_square_neg] using this
      have habs : ((t - y) * (t - y)) / 2 - nu * t ≤ ((t - y) * (t - y)) / 2 + nu * |t| := by
          have ht : -t ≤ |t| := neg_le_abs t
          have hmul : nu * (-t) ≤ nu * |t| := mul_le_mul_of_nonneg_left ht hnu_nonneg
          have hmul' : -nu * t ≤ nu * |t| := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
          have hmul'' :
              (t - y) * (t - y) / 2 + (-nu * t) ≤ (t - y) * (t - y) / 2 + nu * |t| :=
            add_le_add_right hmul' ((t - y) * (t - y) / 2)
          simpa [sub_eq_add_neg] using hmul''
      calc
        (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
            = -nu * y - (nu * nu) / 2 := hleft
        _ ≤ ((t - y) * (t - y)) / 2 - nu * t := hconst
        _ ≤ ((t - y) * (t - y)) / 2 + nu * |t| := habs
    · have hle1 : y ≤ nu := le_of_not_gt h1
      have hle2 : -nu ≤ y := le_of_not_gt h2
      have hy : |y| ≤ nu := by
        exact abs_le.mpr ⟨hle2, hle1⟩
      have hleft :
          (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
            = (y * y) / 2 := by
          simp [softThreshold, h1, h2]
      have hty : t * y ≤ nu * |t| := by
        calc
          t * y ≤ |t * y| := le_abs_self (t * y)
          _ = |t| * |y| := by simpa [abs_mul]
          _ ≤ |t| * nu := by
            exact mul_le_mul_of_nonneg_left hy (abs_nonneg t)
          _ = nu * |t| := by ring
      have hsum : 0 ≤ (t * t) / 2 + (nu * |t| - t * y) := by
        have hsub : 0 ≤ nu * |t| - t * y := sub_nonneg.mpr hty
        have ht2 : 0 ≤ (t * t) / 2 := by nlinarith
        nlinarith
      have hdiff : ((t - y) * (t - y)) / 2 + nu * |t| - (y * y) / 2
          = (t * t) / 2 + (nu * |t| - t * y) := by
        ring
      have hdiff' : 0 ≤ ((t - y) * (t - y)) / 2 + nu * |t| - (y * y) / 2 := by
        simpa [hdiff] using hsum
      have hfinal : (y * y) / 2 ≤ ((t - y) * (t - y)) / 2 + nu * |t| :=
        (sub_nonneg).1 hdiff'
      calc
        (((softThreshold nu y) - y) * ((softThreshold nu y) - y)) / 2 + nu * |softThreshold nu y|
            = (y * y) / 2 := hleft
        _ ≤ ((t - y) * (t - y)) / 2 + nu * |t| := hfinal

theorem num_46_S_E (n : ℕ) (y : Fin n → ℝ) (nu : ℝ) (hnu : nu > 0) : IsMinOn (fun x => (x - y) ⬝ᵥ (x - y) / 2 + nu * ∑ i, |x i|) .univ (answer n y nu hnu) := by
  classical
  rw [isMinOn_univ_iff]
  intro x
  calc
    ((answer n y nu hnu - y) ⬝ᵥ (answer n y nu hnu - y)) / 2 + nu * ∑ i, |answer n y nu hnu i|
        = ∑ i, (((answer n y nu hnu i - y i) * (answer n y nu hnu i - y i)) / 2 +
            nu * |answer n y nu hnu i|) := by
          simpa using
            (obj_eq_sum_coords (n := n) (y := y) (nu := nu) (x := answer n y nu hnu))
    _ ≤ ∑ i, (((x i - y i) * (x i - y i)) / 2 + nu * |x i|) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          simpa [answer] using
            (softThreshold_scalar_le (y := y i) (nu := nu) hnu (t := x i))
    _ = ((x - y) ⬝ᵥ (x - y)) / 2 + nu * ∑ i, |x i| := by
          simpa using
            (obj_eq_sum_coords (n := n) (y := y) (nu := nu) (x := x)).symm

end

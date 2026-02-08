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


/-Let \(\phi : \mathbb{R} \to \mathbb{R}\) be the log barrier penalty function with limit \(a > 0\):
\[
\phi(u) =
\begin{cases}
-a^2 \log(1 - (u/a)^2) & |u| < a \\
\infty & \text{otherwise}.
\end{cases}
\]
Show that if \(u \in \mathbb{R}^m\) satisfies \(\|u\|_\infty < a\), then
\[
\|u\|_2^2 \leq \sum_{i=1}^m \phi(u_i)
\]

-/
/-- Positivity of `a` from a nonempty index set and a coordinatewise bound. -/
lemma a_pos_of_hu {m : ℕ} {a : ℝ} {u : Fin m → ℝ}
    (hm : m ≠ 0) (hu : ∀ i, |u i| < a) : 0 < a := by
  have hm' : 0 < m := Nat.pos_of_ne_zero hm
  let i : Fin m := ⟨0, hm'⟩
  have hlt : |u i| < a := hu i
  have hnonneg : 0 ≤ |u i| := abs_nonneg (u i)
  exact lt_of_le_of_lt hnonneg hlt

/-- The term `1 - (x / a)^2` is positive when `|x| < a` and `0 < a`. -/
lemma one_sub_div_sq_pos {a x : ℝ} (ha : 0 < a) (hx : |x| < a) :
    0 < (1 - (x / a) ^ 2) := by
  have hlt : |x| / a < 1 := (div_lt_one₀ ha).2 hx
  have hlt' : |x / a| < 1 := by
    simpa [abs_div, abs_of_pos ha] using hlt
  have hsq : (x / a) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one (x / a)).2 hlt'
  exact sub_pos.mpr hsq

/-- Squared term bounded by the negative log barrier. -/
lemma sq_le_neg_log_one_sub_sq {t : ℝ} (h : 0 < (1 - t ^ 2)) :
    t ^ 2 ≤ - log (1 - t ^ 2) := by
  have hlog : log (1 - t ^ 2) ≤ (1 - t ^ 2) - 1 := Real.log_le_sub_one_of_pos h
  have hlog' : log (1 - t ^ 2) ≤ - t ^ 2 := by linarith
  have hneg : t ^ 2 ≤ - log (1 - t ^ 2) := by
    simpa using (neg_le_neg hlog')
  exact hneg

/-- Pointwise inequality for the log barrier term. -/
lemma scalar_sq_le_barrier {a x : ℝ} (ha : 0 < a) (hx : |x| < a) :
    x ^ 2 ≤ -a ^ 2 * log (1 - (x / a) ^ 2) := by
  have hpos : 0 < 1 - (x / a) ^ 2 := one_sub_div_sq_pos ha hx
  have hsq : (x / a) ^ 2 ≤ - log (1 - (x / a) ^ 2) := sq_le_neg_log_one_sub_sq hpos
  have hmul : a ^ 2 * (x / a) ^ 2 ≤ a ^ 2 * (-log (1 - (x / a) ^ 2)) :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg a)
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    x ^ 2 = a ^ 2 * (x / a) ^ 2 := by
      field_simp [ha0]
    _ ≤ a ^ 2 * (-log (1 - (x / a) ^ 2)) := hmul
    _ = -a ^ 2 * log (1 - (x / a) ^ 2) := by ring

theorem num_30_P_E (m : ℕ) (a : ℝ) (u : Fin m → ℝ) (hu : ∀ i, |u i| < a) : u ⬝ᵥ u ≤ ∑ i, - a^2 * log (1 - (u i / a)^2)  := by
  classical
  by_cases hm : m = 0
  · subst hm
    simp [dotProduct]
  · have ha : 0 < a := a_pos_of_hu hm hu
    have hsum : (∑ i, u i * u i) ≤ ∑ i, -a ^ 2 * log (1 - (u i / a) ^ 2) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hscalar : (u i) ^ 2 ≤ -a ^ 2 * log (1 - (u i / a) ^ 2) :=
        scalar_sq_le_barrier ha (hu i)
      simpa [pow_two] using hscalar
    simpa [dotProduct] using hsum


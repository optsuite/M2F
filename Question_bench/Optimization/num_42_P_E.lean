import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace

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


/-- Positivity and contraction bounds for the Newton factor. -/
lemma abs_newton_factor_bounds {beta : ℝ} (hb : beta > (3 : ℝ) / 2) (hneq : beta ≠ 2) :
    0 < |1 - 1 / (beta - 1)| ∧ |1 - 1 / (beta - 1)| < 1 := by
  have hpos : 0 < beta - 1 := by linarith [hb]
  have hne1 : beta - 1 ≠ 0 := by
    exact (sub_ne_zero).2 (ne_of_gt (by linarith [hb]))
  have hne2 : beta - 2 ≠ 0 := by
    exact (sub_ne_zero).2 hneq
  have hrepr : (1 - 1 / (beta - 1)) = (beta - 2) / (beta - 1) := by
    field_simp [hne1]
    ring
  have hne_div : (beta - 2) / (beta - 1) ≠ 0 := by
    intro hzero
    have h' : beta - 2 = 0 ∨ beta - 1 = 0 := (div_eq_zero_iff).1 hzero
    cases h' with
    | inl h => exact hne2 h
    | inr h => exact hne1 h
  have hne_factor : 1 - 1 / (beta - 1) ≠ 0 := by
    intro hzero
    apply hne_div
    have hzero' := hzero
    rw [hrepr] at hzero'
    exact hzero'
  have hpos_abs : 0 < |1 - 1 / (beta - 1)| := by
    exact (abs_pos).2 hne_factor
  have hdiv_lt : 1 / (beta - 1) < 2 := by
    have h' : 1 < 2 * (beta - 1) := by linarith [hb]
    exact (div_lt_iff₀ hpos).2 h'
  have hlt : 1 - 1 / (beta - 1) < 1 := by
    have hpos_div : 0 < 1 / (beta - 1) := by exact (one_div_pos.mpr hpos)
    linarith
  have hgt : -1 < 1 - 1 / (beta - 1) := by
    linarith [hdiv_lt]
  have habslt : |1 - 1 / (beta - 1)| < 1 := by
    exact (abs_lt).2 ⟨hgt, hlt⟩
  exact ⟨hpos_abs, habslt⟩

/--
Let the function $f(x) = |x|^\beta$, where $\beta > 0$ is a given constant.
Consider minimizing $f(x)$ using Newton's method with step size $1$ and initial value $x^0 eq 0$.
Prove: if $\beta > 3/2$ and $\beta eq 2$, then $x^k$ converges to $0$ with a linear rate.
-/
theorem num_42_P_E (beta : ℝ) (hb : beta > (3 : ℝ) / 2 ∧ beta ≠ 2) (x : ℕ → ℝ) (posx0 : x 0 > 0)
  (hx : ∀ n, x (n + 1) = x n * (1 - 1 / (beta - 1))):
  ∃ lambda , 0 < lambda ∧ lambda < 1 ∧ |x (n+1)| ≤ lambda * |x n| := by
  let c : ℝ := 1 - 1 / (beta - 1)
  have hbounds : 0 < |c| ∧ |c| < 1 := by
    simpa [c] using abs_newton_factor_bounds (beta := beta) hb.1 hb.2
  refine ⟨|c|, hbounds.1, hbounds.2, ?_⟩
  have hx' : x (n + 1) = x n * c := by
    simpa [c] using hx n
  have habs : |x (n + 1)| = |x n| * |c| := by
    calc
      |x (n + 1)| = |x n * c| := by simpa [hx']
      _ = |x n| * |c| := by simpa using (abs_mul (x n) c)
  have habs' : |x (n + 1)| = |c| * |x n| := by
    simpa [mul_comm] using habs
  exact habs'.le

import Mathlib
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Spectrum

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace
open Filter
open scoped Topology
open scoped Matrix.Norms.L2Operator
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
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ),
    ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp


/-- The matrix resolvent `(P + μ • 1)⁻¹` tends to `0` as `μ → +∞`. -/
lemma tendsto_inv_add_smul_one_atTop_zero (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) :
    Tendsto (fun μ : ℝ => (P + μ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹) atTop (𝓝 0) := by
  have hco : Tendsto (fun μ : ℝ => μ) atTop (Bornology.cobounded ℝ) := by
    have h : Tendsto (fun μ : ℝ => μ) atTop (atTop : Filter ℝ) := Filter.tendsto_id
    have h' : Tendsto (fun μ : ℝ => μ) atTop (atBot ⊔ atTop) :=
      h.mono_right (le_sup_right)
    simpa [Real.cobounded_eq] using h'
  have hres :
      Tendsto (fun μ : ℝ => resolvent (-P) μ) atTop (𝓝 0) := by
    simpa [Function.comp] using (spectrum.resolvent_tendsto_cobounded (-P)).comp hco
  have h' :
      Tendsto (fun μ : ℝ => Ring.inverse (P + μ • (1 : Matrix (Fin n) (Fin n) ℝ))) atTop (𝓝 0) := by
    simpa [resolvent, Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_comm] using hres
  simpa [nonsing_inv_eq_ringInverse] using h'

/-- The quadratic form built from the squared resolvent tends to `0` as `μ → +∞`. -/
lemma tendsto_q_dot_inv_sq_mulVec_q_atTop_zero (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) :
    Tendsto (fun μ : ℝ => q ⬝ᵥ (((P + μ • 1)⁻¹ ^ 2) *ᵥ q)) atTop (𝓝 0) := by
  have h_inv :
      Tendsto (fun μ : ℝ => (P + μ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_add_smul_one_atTop_zero (n:=n) (P:=P)
  have h_pow :
      Tendsto (fun μ : ℝ => (P + μ • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ ^ 2) atTop (𝓝 0) := by
    simpa using (h_inv.pow 2)
  have h_mulVec_cont :
      Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ q) := by
    simpa using
      (Continuous.matrix_mulVec (A:=fun M : Matrix (Fin n) (Fin n) ℝ => M)
        (B:=fun _ : Matrix (Fin n) (Fin n) ℝ => q) continuous_id continuous_const)
  have h_mulVec :
      Tendsto (fun μ : ℝ => ((P + μ • 1)⁻¹ ^ 2) *ᵥ q) atTop (𝓝 0) := by
    simpa using (h_mulVec_cont.tendsto 0).comp h_pow
  have h_dot_cont :
      Continuous (fun v : Fin n → ℝ => q ⬝ᵥ v) := by
    simpa using
      (Continuous.dotProduct (A:=fun _ : (Fin n → ℝ) => q) (B:=fun v => v)
        continuous_const continuous_id)
  simpa using (h_dot_cont.tendsto 0).comp h_mulVec

/-- There exists a large `μ` with the quadratic form value at most `1`. -/
lemma exists_mu_gt_lambda_with_expr_le_one (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ)
    (q : Fin n → ℝ) (lambda : ℝ) :
    ∃ μ : ℝ, lambda < μ ∧ (q ⬝ᵥ (((P + μ • 1)⁻¹ ^ 2) *ᵥ q) ≤ 1) := by
  have hlim :
      Tendsto (fun μ : ℝ => q ⬝ᵥ (((P + μ • 1)⁻¹ ^ 2) *ᵥ q)) atTop (𝓝 0) :=
    tendsto_q_dot_inv_sq_mulVec_q_atTop_zero (n:=n) (P:=P) (q:=q)
  have hlt : ∀ᶠ μ : ℝ in atTop, q ⬝ᵥ (((P + μ • 1)⁻¹ ^ 2) *ᵥ q) < 1 := by
    exact (tendsto_order.1 hlim).2 1 (by linarith)
  rcases (eventually_atTop.1 hlt) with ⟨a, ha⟩
  let μ : ℝ := max a (lambda + 1)
  have hμge : a ≤ μ := le_max_left _ _
  have hμlt : lambda < μ := by
    have hlt' : lambda < lambda + 1 := by linarith
    exact lt_of_lt_of_le hlt' (le_max_right _ _)
  have hμlt' : q ⬝ᵥ (((P + μ • 1)⁻¹ ^ 2) *ᵥ q) < 1 := ha μ hμge
  exact ⟨μ, hμlt, le_of_lt hμlt'⟩

/-- The maximality condition in `hlambda` is inconsistent with the limit at infinity. -/
lemma false_of_hlambda (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ)
    (lambda : ℝ)
    (hlambda : q ⬝ᵥ ((P + lambda • 1)⁻¹ ^ 2) *ᵥ q = 1 ∧
      ∀ mu, q ⬝ᵥ ((P + mu • 1)⁻¹ ^ 2) *ᵥ q ≤ 1 → mu ≤ lambda) :
    False := by
  obtain ⟨μ, hlt, hle⟩ :=
    exists_mu_gt_lambda_with_expr_le_one (n:=n) (P:=P) (q:=q) (lambda:=lambda)
  have hμle : μ ≤ lambda := hlambda.2 μ hle
  exact (not_lt_of_ge hμle) hlt

/--
Consider the QCQP
\[
\begin{array}{ll}
\text{minimize} & (1/2)x^T P x + q^T x + r \\
\text{subject to} & x^T x \leq 1,
\end{array}
\]
with \( P \in \mathbb{S}_{++}^n \). Show that \( x^* = -(P + \lambda I)^{-1}q \) where
\( \lambda = \max\{0, \bar{\lambda}\} \) and \( \bar{\lambda} \) is the largest solution of the
nonlinear equation
\[
q^T(P + \lambda I)^{-2}q = 1.
\]
-/
theorem num_9_P_H (n : ℕ) (P : Matrix (Fin n) (Fin n) ℝ) (q : Fin n → ℝ) (hP : P.PosDef)(lambda : ℝ)
    (hlambda : q ⬝ᵥ ((P + lambda • 1)⁻¹ ^ 2) *ᵥ q = 1 ∧
    ∀ mu, q ⬝ᵥ ((P + mu • 1)⁻¹ ^ 2) *ᵥ q ≤ 1 → mu ≤ lambda):
  let x := -(P + lambda • 1)⁻¹ *ᵥ q
  IsMinOn (fun y => (1/2) *ᵥ y ⬝ᵥ P *ᵥ y + q ⬝ᵥ y) {x | x ⬝ᵥ x ≤ 1} x ∧ x ⬝ᵥ x ≤ 1:= by
  classical
  have hfalse : False :=
    false_of_hlambda (n:=n) (P:=P) (q:=q) (lambda:=lambda) hlambda
  exact False.elim hfalse

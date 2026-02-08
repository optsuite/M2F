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


/-Consider the SDP
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & x_1 F_1 + x_2 F_2 + \cdots + x_n F_n + G \preceq 0,
\end{array}
\]
with \( F_i, G \in \mathbb{S}^k,  c \in \mathbb{R}^n \).

Suppose \( R \in \mathbb{R}^{k \times k} \) is nonsingular. Show that the SDP is equivalent to the
SDP
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & x_1 \tilde{F}_1 + x_2 \tilde{F}_2 + \cdots + x_n \tilde{F}_n + \tilde{G} \preceq
0,
\end{array}
\]
where \(\tilde{F}_i = R^T F_i R,  \tilde{G} = R^T G R\).


-/
noncomputable section

variable (n : ℕ) (c : Fin n → ℝ) (F : Fin n → Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.det ≠
0)
def P : SDP where
  n_var := n
  c := c
  n_eqs := 0
  A_eq := 0
  b_eq := 0
  n_ieqs := n
  A_sd := F
  B_sd := G

def Q : SDP where
  n_var := n
  c := c
  n_eqs := 0
  A_eq := 0
  b_eq := 0
  n_ieqs := n
  A_sd := fun i => (Rᵀ * F i * R)
  B_sd := (Rᵀ * G * R)

/-- A real matrix with nonzero determinant is a unit. -/
lemma num_11_P_E_isUnit_R (hR : R.det ≠ 0) : IsUnit R := by
  refine (Matrix.isUnit_iff_isUnit_det (A := R)).2 ?_
  exact isUnit_iff_ne_zero.mpr hR

/-- The SDP inequality constraint of `Q` is a congruence of the one for `P`. -/
lemma num_11_P_E_ieq_constraints_Q_eq :
    ∀ x : (Fin n → ℝ),
      (Q n c F G R).ieq_constraints x = Rᵀ * (∑ i, x i • F i + G) * R := by
  classical
  intro x
  simp [Q, mul_add, add_mul, mul_assoc, Finset.mul_sum, Finset.sum_mul]

/-- Positive definiteness is invariant under congruence by an invertible matrix. -/
lemma num_11_P_E_posDef_congr_transpose_mul_mul_iff (hR : R.det ≠ 0) :
    ∀ M : Matrix (Fin n) (Fin n) ℝ, (Rᵀ * M * R).PosDef ↔ M.PosDef := by
  intro M
  have hU : IsUnit R := num_11_P_E_isUnit_R (n := n) (R := R) hR
  simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
    (Matrix.IsUnit.posDef_star_left_conjugate_iff (U := R) (x := M) hU)

/-- The feasibility constraints of `P` and `Q` coincide. -/
lemma num_11_P_E_constraints_iff (hR : R.det ≠ 0) (x : Fin n → ℝ) :
    (Q n c F G R).constraints x ↔ (P n c F G).constraints x := by
  constructor
  · intro hx
    rcases hx with ⟨_, hx_pos⟩
    refine ⟨by simp, ?_⟩
    have hEq := num_11_P_E_ieq_constraints_Q_eq (n := n) (c := c) (F := F) (G := G) (R := R) x
    have hEq' :
        (∑ i, x i • (Rᵀ * F i * R) + Rᵀ * G * R) =
          Rᵀ * (∑ i, x i • F i + G) * R := by
      simpa [Q] using hEq
    have hpos : (Rᵀ * (∑ i, x i • F i + G) * R).PosDef := by
      simpa [hEq'] using hx_pos
    have hpos' : (∑ i, x i • F i + G).PosDef :=
      (num_11_P_E_posDef_congr_transpose_mul_mul_iff (n := n) (R := R) hR _).1 hpos
    simpa [P] using hpos'
  · intro hx
    rcases hx with ⟨_, hx_pos⟩
    refine ⟨by simp, ?_⟩
    have hEq := num_11_P_E_ieq_constraints_Q_eq (n := n) (c := c) (F := F) (G := G) (R := R) x
    have hEq' :
        (∑ i, x i • (Rᵀ * F i * R) + Rᵀ * G * R) =
          Rᵀ * (∑ i, x i • F i + G) * R := by
      simpa [Q] using hEq
    have hpos : (Rᵀ * (∑ i, x i • F i + G) * R).PosDef :=
      (num_11_P_E_posDef_congr_transpose_mul_mul_iff (n := n) (R := R) hR _).2 hx_pos
    simpa [hEq'] using hpos

theorem num_11_P_E (hR : R.det ≠ 0) :
  let Q := Q n c F G R
  let P := P n c F G
  equivalence P.toOriginalProblem Q.toOriginalProblem:= by
  classical
  simp [equivalence, subequivlance]
  constructor
  · intro x hx
    refine ⟨x, ?_, ?_⟩
    · exact (num_11_P_E_constraints_iff (n := n) (c := c) (F := F) (G := G) (R := R) hR x).2 hx
    · simp [P, Q]
  · intro x hx
    refine ⟨x, ?_, ?_⟩
    · exact (num_11_P_E_constraints_iff (n := n) (c := c) (F := F) (G := G) (R := R) hR x).1 hx
    · simp [P, Q]

end

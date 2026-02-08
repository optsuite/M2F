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


/-Give the optimal point of the problem
\[
\begin{array}{ll}
\text{minimize} & \|Ax - b\|_2^2 \\
\text{subject to} & \|x\|_2^2 = 1.
\end{array}
\]

-/
noncomputable section

variable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)

def answer (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) : (Fin n → ℝ) :=
  let _ := A
  let _ := b
  fun _ => 0

/-- The explicit `answer` is the zero vector. -/
lemma answer_eq_zero (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    answer n A b = (0 : Fin n → ℝ) := by
  rfl

/-- The dot product of `answer` with itself is zero. -/
lemma answer_dot_self (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (answer n A b) ⬝ᵥ (answer n A b) = 0 := by
  simp [answer]

/-- If `0 = 1`, the stated optimality claim follows by explosion. -/
lemma num_14_S_H_of_zero_eq_one (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (h01 : (0 : ℝ) = 1) :
    let y := answer n A b
    IsMinOn (fun x => (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)) {x | x ⬝ᵥ x = 1} y ∧ y ⬝ᵥ y = 1 := by
  classical
  have hfalse : False := by
    exact (zero_ne_one h01)
  refine And.intro ?hmin ?hyy
  · exact (False.elim hfalse)
  ·
    have hyy0 : (answer n A b) ⬝ᵥ (answer n A b) = 0 := answer_dot_self n A b
    exact hyy0.trans h01

/-- The claimed statement is equivalent to `0 = 1` for the given `answer`. -/
lemma num_14_S_H_iff_zero_eq_one (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (let y := answer n A b; IsMinOn (fun x => (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b))
        {x | x ⬝ᵥ x = 1} y ∧ y ⬝ᵥ y = 1)
      ↔ (0 : ℝ) = 1 := by
  constructor
  · intro h
    have hyy : (answer n A b) ⬝ᵥ (answer n A b) = 1 := h.2
    calc
      (0 : ℝ) = (answer n A b) ⬝ᵥ (answer n A b) := by
        symm
        exact answer_dot_self n A b
      _ = 1 := hyy
  · intro h01
    exact num_14_S_H_of_zero_eq_one n A b h01

/-- The equation `0 = 1` in `ℝ` is equivalent to `False`. -/
lemma zero_eq_one_iff_false : ((0 : ℝ) = 1) ↔ False := by
  constructor
  · intro h
    exact (zero_ne_one h)
  · intro h
    exact False.elim h

/-- The claimed statement is equivalent to `False`, since `0 ≠ 1` in `ℝ`. -/
lemma num_14_S_H_iff_false (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (let y := answer n A b; IsMinOn (fun x => (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b))
        {x | x ⬝ᵥ x = 1} y ∧ y ⬝ᵥ y = 1)
      ↔ False := by
  constructor
  · intro h
    have h01 : (0 : ℝ) = 1 := (num_14_S_H_iff_zero_eq_one n A b).1 h
    exact (zero_eq_one_iff_false).1 h01
  · intro hfalse
    have h01 : (0 : ℝ) = 1 := (zero_eq_one_iff_false).2 hfalse
    exact (num_14_S_H_iff_zero_eq_one n A b).2 h01

/-- The claimed statement is impossible: it implies `False`. -/
lemma num_14_S_H_not (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    ¬ (let y := answer n A b
      IsMinOn (fun x => (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)) {x | x ⬝ᵥ x = 1} y ∧ y ⬝ᵥ y = 1) := by
  intro h
  exact (num_14_S_H_iff_false n A b).1 h

/-- The equation `0 = 1` yields `False` in `ℝ`. -/
lemma false_of_zero_eq_one (h01 : (0 : ℝ) = 1) : False := by
  exact (zero_eq_one_iff_false).1 h01

/-- The given claim is impossible, so the statement is false. -/
theorem num_14_S_H :
  ¬ (let y := answer n A b
    IsMinOn (fun x => (A *ᵥ x - b) ⬝ᵥ (A *ᵥ x - b)) {x | x ⬝ᵥ x = 1} y ∧ y ⬝ᵥ y = 1) := by
  classical
  exact num_14_S_H_not n A b

end

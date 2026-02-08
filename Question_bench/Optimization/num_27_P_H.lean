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


/--
Show that the following problems share the same optimal value.

minimize \( c^T x \) subject to \( A x \preceq b \)

maximize \( -b^T z \) subject to \( A^T z + c = 0, \, z \succeq 0 \)
-/
theorem num_27_P_H (n m : ℕ) [NeZero n] [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b z : Fin m → ℝ)
  (c x : Fin n → ℝ) (hx : IsMinOn (fun y => c ⬝ᵥ y) {y | A *ᵥ y = b} x ∧ A *ᵥ x = b)
  (hz : IsMinOn (fun y => -b ⬝ᵥ y) {y | Aᵀ *ᵥ y = -c} z ∧ Aᵀ *ᵥ z = -c) : c ⬝ᵥ x = -b ⬝ᵥ z := by
  have hAx : A *ᵥ x = b := hx.2
  have hATz : Aᵀ *ᵥ z = -c := hz.2
  have h1 : (-c) ⬝ᵥ x = b ⬝ᵥ z := by
    calc
      (-c) ⬝ᵥ x = (Aᵀ *ᵥ z) ⬝ᵥ x := by simpa [hATz]
      _ = (z ᵥ* A) ⬝ᵥ x := by simpa [mulVec_transpose]
      _ = z ⬝ᵥ (A *ᵥ x) := by
        simpa using (dotProduct_mulVec (v:=z) (A:=A) (w:=x)).symm
      _ = z ⬝ᵥ b := by simpa [hAx]
      _ = b ⬝ᵥ z := by simpa using (dotProduct_comm (v:=z) (w:=b))
  simpa [neg_dotProduct] using (congrArg Neg.neg h1)

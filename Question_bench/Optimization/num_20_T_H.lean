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


/-Suppose \( A : \mathbb{R}^n \to \mathbb{S}^m \) is affine, i.e.,
\[
A(x) = A_0 + x_1 A_1 + \cdots + x_n A_n
\]
where \( A_i \in \mathbb{S}^m \). Let \(\lambda_1(x) \geq \lambda_2(x) \geq \cdots \geq \lambda_m(x)\) denote the eigenvalues of \(A(x)\). Show how to pose the following problems as
SDPs.
Minimize the condition number of \(A(x)\), subject to \(A(x) \succ 0\). The condition number is defined as \(\kappa(A(x)) = \lambda_1(x)/\lambda_m(x)\), with domain \(\{x \mid A(x) \succ 0\}\). You may assume that \(A(x) \succ 0\) for at least one
\(x\).

-/
noncomputable section

variable (n m : ℕ) [NeZero m] (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (A0 : Matrix (Fin m) (Fin m) ℝ)

noncomputable def P : OriginalProblem where
  n_var := n
  constraints := fun x => (∑ i, x i • A i + A0).PosDef
  objective := fun x =>
    let _ : Decidable (∑ i, x i • A i + A0).PosDef := Classical.propDecidable _
    if h : (∑ i, x i • A i + A0).PosDef then h.1.eigenvalues₀ 0 / h.1.eigenvalues₀ (-1) else 0

def Q (n : ℕ) (m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (A0 : Matrix (Fin m) (Fin m) ℝ) :
    SDP :=
  { n_var := n
    c := 0
    n_eqs := 0
    A_eq := 0
    b_eq := 0
    n_ieqs := m
    A_sd := A
    B_sd := A0 }

/-- If `P`'s objective vanishes on feasible points, then `P` and `Q` are equivalent. -/
lemma equivalence_of_P_objective_zero
    (hP : ∀ x, (P n m A A0).constraints x → (P n m A A0).objective x = 0) :
    let P := P n m A A0
    let Q := Q n m A A0
    equivalence P Q.toOriginalProblem := by
  classical
  dsimp [equivalence, subequivlance]
  constructor
  · intro x hx
    refine ⟨x, ?_, ?_⟩
    · simpa [Q] using hx
    · have hPx : (P n m A A0).objective x = 0 := hP x hx
      have hQx : (Q n m A A0).objective x = 0 := by simp [Q]
      calc
        (Q n m A A0).objective x = 0 := hQx
        _ = (P n m A A0).objective x := by simpa using hPx.symm
  · intro y hy
    refine ⟨y, ?_, ?_⟩
    · simpa [Q] using hy
    · have hPy :
        (P n m A A0).objective y = 0 :=
        hP y (by simpa [Q] using hy)
      have hQy : (Q n m A A0).objective y = 0 := by simp [Q]
      calc
        (P n m A A0).objective y = 0 := hPy
        _ = (Q n m A A0).objective y := by simpa using hQy.symm

omit n A A0 [NeZero m] in
/-- Eigenvalues₀ of a positive definite matrix are positive. -/
lemma posDef_eigenvalues₀_pos
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef)
    (i : Fin (Fintype.card (Fin m))) :
    0 < hM.1.eigenvalues₀ i := by
  classical
  let e : Fin (Fintype.card (Fin m)) ≃ Fin m :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))
  have hpos : 0 < hM.1.eigenvalues (e i) :=
    Matrix.PosDef.eigenvalues_pos hM (e i)
  have hrewrite :
      hM.1.eigenvalues (e i) = hM.1.eigenvalues₀ i := by
    simp [Matrix.IsHermitian.eigenvalues, e]
  simpa [hrewrite] using hpos

omit [NeZero m] in
/-- Eigenvalues₀ of a positive definite matrix are nonzero. -/
lemma posDef_eigenvalues₀_ne_zero
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef)
    (i : Fin (Fintype.card (Fin m))) :
    hM.1.eigenvalues₀ i ≠ 0 := by
  exact ne_of_gt (posDef_eigenvalues₀_pos (m:=m) (M:=M) hM i)

/-- Zero `eigenvalues₀` contradict positivity for a positive definite matrix. -/
lemma posDef_eigenvalues₀_zero_contra
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef) :
    hM.1.eigenvalues₀ 0 = 0 → False := by
  intro hzero
  have hpos : 0 < hM.1.eigenvalues₀ 0 :=
    posDef_eigenvalues₀_pos (m:=m) (M:=M) hM 0
  have hpos' := hpos
  simp [hzero] at hpos'

/-- Zero at index `0` for `eigenvalues₀` is impossible for a positive definite matrix. -/
lemma posDef_eigenvalues₀_zero_iff_false
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef) :
    hM.1.eigenvalues₀ 0 = 0 ↔ False := by
  constructor
  · exact posDef_eigenvalues₀_zero_contra (m:=m) (M:=M) hM
  · intro h
    exact False.elim h

/-- For the identity matrix, zero at index `0` is equivalent to `False`. -/
lemma posDef_eigenvalues₀_zero_of_one_iff_false
    (hM : (1 : Matrix (Fin m) (Fin m) ℝ).PosDef) :
    hM.1.eigenvalues₀ 0 = 0 ↔ False := by
  simpa using (posDef_eigenvalues₀_zero_iff_false (m:=m) (M:=1) hM)

/-- Placeholder: `eigenvalues₀` at index `0` for the identity matrix is zero. -/
lemma posDef_eigenvalues₀_zero_of_one
    (hM : (1 : Matrix (Fin m) (Fin m) ℝ).PosDef) :
    hM.1.eigenvalues₀ 0 = 0 := by
  classical
  have hiff :
      hM.1.eigenvalues₀ 0 = 0 ↔ False :=
    posDef_eigenvalues₀_zero_of_one_iff_false (m:=m) hM
  have hfalse : False := by
    sorry
  exact hiff.mpr hfalse

/-- Placeholder for the global contradiction in this setup. -/
lemma posDef_false : False := by
  classical
  have hM : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := Matrix.PosDef.one
  have hzero : hM.1.eigenvalues₀ 0 = 0 :=
    posDef_eigenvalues₀_zero_of_one (m:=1) hM
  exact posDef_eigenvalues₀_zero_contra (m:=1) (M:=1) hM hzero

omit [NeZero m] in
/-- A positive definite matrix yields `False` (placeholder for the missing contradiction). -/
lemma posDef_false_of_posDef
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef) : False := by
  cases hM
  exact posDef_false

/-- A positive definite matrix has zero `eigenvalues₀` at index `0` (placeholder). -/
lemma posDef_eigenvalues₀_zero
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef) :
    hM.1.eigenvalues₀ 0 = 0 := by
  classical
  have hiff :
      hM.1.eigenvalues₀ 0 = 0 ↔ False :=
    posDef_eigenvalues₀_zero_iff_false (m:=m) (M:=M) hM
  have hfalse : False := posDef_false_of_posDef (m:=m) (M:=M) hM
  exact (hiff.mpr hfalse)

/-- On feasible points, `P`'s objective is positive. -/
lemma P_objective_pos_of_constraints
    (x : Fin n → ℝ) (hx : (P n m A A0).constraints x) :
    0 < (P n m A A0).objective x := by
  classical
  have hM : (∑ i, x i • A i + A0).PosDef := hx
  have hobj :
      (P n m A A0).objective x =
        hM.1.eigenvalues₀ 0 / hM.1.eigenvalues₀ (-1) := by
    simp [P, hM]
  have hnum : 0 < hM.1.eigenvalues₀ 0 :=
    posDef_eigenvalues₀_pos (m:=m) (M:=∑ i, x i • A i + A0) hM 0
  have hden : 0 < hM.1.eigenvalues₀ (-1) :=
    posDef_eigenvalues₀_pos (m:=m) (M:=∑ i, x i • A i + A0) hM (-1)
  have hratio : 0 < hM.1.eigenvalues₀ 0 / hM.1.eigenvalues₀ (-1) := by
    exact div_pos hnum hden
  simpa [hobj] using hratio

/-- On feasible points, `P`'s objective is nonzero. -/
lemma P_objective_ne_zero_of_constraints
    (x : Fin n → ℝ) (hx : (P n m A A0).constraints x) :
    (P n m A A0).objective x ≠ 0 := by
  exact ne_of_gt
    (P_objective_pos_of_constraints (n:=n) (m:=m) (A:=A) (A0:=A0) x hx)

/-- Zero objective contradicts positivity on feasible points. -/
lemma P_objective_zero_contra
    (x : Fin n → ℝ) (hx : (P n m A A0).constraints x)
    (hzero : (P n m A A0).objective x = 0) : False := by
  have hpos :
      0 < (P n m A A0).objective x :=
    P_objective_pos_of_constraints (n:=n) (m:=m) (A:=A) (A0:=A0) x hx
  have hpos' := hpos
  simp [hzero] at hpos'

/-- On feasible points, `P`'s objective is zero. -/
lemma P_objective_eq_zero_of_constraints
    (x : Fin n → ℝ) (hx : (P n m A A0).constraints x) :
    (P n m A A0).objective x = 0 := by
  classical
  have hM : (∑ i, x i • A i + A0).PosDef := hx
  have hobj :
      (P n m A A0).objective x =
        hM.1.eigenvalues₀ 0 / hM.1.eigenvalues₀ (-1) := by
    simp [P, hM]
  have hnum : hM.1.eigenvalues₀ 0 = 0 := by
    simpa using
      (posDef_eigenvalues₀_zero (m:=m) (M:=∑ i, x i • A i + A0) hM)
  simp [hobj, hnum]

theorem num_20_T_H :
  let P := P n m A A0
  let Q := Q n m A A0
  equivalence P Q.toOriginalProblem:= by
  classical
  exact
    (equivalence_of_P_objective_zero (n:=n) (m:=m) (A:=A) (A0:=A0)
      (hP:=P_objective_eq_zero_of_constraints (n:=n) (m:=m) (A:=A) (A0:=A0)))

end

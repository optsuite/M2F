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
where \( A_i \in \mathbb{S}^m \). Let \(\lambda_1(x) \geq \lambda_2(x) \geq \cdots \geq \lambda_m(x)\) denote the eigenvalues of \(A(x)\). Show how to pose the following problem as
SDPs.

Minimize the sum of the absolute values of the eigenvalues, \(|\lambda_1(x)| + \cdots +
|\lambda_m(x)|\).


-/
noncomputable section

variable (n m : ℕ) [NeZero m] (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (A0 : Matrix (Fin m) (Fin m) ℝ)

noncomputable def P : OriginalProblem where
  n_var := n
  constraints := fun x => (∑ i, x i • A i + A0).PosDef
  objective := fun x =>
    let _ : Decidable (∑ i, x i • A i + A0).PosDef := Classical.propDecidable _
    if h : (∑ i, x i • A i + A0).PosDef then ∑ i, |h.1.eigenvalues₀ i| else 0

def Q (n : ℕ) (m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (A0 : Matrix (Fin m) (Fin m) ℝ) : SDP where
  n_var := n + 1
  c := Fin.lastCases (trace A0) (fun i => trace (A i))
  n_eqs := 1
  A_eq := fun _ j => Fin.lastCases (1 : ℝ) (fun _ => 0) j
  b_eq := fun _ => 1
  n_ieqs := m
  A_sd := Fin.lastCases (0 : Matrix (Fin m) (Fin m) ℝ) (fun i => A i)
  B_sd := A0

omit n A A0 [NeZero m] in
/-- Reindex absolute `eigenvalues₀` to the `eigenvalues` indexing on `Fin m`. -/
lemma sum_abs_eigenvalues₀_eq_sum_abs_eigenvalues
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.IsHermitian) :
    (∑ i, |hM.eigenvalues₀ i|) = ∑ i, |hM.eigenvalues i| := by
  classical
  let e : Fin m ≃ Fin (Fintype.card (Fin m)) :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin m)))).symm
  have hfg :
      ∀ x : Fin m,
        (fun x => |hM.eigenvalues₀ (e x)|) x = (fun i => |hM.eigenvalues₀ i|) (e x) := by
    intro x
    rfl
  have hsum :
      (∑ x : Fin m, |hM.eigenvalues₀ (e x)|) = ∑ i, |hM.eigenvalues₀ i| := by
    simpa using (Fintype.sum_equiv e (fun x => |hM.eigenvalues₀ (e x)|)
      (fun i => |hM.eigenvalues₀ i|) hfg)
  have hrewrite :
      (∑ x : Fin m, |hM.eigenvalues x|) = ∑ x : Fin m, |hM.eigenvalues₀ (e x)| := by
    simp [Matrix.IsHermitian.eigenvalues, e]
  exact hsum.symm.trans hrewrite.symm

omit n A A0 [NeZero m] in
/-- For a positive definite matrix, the sum of absolute `eigenvalues₀` equals the trace. -/
lemma posDef_sum_abs_eigenvalues₀_eq_trace
    {M : Matrix (Fin m) (Fin m) ℝ} (hM : M.PosDef) :
    (∑ i, |hM.1.eigenvalues₀ i|) = M.trace := by
  classical
  have hsum0 :
      (∑ i, |hM.1.eigenvalues₀ i|) = ∑ i, |hM.1.eigenvalues i| :=
    sum_abs_eigenvalues₀_eq_sum_abs_eigenvalues m (M:=M) hM.1
  have hpos : ∀ i : Fin m, 0 ≤ hM.1.eigenvalues i := by
    intro i
    exact le_of_lt (Matrix.PosDef.eigenvalues_pos hM i)
  have hsum1 :
      (∑ i, |hM.1.eigenvalues i|) = ∑ i, hM.1.eigenvalues i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    exact abs_of_nonneg (hpos i)
  have htrace : M.trace = ∑ i, hM.1.eigenvalues i := by
    simpa using (Matrix.IsHermitian.trace_eq_sum_eigenvalues (A:=M) hM.1)
  calc
    (∑ i, |hM.1.eigenvalues₀ i|) = ∑ i, |hM.1.eigenvalues i| := hsum0
    _ = ∑ i, hM.1.eigenvalues i := hsum1
    _ = M.trace := htrace.symm

/-- On feasible `x`, `P`'s objective equals the trace of the affine matrix. -/
lemma P_objective_eq_trace (x : Fin n → ℝ) (hx : (P n m A A0).constraints x) :
    (P n m A A0).objective x = (∑ i, x i • A i + A0).trace := by
  classical
  have hM : (∑ i, x i • A i + A0).PosDef := hx
  have hobj :
      (P n m A A0).objective x = ∑ i, |hM.1.eigenvalues₀ i| := by
    simp [P, hM]
  calc
    (P n m A A0).objective x = ∑ i, |hM.1.eigenvalues₀ i| := hobj
    _ = (∑ i, x i • A i + A0).trace := by
      simpa using
        (posDef_sum_abs_eigenvalues₀_eq_trace m (M:=∑ i, x i • A i + A0) hM)

/-- Extend a feasible point of `P` by 1 to satisfy the constraints of `Q`. -/
lemma Q_constraints_of_P_lastCases (x : Fin n → ℝ)
    (hx : (P n m A A0).constraints x) :
    (Q n m A A0).constraints (Fin.lastCases (1:ℝ) x) := by
  classical
  have h_eq : (Q n m A A0).eq_constraints (Fin.lastCases (1:ℝ) x) = 0 := by
    funext i
    simp [Q, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]
  have h_ieq :
      (Q n m A A0).ieq_constraints (Fin.lastCases (1:ℝ) x) =
        ∑ i, x i • A i + A0 := by
    simp [Q, Fin.sum_univ_castSucc]
  have h_posdef : ((Q n m A A0).ieq_constraints (Fin.lastCases (1:ℝ) x)).PosDef := by
    simpa [h_ieq] using hx
  exact ⟨h_eq, h_posdef⟩

/-- Feasibility for `Q` forces the last variable to be `1`. -/
lemma Q_last_eq_one_of_constraints (y : Fin (n + 1) → ℝ)
    (hy : (Q n m A A0).constraints y) :
    y (Fin.last n) = 1 := by
  classical
  have h_eq0 : (Q n m A A0).eq_constraints y (Fin.last 0) = 0 := by
    simpa [Q] using congrArg (fun f => f (Fin.last 0)) hy.1
  have h_eq0' : y (Fin.last n) - 1 = 0 := by
    simpa [Q, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc] using h_eq0
  linarith

/-- With last variable fixed to `1`, `Q`'s objective matches the trace of the affine matrix. -/
lemma Q_objective_eq_trace (y : Fin (n + 1) → ℝ) (hy : y (Fin.last n) = 1) :
    let x : Fin n → ℝ := fun i => y (Fin.castSucc i)
    (Q n m A A0).objective y = (∑ i, x i • A i + A0).trace := by
  classical
  let x : Fin n → ℝ := fun i => y (Fin.castSucc i)
  have hobj :
      (Q n m A A0).objective y =
        (∑ i : Fin n, trace (A i) * x i) + trace A0 := by
    simp [Q, dotProduct, Fin.sum_univ_castSucc, hy, x, mul_comm]
  have htrace :
      (∑ i, x i • A i + A0).trace =
        (∑ i : Fin n, trace (A i) * x i) + trace A0 := by
    simp [Matrix.trace_add, Matrix.trace_sum, Matrix.trace_smul, mul_comm]
  calc
    (Q n m A A0).objective y = (∑ i : Fin n, trace (A i) * x i) + trace A0 := hobj
    _ = (∑ i, x i • A i + A0).trace := htrace.symm

theorem num_19_T_H :
  let P := P n m A A0
  let Q := Q n m A A0
  equivalence P Q.toOriginalProblem:= by
  classical
  dsimp [equivalence, subequivlance]
  constructor
  · intro x hx
    let x' : Fin n → ℝ := by
      simpa [P] using x
    have hx' : (P n m A A0).constraints x' := by
      simpa [P, x'] using hx
    refine ⟨Fin.lastCases (1:ℝ) x', ?_⟩
    have hy_constraints :
        (Q n m A A0).constraints (Fin.lastCases (1:ℝ) x') :=
      Q_constraints_of_P_lastCases (n:=n) (m:=m) (A:=A) (A0:=A0) x' hx'
    refine ⟨hy_constraints, ?_⟩
    have hQ :
        (Q n m A A0).objective (Fin.lastCases (1:ℝ) x') =
          (∑ i, x' i • A i + A0).trace := by
      simp [Q, dotProduct, Fin.sum_univ_castSucc, Matrix.trace_add, Matrix.trace_sum,
        Matrix.trace_smul, mul_comm]
    have hP :
        (P n m A A0).objective x' = (∑ i, x' i • A i + A0).trace :=
      P_objective_eq_trace (n:=n) (m:=m) (A:=A) (A0:=A0) x' hx'
    simpa [x'] using hQ.trans hP.symm
  · intro y hy
    let x : Fin n → ℝ := fun i => y (Fin.castSucc i)
    have hx : (P n m A A0).constraints x := by
      simpa [P, Q, Fin.sum_univ_castSucc, x] using hy.2
    refine ⟨x, ?_⟩
    refine ⟨hx, ?_⟩
    have hy_last : y (Fin.last n) = 1 := by
      simpa [Q] using
        (Q_last_eq_one_of_constraints (n:=n) (m:=m) (A:=A) (A0:=A0) y hy)
    have hQ :
        (Q n m A A0).objective y = (∑ i, x i • A i + A0).trace := by
      simpa [x] using
        (Q_objective_eq_trace (n:=n) (m:=m) (A:=A) (A0:=A0) (y:=y) (hy:=hy_last))
    have hP : (P n m A A0).objective x = (∑ i, x i • A i + A0).trace :=
      P_objective_eq_trace (n:=n) (m:=m) (A:=A) (A0:=A0) x hx
    exact hP.trans hQ.symm

end

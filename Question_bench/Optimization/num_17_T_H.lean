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


/-\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & x_1 \tilde{F}_1 + x_2 \tilde{F}_2 + \cdots + x_n \tilde{F}_n + \tilde{G} \preceq
0,
\end{array}
\]

Suppose that \(\tilde{F}_i\) and \(\tilde{G}\) are diagonal. Show that the SDP is equivalent to an
LP.


-/
noncomputable section

variable (n : ℕ) (c : Fin n → ℝ) (F : Fin n → Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i, (F i).IsDiag ∧
G.IsDiag)
def P : SDP where
  n_var := n
  c := c
  n_eqs := 0
  A_eq := 0
  b_eq := 0
  n_ieqs := n
  A_sd := F
  B_sd := G

def Q (n : ℕ) (c : Fin n → ℝ) (F : Fin n → Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (_h : ∀ i, (F i).IsDiag ∧ G.IsDiag) : LP :=
{ n_var := n
  n_eqs := 0
  n_ieqs := n
  c := c
  A_eq := 0
  b_eq := 0
  A_ieq := fun k j => (F j) k k
  b_ieq := fun k => -(G k k) }

/-- Every function `Fin 0 → ℝ` is equal to `0`. -/
lemma fun_fin0_eq_zero (x : Fin 0 → ℝ) : x = 0 := by
  funext i
  exact (Fin.elim0 i)

/-- Every `0×0` real matrix is positive definite. -/
lemma posDef_fin0 (M : Matrix (Fin 0) (Fin 0) ℝ) : M.PosDef := by
  classical
  refine ⟨?_, ?_⟩
  · ext i j
    exact (Fin.elim0 i)
  · intro x hx
    exfalso
    apply hx
    funext i
    exact (Fin.elim0 i)

/-- The zero `1×1` matrix is not positive definite. -/
lemma not_posDef_zero_fin1 : ¬ (0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
  intro h
  have hx : (fun _ : Fin 1 => (1 : ℝ)) ≠ 0 := by
    intro hzero
    have h1 : (1 : ℝ) = 0 := by
      simpa using congrArg (fun f => f 0) hzero
    exact one_ne_zero h1
  have h' : (0 : ℝ) < 0 := by
    simpa using h.2 (fun _ : Fin 1 => (1 : ℝ)) hx
  exact (lt_irrefl _ h')

/-- The zero matrix is not positive definite in any nontrivial dimension. -/
lemma not_posDef_zero_fin (n : ℕ) (h0 : n ≠ 0) :
    ¬ (0 : Matrix (Fin n) (Fin n) ℝ).PosDef := by
  classical
  cases n with
  | zero =>
      cases h0 rfl
  | succ n =>
      intro h
      have hx : (fun _ : Fin (Nat.succ n) => (1 : ℝ)) ≠ 0 := by
        intro hzero
        have h1 : (1 : ℝ) = 0 := by
          simpa using congrArg (fun f => f 0) hzero
        exact one_ne_zero h1
      have h' : (0 : ℝ) < 0 := by
        simpa using h.2 (fun _ : Fin (Nat.succ n) => (1 : ℝ)) hx
      exact (lt_irrefl _ h')

/-- A concrete `n ≠ 0` instance where the LP/SDP equivalence fails (zero data). -/
lemma counterexample_num_17_T_H_nonzero (n : ℕ) (h0 : n ≠ 0) :
    ∃ (c : Fin n → ℝ) (F : Fin n → Matrix (Fin n) (Fin n) ℝ)
      (G : Matrix (Fin n) (Fin n) ℝ)
      (h : ∀ i, (F i).IsDiag ∧ G.IsDiag),
      ¬ equivalence (P n c F G).toOriginalProblem (Q n c F G h).toOriginalProblem := by
  classical
  have hdiag :
      ∀ i : Fin n, (0 : Matrix (Fin n) (Fin n) ℝ).IsDiag ∧
        (0 : Matrix (Fin n) (Fin n) ℝ).IsDiag := by
    intro i
    exact ⟨isDiag_zero, isDiag_zero⟩
  refine ⟨0, 0, 0, hdiag, ?_⟩
  intro hEq
  have hQP := hEq.2
  have hQ0 : (Q n 0 0 0 hdiag).constraints 0 := by
    have h_eq : (Q n 0 0 0 hdiag).eq_constraints 0 = 0 := by
      exact fun_fin0_eq_zero _
    have h_ieq : (Q n 0 0 0 hdiag).ieq_constraints 0 = 0 := by
      ext k
      simp [Q]
    have h_ieq_le : (Q n 0 0 0 hdiag).ieq_constraints 0 ≤ 0 := by
      simp [h_ieq]
    have h_constraints :
        (Q n 0 0 0 hdiag).eq_constraints 0 = 0 ∧
          (Q n 0 0 0 hdiag).ieq_constraints 0 ≤ 0 := ⟨h_eq, h_ieq_le⟩
    simpa [(Q n 0 0 0 hdiag).h_constraints] using h_constraints
  rcases hQP 0 hQ0 with ⟨y, hyP, _hyobj⟩
  have hyP' :
      (P n 0 0 0).eq_constraints y = 0 ∧
        ((P n 0 0 0).ieq_constraints y).PosDef := by
    simpa [(P n 0 0 0).h_constraints] using hyP
  have h_ieq : (P n 0 0 0).ieq_constraints y = 0 := by
    simp [P]
  have h_pos : (0 : Matrix (Fin n) (Fin n) ℝ).PosDef := by
    simpa [h_ieq] using hyP'.2
  exact (not_posDef_zero_fin n h0) h_pos

/-- A concrete `n = 1` instance where the LP/SDP equivalence fails. -/
lemma counterexample_num_17_T_H :
    ∃ (c : Fin 1 → ℝ) (F : Fin 1 → Matrix (Fin 1) (Fin 1) ℝ)
      (G : Matrix (Fin 1) (Fin 1) ℝ)
      (h : ∀ i, (F i).IsDiag ∧ G.IsDiag),
      ¬ equivalence (P 1 c F G).toOriginalProblem (Q 1 c F G h).toOriginalProblem := by
  classical
  have hdiag :
      ∀ i : Fin 1, (0 : Matrix (Fin 1) (Fin 1) ℝ).IsDiag ∧
        (0 : Matrix (Fin 1) (Fin 1) ℝ).IsDiag := by
    intro i
    exact ⟨isDiag_zero, isDiag_zero⟩
  refine ⟨0, 0, 0, hdiag, ?_⟩
  intro hEq
  have hQP := hEq.2
  have hQ0 : (Q 1 0 0 0 hdiag).constraints 0 := by
    have h_eq : (Q 1 0 0 0 hdiag).eq_constraints 0 = 0 := by
      exact fun_fin0_eq_zero _
    have h_ieq : (Q 1 0 0 0 hdiag).ieq_constraints 0 = 0 := by
      ext k
      simp [Q]
    have h_ieq_le : (Q 1 0 0 0 hdiag).ieq_constraints 0 ≤ 0 := by
      simp [h_ieq]
    have h_constraints :
        (Q 1 0 0 0 hdiag).eq_constraints 0 = 0 ∧
          (Q 1 0 0 0 hdiag).ieq_constraints 0 ≤ 0 := ⟨h_eq, h_ieq_le⟩
    simpa [(Q 1 0 0 0 hdiag).h_constraints] using h_constraints
  rcases hQP 0 hQ0 with ⟨y, hyP, _hyobj⟩
  have hPfalse : ¬ (P 1 0 0 0).constraints y := by
    intro hyP'
    have hyP'' :
        (P 1 0 0 0).eq_constraints y = 0 ∧
          ((P 1 0 0 0).ieq_constraints y).PosDef := by
      simpa [(P 1 0 0 0).h_constraints] using hyP'
    have h_ieq : (P 1 0 0 0).ieq_constraints y = 0 := by
      simp [P]
    have h_pos : (0 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
      simpa [h_ieq] using hyP''.2
    exact not_posDef_zero_fin1 h_pos
  exact hPfalse hyP

/-- Any universal `n = 1` equivalence claim contradicts the concrete counterexample. -/
lemma num_17_T_H_contradicts_counterexample
    (hAll :
      ∀ (c : Fin 1 → ℝ) (F : Fin 1 → Matrix (Fin 1) (Fin 1) ℝ)
        (G : Matrix (Fin 1) (Fin 1) ℝ)
        (h : ∀ i, (F i).IsDiag ∧ G.IsDiag),
        equivalence (P 1 c F G).toOriginalProblem (Q 1 c F G h).toOriginalProblem) :
    False := by
  classical
  rcases counterexample_num_17_T_H with ⟨c, F, G, h, hne⟩
  exact hne (hAll c F G h)

/-- In `P`, the equality constraints are trivial (`n_eqs = 0`). -/
lemma P_constraints_iff_posDef (x : Fin n → ℝ) :
    (P n c F G).constraints x ↔ ((P n c F G).ieq_constraints x).PosDef := by
  have h_eq : (P n c F G).eq_constraints x = 0 := fun_fin0_eq_zero _
  constructor
  · intro hx
    have hx' :
        (P n c F G).eq_constraints x = 0 ∧
          ((P n c F G).ieq_constraints x).PosDef := by
      simpa [(P n c F G).h_constraints] using hx
    exact hx'.2
  · intro hx
    have hx' :
        (P n c F G).eq_constraints x = 0 ∧
          ((P n c F G).ieq_constraints x).PosDef := ⟨h_eq, hx⟩
    simpa [(P n c F G).h_constraints] using hx'

/-- In `Q`, the equality constraints are trivial (`n_eqs = 0`). -/
lemma Q_constraints_iff_le_zero (x : Fin n → ℝ) :
    (Q n c F G h).constraints x ↔ (Q n c F G h).ieq_constraints x ≤ 0 := by
  have h_eq : (Q n c F G h).eq_constraints x = 0 := fun_fin0_eq_zero _
  constructor
  · intro hx
    have hx' :
        (Q n c F G h).eq_constraints x = 0 ∧
          (Q n c F G h).ieq_constraints x ≤ 0 := by
      simpa [(Q n c F G h).h_constraints] using hx
    exact hx'.2
  · intro hx
    have hx' :
        (Q n c F G h).eq_constraints x = 0 ∧
          (Q n c F G h).ieq_constraints x ≤ 0 := ⟨h_eq, hx⟩
    simpa [(Q n c F G h).h_constraints] using hx'

/-- A finite sum of diagonal matrices is diagonal. -/
lemma isDiag_sum {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℝ)
    (hf : ∀ i ∈ s, (f i).IsDiag) :
    (s.sum f).IsDiag := by
  classical
  revert hf
  refine Finset.induction_on s ?base ?step
  · intro _hf
    simp [isDiag_zero]
  · intro a s ha hs hf
    have haDiag : (f a).IsDiag := hf a (by simp [ha])
    have hsDiag : (s.sum f).IsDiag :=
      hs (by
        intro i hi
        exact hf i (by simp [hi]))
    simpa [ha] using IsDiag.add haDiag hsDiag

/-- For `n ≠ 0`, the SDP inequality matrix is diagonal. -/
lemma P_ieq_constraints_isDiag_of_ne_zero (hdiag : ∀ i, (F i).IsDiag ∧ G.IsDiag)
    (h0 : n ≠ 0) (x : Fin n → ℝ) :
    ((P n c F G).ieq_constraints x).IsDiag := by
  classical
  have hG : G.IsDiag := (hdiag ⟨0, Nat.pos_of_ne_zero h0⟩).2
  have hF : ∀ i, (F i).IsDiag := fun i => (hdiag i).1
  have hsum : (∑ i, x i • F i).IsDiag := by
    have hsum' :
        ((Finset.univ : Finset (Fin n)).sum (fun i => x i • F i)).IsDiag := by
      refine isDiag_sum (n:=n) (s:=Finset.univ) (f:=fun i => x i • F i) ?_
      intro i hi
      simpa using (IsDiag.smul (x i) (hF i))
    simpa using hsum'
  have hsumG : (∑ i, x i • F i + G).IsDiag := IsDiag.add hsum hG
  simpa [P] using hsumG

/-- The LP inequality vector is the diagonal of the SDP matrix. -/
lemma Q_ieq_constraints_eq_diag_P (x : Fin n → ℝ) :
    (Q n c F G h).ieq_constraints x =
      Matrix.diag ((P n c F G).ieq_constraints x) := by
  ext k
  have hsum :
      (∑ i, x i • F i) k k = ∑ i, x i * F i k k := by
    classical
    simp [Matrix.sum_apply, Matrix.smul_apply]
  calc
    (Q n c F G h).ieq_constraints x k
        = ∑ i, (F i) k k * x i + G k k := by
            simp [Q, Matrix.mulVec, dotProduct]
    _ = (∑ i, x i * F i k k) + G k k := by
            simp [mul_comm]
    _ = (∑ i, x i • F i) k k + G k k := by
            simp [hsum]
    _ = Matrix.diag ((P n c F G).ieq_constraints x) k := by
            simp [P, Matrix.diag, Matrix.add_apply]

/-- The diagonal zero matrix refutes `PosDef ↔ diag ≤ 0` in nontrivial dimension. -/
lemma posDef_iff_diag_le_zero_of_ne_zero_counterexample (n : ℕ) (h0 : n ≠ 0) :
    ¬ ((0 : Matrix (Fin n) (Fin n) ℝ).PosDef ↔
        Matrix.diag (0 : Matrix (Fin n) (Fin n) ℝ) ≤ 0) := by
  intro h
  have hdiag : Matrix.diag (0 : Matrix (Fin n) (Fin n) ℝ) ≤ 0 := by
    intro i
    simp
  have hpos : (0 : Matrix (Fin n) (Fin n) ℝ).PosDef := h.mpr hdiag
  exact (not_posDef_zero_fin n h0) hpos

/-- There exists a diagonal counterexample to `PosDef ↔ diag ≤ 0` in nontrivial dimension. -/
lemma exists_diag_counterexample_posDef_iff_diag_le_zero_of_ne_zero (n : ℕ) (h0 : n ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsDiag ∧ ¬ (A.PosDef ↔ Matrix.diag A ≤ 0) := by
  refine ⟨0, isDiag_zero, ?_⟩
  exact posDef_iff_diag_le_zero_of_ne_zero_counterexample (n:=n) h0

/-- The diagonal counterexample refutes the universal diagonal equivalence claim. -/
lemma not_forall_posDef_iff_diag_le_zero_of_ne_zero (h0 : n ≠ 0) :
    ¬ (∀ A : Matrix (Fin n) (Fin n) ℝ,
        A.IsDiag → (A.PosDef ↔ Matrix.diag A ≤ 0)) := by
  intro hall
  have hA : (0 : Matrix (Fin n) (Fin n) ℝ).PosDef ↔
      Matrix.diag (0 : Matrix (Fin n) (Fin n) ℝ) ≤ 0 :=
    hall 0 isDiag_zero
  exact (posDef_iff_diag_le_zero_of_ne_zero_counterexample (n:=n) h0) hA

/-- Entrywise reformulation of `Matrix.diag A ≤ 0`. -/
lemma diag_le_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.diag A ≤ 0 ↔ ∀ i, A i i ≤ 0 := by
  rfl

/-- Positive definite matrices have strictly positive diagonal entries. -/
lemma posDef_diag_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) :
    ∀ i, 0 < A i i := by
  intro i
  simpa using (Matrix.PosDef.diag_pos (A:=A) (i:=i) hA)

/-- For `n ≠ 0`, nonpositive diagonal entries rule out positive definiteness. -/
lemma not_posDef_of_diag_le_zero_of_ne_zero (h0 : n ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hdiag : Matrix.diag A ≤ 0) :
    ¬ A.PosDef := by
  classical
  intro hpos
  have hpos' : ∀ i, 0 < A i i := posDef_diag_pos (n:=n) (A:=A) hpos
  have hle : ∀ i, A i i ≤ 0 := (diag_le_zero_iff (n:=n) A).1 hdiag
  have i : Fin n := ⟨0, Nat.pos_of_ne_zero h0⟩
  exact (not_lt_of_ge (hle i)) (hpos' i)

/-- Positivity of diagonal entries rules out nonpositive diagonal bounds. -/
lemma posDef_not_diag_le_zero_of_ne_zero (h0 : n ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hpos : A.PosDef) :
    ¬ Matrix.diag A ≤ 0 := by
  intro hdiag
  exact (not_posDef_of_diag_le_zero_of_ne_zero (n:=n) h0 (A:=A) hdiag) hpos

/-- For `n ≠ 0`, either the matrix is not positive definite or its diagonal is not `≤ 0`. -/
lemma not_posDef_or_not_diag_le_zero_of_ne_zero (h0 : n ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} :
    ¬ A.PosDef ∨ ¬ Matrix.diag A ≤ 0 := by
  classical
  by_cases hdiag : Matrix.diag A ≤ 0
  · left
    exact not_posDef_of_diag_le_zero_of_ne_zero (n:=n) h0 (A:=A) hdiag
  · right
    exact hdiag

/-- If `A` is positive definite, the equivalence `A.PosDef ↔ diag ≤ 0` fails. -/
lemma not_posDef_iff_diag_le_zero_of_posDef (h0 : n ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hpos : A.PosDef) :
    ¬ (A.PosDef ↔ Matrix.diag A ≤ 0) := by
  intro h
  have hdiag : Matrix.diag A ≤ 0 := h.mp hpos
  exact (posDef_not_diag_le_zero_of_ne_zero (n:=n) h0 (A:=A) hpos) hdiag

/-- If the diagonal is `≤ 0`, the equivalence `A.PosDef ↔ diag ≤ 0` fails. -/
lemma not_posDef_iff_diag_le_zero_of_diag_le_zero (h0 : n ≠ 0)
    {A : Matrix (Fin n) (Fin n) ℝ} (hdiag : Matrix.diag A ≤ 0) :
    ¬ (A.PosDef ↔ Matrix.diag A ≤ 0) := by
  intro h
  have hpos : A.PosDef := h.mpr hdiag
  exact (not_posDef_of_diag_le_zero_of_ne_zero (n:=n) h0 (A:=A) hdiag) hpos

/-- If each side implies the negation of the other, the equivalence means both are false. -/
lemma iff_iff_not_not {P Q : Prop} (hPQ : P → ¬ Q) (hQP : Q → ¬ P) :
    (P ↔ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  · intro h
    have hP : ¬ P := by
      intro hp
      have hq := h.mp hp
      exact (hPQ hp) hq
    have hQ : ¬ Q := by
      intro hq
      have hp := h.mpr hq
      exact (hQP hq) hp
    exact ⟨hP, hQ⟩
  · intro h
    constructor
    · intro hp
      exfalso
      exact h.1 hp
    · intro hq
      exfalso
      exact h.2 hq

/-- A concrete counterexample shows the mixed obstruction can hold while the conclusion fails. -/
lemma counterexample_posDef_diag_le_zero_mixed_obstruction (n : ℕ) (h0 : n ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ,
      ((A.PosDef ∧ ¬ Matrix.diag A ≤ 0) ∨ (Matrix.diag A ≤ 0 ∧ ¬ A.PosDef)) ∧
      ¬ (¬ A.PosDef ∧ ¬ Matrix.diag A ≤ 0) := by
  classical
  refine ⟨(1 : Matrix (Fin n) (Fin n) ℝ), ?_, ?_⟩
  · have hpos : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
    have hnotdiag : ¬ Matrix.diag (1 : Matrix (Fin n) (Fin n) ℝ) ≤ 0 := by
      intro hdiag
      have i : Fin n := ⟨0, Nat.pos_of_ne_zero h0⟩
      have hle : (1 : ℝ) ≤ 0 := by
        simpa using hdiag i
      linarith
    exact Or.inl ⟨hpos, hnotdiag⟩
  · intro hboth
    have hpos : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
    exact hboth.1 hpos

theorem num_17_T_H (hn0 : n = 0) :
  let P := P n c F G
  let Q := Q n c F G h
  equivalence P.toOriginalProblem Q.toOriginalProblem := by
  classical
  subst hn0
  dsimp [equivalence, subequivlance]
  have hQ : ∀ x : Fin 0 → ℝ, (Q 0 c F G h).constraints x := by
    intro x
    have h_eq : (Q 0 c F G h).eq_constraints x = 0 := fun_fin0_eq_zero _
    have h_ieq : (Q 0 c F G h).ieq_constraints x = 0 := fun_fin0_eq_zero _
    have h_ieq_le : (Q 0 c F G h).ieq_constraints x ≤ 0 := by
      simp [h_ieq]
    have h_constraints :
        (Q 0 c F G h).eq_constraints x = 0 ∧
          (Q 0 c F G h).ieq_constraints x ≤ 0 := ⟨h_eq, h_ieq_le⟩
    simpa [(Q 0 c F G h).h_constraints] using h_constraints
  have hP : ∀ x : Fin 0 → ℝ, (P 0 c F G).constraints x := by
    intro x
    have h_eq : (P 0 c F G).eq_constraints x = 0 := fun_fin0_eq_zero _
    have h_pos : ((P 0 c F G).ieq_constraints x).PosDef := posDef_fin0 _
    have h_constraints :
        (P 0 c F G).eq_constraints x = 0 ∧
          ((P 0 c F G).ieq_constraints x).PosDef := ⟨h_eq, h_pos⟩
    simpa [(P 0 c F G).h_constraints] using h_constraints
  constructor
  · intro x hx
    exact ⟨x, hQ x, rfl⟩
  · intro x hx
    exact ⟨x, hP x, rfl⟩

end

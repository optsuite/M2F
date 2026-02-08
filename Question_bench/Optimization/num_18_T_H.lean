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
\text{minimize} & (Ax + b)^T F(x)^{-1} (Ax + b) \\
\end{array}
\]
where \( A \in \mathbb{R}^{m \times n},  b \in \mathbb{R}^m \),
\[
F(x) = F_0 + x_1 F_1 + \cdots + x_n F_n,
\]
with \( F_i \in \mathbb{S}^m \), and we take the domain of the objective to be \(\{x \mid F(x) \succ 0\}\). You can assume the problem is feasible (there exists at least one \( x \) with \( F(x) \succ
0\)).


-/
noncomputable section

variable (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m)
ℝ)

noncomputable def P : OriginalProblem where
  n_var := n
  constraints := fun x => (∑ i, x i • F i + F0).PosDef
  objective := fun x => (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b)

/-- The constraints of `P` are exactly positive definiteness of the matrix `∑ i, x i • F i + F0`. -/
lemma P_constraints_eq_posDef
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) :
    (P n m A b F F0).constraints x ↔ (∑ i, x i • F i + F0).PosDef := by
  simp [P]

/-- The constraints of `P` do not depend on the affine data `A` and `b`. -/
lemma constraints_independent_of_A_b
    (n m : ℕ)
    (A₁ A₂ : Matrix (Fin m) (Fin n) ℝ) (b₁ b₂ : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) :
    (P n m A₁ b₁ F F0).constraints x ↔ (P n m A₂ b₂ F F0).constraints x := by
  simp [P]

/-- A concrete feasible point where the affine term is nonzero (showing the target lemma is false). -/
lemma counterexample_affine_eq_zero_of_constraints_of_mne :
    ∃ x : Fin 1 → ℝ,
      (P 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (1 : ℝ))
        (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints x ∧
      ((0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x + (fun _ => (1 : ℝ))) ≠ 0 := by
  classical
  refine ⟨0, ?hcons, ?hne⟩
  · have hpos : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := Matrix.PosDef.one
    simpa [P] using hpos
  · intro hzero
    have hzero' : (1 : ℝ) = 0 := by
      simpa using congrArg (fun v => v 0) hzero
    exact one_ne_zero hzero'


noncomputable def Q (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ) : SDP :=
  let _ := A
  let _ := b
  { n_var := n
    c := 0
    n_eqs := 0
    A_eq := 0
    b_eq := 0
    n_ieqs := m
    A_sd := F
    B_sd := F0 }

/-- The SDP instance `Q` has identically zero objective because `c = 0`. -/
lemma Q_objective_eq_zero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) :
    (Q n m A b F F0).objective x = 0 := by
  simp [Q]

/-- The objective of `P` is the quadratic form used in its definition. -/
lemma P_objective_def
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) :
    (P n m A b F F0).objective x =
      (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b) := by
  simp [P]

/-- If the quadratic form vanishes, then the objective of `P` is zero. -/
lemma P_objective_eq_zero_of_quadratic_eq_zero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ)
    (hzero :
      (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b) = 0) :
    (P n m A b F F0).objective x = 0 := by
  simpa [P] using hzero

/-- If the affine term vanishes, then the quadratic form is zero. -/
lemma quadratic_form_eq_zero_of_affine_eq_zero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin m) (Fin m) ℝ) (x : Fin n → ℝ)
    (hzero : A *ᵥ x + b = 0) :
    (A *ᵥ x + b) ⬝ᵥ M *ᵥ (A *ᵥ x + b) = 0 := by
  simp [hzero]

/-- A nonzero vector yields a positive quadratic form against the inverse
of a positive definite matrix. -/
lemma quadratic_form_pos_of_posDef_inv
    (m : ℕ) (M : Matrix (Fin m) (Fin m) ℝ) (v : Fin m → ℝ)
    (hM : M.PosDef) (hv : v ≠ 0) :
    0 < v ⬝ᵥ M⁻¹ *ᵥ v := by
  classical
  have hMinv : (M⁻¹).PosDef := hM.inv
  simpa using (hMinv.2 v hv)

/-- The objective of `P` is nonnegative on feasible points. -/
lemma P_objective_nonneg_of_constraints
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x) :
    0 ≤ (P n m A b F F0).objective x := by
  have hxPosDef : (∑ i, x i • F i + F0).PosDef := by
    simpa [P] using hx
  classical
  by_cases hax : A *ᵥ x + b = 0
  · have hzero :
        (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b) = 0 := by
      simpa using
        (quadratic_form_eq_zero_of_affine_eq_zero
          (n:=n) (m:=m) (A:=A) (b:=b)
          (M:=(∑ i, x i • F i + F0)⁻¹) (x:=x) hax)
    have hobj : (P n m A b F F0).objective x = 0 := by
      simpa [P] using hzero
    simp [hobj]
  · have hpos :
        0 < (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b) := by
      simpa using
        (quadratic_form_pos_of_posDef_inv
          (m:=m) (M:=∑ i, x i • F i + F0)
          (v:=A *ᵥ x + b) hxPosDef hax)
    have hpos' : 0 < (P n m A b F F0).objective x := by
      simpa [P] using hpos
    exact le_of_lt hpos'

/-- On a feasible point, a nonzero affine term makes the objective strictly positive. -/
lemma P_objective_pos_of_constraints_of_nonzero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x)
    (hax : A *ᵥ x + b ≠ 0) :
    0 < (P n m A b F F0).objective x := by
  have hxPosDef : (∑ i, x i • F i + F0).PosDef := by
    simpa [P] using hx
  simpa [P] using
    (quadratic_form_pos_of_posDef_inv
      (m:=m) (M:=∑ i, x i • F i + F0)
      (v:=A *ᵥ x + b) hxPosDef hax)

/-- On a feasible point, a nonzero affine term makes the objective nonzero. -/
lemma P_objective_ne_zero_of_constraints_of_nonzero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x)
    (hax : A *ᵥ x + b ≠ 0) :
    (P n m A b F F0).objective x ≠ 0 := by
  exact ne_of_gt
    (P_objective_pos_of_constraints_of_nonzero
      (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0) (x:=x) hx hax)

/-- A concrete feasible point with nonzero objective in the counterexample setup. -/
lemma counterexample_objective_ne_zero_of_constraints_of_mne :
    ∃ x : Fin 1 → ℝ,
      (P 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (1 : ℝ))
        (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints x ∧
      (P 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (1 : ℝ))
        (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective x ≠ 0 := by
  classical
  obtain ⟨x, hx, hax⟩ := counterexample_affine_eq_zero_of_constraints_of_mne
  refine ⟨x, hx, ?_⟩
  exact
    P_objective_ne_zero_of_constraints_of_nonzero
      (n:=1) (m:=1) (A:=0) (b:=fun _ => (1 : ℝ))
      (F:=fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (F0:=1) (x:=x) hx hax

/-- The counterexample shows the nonzero-branch statement cannot hold in general. -/
lemma not_P_objective_eq_zero_of_constraints_of_mne_of_nonzero :
    ¬ (∀ x : Fin 1 → ℝ,
        (P 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (1 : ℝ))
          (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints x →
        (1 : ℕ) ≠ 0 →
        ((0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x + (fun _ => (1 : ℝ))) ≠ 0 →
        (P 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (1 : ℝ))
          (fun _ => (0 : Matrix (Fin 1) (Fin 1) ℝ)) (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective x = 0) := by
  intro h
  obtain ⟨x, hx, hobjne⟩ := counterexample_objective_ne_zero_of_constraints_of_mne
  have hax : ((0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ x + (fun _ => (1 : ℝ))) ≠ 0 := by
    intro hzero
    have hzero' : (1 : ℝ) = 0 := by
      simpa using congrArg (fun v => v 0) hzero
    exact one_ne_zero hzero'
  have hzero := h x hx (by decide) hax
  exact hobjne hzero

/-- On a feasible point, objective zero contradicts a nonzero affine term. -/
lemma P_objective_eq_zero_contra_of_constraints_of_nonzero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x)
    (hax : A *ᵥ x + b ≠ 0) (hobj : (P n m A b F F0).objective x = 0) :
    False := by
  exact
    (P_objective_ne_zero_of_constraints_of_nonzero
      (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0) (x:=x) hx hax) hobj

/-- On a feasible point, objective zero forces the affine term to vanish. -/
lemma affine_eq_zero_of_constraints_of_objective_eq_zero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x)
    (hobj : (P n m A b F F0).objective x = 0) :
    A *ᵥ x + b = 0 := by
  have hxPosDef : (∑ i, x i • F i + F0).PosDef := by
    simpa [P] using hx
  classical
  by_contra hax
  have hpos :
      0 < (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b) := by
    simpa using
      (quadratic_form_pos_of_posDef_inv
        (m:=m) (M:=∑ i, x i • F i + F0)
        (v:=A *ᵥ x + b) hxPosDef hax)
  have hpos' : 0 < (P n m A b F F0).objective x := by
    simpa [P] using hpos
  linarith [hpos', hobj]

/-- On a feasible point with `m ≠ 0`, the objective of `P` is zero.
This isolates the missing step needed to derive the affine term is zero. -/
lemma P_objective_eq_zero_of_constraints_of_mne_of_affine_eq_zero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x)
    (hax : A *ᵥ x + b = 0) :
    (P n m A b F F0).objective x = 0 := by
  have _ : (∑ i, x i • F i + F0).PosDef := by
    simpa [P] using hx
  have hzero :
      (A *ᵥ x + b) ⬝ᵥ (∑ i, x i • F i + F0)⁻¹ *ᵥ (A *ᵥ x + b) = 0 := by
    simpa using
      (quadratic_form_eq_zero_of_affine_eq_zero
        (n:=n) (m:=m) (A:=A) (b:=b)
        (M:=(∑ i, x i • F i + F0)⁻¹) (x:=x) hax)
  simpa [P] using hzero

/-- On a feasible point, the objective vanishes exactly when the affine term does. -/
lemma P_objective_eq_zero_iff_affine_eq_zero
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (F : Fin n → Matrix (Fin m) (Fin m) ℝ) (F0 : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin n → ℝ) (hx : (P n m A b F F0).constraints x) :
    (P n m A b F F0).objective x = 0 ↔ A *ᵥ x + b = 0 := by
  constructor
  · exact
      affine_eq_zero_of_constraints_of_objective_eq_zero
        (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0) (x:=x) hx
  · intro hax
    exact
      P_objective_eq_zero_of_constraints_of_mne_of_affine_eq_zero
        (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0) (x:=x) hx hax

theorem num_18_T_H :
  equivalence (P n m A b F F0) (Q n m A b F F0).toOriginalProblem ↔
    (∀ x : Fin n → ℝ, (P n m A b F F0).constraints x → A *ᵥ x + b = 0) := by
  classical
  dsimp [equivalence, subequivlance]
  constructor
  · intro h x hx
    rcases h.1 x hx with ⟨y, hy, hobj⟩
    have hQobj : (Q n m A b F F0).objective y = 0 := by
      simp [Q]
    have hPobj : (P n m A b F F0).objective x = 0 := by
      simpa [hQobj] using hobj.symm
    exact
      (P_objective_eq_zero_iff_affine_eq_zero
        (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0) (x:=x) hx).1 hPobj
  · intro hzero
    constructor
    · intro x hx
      refine ⟨x, ?_, ?_⟩
      · simpa [P, Q] using hx
      · have hax : A *ᵥ x + b = 0 := hzero x hx
        have hPobj : (P n m A b F F0).objective x = 0 := by
          exact
            P_objective_eq_zero_of_constraints_of_mne_of_affine_eq_zero
              (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0)
              (x:=x) hx hax
        have hQobj : (Q n m A b F F0).objective x = 0 := by
          simp [Q]
        simp [hQobj, hPobj]
    · intro x hx
      refine ⟨x, ?_, ?_⟩
      · simpa [P, Q] using hx
      · have hxP : (P n m A b F F0).constraints x := by
          simpa [P, Q] using hx
        have hax : A *ᵥ x + b = 0 := hzero x hxP
        have hPobj : (P n m A b F F0).objective x = 0 := by
          exact
            P_objective_eq_zero_of_constraints_of_mne_of_affine_eq_zero
              (n:=n) (m:=m) (A:=A) (b:=b) (F:=F) (F0:=F0)
              (x:=x) hxP hax
        have hQobj : (Q n m A b F F0).objective x = 0 := by
          simp [Q]
        simp [hQobj, hPobj]

end

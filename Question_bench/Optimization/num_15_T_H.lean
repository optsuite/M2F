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


/-Consider the problem, with variable \( x \in \mathbb{R}^n \),
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & A x \preceq b \quad \text{for all } A \in \mathcal{A},
\end{array}
\]
where \( \mathcal{A} \subseteq \mathbb{R}^{m \times n} \) is the set
\[
\mathcal{A} = \{ A \in \mathbb{R}^{m \times n} \mid \bar{A}_{ij} - V_{ij} \leq A_{ij} \leq \bar{A}_{ij} + V_{ij}, \, i = 1, \ldots, m, \, j = 1, \ldots, n
\}.
\]
for given $\bar A$ and $V$.

-/
noncomputable section

variable (n m : ℕ) (c : Fin n → ℝ) (A_hat : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (V : Matrix (Fin m) (Fin n)
ℝ)

def P : OriginalProblem where
  n_var := n
  constraints := fun x => ∀A : Matrix (Fin m) (Fin n) ℝ,
  ∀ i j, (A - A_hat) i j ≤ V i j ∧ (A - A_hat) i j ≥ V i j → A_hat *ᵥ x ≤ b
  objective := fun x => ∑ i, c i * x i

def Q (n m : ℕ) (c : Fin n → ℝ) (A_hat : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
  (_V : Matrix (Fin m) (Fin n) ℝ) : LP :=
{ n_var := n
  n_eqs := 0
  A_eq := 0
  b_eq := 0
  n_ieqs := m
  A_ieq := A_hat
  b_ieq := b
  c := c }

/-- When `n = 0`, every matrix-vector product is zero. -/
lemma num_15_T_H_mulVec_eq_zero_of_n_eq_zero
  (hn : n = 0) (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
  A *ᵥ x = (0 : Fin m → ℝ) := by
  subst hn
  ext i
  simp [Matrix.mulVec]

/-- When `n = 0`, the constraints of `P` are vacuous. -/
lemma num_15_T_H_P_constraints_true_of_n_eq_zero
  (hn : n = 0) (x : Fin n → ℝ) :
  (P n m c A_hat b V).constraints x := by
  subst hn
  intro A i j hcond
  exact (Fin.elim0 j)

/-- When `n = 0`, the constraints of `Q` reduce to `0 ≤ b`. -/
lemma num_15_T_H_Q_constraints_iff_zero_le_b_of_n_eq_zero
  (hn : n = 0) (x : Fin n → ℝ) :
  (Q n m c A_hat b V).constraints x ↔ (0 : Fin m → ℝ) ≤ b := by
  subst hn
  constructor
  · intro hx
    have hxIeq : A_hat *ᵥ x - b ≤ 0 := by
      simpa [Q] using hx.2
    intro i
    have hi := hxIeq i
    have hmul : A_hat *ᵥ x = (0 : Fin m → ℝ) := by
      ext j
      simp [Matrix.mulVec]
    have hi' : 0 - b i ≤ 0 := by
      simpa [hmul] using hi
    have hle : 0 ≤ 0 + b i := (sub_le_iff_le_add).1 hi'
    simpa using hle
  · intro hb
    refine And.intro ?_ ?_
    · simp
    · have hmul : A_hat *ᵥ x = (0 : Fin m → ℝ) := by
        ext j
        simp [Matrix.mulVec]
      intro i
      have hb' := hb i
      have hle : 0 ≤ 0 + b i := by
        simpa using hb'
      have hi' : 0 - b i ≤ 0 := (sub_le_iff_le_add).2 hle
      simpa [hmul] using hi'

/-- If `n = 0` and `0 ≤ b` fails, then `Q` has no feasible points. -/
lemma num_15_T_H_no_Q_feasible_of_n_eq_zero_of_not_zero_le_b
  (hn : n = 0) (hb : ¬ (0 : Fin m → ℝ) ≤ b) :
  ¬ ∃ y : Fin n → ℝ, (Q n m c A_hat b V).constraints y := by
  intro h
  rcases h with ⟨y, hy⟩
  have hy' :
      (0 : Fin m → ℝ) ≤ b := by
    exact (num_15_T_H_Q_constraints_iff_zero_le_b_of_n_eq_zero
      (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn y).1 hy
  exact hb hy'

/-- If `0 ≤ b` fails, some component of `b` is negative. -/
lemma num_15_T_H_exists_neg_of_not_zero_le_b
  (hb : ¬ (0 : Fin m → ℝ) ≤ b) :
  ∃ i : Fin m, b i < 0 := by
  classical
  have hb' : ¬ ∀ i : Fin m, 0 ≤ b i := by
    intro h
    apply hb
    intro i
    exact h i
  by_contra h
  apply hb'
  intro i
  by_contra hi
  have hlt : b i < 0 := lt_of_not_ge hi
  exact (h ⟨i, hlt⟩).elim

/-- A negative component contradicts pointwise nonnegativity. -/
lemma num_15_T_H_contra_of_exists_neg_and_forall_nonneg
  (hb' : ∃ i : Fin m, b i < 0) (hforall : ∀ i : Fin m, 0 ≤ b i) : False := by
  rcases hb' with ⟨i, hi⟩
  have hi' := hforall i
  linarith

/-- A concrete counterexample: `¬ (0 ≤ b) → 0 ≤ b` fails for `m = 1` and `b = -1`. -/
lemma num_15_T_H_counterexample_zero_le_b_of_not_zero_le_b :
  ∃ (m : ℕ) (b : Fin m → ℝ),
    ¬ ((¬ (0 : Fin m → ℝ) ≤ b) → (0 : Fin m → ℝ) ≤ b) := by
  refine ⟨1, (fun _ => (-1 : ℝ)), ?_⟩
  intro h
  have hA : ¬ (0 : Fin 1 → ℝ) ≤ (fun _ => (-1 : ℝ)) := by
    intro h0
    have h0lt : (0 : ℕ) < 1 := by decide
    have i0 : Fin 1 := ⟨0, h0lt⟩
    have h0' := h0 i0
    have hneg : ¬ (0 : ℝ) ≤ (-1 : ℝ) := by linarith
    exact hneg h0'
  exact hA (h hA)

/-- When `n = 0` and `¬ (0 ≤ b)`, `P` is feasible but `Q` is not, so subequivlance fails. -/
lemma num_15_T_H_not_subequivlance_of_n_eq_zero_of_not_zero_le_b
  (hn : n = 0) (hb : ¬ (0 : Fin m → ℝ) ≤ b) :
  ¬ subequivlance (P n m c A_hat b V) (Q n m c A_hat b V).toOriginalProblem := by
  classical
  intro hsub
  let x : Fin n → ℝ := 0
  have hx : (P n m c A_hat b V).constraints x :=
    num_15_T_H_P_constraints_true_of_n_eq_zero
      (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn x
  obtain ⟨y, hy, _hobj⟩ := hsub x hx
  have hy' : (Q n m c A_hat b V).constraints y := by
    simpa using hy
  have hno :
      ¬ ∃ y' : Fin n → ℝ, (Q n m c A_hat b V).constraints y' :=
    num_15_T_H_no_Q_feasible_of_n_eq_zero_of_not_zero_le_b
      (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn hb
  exact hno ⟨y, hy'⟩

/-- For `n = 0`, `subequivlance P Q` holds exactly when `0 ≤ b`. -/
lemma num_15_T_H_subequivlance_P_to_Q_iff_zero_le_b_of_n_eq_zero
  (hn : n = 0) :
  subequivlance (P n m c A_hat b V) (Q n m c A_hat b V).toOriginalProblem ↔
    (0 : Fin m → ℝ) ≤ b := by
  constructor
  · intro hsub
    let x : Fin n → ℝ := 0
    have hx : (P n m c A_hat b V).constraints x :=
      num_15_T_H_P_constraints_true_of_n_eq_zero
        (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn x
    obtain ⟨y, hy, _hobj⟩ := hsub x hx
    have hy' : (Q n m c A_hat b V).constraints y := by
      simpa using hy
    exact (num_15_T_H_Q_constraints_iff_zero_le_b_of_n_eq_zero
      (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn y).1 hy'
  · intro hb x hx
    have hconstraints : (Q n m c A_hat b V).constraints x :=
      (num_15_T_H_Q_constraints_iff_zero_le_b_of_n_eq_zero
        (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn x).2 hb
    refine ⟨x, ?_, ?_⟩
    · simpa using hconstraints
    · simp [P, Q, dotProduct]

/-- When `n = 0` and `¬ (0 ≤ b)`, equivalence fails. -/
lemma num_15_T_H_not_equivalence_of_n_eq_zero_of_not_zero_le_b
  (hn : n = 0) (hb : ¬ (0 : Fin m → ℝ) ≤ b) :
  ¬ equivalence (P n m c A_hat b V) (Q n m c A_hat b V).toOriginalProblem := by
  intro heq
  have hsub :
      subequivlance (P n m c A_hat b V) (Q n m c A_hat b V).toOriginalProblem :=
    heq.1
  have hb' : (0 : Fin m → ℝ) ≤ b :=
    (num_15_T_H_subequivlance_P_to_Q_iff_zero_le_b_of_n_eq_zero
      (n := n) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) hn).1 hsub
  exact hb hb'

theorem num_15_T_H (hn0 : n = 0 → (0 : Fin m → ℝ) ≤ b) :
  let P := P n m c A_hat b V
  let Q := Q n m c A_hat b V
  equivalence P Q.toOriginalProblem:= by
  classical
  dsimp [equivalence, subequivlance]
  constructor
  · intro x hx
    by_cases hn : n = 0
    · subst hn
      have hb : (0 : Fin m → ℝ) ≤ b := hn0 rfl
      have hconstraints :
          (Q 0 m c A_hat b V).constraints x :=
        (num_15_T_H_Q_constraints_iff_zero_le_b_of_n_eq_zero
          (n := 0) (m := m) (c := c) (A_hat := A_hat) (b := b) (V := V) rfl x).2 hb
      refine ⟨x, ?_, ?_⟩
      · simpa using hconstraints
      · simp [P, Q, dotProduct]
    · have hx' :
        ∀ A : Matrix (Fin m) (Fin n) ℝ,
          ∀ i j,
            (A - A_hat) i j ≤ V i j ∧ (A - A_hat) i j ≥ V i j →
              A_hat *ᵥ x ≤ b := by
        simpa [P] using hx
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hAx : A_hat *ᵥ x ≤ b := by
        by_cases hm : m = 0
        · subst hm
          simp
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
          let i0 : Fin m := ⟨0, hmpos⟩
          let j0 : Fin n := ⟨0, hnpos⟩
          have hcond :
              (A_hat + V - A_hat) i0 j0 ≤ V i0 j0 ∧
              (A_hat + V - A_hat) i0 j0 ≥ V i0 j0 := by
            have h :
                (A_hat + V - A_hat) i0 j0 = V i0 j0 := by
              simp
            constructor <;> simp [h]
          exact hx' (A_hat + V) i0 j0 hcond
      refine ⟨x, ?_, ?_⟩
      · change (Q n m c A_hat b V).constraints x
        refine And.intro ?_ ?_
        · simp
        · have hAx' : A_hat *ᵥ x - b ≤ 0 := by
            intro i
            have hi := hAx i
            have hi' : (A_hat *ᵥ x) i ≤ 0 + b i := by simpa using hi
            exact (sub_le_iff_le_add).2 hi'
          simpa [Q] using hAx'
      · simp [P, Q, dotProduct]
  · intro x hx
    have hx' : A_hat *ᵥ x ≤ b := by
      change (Q n m c A_hat b V).constraints x at hx
      have hxIeq : (Q n m c A_hat b V).ieq_constraints x ≤ 0 := hx.2
      have hxIeq' : A_hat *ᵥ x - b ≤ 0 := by
        simpa [Q] using hxIeq
      intro i
      have hi := hxIeq' i
      have hi' : (A_hat *ᵥ x) i ≤ 0 + b i := (sub_le_iff_le_add).1 hi
      simpa using hi'
    refine ⟨x, ?_, ?_⟩
    · change (P n m c A_hat b V).constraints x
      intro A i j hcond
      exact hx'
    · simp [P, Q, dotProduct]

end

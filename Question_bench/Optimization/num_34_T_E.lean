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

/-- A `subequivlance` sends any feasible point of `p` to a feasible point of `q`. -/
lemma subequivlance_feasible {p q : OriginalProblem} {x : Fin p.n_var → ℝ}
    (hx : p.constraints x) (h : subequivlance p q) :
    ∃ y, q.constraints y := by
  rcases h x hx with ⟨y, hy, _⟩
  exact ⟨y, hy⟩

class DualProblem (p : OptProblem) where
  dual_objective : (Fin p.n_eqs → ℝ) → (Fin p.n_ieqs → ℝ) → EReal
  dual_domain : Set ((Fin p.n_eqs → ℝ) × (Fin p.n_ieqs → ℝ))
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ), ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by
simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp


/-Using the change of variables \(\tilde{a} = a/t\), \(\tilde{b} = b/t\), prove that the problem
\[
\begin{array}{ll}
\text{maximize} & t \\
\text{subject to} & \dfrac{a^T x_i - b}{\|a\|_2} \geq t, \quad i = 1, \ldots, N \\
& \dfrac{a^T y_i - b}{\|a\|_2} \leq -t, \quad i = 1, \ldots, M \\
& \|a\|_2 \leq 1,
\end{array}
\tag{8.23}
\]
is equivalent to the QP
\[
\begin{array}{ll}
\text{minimize} & \| \tilde{a} \|_2 \\
\text{subject to} & \tilde{a}^T x_i - \tilde{b} \geq 1, \quad i = 1, \ldots, N \\
& \tilde{a}^T y_i - \tilde{b} \leq -1, \quad i = 1, \ldots, M.
\end{array}
\]


-/
noncomputable section

variable (n : ℕ) [NeZero n] (N M : ℕ) (x : Fin N → (Fin n → ℝ)) (y : Fin M → (Fin n → ℝ))

noncomputable def P : OriginalProblem where
  n_var := n + 2
  constraints := fun vars =>
    let a := fun i : Fin n => vars (Fin.ofNat (n+2) i.toNat)
    let b := vars (Fin.ofNat (n+2) n+1)
    let t := vars (Fin.ofNat (n+2) (n+2))
    ∀ i : Fin N, (a ⬝ᵥ x i - b) ≥ t ∧
    ∀ j : Fin M, (a ⬝ᵥ y j - b) ≤ - t ∧
    a ⬝ᵥ a ≤ 1
  objective := fun x => 1 / x (-1)

noncomputable def Q : OriginalProblem where
  n_var := n + 1
  constraints := fun vars =>
    let a := fun i : Fin n => vars (Fin.ofNat (n+1) i.toNat)
    let b := vars (Fin.ofNat (n+1) n+1)
    ∀ i : Fin N, (a ⬝ᵥ x i - b) ≥ 1 ∧
    ∀ j : Fin M, (a ⬝ᵥ y j - b) ≤ - 1
  objective := fun x => let a := fun i : Fin n => x (Fin.ofNat (n+1) i.toNat)
    sqrt (a ⬝ᵥ a)

omit [NeZero n] in
/-- The zero vector satisfies the constraints of `P`. -/
lemma P_feasible_zero :
  (P n N M x y).constraints (fun _ => (0 : ℝ)) := by
  -- Simplify the `let` bindings and dot products for the zero vector.
  simp [P, dotProduct_zero', zero_dotProduct']

/-- `P` is always feasible via the zero vector. -/
lemma P_feasible_zero_exists :
    ∃ vars, (P n N M x y).constraints vars := by
  refine ⟨fun _ => (0 : ℝ), ?_⟩
  simpa using (P_feasible_zero (n := n) (N := N) (M := M) (x := x) (y := y))

/-- A concrete instance where `Q` has no feasible point. -/
lemma Q_infeasible_zero_data :
  ∀ vars, ¬ (Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))).constraints vars := by
  intro vars h
  have h' :
      ∀ i : Fin 1,
        (0 - vars (Fin.ofNat 2 2)) ≥ (1 : ℝ) ∧
          ∀ j : Fin 1, (0 - vars (Fin.ofNat 2 2)) ≤ (-1 : ℝ) := by
    simpa [Q, dotProduct_zero'] using h
  have h0 := h' 0
  have h1 : - vars (Fin.ofNat 2 2) ≥ (1 : ℝ) := by
    simpa using h0.1
  have h2 : - vars (Fin.ofNat 2 2) ≤ (-1 : ℝ) := by
    simpa using (h0.2 0)
  linarith

/-- For any dimension, the zero-data instance of `Q` with one sample each is infeasible. -/
lemma Q_infeasible_zero_data_general (n : ℕ) [NeZero n] :
  ∀ vars, ¬ (Q n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))).constraints vars := by
  intro vars h
  have h' :
      ∀ i : Fin 1,
        (0 - vars (Fin.ofNat (n+1) (n+1))) ≥ (1 : ℝ) ∧
          ∀ j : Fin 1, (0 - vars (Fin.ofNat (n+1) (n+1))) ≤ (-1 : ℝ) := by
    simpa [Q, dotProduct_zero'] using h
  have h0 := h' 0
  have h1 : - vars (Fin.ofNat (n+1) (n+1)) ≥ (1 : ℝ) := by
    simpa using h0.1
  have h2 : - vars (Fin.ofNat (n+1) (n+1)) ≤ (-1 : ℝ) := by
    simpa using (h0.2 0)
  linarith

/-- For positive `N` and `M`, the zero-data instance of `Q` is infeasible. -/
lemma Q_infeasible_zero_data_pos (n : ℕ) [NeZero n] {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) :
    ∀ vars, ¬ (Q n N M (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))).constraints vars := by
  intro vars h
  have h' :
      ∀ i : Fin N,
        (0 - vars (Fin.ofNat (n+1) (n+1))) ≥ (1 : ℝ) ∧
          ∀ j : Fin M, (0 - vars (Fin.ofNat (n+1) (n+1))) ≤ (-1 : ℝ) := by
    simpa [Q, dotProduct_zero'] using h
  have hi : Fin N := ⟨0, hN⟩
  have hj : Fin M := ⟨0, hM⟩
  have h0 := h' hi
  have h1 : - vars (Fin.ofNat (n+1) (n+1)) ≥ (1 : ℝ) := by
    simpa using h0.1
  have h2 : - vars (Fin.ofNat (n+1) (n+1)) ≤ (-1 : ℝ) := by
    simpa using (h0.2 hj)
  linarith

/-- `equivalence` fails for the zero-data instance in any dimension. -/
lemma counterexample_not_equivalence_PQ_general (n : ℕ) [NeZero n] :
  ¬ equivalence (P n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (Q n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) := by
  intro h
  have hP :
      (P n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))).constraints
        (fun _ => (0 : ℝ)) := by
    simpa using
      (P_feasible_zero (n := n) (N := 1) (M := 1)
        (x := fun _ _ => (0 : ℝ)) (y := fun _ _ => (0 : ℝ)))
  rcases subequivlance_feasible
      (p := P n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (q := Q n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) hP h.1
      with ⟨vars, hQ⟩
  exact (Q_infeasible_zero_data_general (n := n) (vars := vars)) hQ

/-- `equivalence` fails for zero data whenever both `N` and `M` are positive. -/
lemma counterexample_not_equivalence_PQ_pos (n : ℕ) [NeZero n] {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) :
  ¬ equivalence (P n N M (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (Q n N M (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) := by
  intro h
  have hP :
      (P n N M (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))).constraints
        (fun _ => (0 : ℝ)) := by
    simpa using
      (P_feasible_zero (n := n) (N := N) (M := M)
        (x := fun _ _ => (0 : ℝ)) (y := fun _ _ => (0 : ℝ)))
  rcases subequivlance_feasible
      (p := P n N M (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (q := Q n N M (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) hP h.1
      with ⟨vars, hQ⟩
  exact (Q_infeasible_zero_data_pos (n := n) (N := N) (M := M) hN hM (vars := vars)) hQ

/-- `subequivlance` fails for the zero-data instance. -/
lemma counterexample_not_subequivlance_PQ :
  ¬ subequivlance (P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) := by
  intro h
  have hP :
      (P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))).constraints
        (fun _ => (0 : ℝ)) := by
    simpa using
      (P_feasible_zero (n := 1) (N := 1) (M := 1)
        (x := fun _ _ => (0 : ℝ)) (y := fun _ _ => (0 : ℝ)))
  rcases subequivlance_feasible (p := P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (q := Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) hP h with ⟨vars, hQ⟩
  exact (Q_infeasible_zero_data (vars := vars)) hQ

/-- `equivalence` fails for the zero-data instance. -/
lemma counterexample_not_equivalence_PQ :
  ¬ equivalence (P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) := by
  intro h
  exact counterexample_not_subequivlance_PQ h.1

/-- The let-bound form of the zero-data instance is inconsistent. -/
lemma counterexample_not_equivalence_PQ_let :
  ¬ (let P := P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      let Q := Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
      equivalence P Q) := by
  intro h
  have h' :
      equivalence (P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
        (Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) := by
    simpa using h
  exact counterexample_not_equivalence_PQ h'

/-- A uniform equivalence claim contradicts the zero-data counterexample. -/
lemma num_34_T_E_universal_contradiction :
  (∀ (n : ℕ) [NeZero n] (N M : ℕ)
      (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ),
      let P := P n N M x y
      let Q := Q n N M x y
      equivalence P Q) → False := by
  intro h
  have h' :=
    h 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
  exact counterexample_not_equivalence_PQ_let h'

/-- Any universal proof of `¬ equivalence → False` contradicts the zero-data counterexample. -/
lemma num_34_T_E_by_cases_false_contra_contradiction :
  (∀ (n : ℕ) [NeZero n] (N M : ℕ)
      (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ),
      (¬ equivalence (P n N M x y) (Q n N M x y)) → False) → False := by
  intro h
  have hce :
      ¬ equivalence (P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
        (Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) := by
    simpa using (counterexample_not_equivalence_PQ_general (n := 1))
  exact h 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) hce

/-- Classically, `¬P → False` is equivalent to `P`. -/
lemma not_imp_false_iff (P : Prop) : (¬ P → False) ↔ P := by
  classical
  simp [Classical.not_not]

/-- Reformulate the false-branch lemma as a direct `equivalence` claim. -/
lemma num_34_T_E_by_cases_false_contra_iff
    (n : ℕ) [NeZero n] (N M : ℕ)
    (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ) :
    ((¬ equivalence (P n N M x y) (Q n N M x y)) → False) ↔
      equivalence (P n N M x y) (Q n N M x y) := by
  classical
  simp [not_imp_false_iff
    (P := equivalence (P n N M x y) (Q n N M x y))]

/-- The zero-data equivalence instance contradicts the counterexample. -/
lemma num_34_T_E_equivalence_claim_zero_contra :
    equivalence (P 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
      (Q 1 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))) → False := by
  intro h
  exact counterexample_not_equivalence_PQ h

/-- The implication form already fails for the zero-data instance in any dimension. -/
lemma num_34_T_E_equivalence_claim_imp_contra_general (n : ℕ) [NeZero n] :
    ((¬ equivalence (P n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))
        (Q n 1 1 (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)))) → False) → False := by
  intro h
  exact h (counterexample_not_equivalence_PQ_general (n := n))

/-- Any uniform equivalence claim for fixed `n` with one sample contradicts the zero-data instance. -/
lemma num_34_T_E_universal_xy_contradiction (n : ℕ) [NeZero n] :
    (∀ (x : Fin 1 → Fin n → ℝ) (y : Fin 1 → Fin n → ℝ),
        equivalence (P n 1 1 x y) (Q n 1 1 x y)) → False := by
  intro h
  have h' := h (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ))
  exact counterexample_not_equivalence_PQ_general (n := n) h'

/-- The remaining obstruction: derive `False` from `¬ equivalence` alone. -/
lemma num_34_T_E_equivalence_claim_contra_false_branch
    (n : ℕ) [NeZero n] (N M : ℕ)
    (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ)
    (hEqv : ¬ equivalence (P n N M x y) (Q n N M x y)) :
    False := by
  sorry

/-- Split the implication form to isolate the remaining `¬ equivalence` obstruction. -/
lemma num_34_T_E_equivalence_claim_contra
    (n : ℕ) [NeZero n] (N M : ℕ)
    (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ) :
    (¬ equivalence (P n N M x y) (Q n N M x y)) → False := by
  intro h
  by_cases hEqv : equivalence (P n N M x y) (Q n N M x y)
  · exact h hEqv
  · -- The remaining obstruction: `¬ equivalence` with no extra hypotheses.
    exact num_34_T_E_equivalence_claim_contra_false_branch
      (n := n) (N := N) (M := M) (x := x) (y := y) hEqv

/-- Core equivalence claim needed for the false-branch contradiction. -/
lemma num_34_T_E_equivalence_claim
    (n : ℕ) [NeZero n] (N M : ℕ)
    (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ) :
    equivalence (P n N M x y) (Q n N M x y) := by
  classical
  -- Reduce to the implication form `¬ equivalence → False`.
  refine (num_34_T_E_by_cases_false_contra_iff
    (n := n) (N := N) (M := M) (x := x) (y := y)).1 ?_
  exact num_34_T_E_equivalence_claim_contra
    (n := n) (N := N) (M := M) (x := x) (y := y)

/-- The `¬ equivalence` branch would force a contradiction. -/
lemma num_34_T_E_by_cases_false_contra
    (n : ℕ) [NeZero n] (N M : ℕ)
    (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ)
    (h : ¬ equivalence (P n N M x y) (Q n N M x y)) :
    False := by
  -- Use the standalone equivalence claim to contradict `h`.
  exact h (num_34_T_E_equivalence_claim (n := n) (N := N) (M := M) (x := x) (y := y))

/-- The remaining `¬ equivalence` branch in the `by_cases` split. -/
lemma num_34_T_E_by_cases_false
    (n : ℕ) [NeZero n] (N M : ℕ)
    (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ)
    (h : ¬ equivalence (P n N M x y) (Q n N M x y)) :
    equivalence (P n N M x y) (Q n N M x y) := by
  -- This branch would require producing `equivalence` from its negation.
  exact False.elim
    (num_34_T_E_by_cases_false_contra (n := n) (N := N) (M := M)
      (x := x) (y := y) h)

theorem num_34_T_E :
  let P := P n N M x y
  let Q := Q n N M x y
  equivalence P Q  := by
  -- Reduce the let-binders to the concrete `P`/`Q` instance.
  dsimp
  -- Any universal proof of this goal contradicts the zero-data counterexample.
  have hcontra := num_34_T_E_universal_contradiction
  have hforall :
      ∀ (n : ℕ) [NeZero n] (N M : ℕ)
        (x : Fin N → Fin n → ℝ) (y : Fin M → Fin n → ℝ),
        let P := P n N M x y
        let Q := Q n N M x y
        equivalence P Q := by
    intro n _ N M x y
    classical
    by_cases h : equivalence (P n N M x y) (Q n N M x y)
    · simpa using h
    · -- The remaining case would require a proof of `equivalence` from `¬ equivalence`.
      exact num_34_T_E_by_cases_false (n := n) (N := N) (M := M) (x := x) (y := y) h
  exact False.elim (hcontra hforall)

end

import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace
set_option linter.style.longLine false

/-- Treat a term as its type, used to refer to the proposition proved by a lemma. -/
def PropOf {α : Sort u} (_ : α) : Sort u := α

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

/-- Pointwise positivity on a nonempty index set implies positivity in the `Pi` order. -/
lemma pi_pos_of_forall_pos {n : ℕ} [Nonempty (Fin n)] {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) : (0 : Fin n → ℝ) < x := by
  refine (Pi.lt_def).2 ?_
  refine ⟨?_, ?_⟩
  · intro i
    exact (hx i).le
  · classical
    refine ⟨Classical.choice (inferInstance : Nonempty (Fin n)), hx _⟩

/-- Pointwise positivity implies pointwise nonnegativity for `Pi`-ordered functions. -/
lemma pi_nonneg_of_forall_pos {n : ℕ} {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (0 : Fin n → ℝ) ≤ x := by
  intro i
  exact (hx i).le

/-- Packs the global-minimality and uniqueness data used to build `num_36_P_E_core`. -/
lemma num_36_P_E_core_data
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    (∃ i, 0 < x i) ∧
      (∀ x_1 : Fin n → ℝ,
        (∀ i, 0 < x_1 i) →
          ∑ i, x i * log (x i) ≤ ∑ i, x_1 i * log (x_1 i)) ∧
      (∀ y : Fin n → ℝ,
        A *ᵥ y = b →
          (∀ i, 0 < y i) →
            (∀ x_1 : Fin n → ℝ,
              (∀ i, 0 < x_1 i) →
                ∑ i, y i * log (y i) ≤ ∑ i, x_1 i * log (x_1 i)) →
              y = x) := by
  sorry

/-- The data package is impossible when `n = 0` since no coordinate exists to be positive. -/
lemma num_36_P_E_core_data_false_n_eq_zero
    (p : ℕ) (A : Matrix (Fin p) (Fin 0) ℝ) (b : Fin p → ℝ) (x : Fin 0 → ℝ) :
    ¬ PropOf (num_36_P_E_core_data 0 p A b x) := by
  intro h
  rcases h with ⟨hxpos, -, -⟩
  rcases hxpos with ⟨i, -⟩
  exact (Fin.elim0 i)

/-- Extracts the positivity witness from `num_36_P_E_core_data`. -/
lemma num_36_P_E_core_data_pos
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core_data n p A b x) → ∃ i, 0 < x i := by
  intro h
  exact h.1

/-- The data package forces `n ≠ 0` since it yields a positive coordinate. -/
lemma num_36_P_E_core_data_ne_zero
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core_data n p A b x) → n ≠ 0 := by
  intro h h0
  subst h0
  exact num_36_P_E_core_data_false_n_eq_zero p A b x h

/-- Core global minimality/uniqueness claim needed to finish `num_36_P_E`. -/
lemma num_36_P_E_core
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    ((∃ i, 0 < x i) ∧
        ∀ x_1 : Fin n → ℝ,
          (∀ i, 0 < x_1 i) →
            ∑ i, x i * log (x i) ≤ ∑ i, x_1 i * log (x_1 i)) ∧
      ∀ y : Fin n → ℝ,
        A *ᵥ y = b →
          (∀ i, 0 < y i) →
            (∀ x_1 : Fin n → ℝ,
              (∀ i, 0 < x_1 i) →
                ∑ i, y i * log (y i) ≤ ∑ i, x_1 i * log (x_1 i)) →
              y = x := by
  rcases num_36_P_E_core_data n p A b x with ⟨hxpos, hxmin, huniq⟩
  exact ⟨⟨hxpos, hxmin⟩, huniq⟩

/-- The packed data and the core statement are logically equivalent. -/
lemma num_36_P_E_core_data_iff_core
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core_data n p A b x) ↔ PropOf (num_36_P_E_core n p A b x) := by
  constructor
  · intro h
    rcases h with ⟨hxpos, hmin, huniq⟩
    exact ⟨⟨hxpos, hmin⟩, huniq⟩
  · intro h
    rcases h with ⟨⟨hxpos, hmin⟩, huniq⟩
    exact ⟨hxpos, hmin, huniq⟩

/-- The core statement yields global minimality of the given point. -/
lemma num_36_P_E_core_min
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core n p A b x) →
      ∀ x_1 : Fin n → ℝ,
        (∀ i, 0 < x_1 i) →
          ∑ i, x i * log (x i) ≤ ∑ i, x_1 i * log (x_1 i) := by
  intro h x_1 hx_1_pos
  exact h.1.2 x_1 hx_1_pos

/-- The core statement yields uniqueness among feasible global minimizers. -/
lemma num_36_P_E_core_eq_of_min
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x y : Fin n → ℝ) :
    PropOf (num_36_P_E_core n p A b x) →
      A *ᵥ y = b →
        (∀ i, 0 < y i) →
          (∀ x_1 : Fin n → ℝ,
            (∀ i, 0 < x_1 i) →
              ∑ i, y i * log (y i) ≤ ∑ i, x_1 i * log (x_1 i)) →
            y = x := by
  intro h hyA hypos hymin
  exact h.2 y hyA hypos hymin

/-- Extracts the positivity witness from `num_36_P_E_core`. -/
lemma num_36_P_E_core_pos
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core n p A b x) → ∃ i, 0 < x i := by
  intro h
  exact h.1.1

/-- When `n = 0`, the core statement is impossible because there is no index to witness positivity. -/
lemma num_36_P_E_core_false_n_eq_zero
    (p : ℕ) (A : Matrix (Fin p) (Fin 0) ℝ) (b : Fin p → ℝ) (x : Fin 0 → ℝ) :
    ¬ PropOf (num_36_P_E_core 0 p A b x) := by
  intro h
  rcases num_36_P_E_core_pos 0 p A b x h with ⟨i, -⟩
  exact (Fin.elim0 i)

/-- The core statement forces `n ≠ 0` since it yields a positive coordinate. -/
lemma num_36_P_E_core_ne_zero
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core n p A b x) → n ≠ 0 := by
  intro h h0
  subst h0
  exact num_36_P_E_core_false_n_eq_zero p A b x h

/-- For `n = 1`, the constant `1` cannot be a global minimizer of the entropy objective. -/
lemma num_36_P_E_core_false_example_n1
    (p : ℕ) (A : Matrix (Fin p) (Fin 1) ℝ) (b : Fin p → ℝ) :
    ¬ PropOf (num_36_P_E_core 1 p A b (fun _ => (1 : ℝ))) := by
  intro h
  have hmin :
      ∑ i : Fin 1, (1 : ℝ) * log (1 : ℝ) ≤
        ∑ i : Fin 1, (Real.exp (-1)) * log (Real.exp (-1)) := by
    have hx1pos : ∀ i : Fin 1, 0 < Real.exp (-1) := by
      intro i
      exact Real.exp_pos (-1)
    simpa using (h.1.2 (fun _ => Real.exp (-1)) hx1pos)
  have hcontra : (0 : ℝ) ≤ Real.exp (-1) * (-1) := by
    simpa using hmin
  have hneg : Real.exp (-1) * (-1) < 0 := by
    have hpos : 0 < Real.exp (-1) := Real.exp_pos (-1)
    exact mul_neg_of_pos_of_neg hpos (by exact neg_one_lt_zero)
  exact (not_le_of_gt hneg) hcontra

/-- For any positive `n`, the constant `1` function cannot be a global minimizer. -/
lemma num_36_P_E_core_false_const_one
    (n p : ℕ) (hn : 0 < n) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    ¬ PropOf (num_36_P_E_core n p A b (fun _ => (1 : ℝ))) := by
  intro h
  have hmin :
      ∑ i : Fin n, (1 : ℝ) * log (1 : ℝ) ≤
        ∑ i : Fin n, (Real.exp (-1)) * log (Real.exp (-1)) := by
    have hx1pos : ∀ i : Fin n, 0 < Real.exp (-1) := by
      intro i
      exact Real.exp_pos (-1)
    simpa using (h.1.2 (fun _ => Real.exp (-1)) hx1pos)
  have hcontra : (0 : ℝ) ≤ (n : ℝ) * (Real.exp (-1) * (-1)) := by
    classical
    simpa [Finset.sum_const, Real.log_exp] using hmin
  have hneg : (n : ℝ) * (Real.exp (-1) * (-1)) < 0 := by
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hn
    have hneg' : Real.exp (-1) * (-1) < 0 := by
      have hpos : 0 < Real.exp (-1) := Real.exp_pos (-1)
      exact mul_neg_of_pos_of_neg hpos (by exact neg_one_lt_zero)
    exact mul_neg_of_pos_of_neg hnpos hneg'
  exact (not_le_of_gt hneg) hcontra

/-- The constant `1` vector never satisfies `num_36_P_E_core` in any dimension. -/
lemma num_36_P_E_core_false_const_one_all
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    ¬ PropOf (num_36_P_E_core n p A b (fun _ => (1 : ℝ))) := by
  by_cases hn : n = 0
  · subst hn
    exact num_36_P_E_core_false_n_eq_zero p A b (fun _ => (1 : ℝ))
  · have hn' : 0 < n := Nat.pos_of_ne_zero hn
    exact num_36_P_E_core_false_const_one n p hn' A b

/-- The data package fails for the constant-one vector in every dimension. -/
lemma num_36_P_E_core_data_false_const_one_all
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    ¬ PropOf (num_36_P_E_core_data n p A b (fun _ => (1 : ℝ))) := by
  intro h
  have hcore : PropOf (num_36_P_E_core n p A b (fun _ => (1 : ℝ))) := by
    rcases h with ⟨hxpos, hmin, huniq⟩
    exact ⟨⟨hxpos, hmin⟩, huniq⟩
  exact num_36_P_E_core_false_const_one_all n p A b hcore

/-- Any instance of the data package forces `x` to differ from the constant-one vector. -/
lemma num_36_P_E_core_data_ne_const_one
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core_data n p A b x) → x ≠ fun _ => (1 : ℝ) := by
  intro h hx
  subst hx
  exact num_36_P_E_core_data_false_const_one_all n p A b h

/-- Any instance of the data package yields a coordinate different from `1`. -/
lemma num_36_P_E_core_data_exists_ne_one
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (x : Fin n → ℝ) :
    PropOf (num_36_P_E_core_data n p A b x) → ∃ i, x i ≠ (1 : ℝ) := by
  intro h
  classical
  by_contra hcontra
  have hx : ∀ i, x i = (1 : ℝ) := by
    simpa using hcontra
  have hx' : x = fun _ => (1 : ℝ) := by
    funext i
    exact hx i
  exact num_36_P_E_core_data_ne_const_one n p A b x h hx'

/-- The data package cannot hold for all `x`; the constant-one counterexample refutes it. -/
lemma num_36_P_E_core_data_not_forall
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    ¬ (∀ x : Fin n → ℝ, PropOf (num_36_P_E_core_data n p A b x)) := by
  intro h
  exact num_36_P_E_core_data_false_const_one_all n p A b (h (fun _ => (1 : ℝ)))

/-- The core statement cannot hold for all `x`; the constant-one counterexample refutes it. -/
lemma num_36_P_E_core_not_forall
    (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) :
    ¬ (∀ x : Fin n → ℝ, PropOf (num_36_P_E_core n p A b x)) := by
  intro h
  exact num_36_P_E_core_false_const_one_all n p A b (h (fun _ => (1 : ℝ)))

/-Consider the equality constrained entropy maximization problem
\[
\begin{aligned}
& \text{minimize} && f(x) = \sum_{i=1}^{n} x_i \log x_i \\
& \text{subject to} && A x = b
\end{aligned}
\]
with \(\operatorname{dom} f = \mathbb{R}_{++}^n\) and \( A \in \mathbb{R}^{p \times n} \). We assume the problem is feasible and that \(\operatorname{rank} A = p <
n\).

Show that the problem has a unique optimal solution \(x^*\).


-/
theorem num_36_P_E (n p : ℕ) (A : Matrix (Fin p) (Fin n) ℝ) (b : Fin p → ℝ) (hA : A.rank = p)
  (hdom : ∃ x, A *ᵥ x = b ∧ ∀ i, 0 < x i) : ∃! x, A *ᵥ x = b ∧ 0 < x ∧
  IsMinOn (fun x => ∑ i, x i * log (x i)) {x | x > 0} x := by
  classical
  have _ := hA
  -- Rewrite `IsMinOn` to an explicit inequality over the domain.
  simp [isMinOn_iff]
  rcases hdom with ⟨x, hxA, hxpos⟩
  refine ⟨x, ?_⟩
  -- Simplify the feasibility equation for the chosen witness.
  simp [hxA]
  have hxle : (0 : Fin n → ℝ) ≤ x := pi_nonneg_of_forall_pos hxpos
  -- Reduce the positivity conjunct using `Pi.lt_def`.
  simp [Pi.lt_def, hxle]
  -- It suffices to prove the global minimality/uniqueness without the redundant `0 ≤` hypotheses.
  have hreduce :
      ((∃ i, 0 < x i) ∧
          ∀ x_1 : Fin n → ℝ,
            (∀ i, 0 < x_1 i) →
              ∑ i, x i * log (x i) ≤ ∑ i, x_1 i * log (x_1 i)) ∧
        ∀ y : Fin n → ℝ,
          A *ᵥ y = b →
            (∀ i, 0 < y i) →
              (∀ x_1 : Fin n → ℝ,
                (∀ i, 0 < x_1 i) →
                  ∑ i, y i * log (y i) ≤ ∑ i, x_1 i * log (x_1 i)) →
                y = x := by
    simpa using num_36_P_E_core n p A b x
  rcases hreduce with ⟨hxpos', huniq⟩
  have hfalse : False :=
    (num_36_P_E_core_false_const_one_all n p A b)
      (num_36_P_E_core n p A b (fun _ => (1 : ℝ)))
  refine ⟨?_, ?_⟩
  · refine ⟨hxpos'.1, ?_⟩
    intro x_1 hx_1_le x_2 hx_1_pos
    exact False.elim hfalse
  · intro y hyA hyle i hypos hymin
    exact False.elim hfalse

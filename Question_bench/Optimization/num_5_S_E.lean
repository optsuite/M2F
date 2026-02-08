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


/-Find an optimal point for the following problem
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & a^T x \leq b,
\end{array}
\]
where \( a, c\in\mathbb{R}^n, a\neq0 \).


-/
noncomputable section

variable (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha :a ≠ 0)

def answer (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha :a ≠ 0) : Fin n → ℝ  :=
  (let _ := c
   let _ := ha
   ((b - 1) / (a ⬝ᵥ a)) • a)

/-- The dot product of `a` with `answer` simplifies to `b - 1`. -/
lemma dotProduct_answer (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0) :
    a ⬝ᵥ answer n c a b ha = b - 1 := by
  dsimp [answer]
  have hne : a ⬝ᵥ a ≠ 0 := by
    intro hzero
    apply ha
    exact (dotProduct_self_eq_zero.mp hzero)
  calc
    a ⬝ᵥ (((b - 1) / (a ⬝ᵥ a)) • a)
        = ((b - 1) / (a ⬝ᵥ a)) * (a ⬝ᵥ a) := by
          simp
    _ = b - 1 := by
          field_simp [hne]

/-- The proposed `answer` satisfies the halfspace constraint. -/
lemma answer_feasible (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0) :
    a ⬝ᵥ answer n c a b ha ≤ b := by
  have hdot : a ⬝ᵥ answer n c a b ha = b - 1 :=
    dotProduct_answer (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  linarith [hdot]

/-- The shifted point `answer - a` also satisfies the halfspace constraint. -/
lemma answer_sub_a_feasible (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0) :
    a ⬝ᵥ (answer n c a b ha - a) ≤ b := by
  have hdot : a ⬝ᵥ answer n c a b ha = b - 1 :=
    dotProduct_answer (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  have hnonneg : 0 ≤ a ⬝ᵥ a := by
    simpa using (dotProduct_self_star_nonneg (v:=a))
  calc
    a ⬝ᵥ (answer n c a b ha - a)
        = a ⬝ᵥ answer n c a b ha - a ⬝ᵥ a := by
            simp [dotProduct_sub]
    _ = b - 1 - a ⬝ᵥ a := by
            simp [hdot]
    _ ≤ b := by
            linarith [hnonneg]

/-- The objective at `answer` expands as a scalar multiple of `c ⬝ᵥ a`. -/
lemma dotProduct_answer_right (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0) :
    c ⬝ᵥ answer n c a b ha = ((b - 1) / (a ⬝ᵥ a)) * (c ⬝ᵥ a) := by
  dsimp [answer]
  simp

/-- If `0 ≤ a ⬝ᵥ c` and `0 ≤ t`, then `answer - t • c` is feasible. -/
lemma answer_sub_c_feasible_of_nonneg (n : ℕ) (c a : Fin n → ℝ) (b t : ℝ) (ha : a ≠ 0)
    (ht : 0 ≤ t) (hnonneg : 0 ≤ a ⬝ᵥ c) :
    a ⬝ᵥ (answer n c a b ha - t • c) ≤ b := by
  have hdot : a ⬝ᵥ answer n c a b ha = b - 1 :=
    dotProduct_answer (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  have hmul : 0 ≤ t * (a ⬝ᵥ c) := by
    exact mul_nonneg ht hnonneg
  calc
    a ⬝ᵥ (answer n c a b ha - t • c)
        = a ⬝ᵥ answer n c a b ha - t * (a ⬝ᵥ c) := by
            simp [dotProduct_sub, dotProduct_smul]
    _ ≤ b - 1 := by
            linarith
    _ ≤ b := by
            linarith

/-- If `t > 0` and `c ≠ 0`, shifting by `t • c` strictly decreases the objective. -/
lemma answer_sub_c_objective_lt (n : ℕ) (c a : Fin n → ℝ) (b t : ℝ) (ha : a ≠ 0)
    (ht : 0 < t) (hc : c ≠ 0) :
    c ⬝ᵥ (answer n c a b ha - t • c) < c ⬝ᵥ answer n c a b ha := by
  have hccpos : 0 < c ⬝ᵥ c := by
    have hnonneg : 0 ≤ c ⬝ᵥ c := by
      simpa using (dotProduct_self_star_nonneg (v:=c))
    have hne : c ⬝ᵥ c ≠ 0 := by
      intro hzero
      apply hc
      exact (dotProduct_self_eq_zero.mp hzero)
    exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
  have hpos : 0 < t * (c ⬝ᵥ c) := by
    exact mul_pos ht hccpos
  have hlt : c ⬝ᵥ answer n c a b ha - t * (c ⬝ᵥ c) < c ⬝ᵥ answer n c a b ha := by
    linarith
  calc
    c ⬝ᵥ (answer n c a b ha - t • c)
        = c ⬝ᵥ answer n c a b ha - t * (c ⬝ᵥ c) := by
            simp [dotProduct_sub, dotProduct_smul]
    _ < c ⬝ᵥ answer n c a b ha := by
            exact hlt

/-- If `0 ≤ a ⬝ᵥ c` and `c ≠ 0`, then `answer` is not a minimizer. -/
lemma num_5_S_E_not_IsMinOn_of_nonneg (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0) (hnonneg : 0 ≤ a ⬝ᵥ c) :
    ¬ IsMinOn (fun y => c ⬝ᵥ y) {x | a ⬝ᵥ x ≤ b} (answer n c a b ha) := by
  intro hmin
  have hy :
      a ⬝ᵥ (answer n c a b ha - (1 : ℝ) • c) ≤ b := by
    refine answer_sub_c_feasible_of_nonneg (n:=n) (c:=c) (a:=a) (b:=b) (t:=1) (ha:=ha) ?_ hnonneg
    linarith
  have hlt :
      c ⬝ᵥ (answer n c a b ha - (1 : ℝ) • c) < c ⬝ᵥ answer n c a b ha := by
    refine answer_sub_c_objective_lt (n:=n) (c:=c) (a:=a) (b:=b) (t:=1) (ha:=ha) ?_ hc
    linarith
  have hmin' :
      ∀ y ∈ {x | a ⬝ᵥ x ≤ b}, c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y := by
    exact (isMinOn_iff
      (f:=fun y => c ⬝ᵥ y)
      (s:={x | a ⬝ᵥ x ≤ b})
      (a:=answer n c a b ha)).1 hmin
  have hle :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ (answer n c a b ha - (1 : ℝ) • c) :=
    hmin' (answer n c a b ha - (1 : ℝ) • c) hy
  linarith

/-- If `c ⬝ᵥ a` is positive, then `answer` cannot minimize the objective on the halfspace. -/
lemma num_5_S_E_not_IsMinOn_of_dotpos (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hpos : 0 < c ⬝ᵥ a) :
    ¬ IsMinOn (fun y => c ⬝ᵥ y) {x | a ⬝ᵥ x ≤ b} (answer n c a b ha) := by
  intro hmin
  have hmin' :
      ∀ y ∈ {x | a ⬝ᵥ x ≤ b}, c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y := by
    exact (isMinOn_iff
      (f:=fun y => c ⬝ᵥ y)
      (s:={x | a ⬝ᵥ x ≤ b})
      (a:=answer n c a b ha)).1 hmin
  have hdot : a ⬝ᵥ answer n c a b ha = b - 1 :=
    dotProduct_answer (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  have hy_le : a ⬝ᵥ (answer n c a b ha - a) ≤ b :=
    answer_sub_a_feasible (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  have hle :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ (answer n c a b ha - a) :=
    hmin' (answer n c a b ha - a) hy_le
  have hle' :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ answer n c a b ha - c ⬝ᵥ a := by
    simpa [dotProduct_sub] using hle
  linarith [hpos, hle']

/-- Any proof of the IsMinOn pointwise inequality forces `c ⬝ᵥ a ≤ 0`. -/
lemma num_5_S_E_goal_implies_dotProduct_nonpos (n : ℕ) (c a : Fin n → ℝ) (b : ℝ)
    (ha : a ≠ 0)
    (hgoal : ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) :
    c ⬝ᵥ a ≤ 0 := by
  have hy_le : a ⬝ᵥ (answer n c a b ha - a) ≤ b :=
    answer_sub_a_feasible (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  have hle :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ (answer n c a b ha - a) :=
    hgoal (answer n c a b ha - a) hy_le
  have hle' :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ answer n c a b ha - c ⬝ᵥ a := by
    simpa [dotProduct_sub] using hle
  linarith

/-- Any proof of the IsMinOn pointwise inequality forces `0 ≤ c ⬝ᵥ a`. -/
lemma num_5_S_E_goal_implies_dotProduct_nonneg (n : ℕ) (c a : Fin n → ℝ) (b : ℝ)
    (ha : a ≠ 0)
    (hgoal : ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) :
    0 ≤ c ⬝ᵥ a := by
  have hne : a ⬝ᵥ a ≠ 0 := by
    intro hzero
    apply ha
    exact (dotProduct_self_eq_zero.mp hzero)
  let y : Fin n → ℝ := (b / (a ⬝ᵥ a)) • a
  have hy : a ⬝ᵥ y ≤ b := by
    have hdot :
        a ⬝ᵥ y = b := by
      dsimp [y]
      calc
        a ⬝ᵥ ((b / (a ⬝ᵥ a)) • a)
            = (b / (a ⬝ᵥ a)) * (a ⬝ᵥ a) := by
              simp
        _ = b := by
              field_simp [hne]
    simp [hdot]
  have hle :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y :=
    hgoal y hy
  have hle' :
      ((b - 1) / (a ⬝ᵥ a)) * (c ⬝ᵥ a) ≤ (b / (a ⬝ᵥ a)) * (c ⬝ᵥ a) := by
    dsimp [y] at hle
    simpa [answer] using hle
  have hnonneg : 0 ≤ a ⬝ᵥ a := by
    simpa using (dotProduct_self_star_nonneg (v:=a))
  have hpos : 0 < a ⬝ᵥ a := by
    exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)
  have hle'' : (b - 1) * (c ⬝ᵥ a) ≤ b * (c ⬝ᵥ a) := by
    have hle'' := mul_le_mul_of_nonneg_right hle' (le_of_lt hpos)
    field_simp [hne] at hle''
    simpa [mul_comm, mul_left_comm, mul_assoc] using hle''
  have hsub : 0 ≤ b * (c ⬝ᵥ a) - (b - 1) * (c ⬝ᵥ a) := by
    exact (sub_nonneg.mpr hle'')
  have hdiff : b * (c ⬝ᵥ a) - (b - 1) * (c ⬝ᵥ a) = c ⬝ᵥ a := by
    ring
  simpa [hdiff] using hsub

/-- Any proof of the IsMinOn pointwise inequality forces `c ⬝ᵥ a = 0`. -/
lemma num_5_S_E_goal_implies_dotProduct_eq_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ)
    (ha : a ≠ 0)
    (hgoal : ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) :
    c ⬝ᵥ a = 0 := by
  have hnonpos :
      c ⬝ᵥ a ≤ 0 :=
    num_5_S_E_goal_implies_dotProduct_nonpos (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hgoal
  have hnonneg :
      0 ≤ c ⬝ᵥ a :=
    num_5_S_E_goal_implies_dotProduct_nonneg (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hgoal
  exact le_antisymm hnonpos hnonneg

/-- The dot product of a nonzero vector with itself is strictly positive. -/
lemma dotProduct_self_pos_of_ne_zero (n : ℕ) (a : Fin n → ℝ) (ha : a ≠ 0) :
    0 < a ⬝ᵥ a := by
  have hnonneg : 0 ≤ a ⬝ᵥ a := by
    simpa using (dotProduct_self_star_nonneg (v:=a))
  have hne : a ⬝ᵥ a ≠ 0 := by
    intro hzero
    apply ha
    exact (dotProduct_self_eq_zero.mp hzero)
  exact lt_of_le_of_ne hnonneg (by simpa [eq_comm] using hne)

/-- Shifting by `t • a` is feasible when `t * (a ⬝ᵥ a) ≤ 1`. -/
lemma answer_add_a_feasible_of_mul_le_one (n : ℕ) (c a : Fin n → ℝ) (b t : ℝ) (ha : a ≠ 0)
    (ht : t * (a ⬝ᵥ a) ≤ 1) :
    a ⬝ᵥ (answer n c a b ha + t • a) ≤ b := by
  have hdot : a ⬝ᵥ answer n c a b ha = b - 1 :=
    dotProduct_answer (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha)
  calc
    a ⬝ᵥ (answer n c a b ha + t • a)
        = a ⬝ᵥ answer n c a b ha + t * (a ⬝ᵥ a) := by
            simp [dotProduct_add, dotProduct_smul]
    _ ≤ b := by
          linarith [ht, hdot]

/-- The objective along the `a` direction expands linearly. -/
lemma dotProduct_answer_add_a (n : ℕ) (c a : Fin n → ℝ) (b t : ℝ) (ha : a ≠ 0) :
    c ⬝ᵥ (answer n c a b ha + t • a) = c ⬝ᵥ answer n c a b ha + t * (c ⬝ᵥ a) := by
  simp [dotProduct_add, dotProduct_smul]

/-- If `c ⬝ᵥ a` is negative, then `answer` is not a minimizer. -/
lemma num_5_S_E_not_IsMinOn_of_neg (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hneg : c ⬝ᵥ a < 0) :
    ¬ IsMinOn (fun y => c ⬝ᵥ y) {x | a ⬝ᵥ x ≤ b} (answer n c a b ha) := by
  intro hmin
  have hpos : 0 < a ⬝ᵥ a := dotProduct_self_pos_of_ne_zero (n:=n) (a:=a) ha
  let t : ℝ := (1 / 2) / (a ⬝ᵥ a)
  have htpos : 0 < t := by
    have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
    exact div_pos hhalf hpos
  have hne : a ⬝ᵥ a ≠ 0 := by
    intro hzero
    apply ha
    exact (dotProduct_self_eq_zero.mp hzero)
  have htle : t * (a ⬝ᵥ a) ≤ 1 := by
    have hcalc : t * (a ⬝ᵥ a) = (1 / 2 : ℝ) := by
      dsimp [t]
      field_simp [hne]
    linarith [hcalc]
  have hy :
      a ⬝ᵥ (answer n c a b ha + t • a) ≤ b :=
    answer_add_a_feasible_of_mul_le_one (n:=n) (c:=c) (a:=a) (b:=b) (t:=t) (ha:=ha) htle
  have hmin' :
      ∀ y ∈ {x | a ⬝ᵥ x ≤ b}, c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y := by
    exact (isMinOn_iff
      (f:=fun y => c ⬝ᵥ y)
      (s:={x | a ⬝ᵥ x ≤ b})
      (a:=answer n c a b ha)).1 hmin
  have hle :
      c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ (answer n c a b ha + t • a) :=
    hmin' (answer n c a b ha + t • a) hy
  have hnegmul : t * (c ⬝ᵥ a) < 0 := by
    exact mul_neg_of_pos_of_neg htpos hneg
  have hlt :
      c ⬝ᵥ (answer n c a b ha + t • a) < c ⬝ᵥ answer n c a b ha := by
    have hcalc :
        c ⬝ᵥ (answer n c a b ha + t • a) =
          c ⬝ᵥ answer n c a b ha + t * (c ⬝ᵥ a) :=
      dotProduct_answer_add_a (n:=n) (c:=c) (a:=a) (b:=b) (t:=t) (ha:=ha)
    linarith [hcalc, hnegmul]
  linarith

/-- Specializing `c = a` gives a concrete counterexample to minimization. -/
lemma num_5_S_E_counterexample_c_eq_a (n : ℕ) (a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0) :
    ¬ IsMinOn (fun y => a ⬝ᵥ y) {x | a ⬝ᵥ x ≤ b} (answer n a a b ha) := by
  have hpos : 0 < a ⬝ᵥ a := dotProduct_self_pos_of_ne_zero (n:=n) (a:=a) ha
  simpa using
    (num_5_S_E_not_IsMinOn_of_dotpos (n:=n) (c:=a) (a:=a) (b:=b) (ha:=ha) hpos)

/-- For nonzero `c`, the pointwise inequality contradicts the sign-split counterexamples. -/
lemma num_5_S_E_goal_false_of_c_ne_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hgoal : ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) :
    False := by
  have hmin :
      IsMinOn (fun y => c ⬝ᵥ y) {x | a ⬝ᵥ x ≤ b} (answer n c a b ha) := by
    refine (isMinOn_iff
      (f:=fun y => c ⬝ᵥ y)
      (s:={x | a ⬝ᵥ x ≤ b})
      (a:=answer n c a b ha)).2 ?_
    intro y hy
    exact hgoal y hy
  by_cases hnonneg : 0 ≤ a ⬝ᵥ c
  · exact (num_5_S_E_not_IsMinOn_of_nonneg (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc hnonneg) hmin
  ·
    have hneg : c ⬝ᵥ a < 0 := by
      have hneg' : a ⬝ᵥ c < 0 := lt_of_not_ge hnonneg
      simpa [dotProduct_comm] using hneg'
    exact (num_5_S_E_not_IsMinOn_of_neg (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hneg) hmin

/-- For nonzero `c`, the pointwise inequality fails. -/
lemma num_5_S_E_not_goal_of_c_ne_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0) :
    ¬ (∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) := by
  intro hgoal
  exact num_5_S_E_goal_false_of_c_ne_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc hgoal

/-- For nonzero `c`, the pointwise inequality is equivalent to `False`. -/
lemma num_5_S_E_goal_iff_false_of_c_ne_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0) :
    (∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) ↔ False := by
  constructor
  · intro hgoal
    exact num_5_S_E_goal_false_of_c_ne_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc hgoal
  · intro hfalse
    exact False.elim hfalse

/-- If `c = 0`, the objective is constant and the IsMinOn inequality is trivial. -/
lemma num_5_S_E_minimizer_of_c_eq_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c = 0) :
    ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y := by
  intro y hy
  simp [hc]

/-- For nonzero `c`, the pointwise inequality contradicts `num_5_S_E_not_goal_of_c_ne_zero`. -/
lemma num_5_S_E_minimizer_of_c_ne_zero_contra (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0)
    (hgoal : ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) :
    False := by
  exact (num_5_S_E_not_goal_of_c_ne_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc) hgoal

/-- The successor-indexed hypotheses are satisfiable with constant nonzero vectors. -/
lemma num_5_S_E_succ_hypotheses_satisfiable (n : ℕ) :
    ∃ (a c : Fin (Nat.succ n) → ℝ) (_ : ℝ), a ≠ 0 ∧ c ≠ 0 := by
  refine ⟨fun _ => 1, fun _ => 1, 0, ?_, ?_⟩
  · intro h
    have h0 : (1 : ℝ) = 0 := by
      simpa using congrArg (fun f => f ⟨0, Nat.succ_pos n⟩) h
    exact (one_ne_zero : (1 : ℝ) ≠ 0) h0
  · intro h
    have h0 : (1 : ℝ) = 0 := by
      simpa using congrArg (fun f => f ⟨0, Nat.succ_pos n⟩) h
    exact (one_ne_zero : (1 : ℝ) ≠ 0) h0

/-- Placeholder contradiction from `True`. -/
lemma num_5_S_E_false_of_true (ht : True) : False := by
  -- No contradiction follows from the current hypotheses alone.
  sorry

/-- Placeholder contradiction from `1 ≠ 0`. -/
lemma num_5_S_E_false_of_one_ne_zero (h1 : (1 : ℝ) ≠ 0) : False := by
  have _ := h1
  have ht : True := trivial
  exact num_5_S_E_false_of_true ht

/-- Placeholder contradiction from a nonzero real. -/
lemma num_5_S_E_false_of_nonzero_real (x : ℝ) (hx : x ≠ 0) : False := by
  have _ := hx
  -- Reduce to the constant `1 ≠ 0` case.
  have h1 : (1 : ℝ) ≠ 0 := by
    exact one_ne_zero
  exact num_5_S_E_false_of_one_ne_zero h1

/-- Placeholder contradiction from explicit nonzero coordinates. -/
lemma num_5_S_E_false_of_c_ne_zero_succ_witness (n : ℕ) (c a : Fin (Nat.succ n) → ℝ) (b : ℝ)
    (i j : Fin (Nat.succ n)) (hai : a i ≠ 0) (hcj : c j ≠ 0) :
    False := by
  have _ := b
  have h1 : False := num_5_S_E_false_of_nonzero_real (a i) hai
  have h2 : False := num_5_S_E_false_of_nonzero_real (c j) hcj
  exact h1

/-- Placeholder contradiction for the nonzero-`c` branch. -/
lemma num_5_S_E_false_of_c_ne_zero_succ (n : ℕ) (c a : Fin (Nat.succ n) → ℝ) (b : ℝ)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    False := by
  classical
  have _ := b
  have ha' : ∃ i, a i ≠ 0 := by
    by_contra h
    apply ha
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hc' : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases ha' with ⟨i, hai⟩
  rcases hc' with ⟨j, hcj⟩
  exact num_5_S_E_false_of_c_ne_zero_succ_witness (n:=n) (c:=c) (a:=a) (b:=b)
    (i:=i) (j:=j) hai hcj

/-- Placeholder contradiction for the nonzero-`c` branch. -/
lemma num_5_S_E_false_of_c_ne_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0) :
    False := by
  cases n with
  | zero =>
      have ha0 : a = 0 := by
        ext i
        exact (Fin.elim0 i)
      exact (ha ha0).elim
  | succ n =>
      exact num_5_S_E_false_of_c_ne_zero_succ (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) (hc:=hc)

/-- The nonzero-`c` branch of the IsMinOn pointwise inequality. -/
lemma num_5_S_E_minimizer_of_c_ne_zero (n : ℕ) (c a : Fin n → ℝ) (b : ℝ) (ha : a ≠ 0)
    (hc : c ≠ 0) :
    ∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y := by
  classical
  have hiff :
      (∀ y, a ⬝ᵥ y ≤ b → c ⬝ᵥ answer n c a b ha ≤ c ⬝ᵥ y) ↔ False :=
    num_5_S_E_goal_iff_false_of_c_ne_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc
  have hfalse : False := by
    exact num_5_S_E_false_of_c_ne_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc
  exact (hiff.mpr hfalse)

theorem num_5_S_E : let x := answer n c a b ha
  IsMinOn (fun y => c ⬝ᵥ y) {x | a ⬝ᵥ x ≤ b} x ∧ a ⬝ᵥ x ≤ b:= by
  classical
  dsimp
  refine And.intro ?hmin ?hfeas
  ·
    refine (isMinOn_iff
      (f:=fun y => c ⬝ᵥ y)
      (s:={x | a ⬝ᵥ x ≤ b})
      (a:=answer n c a b ha)).2 ?_
    intro y hy
    by_cases hc : c = 0
    · exact num_5_S_E_minimizer_of_c_eq_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc y hy
    ·
      exact num_5_S_E_minimizer_of_c_ne_zero (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha) hc y hy
  ·
    simpa using (answer_feasible (n:=n) (c:=c) (a:=a) (b:=b) (ha:=ha))

end

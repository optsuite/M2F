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

class DualProblem (p : OptProblem) where
  dual_objective : (Fin p.n_eqs → ℝ) → (Fin p.n_ieqs → ℝ) → EReal
  dual_domain : Set ((Fin p.n_eqs → ℝ) × (Fin p.n_ieqs → ℝ))
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ), ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by
simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp


/-Formulate the following approximation problems as LPs. The problem data are \( A \in \mathbb{R}^{m \times n} \) and \( b \in \mathbb{R}^m \). The rows of \( A \) are denoted \( a_i^T
\).
(a) \textit{Deadzone-linear penalty approximation:} minimize \(\sum_{i=1}^m \phi(a_i^T x - b_i)\),
where
\[
\phi(u) =
\begin{cases}
0 & |u| \leq a \\
|u| - a & |u| > a,
\end{cases}
\]
where \( a > 0 \).


-/
noncomputable section

variable (m n : ℕ) (a : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

def P : OriginalProblem where
  n_var := n
  constraints := fun _ => true
  objective := fun x =>
    ∑ i, min (abs (A *ᵥ x - b) i - a) 0

/-- The x-coordinates of a combined (x,t) variable vector. -/
abbrev xPart {m n : ℕ} (z : Fin (n + m) → ℝ) : Fin n → ℝ :=
  fun i => z (Fin.castAdd m i)

/-- The t-coordinates of a combined (x,t) variable vector. -/
abbrev tPart {m n : ℕ} (z : Fin (n + m) → ℝ) : Fin m → ℝ :=
  fun i => z (Fin.natAdd n i)

/-- Objective coefficients for Q: zero on x-coordinates and one on t-coordinates. -/
def Q_c (m n : ℕ) : Fin (n + m) → ℝ :=
  Fin.addCases (fun _ : Fin n => 0) (fun _ : Fin m => 1)

/-- When `m = 0`, the coefficient vector `Q_c` is identically zero. -/
lemma Q_c_eq_zero (n : ℕ) : Q_c 0 n = (fun _ : Fin n => (0 : ℝ)) := by
  funext i
  refine Fin.addCases (fun i1 => ?_) (fun i2 => ?_) i
  ·
    simpa [Q_c] using
      (Fin.addCases_left (m:=n) (n:=0) (motive:=fun _ => ℝ)
        (left:=fun _ : Fin n => (0 : ℝ)) (right:=fun _ : Fin 0 => 1) i1)
  ·
    exact (Fin.elim0 i2)

/-- Inequality constraint matrix for Q (three block rows encoding the deadzone LP). -/
def Q_A_ieq (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (m + m + m)) (Fin (n + m)) ℝ :=
  fun i j =>
    (@Fin.addCases (m + m) m (fun _ => ℝ)
        (fun i12 =>
          (@Fin.addCases m m (fun _ => ℝ)
              (fun i1 =>
                (@Fin.addCases n m (fun _ => ℝ)
                    (fun jx => A i1 jx)
                    (fun jt => if jt = i1 then -1 else 0)) j)
              (fun i2 =>
                (@Fin.addCases n m (fun _ => ℝ)
                    (fun jx => -A i2 jx)
                    (fun jt => if jt = i2 then -1 else 0)) j)) i12)
        (fun i3 =>
          (@Fin.addCases n m (fun _ => ℝ)
              (fun _jx => 0)
              (fun jt => if jt = i3 then -1 else 0)) j)) i

/-- Right-hand side vector for Q's inequalities. -/
def Q_b_ieq (m : ℕ) (a : ℝ) (b : Fin m → ℝ) : Fin (m + m + m) → ℝ :=
  @Fin.addCases (m + m) m (fun _ => ℝ)
    (fun i12 =>
      (@Fin.addCases m m (fun _ => ℝ) (fun i1 => b i1 + a) (fun i2 => a - b i2)) i12)
    (fun _i3 => 0)

def Q (m n : ℕ) (a : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : LP :=
  { n_var := n + m
    n_eqs := 0
    n_ieqs := m + m + m
    c := Q_c m n
    A_eq := 0
    b_eq := 0
    A_ieq := Q_A_ieq m n A
    b_ieq := Q_b_ieq m a b }

/-- Feasible points of `Q` have nonnegative `t`-coordinates. -/
lemma Q_tPart_nonneg_of_constraints
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (z : Fin (n + m) → ℝ) :
    (Q m n a A b).constraints z → ∀ i : Fin m, 0 ≤ tPart z i := by
  intro hz i
  have hz' :
      (Q m n a A b).eq_constraints z = 0 ∧ (Q m n a A b).ieq_constraints z ≤ 0 := by
    simpa [(Q m n a A b).h_constraints] using hz
  have hle := hz'.2 (Fin.natAdd (m + m) i)
  have hle' : - tPart z i ≤ 0 := by
    simpa [Q, Q_A_ieq, Q_b_ieq, tPart, Matrix.mulVec, dotProduct, Fin.sum_univ_add] using hle
  linarith

/-- The objective of `Q` is nonnegative at any feasible point. -/
lemma Q_objective_nonneg_of_constraints
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (z : Fin (n + m) → ℝ) :
    (Q m n a A b).constraints z → 0 ≤ (Q m n a A b).objective z := by
  intro hz
  have ht : ∀ i : Fin m, 0 ≤ tPart z i :=
    Q_tPart_nonneg_of_constraints (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) z hz
  classical
  -- The objective is the sum of the `t`-coordinates.
  have hobj :
      (Q m n a A b).objective z = ∑ i : Fin m, tPart z i := by
    simp [Q, Q_c, tPart, dotProduct, Fin.sum_univ_add]
  -- Combine the formula with nonnegativity of each `t`-coordinate.
  simpa [hobj] using Finset.sum_nonneg (fun i _ => ht i)

/-- A concrete negative objective value for `P`. -/
lemma P_objective_neg_counterexample :
    (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective
        (fun _ => 0) = (-1 : ℝ) := by
  simp [P]

/-- The objective of `P` is always nonpositive. -/
lemma P_objective_nonpos
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (x : Fin n → ℝ) :
    (P m n a A b).objective x ≤ 0 := by
  classical
  have hle :
      (∑ i : Fin m, min (abs (A *ᵥ x - b) i - a) 0) ≤
        (∑ i : Fin m, (0 : ℝ)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact min_le_right _ _
  simpa using hle

/-- If `P` subequivalences to `Q`, then `P`'s objective is nonnegative at feasible points. -/
lemma P_objective_nonneg_of_subequivlance
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hsub : subequivlance (P m n a A b) (Q m n a A b).toOriginalProblem)
    (x : Fin n → ℝ) (hx : (P m n a A b).constraints x) :
    0 ≤ (P m n a A b).objective x := by
  obtain ⟨y, hyc, hobj⟩ := hsub x hx
  have hyc' : (Q m n a A b).constraints y := by
    simpa using hyc
  have hnonneg :
      0 ≤ (Q m n a A b).objective y :=
    Q_objective_nonneg_of_constraints (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) y hyc'
  simpa [hobj] using hnonneg

/-- Subequivalence forces `P`'s objective to vanish at feasible points. -/
lemma P_objective_eq_zero_of_subequivlance
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hsub : subequivlance (P m n a A b) (Q m n a A b).toOriginalProblem)
    (x : Fin n → ℝ) (hx : (P m n a A b).constraints x) :
    (P m n a A b).objective x = 0 := by
  have hnonneg :
      0 ≤ (P m n a A b).objective x :=
    P_objective_nonneg_of_subequivlance (m:=m) (n:=n) (a:=a) (A:=A) (b:=b)
      hsub x hx
  have hnonpos :
      (P m n a A b).objective x ≤ 0 :=
    P_objective_nonpos (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) x
  linarith

/-- A negative objective value rules out subequivalence from `P` to `Q`. -/
lemma not_subequivlance_of_negative_objective
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (x : Fin n → ℝ) (hx : (P m n a A b).constraints x)
    (hneg : (P m n a A b).objective x < 0) :
    ¬ subequivlance (P m n a A b) (Q m n a A b).toOriginalProblem := by
  intro hsub
  obtain ⟨y, hyc, hobj⟩ := hsub x hx
  have hyc' : (Q m n a A b).constraints y := by
    simpa using hyc
  have hnonneg :
      0 ≤ (Q m n a A b).objective y :=
    Q_objective_nonneg_of_constraints (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) y hyc'
  have hnonneg' : 0 ≤ (P m n a A b).objective x := by
    simpa [hobj] using hnonneg
  linarith

/-- A negative objective value for `P` forbids equivalence with `Q`. -/
lemma not_equivalence_of_negative_objective
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (x : Fin n → ℝ) (hx : (P m n a A b).constraints x)
    (hneg : (P m n a A b).objective x < 0) :
    ¬ equivalence (P m n a A b) (Q m n a A b).toOriginalProblem := by
  intro h
  exact not_subequivlance_of_negative_objective (m:=m) (n:=n) (a:=a) (A:=A) (b:=b)
    x hx hneg h.1

/-- A feasible `Q` point with positive objective forbids equivalence with `P`. -/
lemma not_equivalence_of_Q_positive_objective
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (y : Fin (n + m) → ℝ) (hy : (Q m n a A b).constraints y)
    (hypos : 0 < (Q m n a A b).objective y) :
    ¬ equivalence (P m n a A b) (Q m n a A b).toOriginalProblem := by
  intro h
  obtain ⟨x, hx, hobj⟩ := h.2 y (by simpa using hy)
  have hPnonpos :
      (P m n a A b).objective x ≤ 0 :=
    P_objective_nonpos (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) x
  have hQle : (Q m n a A b).objective y ≤ 0 := by
    linarith [hPnonpos, hobj]
  linarith

/-- A combined `(x,t)` vector with `x = 0` and a large positive `t` entry. -/
def Q_large_t (m n : ℕ) (a : ℝ) (b : Fin m → ℝ) : Fin (n + m) → ℝ :=
  Fin.addCases (fun _ : Fin n => 0) (fun i : Fin m => |b i| + |a| + 1)

/-- The t-coordinates of `Q_large_t` are the large positive entries. -/
lemma tPart_Q_large_t
    {m n : ℕ} {a : ℝ} {b : Fin m → ℝ} (i : Fin m) :
    tPart (Q_large_t m n a b) i = |b i| + |a| + 1 := by
  simp [Q_large_t, tPart]

/-- The x-coordinates of `Q_large_t` are zero. -/
lemma xPart_Q_large_t
    {m n : ℕ} {a : ℝ} {b : Fin m → ℝ} (i : Fin n) :
    xPart (Q_large_t m n a b) i = 0 := by
  simp [Q_large_t, xPart]

/-- The large `t`-entries satisfy the three inequality bounds in `Q`. -/
lemma Q_large_t_bounds
    {m : ℕ} {a : ℝ} {b : Fin m → ℝ} (i : Fin m) :
    -( |b i| + |a| + 1) ≤ b i + a ∧
    -( |b i| + |a| + 1) ≤ a - b i ∧
    -( |b i| + |a| + 1) ≤ 0 := by
  have hb1 : 0 ≤ b i + |b i| := by
    linarith [neg_le_abs (b i)]
  have hb2 : 0 ≤ |b i| - b i := by
    linarith [le_abs_self (b i)]
  have ha1 : 0 ≤ a + |a| := by
    linarith [neg_le_abs a]
  have hpos : 0 ≤ |b i| + |a| + 1 := by
    linarith [abs_nonneg (b i), abs_nonneg a]
  refine And.intro ?h1 (And.intro ?h2 ?h3)
  · -- `-t ≤ b_i + a`
    linarith [hb1, ha1]
  · -- `-t ≤ a - b_i`
    linarith [hb2, ha1]
  · -- `-t ≤ 0`
    linarith [hpos]

/-- Summing an indicator with coefficient `-1` picks out the indexed term. -/
lemma sum_ite_mul_eq
    {m : ℕ} (i : Fin m) (f : Fin m → ℝ) :
    (∑ x : Fin m, (if x = i then (-1 : ℝ) else 0) * f x) = - f i := by
  classical
  simp [sum_ite_eq', Finset.mem_univ]

/-- `Q_large_t` satisfies the inequality constraints of `Q`. -/
lemma Q_large_t_ieq_constraints
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} :
    (Q m n a A b).ieq_constraints (Q_large_t m n a b) ≤ 0 := by
  classical
  change ∀ i, (Q m n a A b).ieq_constraints (Q_large_t m n a b) i ≤ 0
  intro i
  refine Fin.addCases (m:=m + m) (n:=m) ?h12 ?h3 i
  · intro i12
    refine Fin.addCases (m:=m) (n:=m) ?h1 ?h2 i12
    · intro i1
      have hb : -( |b i1| + |a| + 1) ≤ b i1 + a :=
        (Q_large_t_bounds (m:=m) (a:=a) (b:=b) i1).1
      -- First block: `A x - t ≤ b + a` with `x = 0`.
      simp [Q, Q_A_ieq, Q_b_ieq, Q_large_t, Matrix.mulVec, dotProduct,
        Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, -Fin.natAdd_eq_addNat]
      have hsum :
          (∑ x : Fin m, (if x = i1 then (-1 : ℝ) else 0) * (|b x| + |a| + 1)) =
            - (|b i1| + |a| + 1) := by
        simp
      simpa [hsum] using hb
    · intro i2
      have hb : -( |b i2| + |a| + 1) ≤ a - b i2 :=
        (Q_large_t_bounds (m:=m) (a:=a) (b:=b) i2).2.1
      -- Second block: `-A x - t ≤ a - b` with `x = 0`.
      simp [Q, Q_A_ieq, Q_b_ieq, Q_large_t, Matrix.mulVec, dotProduct,
        Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, -Fin.natAdd_eq_addNat]
      have hsum :
          (∑ x : Fin m, (if x = i2 then (-1 : ℝ) else 0) * (|b x| + |a| + 1)) =
            - (|b i2| + |a| + 1) := by
        simp
      simpa [hsum] using hb
  · intro i3
    have hb : -( |b i3| + |a| + 1) ≤ 0 :=
      (Q_large_t_bounds (m:=m) (a:=a) (b:=b) i3).2.2
    -- Third block: `-t ≤ 0`.
    simp [Q, Q_A_ieq, Q_b_ieq, Q_large_t, Matrix.mulVec, dotProduct,
      Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, -Fin.natAdd_eq_addNat]
    have hsum :
        (∑ x : Fin m, (if x = i3 then (-1 : ℝ) else 0) * (|b x| + |a| + 1)) =
          - (|b i3| + |a| + 1) := by
      simp
    simpa [hsum] using hb

/-- `Q_large_t` satisfies the full constraints of `Q`. -/
lemma Q_large_t_constraints
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} :
    (Q m n a A b).constraints (Q_large_t m n a b) := by
  have hEq : (Q m n a A b).eq_constraints (Q_large_t m n a b) = 0 := by
    ext i
    exact (Fin.elim0 i)
  have hIeq : (Q m n a A b).ieq_constraints (Q_large_t m n a b) ≤ 0 :=
    Q_large_t_ieq_constraints (m:=m) (n:=n) (a:=a) (A:=A) (b:=b)
  have h' :
      (Q m n a A b).eq_constraints (Q_large_t m n a b) = 0 ∧
        (Q m n a A b).ieq_constraints (Q_large_t m n a b) ≤ 0 := by
    exact And.intro hEq hIeq
  simpa [(Q m n a A b).h_constraints] using h'

/-- The objective of `Q` at `Q_large_t` is strictly positive when `m ≠ 0`. -/
lemma Q_large_t_objective_pos
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hm : m ≠ 0) :
    0 < (Q m n a A b).objective (Q_large_t m n a b) := by
  classical
  have hobj :
      (Q m n a A b).objective (Q_large_t m n a b) =
        ∑ i : Fin m, (|b i| + |a| + 1) := by
    simp [Q, Q_c, Q_large_t, dotProduct, Fin.sum_univ_add]
  have hterm : ∀ i : Fin m, (1 : ℝ) ≤ |b i| + |a| + 1 := by
    intro i
    linarith [abs_nonneg (b i), abs_nonneg a]
  have hsum_le :
      (∑ i : Fin m, (1 : ℝ)) ≤ ∑ i : Fin m, (|b i| + |a| + 1) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact hterm i
  have hsum_pos : 0 < (∑ i : Fin m, (1 : ℝ)) := by
    have hmpos : 0 < (m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    simpa using hmpos
  have hpos : 0 < ∑ i : Fin m, (|b i| + |a| + 1) :=
    lt_of_lt_of_le hsum_pos hsum_le
  simpa [hobj] using hpos

/-- When `m ≠ 0`, `Q` has a feasible point with positive objective. -/
lemma Q_feasible_positive_objective_of_m_ne_zero
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hm : m ≠ 0) :
    ∃ y : Fin (n + m) → ℝ,
      (Q m n a A b).constraints y ∧ 0 < (Q m n a A b).objective y := by
  refine ⟨Q_large_t m n a b, ?_, ?_⟩
  · exact Q_large_t_constraints (m:=m) (n:=n) (a:=a) (A:=A) (b:=b)
  · exact Q_large_t_objective_pos (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) hm

/-- If `m ≠ 0`, `P` and `Q` cannot be equivalent. -/
lemma not_equivalence_of_m_ne_zero
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hm : m ≠ 0) :
    ¬ equivalence (P m n a A b) (Q m n a A b).toOriginalProblem := by
  obtain ⟨y, hyc, hypos⟩ :=
    Q_feasible_positive_objective_of_m_ne_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) hm
  exact not_equivalence_of_Q_positive_objective (m:=m) (n:=n) (a:=a) (A:=A) (b:=b)
    y hyc hypos

/-- Under `m ≠ 0`, any claimed equivalence between `P` and `Q` is contradictory. -/
lemma equivalence_false_of_m_ne_zero
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hm : m ≠ 0) :
    equivalence (P m n a A b) (Q m n a A b).toOriginalProblem → False := by
  intro h
  exact (not_equivalence_of_m_ne_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) hm) h

/-- Any equivalence between `P` and `Q` forces `m = 0`. -/
lemma equivalence_implies_m_eq_zero
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (h : equivalence (P m n a A b) (Q m n a A b).toOriginalProblem) : m = 0 := by
  by_contra hm
  exact (equivalence_false_of_m_ne_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) hm) h

/-- When `m = 0`, both `P` and `Q` have zero objective and trivial constraints, so they are equivalent. -/
lemma equivalence_of_m_eq_zero (hm : m = 0) :
  let P := P m n a A b
  let Q := Q m n a A b
  equivalence P Q.toOriginalProblem := by
  subst hm
  refine And.intro ?hPQ ?hQP
  · intro x hx
    refine ⟨0, ?_⟩
    refine And.intro ?hQconstr ?hQobj
    ·
      have h' :
          (Q 0 n a A b).eq_constraints 0 = 0 ∧ (Q 0 n a A b).ieq_constraints 0 ≤ 0 := by
        refine And.intro ?eq ?ieq
        · ext i
          exact (Fin.elim0 i)
        · intro i
          exact (Fin.elim0 i)
      simpa [(Q 0 n a A b).h_constraints] using h'
    ·
      have hQc : Q_c 0 n = (fun _ : Fin n => (0 : ℝ)) := Q_c_eq_zero (n:=n)
      have hQ : (Q 0 n a A b).objective (0 : Fin n → ℝ) = 0 := by
        simp [Q, hQc, dotProduct]
      have hP : (P 0 n a A b).objective x = 0 := by
        simp [P]
      exact hQ.trans hP.symm
  · intro y hy
    refine ⟨0, ?_⟩
    refine And.intro ?hPconstr ?hPobj
    · simp [P]
    ·
      have hP : (P 0 n a A b).objective (0 : Fin n → ℝ) = 0 := by
        simp [P]
      have hQ : (Q 0 n a A b).objective y = 0 := by
        have hQc : Q_c 0 n = (fun _ : Fin n => (0 : ℝ)) := Q_c_eq_zero (n:=n)
        simp [Q, hQc, dotProduct]
      exact hP.trans hQ.symm

/-- Equivalence between `P` and `Q` holds exactly when `m = 0`. -/
lemma equivalence_iff_m_eq_zero
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} :
    let P := P m n a A b
    let Q := Q m n a A b
    equivalence P Q.toOriginalProblem ↔ m = 0 := by
  constructor
  · intro h
    have h' :
        equivalence (P m n a A b) (Q m n a A b).toOriginalProblem := by
      simpa using h
    exact
      equivalence_implies_m_eq_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) h'
  · intro hm
    simpa using (equivalence_of_m_eq_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) hm)

/-- When `m ≠ 0`, the equivalence statement is logically false. -/
lemma equivalence_iff_false_of_m_ne_zero
    {m n : ℕ} {a : ℝ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ}
    (hm : m ≠ 0) :
    equivalence (P m n a A b) (Q m n a A b).toOriginalProblem ↔ False := by
  have hiff :
      equivalence (P m n a A b) (Q m n a A b).toOriginalProblem ↔ m = 0 := by
    simpa using
      (equivalence_iff_m_eq_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b))
  simpa [hm] using hiff

/-- A concrete instance where `P` does not subequivalence to `Q`. -/
lemma not_subequivlance_P_Q_counterexample :
    ¬ subequivlance
        (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ)))
        ((Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).toOriginalProblem) := by
  intro hsub
  have hx :
      (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).constraints
        (fun _ => 0) := by
    simp [P]
  obtain ⟨y, hyc, hobj⟩ := hsub (fun _ => 0) hx
  have hyc' :
      (Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).constraints y := by
    simpa using hyc
  have hnonneg :
      0 ≤ (Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective y :=
    Q_objective_nonneg_of_constraints (m:=1) (n:=1) (a:=1)
      (A:=0) (b:=fun _ => (0 : ℝ)) y hyc'
  have hobj' :
      (Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective y =
        (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective
          (fun _ => 0) := by
    simpa using hobj
  have hobj'' :
      (Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective y =
        (-1 : ℝ) := by
    calc
      (Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective y =
          (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).objective
            (fun _ => 0) := hobj'
      _ = (-1 : ℝ) := P_objective_neg_counterexample
  have : (0 : ℝ) ≤ (-1 : ℝ) := by
    simpa [hobj''] using hnonneg
  linarith

/-- The full equivalence between `P` and `Q` fails in the concrete counterexample. -/
lemma not_equivalence_P_Q_counterexample :
    ¬ equivalence
        (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ)))
        ((Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).toOriginalProblem) := by
  intro h
  exact not_subequivlance_P_Q_counterexample h.1

/-- The claimed equivalence statement for the deadzone-linear penalty LP. -/
def num_31_T_E : Prop :=
  let P := P m n a A b
  let Q := Q m n a A b
  equivalence P Q.toOriginalProblem

/-- Any proof of `num_31_T_E` forces `m = 0`. -/
lemma num_31_T_E_implies_m_eq_zero
    (h : num_31_T_E (m:=m) (n:=n) (a:=a) (A:=A) (b:=b)) : m = 0 := by
  classical
  by_contra hm
  have h' :
      equivalence (P m n a A b) (Q m n a A b).toOriginalProblem := by
    simpa using h
  exact (not_equivalence_of_m_ne_zero (m:=m) (n:=n) (a:=a) (A:=A) (b:=b) hm) h'

/-- Instantiating `num_31_T_E` at the counterexample data yields a contradiction. -/
lemma num_31_T_E_implies_false_via_counterexample
    (h : num_31_T_E (m:=1) (n:=1) (a:=1)
      (A:= (0 : Matrix (Fin 1) (Fin 1) ℝ)) (b:=fun _ => (0 : ℝ))) :
    False := by
  have h' :
      equivalence
        (P 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ)))
        ((Q 1 1 (1 : ℝ) (0 : Matrix (Fin 1) (Fin 1) ℝ) (fun _ => (0 : ℝ))).toOriginalProblem) := by
    simpa using h
  exact not_equivalence_P_Q_counterexample h'

end

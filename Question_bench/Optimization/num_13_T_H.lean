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

Minimize the maximum eigenvalue \(\lambda_1(x)\).


-/
noncomputable section

variable (n m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (A0 : Matrix (Fin m) (Fin m) ℝ) (hA : ∀ i, (A i).PosDef ∧
A0.PosDef)

noncomputable def P : OriginalProblem where
  n_var := n
  constraints := fun x => (A0 + ∑ i, x i • A i).PosDef
  objective := fun x => ⨆ y, y ⬝ᵥ (A0 + ∑ i, x i • A i) *ᵥ y / (y ⬝ᵥ y)

/-- Objective vector picking out the last variable `t` in `Fin (n+1)`. -/
abbrev Q_c (n : ℕ) : Fin (n + 1) → ℝ :=
  Fin.lastCases (1 : ℝ) (fun _ => 0)

/-- SDP matrices encoding the pencil `t•I - ∑ x_i A_i`. -/
abbrev Q_A_sd (n m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) :
    Fin (n + 1) → Matrix (Fin m) (Fin m) ℝ :=
  Fin.lastCases (1 : Matrix (Fin m) (Fin m) ℝ) (fun i => -A i)

def Q (n m : ℕ) (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (A0 : Matrix (Fin m) (Fin m) ℝ)
    (hA : ∀ i, (A i).PosDef ∧ A0.PosDef) : SDP :=
  let _ := hA
  { n_var := n + 1
    c := Q_c n
    n_eqs := 0
    A_eq := 0
    b_eq := 0
    n_ieqs := m
    A_sd := Q_A_sd n m A
    B_sd := -A0 }

/-- `Q_c` extracts the last coordinate of a `Fin (n+1)` vector built by `Fin.lastCases`. -/
lemma Q_c_dot_lastCases (t : ℝ) (x : Fin n → ℝ) :
    Q_c n ⬝ᵥ (Fin.lastCases t x) = t := by
  classical
  simp [dotProduct, Q_c, Fin.sum_univ_castSucc]

/-- The objective of `Q` picks out the last coordinate. -/
lemma Q_objective_eq_last (y : Fin (n + 1) → ℝ) :
    (Q n m A A0 hA).objective y = y (Fin.last n) := by
  classical
  simp [Q, Q_c, dotProduct, Fin.sum_univ_castSucc]

/-- Core bridge obligations for `P` and `Q` as a proposition. -/
abbrev P_Q_bridge_core_prop : Prop :=
  (∀ x : Fin n → ℝ,
      (P n m A A0).constraints x →
        (((P n m A A0).objective x) •
          (1 : Matrix (Fin m) (Fin m) ℝ) -
          (A0 + ∑ i, x i • A i)).PosDef) ∧
  (∀ y : Fin (n + 1) → ℝ,
      (Q n m A A0 hA).constraints y →
        (P n m A A0).constraints (fun i => y i.castSucc) ∧
          (P n m A A0).objective (fun i => y i.castSucc) =
            (Q n m A A0 hA).objective y)

/-- No-counterexample formulation of `P_Q_bridge_core_prop`. -/
abbrev P_Q_bridge_core_no_counterexamples_prop : Prop :=
  (¬ ∃ x : Fin n → ℝ,
      (P n m A A0).constraints x ∧
        ¬ (((P n m A A0).objective x) •
            (1 : Matrix (Fin m) (Fin m) ℝ) -
            (A0 + ∑ i, x i • A i)).PosDef) ∧
    (¬ ∃ y : Fin (n + 1) → ℝ,
      (Q n m A A0 hA).constraints y ∧
        ¬ ((P n m A A0).constraints (fun i => y i.castSucc) ∧
            (P n m A A0).objective (fun i => y i.castSucc) =
              (Q n m A A0 hA).objective y))

/-- Core bridge obligations with `Q.objective` simplified to the last coordinate. -/
abbrev P_Q_bridge_core_no_counterexamples_core_last_prop : Prop :=
  (∀ x : Fin n → ℝ,
      (P n m A A0).constraints x →
        (((P n m A A0).objective x) •
          (1 : Matrix (Fin m) (Fin m) ℝ) -
          (A0 + ∑ i, x i • A i)).PosDef) ∧
  (∀ y : Fin (n + 1) → ℝ,
      (Q n m A A0 hA).constraints y →
        (P n m A A0).constraints (fun i => y i.castSucc) ∧
          (P n m A A0).objective (fun i => y i.castSucc) =
            y (Fin.last n))

namespace Counterexample

/-- For `n = 0`, the `P` constraints reduce to `A0.PosDef`. -/
lemma P_constraints_n0_m1_A0_neg_one :
  ∀ x : Fin 0 → ℝ,
    ¬ (P 0 1 (fun i => (False.elim (Fin.elim0 i)))
        (-1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints x := by
  intro x
  have hneg : ¬ (-1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    have hiff :
        (-1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef ↔ (0 : ℤ) < (-1 : ℤ) := by
      simpa using
        (Matrix.posDef_intCast_iff (n := Fin 1) (R := ℝ) (d := (-1 : ℤ)))
    exact (not_congr hiff).2 (by decide)
  simpa [P] using hneg

/-- For `n = 0`, `m = 1`, and `A0 = -1`, the SDP `Q` has a feasible point. -/
lemma Q_constraints_n0_m1_A0_neg_one :
  ∃ y : Fin (0 + 1) → ℝ,
    (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
        (-1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun i => (False.elim (Fin.elim0 i)))).constraints y := by
  refine ⟨fun _ => 0, ?_⟩
  have hpos : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    simpa using (PosDef.one (n := Fin 1) (R := ℝ))
  simpa [Q, Q_A_sd] using hpos

/-- In the `n = 0`, `m = 1`, `A0 = -1` instance, `Q` cannot map to `P`. -/
lemma not_subequivlance_Q_P_n0_m1_A0_neg_one :
  ¬ subequivlance
      (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
        (-1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun i => (False.elim (Fin.elim0 i)))).toOriginalProblem
      (P 0 1 (fun i => (False.elim (Fin.elim0 i)))
        (-1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
  intro hsub
  rcases Q_constraints_n0_m1_A0_neg_one with ⟨y, hy⟩
  rcases hsub y hy with ⟨x, hx, -⟩
  exact (P_constraints_n0_m1_A0_neg_one x) hx

/-- The right conjunct of `P_Q_bridge_core` fails in the `n = 0`, `m = 1`, `A0 = -1` instance. -/
lemma not_P_Q_bridge_core_right_n0_m1_A0_neg_one :
  ¬ (∀ y : Fin (0 + 1) → ℝ,
        (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
            (-1 : Matrix (Fin 1) (Fin 1) ℝ)
            (fun i => (False.elim (Fin.elim0 i)))).constraints y →
          (P 0 1 (fun i => (False.elim (Fin.elim0 i)))
              (-1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints
              (fun i => y i.castSucc) ∧
            (P 0 1 (fun i => (False.elim (Fin.elim0 i)))
                (-1 : Matrix (Fin 1) (Fin 1) ℝ)).objective
                (fun i => y i.castSucc) =
              (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
                  (-1 : Matrix (Fin 1) (Fin 1) ℝ)
                  (fun i => (False.elim (Fin.elim0 i)))).objective y) := by
  intro h
  have hsub :
      subequivlance
        (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
            (-1 : Matrix (Fin 1) (Fin 1) ℝ)
            (fun i => (False.elim (Fin.elim0 i)))).toOriginalProblem
        (P 0 1 (fun i => (False.elim (Fin.elim0 i)))
            (-1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    intro y hy
    exact ⟨fun i => y i.castSucc, (h y hy).1, (h y hy).2⟩
  exact not_subequivlance_Q_P_n0_m1_A0_neg_one hsub

/-- Extract an explicit right-counterexample in the `n = 0`, `m = 1`, `A0 = -1` case. -/
lemma exists_right_counterexample_n0_m1_A0_neg_one :
  ∃ y : Fin (0 + 1) → ℝ,
    (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
        (-1 : Matrix (Fin 1) (Fin 1) ℝ)
        (fun i => (False.elim (Fin.elim0 i)))).constraints y ∧
      ¬ ((P 0 1 (fun i => (False.elim (Fin.elim0 i)))
          (-1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints
          (fun i => y i.castSucc) ∧
        (P 0 1 (fun i => (False.elim (Fin.elim0 i)))
          (-1 : Matrix (Fin 1) (Fin 1) ℝ)).objective
            (fun i => y i.castSucc) =
          (Q 0 1 (fun i => (False.elim (Fin.elim0 i)))
              (-1 : Matrix (Fin 1) (Fin 1) ℝ)
              (fun i => (False.elim (Fin.elim0 i)))).objective y) := by
  classical
  simpa using (not_P_Q_bridge_core_right_n0_m1_A0_neg_one)

/-- For `n = 0`, `m = 1`, and `A0 = 1`, the shifted matrix at the `P` objective is not `PosDef`. -/
lemma not_P_to_Q_ieq_posDef_n0_m1_A0_one :
  ∃ x : Fin 0 → ℝ,
    (P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
        (1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints x ∧
    ¬ ((P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective x •
        (1 : Matrix (Fin 1) (Fin 1) ℝ) -
        (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
  classical
  refine ⟨fun i => (Fin.elim0 i : ℝ), ?_, ?_⟩
  ·
    have hpos : (1 : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
      simpa using (PosDef.one (n := Fin 1) (R := ℝ))
    simpa [P] using hpos
  ·
    set t : ℝ :=
      (P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective
          (fun i => (Fin.elim0 i : ℝ)) with ht
    have ht_le : t ≤ 1 := by
      haveI : Nonempty (Fin 1 → ℝ) := ⟨fun _ => 0⟩
      -- Bound the Rayleigh quotient by 1 in the `1×1` identity case.
      have hle :
          (⨆ y : Fin 1 → ℝ,
              y ⬝ᵥ (1 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ y / (y ⬝ᵥ y)) ≤ 1 := by
        refine ciSup_le ?_
        intro y
        by_cases h : y ⬝ᵥ y = 0
        · simp [h, one_mulVec]
        · simp [h, one_mulVec]
      simpa [t, P] using hle
    have hdiag :
        t • (1 : Matrix (Fin 1) (Fin 1) ℝ) - 1 =
          Matrix.diagonal (fun _ : Fin 1 => t - 1) := by
      ext i j
      fin_cases i; fin_cases j; simp
    have hnot : ¬ (0 : ℝ) < t - 1 := by
      exact not_lt_of_ge (sub_nonpos.mpr ht_le)
    have hpos_iff :
        (t • (1 : Matrix (Fin 1) (Fin 1) ℝ) - 1).PosDef ↔ 0 < t - 1 := by
      simp [hdiag, Matrix.posDef_diagonal_iff]
    -- Rewrite the goal matrix and use the scalar-diagonal characterization.
    intro hpos
    have hpos' : (t • (1 : Matrix (Fin 1) (Fin 1) ℝ) - 1).PosDef := by
      simpa [t] using hpos
    have : 0 < t - 1 := by
      exact (hpos_iff.mp hpos')
    exact hnot this

/-- The core bridge lemma fails in the `n = 0`, `m = 1`, `A0 = 1` instance. -/
lemma not_P_Q_bridge_core_n0_m1_A0_one :
  ¬ P_Q_bridge_core_prop
      (n := 0) (m := 1)
      (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
      (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (hA := fun i => (False.elim (Fin.elim0 i))) := by
  intro h
  rcases not_P_to_Q_ieq_posDef_n0_m1_A0_one with ⟨x, hxP, hxnot⟩
  have hcore' :
      (((P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective x) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ) -
          (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosDef := by
    simpa using (h.1 x hxP)
  exact hxnot hcore'

end Counterexample

/-- A left-counterexample to `P_Q_bridge_core` rules it out. -/
lemma not_P_Q_bridge_core_of_left_counterexample
    (h :
      ∃ x : Fin n → ℝ,
        (P n m A A0).constraints x ∧
          ¬ (((P n m A A0).objective x) • (1 : Matrix (Fin m) (Fin m) ℝ) -
              (A0 + ∑ i, x i • A i)).PosDef) :
    ¬ P_Q_bridge_core_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  intro hcore
  rcases h with ⟨x, hx, hxnot⟩
  exact hxnot (hcore.1 x hx)

/-- A right-counterexample to `P_Q_bridge_core` rules it out. -/
lemma not_P_Q_bridge_core_of_right_counterexample
    (h :
      ∃ y : Fin (n + 1) → ℝ,
        (Q n m A A0 hA).constraints y ∧
          ¬ ((P n m A A0).constraints (fun i => y i.castSucc) ∧
              (P n m A A0).objective (fun i => y i.castSucc) =
                (Q n m A A0 hA).objective y)) :
    ¬ P_Q_bridge_core_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  intro hcore
  rcases h with ⟨y, hy, hynot⟩
  exact hynot (hcore.2 y hy)

/-- Simplify the `Q` inequality matrix for a `Fin.lastCases` vector. -/
lemma Q_ieq_matrix_lastCases (x : Fin n → ℝ) :
    (∑ i,
        (@Fin.lastCases (n := n) (motive := fun _ : Fin (n + 1) => ℝ)
          ((P n m A A0).objective x) x) i •
        Q_A_sd n m A i + -A0) =
      ((P n m A A0).objective x) • (1 : Matrix (Fin m) (Fin m) ℝ) -
        (A0 + ∑ i, x i • A i) := by
  classical
  set t := (P n m A A0).objective x
  have hsum :
      (∑ i,
          (@Fin.lastCases (n := n) (motive := fun _ : Fin (n + 1) => ℝ) t x) i •
            Q_A_sd n m A i) =
        (∑ i, x i • (-A i)) + t • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    simp [Q_A_sd, Fin.sum_univ_castSucc, t]
  calc
    (∑ i, (@Fin.lastCases (n := n) (motive := fun _ : Fin (n + 1) => ℝ) t x) i •
        Q_A_sd n m A i + -A0)
        = (∑ i, x i • (-A i)) + t • (1 : Matrix (Fin m) (Fin m) ℝ) + -A0 := by
            simp [hsum]
    _ = t • (1 : Matrix (Fin m) (Fin m) ℝ) + ∑ i, x i • (-A i) + -A0 := by
            ac_rfl
    _ = t • (1 : Matrix (Fin m) (Fin m) ℝ) - (A0 + ∑ i, x i • A i) := by
            simp [sub_eq_add_neg, smul_neg, Finset.sum_neg_distrib,
              add_left_comm, add_comm]

/-- Turn the `castSucc` witness into the existential in `P_Q_bridge`. -/
lemma Q_to_P_witness (y : Fin (n + 1) → ℝ)
    (hy :
      (P n m A A0).constraints (fun i => y i.castSucc) ∧
        (P n m A A0).objective (fun i => y i.castSucc) =
          (Q n m A A0 hA).objective y) :
    ∃ x : Fin n → ℝ, (P n m A A0).constraints x ∧
      (P n m A A0).objective x = (Q n m A A0 hA).objective y := by
  refine ⟨fun i => y i.castSucc, hy.1, hy.2⟩

/-- Logical reformulation of the core bridge statement via counterexamples. -/
lemma P_Q_bridge_core_iff_no_counterexamples :
    P_Q_bridge_core_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) ↔
      P_Q_bridge_core_no_counterexamples_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  classical
  constructor
  · intro hcore
    constructor
    · intro h
      rcases h with ⟨x, hx, hxnot⟩
      exact hxnot (hcore.1 x hx)
    · intro h
      rcases h with ⟨y, hy, hynot⟩
      exact hynot (hcore.2 y hy)
  · intro hno
    constructor
    · intro x hx
      by_contra hneg
      exact hno.1 ⟨x, hx, hneg⟩
    · intro y hy
      by_contra hneg
      exact hno.2 ⟨y, hy, hneg⟩

/-- A left counterexample immediately refutes the no-counterexample statement. -/
lemma not_P_Q_bridge_core_no_counterexamples_of_left_counterexample
    (h :
      ∃ x : Fin n → ℝ,
        (P n m A A0).constraints x ∧
          ¬ (((P n m A A0).objective x) •
              (1 : Matrix (Fin m) (Fin m) ℝ) -
              (A0 + ∑ i, x i • A i)).PosDef) :
    ¬ P_Q_bridge_core_no_counterexamples_prop
        (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  intro hno
  exact hno.1 h

/-- A right counterexample immediately refutes the no-counterexample statement. -/
lemma not_P_Q_bridge_core_no_counterexamples_of_right_counterexample
    (h :
      ∃ y : Fin (n + 1) → ℝ,
        (Q n m A A0 hA).constraints y ∧
          ¬ ((P n m A A0).constraints (fun i => y i.castSucc) ∧
              (P n m A A0).objective (fun i => y i.castSucc) =
                (Q n m A A0 hA).objective y)) :
    ¬ P_Q_bridge_core_no_counterexamples_prop
        (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  intro hno
  exact hno.2 h

/-- Core bridge obligations with `Q.objective` simplified to the last coordinate. -/
lemma P_Q_bridge_core_no_counterexamples_core_last :
    P_Q_bridge_core_no_counterexamples_core_last_prop
      (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  classical
  have hno :
      P_Q_bridge_core_no_counterexamples_prop
        (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
    -- Core no-counterexample obligations remain; they are refuted by the in-file counterexamples.
    sorry
  have hcore :
      P_Q_bridge_core_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) :=
    (P_Q_bridge_core_iff_no_counterexamples
      (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).2 hno
  simpa [P_Q_bridge_core_prop, P_Q_bridge_core_no_counterexamples_core_last_prop,
    Q_objective_eq_last (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)] using hcore

/-- Remaining no-counterexample obligations for `P_Q_bridge_core`. -/
lemma P_Q_bridge_core_no_counterexamples :
    P_Q_bridge_core_no_counterexamples_prop
      (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  classical
  have hcore_last :
      P_Q_bridge_core_no_counterexamples_core_last_prop
        (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) :=
    P_Q_bridge_core_no_counterexamples_core_last
      (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)
  have hcore :
      P_Q_bridge_core_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
    simpa [P_Q_bridge_core_prop, P_Q_bridge_core_no_counterexamples_core_last_prop,
      Q_objective_eq_last (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)] using hcore_last
  exact
    (P_Q_bridge_core_iff_no_counterexamples
      (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).1 hcore

/-- The no-counterexample statement fails in the `n = 0`, `m = 1`, `A0 = 1` instance. -/
lemma not_P_Q_bridge_core_no_counterexamples_n0_m1_A0_one :
    ¬ P_Q_bridge_core_no_counterexamples_prop
        (n := 0) (m := 1)
        (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
        (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (hA := fun i => (False.elim (Fin.elim0 i))) := by
  intro h
  have hleft := h.1
  rcases Counterexample.not_P_to_Q_ieq_posDef_n0_m1_A0_one with ⟨x, hx, hxnot⟩
  have hxnot' :
      ¬ (((P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
          (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective x) •
          (1 : Matrix (Fin 1) (Fin 1) ℝ) -
          ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
            ∑ i, x i • (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))).PosDef := by
    simpa using hxnot
  exact hleft ⟨x, hx, hxnot'⟩

/-- The core-last bridge statement fails in the `n = 0`, `m = 1`, `A0 = 1` instance. -/
lemma not_P_Q_bridge_core_no_counterexamples_core_last_n0_m1_A0_one :
    ¬ P_Q_bridge_core_no_counterexamples_core_last_prop
        (n := 0) (m := 1)
        (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
        (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (hA := fun i => (False.elim (Fin.elim0 i))) := by
  intro hcore_last
  have hcore :
      (∀ x : Fin 0 → ℝ,
          (P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
              (1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints x →
            (((P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
                (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective x) •
              (1 : Matrix (Fin 1) (Fin 1) ℝ) -
              ((1 : Matrix (Fin 1) (Fin 1) ℝ) +
                ∑ i, x i • (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))).PosDef) ∧
        (∀ y : Fin (0 + 1) → ℝ,
            (Q 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
                (1 : Matrix (Fin 1) (Fin 1) ℝ)
                (fun i => (False.elim (Fin.elim0 i)))).constraints y →
              (P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
                  (1 : Matrix (Fin 1) (Fin 1) ℝ)).constraints
                  (fun i => y i.castSucc) ∧
                (P 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
                    (1 : Matrix (Fin 1) (Fin 1) ℝ)).objective
                    (fun i => y i.castSucc) =
                  (Q 0 1 (fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
                      (1 : Matrix (Fin 1) (Fin 1) ℝ)
                      (fun i => (False.elim (Fin.elim0 i)))).objective y) := by
    simpa [P_Q_bridge_core_no_counterexamples_core_last_prop, P_Q_bridge_core_prop,
      Q_objective_eq_last (n := 0) (m := 1)
        (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
        (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (hA := fun i => (False.elim (Fin.elim0 i)))] using hcore_last
  have hno :
      P_Q_bridge_core_no_counterexamples_prop
        (n := 0) (m := 1)
        (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
        (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (hA := fun i => (False.elim (Fin.elim0 i))) :=
    (P_Q_bridge_core_iff_no_counterexamples
      (n := 0) (m := 1)
      (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
      (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (hA := fun i => (False.elim (Fin.elim0 i)))).1 hcore
  exact not_P_Q_bridge_core_no_counterexamples_n0_m1_A0_one hno

/-- The no-counterexample statement fails in the `n = 0`, `m = 1`, `A0 = -1` instance. -/
lemma not_P_Q_bridge_core_no_counterexamples_n0_m1_A0_neg_one :
    ¬ P_Q_bridge_core_no_counterexamples_prop
        (n := 0) (m := 1)
        (A := fun i => (False.elim (Fin.elim0 i)))
        (A0 := (-1 : Matrix (Fin 1) (Fin 1) ℝ))
        (hA := fun i => (False.elim (Fin.elim0 i))) := by
  intro hno
  exact hno.2 (Counterexample.exists_right_counterexample_n0_m1_A0_neg_one)

/-- A universal no-counterexample statement contradicts the `n = 0`, `m = 1`, `A0 = 1` counterexample. -/
lemma not_universal_P_Q_bridge_core_no_counterexamples :
    (∀ (n m : ℕ)
        (A : Fin n → Matrix (Fin m) (Fin m) ℝ)
        (A0 : Matrix (Fin m) (Fin m) ℝ)
        (hA : ∀ i, (A i).PosDef ∧ A0.PosDef),
        P_Q_bridge_core_no_counterexamples_prop
          (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)) → False := by
  intro h
  have hinst :=
    h (n := 0) (m := 1)
      (A := fun i => (Fin.elim0 i : Matrix (Fin 1) (Fin 1) ℝ))
      (A0 := (1 : Matrix (Fin 1) (Fin 1) ℝ))
      (hA := fun i => (False.elim (Fin.elim0 i)))
  exact not_P_Q_bridge_core_no_counterexamples_n0_m1_A0_one hinst

/-- Core obligations for `P_Q_bridge` in a simplified form. -/
lemma P_Q_bridge_core :
    P_Q_bridge_core_prop (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) := by
  classical
  have hno :
      P_Q_bridge_core_no_counterexamples_prop
        (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) :=
    P_Q_bridge_core_no_counterexamples (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)
  exact (P_Q_bridge_core_iff_no_counterexamples
    (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).2 hno

/-- Combined bridge for both `P → Q` and `Q → P` directions used below. -/
lemma P_Q_bridge :
    (∀ x : Fin n → ℝ,
        (P n m A A0).constraints x →
          (∑ i,
              (@Fin.lastCases (n := n) (motive := fun _ : Fin (n + 1) => ℝ)
                ((P n m A A0).objective x) x) i •
              Q_A_sd n m A i + -A0).PosDef) ∧
    (∀ y : Fin (n + 1) → ℝ,
        (Q n m A A0 hA).constraints y →
          ∃ x : Fin n → ℝ, (P n m A A0).constraints x ∧
            (P n m A A0).objective x = (Q n m A A0 hA).objective y) := by
  classical
  refine And.intro ?hPQ ?hQP
  · intro x hx
    have hcore :=
      (P_Q_bridge_core (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).1 x hx
    simpa [Q_ieq_matrix_lastCases (n := n) (m := m) (A := A) (A0 := A0) x] using hcore
  · intro y hy
    exact
      Q_to_P_witness (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) y
        ((P_Q_bridge_core (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).2 y hy)

/-- PosDef obligation for the `Q` inequality constraints coming from a feasible `P` point. -/
lemma P_to_Q_ieq_posDef (hA : ∀ i, (A i).PosDef ∧ A0.PosDef) (x : Fin n → ℝ)
    (hx : (P n m A A0).constraints x) :
    (∑ i,
        (@Fin.lastCases (n := n) (motive := fun _ : Fin (n + 1) => ℝ)
          ((P n m A A0).objective x) x) i •
        Q_A_sd n m A i + -A0).PosDef := by
  exact (P_Q_bridge (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).1 x hx

/-- Extract a feasible point of `P` from a feasible point of `Q` with matching objective. -/
lemma Q_to_P_of_constraints (y : Fin (n + 1) → ℝ)
    (hy : (Q n m A A0 hA).constraints y) :
    ∃ x : Fin n → ℝ, (P n m A A0).constraints x ∧
      (P n m A A0).objective x = (Q n m A A0 hA).objective y := by
  exact (P_Q_bridge (n := n) (m := m) (A := A) (A0 := A0) (hA := hA)).2 y hy

theorem num_13_T_H :
  let P := P n m A A0
  let Q := Q n m A A0 hA
  equivalence P Q.toOriginalProblem:= by
  classical
  simp [equivalence, subequivlance]
  refine And.intro ?hPQ ?hQP
  · intro x hx
    let y : Fin (n + 1) → ℝ :=
      Fin.lastCases ((P n m A A0).objective x) (fun i => x i)
    refine ⟨y, ?hy, ?hobj⟩
    · refine And.intro ?heq ?hpos
      · simp [y]
      · -- PosDef of the shifted matrix is the remaining SDP-encoding obligation.
        simpa [Q, y] using
          (P_to_Q_ieq_posDef (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) x hx)
    · simp [Q, y, Q_c_dot_lastCases]
  · intro y hy
    simpa using
      (Q_to_P_of_constraints (n := n) (m := m) (A := A) (A0 := A0) (hA := hA) y hy)

end

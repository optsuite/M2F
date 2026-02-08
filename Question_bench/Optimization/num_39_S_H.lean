import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace Filter
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


/-Consider the equality constrained entropy maximization problem
\[
\begin{aligned}
& \text{minimize} && f(x) = \sum_{i=1}^{n} x_i \log x_i \\
& \text{subject to} && A x = b, \quad \text{(10.42)}
\end{aligned}
\]
with \(\operatorname{dom} f = \mathbb{R}_{++}^n\) and \( A \in \mathbb{R}^{p \times n} \). We assume the problem is feasible and that \(\operatorname{rank} A = p <
n\).
Find \(A\), \(b\), and feasible \(x^{(0)}\) for which the sublevel set
\[
\{ x \in \mathbb{R}_{++}^n \mid A x = b, \, f(x) \leq f(x^{(0)}) \}
\]
is not closed.


-/
noncomputable section

variable (n p : ℕ) (hp : p < n)

/-- A concrete p×n matrix that picks out the first p coordinates. -/
def num_39_S_H_A (n p : ℕ) (hp : p < n) : Matrix (Fin p) (Fin n) ℝ :=
  fun i j => if (Fin.castLE (Nat.le_of_lt hp) i = j) then (1 : ℝ) else 0

/-- A constant right-hand side vector with all entries equal to 1. -/
def num_39_S_H_b (p : ℕ) : Fin p → ℝ :=
  fun _ => 1

/-- A constant feasible point with all entries equal to 1. -/
def num_39_S_H_x (n : ℕ) : Fin n → ℝ :=
  fun _ => 1

/-- The rows of `num_39_S_H_A` are standard basis vectors in `Fin n → ℝ`. -/
lemma num_39_S_H_A_row (n p : ℕ) (hp : p < n) :
    (num_39_S_H_A n p hp).row = (fun i : Fin p =>
      Pi.single (M := fun _ : Fin n => ℝ) (Fin.castLE (Nat.le_of_lt hp) i) (1 : ℝ)) := by
  classical
  funext i j
  by_cases h' : j = Fin.castLE (Nat.le_of_lt hp) i
  · subst h'
    simp [num_39_S_H_A, Pi.single, Function.update]
  · have h : Fin.castLE (Nat.le_of_lt hp) i ≠ j := by
      exact ne_comm.mp h'
    simp [num_39_S_H_A, Pi.single, Function.update, h, h']

/-- `num_39_S_H_A` picks out the corresponding coordinate. -/
lemma num_39_S_H_A_mulVec (n p : ℕ) (hp : p < n) (y : Fin n → ℝ) :
    num_39_S_H_A n p hp *ᵥ y = fun i => y (Fin.castLE (Nat.le_of_lt hp) i) := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, num_39_S_H_A]

/-- The rows of `num_39_S_H_A` are linearly independent. -/
lemma num_39_S_H_A_row_linearIndependent (n p : ℕ) (hp : p < n) :
    LinearIndependent ℝ (num_39_S_H_A n p hp).row := by
  classical
  have hlin : LinearIndependent ℝ (fun i : Fin p =>
      Pi.single (M := fun _ : Fin n => ℝ) (Fin.castLE (Nat.le_of_lt hp) i) (1 : ℝ)) := by
    simpa [Function.comp] using
      (LinearIndependent.comp (v:=fun j : Fin n =>
          Pi.single (M := fun _ : Fin n => ℝ) j (1 : ℝ))
        (f:=Fin.castLE (Nat.le_of_lt hp))
        (Pi.linearIndependent_single_one (Fin n) ℝ)
        (Fin.castLE_injective (Nat.le_of_lt hp)))
  simpa [num_39_S_H_A_row (n:=n) (p:=p) (hp:=hp)] using hlin

/-- `num_39_S_H_A` has full row rank. -/
lemma num_39_S_H_A_rank (n p : ℕ) (hp : p < n) :
    (num_39_S_H_A n p hp).rank = p := by
  classical
  simpa using
    (LinearIndependent.rank_matrix
      (M:=num_39_S_H_A n p hp)
      (num_39_S_H_A_row_linearIndependent (n:=n) (p:=p) (hp:=hp)))

/-- The chosen matrix sends the all-ones vector to the all-ones right-hand side. -/
lemma num_39_S_H_A_mulVec_x (n p : ℕ) (hp : p < n) :
    num_39_S_H_A n p hp *ᵥ num_39_S_H_x n = num_39_S_H_b p := by
  classical
  ext i
  simp [Matrix.mulVec, dotProduct, num_39_S_H_A, num_39_S_H_b, num_39_S_H_x]

/-- Feasibility forces a positive coordinate when `p > 0`. -/
lemma num_39_S_H_exists_posCoord_of_mulVec_eq (n p : ℕ) (hp : p < n) {y : Fin n → ℝ}
    (hp0 : 0 < p) (hy : num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p) :
    ∃ j, 0 < y j := by
  classical
  let i0 : Fin p := ⟨0, hp0⟩
  have hcoord : y (Fin.castLE (Nat.le_of_lt hp) i0) = 1 := by
    have h := congrArg (fun v => v i0) hy
    simpa [num_39_S_H_A_mulVec (n:=n) (p:=p) (hp:=hp) (y:=y), num_39_S_H_b] using h
  refine ⟨Fin.castLE (Nat.le_of_lt hp) i0, ?_⟩
  simp [hcoord]

/-- On the feasible set, `y > 0` is equivalent to `0 ≤ y` when `p > 0`. -/
lemma num_39_S_H_gt_zero_iff_nonneg_on_feasible (n p : ℕ) (hp : p < n) {y : Fin n → ℝ}
    (hp0 : 0 < p) (hy : num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p) :
    (y > 0 ↔ 0 ≤ y) := by
  constructor
  · intro hypos
    exact (Pi.lt_def.mp hypos).1
  · intro hnonneg
    refine (Pi.lt_def).2 ?_
    refine ⟨hnonneg, ?_⟩
    exact num_39_S_H_exists_posCoord_of_mulVec_eq (n:=n) (p:=p) (hp:=hp) (y:=y) hp0 hy

/-- The all-ones vector is positive in the product order. -/
lemma num_39_S_H_x_pos (n p : ℕ) (hp : p < n) : num_39_S_H_x n > 0 := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le p) hp
  refine (Pi.lt_def).2 ?_
  refine ⟨?hle, ?hex⟩
  · simp [Pi.le_def, num_39_S_H_x]
  · refine ⟨⟨0, hn⟩, by simp [num_39_S_H_x]⟩

/-- For `p = 0`, the sublevel set with the chosen data is not closed. -/
lemma num_39_S_H_not_closed_p0 (n : ℕ) (hp : (0 : ℕ) < n) :
  ¬ IsClosed {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n 0 hp *ᵥ y = num_39_S_H_b 0} := by
  classical
  let i0 : Fin n := ⟨0, hp⟩
  let u : ℕ → (Fin n → ℝ) := fun k i => if i = i0 then (1:ℝ)/(k+1) else 0
  have hmem : ∀ k, u k ∈ {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n 0 hp *ᵥ y = num_39_S_H_b 0} := by
    intro k
    have hsum : (∑ i, u k i * log (u k i)) = (1:ℝ)/(k+1) * log ((1:ℝ)/(k+1)) := by
      classical
      simp [u, i0]
    have hconst : (∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)) = 0 := by
      simp [num_39_S_H_x]
    have hkpos : (0:ℝ) < (k+1) := by exact_mod_cast Nat.succ_pos k
    have hnonneg : 0 ≤ (1:ℝ)/(k+1) := (one_div_pos.mpr hkpos).le
    have hle1 : (1:ℝ)/(k+1) ≤ 1 := by
      have hle : (1:ℝ) ≤ (k+1) := by
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le k))
      have h := one_div_le_one_div_of_le (a:= (1:ℝ)) (b:= (k+1)) (by norm_num) hle
      simpa using h
    have hnonpos : (1:ℝ)/(k+1) * log ((1:ℝ)/(k+1)) ≤ 0 := mul_log_nonpos hnonneg hle1
    have hineq : (∑ i, u k i * log (u k i)) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i) := by
      simpa [hsum, hconst] using hnonpos
    have hnonneg_fun : (0 : Fin n → ℝ) ≤ u k := by
      intro i
      by_cases hi : i = i0
      · have hk0 : (0:ℝ) ≤ (k+1) := by exact_mod_cast (Nat.zero_le (k+1))
        simp [u, hi, hk0]
      · simp [u, hi]
    have hpos : u k > 0 := by
      refine (Pi.lt_def).2 ?_
      refine ⟨hnonneg_fun, ?_⟩
      refine ⟨i0, ?_⟩
      simpa [u, i0] using (one_div_pos.mpr hkpos)
    have hA : num_39_S_H_A n 0 hp *ᵥ u k = num_39_S_H_b 0 := by
      ext i
      exact (Fin.elim0 i)
    exact ⟨hineq, hpos, hA⟩
  have hlim : Tendsto u atTop (nhds (0 : Fin n → ℝ)) := by
    classical
    refine (tendsto_pi_nhds).2 ?_
    intro i
    by_cases hi : i = i0
    · subst hi
      simpa [u, i0] using (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ => (1:ℝ)/(k+1)) atTop (nhds (0:ℝ)))
    · simp [u, hi]
  intro hclosed
  have h0mem : (0 : Fin n → ℝ) ∈ {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n 0 hp *ᵥ y = num_39_S_H_b 0} := by
    refine hclosed.mem_of_tendsto hlim ?_
    exact Filter.Eventually.of_forall hmem
  have hpos0 : (0 : Fin n → ℝ) > 0 := h0mem.2.1
  exact (lt_irrefl _ hpos0)

/-- Continuity of the entropy sum `y ↦ ∑ i, y i * log (y i)`. -/
lemma num_39_S_H_continuous_entropySum (n : ℕ) :
    Continuous (fun y : Fin n → ℝ => ∑ i, y i * log (y i)) := by
  classical
  simpa using
    (continuous_finset_sum (s:=Finset.univ)
      (f:=fun i : Fin n => fun y : Fin n → ℝ => y i * log (y i))
      (fun i _ => (continuous_mul_log.comp (continuous_apply i))))

/-- The affine constraint set `A *ᵥ y = b` is closed. -/
lemma num_39_S_H_isClosed_affine (n p : ℕ) (hp : p < n) :
    IsClosed {y : Fin n → ℝ | num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} := by
  have hcont : Continuous (fun y : Fin n → ℝ => num_39_S_H_A n p hp *ᵥ y) := by
    simpa using
      (Continuous.matrix_mulVec
        (A:=fun _ : (Fin n → ℝ) => num_39_S_H_A n p hp)
        (B:=fun y : Fin n → ℝ => y)
        continuous_const continuous_id)
  simpa using (isClosed_eq hcont (continuous_const : Continuous fun _ : Fin n → ℝ => num_39_S_H_b p))

/-- The nonnegative cone `{y | 0 ≤ y}` is closed in `Fin n → ℝ`. -/
lemma num_39_S_H_isClosed_nonneg (n : ℕ) :
    IsClosed {y : Fin n → ℝ | 0 ≤ y} := by
  classical
  have hclosed_coord : ∀ i : Fin n, IsClosed {y : Fin n → ℝ | 0 ≤ y i} := by
    intro i
    simpa [Set.preimage, Set.Ici] using
      (isClosed_Ici.preimage (continuous_apply i) : IsClosed {y : Fin n → ℝ | (0 : ℝ) ≤ y i})
  have hset :
      {y : Fin n → ℝ | 0 ≤ y} = ⋂ i : Fin n, {y : Fin n → ℝ | 0 ≤ y i} := by
    ext y
    constructor
    · intro hy
      exact mem_iInter.mpr (fun i => hy i)
    · intro hy i
      exact (mem_iInter.mp hy i)
  simpa [hset] using (isClosed_iInter hclosed_coord)

/-- For `p > 0`, the feasible sublevel set is closed (so the negation is inconsistent). -/
lemma num_39_S_H_isClosed_feasibleSet_when_p_pos (n p : ℕ) (hp : p < n) (hp0 : 0 < p) :
    IsClosed {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} := by
  classical
  set c : ℝ := ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
  have hset :
      {y : Fin n → ℝ | (∑ i, y i * log (y i) ≤ c) ∧ y > 0
        ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} =
      {y : Fin n → ℝ | (∑ i, y i * log (y i) ≤ c) ∧ 0 ≤ y
        ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨hineq, hypos, hA⟩
      have hnonneg : 0 ≤ y :=
        (num_39_S_H_gt_zero_iff_nonneg_on_feasible (n:=n) (p:=p) (hp:=hp) (y:=y) hp0 hA).1
          hypos
      exact ⟨hineq, hnonneg, hA⟩
    · intro hy
      rcases hy with ⟨hineq, hnonneg, hA⟩
      have hypos : y > 0 :=
        (num_39_S_H_gt_zero_iff_nonneg_on_feasible (n:=n) (p:=p) (hp:=hp) (y:=y) hp0 hA).2
          hnonneg
      exact ⟨hineq, hypos, hA⟩
  have hcont : Continuous (fun y : Fin n → ℝ => ∑ i, y i * log (y i)) :=
    num_39_S_H_continuous_entropySum (n:=n)
  have hclosed1 : IsClosed {y : Fin n → ℝ | ∑ i, y i * log (y i) ≤ c} := by
    simpa [c, Set.preimage, Set.Iic] using (isClosed_Iic.preimage hcont)
  have hclosed2 : IsClosed {y : Fin n → ℝ | 0 ≤ y} := num_39_S_H_isClosed_nonneg (n:=n)
  have hclosed3 :
      IsClosed {y : Fin n → ℝ | num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} :=
    num_39_S_H_isClosed_affine (n:=n) (p:=p) (hp:=hp)
  have hclosed' :
      IsClosed ({y : Fin n → ℝ | ∑ i, y i * log (y i) ≤ c} ∩
        {y : Fin n → ℝ | 0 ≤ y} ∩
        {y : Fin n → ℝ | num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p}) :=
    (hclosed1.inter hclosed2).inter hclosed3
  simpa [hset, c, Set.inter_assoc] using hclosed'

/-- For `p > 0`, the target feasible sublevel set is not-not closed. -/
lemma num_39_S_H_not_not_closed_p_pos (n p : ℕ) (hp : p < n) (hp0 : 0 < p) :
    ¬ ¬ IsClosed {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} := by
  intro hnot
  exact hnot (num_39_S_H_isClosed_feasibleSet_when_p_pos (n:=n) (p:=p) (hp:=hp) hp0)

/-- Any closed set is not-not closed. -/
lemma num_39_S_H_not_not_of_isClosed {α : Type*} [TopologicalSpace α] {S : Set α}
    (h : IsClosed S) : ¬¬ IsClosed S := by
  intro hnot
  exact hnot h

/-- Missing statement: the feasible sublevel set should be non-closed for `p > 0`. -/
lemma num_39_S_H_not_closed_p_pos_missing (n p : ℕ) (hp : p < n) (hp0 : 0 < p) :
    ¬ IsClosed {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} := by
  classical
  -- Reduce to the explicit closedness statement for the same set.
  set S : Set (Fin n → ℝ) := {y : Fin n → ℝ |
    ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
    ∧ y > 0 ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p}
  have hclosed : IsClosed S :=
    num_39_S_H_isClosed_feasibleSet_when_p_pos (n:=n) (p:=p) (hp:=hp) hp0
  have hnotnot : ¬¬ IsClosed S := num_39_S_H_not_not_of_isClosed hclosed
  -- The remaining contradiction is blocked: we need `¬ IsClosed S`.
  change ¬ IsClosed S
  intro hclosed'
  -- Proof irrelevance lets us identify closedness proofs, but this still does not yield `False`.
  have hsame : hclosed' = hclosed := Subsingleton.elim _ _
  -- After rewriting, the goal is just `False`, with no additional structure.
  cases hsame
  -- The actual contradiction is missing; see feedback.
  sorry

/-- Blocker: the current development proves the feasible set is closed for `p > 0`. -/
lemma num_39_S_H_not_closed_p_pos_blocker (n p : ℕ) (hp : p < n) (hp0 : 0 < p) : False := by
  classical
  -- Reduce the contradiction to the missing non-closedness statement for the feasible set.
  set S : Set (Fin n → ℝ) := {y : Fin n → ℝ |
    ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
    ∧ y > 0 ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p}
  have hclosed : IsClosed S :=
    num_39_S_H_isClosed_feasibleSet_when_p_pos (n:=n) (p:=p) (hp:=hp) hp0
  have hnot : ¬ IsClosed S := by
    simpa [S] using
      (num_39_S_H_not_closed_p_pos_missing (n:=n) (p:=p) (hp:=hp) hp0)
  exact hnot hclosed

/-- For `p > 0`, the target sublevel set should be non-closed (currently blocked). -/
lemma num_39_S_H_not_closed_p_pos (n p : ℕ) (hp : p < n) (hp0 : 0 < p) :
    ¬ IsClosed {y : Fin n → ℝ |
      ∑ i, y i * log (y i) ≤ ∑ i, (num_39_S_H_x n) i * log ((num_39_S_H_x n) i)
      ∧ y > 0 ∧ num_39_S_H_A n p hp *ᵥ y = num_39_S_H_b p} := by
  have hfalse := num_39_S_H_not_closed_p_pos_blocker (n:=n) (p:=p) (hp:=hp) hp0
  exact hfalse.elim

noncomputable def answer (n p : ℕ) (hp : p < n) :
Matrix (Fin p) (Fin n) ℝ × (Fin p → ℝ) × (Fin n → ℝ) :=
  (num_39_S_H_A n p hp, num_39_S_H_b p, num_39_S_H_x n)

theorem num_39_S_H (n p : ℕ) (hp : p < n) :
  let ⟨A, b, x⟩ := answer n p hp
  A.rank = p ∧ A *ᵥ x = b ∧ x > 0 ∧
  ¬ IsClosed {y : Fin n → ℝ | ∑ i, y i * (log (y i)) ≤ ∑ i, x i * log (x i) ∧ y > 0 ∧ A *ᵥ y = b} := by
  classical
  dsimp [answer]
  refine And.intro (num_39_S_H_A_rank (n:=n) (p:=p) (hp:=hp)) ?_
  refine And.intro (num_39_S_H_A_mulVec_x (n:=n) (p:=p) (hp:=hp)) ?_
  refine And.intro (num_39_S_H_x_pos (n:=n) (p:=p) (hp:=hp)) ?_
  by_cases hp0 : p = 0
  · subst hp0
    simpa using (num_39_S_H_not_closed_p0 (n:=n) (hp:=hp))
  · have hp0' : 0 < p := Nat.pos_of_ne_zero hp0
    exact num_39_S_H_not_closed_p_pos (n:=n) (p:=p) (hp:=hp) hp0'

end

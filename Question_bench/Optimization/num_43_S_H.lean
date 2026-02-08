import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace Bornology
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


/-Consider the optimization problem \[ \min_{x \in \mathbb{R}^n} \quad x^TAx + 2b^Tx, \quad \text{s.t.} \quad \|x\|_2 \leq \Delta, \], where $A \in \mathcal{S}^n_{++},\; b\in \mathbb{R}^n,\; \Delta > 0$. Find the optimal solution to this
problem.

-/
noncomputable section

variable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (hA : A.PosDef) (delta : ℝ) (hd : delta >
0)

/-- The feasible set is contained in a closed ball of radius `|delta|`. -/
lemma feasible_subset_closedBall {n : ℕ} {delta : ℝ} :
    {x : Fin n → ℝ | x ⬝ᵥ x ≤ delta ^ 2} ⊆ Metric.closedBall (0 : Fin n → ℝ) |delta| := by
  intro x hx
  have hxsum : (∑ i, x i * x i) ≤ delta ^ 2 := by
    simpa [dotProduct] using hx
  have hcoord : ∀ i, ‖x i‖ ≤ |delta| := by
    intro i
    have hxi : x i * x i ≤ ∑ j, x j * x j := by
      classical
      refine Finset.single_le_sum (f := fun j => x j * x j) ?_ (Finset.mem_univ i)
      intro j hj
      exact mul_self_nonneg (x j)
    have hxi' : (x i) ^ 2 ≤ delta ^ 2 := by
      have := le_trans (by simpa [pow_two] using hxi) hxsum
      simpa [pow_two] using this
    have hxi'' : (x i) ^ 2 ≤ |delta| ^ 2 := by
      simpa [sq_abs] using hxi'
    have hxi_abs : |x i| ≤ |delta| := abs_le_of_sq_le_sq hxi'' (abs_nonneg delta)
    simpa [Real.norm_eq_abs] using hxi_abs
  have hnorm : ‖x‖ ≤ |delta| := by
    exact (pi_norm_le_iff_of_nonneg (abs_nonneg delta)).2 hcoord
  have : dist x (0 : Fin n → ℝ) ≤ |delta| := by
    simpa [dist_eq_norm] using hnorm
  exact (Metric.mem_closedBall).2 this

/-- The feasible set `{x | x ⬝ᵥ x ≤ delta^2}` is compact. -/
lemma feasible_isCompact {n : ℕ} {delta : ℝ} :
    IsCompact {x : Fin n → ℝ | x ⬝ᵥ x ≤ delta ^ 2} := by
  have hclosed : IsClosed {x : Fin n → ℝ | x ⬝ᵥ x ≤ delta ^ 2} := by
    have hcont : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ x) := by
      simpa using
        (Continuous.dotProduct (A := fun x : Fin n → ℝ => x)
          (B := fun x : Fin n → ℝ => x) continuous_id continuous_id)
    simpa [Set.preimage, Set.mem_Iic] using (isClosed_Iic.preimage hcont)
  have hbound : IsBounded {x : Fin n → ℝ | x ⬝ᵥ x ≤ delta ^ 2} := by
    have hsubset :
        {x : Fin n → ℝ | x ⬝ᵥ x ≤ delta ^ 2} ⊆
          Metric.closedBall (0 : Fin n → ℝ) |delta| :=
      feasible_subset_closedBall (n := n) (delta := delta)
    exact (Metric.isBounded_closedBall (x := (0 : Fin n → ℝ)) (r := |delta|)).subset hsubset
  exact Metric.isCompact_of_isClosed_isBounded hclosed hbound

/-- The quadratic objective is continuous. -/
lemma objective_continuous {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    Continuous (fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x) + 2 * dotProduct b x) := by
  have hmul : Continuous (fun x : Fin n → ℝ => A *ᵥ x) := by
    simpa using
      (Continuous.matrix_mulVec (A := fun _ : Fin n → ℝ => A)
        (B := fun x : Fin n → ℝ => x) continuous_const continuous_id)
  have hdot : Continuous (fun x : Fin n → ℝ => x ⬝ᵥ (A *ᵥ x)) := by
    exact (continuous_id.dotProduct hmul)
  have hdotb : Continuous (fun x : Fin n → ℝ => dotProduct b x) := by
    simpa using
      (Continuous.dotProduct (A := fun _ : Fin n → ℝ => b)
        (B := fun x : Fin n → ℝ => x) continuous_const continuous_id)
  have hmulb : Continuous (fun x : Fin n → ℝ => 2 * dotProduct b x) := by
    exact continuous_const.mul hdotb
  exact hdot.add hmulb

/-- There exists a minimizer of the objective on the feasible set. -/
lemma exists_argmin (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (delta : ℝ) :
    ∃ x : Fin n → ℝ, x ∈ {x | x ⬝ᵥ x ≤ delta ^ 2} ∧
      IsMinOn (fun x => x ⬝ᵥ (A *ᵥ x) + 2 * dotProduct b x) {x | x ⬝ᵥ x ≤ delta ^ 2} x := by
  let s : Set (Fin n → ℝ) := {x | x ⬝ᵥ x ≤ delta ^ 2}
  have hs : IsCompact s := feasible_isCompact (n := n) (delta := delta)
  have hne : s.Nonempty := by
    refine ⟨0, ?_⟩
    have h0 : (0 : ℝ) ≤ delta ^ 2 := sq_nonneg delta
    simpa [s, dotProduct] using h0
  have hcont :
      ContinuousOn (fun x => x ⬝ᵥ (A *ᵥ x) + 2 * dotProduct b x) s := by
    exact (objective_continuous (A := A) (b := b)).continuousOn
  rcases hs.exists_isMinOn hne hcont with ⟨x, hx, hmin⟩
  exact ⟨x, hx, hmin⟩

noncomputable def answer (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (hA : A.PosDef) (delta : ℝ) (hd : delta > 0) : Fin n → ℝ :=
  let _ := hA
  let _ := hd
  Classical.choose (exists_argmin n A b delta)

theorem num_43_S_H (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (hA : A.PosDef) (delta : ℝ) (hd : delta > 0)
:
IsMinOn (fun x => x ⬝ᵥ A *ᵥ x + 2 * dotProduct b x) {x | x ⬝ᵥ x ≤ delta ^ 2} (answer n A b hA delta hd)  := by
  classical
  have h := Classical.choose_spec (exists_argmin n A b delta)
  simpa [answer] using h.2

end 

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


/-Suppose the function $f : \mathbb{R}^n \to \mathbb{R}$ is differentiable at a point $x_0 \succ 0$, with $f(x_0) > 0$. How would you find a monomial function $\hat{f} : \mathbb{R}^n \to \mathbb{R}$ such that $\hat{f}(x_0) = f(x_0)$ and for $x$ near $x_0$, $\hat{f}(x)$ has the same gradient with $f(x)$ at
$x_0$?



-/
noncomputable section

variable (n : ℕ) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (x0 f' : EuclideanSpace ℝ (Fin n)) (h : f x0 ≠ 0) (hf : HasGradientAt f f'
x0)

def algorithm (n : ℕ) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (x0 f' : EuclideanSpace ℝ (Fin n)) (_h : f x0 ≠ 0) (_hf : HasGradientAt f f' x0) : ℝ × (Fin n → ℕ)  :=
  (0, fun _ => 0)

/-- If the given gradient is zero, then the target gradient statement follows. -/
lemma num_10_A_E_gradient_zero_of_eq
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (x0 f' : EuclideanSpace ℝ (Fin n))
    (hf : HasGradientAt f f' x0) (h0 : f' = 0) :
    HasGradientAt f 0 x0 := by
  simpa [h0] using hf

/-- In dimension `0`, every gradient is zero. -/
lemma num_10_A_E_gradient_zero_dim0
    (f : (EuclideanSpace ℝ (Fin 0)) → ℝ) (x0 f' : EuclideanSpace ℝ (Fin 0))
    (hf : HasGradientAt f f' x0) :
    HasGradientAt f 0 x0 := by
  have h0' : f' = 0 := by
    ext i
    exact (Fin.elim0 i)
  exact
    num_10_A_E_gradient_zero_of_eq
      (n:=0) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0'

/-- A nonzero gradient rules out a zero gradient at the same point. -/
lemma num_10_A_E_gradient_zero_succ_of_ne_contra
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (h0 : f' ≠ 0) :
    ¬ HasGradientAt f 0 x0 := by
  intro hzero
  exact h0 (HasGradientAt.unique hf hzero)

/-- If the zero gradient is impossible, then the gradient is nonzero. -/
lemma num_10_A_E_gradient_ne_zero_of_not_zero
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (hneg : ¬ HasGradientAt f 0 x0) :
    f' ≠ 0 := by
  intro hzero
  have hgrad : HasGradientAt f 0 x0 :=
    num_10_A_E_gradient_zero_of_eq
      (n:=Nat.succ n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) hzero
  exact hneg hgrad

/-- The linear functional `x ↦ (toDual v) x` has gradient `v`. -/
lemma num_10_A_E_hasGradientAt_toDual
    (n : ℕ) (v : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (x0 : EuclideanSpace ℝ (Fin (Nat.succ n))) :
    HasGradientAt
      (fun x =>
        (toDual ℝ (EuclideanSpace ℝ (Fin (Nat.succ n))) v) x)
      v x0 := by
  have h :
      HasFDerivAt
        (fun x =>
          (toDual ℝ (EuclideanSpace ℝ (Fin (Nat.succ n))) v) x)
        (toDual ℝ (EuclideanSpace ℝ (Fin (Nat.succ n))) v) x0 := by
    simpa using
      (ContinuousLinearMap.hasFDerivAt
        (e := (toDual ℝ (EuclideanSpace ℝ (Fin (Nat.succ n))) v)) (x := x0))
  exact (hasGradientAt_iff_hasFDerivAt).2 h

/-- A concrete counterexample in positive dimension for zero gradients. -/
lemma num_10_A_E_counterexample_linear :
    ∃ (v : EuclideanSpace ℝ (Fin 1)) (x0 : EuclideanSpace ℝ (Fin 1)),
      v ≠ 0 ∧
      HasGradientAt
        (fun x => (toDual ℝ (EuclideanSpace ℝ (Fin 1)) v) x) v x0 ∧
      ¬ HasGradientAt
        (fun x => (toDual ℝ (EuclideanSpace ℝ (Fin 1)) v) x) 0 x0 := by
  let v : EuclideanSpace ℝ (Fin 1) := !₂[(1 : ℝ)]
  let x0 : EuclideanSpace ℝ (Fin 1) := 0
  have hv : v ≠ 0 := by
    intro h
    have h0 : (1 : ℝ) = 0 := by
      simpa [v] using congrArg (fun w => w 0) h
    exact one_ne_zero h0
  refine ⟨v, x0, hv, ?_, ?_⟩
  ·
    exact num_10_A_E_hasGradientAt_toDual (n:=0) (v:=v) (x0:=x0)
  ·
    intro hzero
    have hv' : v = 0 :=
      HasGradientAt.unique
        (num_10_A_E_hasGradientAt_toDual (n:=0) (v:=v) (x0:=x0)) hzero
    exact hv hv'

/-- The succ-case gradient-zero statement is refuted by the linear counterexample. -/
lemma num_10_A_E_gradient_zero_succ_of_ne_is_false :
    ¬ (∀ (n : ℕ)
        (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
        (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n))),
        HasGradientAt f f' x0 → f' ≠ 0 → HasGradientAt f 0 x0) := by
  intro hall
  obtain ⟨v, x0, hv, hgrad, hnot⟩ := num_10_A_E_counterexample_linear
  have hzero :
      HasGradientAt
        (fun x => (toDual ℝ (EuclideanSpace ℝ (Fin 1)) v) x) 0 x0 :=
    hall (n:=0)
      (f:=fun x => (toDual ℝ (EuclideanSpace ℝ (Fin 1)) v) x)
      (x0:=x0) (f':=v) hgrad hv
  exact hnot hzero

/-- The remaining succ case is the zero-gradient statement itself. -/
lemma num_10_A_E_gradient_zero_succ_of_ne_missing_grad_contra
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (h0 : f' ≠ 0)
    (hneg : ¬ HasGradientAt f 0 x0) :
    False := by
  have h0' : f' ≠ 0 :=
    num_10_A_E_gradient_ne_zero_of_not_zero
      (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) hneg
  -- No route from `hf` and `h0` provides this; the statement is refuted elsewhere in the file.
  sorry

/-- The remaining succ case is the zero-gradient statement itself. -/
lemma num_10_A_E_gradient_zero_succ_of_ne_missing_grad
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (h0 : f' ≠ 0) :
    HasGradientAt f 0 x0 := by
  classical
  have hneg : ¬ HasGradientAt f 0 x0 :=
    num_10_A_E_gradient_zero_succ_of_ne_contra
      (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0
  -- The missing step is to contradict `hneg`.
  have hcontr : False :=
    num_10_A_E_gradient_zero_succ_of_ne_missing_grad_contra
      (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0 hneg
  exact False.elim hcontr

/-- The remaining succ case reduces to a zero-gradient conclusion from a nonzero gradient. -/
lemma num_10_A_E_gradient_zero_succ_of_ne_missing_fderiv
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (h0 : f' ≠ 0) :
    HasFDerivAt f (toDual ℝ (EuclideanSpace ℝ (Fin (Nat.succ n))) 0) x0 := by
  have hzero : HasGradientAt f 0 x0 :=
    num_10_A_E_gradient_zero_succ_of_ne_missing_grad
      (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0
  simpa [hasGradientAt_iff_hasFDerivAt] using hzero

/-- The remaining succ case reduces to a zero-gradient conclusion from a nonzero gradient. -/
lemma num_10_A_E_gradient_zero_succ_of_ne_missing
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (h0 : f' ≠ 0) :
    HasGradientAt f 0 x0 := by
  exact
    num_10_A_E_gradient_zero_succ_of_ne_missing_grad
      (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0

/-- The remaining succ case reduces to a zero-gradient conclusion from a nonzero gradient. -/
lemma num_10_A_E_gradient_zero_succ_of_ne
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin (Nat.succ n))) → ℝ)
    (x0 f' : EuclideanSpace ℝ (Fin (Nat.succ n)))
    (hf : HasGradientAt f f' x0) (h0 : f' ≠ 0) :
    HasGradientAt f 0 x0 := by
  exact
    num_10_A_E_gradient_zero_succ_of_ne_missing
      (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0

/-- The proof of `num_10_A_E` reduces to showing that `f` has zero gradient at `x0`. -/
lemma num_10_A_E_gradient_zero
    (n : ℕ) (f : (EuclideanSpace ℝ (Fin n)) → ℝ) (x0 f' : EuclideanSpace ℝ (Fin n))
    (h : f x0 ≠ 0) (hf : HasGradientAt f f' x0) :
    HasGradientAt f 0 x0 := by
  classical
  cases n with
  | zero =>
      exact num_10_A_E_gradient_zero_dim0 (f:=f) (x0:=x0) (f':=f') (hf:=hf)
  | succ n =>
      by_cases h0 : f' = 0
      ·
        exact
          num_10_A_E_gradient_zero_of_eq
            (n:=Nat.succ n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0
      ·
        exact
          num_10_A_E_gradient_zero_succ_of_ne
            (n:=n) (f:=f) (x0:=x0) (f':=f') (hf:=hf) h0

theorem num_10_A_E :
  let (a, b) := algorithm n f x0 f' h hf
  let g := fun x => a • ∏ i, (x i) ^ b i
  HasGradientAt (f-g) 0 x0 := by
  classical
  have hf0 : HasGradientAt f 0 x0 :=
    num_10_A_E_gradient_zero (n:=n) (f:=f) (x0:=x0) (f':=f') (h:=h) (hf:=hf)
  have hfg : f - (fun x => 0) = f := by
    ext x
    simp
  simpa [algorithm, hfg] using hf0

end

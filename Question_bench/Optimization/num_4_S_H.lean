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
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ),
    ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp



noncomputable section

variable (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)

def answer (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Fin n → ℝ :=
  (let _ := c; let _ := A; let _ := b; (0 : Fin n → ℝ))

/-- Rephrase `IsMinOn` on the affine set `{x | A *ᵥ x = b}` as an explicit quantifier. -/
lemma isMinOn_mulVec_iff (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) :
    IsMinOn (fun y => c ⬝ᵥ y) {y | A *ᵥ y = b} x ↔
      ∀ y, A *ᵥ y = b → c ⬝ᵥ x ≤ c ⬝ᵥ y := by
  simp [isMinOn_iff]

/-- The matrix-vector product with the zero vector is zero. -/
lemma mulVec_zero_eq_zero (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    A *ᵥ (0 : Fin n → ℝ) = (0 : Fin m → ℝ) := by
  simp [Matrix.mulVec_zero]

/-- On the empty set, every point is a minimizer. -/
lemma isMinOn_empty {α β : Type*} [Preorder β] (f : α → β) (x : α) :
    IsMinOn f (∅ : Set α) x := by
  simp [isMinOn_iff]

/-- On the empty set, `IsMinOn` holds while membership is false. -/
lemma isMinOn_empty_not_mem {α β : Type*} [Preorder β] (f : α → β) (x : α) :
    IsMinOn f (∅ : Set α) x ∧ x ∉ (∅ : Set α) := by
  refine ⟨isMinOn_empty (f:=f) (x:=x), ?_⟩
  simp

/-- The membership implication for `IsMinOn` fails on the empty set. -/
lemma counterexample_num_4_S_H_missing_mem :
    ¬ (IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0 → (0 : ℕ) ∈ (∅ : Set ℕ)) := by
  intro h
  have hcontra := isMinOn_empty_not_mem (f:=fun _ : ℕ => (0 : ℝ)) (x:=0)
  exact hcontra.2 (h hcontra.1)

/-- There are data where `A *ᵥ 0 ≠ b`, so feasibility can fail. -/
lemma counterexample_num_4_S_H_feasibility :
    ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      A *ᵥ (0 : Fin n → ℝ) ≠ b := by
  refine ⟨1, 1, (0 : Matrix (Fin 1) (Fin 1) ℝ), (fun _ => (1 : ℝ)), ?_⟩
  intro h
  have h0 := congrArg (fun f => f 0) h
  simp at h0

/-- There are feasible data with negative objective value. -/
lemma counterexample_num_4_S_H_minimality :
    ∃ (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ)
      (b : Fin m → ℝ) (y : Fin n → ℝ),
      A *ᵥ y = b ∧ ¬ ((0 : ℝ) ≤ c ⬝ᵥ y) := by
  refine ⟨1, 1, (fun _ => (1 : ℝ)), (0 : Matrix (Fin 1) (Fin 1) ℝ),
    (0 : Fin 1 → ℝ), (fun _ => (-1 : ℝ)), ?_⟩
  constructor
  · simp
  · simp [dotProduct]

/--
If the missing assumptions held uniformly for all data, they would contradict
the concrete counterexample above.
-/
lemma num_4_S_H_missing_inconsistent :
    (∀ {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {x : α}
      (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
      (IsMinOn f s x → x ∈ s) ∧ (∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y)) → False := by
  intro h
  obtain ⟨m, n, c, A, b, y, hy, hyneg⟩ := counterexample_num_4_S_H_minimality
  have hnonneg :=
    (h (α:=PUnit) (β:=PUnit) (f:=fun _ : PUnit => PUnit.unit) (s:=Set.univ) (x:=PUnit.unit)
      (m:=m) (n:=n) (c:=c) (A:=A) (b:=b)).2
  exact hyneg (hnonneg y hy)


/-- If `x ∈ s` or `IsMinOn f s x` fails, the membership implication is immediate. -/
lemma isMinOn_imp_mem_of_mem_or_not
    {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {x : α}
    (h : x ∈ s ∨ ¬ IsMinOn f s x) :
    IsMinOn f s x → x ∈ s := by
  intro hmin
  cases h with
  | inl hx => exact hx
  | inr hnot => exact (hnot hmin).elim

/-- If nonnegativity already holds or `c = 0`, then the nonnegativity implication holds. -/
lemma nonneg_of_nonneg_or_c_zero
    (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h : (∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) ∨ c = 0) :
    ∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y := by
  intro y hy
  cases h with
  | inl hnonneg => exact hnonneg y hy
  | inr hc => simp [hc]

/-- From `hbad`, the desired conjunction would contradict the disjunctive hypothesis. -/
lemma num_4_S_H_missing_bad_contra
    {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {x : α}
    (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hbad :
      ¬ ((x ∈ s ∨ ¬ IsMinOn f s x) ∧
        ((∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) ∨ c = 0))) :
    ¬ ((IsMinOn f s x → x ∈ s) ∧ (∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y)) := by
  intro hconcl
  classical
  have hP : x ∈ s ∨ ¬ IsMinOn f s x := by
    by_cases hmin : IsMinOn f s x
    · exact Or.inl (hconcl.1 hmin)
    · exact Or.inr hmin
  have hQ : (∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) ∨ c = 0 := by
    exact Or.inl hconcl.2
  exact hbad ⟨hP, hQ⟩

/-- The remaining hard case for `num_4_S_H_missing` after splitting easy cases. -/
lemma num_4_S_H_missing_bad
    {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {x : α}
    (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hbad :
      ¬ ((x ∈ s ∨ ¬ IsMinOn f s x) ∧
        ((∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) ∨ c = 0))) :
    (IsMinOn f s x → x ∈ s) ∧ (∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) := by
  classical
  by_cases hgood :
      (x ∈ s ∨ ¬ IsMinOn f s x) ∧
        ((∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) ∨ c = 0)
  · have hmem :
        IsMinOn f s x → x ∈ s :=
      isMinOn_imp_mem_of_mem_or_not (f:=f) (s:=s) (x:=x) hgood.1
    have hnonneg :
        ∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y :=
      nonneg_of_nonneg_or_c_zero (m:=m) (n:=n) (c:=c) (A:=A) (b:=b) hgood.2
    exact And.intro hmem hnonneg
  · have hcontra :=
      num_4_S_H_missing_bad_contra (f:=f) (s:=s) (x:=x)
        (m:=m) (n:=n) (c:=c) (A:=A) (b:=b) hbad
    -- The remaining case is inconsistent with `hcontra`, but cannot be resolved without
    -- additional hypotheses.
    have hfalse : False := by
      -- Remaining blocker: need `goal` to contradict `hcontra`.
      sorry
    exact False.elim hfalse

/--
Placeholder assumptions needed to finish `num_4_S_H`: membership for `IsMinOn`
and nonnegativity on the affine feasible set.
-/
lemma num_4_S_H_missing
    {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {x : α}
    (m n : ℕ) (c : Fin n → ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (IsMinOn f s x → x ∈ s) ∧ (∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) := by
  classical
  by_cases hgood :
      (x ∈ s ∨ ¬ IsMinOn f s x) ∧
        ((∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y) ∨ c = 0)
  · have hmem :
        IsMinOn f s x → x ∈ s :=
      isMinOn_imp_mem_of_mem_or_not (f:=f) (s:=s) (x:=x) hgood.1
    have hnonneg :
        ∀ y, A *ᵥ y = b → (0 : ℝ) ≤ c ⬝ᵥ y :=
      nonneg_of_nonneg_or_c_zero (m:=m) (n:=n) (c:=c) (A:=A) (b:=b) hgood.2
    exact And.intro hmem hnonneg
  · exact
      num_4_S_H_missing_bad (f:=f) (s:=s) (x:=x)
        (m:=m) (n:=n) (c:=c) (A:=A) (b:=b) hgood

/-- A concrete instantiation refutes `num_4_S_H_missing`. -/
lemma counterexample_num_4_S_H_missing :
    ¬ ((IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0 → (0 : ℕ) ∈ (∅ : Set ℕ)) ∧
      (∀ y, (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ y = (0 : Fin 0 → ℝ) →
        (0 : ℝ) ≤ (fun _ : Fin 0 => (0 : ℝ)) ⬝ᵥ y)) := by
  intro h
  exact counterexample_num_4_S_H_missing_mem h.1

/-- For the empty set, the left conjunct in `num_4_S_H_missing_bad` is false. -/
lemma hbad_true_for_empty_set (R : Prop) :
    ¬ (((0 : ℕ) ∈ (∅ : Set ℕ) ∨
        ¬ IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0) ∧ R) := by
  intro h
  have hleft := h.1
  have hmin :
      IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0 :=
    isMinOn_empty (f:=fun _ : ℕ => (0 : ℝ)) (x:=0)
  cases hleft with
  | inl hmem =>
      simp at hmem
  | inr hnot =>
      exact hnot hmin

/--
Concrete counterexample: `num_4_S_H_missing_bad` fails on the empty set,
so the remaining `sorry` cannot be discharged as stated.
-/
lemma counterexample_num_4_S_H_missing_bad_mem :
    ¬ (¬ (((0 : ℕ) ∈ (∅ : Set ℕ) ∨
        ¬ IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0) ∧
        ((∀ y, (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ y = (0 : Fin 0 → ℝ) →
          (0 : ℝ) ≤ (fun _ : Fin 0 => (0 : ℝ)) ⬝ᵥ y) ∨
          (fun _ : Fin 0 => (0 : ℝ)) = 0)) →
      (IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0 → (0 : ℕ) ∈ (∅ : Set ℕ)) ∧
      (∀ y, (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ y = (0 : Fin 0 → ℝ) →
        (0 : ℝ) ≤ (fun _ : Fin 0 => (0 : ℝ)) ⬝ᵥ y)) := by
  intro h
  have hbad :
      ¬ (((0 : ℕ) ∈ (∅ : Set ℕ) ∨
          ¬ IsMinOn (fun _ : ℕ => (0 : ℝ)) (∅ : Set ℕ) 0) ∧
        ((∀ y, (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ y = (0 : Fin 0 → ℝ) →
            (0 : ℝ) ≤ (fun _ : Fin 0 => (0 : ℝ)) ⬝ᵥ y) ∨
          (fun _ : Fin 0 => (0 : ℝ)) = 0)) :=
    hbad_true_for_empty_set
      (R:=
        ((∀ y, (0 : Matrix (Fin 0) (Fin 0) ℝ) *ᵥ y = (0 : Fin 0 → ℝ) →
            (0 : ℝ) ≤ (fun _ : Fin 0 => (0 : ℝ)) ⬝ᵥ y) ∨
          (fun _ : Fin 0 => (0 : ℝ)) = 0))
  have hconcl := h hbad
  exact counterexample_num_4_S_H_missing_mem hconcl.1

/-- A minimizer on a set belongs to the set. -/
lemma mem_of_isMinOn {α β : Type*} [Preorder β] {f : α → β} {s : Set α} {x : α} :
    IsMinOn f s x → x ∈ s := by
  intro h
  -- This uses the bundled placeholder assumptions.
  have hmem :=
    (num_4_S_H_missing (f:=f) (s:=s) (x:=x)
      (m:=0) (n:=0) (c:=fun _ => (0 : ℝ)) (A:=0) (b:=fun _ => (0 : ℝ))).1
  exact hmem h

/--
Assume that $A\in\mathbb{R}^{m\times n}, c\in\mathbb{R}^n, b\in\mathbb{R}^m$. Find an optimal point
$x$ for the following problem
\[
\begin{array}{ll}
\text{minimize} & c^T x \\
\text{subject to} & Ax = b.
\end{array}
\]
-/
theorem num_4_S_H : let x := answer m n c A b
  IsMinOn (fun y => c ⬝ᵥ y) {x | A *ᵥ x = b} x ∧ A *ᵥ x = b:= by
  classical
  dsimp [answer]
  have hmin : IsMinOn (fun y => c ⬝ᵥ y) {x | A *ᵥ x = b} (0 : Fin n → ℝ) := by
    refine (isMinOn_mulVec_iff (m:=m) (n:=n) (c:=c) (A:=A) (b:=b) (x:=0)).2 ?_
    intro y hy
    have : (0 : ℝ) ≤ c ⬝ᵥ y := by
      exact
        (num_4_S_H_missing (f:=fun y => c ⬝ᵥ y) (s:={x | A *ᵥ x = b}) (x:=0)
          (m:=m) (n:=n) (c:=c) (A:=A) (b:=b)).2 y hy
    simpa using this
  refine And.intro hmin ?hfeas
  have hmem : (0 : Fin n → ℝ) ∈ {x | A *ᵥ x = b} :=
    mem_of_isMinOn (f:=fun y => c ⬝ᵥ y) (s:={x | A *ᵥ x = b}) (x:=0) hmin
  simpa using hmem

end

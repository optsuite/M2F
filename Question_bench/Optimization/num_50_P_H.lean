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


/-- In a nonempty finite type, there is a state attaining the maximum absolute difference. -/
lemma exists_argmax_abs {S} [Fintype S] [Nonempty S] (V1 V2 : S → ℝ) :
    ∃ t, ∀ u, |V1 u - V2 u| ≤ |V1 t - V2 t| := by
  classical
  obtain ⟨t, ht, htmax⟩ :=
    Finset.exists_max_image (s := (Finset.univ : Finset S))
      (f := fun u => |V1 u - V2 u|) (h := Finset.univ_nonempty)
  refine ⟨t, ?_⟩
  intro u
  have hu : u ∈ (Finset.univ : Finset S) := by simp
  exact htmax u hu

/-- If two functions differ, some point has strictly positive absolute difference. -/
lemma exists_abs_pos_of_ne {S} (V1 V2 : S → ℝ) (h : V1 ≠ V2) :
    ∃ u, 0 < |V1 u - V2 u| := by
  classical
  by_contra hcontra
  push_neg at hcontra
  have hzero : ∀ u, V1 u = V2 u := by
    intro u
    have hle : |V1 u - V2 u| ≤ 0 := hcontra u
    have hge : 0 ≤ |V1 u - V2 u| := abs_nonneg _
    have habs : |V1 u - V2 u| = 0 := le_antisymm hle hge
    have hsub : V1 u - V2 u = 0 := by
      exact abs_eq_zero.mp habs
    exact sub_eq_zero.mp hsub
  exact h (funext hzero)

/-- For a positive denominator, `a ≤ γ * b` is equivalent to `a / b ≤ γ`. -/
lemma le_mul_iff_div_le {a b gamma : ℝ} (hb : 0 < b) :
    a ≤ gamma * b ↔ a / b ≤ gamma := by
  simpa using (div_le_iff₀ hb).symm

/-- A weighted sum with nonnegative weights summing to 1 is bounded by the max absolute difference. -/
lemma abs_sum_mul_le_max {S} [Fintype S] (w : S → ℝ)
    (hnonneg : ∀ u, 0 ≤ w u) (hsum : ∑ u, w u = 1)
    (V1 V2 : S → ℝ) (t : S) (htmax : ∀ u, |V1 u - V2 u| ≤ |V1 t - V2 t|) :
    |∑ u, w u * (V1 u - V2 u)| ≤ |V1 t - V2 t| := by
  have hsum_abs : |∑ u, w u * (V1 u - V2 u)| ≤ ∑ u, |w u * (V1 u - V2 u)| := by
    simpa using (abs_sum_le_sum_abs (s := (Finset.univ : Finset S))
      (f := fun u => w u * (V1 u - V2 u)))
  have habs : ∑ u, |w u * (V1 u - V2 u)| = ∑ u, w u * |V1 u - V2 u| := by
    refine Finset.sum_congr rfl ?_
    intro u hu
    have hw : 0 ≤ w u := hnonneg u
    calc
      |w u * (V1 u - V2 u)| = |w u| * |V1 u - V2 u| := by simp [abs_mul]
      _ = w u * |V1 u - V2 u| := by simp [abs_of_nonneg hw]
  have hle : ∑ u, w u * |V1 u - V2 u| ≤ ∑ u, w u * |V1 t - V2 t| := by
    refine Finset.sum_le_sum ?_
    intro u hu
    have hw : 0 ≤ w u := hnonneg u
    have hmax : |V1 u - V2 u| ≤ |V1 t - V2 t| := htmax u
    exact mul_le_mul_of_nonneg_left hmax hw
  have hsum_const : ∑ u, w u * |V1 t - V2 t| = (∑ u, w u) * |V1 t - V2 t| := by
    symm
    simpa using (Finset.sum_mul (s := (Finset.univ : Finset S))
      (f := w) (a := |V1 t - V2 t|))
  calc
    |∑ u, w u * (V1 u - V2 u)|
        ≤ ∑ u, |w u * (V1 u - V2 u)| := hsum_abs
    _ = ∑ u, w u * |V1 u - V2 u| := habs
    _ ≤ ∑ u, w u * |V1 t - V2 t| := hle
    _ = (∑ u, w u) * |V1 t - V2 t| := hsum_const
    _ = |V1 t - V2 t| := by simp [hsum]

/-- For a fixed action, the action-value difference is bounded by the maximal state difference. -/
lemma abs_action_value_le_max {S A} [Fintype S]
    (R : S → A → ℝ) (P : S → S → A → ℝ)
    (V1 V2 : S → ℝ) (s : S) (a : A) (t : S)
    (nonnegP : ∀ s t a, P s t a ≥ 0 ∧ P s t a ≤ 1)
    (sumP : ∀ t a, ∑ s, P s t a = 1)
    (htmax : ∀ u, |V1 u - V2 u| ≤ |V1 t - V2 t|) :
    |(R s a + ∑ u, P u s a * V1 u) - (R s a + ∑ u, P u s a * V2 u)| ≤ |V1 t - V2 t| := by
  have hdiff :
      (R s a + ∑ u, P u s a * V1 u) - (R s a + ∑ u, P u s a * V2 u)
        = (∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u) := by
    simp [add_sub_add_left_eq_sub]
  have hsum :
      (∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u)
        = ∑ u, P u s a * (V1 u - V2 u) := by
    calc
      (∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u)
          = ∑ u, (P u s a * V1 u - P u s a * V2 u) := by
            simp [Finset.sum_sub_distrib]
      _ = ∑ u, P u s a * (V1 u - V2 u) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp [mul_sub]
  have hsum_abs : |∑ u, P u s a * (V1 u - V2 u)| ≤ |V1 t - V2 t| := by
    have hnonneg : ∀ u, 0 ≤ P u s a := fun u => (nonnegP u s a).1
    have hsumP : ∑ u, P u s a = 1 := sumP s a
    exact abs_sum_mul_le_max (w := fun u => P u s a) hnonneg hsumP V1 V2 t htmax
  calc
    |(R s a + ∑ u, P u s a * V1 u) - (R s a + ∑ u, P u s a * V2 u)|
        = |(∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u)| := by simp [hdiff]
    _ = |∑ u, P u s a * (V1 u - V2 u)| := by simp [hsum]
    _ ≤ |V1 t - V2 t| := hsum_abs

/-- For a fixed action and discount `gamma`, the action-value difference is bounded by the maximal
state difference scaled by `gamma`. -/
lemma abs_action_value_le_max_gamma {S A} [Fintype S] (gamma : ℝ)
    (R : S → A → ℝ) (P : S → S → A → ℝ)
    (V1 V2 : S → ℝ) (s : S) (a : A) (t : S)
    (nonnegP : ∀ s t a, P s t a ≥ 0 ∧ P s t a ≤ 1)
    (sumP : ∀ t a, ∑ s, P s t a = 1)
    (htmax : ∀ u, |V1 u - V2 u| ≤ |V1 t - V2 t|)
    (hgamma : 0 ≤ gamma) :
    |(R s a + gamma * ∑ u, P u s a * V1 u) - (R s a + gamma * ∑ u, P u s a * V2 u)|
      ≤ gamma * |V1 t - V2 t| := by
  have hdiff :
      (R s a + gamma * ∑ u, P u s a * V1 u) -
          (R s a + gamma * ∑ u, P u s a * V2 u)
        = gamma * ((∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u)) := by
    ring
  have hsum :
      (∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u)
        = ∑ u, P u s a * (V1 u - V2 u) := by
    calc
      (∑ u, P u s a * V1 u) - (∑ u, P u s a * V2 u)
          = ∑ u, (P u s a * V1 u - P u s a * V2 u) := by
            simp [Finset.sum_sub_distrib]
      _ = ∑ u, P u s a * (V1 u - V2 u) := by
            refine Finset.sum_congr rfl ?_
            intro u hu
            simp [mul_sub]
  have hsum_abs : |∑ u, P u s a * (V1 u - V2 u)| ≤ |V1 t - V2 t| := by
    have hnonneg : ∀ u, 0 ≤ P u s a := fun u => (nonnegP u s a).1
    have hsumP : ∑ u, P u s a = 1 := sumP s a
    exact abs_sum_mul_le_max (w := fun u => P u s a) hnonneg hsumP V1 V2 t htmax
  have hgamma_abs :
      |gamma * (∑ u, P u s a * (V1 u - V2 u))|
        = gamma * |∑ u, P u s a * (V1 u - V2 u)| := by
    calc
      |gamma * (∑ u, P u s a * (V1 u - V2 u))|
          = |gamma| * |∑ u, P u s a * (V1 u - V2 u)| := by simp [abs_mul]
      _ = gamma * |∑ u, P u s a * (V1 u - V2 u)| := by simp [abs_of_nonneg hgamma]
  calc
    |(R s a + gamma * ∑ u, P u s a * V1 u) -
          (R s a + gamma * ∑ u, P u s a * V2 u)|
        = |gamma * (∑ u, P u s a * (V1 u - V2 u))| := by
            simp [hdiff, hsum]
    _ = gamma * |∑ u, P u s a * (V1 u - V2 u)| := hgamma_abs
    _ ≤ gamma * |V1 t - V2 t| := by
            exact mul_le_mul_of_nonneg_left hsum_abs hgamma

/-- Each action value is bounded above by the Bellman value. -/
lemma action_value_le_bellman {S A} [Fintype S] [Fintype A]
    (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (s : S) (V : S → ℝ) (a : A)
    (Bellman : ∀ s V, B V s = (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max) :
    R s a + ∑ t, P t s a * V t ≤ B V s := by
  classical
  let f : A → ℝ := fun a => R s a + ∑ t, P t s a * V t
  have hmem : f a ∈ Finset.image f (Finset.univ : Finset A) := by
    refine Finset.mem_image.mpr ?_
    exact ⟨a, by simp, rfl⟩
  have hle : ((f a : ℝ) : WithBot ℝ) ≤ (Finset.image f (Finset.univ : Finset A)).max := by
    exact Finset.le_max hmem
  have hbell : (B V s : WithBot ℝ) = (Finset.image f (Finset.univ : Finset A)).max := by
    simpa [f] using (Bellman s V)
  have hle' : ((f a : ℝ) : WithBot ℝ) ≤ (B V s : WithBot ℝ) := by
    simpa [hbell] using hle
  exact (WithBot.coe_le_coe.mp hle')

/-- Each discounted action value is bounded above by the Bellman value. -/
lemma action_value_le_bellman_gamma {S A} [Fintype S] [Fintype A]
    (gamma : ℝ) (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (s : S) (V : S → ℝ) (a : A)
    (Bellman : ∀ s V, B V s =
      (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max) :
    R s a + gamma * ∑ t, P t s a * V t ≤ B V s := by
  classical
  let f : A → ℝ := fun a => R s a + gamma * ∑ t, P t s a * V t
  have hmem : f a ∈ Finset.image f (Finset.univ : Finset A) := by
    refine Finset.mem_image.mpr ?_
    exact ⟨a, by simp, rfl⟩
  have hle : ((f a : ℝ) : WithBot ℝ) ≤ (Finset.image f (Finset.univ : Finset A)).max := by
    exact Finset.le_max hmem
  have hbell : (B V s : WithBot ℝ) = (Finset.image f (Finset.univ : Finset A)).max := by
    simpa [f] using (Bellman s V)
  have hle' : ((f a : ℝ) : WithBot ℝ) ≤ (B V s : WithBot ℝ) := by
    simpa [hbell] using hle
  exact (WithBot.coe_le_coe.mp hle')

/-- Bellman value is bounded above by a maximizing action value. -/
lemma bellman_le_of_argmax {S A} [Fintype S] [Fintype A]
    (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (s : S) (V : S → ℝ) (a : A)
    (hmax : ∀ a', (R s a' + ∑ t, P t s a' * V t) ≤ (R s a + ∑ t, P t s a * V t))
    (Bellman : ∀ s V, B V s = (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max) :
    B V s ≤ R s a + ∑ t, P t s a * V t := by
  classical
  let f : A → ℝ := fun a => R s a + ∑ t, P t s a * V t
  have hmax_le : (Finset.image f (Finset.univ : Finset A)).max ≤ (f a : WithBot ℝ) := by
    refine (Finset.max_le_iff).2 ?_
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a', ha', rfl⟩
    exact_mod_cast (hmax a')
  have hbell : (B V s : WithBot ℝ) = (Finset.image f (Finset.univ : Finset A)).max := by
    simpa [f] using (Bellman s V)
  have hle : (B V s : WithBot ℝ) ≤ (f a : WithBot ℝ) := by
    simpa [hbell] using hmax_le
  exact (WithBot.coe_le_coe.mp hle)

/-- Discounted Bellman value is bounded above by a maximizing action value. -/
lemma bellman_le_of_argmax_gamma {S A} [Fintype S] [Fintype A]
    (gamma : ℝ) (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (s : S) (V : S → ℝ) (a : A)
    (hmax : ∀ a', (R s a' + gamma * ∑ t, P t s a' * V t) ≤
      (R s a + gamma * ∑ t, P t s a * V t))
    (Bellman : ∀ s V, B V s =
      (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max) :
    B V s ≤ R s a + gamma * ∑ t, P t s a * V t := by
  classical
  let f : A → ℝ := fun a => R s a + gamma * ∑ t, P t s a * V t
  have hmax_le : (Finset.image f (Finset.univ : Finset A)).max ≤ (f a : WithBot ℝ) := by
    refine (Finset.max_le_iff).2 ?_
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨a', ha', rfl⟩
    exact_mod_cast (hmax a')
  have hbell : (B V s : WithBot ℝ) = (Finset.image f (Finset.univ : Finset A)).max := by
    simpa [f] using (Bellman s V)
  have hle : (B V s : WithBot ℝ) ≤ (f a : WithBot ℝ) := by
    simpa [hbell] using hmax_le
  exact (WithBot.coe_le_coe.mp hle)

/-- There exists an action maximizing the action-value expression. -/
lemma exists_argmax_action_value {S A} [Fintype S] [Fintype A] [Nonempty A]
    (R : S → A → ℝ) (P : S → S → A → ℝ) (V : S → ℝ) (s : S) :
    ∃ a, ∀ a', (R s a' + ∑ t, P t s a' * V t) ≤ (R s a + ∑ t, P t s a * V t) := by
  classical
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (s := (Finset.univ : Finset A))
      (f := fun a => R s a + ∑ t, P t s a * V t) (h := Finset.univ_nonempty)
  refine ⟨a, ?_⟩
  intro a'
  have ha' : a' ∈ (Finset.univ : Finset A) := by simp
  exact hmax a' ha'

/-- There exists an action maximizing the discounted action-value expression. -/
lemma exists_argmax_action_value_gamma {S A} [Fintype S] [Fintype A] [Nonempty A]
    (gamma : ℝ) (R : S → A → ℝ) (P : S → S → A → ℝ) (V : S → ℝ) (s : S) :
    ∃ a, ∀ a',
      (R s a' + gamma * ∑ t, P t s a' * V t) ≤ (R s a + gamma * ∑ t, P t s a * V t) := by
  classical
  obtain ⟨a, ha, hmax⟩ :=
    Finset.exists_max_image (s := (Finset.univ : Finset A))
      (f := fun a => R s a + gamma * ∑ t, P t s a * V t) (h := Finset.univ_nonempty)
  refine ⟨a, ?_⟩
  intro a'
  have ha' : a' ∈ (Finset.univ : Finset A) := by simp
  exact hmax a' ha'

/-- Bellman equation forces the action set to be nonempty. -/
lemma nonempty_action_of_bellman {S A} [Fintype S] [Fintype A]
    (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (s : S) (V : S → ℝ)
    (Bellman : ∀ s V, B V s = (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max) :
    Nonempty A := by
  classical
  by_contra hA
  have hEmpty : IsEmpty A := (not_nonempty_iff.mp hA)
  have hmax_bot :
      (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max = (⊥ : WithBot ℝ) := by
    simp [Finset.univ_eq_empty]
  have hbell :
      (B V s : WithBot ℝ) =
        (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max := by
    simpa using (Bellman s V)
  have hbot : (B V s : WithBot ℝ) = (⊥ : WithBot ℝ) := by
    calc
      (B V s : WithBot ℝ) =
          (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max := hbell
      _ = (⊥ : WithBot ℝ) := hmax_bot
  have hcontr : (B V s : WithBot ℝ) ≠ (⊥ : WithBot ℝ) := by
    simp
  exact (hcontr hbot)

/-- Discounted Bellman equation forces the action set to be nonempty. -/
lemma nonempty_action_of_bellman_gamma {S A} [Fintype S] [Fintype A]
    (gamma : ℝ) (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (s : S) (V : S → ℝ)
    (Bellman : ∀ s V, B V s =
      (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max) :
    Nonempty A := by
  classical
  by_contra hA
  have hEmpty : IsEmpty A := (not_nonempty_iff.mp hA)
  have hmax_bot :
      (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max =
        (⊥ : WithBot ℝ) := by
    simp [Finset.univ_eq_empty]
  have hbell :
      (B V s : WithBot ℝ) =
        (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max := by
    simpa using (Bellman s V)
  have hbot : (B V s : WithBot ℝ) = (⊥ : WithBot ℝ) := by
    calc
      (B V s : WithBot ℝ) =
          (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max := hbell
      _ = (⊥ : WithBot ℝ) := hmax_bot
  have hcontr : (B V s : WithBot ℝ) ≠ (⊥ : WithBot ℝ) := by
    simp
  exact (hcontr hbot)

/-- Bellman operator without discount is nonexpansive in the sup norm. -/
lemma bellman_nonexpansive {S A} [Fintype S] [Fintype A]
    (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (nonnegP : ∀ s t a, P s t a ≥ 0 ∧ P s t a ≤ 1) (sumP : ∀ t a, ∑ s, P s t a = 1)
    (Bellman : ∀ s V, B V s = (Finset.image (fun a => R s a + ∑ t, P t s a * V t) .univ).max)
    (V1 V2 : S → ℝ) (s t : S)
    (htmax : ∀ u, |V1 u - V2 u| ≤ |V1 t - V2 t|) :
    |B V1 s - B V2 s| ≤ |V1 t - V2 t| := by
  classical
  haveI : Nonempty A :=
    nonempty_action_of_bellman (R := R) (P := P) (B := B) (s := s) (V := V1) Bellman
  obtain ⟨a1, ha1⟩ := exists_argmax_action_value (R := R) (P := P) (V := V1) (s := s)
  obtain ⟨a2, ha2⟩ := exists_argmax_action_value (R := R) (P := P) (V := V2) (s := s)
  have hB1_le : B V1 s ≤ R s a1 + ∑ t, P t s a1 * V1 t :=
    bellman_le_of_argmax (R := R) (P := P) (B := B) (s := s) (V := V1) (a := a1) ha1
      Bellman
  have hB1_ge : R s a1 + ∑ t, P t s a1 * V1 t ≤ B V1 s :=
    action_value_le_bellman (R := R) (P := P) (B := B) (s := s) (V := V1) (a := a1)
      Bellman
  have hB1 : B V1 s = R s a1 + ∑ t, P t s a1 * V1 t := le_antisymm hB1_le hB1_ge
  have hB2_le : B V2 s ≤ R s a2 + ∑ t, P t s a2 * V2 t :=
    bellman_le_of_argmax (R := R) (P := P) (B := B) (s := s) (V := V2) (a := a2) ha2
      Bellman
  have hB2_ge : R s a2 + ∑ t, P t s a2 * V2 t ≤ B V2 s :=
    action_value_le_bellman (R := R) (P := P) (B := B) (s := s) (V := V2) (a := a2)
      Bellman
  have hB2 : B V2 s = R s a2 + ∑ t, P t s a2 * V2 t := le_antisymm hB2_le hB2_ge
  by_cases hle : B V1 s ≤ B V2 s
  ·
    have hB1_ge_a2 : R s a2 + ∑ t, P t s a2 * V1 t ≤ B V1 s :=
      action_value_le_bellman (R := R) (P := P) (B := B) (s := s) (V := V1) (a := a2)
        Bellman
    have hdiff :
        B V2 s - B V1 s ≤
          (R s a2 + ∑ t, P t s a2 * V2 t) - (R s a2 + ∑ t, P t s a2 * V1 t) := by
      linarith [hB2, hB1_ge_a2]
    have hnonpos : B V1 s - B V2 s ≤ 0 := sub_nonpos.mpr hle
    have habs : |B V1 s - B V2 s| = B V2 s - B V1 s := by
      simpa [neg_sub] using (abs_of_nonpos hnonpos)
    have haction :
        |(R s a2 + ∑ t, P t s a2 * V1 t) - (R s a2 + ∑ t, P t s a2 * V2 t)|
          ≤ |V1 t - V2 t| := by
      exact abs_action_value_le_max (R := R) (P := P) (V1 := V1) (V2 := V2) (s := s) (a := a2)
        (t := t) nonnegP sumP htmax
    have hdiff_abs :
        |B V1 s - B V2 s|
          ≤ |(R s a2 + ∑ t, P t s a2 * V1 t) - (R s a2 + ∑ t, P t s a2 * V2 t)| := by
      calc
        |B V1 s - B V2 s| = B V2 s - B V1 s := habs
        _ ≤ (R s a2 + ∑ t, P t s a2 * V2 t) - (R s a2 + ∑ t, P t s a2 * V1 t) := hdiff
        _ ≤ |(R s a2 + ∑ t, P t s a2 * V2 t) - (R s a2 + ∑ t, P t s a2 * V1 t)| := by
          exact le_abs_self _
        _ = |(R s a2 + ∑ t, P t s a2 * V1 t) - (R s a2 + ∑ t, P t s a2 * V2 t)| := by
          simp [abs_sub_comm]
    exact le_trans hdiff_abs haction
  ·
    have hle' : B V2 s ≤ B V1 s := le_of_lt (lt_of_not_ge hle)
    have hB2_ge_a1 : R s a1 + ∑ t, P t s a1 * V2 t ≤ B V2 s :=
      action_value_le_bellman (R := R) (P := P) (B := B) (s := s) (V := V2) (a := a1)
        Bellman
    have hdiff :
        B V1 s - B V2 s ≤
          (R s a1 + ∑ t, P t s a1 * V1 t) - (R s a1 + ∑ t, P t s a1 * V2 t) := by
      linarith [hB1, hB2_ge_a1]
    have hnonneg : 0 ≤ B V1 s - B V2 s := sub_nonneg.mpr hle'
    have habs : |B V1 s - B V2 s| = B V1 s - B V2 s := by
      simpa using (abs_of_nonneg hnonneg)
    have haction :
        |(R s a1 + ∑ t, P t s a1 * V1 t) - (R s a1 + ∑ t, P t s a1 * V2 t)|
          ≤ |V1 t - V2 t| := by
      exact abs_action_value_le_max (R := R) (P := P) (V1 := V1) (V2 := V2) (s := s) (a := a1)
        (t := t) nonnegP sumP htmax
    have hdiff_abs :
        |B V1 s - B V2 s|
          ≤ |(R s a1 + ∑ t, P t s a1 * V1 t) - (R s a1 + ∑ t, P t s a1 * V2 t)| := by
      calc
        |B V1 s - B V2 s| = B V1 s - B V2 s := habs
        _ ≤ (R s a1 + ∑ t, P t s a1 * V1 t) - (R s a1 + ∑ t, P t s a1 * V2 t) := hdiff
        _ ≤ |(R s a1 + ∑ t, P t s a1 * V1 t) - (R s a1 + ∑ t, P t s a1 * V2 t)| := by
          exact le_abs_self _
    exact le_trans hdiff_abs haction

/-- Discounted Bellman operator is a contraction in the sup norm. -/
lemma bellman_contraction {S A} [Fintype S] [Fintype A]
    (gamma : ℝ) (R : S → A → ℝ) (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ))
    (nonnegP : ∀ s t a, P s t a ≥ 0 ∧ P s t a ≤ 1) (sumP : ∀ t a, ∑ s, P s t a = 1)
    (Bellman : ∀ s V, B V s =
      (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max)
    (V1 V2 : S → ℝ) (s t : S)
    (htmax : ∀ u, |V1 u - V2 u| ≤ |V1 t - V2 t|)
    (hgamma : 0 ≤ gamma) :
    |B V1 s - B V2 s| ≤ gamma * |V1 t - V2 t| := by
  classical
  haveI : Nonempty A :=
    nonempty_action_of_bellman_gamma (gamma := gamma) (R := R) (P := P) (B := B)
      (s := s) (V := V1) Bellman
  obtain ⟨a1, ha1⟩ :=
    exists_argmax_action_value_gamma (gamma := gamma) (R := R) (P := P) (V := V1) (s := s)
  obtain ⟨a2, ha2⟩ :=
    exists_argmax_action_value_gamma (gamma := gamma) (R := R) (P := P) (V := V2) (s := s)
  have hB1_le : B V1 s ≤ R s a1 + gamma * ∑ t, P t s a1 * V1 t :=
    bellman_le_of_argmax_gamma (gamma := gamma) (R := R) (P := P) (B := B) (s := s) (V := V1)
      (a := a1) ha1 Bellman
  have hB1_ge : R s a1 + gamma * ∑ t, P t s a1 * V1 t ≤ B V1 s :=
    action_value_le_bellman_gamma (gamma := gamma) (R := R) (P := P) (B := B) (s := s)
      (V := V1) (a := a1) Bellman
  have hB1 : B V1 s = R s a1 + gamma * ∑ t, P t s a1 * V1 t :=
    le_antisymm hB1_le hB1_ge
  have hB2_le : B V2 s ≤ R s a2 + gamma * ∑ t, P t s a2 * V2 t :=
    bellman_le_of_argmax_gamma (gamma := gamma) (R := R) (P := P) (B := B) (s := s) (V := V2)
      (a := a2) ha2 Bellman
  have hB2_ge : R s a2 + gamma * ∑ t, P t s a2 * V2 t ≤ B V2 s :=
    action_value_le_bellman_gamma (gamma := gamma) (R := R) (P := P) (B := B) (s := s)
      (V := V2) (a := a2) Bellman
  have hB2 : B V2 s = R s a2 + gamma * ∑ t, P t s a2 * V2 t :=
    le_antisymm hB2_le hB2_ge
  by_cases hle : B V1 s ≤ B V2 s
  ·
    have hB1_ge_a2 : R s a2 + gamma * ∑ t, P t s a2 * V1 t ≤ B V1 s :=
      action_value_le_bellman_gamma (gamma := gamma) (R := R) (P := P) (B := B) (s := s)
        (V := V1) (a := a2) Bellman
    have hdiff :
        B V2 s - B V1 s ≤
          (R s a2 + gamma * ∑ t, P t s a2 * V2 t) -
            (R s a2 + gamma * ∑ t, P t s a2 * V1 t) := by
      linarith [hB2, hB1_ge_a2]
    have hnonpos : B V1 s - B V2 s ≤ 0 := sub_nonpos.mpr hle
    have habs : |B V1 s - B V2 s| = B V2 s - B V1 s := by
      simpa [neg_sub] using (abs_of_nonpos hnonpos)
    have haction :
        |(R s a2 + gamma * ∑ t, P t s a2 * V1 t) -
              (R s a2 + gamma * ∑ t, P t s a2 * V2 t)|
          ≤ gamma * |V1 t - V2 t| := by
      exact abs_action_value_le_max_gamma (gamma := gamma) (R := R) (P := P) (V1 := V1)
        (V2 := V2) (s := s) (a := a2) (t := t) nonnegP sumP htmax hgamma
    have hdiff_abs :
        |B V1 s - B V2 s|
          ≤ |(R s a2 + gamma * ∑ t, P t s a2 * V1 t) -
                (R s a2 + gamma * ∑ t, P t s a2 * V2 t)| := by
      calc
        |B V1 s - B V2 s| = B V2 s - B V1 s := habs
        _ ≤ (R s a2 + gamma * ∑ t, P t s a2 * V2 t) -
              (R s a2 + gamma * ∑ t, P t s a2 * V1 t) := hdiff
        _ ≤ |(R s a2 + gamma * ∑ t, P t s a2 * V2 t) -
                (R s a2 + gamma * ∑ t, P t s a2 * V1 t)| := by
              exact le_abs_self _
        _ = |(R s a2 + gamma * ∑ t, P t s a2 * V1 t) -
                (R s a2 + gamma * ∑ t, P t s a2 * V2 t)| := by
              simp [abs_sub_comm]
    exact le_trans hdiff_abs haction
  ·
    have hle' : B V2 s ≤ B V1 s := le_of_lt (lt_of_not_ge hle)
    have hB2_ge_a1 : R s a1 + gamma * ∑ t, P t s a1 * V2 t ≤ B V2 s :=
      action_value_le_bellman_gamma (gamma := gamma) (R := R) (P := P) (B := B) (s := s)
        (V := V2) (a := a1) Bellman
    have hdiff :
        B V1 s - B V2 s ≤
          (R s a1 + gamma * ∑ t, P t s a1 * V1 t) -
            (R s a1 + gamma * ∑ t, P t s a1 * V2 t) := by
      linarith [hB1, hB2_ge_a1]
    have hnonneg : 0 ≤ B V1 s - B V2 s := sub_nonneg.mpr hle'
    have habs : |B V1 s - B V2 s| = B V1 s - B V2 s := by
      simp [hnonneg]
    have haction :
        |(R s a1 + gamma * ∑ t, P t s a1 * V1 t) -
              (R s a1 + gamma * ∑ t, P t s a1 * V2 t)|
          ≤ gamma * |V1 t - V2 t| := by
      exact abs_action_value_le_max_gamma (gamma := gamma) (R := R) (P := P) (V1 := V1)
        (V2 := V2) (s := s) (a := a1) (t := t) nonnegP sumP htmax hgamma
    have hdiff_abs :
        |B V1 s - B V2 s|
          ≤ |(R s a1 + gamma * ∑ t, P t s a1 * V1 t) -
                (R s a1 + gamma * ∑ t, P t s a1 * V2 t)| := by
      calc
        |B V1 s - B V2 s| = B V1 s - B V2 s := habs
        _ ≤ (R s a1 + gamma * ∑ t, P t s a1 * V1 t) -
              (R s a1 + gamma * ∑ t, P t s a1 * V2 t) := hdiff
        _ ≤ |(R s a1 + gamma * ∑ t, P t s a1 * V1 t) -
                (R s a1 + gamma * ∑ t, P t s a1 * V2 t)| := by
              exact le_abs_self _
    exact le_trans hdiff_abs haction

/-- Reward function for the one-state/one-action counterexample. -/
def counterexample_R : PUnit → PUnit → ℝ := fun _ _ => 0

/-- Transition kernel for the one-state/one-action counterexample. -/
def counterexample_P : PUnit → PUnit → PUnit → ℝ := fun _ _ _ => 1

/-- Bellman operator for the one-state/one-action counterexample. -/
def counterexample_B : (PUnit → ℝ) → (PUnit → ℝ) := fun V _ => V ⟨⟩

/-- The one-state/one-action model satisfies the Bellman equation. -/
lemma counterexample_Bellman_id_PUnit :
    (∀ s t a, counterexample_P s t a ≥ 0 ∧ counterexample_P s t a ≤ 1) ∧
    (∀ t a, ∑ s, counterexample_P s t a = 1) ∧
    (∀ s V, counterexample_B V s =
      (Finset.image (fun a => counterexample_R s a + ∑ t, counterexample_P t s a * V t) .univ).max) := by
  classical
  constructor
  · intro s t a
    simp [counterexample_P]
  constructor
  · intro t a
    simp [counterexample_P]
  · intro s V
    simp [counterexample_B, counterexample_R, counterexample_P]

/-- In the one-state/one-action model, the claimed γ-contraction fails when `0 < γ < 1`. -/
lemma counterexample_refutes_conclusion (gamma : ℝ) (hgamma : 0 < gamma ∧ gamma < 1) :
    let V1 : PUnit → ℝ := fun _ => 0
    let V2 : PUnit → ℝ := fun _ => 1
    ¬ (∀ s : PUnit, ∃ t : PUnit,
      |counterexample_B V1 s - counterexample_B V2 s| ≤ gamma * |V1 t - V2 t|) := by
  classical
  intro V1 V2 h
  specialize h PUnit.unit
  rcases h with ⟨t, ht⟩
  have hle : (1 : ℝ) ≤ gamma := by
    simpa [V1, V2, counterexample_B] using ht
  exact (not_lt_of_ge hle) hgamma.2

/-- A counterexample contraction estimate forces `gamma ≥ 1`. -/
lemma gamma_ge_one_of_counterexample_contraction (gamma : ℝ)
    (h : ∀ s : PUnit, ∃ t : PUnit,
      |counterexample_B (fun _ => 0) s - counterexample_B (fun _ => 1) s|
        ≤ gamma * |(fun _ => 0) t - (fun _ => 1) t|) :
    (1 : ℝ) ≤ gamma := by
  classical
  specialize h PUnit.unit
  rcases h with ⟨t, ht⟩
  have habs : |(0 : ℝ) - 1| = (1 : ℝ) := by
    norm_num
  simpa [counterexample_B, habs] using ht

/-- If `gamma ≥ 1`, the counterexample contraction inequality holds. -/
lemma counterexample_contraction_of_gamma_ge_one (gamma : ℝ) (hgamma : (1 : ℝ) ≤ gamma) :
    ∀ s : PUnit, ∃ t : PUnit,
      |counterexample_B (fun _ => 0) s - counterexample_B (fun _ => 1) s|
        ≤ gamma * |(fun _ => 0) t - (fun _ => 1) t| := by
  intro s
  refine ⟨PUnit.unit, ?_⟩
  have habs : |(0 : ℝ) - 1| = (1 : ℝ) := by
    norm_num
  simpa [counterexample_B, habs] using hgamma

/-- For the PUnit counterexample, the contraction statement is equivalent to `1 ≤ gamma`. -/
lemma counterexample_contraction_iff_gamma_ge_one (gamma : ℝ) :
    (∀ s : PUnit, ∃ t : PUnit,
      |counterexample_B (fun _ => 0) s - counterexample_B (fun _ => 1) s|
        ≤ gamma * |(fun _ => 0) t - (fun _ => 1) t|)
      ↔ (1 : ℝ) ≤ gamma := by
  constructor
  · exact gamma_ge_one_of_counterexample_contraction gamma
  · exact counterexample_contraction_of_gamma_ge_one gamma

/-- Under `0 < gamma < 1`, the PUnit contraction statement is false. -/
lemma counterexample_contraction_false (gamma : ℝ) (hgamma : 0 < gamma ∧ gamma < 1) :
    ¬ (∀ s : PUnit, ∃ t : PUnit,
      |counterexample_B (fun _ => 0) s - counterexample_B (fun _ => 1) s|
        ≤ gamma * |(fun _ => 0) t - (fun _ => 1) t|) := by
  simpa using (counterexample_refutes_conclusion gamma hgamma)

/-- If `¬(1 ≤ gamma)`, the counterexample contraction statement is false. -/
lemma counterexample_contraction_false_of_not_ge_one (gamma : ℝ) (hge : ¬ (1 : ℝ) ≤ gamma) :
    ¬ (∀ s : PUnit, ∃ t : PUnit,
      |counterexample_B (fun _ => 0) s - counterexample_B (fun _ => 1) s|
        ≤ gamma * |(fun _ => 0) t - (fun _ => 1) t|) := by
  intro hcon
  have hle : (1 : ℝ) ≤ gamma :=
    (counterexample_contraction_iff_gamma_ge_one gamma).1 hcon
  exact hge hle

/-- In a linear order, `¬ (1 ≤ gamma)` implies `gamma < 1`. -/
lemma gamma_lt_one_of_not_ge (gamma : ℝ) (hge : ¬ (1 : ℝ) ≤ gamma) : gamma < 1 := by
  exact lt_of_not_ge hge


/--
Consider a finite MDP $(S,A,P,R,\gamma)$, where $S$ is a finite set of discrete states, $A$ is a
finite set of discrete actions, $R$ is the reward function, and $\gamma \in (0,1)$ is the discount
factor. Given state $s$ and action $a$ at time $t$, the probability of transitioning to state $s'$
at the next time step is $P(s'\mid s, a)=P(s_{t+1}=s'\mid s_t = s, a_t = a)$. Let $V(s)$ be the
value function, define the Bellman operator $B$: $ B V(s) = \max_{a} \left\{ R(s,a) + \gamma
\sum_{s' \in S} P(s'\mid s, a) V(s') \right\}, \quad \forall s \in S.$ Prove that the operator $B$
is a contraction mapping, i.e., $|BV-BV'|{\infty} \le \gamma |V-V'|{\infty}$, where $|V-V'|{\infty}
= \max{s} |V(s)-V'(s)|$.
-/
theorem num_50_P_H {S A} [Fintype S] [Fintype A] (gamma : ℝ) (R : S → A → ℝ) (f : S → ℝ)
  (P : S → S → A → ℝ) (B : (S → ℝ) → (S → ℝ)) (hgamma : 0 < gamma ∧ gamma < 1)
  (nonnegP : ∀ s t a, P s t a ≥ 0 ∧ P s t a ≤ 1) (sumP : ∀ t a, ∑ s, P s t a = 1)
  (Bellman : ∀ s V, B V s =
    (Finset.image (fun a => R s a + gamma * ∑ t, P t s a * V t) .univ).max) :
  ∀ V1 V2, ∀ s, ∃t, |B V1 s - B V2 s| ≤ gamma * |V1 t - V2 t| := by
  classical
  have hf : S → ℝ := f
  intro V1 V2 s
  by_cases hV : V1 = V2
  · refine ⟨s, ?_⟩
    simp [hV]
  ·
    haveI : Nonempty S := ⟨s⟩
    obtain ⟨t, htmax⟩ := exists_argmax_abs (S := S) V1 V2
    refine ⟨t, ?_⟩
    have hgamma_nonneg : 0 ≤ gamma := le_of_lt hgamma.1
    exact bellman_contraction (gamma := gamma) (R := R) (P := P) (B := B)
      nonnegP sumP Bellman V1 V2 s t htmax hgamma_nonneg

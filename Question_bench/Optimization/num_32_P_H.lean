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


/-A function $f : \mathbf{R}^k \to \mathbf{R}$ is \emph{monotone nondecreasing} (with respect to $\mathbf{R}_+^k$) if $f(u) \geq f(v)$ whenever $u \succeq v$.Show that there exists a convex monotone nondecreasing function $f : \mathbf{R}^k \to \mathbf{R}$, with $\operatorname{dom} f = \mathbf{R}^k$, that satisfies $f(u_i) = y_i$ for $i = 1, \ldots, m$, if and only if there exist $g_i \in \mathbf{R}^k$, $i = 1, \ldots, m$, such
that
\[
g_i \succeq 0, \quad i = 1, \ldots, m, \quad y_j \geq y_i + g_i^T (u_j - u_i), \quad i, j = 1, \ldots,
m.
\]

-/
/-- If all `y i` are equal, then choosing `g = 0` satisfies the inequalities. -/
lemma num_32_P_H.exists_g_of_y_const (m k : ℕ) [NeZero m]
    (u : Fin m → (Fin k → ℝ)) (y : Fin m → ℝ)
    (hy : ∀ i : Fin m, y i = y 0) :
    ∃ g : Fin m → (Fin k → ℝ), (∀ i, g i ≥ 0) ∧
      ∀ i j, y j ≥ y i + g i ⬝ᵥ (u j - u i) := by
  classical
  refine ⟨fun _ => 0, ?_, ?_⟩
  · intro i
    simp
  · intro i j
    simp [hy i, hy j]

/-- Interpolation for the finite supremum defined from `g`. -/
lemma num_32_P_H.f_from_g_interpolation (m k : ℕ) (u : Fin m → (Fin k → ℝ)) (y : Fin m → ℝ)
    (g : Fin m → (Fin k → ℝ)) (hm : (Finset.univ : Finset (Fin m)).Nonempty)
    (hineq : ∀ i j, y j ≥ y i + g i ⬝ᵥ (u j - u i)) :
    let f : (Fin k → ℝ) → ℝ :=
      fun x => (Finset.univ).sup' hm (fun i => y i + g i ⬝ᵥ (x - u i));
    ∀ i, f (u i) = y i := by
  classical
  dsimp
  intro i
  have hle :
      (Finset.univ).sup' hm (fun j => y j + g j ⬝ᵥ (u i - u j)) ≤ y i := by
    refine Finset.sup'_le (s := Finset.univ) (H := hm)
      (f := fun j => y j + g j ⬝ᵥ (u i - u j)) ?_
    intro j hj
    exact hineq j i
  have hge :
      y i ≤ (Finset.univ).sup' hm (fun j => y j + g j ⬝ᵥ (u i - u j)) := by
    refine Finset.le_sup'_of_le (s := Finset.univ)
      (f := fun j => y j + g j ⬝ᵥ (u i - u j)) (b := i) (Finset.mem_univ i) ?_
    simp
  have hsup :
      (Finset.univ).sup' hm (fun j => y j + g j ⬝ᵥ (u i - u j)) = y i :=
    le_antisymm hle hge
  exact hsup

/-- Monotonicity of the finite supremum when all `g i` are nonnegative. -/
lemma num_32_P_H.f_from_g_monotone (m k : ℕ) (u : Fin m → (Fin k → ℝ)) (y : Fin m → ℝ)
    (g : Fin m → (Fin k → ℝ)) (hm : (Finset.univ : Finset (Fin m)).Nonempty)
    (hg0 : ∀ i, g i ≥ 0) :
    let f : (Fin k → ℝ) → ℝ :=
      fun x => (Finset.univ).sup' hm (fun i => y i + g i ⬝ᵥ (x - u i));
    ∀ p q, p ≤ q → f p ≤ f q := by
  classical
  dsimp
  intro p q hpq
  refine Finset.sup'_le (s := Finset.univ) (H := hm)
    (f := fun i => y i + g i ⬝ᵥ (p - u i)) ?_
  intro i hi
  have hsub : (p - u i) ≤ (q - u i) := by
    intro j
    exact sub_le_sub_right (hpq j) _
  have hdot : g i ⬝ᵥ (p - u i) ≤ g i ⬝ᵥ (q - u i) :=
    dotProduct_le_dotProduct_of_nonneg_left hsub (hg0 i)
  have hterm : y i + g i ⬝ᵥ (p - u i) ≤ y i + g i ⬝ᵥ (q - u i) :=
    add_le_add_right hdot (y i)
  exact hterm.trans (Finset.le_sup' (s := Finset.univ)
    (f := fun j => y j + g j ⬝ᵥ (q - u j)) hi)

/-- Convexity of the finite supremum of affine functions. -/
lemma num_32_P_H.f_from_g_convex (m k : ℕ) (u : Fin m → (Fin k → ℝ)) (y : Fin m → ℝ)
    (g : Fin m → (Fin k → ℝ)) (hm : (Finset.univ : Finset (Fin m)).Nonempty) :
    let f : (Fin k → ℝ) → ℝ :=
      fun x => (Finset.univ).sup' hm (fun i => y i + g i ⬝ᵥ (x - u i));
    ConvexOn ℝ Set.univ f := by
  classical
  dsimp
  let F : Fin m → (Fin k → ℝ) → ℝ := fun i x => y i + g i ⬝ᵥ (x - u i)
  have hF : ∀ i, ConvexOn ℝ Set.univ (F i) := by
    intro i
    have hconv : Convex ℝ (Set.univ : Set (Fin k → ℝ)) := by
      simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin k → ℝ)))
    have hlin : ConvexOn ℝ Set.univ (fun x => g i ⬝ᵥ x) := by
      simpa using
        (LinearMap.convexOn (dotProductBilin ℝ ℝ (g i)) (s := Set.univ) hconv)
    have hlin' :
        ConvexOn ℝ Set.univ (fun x => y i + (g i ⬝ᵥ x - g i ⬝ᵥ u i)) := by
      have hlin'' :
          ConvexOn ℝ Set.univ (fun x => g i ⬝ᵥ x - g i ⬝ᵥ u i) := by
        simpa [sub_eq_add_neg] using (ConvexOn.add_const hlin (- g i ⬝ᵥ u i))
      simpa [add_comm] using (ConvexOn.add_const hlin'' (y i))
    have hrew :
        (fun x => y i + g i ⬝ᵥ (x - u i)) =
          (fun x => y i + (g i ⬝ᵥ x - g i ⬝ᵥ u i)) := by
      funext x
      simp [dotProduct_sub]
    simpa [F, hrew] using hlin'
  have hsup :
      ConvexOn ℝ Set.univ ((Finset.univ).sup' hm F) := by
    refine Finset.sup'_induction (s := Finset.univ) (H := hm) (f := F)
      (p := fun f => ConvexOn ℝ Set.univ f) ?_ ?_
    · intro f hf g hg
      simpa using (ConvexOn.sup hf hg)
    · intro i hi
      exact hF i
  have hfun :
      (Finset.univ).sup' hm F =
        (fun x => (Finset.univ).sup' hm (fun i => y i + g i ⬝ᵥ (x - u i))) := by
    funext x
    simp [F]
  simpa [hfun] using hsup

theorem num_32_P_H (m k : ℕ) [NeZero k] (u : Fin m → (Fin k → ℝ)) (y : Fin m → ℝ) :
  ∃ f : (Fin k → ℝ) → ℝ, (∀ i, f (u i) = y i) ∧ (∀ p q, (p ≤ q) → f p ≤ f q) ∧ ConvexOn ℝ .univ f ↔
  ∃ g : Fin m → (Fin k → ℝ), (∀ i, g i ≥ 0) ∧ ∀ i j, y j ≥ y i + g i ⬝ᵥ (u j - u i) := by
  classical
  by_cases hm0 : m = 0
  · subst hm0
    let f : (Fin k → ℝ) → ℝ := fun _ => 0
    refine ⟨f, ?_⟩
    have hP :
        (∀ i : Fin 0, f (u i) = y i) ∧
          (∀ p q, p ≤ q → f p ≤ f q) ∧ ConvexOn ℝ Set.univ f := by
      refine ⟨?_, ?_, ?_⟩
      · simp
      · intro p q hpq
        simp [f]
      ·
        have : Convex ℝ (Set.univ : Set (Fin k → ℝ)) := by
          simpa using (convex_univ : Convex ℝ (Set.univ : Set (Fin k → ℝ)))
        simpa [f] using (convexOn_const (c := (0 : ℝ)) (s := Set.univ) this)
    have hQ :
        ∃ g : Fin 0 → (Fin k → ℝ), (∀ i, g i ≥ 0) ∧
          ∀ i j, y j ≥ y i + g i ⬝ᵥ (u j - u i) := by
      refine ⟨fun _ => 0, ?_, ?_⟩ <;> simp
    constructor
    · intro _
      exact hQ
    · intro _
      exact hP
  ·
    haveI : NeZero m := ⟨hm0⟩
    have hm : (Finset.univ : Finset (Fin m)).Nonempty := by
      classical
      have hpos : 0 < m := Nat.pos_of_ne_zero hm0
      letI : Nonempty (Fin m) := ⟨⟨0, hpos⟩⟩
      simp
    by_cases hQ :
        ∃ g : Fin m → (Fin k → ℝ), (∀ i, g i ≥ 0) ∧
          ∀ i j, y j ≥ y i + g i ⬝ᵥ (u j - u i)
    · rcases hQ with ⟨g, hg0, hineq⟩
      have hQ' :
          ∃ g : Fin m → (Fin k → ℝ), (∀ i, g i ≥ 0) ∧
            ∀ i j, y j ≥ y i + g i ⬝ᵥ (u j - u i) := ⟨g, hg0, hineq⟩
      let f : (Fin k → ℝ) → ℝ :=
        fun x => (Finset.univ).sup' hm (fun i => y i + g i ⬝ᵥ (x - u i))
      have hf_inter : ∀ i, f (u i) = y i := by
        simpa [f] using
          (num_32_P_H.f_from_g_interpolation m k u y g hm hineq)
      have hf_mono : ∀ p q, p ≤ q → f p ≤ f q := by
        simpa [f] using
          (num_32_P_H.f_from_g_monotone m k u y g hm hg0)
      have hf_conv : ConvexOn ℝ Set.univ f := by
        simpa [f] using
          (num_32_P_H.f_from_g_convex m k u y g hm)
      have hP :
          (∀ i, f (u i) = y i) ∧ (∀ p q, p ≤ q → f p ≤ f q) ∧ ConvexOn ℝ Set.univ f :=
        ⟨hf_inter, hf_mono, hf_conv⟩
      refine ⟨f, ?_⟩
      constructor
      · intro _
        exact hQ'
      · intro _
        exact hP
    ·
      let f : (Fin k → ℝ) → ℝ := fun _ => y 0
      have hy_not : ¬ (∀ i : Fin m, y i = y 0) := by
        intro hy
        exact hQ (num_32_P_H.exists_g_of_y_const m k u y hy)
      have hPf :
          ¬ ((∀ i, f (u i) = y i) ∧
              (∀ p q, p ≤ q → f p ≤ f q) ∧ ConvexOn ℝ Set.univ f) := by
        intro hP
        have hy : ∀ i : Fin m, y i = y 0 := by
          intro i
          have : y 0 = y i := by
            simpa [f] using (hP.1 i)
          exact this.symm
        exact hy_not hy
      refine ⟨f, ?_⟩
      constructor
      · intro hP
        exact (hPf hP).elim
      · intro hQ'
        exact (hQ hQ').elim

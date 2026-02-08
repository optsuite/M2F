import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace WithLp
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


/-- Relate the dot product of a difference in `Fin n → ℝ` to the squared Euclidean norm. -/
lemma num_33_P_E_dotProduct_sub_self_eq_norm_sub_sq (n : ℕ) (x x0 : Fin n → ℝ) :
    (x - x0) ⬝ᵥ (x - x0) =
      ‖(toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0‖ ^ 2 := by
  have hsub :
      (toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0 = toLp 2 (x - x0) := by
    simpa using (toLp_sub (p := 2) x x0).symm
  have hinner :
      ⟪(toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0,
        (toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0⟫_ℝ =
        (x - x0) ⬝ᵥ (x - x0) := by
    calc
      ⟪(toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0,
        (toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0⟫_ℝ =
          ⟪toLp 2 (x - x0), toLp 2 (x - x0)⟫_ℝ := by
          rw [hsub]
      _ = (x - x0) ⬝ᵥ (x - x0) := by
          simpa using (EuclideanSpace.inner_toLp_toLp (x - x0) (x - x0))
  calc
    (x - x0) ⬝ᵥ (x - x0) =
        ⟪(toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0,
          (toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0⟫_ℝ := by
        simpa using hinner.symm
    _ = ‖(toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0‖ ^ 2 := by
        simpa using
          (real_inner_self_eq_norm_sq
            ((toLp 2 x : EuclideanSpace ℝ (Fin n)) - toLp 2 x0))

/-- Transfer closedness, convexity, and nonemptiness of `C` to `K := {z | ofLp z ∈ C}`. -/
lemma num_33_P_E_convex_closed_transfer (n : ℕ) (C : Set (Fin n → ℝ)) (hx : C ≠ ∅)
    (hC : IsClosed C ∧ Convex ℝ C) :
    IsClosed {z : EuclideanSpace ℝ (Fin n) | ofLp z ∈ C} ∧
      Convex ℝ {z : EuclideanSpace ℝ (Fin n) | ofLp z ∈ C} ∧
      ({z : EuclideanSpace ℝ (Fin n) | ofLp z ∈ C}).Nonempty := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin n)) := {z | ofLp z ∈ C}
  have hclosed : IsClosed K := by
    -- `K` is the preimage of `C` under `ofLp`.
    have hpre : IsClosed ((fun z : EuclideanSpace ℝ (Fin n) => ofLp z) ⁻¹' C) :=
      hC.1.preimage (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ))
    simpa [K, Set.preimage] using hpre
  have hconvex : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    have hxC : ofLp x ∈ C := hx
    have hyC : ofLp y ∈ C := hy
    have h := hC.2 hxC hyC ha hb hab
    simpa [K, ofLp_add, ofLp_smul] using h
  have hnonempty : K.Nonempty := by
    rcases Set.nonempty_iff_ne_empty.mpr hx with ⟨x, hxC⟩
    refine ⟨toLp 2 x, ?_⟩
    simpa [K] using hxC
  refine ⟨?_, ?_, ?_⟩
  · simpa [K] using hclosed
  · simpa [K] using hconvex
  · simpa [K] using hnonempty

/-- Uniqueness of a norm minimizer in a convex set of a real inner product space. -/
lemma num_33_P_E_unique_minimizer_norm
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hK : Convex ℝ K) {u v1 v2 : F}
    (hv1 : v1 ∈ K) (hv2 : v2 ∈ K)
    (h1 : ‖u - v1‖ = ⨅ w : K, ‖u - w‖)
    (h2 : ‖u - v2‖ = ⨅ w : K, ‖u - w‖) :
    v1 = v2 := by
  have hineq1 : ∀ w ∈ K, ⟪u - v1, w - v1⟫_ℝ ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hK hv1).1 h1
  have hineq2 : ∀ w ∈ K, ⟪u - v2, w - v2⟫_ℝ ≤ 0 := by
    exact (norm_eq_iInf_iff_real_inner_le_zero hK hv2).1 h2
  have h12 : ⟪u - v1, v2 - v1⟫_ℝ ≤ 0 := hineq1 v2 hv2
  have h21' : ⟪u - v2, v1 - v2⟫_ℝ ≤ 0 := hineq2 v1 hv1
  have h21 : 0 ≤ ⟪u - v2, v2 - v1⟫_ℝ := by
    have hsub : v1 - v2 = -(v2 - v1) := by
      abel
    have hneg' : -⟪u - v2, v2 - v1⟫_ℝ ≤ 0 := by
      have htmp := h21'
      rw [hsub] at htmp
      rw [inner_neg_right] at htmp
      exact htmp
    linarith
  have hrewrite :
      ⟪u - v2, v2 - v1⟫_ℝ =
        ⟪u - v1, v2 - v1⟫_ℝ - ⟪v2 - v1, v2 - v1⟫_ℝ := by
    have hsub : u - v2 = (u - v1) - (v2 - v1) := by
      abel
    calc
      ⟪u - v2, v2 - v1⟫_ℝ = ⟪(u - v1) - (v2 - v1), v2 - v1⟫_ℝ := by
        rw [hsub]
      _ = ⟪u - v1, v2 - v1⟫_ℝ - ⟪v2 - v1, v2 - v1⟫_ℝ := by
        simpa using (inner_sub_left (u - v1) (v2 - v1) (v2 - v1))
  have hinner_self_le : ⟪v2 - v1, v2 - v1⟫_ℝ ≤ 0 := by
    have h21' : 0 ≤
        ⟪u - v1, v2 - v1⟫_ℝ - ⟪v2 - v1, v2 - v1⟫_ℝ := by
      have h21'' := h21
      rw [hrewrite] at h21''
      exact h21''
    linarith
  have hinner_self_eq : ⟪v2 - v1, v2 - v1⟫_ℝ = 0 := by
    exact le_antisymm hinner_self_le (real_inner_self_nonneg (x := v2 - v1))
  have hzero : v2 - v1 = 0 := (inner_self_eq_zero).1 hinner_self_eq
  exact (sub_eq_zero.mp hzero).symm

/--
Show that if $C \subseteq \mathbb{R}^n$ is nonempty, closed and convex, and the norm
$\|\cdot\|$ is strictly convex, then for every $x_0$ there is exactly one $x \in C$ closest to
$x_0$. In other words the projection of $x_0$ on $C$ is unique.
-/
theorem num_33_P_E (n : ℕ) (C : Set (Fin n → ℝ)) (hx : C ≠ ∅) (hC : IsClosed C ∧ Convex ℝ C)
  (x0 : Fin n → ℝ) : ∃! x ∈ C, ∀ y ∈ C, (x - x0) ⬝ᵥ (x - x0) ≤ (y - x0) ⬝ᵥ (y - x0) := by
  classical
  let K : Set (EuclideanSpace ℝ (Fin n)) := {z | ofLp z ∈ C}
  let x0e : EuclideanSpace ℝ (Fin n) := toLp 2 x0
  have hK : IsClosed K ∧ Convex ℝ K ∧ K.Nonempty := by
    simpa [K] using num_33_P_E_convex_closed_transfer n C hx hC
  letI : Nonempty K := hK.2.2.to_subtype
  have hcomplete : IsComplete K := hK.1.isComplete
  obtain ⟨v, hvK, hvmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hK.2.2 hcomplete hK.2.1 x0e
  let x : Fin n → ℝ := ofLp v
  have hxC : x ∈ C := by
    simpa [K, x] using hvK
  have hminineq :
      ∀ y ∈ C, (x - x0) ⬝ᵥ (x - x0) ≤ (y - x0) ⬝ᵥ (y - x0) := by
    intro y hy
    have hyK : (toLp 2 y : EuclideanSpace ℝ (Fin n)) ∈ K := by
      simpa [K] using hy
    have hbdd :
        BddBelow (Set.range fun w : K => ‖x0e - w‖) := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨w, rfl⟩
      exact norm_nonneg _
    have hnorm_le :
        ‖x0e - v‖ ≤ ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
      have hci := ciInf_le hbdd (⟨toLp 2 y, hyK⟩ : K)
      calc
        ‖x0e - v‖ = ⨅ w : K, ‖x0e - w‖ := hvmin
        _ ≤ ‖x0e - (⟨toLp 2 y, hyK⟩ : K)‖ := hci
        _ = ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := rfl
    have hnorm_le' :
        ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ ≤
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ := by
      calc
        ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ =
            ‖x0e - (v : EuclideanSpace ℝ (Fin n))‖ := by
            simpa using (norm_sub_rev (v : EuclideanSpace ℝ (Fin n)) x0e)
        _ ≤ ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := hnorm_le
        _ = ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ := by
            simpa using (norm_sub_rev x0e (toLp 2 y))
    have hsq :
        ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 ≤
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := by
      have hmul :
          ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ *
            ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ ≤
            ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ *
              ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ := by
        exact mul_le_mul hnorm_le' hnorm_le' (norm_nonneg _) (norm_nonneg _)
      simpa [pow_two] using hmul
    have hxnorm :
        (x - x0) ⬝ᵥ (x - x0) =
          ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := by
      simpa [x, x0e] using
        (num_33_P_E_dotProduct_sub_self_eq_norm_sub_sq n x x0)
    have hynorm :
        (y - x0) ⬝ᵥ (y - x0) =
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := by
      simpa [x0e] using
        (num_33_P_E_dotProduct_sub_self_eq_norm_sub_sq n y x0)
    calc
      (x - x0) ⬝ᵥ (x - x0) = ‖(v : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := hxnorm
      _ ≤ ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := hsq
      _ = (y - x0) ⬝ᵥ (y - x0) := by
        simpa using hynorm.symm
  refine ⟨x, ?_, ?_⟩
  · exact ⟨hxC, hminineq⟩
  · intro y hy
    rcases hy with ⟨hyC, hymin⟩
    have hyK : (toLp 2 y : EuclideanSpace ℝ (Fin n)) ∈ K := by
      simpa [K] using hyC
    have hbdd :
        BddBelow (Set.range fun w : K => ‖x0e - w‖) := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨w, rfl⟩
      exact norm_nonneg _
    have hnorm_le :
        ∀ w : K, ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ≤ ‖x0e - w‖ := by
      intro w
      have hwC : ofLp (w : EuclideanSpace ℝ (Fin n)) ∈ C := w.property
      have hdot := hymin (ofLp (w : EuclideanSpace ℝ (Fin n))) hwC
      have hy_norm :
          (y - x0) ⬝ᵥ (y - x0) =
            ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := by
        simpa [x0e] using
          (num_33_P_E_dotProduct_sub_self_eq_norm_sub_sq n y x0)
      have hw_norm :
          (ofLp (w : EuclideanSpace ℝ (Fin n)) - x0) ⬝ᵥ
              (ofLp (w : EuclideanSpace ℝ (Fin n)) - x0) =
            ‖(w : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := by
        simpa [x0e] using
          (num_33_P_E_dotProduct_sub_self_eq_norm_sub_sq n
            (ofLp (w : EuclideanSpace ℝ (Fin n))) x0)
      have hsq :
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 ≤
            ‖(w : EuclideanSpace ℝ (Fin n)) - x0e‖ ^ 2 := by
        simpa [hy_norm, hw_norm] using hdot
      have hmul :
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ *
              ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ≤
            ‖(w : EuclideanSpace ℝ (Fin n)) - x0e‖ *
              ‖(w : EuclideanSpace ℝ (Fin n)) - x0e‖ := by
        simpa [pow_two] using hsq
      have hle :
          ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ ≤
            ‖(w : EuclideanSpace ℝ (Fin n)) - x0e‖ :=
        nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _) hmul
      calc
        ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ =
            ‖(toLp 2 y : EuclideanSpace ℝ (Fin n)) - x0e‖ := by
            simpa using (norm_sub_rev x0e (toLp 2 y))
        _ ≤ ‖(w : EuclideanSpace ℝ (Fin n)) - x0e‖ := hle
        _ = ‖x0e - (w : EuclideanSpace ℝ (Fin n))‖ := by
            simpa using (norm_sub_rev (w : EuclideanSpace ℝ (Fin n)) x0e)
    have hle_ciInf :
        ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ≤
          ⨅ w : K, ‖x0e - w‖ := by
      classical
      have h' : ∀ w : K, ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ ≤ ‖x0e - w‖ := by
        intro w
        simpa using hnorm_le w
      exact le_ciInf (fun w => h' w)
    have hciInf_le :
        (⨅ w : K, ‖x0e - w‖) ≤ ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ := by
      exact ciInf_le hbdd (⟨toLp 2 y, hyK⟩ : K)
    have hymin_eq :
        ‖x0e - (toLp 2 y : EuclideanSpace ℝ (Fin n))‖ =
          ⨅ w : K, ‖x0e - w‖ := by
      exact le_antisymm hle_ciInf hciInf_le
    have hv_eq :
        v = (toLp 2 y : EuclideanSpace ℝ (Fin n)) := by
      have hvmin' : ‖x0e - v‖ = ⨅ w : K, ‖x0e - w‖ := hvmin
      exact num_33_P_E_unique_minimizer_norm hK.2.1 hvK hyK hvmin' hymin_eq
    have hx_eq : x = y := by
      have : ofLp v = ofLp (toLp 2 y : EuclideanSpace ℝ (Fin n)) := by
        simpa [hv_eq]
      simpa [x] using this
    exact hx_eq.symm

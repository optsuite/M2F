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


/-- The minimax inequality in a complete linear order. -/
lemma iSup₂_iInf₂_le_iInf₂_iSup₂_complete {E F β : Type*} [CompleteLinearOrder β]
    (X : Set E) (Y : Set F) (f : E → F → β) :
    (⨆ y ∈ Y, ⨅ x ∈ X, f x y) ≤ (⨅ x ∈ X, ⨆ y ∈ Y, f x y) := by
  simpa using (iSup₂_iInf₂_le_iInf₂_iSup₂ (X := X) (Y := Y) (f := f))

/-- The minimax inequality after coercing to `EReal`, which is a complete linear order. -/
lemma iSup₂_iInf₂_le_iInf₂_iSup₂_ereal {E F : Type*} (X : Set E) (Y : Set F) (f : E → F → ℝ) :
    (⨆ y ∈ Y, ⨅ x ∈ X, (f x y : EReal)) ≤ (⨅ x ∈ X, ⨆ y ∈ Y, (f x y : EReal)) := by
  simpa using
    (iSup₂_iInf₂_le_iInf₂_iSup₂ (X := X) (Y := Y) (f := fun x y => (f x y : EReal)))

/-- Transfer the minimax inequality from `EReal` once the coercions commute with `iSup`/`iInf`. -/
lemma num_28_P_H_of_ereal {m n : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (hSupInf :
      Real.toEReal (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = ⨆ z ∈ Z, ⨅ w ∈ W, (f w z : EReal) ∧
      Real.toEReal (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = ⨅ w ∈ W, ⨆ z ∈ Z, (f w z : EReal)) :
    (⨆ z ∈ Z, ⨅ w ∈ W, f w z) ≤ (⨅ w ∈ W, ⨆ z ∈ Z, f w z) := by
  rcases hSupInf with ⟨hSup, hInf⟩
  -- Work in `EReal`, then pass to `ℝ` via `toReal`.
  set supE : EReal := ⨆ z ∈ Z, ⨅ w ∈ W, (f w z : EReal)
  set infE : EReal := ⨅ w ∈ W, ⨆ z ∈ Z, (f w z : EReal)
  have hE : supE ≤ infE := by
    simpa [supE, infE] using
      (iSup₂_iInf₂_le_iInf₂_iSup₂_ereal (X := W) (Y := Z) (f := f))
  have hSup_ne_bot : supE ≠ ⊥ := by
    intro hbot
    have : Real.toEReal (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = ⊥ := by
      calc
        Real.toEReal (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = supE := by simpa [supE] using hSup
        _ = ⊥ := hbot
    exact (EReal.coe_ne_bot _) this
  have hInf_ne_top : infE ≠ ⊤ := by
    intro htop
    have : Real.toEReal (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = ⊤ := by
      calc
        Real.toEReal (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = infE := by simpa [infE] using hInf
        _ = ⊤ := htop
    exact (EReal.coe_ne_top _) this
  have hE_real : supE.toReal ≤ infE.toReal :=
    EReal.toReal_le_toReal (x := supE) (y := infE) hE hSup_ne_bot hInf_ne_top
  have hSup_toReal : supE.toReal = ⨆ z ∈ Z, ⨅ w ∈ W, f w z := by
    have h := congrArg EReal.toReal hSup
    simpa [supE] using h.symm
  have hInf_toReal : infE.toReal = ⨅ w ∈ W, ⨆ z ∈ Z, f w z := by
    have h := congrArg EReal.toReal hInf
    simpa [infE] using h.symm
  simpa [hSup_toReal, hInf_toReal] using hE_real

/-- `BddBelow` is preserved when coercing into `WithTop`. -/
lemma bddBelow_range_coe_withTop {ι : Sort*} {f : ι → ℝ} (hf : BddBelow (Set.range f)) :
    BddBelow (Set.range fun i => (f i : WithTop ℝ)) := by
  rcases hf with ⟨a, ha⟩
  refine ⟨(a : WithTop ℝ), ?_⟩
  intro y hy
  rcases hy with ⟨i, rfl⟩
  have hle : a ≤ f i := ha ⟨i, rfl⟩
  simpa using hle

/-- Coercion to `EReal` commutes with `iSup` for bounded real families. -/
lemma toEReal_iSup_of_bdd {ι : Sort*} [Nonempty ι] {f : ι → ℝ}
    (hf : BddAbove (Set.range f)) :
    Real.toEReal (⨆ i, f i) = ⨆ i, (f i : EReal) := by
  have htop : ((⨆ i, f i : ℝ) : WithTop ℝ) = ⨆ i, (f i : WithTop ℝ) := by
    exact (WithTop.coe_iSup (f := f) hf)
  have hbot :
      (((⨆ i, (f i : WithTop ℝ)) : WithTop ℝ) : WithBot (WithTop ℝ)) =
        ⨆ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ)) := by
    exact
      (WithBot.coe_iSup (f := fun i => (f i : WithTop ℝ)) (OrderTop.bddAbove _))
  change (((⨆ i, f i : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) =
      ⨆ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ))
  have htop' :
      (((⨆ i, f i : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) =
        (((⨆ i, (f i : WithTop ℝ)) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
    exact congrArg (fun x : WithTop ℝ => (x : WithBot (WithTop ℝ))) htop
  simp [htop', hbot]

/-- Coercion to `EReal` commutes with `iInf` for bounded real families. -/
lemma toEReal_iInf_of_bdd {ι : Sort*} [Nonempty ι] {f : ι → ℝ}
    (hf : BddBelow (Set.range f)) :
    Real.toEReal (⨅ i, f i) = ⨅ i, (f i : EReal) := by
  have htop : ((⨅ i, f i : ℝ) : WithTop ℝ) = ⨅ i, (f i : WithTop ℝ) := by
    exact (WithTop.coe_iInf (f := f) hf)
  have hf' : BddBelow (Set.range fun i => (f i : WithTop ℝ)) :=
    bddBelow_range_coe_withTop (f := f) hf
  have hbot :
      (((⨅ i, (f i : WithTop ℝ)) : WithTop ℝ) : WithBot (WithTop ℝ)) =
        ⨅ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ)) := by
    exact (WithBot.coe_iInf (f := fun i => (f i : WithTop ℝ)) hf')
  change (((⨅ i, f i : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) =
      ⨅ i, ((f i : WithTop ℝ) : WithBot (WithTop ℝ))
  have htop' :
      (((⨅ i, f i : ℝ) : WithTop ℝ) : WithBot (WithTop ℝ)) =
        (((⨅ i, (f i : WithTop ℝ)) : WithTop ℝ) : WithBot (WithTop ℝ)) := by
    exact congrArg (fun x : WithTop ℝ => (x : WithBot (WithTop ℝ))) htop
  simp [htop', hbot]

/-- `EReal` coercion commutes with the outer `iSup`/`iInf` under boundedness. -/
lemma num_28_P_H_hSupInf_of_bdd {m n : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (hSup :
      BddAbove (Set.range fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z))
    (hInf :
      BddBelow (Set.range fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z)) :
    Real.toEReal (⨆ z ∈ Z, ⨅ w ∈ W, f w z) =
        ⨆ z, Real.toEReal (⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z) ∧
      Real.toEReal (⨅ w ∈ W, ⨆ z ∈ Z, f w z) =
        ⨅ w, Real.toEReal (⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z) := by
  refine ⟨?_, ?_⟩
  · exact
      (toEReal_iSup_of_bdd (f := fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z) hSup)
  · exact
      (toEReal_iInf_of_bdd (f := fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z) hInf)

/-- If the outer `iSup` range is unbounded above, the real `iSup` collapses to `0`. -/
lemma num_28_P_H_iSup_eq_zero_of_not_bddAbove {m n : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (hSup : ¬ BddAbove (Set.range fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z)) :
    (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = 0 := by
  have h :=
    Real.iSup_of_not_bddAbove
      (f := fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z) hSup
  simpa using h

/-- If the outer `iInf` range is unbounded below, the real `iInf` collapses to `0`. -/
lemma num_28_P_H_iInf_eq_zero_of_not_bddBelow {m n : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (hInf : ¬ BddBelow (Set.range fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z)) :
    (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = 0 := by
  have h :=
    Real.iInf_of_not_bddBelow
      (f := fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z) hInf
  simpa using h

/-- In the unbounded case, at least one outer real extremum is forced to be `0`. -/
lemma num_28_P_H_unbounded_sup_or_inf_eq_zero {m n : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (hbd :
      ¬ (BddAbove (Set.range fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z) ∧
         BddBelow (Set.range fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z))) :
    (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = 0 ∨
      (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = 0 := by
  have hbd' :
      ¬ BddAbove (Set.range fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z) ∨
        ¬ BddBelow (Set.range fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z) :=
    (not_and_or.mp hbd)
  rcases hbd' with hSup | hInf
  · left
    exact num_28_P_H_iSup_eq_zero_of_not_bddAbove (f := f) (W := W) (Z := Z) hSup
  · right
    exact num_28_P_H_iInf_eq_zero_of_not_bddBelow (f := f) (W := W) (Z := Z) hInf

/-- In the unbounded case, at least one coerced extremum equals `0` in `EReal`. -/
lemma num_28_P_H_unbounded_sup_or_inf_eq_zero_ereal {m n : ℕ}
    (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ))
    (hbd :
      ¬ (BddAbove (Set.range fun z => ⨆ _ : z ∈ Z, ⨅ w ∈ W, f w z) ∧
         BddBelow (Set.range fun w => ⨅ _ : w ∈ W, ⨆ z ∈ Z, f w z))) :
    Real.toEReal (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = 0 ∨
      Real.toEReal (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = 0 := by
  have h0 :=
    num_28_P_H_unbounded_sup_or_inf_eq_zero (f := f) (W := W) (Z := Z) hbd
  rcases h0 with h0 | h0
  · left
    exact (EReal.coe_eq_zero).2 h0
  · right
    exact (EReal.coe_eq_zero).2 h0

/-- Quadratic function used in the counterexample. -/
def num_28_P_H_counterexample_f (w z : Fin 1 → ℝ) : ℝ :=
  1 + (w 0 - z 0) ^ 2

/-- The counterexample function is unbounded above in its second argument. -/
lemma num_28_P_H_counterexample_not_bddAbove (w : Fin 1 → ℝ) :
    ¬ BddAbove (Set.range (fun z => num_28_P_H_counterexample_f w z)) := by
  refine (not_bddAbove_iff).2 ?_
  intro r
  let z : Fin 1 → ℝ := fun _ => w 0 + (r + 1)
  refine ⟨num_28_P_H_counterexample_f w z, ?_, ?_⟩
  · exact ⟨z, rfl⟩
  · simp [num_28_P_H_counterexample_f, z]
    nlinarith

/-- The right-hand side of the counterexample collapses to `0` in `ℝ`. -/
lemma num_28_P_H_counterexample_rhs_eq_zero :
    (⨅ w : Fin 1 → ℝ, ⨆ z : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) = 0 := by
  have h0 : ∀ w : Fin 1 → ℝ, (⨆ z : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) = 0 := by
    intro w
    have h :=
      Real.iSup_of_not_bddAbove (f := fun z : Fin 1 → ℝ => num_28_P_H_counterexample_f w z)
        (num_28_P_H_counterexample_not_bddAbove w)
    simpa using h
  simp [h0]

/-- For fixed `z`, the infimum over `w` of the counterexample is `1`. -/
lemma num_28_P_H_counterexample_inf_eq_one (z : Fin 1 → ℝ) :
    (⨅ w : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) = 1 := by
  have h_lower : 1 ≤ ⨅ w : Fin 1 → ℝ, num_28_P_H_counterexample_f w z := by
    refine le_ciInf ?_
    intro w
    have hsq : 0 ≤ (w 0 - z 0) ^ 2 := by nlinarith
    have hle : 1 ≤ 1 + (w 0 - z 0) ^ 2 := by linarith
    simpa [num_28_P_H_counterexample_f] using hle
  have h_bdd : BddBelow (Set.range (fun w : Fin 1 → ℝ => num_28_P_H_counterexample_f w z)) := by
    refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨w, rfl⟩
    have hsq : 0 ≤ (w 0 - z 0) ^ 2 := by nlinarith
    have hle : 1 ≤ 1 + (w 0 - z 0) ^ 2 := by linarith
    simpa [num_28_P_H_counterexample_f] using hle
  have h_upper : (⨅ w : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) ≤ 1 := by
    have h :=
      ciInf_le (f := fun w : Fin 1 → ℝ => num_28_P_H_counterexample_f w z) h_bdd z
    simpa [num_28_P_H_counterexample_f] using h
  exact le_antisymm h_upper h_lower

/-- The left-hand side of the counterexample equals `1`. -/
lemma num_28_P_H_counterexample_lhs_eq_one :
    (⨆ z : Fin 1 → ℝ, ⨅ w : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) = 1 := by
  have h1 : ∀ z : Fin 1 → ℝ, (⨅ w : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) = 1 := by
    intro z
    exact num_28_P_H_counterexample_inf_eq_one z
  simp [h1]

/-- The claimed inequality fails for the quadratic counterexample on `Set.univ`. -/
lemma num_28_P_H_counterexample :
    ¬ ((⨆ z ∈ (Set.univ : Set (Fin 1 → ℝ)),
          ⨅ w ∈ (Set.univ : Set (Fin 1 → ℝ)), num_28_P_H_counterexample_f w z) ≤
        (⨅ w ∈ (Set.univ : Set (Fin 1 → ℝ)),
          ⨆ z ∈ (Set.univ : Set (Fin 1 → ℝ)), num_28_P_H_counterexample_f w z)) := by
  have hlt :
      (⨅ w : Fin 1 → ℝ, ⨆ z : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) <
        (⨆ z : Fin 1 → ℝ, ⨅ w : Fin 1 → ℝ, num_28_P_H_counterexample_f w z) := by
    simp [num_28_P_H_counterexample_rhs_eq_zero, num_28_P_H_counterexample_lhs_eq_one]
  have hlt' :
      (⨅ w ∈ (Set.univ : Set (Fin 1 → ℝ)),
          ⨆ z ∈ (Set.univ : Set (Fin 1 → ℝ)), num_28_P_H_counterexample_f w z) <
        (⨆ z ∈ (Set.univ : Set (Fin 1 → ℝ)),
          ⨅ w ∈ (Set.univ : Set (Fin 1 → ℝ)), num_28_P_H_counterexample_f w z) := by
    simpa using hlt
  exact not_le_of_gt hlt'

/-- The universal minimax statement contradicts the counterexample instance. -/
lemma num_28_P_H_unprovable :
    (∀ (m n : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
        (W : Set (Fin n → ℝ)) (Z : Set (Fin m → ℝ)),
        (⨆ z ∈ Z, ⨅ w ∈ W, f w z) ≤ (⨅ w ∈ W, ⨆ z ∈ Z, f w z)) → False := by
  intro h
  have h' := h 1 1 num_28_P_H_counterexample_f Set.univ Set.univ
  exact num_28_P_H_counterexample h'

/--
Show that the weak max-min inequality
\[
\sup_{z \in Z} \inf_{w \in W} f(w, z) \leq \inf_{w \in W} \sup_{z \in Z} f(w, z)
\]
holds when coercion to `EReal` commutes with the outer `iSup`/`iInf` for
\( f : \mathbb{R}^n \times \mathbb{R}^m \to \mathbb{R} \) and \( W \subseteq \mathbb{R}^n \),
\( Z \subseteq \mathbb{R}^m \).
-/
theorem num_28_P_H (m n : ℕ) (f : (Fin n → ℝ) → (Fin m → ℝ) → ℝ) (W : Set (Fin n → ℝ))
  (Z : Set (Fin m → ℝ))
  (hSupInf :
    Real.toEReal (⨆ z ∈ Z, ⨅ w ∈ W, f w z) = ⨆ z ∈ Z, ⨅ w ∈ W, (f w z : EReal) ∧
      Real.toEReal (⨅ w ∈ W, ⨆ z ∈ Z, f w z) = ⨅ w ∈ W, ⨆ z ∈ Z, (f w z : EReal)) :
  (⨆ z ∈ Z, ⨅ w ∈ W, f w z) ≤ (⨅ w ∈ W, ⨆ z ∈ Z, f w z) := by
  exact num_28_P_H_of_ereal (f := f) (W := W) (Z := Z) hSupInf

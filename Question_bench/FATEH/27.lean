import Mathlib

open scoped Matrix

-- Evaluation of a matrix subalgebra element on a fixed vector.
def evalLinear {n : ℕ} (F : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℚ)) (v : Fin n → ℚ) :
    F →ₗ[ℚ] (Fin n → ℚ) :=
  { toFun := fun a => (a : Matrix (Fin n) (Fin n) ℚ) *ᵥ v
    map_add' := by
      intro a b
      simpa [Subalgebra.coe_add] using
        (Matrix.add_mulVec (A := (a : Matrix (Fin n) (Fin n) ℚ))
          (B := (b : Matrix (Fin n) (Fin n) ℚ)) (x := v))
    map_smul' := by
      intro r a
      simpa using
        (Matrix.smul_mulVec (b := r) (M := (a : Matrix (Fin n) (Fin n) ℚ)) (v := v)) }

@[simp]
lemma evalLinear_apply {n : ℕ} (F : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℚ)) (v : Fin n → ℚ)
    (a : F) : evalLinear F v a = (a : Matrix (Fin n) (Fin n) ℚ) *ᵥ v := rfl

-- A nonzero vector detects distinct field elements by matrix action.
lemma evalLinear_injective {n : ℕ} (F : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℚ))
    (hF : IsField F) {v : Fin n → ℚ} (hv : v ≠ 0) :
    Function.Injective (evalLinear F v) := by
  classical
  letI := hF.toField
  intro a b h
  by_contra hne
  have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
  have hunit : IsUnit (a - b : F) := isUnit_iff_ne_zero.mpr hne'
  have hunitM : IsUnit ((a - b : F) : Matrix (Fin n) (Fin n) ℚ) :=
    hunit.map (F.val : F →+* Matrix (Fin n) (Fin n) ℚ)
  have hinj :
      Function.Injective (((a - b : F) : Matrix (Fin n) (Fin n) ℚ).mulVec) :=
    (Matrix.mulVec_injective_iff_isUnit
      (A := ((a - b : F) : Matrix (Fin n) (Fin n) ℚ))).2 hunitM
  have hmul : ((a - b : F) : Matrix (Fin n) (Fin n) ℚ) *ᵥ v = 0 := by
    have h' :
        (a : Matrix (Fin n) (Fin n) ℚ) *ᵥ v =
          (b : Matrix (Fin n) (Fin n) ℚ) *ᵥ v := by
      simpa using h
    calc
      ((a - b : F) : Matrix (Fin n) (Fin n) ℚ) *ᵥ v
          =
            (a : Matrix (Fin n) (Fin n) ℚ) *ᵥ v -
              (b : Matrix (Fin n) (Fin n) ℚ) *ᵥ v := by
            simpa [Subalgebra.coe_sub] using
              (Matrix.sub_mulVec (A := (a : Matrix (Fin n) (Fin n) ℚ))
                (B := (b : Matrix (Fin n) (Fin n) ℚ)) (x := v))
      _ = 0 := by simp [h']
  have hv0 : v = 0 := by
    apply hinj
    calc
      ((a - b : F) : Matrix (Fin n) (Fin n) ℚ) *ᵥ v = 0 := hmul
      _ = ((a - b : F) : Matrix (Fin n) (Fin n) ℚ) *ᵥ 0 := by
        simp
  exact hv hv0

/-- Let $F$ be a field contained in the ring of $n \times n$ matrices over $\mathbb{Q}$.
Prove that $[F:\mathbb{Q}] \leq n$. -/
theorem rank_le_of_subalgebra_matrix {n : ℕ} (F : Subalgebra ℚ (Matrix (Fin n) (Fin n) ℚ))
    (h : IsField F) : Module.rank ℚ F ≤ n := by
  classical
  cases n with
  | zero =>
      exfalso
      haveI : Subsingleton (Matrix (Fin 0) (Fin 0) ℚ) := by infer_instance
      haveI : Subsingleton F := by infer_instance
      exact (not_isField_of_subsingleton F) h
  | succ n =>
      let v : Fin (Nat.succ n) → ℚ := fun i => if i = 0 then 1 else 0
      have hv : v ≠ 0 := by
        intro hzero
        have : (1 : ℚ) = 0 := by
          simpa [v] using congrArg (fun f => f 0) hzero
        exact one_ne_zero this
      have hinj : Function.Injective (evalLinear F v) :=
        evalLinear_injective F h hv
      have hrank :
          Module.rank ℚ F ≤ Module.rank ℚ (Fin (Nat.succ n) → ℚ) :=
        LinearMap.rank_le_of_injective (evalLinear F v) hinj
      simpa [rank_fin_fun] using hrank

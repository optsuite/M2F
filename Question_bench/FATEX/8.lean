import Mathlib

open Quaternion
open scoped Matrix

/-- `M₂(ℝ)` has zero divisors, so it is not a domain. -/
lemma matrix_not_isDomain : ¬ IsDomain (Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  intro hdom
  haveI : IsDomain (Matrix (Fin 2) (Fin 2) ℝ) := hdom
  let E : Matrix (Fin 2) (Fin 2) ℝ := Matrix.single 0 1 (1 : ℝ)
  have hE_nonzero : E ≠ 0 := by
    intro hzero
    have h : False := by
      simpa [E] using congrArg (fun M => M 0 1) hzero
    exact h
  have hE_sq : E * E = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [E, Matrix.mul_apply]
  have hE_eq : E = 0 := by
    have hmul : E * E = E * 0 := by
      calc
        E * E = 0 := hE_sq
        _ = E * 0 := by simp
    exact mul_left_cancel₀ (a := E) (b := E) (c := 0) hE_nonzero hmul
  exact hE_nonzero hE_eq

/-- No `ℝ`-algebra equivalence between `M₂(ℝ)` and Hamilton's quaternions. -/
lemma no_algEquiv_matrix_hamilton :
    IsEmpty (Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] ℍ[ℝ, -1, -1]) := by
  classical
  refine ⟨?h⟩
  intro e
  haveI : IsDomain ℍ[ℝ, -1, -1] := by
    simpa using (by infer_instance : IsDomain ℍ[ℝ])
  have hdom : IsDomain (Matrix (Fin 2) (Fin 2) ℝ) :=
    (MulEquiv.isDomain_iff (e := e.toMulEquiv)).mpr (by infer_instance)
  exact matrix_not_isDomain hdom

section MatrixModel

/-- `ℍ[ℝ, 1, 1]` as `2×2` matrices over `ℝ` (split quaternions). -/
noncomputable def quaternionBasisMatrix11 :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ) where
  i := !![(1 : ℝ), 0; 0, (-1 : ℝ)]
  j := !![(0 : ℝ), 1; 1, (0 : ℝ)]
  k := !![(0 : ℝ), 1; (-1 : ℝ), (0 : ℝ)]
  i_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  j_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  i_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  j_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

noncomputable def toMatrix11 : ℍ[ℝ, (1 : ℝ), (1 : ℝ)] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (quaternionBasisMatrix11).liftHom

@[simp]
lemma toMatrix11_mk (a b c d : ℝ) :
    toMatrix11 (⟨a, b, c, d⟩ : ℍ[ℝ, (1 : ℝ), (1 : ℝ)]) =
      !![a + b, c + d; c - d, a - b] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [toMatrix11, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift,
      quaternionBasisMatrix11, Matrix.algebraMap_eq_diagonal] <;> ring

noncomputable def quaternionAlgEquivMatrix11 :
    ℍ[ℝ, (1 : ℝ), (1 : ℝ)] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  classical
  refine AlgEquiv.ofBijective toMatrix11 ?_
  constructor
  · -- injective follows from surjective (both sides have `finrank = 4`)
    have hfin :
        Module.finrank ℝ ℍ[ℝ, (1 : ℝ), (1 : ℝ)] =
          Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) := by
      -- both are `4`
      have h₁ :
          Module.finrank ℝ (ℍ[ℝ, (1 : ℝ), (0 : ℝ), (1 : ℝ)]) = 4 := by
        simpa using
          (QuaternionAlgebra.finrank_eq_four (R := ℝ) (c₁ := (1 : ℝ)) (c₂ := (0 : ℝ))
            (c₃ := (1 : ℝ)))
      have h₂ :
          Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) = 4 := by
        simp [Module.finrank_matrix]
      simpa using (h₁.trans h₂.symm)
    have hsurj : Function.Surjective toMatrix11 := by
      intro M
      refine ⟨(⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / 2, (M 0 1 + M 1 0) / 2,
        (M 0 1 - M 1 0) / 2⟩ : ℍ[ℝ, (1 : ℝ), (1 : ℝ)]), ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [toMatrix11_mk] <;> ring
    -- now use the finite-dimensional linear-algebra lemma
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
          (f := (toMatrix11.toLinearMap))).2 hsurj
  · intro M
    refine ⟨(⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / 2, (M 0 1 + M 1 0) / 2,
      (M 0 1 - M 1 0) / 2⟩ : ℍ[ℝ, (1 : ℝ), (1 : ℝ)]), ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [toMatrix11_mk] <;> ring

/-- `ℍ[ℝ, 1, -1]` as `2×2` matrices over `ℝ` (split quaternions). -/
noncomputable def quaternionBasisMatrix1m1 :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℝ) (1 : ℝ) (0 : ℝ) (-1 : ℝ) where
  i := !![(1 : ℝ), 0; 0, (-1 : ℝ)]
  j := !![(0 : ℝ), (-1 : ℝ); (1 : ℝ), (0 : ℝ)]
  k := !![(0 : ℝ), (-1 : ℝ); (-1 : ℝ), (0 : ℝ)]
  i_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  j_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  i_mul_j := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]
  j_mul_i := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply]

noncomputable def toMatrix1m1 : ℍ[ℝ, (1 : ℝ), (-1 : ℝ)] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ :=
  (quaternionBasisMatrix1m1).liftHom

@[simp]
lemma toMatrix1m1_mk (a b c d : ℝ) :
    toMatrix1m1 (⟨a, b, c, d⟩ : ℍ[ℝ, (1 : ℝ), (-1 : ℝ)]) =
      !![a + b, -(c + d); c - d, a - b] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [toMatrix1m1, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift,
      quaternionBasisMatrix1m1, Matrix.algebraMap_eq_diagonal] <;> ring

noncomputable def quaternionAlgEquivMatrix1m1 :
    ℍ[ℝ, (1 : ℝ), (-1 : ℝ)] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ := by
  classical
  refine AlgEquiv.ofBijective toMatrix1m1 ?_
  constructor
  · have hfin :
        Module.finrank ℝ ℍ[ℝ, (1 : ℝ), (-1 : ℝ)] =
          Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) := by
      have h₁ :
          Module.finrank ℝ (ℍ[ℝ, (1 : ℝ), (0 : ℝ), (-1 : ℝ)]) = 4 := by
        simpa using
          (QuaternionAlgebra.finrank_eq_four (R := ℝ) (c₁ := (1 : ℝ)) (c₂ := (0 : ℝ))
            (c₃ := (-1 : ℝ)))
      have h₂ :
          Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℝ) = 4 := by
        simp [Module.finrank_matrix]
      simpa using (h₁.trans h₂.symm)
    have hsurj : Function.Surjective toMatrix1m1 := by
      intro M
      refine ⟨(⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / 2, (-M 0 1 + M 1 0) / 2,
        (-M 0 1 - M 1 0) / 2⟩ : ℍ[ℝ, (1 : ℝ), (-1 : ℝ)]), ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [toMatrix1m1_mk] <;> ring
    exact
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
          (f := (toMatrix1m1.toLinearMap))).2 hsurj
  · intro M
    refine ⟨(⟨(M 0 0 + M 1 1) / 2, (M 0 0 - M 1 1) / 2, (-M 0 1 + M 1 0) / 2,
      (-M 0 1 - M 1 0) / 2⟩ : ℍ[ℝ, (1 : ℝ), (-1 : ℝ)]), ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [toMatrix1m1_mk] <;> ring

end MatrixModel

section Classification

private lemma abs_mul_realSign (a : ℝ) (ha : a ≠ 0) : |a| * Real.sign a = a := by
  obtain hlt | hgt := lt_or_gt_of_ne ha
  · simp [Real.sign_of_neg hlt, abs_of_neg hlt]
  · simp [Real.sign_of_pos hgt, abs_of_pos hgt]

noncomputable def quaternionAlgEquivNormalize (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ℍ[ℝ, a, b] ≃ₐ[ℝ] ℍ[ℝ, Real.sign a, Real.sign b] := by
  classical
  let u : ℝ := Real.sqrt |a|
  let v : ℝ := Real.sqrt |b|
  have hu : u ≠ 0 := by
    have : (0 : ℝ) < |a| := abs_pos.mpr ha
    exact (Real.sqrt_ne_zero').2 this
  have hv : v ≠ 0 := by
    have : (0 : ℝ) < |b| := abs_pos.mpr hb
    exact (Real.sqrt_ne_zero').2 this
  have hu2 : u * u = |a| := by simp [u]
  have hv2 : v * v = |b| := by simp [v]
  have hmulA : u * u * Real.sign a = a := by
    -- `u^2 = |a|` and `|a| * sign a = a`
    calc
      u * u * Real.sign a = |a| * Real.sign a := by simp [hu2]
      _ = a := abs_mul_realSign a ha
  have hmulB : v * v * Real.sign b = b := by
    calc
      v * v * Real.sign b = |b| * Real.sign b := by simp [hv2]
      _ = b := abs_mul_realSign b hb

  let qN : QuaternionAlgebra.Basis (ℍ[ℝ, Real.sign a, Real.sign b]) (Real.sign a) (0 : ℝ)
      (Real.sign b) :=
    QuaternionAlgebra.Basis.self ℝ
  let qO : QuaternionAlgebra.Basis (ℍ[ℝ, a, b]) (a : ℝ) (0 : ℝ) (b : ℝ) :=
    QuaternionAlgebra.Basis.self ℝ

  -- `ℍ[ℝ, a, b] →ₐ[ℝ] ℍ[ℝ, sign a, sign b]` by scaling `i` and `j`.
  let qT : QuaternionAlgebra.Basis (ℍ[ℝ, Real.sign a, Real.sign b]) a (0 : ℝ) b :=
    { i := u • qN.i
      j := v • qN.j
      k := (u • qN.i) * (v • qN.j)
      i_mul_i := by
        have hi : qN.i * qN.i = (Real.sign a : ℝ) • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
          simp [qN.i_mul_i]
        have hcalc :
            (u • qN.i) * (u • qN.i) = a • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
          calc
            (u • qN.i) * (u • qN.i) = (u * u) • (qN.i * qN.i) := by
              simp [smul_smul, mul_assoc]
            _ = (u * u) • ((Real.sign a : ℝ) • (1 : ℍ[ℝ, Real.sign a, Real.sign b])) := by
              simp [hi]
            _ = ((u * u) * Real.sign a) • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
              simp [smul_smul]
            _ = a • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
              simp [hmulA]
        -- `c₂ = 0`, so the statement is `= a•1 + 0•i`.
        simp [hcalc]
      j_mul_j := by
        have hj : qN.j * qN.j = (Real.sign b : ℝ) • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
          simp [qN.j_mul_j]
        calc
          (v • qN.j) * (v • qN.j) = (v * v) • (qN.j * qN.j) := by
            simp [smul_smul, mul_assoc]
          _ = (v * v) • ((Real.sign b : ℝ) • (1 : ℍ[ℝ, Real.sign a, Real.sign b])) := by
            simp [hj]
          _ = ((v * v) * Real.sign b) • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
            simp [smul_smul]
          _ = b • (1 : ℍ[ℝ, Real.sign a, Real.sign b]) := by
            simp [hmulB]
      i_mul_j := by simp
      j_mul_i := by
        -- scaling preserves the `c₂ = 0` anticommutation relation
        simp [qN, mul_comm] }
  let f : ℍ[ℝ, a, b] →ₐ[ℝ] ℍ[ℝ, Real.sign a, Real.sign b] := qT.liftHom

  -- The inverse map scales by `u⁻¹` and `v⁻¹`.
  have hsignA : (u * u)⁻¹ * a = Real.sign a := by
    have hu' : u * u ≠ 0 := mul_ne_zero hu hu
    calc
      (u * u)⁻¹ * a = (u * u)⁻¹ * (u * u * Real.sign a) := by simp [hmulA, mul_assoc]
      _ = ((u * u)⁻¹ * (u * u)) * Real.sign a := by simp [mul_assoc]
      _ = (1 : ℝ) * Real.sign a := by
        rw [inv_mul_cancel₀ hu']
      _ = Real.sign a := by simp
  have hsignB : (v * v)⁻¹ * b = Real.sign b := by
    have hv' : v * v ≠ 0 := mul_ne_zero hv hv
    calc
      (v * v)⁻¹ * b = (v * v)⁻¹ * (v * v * Real.sign b) := by simp [hmulB, mul_assoc]
      _ = ((v * v)⁻¹ * (v * v)) * Real.sign b := by simp [mul_assoc]
      _ = (1 : ℝ) * Real.sign b := by
        rw [inv_mul_cancel₀ hv']
      _ = Real.sign b := by simp

  let qS : QuaternionAlgebra.Basis (ℍ[ℝ, a, b]) (Real.sign a) (0 : ℝ) (Real.sign b) :=
    { i := u⁻¹ • qO.i
      j := v⁻¹ • qO.j
      k := (u⁻¹ • qO.i) * (v⁻¹ • qO.j)
      i_mul_i := by
        have hcalc :
            (u⁻¹ • qO.i) * (u⁻¹ • qO.i) =
              (Real.sign a : ℝ) • (1 : ℍ[ℝ, a, b]) := by
          calc
            (u⁻¹ • qO.i) * (u⁻¹ • qO.i) = (u⁻¹ * u⁻¹) • (qO.i * qO.i) := by
              simp [smul_smul, mul_assoc]
            _ = (u⁻¹ * u⁻¹) • ((a : ℝ) • (1 : ℍ[ℝ, a, b])) := by
              simp [qO.i_mul_i]
            _ = ((u⁻¹ * u⁻¹) * a) • (1 : ℍ[ℝ, a, b]) := by
              simp [smul_smul, mul_assoc]
            _ = (Real.sign a : ℝ) • (1 : ℍ[ℝ, a, b]) := by
              have huInv : u⁻¹ * u⁻¹ = (u * u)⁻¹ := by simp
              have huInv' : (u⁻¹ * u⁻¹) * a = Real.sign a := by
                calc
                  (u⁻¹ * u⁻¹) * a = (u * u)⁻¹ * a := by
                    rw [huInv]
                  _ = Real.sign a := hsignA
              simp [huInv']
        simp [hcalc]
      j_mul_j := by
        have hcalc :
            (v⁻¹ • qO.j) * (v⁻¹ • qO.j) =
              (Real.sign b : ℝ) • (1 : ℍ[ℝ, a, b]) := by
          calc
            (v⁻¹ • qO.j) * (v⁻¹ • qO.j) = (v⁻¹ * v⁻¹) • (qO.j * qO.j) := by
              simp [smul_smul, mul_assoc]
            _ = (v⁻¹ * v⁻¹) • ((b : ℝ) • (1 : ℍ[ℝ, a, b])) := by
              simp [qO.j_mul_j]
            _ = ((v⁻¹ * v⁻¹) * b) • (1 : ℍ[ℝ, a, b]) := by
              simp [smul_smul, mul_assoc]
            _ = (Real.sign b : ℝ) • (1 : ℍ[ℝ, a, b]) := by
              have hvInv : v⁻¹ * v⁻¹ = (v * v)⁻¹ := by simp
              have hvInv' : (v⁻¹ * v⁻¹) * b = Real.sign b := by
                calc
                  (v⁻¹ * v⁻¹) * b = (v * v)⁻¹ * b := by
                    rw [hvInv]
                  _ = Real.sign b := hsignB
              simp [hvInv']
        simp [hcalc]
      i_mul_j := by simp
      j_mul_i := by
        simp [qO, mul_comm, mul_left_comm] }
  let g : ℍ[ℝ, Real.sign a, Real.sign b] →ₐ[ℝ] ℍ[ℝ, a, b] := qS.liftHom

  have hf_i : f qO.i = u • qN.i := by
    simp [f, qT, qN, qO, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift]
  have hf_j : f qO.j = v • qN.j := by
    simp [f, qT, qN, qO, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift]
  have hg_i : g qN.i = u⁻¹ • qO.i := by
    simp [g, qS, qN, qO, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift]
  have hg_j : g qN.j = v⁻¹ • qO.j := by
    simp [g, qS, qN, qO, QuaternionAlgebra.Basis.liftHom, QuaternionAlgebra.Basis.lift]

  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · -- `f ∘ g = id` on the normalized algebra
    apply QuaternionAlgebra.hom_ext (R := ℝ) (A := ℍ[ℝ, Real.sign a, Real.sign b])
    · -- `i`
      simp [AlgHom.comp_apply, AlgHom.id_apply]
      change f (g qN.i) = qN.i
      rw [hg_i]
      calc
        f (u⁻¹ • qO.i) = u⁻¹ • f qO.i := by
          simp
        _ = u⁻¹ • (u • qN.i) := by simp [hf_i]
        _ = (u⁻¹ * u) • qN.i := by simp [smul_smul]
        _ = qN.i := by simp [inv_mul_cancel₀ hu]
    · -- `j`
      simp [AlgHom.comp_apply, AlgHom.id_apply]
      change f (g qN.j) = qN.j
      rw [hg_j]
      calc
        f (v⁻¹ • qO.j) = v⁻¹ • f qO.j := by
          simp
        _ = v⁻¹ • (v • qN.j) := by simp [hf_j]
        _ = (v⁻¹ * v) • qN.j := by simp [smul_smul]
        _ = qN.j := by simp [inv_mul_cancel₀ hv]
  · -- `g ∘ f = id` on the original algebra
    apply QuaternionAlgebra.hom_ext (R := ℝ) (A := ℍ[ℝ, a, b])
    · -- `i`
      simp [AlgHom.comp_apply, AlgHom.id_apply]
      change g (f qO.i) = qO.i
      rw [hf_i]
      calc
        g (u • qN.i) = u • g qN.i := by
          simp
        _ = u • (u⁻¹ • qO.i) := by simp [hg_i]
        _ = (u * u⁻¹) • qO.i := by simp [smul_smul]
        _ = qO.i := by simp [mul_inv_cancel₀ hu]
    · -- `j`
      simp [AlgHom.comp_apply, AlgHom.id_apply]
      change g (f qO.j) = qO.j
      rw [hf_j]
      calc
        g (v • qN.j) = v • g qN.j := by
          simp
        _ = v • (v⁻¹ • qO.j) := by simp [hg_j]
        _ = (v * v⁻¹) • qO.j := by simp [smul_smul]
        _ = qO.j := by simp [mul_inv_cancel₀ hv]

private def quaternionAlgEquivCongr {c₁ c₃ d₁ d₃ : ℝ} (h₁ : c₁ = d₁) (h₃ : c₃ = d₃) :
    ℍ[ℝ, c₁, c₃] ≃ₐ[ℝ] ℍ[ℝ, d₁, d₃] := by
  cases h₁
  cases h₃
  exact AlgEquiv.refl (R := ℝ) (A₁ := ℍ[ℝ, c₁, c₃])

lemma quaternionAlgebra_real_classification (A B : ℚ) (ha : A ≠ 0) (hb : B ≠ 0) :
    Nonempty (ℍ[ℝ, A, B] ≃ₐ[ℝ] ℍ[ℝ, -1, -1]) ∨
      Nonempty (ℍ[ℝ, A, B] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) := by
  classical
  have haR : (A : ℝ) ≠ 0 := by
    intro h
    apply ha
    exact Rat.cast_injective (α := ℝ) (by simpa using h)
  have hbR : (B : ℝ) ≠ 0 := by
    intro h
    apply hb
    exact Rat.cast_injective (α := ℝ) (by simpa using h)
  let e :=
    quaternionAlgEquivNormalize (a := (A : ℝ)) (b := (B : ℝ)) haR hbR
  have hsignA : Real.sign (A : ℝ) = -1 ∨ Real.sign (A : ℝ) = 1 :=
    Real.sign_apply_eq_of_ne_zero (A : ℝ) haR
  have hsignB : Real.sign (B : ℝ) = -1 ∨ Real.sign (B : ℝ) = 1 :=
    Real.sign_apply_eq_of_ne_zero (B : ℝ) hbR
  rcases hsignA with hAneg | hApos <;> rcases hsignB with hBneg | hBpos
  · left
    exact ⟨e.trans (quaternionAlgEquivCongr hAneg hBneg)⟩
  · right
    refine ⟨?_⟩
    have e' : ℍ[ℝ, A, B] ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), (1 : ℝ)] :=
      e.trans (quaternionAlgEquivCongr hAneg hBpos)
    exact
      ((e'.trans (QuaternionAlgebra.swapEquiv (R := ℝ) (c₁ := (-1 : ℝ)) (c₃ := (1 : ℝ)))).trans
        quaternionAlgEquivMatrix1m1)
  · right
    refine ⟨?_⟩
    have e' : ℍ[ℝ, A, B] ≃ₐ[ℝ] ℍ[ℝ, (1 : ℝ), (-1 : ℝ)] :=
      e.trans (quaternionAlgEquivCongr hApos hBneg)
    exact e'.trans quaternionAlgEquivMatrix1m1
  · right
    refine ⟨?_⟩
    have e' : ℍ[ℝ, A, B] ≃ₐ[ℝ] ℍ[ℝ, (1 : ℝ), (1 : ℝ)] :=
      e.trans (quaternionAlgEquivCongr hApos hBpos)
    exact e'.trans quaternionAlgEquivMatrix11

end Classification

/--
Let $A, B \in \mathbb{Q}^\times$ be rational numbers. Consider the quaternion ring
$$
D_{A, B, \mathbb{R}} = \{a+b\boldsymbol{i} +c\boldsymbol{j}+d\boldsymbol{k}\;|\; a,b,c,d \in
\mathbb{R}\}$$
in which the multiplication satisfies relations: $\boldsymbol{i}^2 = A$, $\boldsymbol{j}^ 2 = B$,
and $\boldsymbol{i}\boldsymbol{j}= -\boldsymbol{j}\boldsymbol{i} = \boldsymbol{k}$.
Show that $D_{A, B, \mathbb{R}}$ is either isomorphic to $\mathbb{H}$ (Hamilton quaternion) or
isomorphic to $\mathrm{Mat}_{2\times 2}(\mathbb{R})$ as $\mathbb{R}$-algebras.
-/
theorem quaternionAlgebra_isomorphic_to_matrix_ring_or_quaternion_ring
    (A B : ℚ) (ha : A ≠ 0) (hb : B ≠ 0) :
    ((Nonempty (ℍ[ℝ, A, B] ≃ₐ[ℝ] ℍ[ℝ, -1, -1])) ∨
        (Nonempty (ℍ[ℝ, A, B] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)))
    ∧ IsEmpty (Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] ℍ[ℝ, -1, -1]) := by
  constructor
  · exact quaternionAlgebra_real_classification (A := A) (B := B) ha hb
  · exact no_algEquiv_matrix_hamilton

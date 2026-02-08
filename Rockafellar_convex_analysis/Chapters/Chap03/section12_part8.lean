import Mathlib
import Rockafellar_convex_analysis.Chapters.Chap03.section12_part7

section Chap03
section Section12

/-- Given a linear equivalence `A` and diagonal weights `d`, build a dot-product symmetric linear
map `Q` whose quadratic form is `x ↦ ∑ i, d i * (A x i)^2`. -/
lemma exists_Q_of_linearEquiv_diag {n : Nat} (A : (Fin n → Real) ≃ₗ[ℝ] (Fin n → Real))
    (d : Fin n → Real) :
    ∃ Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real),
      (∀ x y : Fin n → Real, (Q x) ⬝ᵥ y = x ⬝ᵥ Q y) ∧
        ∀ x : Fin n → Real, (x ⬝ᵥ Q x : Real) = ∑ i : Fin n, d i * (A x i) ^ 2 := by
  classical
  let eL : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → Real) := EuclideanSpace.equiv (Fin n) ℝ
  let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → Real) := eL.toLinearEquiv
  -- Transport `A` to a linear equivalence of `EuclideanSpace`.
  let Ae : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (e.trans A).trans e.symm
  -- Diagonal scaling, defined on `Fin n → ℝ` and transported to `EuclideanSpace`.
  let Dv : (Fin n → Real) →ₗ[ℝ] (Fin n → Real) :=
    { toFun := fun y i => d i * y i
      map_add' := by
        intro x y
        ext i
        simp [mul_add]
      map_smul' := by
        intro r x
        ext i
        simp [smul_eq_mul]
        ring }
  let D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    eL.symm.toLinearMap ∘ₗ Dv ∘ₗ eL.toLinearMap
  -- The self-adjoint operator `Ae† D Ae` on `EuclideanSpace`.
  let Qe : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearMap.adjoint Ae.toLinearMap) ∘ₗ D ∘ₗ Ae.toLinearMap
  -- Translate back to the dot-product world.
  let Q : (Fin n → Real) →ₗ[ℝ] (Fin n → Real) :=
    e.toLinearMap ∘ₗ Qe ∘ₗ e.symm.toLinearMap
  refine ⟨Q, ?_, ?_⟩
  · intro x y
    -- Prove dot-product symmetry by transporting to `EuclideanSpace` and using symmetry of `Qe`.
    have hInnerDot :
        ∀ u v : EuclideanSpace ℝ (Fin n), inner ℝ u v = (eL u ⬝ᵥ eL v : Real) := by
      intro u v
      have h := dotProduct_eq_inner_euclideanSpace (n := n) (x := eL u) (y := eL v)
      simpa [eL] using h.symm
    have hDsymm :
        ∀ u v : EuclideanSpace ℝ (Fin n), inner ℝ (D u) v = inner ℝ u (D v) := by
      intro u v
      -- Reduce to a dot-product computation on `Fin n → ℝ`.
      have hDv_symm : ∀ a b : Fin n → Real, (Dv a) ⬝ᵥ b = a ⬝ᵥ (Dv b) := by
        intro a b
        simp [Dv, dotProduct, mul_left_comm, mul_comm]
      -- Transport through the `eL` bridge.
      -- `inner u v = (eL u) ⬝ᵥ (eL v)` by `dotProduct_eq_inner_euclideanSpace`.
      have huv : inner ℝ (D u) v = ((Dv (eL u)) ⬝ᵥ (eL v) : Real) := by
        have : inner ℝ (D u) v = (eL (D u) ⬝ᵥ eL v : Real) := by
          simp [hInnerDot]
        -- `eL (D u) = Dv (eL u)` by definition of `D`.
        simpa [D, Dv, LinearMap.comp_apply, eL, e] using this
      have huv' : inner ℝ u (D v) = ((eL u) ⬝ᵥ (Dv (eL v)) : Real) := by
        have : inner ℝ u (D v) = (eL u ⬝ᵥ eL (D v) : Real) := by
          simp [hInnerDot]
        simpa [D, Dv, LinearMap.comp_apply, eL, e] using this
      -- Conclude using the symmetry of `Dv` with respect to `dotProduct`.
      simpa [huv, huv'] using hDv_symm (eL u) (eL v)
    have hQe_symm :
        ∀ u v : EuclideanSpace ℝ (Fin n), inner ℝ (Qe u) v = inner ℝ u (Qe v) := by
      intro u v
      -- Expand `Qe` and use the defining properties of the adjoint and symmetry of `D`.
      have h1 :
          inner ℝ (Qe u) v = inner ℝ (D (Ae u)) (Ae v) := by
        -- `⟪Ae† (D (Ae u)), v⟫ = ⟪D (Ae u), Ae v⟫`.
        simpa [Qe, LinearMap.comp_apply] using
          (LinearMap.adjoint_inner_left (A := Ae.toLinearMap) (x := v) (y := D (Ae u)))
      have h2 :
          inner ℝ u (Qe v) = inner ℝ (Ae u) (D (Ae v)) := by
        -- `⟪u, Ae† (D (Ae v))⟫ = ⟪Ae u, D (Ae v)⟫`.
        simpa [Qe, LinearMap.comp_apply] using
          (LinearMap.adjoint_inner_right (A := Ae.toLinearMap) (x := u) (y := D (Ae v)))
      -- Use symmetry of `D` to swap.
      rw [h1, h2, hDsymm]
    -- Convert the dot products on `Fin n → ℝ` to inner products and apply `hQe_symm`.
    have hx :
        ((Q x) ⬝ᵥ y : Real) = inner ℝ (eL.symm (Q x)) (eL.symm y) := by
      simpa using dotProduct_eq_inner_euclideanSpace (n := n) (x := Q x) (y := y)
    have hy :
        (x ⬝ᵥ Q y : Real) = inner ℝ (eL.symm x) (eL.symm (Q y)) := by
      simpa using dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := Q y)
    -- `eL.symm (Q x) = Qe (eL.symm x)` and similarly for `y`.
    have hcancel1 : eL.symm (Q x) = Qe (eL.symm x) := by
      simp [Q, Qe, eL, e, LinearMap.comp_apply]
    have hcancel2 : eL.symm (Q y) = Qe (eL.symm y) := by
      simp [Q, Qe, eL, e, LinearMap.comp_apply]
    rw [hx, hy, hcancel1, hcancel2, hQe_symm]
  · intro x
    -- Work on `EuclideanSpace`, then translate back to dot products.
    have hInnerDot :
        ∀ u v : EuclideanSpace ℝ (Fin n), inner ℝ u v = (eL u ⬝ᵥ eL v : Real) := by
      intro u v
      have h := dotProduct_eq_inner_euclideanSpace (n := n) (x := eL u) (y := eL v)
      simpa [eL] using h.symm
    have hquad :
        (x ⬝ᵥ Q x : Real) = inner ℝ (eL.symm x) (Qe (eL.symm x)) := by
      have h := dotProduct_eq_inner_euclideanSpace (n := n) (x := x) (y := Q x)
      simpa [Q, Qe, eL, e, LinearMap.comp_apply] using h
    -- Compute the inner product `⟪u, Ae† D Ae u⟫ = ⟪Ae u, D (Ae u)⟫`.
    have hinner :
        inner ℝ (eL.symm x) (Qe (eL.symm x)) =
          inner ℝ (Ae (eL.symm x)) (D (Ae (eL.symm x))) := by
      simpa [Qe, LinearMap.comp_apply] using
        (LinearMap.adjoint_inner_right (A := Ae.toLinearMap) (x := eL.symm x)
          (y := D (Ae (eL.symm x))))
    -- Expand as a dot product in coordinates.
    have hcoords :
        inner ℝ (Ae (eL.symm x)) (D (Ae (eL.symm x))) =
          ∑ i : Fin n, d i * (A x i) ^ 2 := by
      -- `inner` on `EuclideanSpace` is a dot product of the underlying coordinate functions.
      have hdot :
          inner ℝ (Ae (eL.symm x)) (D (Ae (eL.symm x))) =
            (eL (Ae (eL.symm x)) ⬝ᵥ eL (D (Ae (eL.symm x))) : Real) := by
        simp [hInnerDot]
      -- Simplify `eL (Ae (eL.symm x))` and expand the dot product.
      have hAe_eval : Ae (eL.symm x) = eL.symm (A x) := by
        simp [Ae, e, LinearEquiv.trans_apply]
      have hA_eval : eL (Ae (eL.symm x)) = A x := by
        simp [hAe_eval]
      have hD_eval : eL (D (Ae (eL.symm x))) = fun i => d i * (A x i) := by
        -- Transport through the definition of `D`.
        have : eL (D (Ae (eL.symm x))) = Dv (eL (Ae (eL.symm x))) := by
          -- `D = eL.symm ∘ Dv ∘ eL`.
          simp [D, LinearMap.comp_apply]
        -- Now expand `Dv` and use `hA_eval`.
        simpa [Dv, hA_eval]
      -- Finish.
      simp [hdot, hA_eval, hD_eval, dotProduct, mul_left_comm, pow_two]
    -- Put everything together.
    simpa [hquad, hinner] using hcoords
end Section12
end Chap03

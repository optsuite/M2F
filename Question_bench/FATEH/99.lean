import Mathlib

-- For `A` in the special orthogonal group, `det (1 - A) = det (A - 1)`.
lemma det_one_sub_eq_det_sub_one_of_SO {R : Type} [CommRing R] (n : ℕ)
    (A : Matrix.specialOrthogonalGroup (Fin (2 * n + 1)) R) :
    (1 - A.1).det = (A.1 - 1).det := by
  classical
  have hA : A.1 ∈ Matrix.orthogonalGroup (Fin (2 * n + 1)) R :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  have hdet : (A.1).det = 1 := (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).2
  have horth : Matrix.transpose A.1 * A.1 = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (A := A.1)).1 hA
  calc
    (1 - A.1).det = (Matrix.transpose (1 - A.1)).det := by
      exact (Matrix.det_transpose (1 - A.1)).symm
    _ = (1 - Matrix.transpose A.1).det := by
      simp [Matrix.transpose_sub]
    _ = (Matrix.transpose A.1 * (A.1 - 1)).det := by
      have hrewrite : (1 - Matrix.transpose A.1) = Matrix.transpose A.1 * (A.1 - 1) := by
        calc
          1 - Matrix.transpose A.1
              = Matrix.transpose A.1 * A.1 - Matrix.transpose A.1 := by
                  simp [horth]
          _ = Matrix.transpose A.1 * (A.1 - 1) := by
                  symm
                  simp [mul_sub]
      simp [hrewrite]
    _ = (Matrix.transpose A.1).det * (A.1 - 1).det := by
      simp
    _ = (A.1).det * (A.1 - 1).det := by
      simp
    _ = (A.1 - 1).det := by
      simp [hdet]

-- For odd size, `det (M - 1) = - det (1 - M)`.
lemma det_sub_one_eq_neg_det_one_sub_odd {R : Type} [CommRing R] (n : ℕ)
    (M : Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) R) :
    (M - 1).det = - (1 - M).det := by
  classical
  have hodd : Odd (2 * n + 1) := by
    simp
  have hneg : (-1 : R) ^ (2 * n + 1) = -1 := by
    simpa using (hodd.neg_one_pow : (-1 : R) ^ (2 * n + 1) = -1)
  have hrewrite : M - 1 = -(1 - M) := by
    ext i j
    simp
  calc
    (M - 1).det = (-(1 - M)).det := by
      exact congrArg Matrix.det hrewrite
    _ = (-1 : R) ^ Fintype.card (Fin (2 * n + 1)) * (1 - M).det := by
      exact Matrix.det_neg (1 - M)
    _ = (-1 : R) ^ (2 * n + 1) * (1 - M).det := by
      simp [Fintype.card_fin]
    _ = - (1 - M).det := by
      simp [hneg]

-- If `2` is invertible and `x = -x`, then `x = 0`.
lemma eq_zero_of_eq_neg_with_unit_two {R : Type} [CommRing R] (h2 : IsUnit (2 : R))
    {x : R} (hx : x = -x) : x = 0 := by
  have hx' : x + x = 0 := by
    have hx' : x + x = x + -x := by
      simpa using congrArg (fun y => x + y) hx
    calc
      x + x = x + -x := hx'
      _ = 0 := by simp
  have hx'' : (2 : R) * x = 0 := by
    simpa [two_mul] using hx'
  have hx''' : (2 : R) * x = (2 : R) * 0 := by
    simpa using hx''
  exact (IsUnit.mul_right_inj h2).1 hx'''

/--
For a commutative ring \(R\) and \(n \in \mathbb{N}\) such that \(2\) is invertible in \(R\).
If \(A \in SO(2n + 1,  R)\), then \(det(I - A) = 0\).-/
theorem determinant_eq_zero (R : Type) [CommRing R] (n : ℕ) (h2_inv : IsUnit (2 : R))
    (A : Matrix.specialOrthogonalGroup (Fin (2 * n + 1)) R) : (1 - A.1).det = 0 := by
  have hdet : (1 - A.1).det = (A.1 - 1).det :=
    det_one_sub_eq_det_sub_one_of_SO n A
  have hneg : (A.1 - 1).det = - (1 - A.1).det :=
    det_sub_one_eq_neg_det_one_sub_odd n A.1
  have hx : (1 - A.1).det = - (1 - A.1).det := by
    calc
      (1 - A.1).det = (A.1 - 1).det := hdet
      _ = - (1 - A.1).det := hneg
  exact eq_zero_of_eq_neg_with_unit_two h2_inv hx

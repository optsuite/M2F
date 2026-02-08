import Mathlib

/--
For a commutative ring \( A \), \( dim A[x, y] + dim A \le 2 * dim A[x]\).
-/
theorem dimension_convex (A : Type) [CommRing A] :
    ringKrullDim (MvPolynomial A (Fin 2)) + ringKrullDim A ≤ 2 * ringKrullDim (Polynomial A) := by
  sorry

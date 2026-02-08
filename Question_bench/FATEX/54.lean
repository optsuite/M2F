import Mathlib

/--
Let \( A \) be a $\mathbb{Q}$-algebra.
Suppose that \( x \in A \) and \( D \in \operatorname{Der}(A) \) are such that \( Dx = 1 \) and \( \bigcap_{n=1}^{\infty} x^n A = (0) \).
Show that \( x \) is a non-zero-divisor of \( A \).
-/
theorem not_zero_divisor_of_hausdorff_of_der_eq_one (A : Type) [CommRing A] [Algebra ℚ A]
    (x : A) (D : Derivation ℤ A A) (h_dx : D x = 1) (h_hausdorff : IsHausdorff (Ideal.span {x}) A) :
    x ∈ nonZeroDivisors A := by
  sorry

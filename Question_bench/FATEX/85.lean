import Mathlib

/--
Definition of a Euclidean norm taking value in \(\mathbb{N}\).
-/
class EuclideanNormNat (R : Type) [CommRing R] extends Nontrivial R where
  quotient : R → R → R
  quotient_zero : ∀ a, quotient a 0 = 0
  remainder : R → R → R
  quotient_mul_add_remainder_eq : ∀ a b, b * quotient a b + remainder a b = a
  norm : R → ℕ
  remainder_lt : ∀ (a) {b}, b ≠ 0 → norm (remainder a b) < norm b
  mul_left_not_lt : ∀ (a) {b}, b ≠ 0 → ¬ norm (a * b) < norm a

/--
There exists a transfinite Euclidean domain such that it cannot be given a Euclidean norm taking value in \(\mathbb{N}\).-/
theorem exist_euclideanDomain_not_norm_nat :
    ∃ (R : Type) (_ : EuclideanDomain R), IsEmpty (EuclideanNormNat R) := by
  sorry

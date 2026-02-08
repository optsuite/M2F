import Mathlib

open CategoryTheory MvPolynomial

/-- The Picard group of a commutative ring R consists of the invertible R-modules,
  up to isomorphism. -/
abbrev CommRing.Pic (R : Type) [CommRing R] : Type 1 := (Skeleton <| ModuleCat.{0} R)ˣ

/--
Let $ k $ be a field, $ A := k[x, y]/(xy(x + y - 1)) $, then $ \mathrm{Pic}\ A \cong k^{\times} $.
-/
theorem pic_three_lines {k : Type} [Field k] : Nonempty <|
    CommRing.Pic (MvPolynomial (Fin 2) k ⧸ Ideal.span ({(X 0) * (X 1) * (X 0 + X 1 - 1)} :
    Set (MvPolynomial (Fin 2) k))) ≃* kˣ := by
  sorry

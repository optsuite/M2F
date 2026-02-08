import Mathlib

/--
The ring $R = \mathbb{C}[x, y, z] / (x^2 + y^3 + z^7)$.
-/
abbrev R : Type := (MvPolynomial (Fin 3) ℂ) ⧸ Ideal.span {(.X 0 ^ 2 + .X 1 ^ 3 + .X 2 ^ 7 : MvPolynomial (Fin 3) ℂ)}

/--
$\mathbb{C}[x, y, z] / (x^2 + y^3 + z^7)$ is a UFD.
-/
theorem quotient_not_UFD :
    ∃ (h : IsDomain R),
    (UniqueFactorizationMonoid R) := by
  sorry

import Mathlib

/--
Let $R$ be a ring, \( \mathfrak{m} \) is an ideal in the Jacobson radical of \( R \),
and \( G_{1}, G_{2} \in R[x] \) are polynomials such that $G_1$ is monic.
If $G_i \mod \mathfrak{m}$ gnerate the unit ideal of $R/\mathfrak{m}[x]$,
then \( G_{1}, G_{2} \) together generate the unit ideal of \( R[x] \).
-/
theorem generate_unit_ideal_of_quotient (R : Type) [CommRing R] (m : Ideal R)
    (h_le_jac : m ≤ Ring.jacobson R) (G₁ G₂ : Polynomial R) (h_monic : G₁.Monic)
    (h_gen : Ideal.span {G₁.map (Ideal.Quotient.mk m), G₂.map (Ideal.Quotient.mk m)} = ⊤) :
    Ideal.span {G₁, G₂} = ⊤ := by
  sorry

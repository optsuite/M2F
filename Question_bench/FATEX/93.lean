import Mathlib

/--
There exists a field $k$ and a (not necessarily commutative) ring $A$
such that $A$ is integral and finitely generated over $k$ but $\dim_k A$ is not finite.
-/
theorem exists_integral_finiteType_not_finiteDimensional : ∃ (k A : Type) (_ : Field k)
    (_ : Ring A) (_ : Algebra k A),
    Algebra.IsIntegral k A ∧ Algebra.FiniteType k A ∧ ¬ FiniteDimensional k A := by
  sorry

import Mathlib

/--
Given a field $k$, there exists some $n > 0$, there exists some subfield $K \subseteq k(x_1, \cdots ,x_n) $,
such that $K \cap k [X_1, \cdots, x_n]$ is not a finitely generated $k$-algebra.
-/
theorem not_finiteType_inf_algebraMap_range (k : Type) [Field k] :
    ∃ (n : ℕ) (K : IntermediateField k (FractionRing (MvPolynomial (Fin n) k))),
    ¬ Algebra.FiniteType k (K.toSubalgebra ⊓ (Algebra.algHom k (MvPolynomial (Fin n) k)
    (FractionRing (MvPolynomial (Fin n) k))).range :
    Subalgebra k (FractionRing (MvPolynomial (Fin n) k))) := by
  sorry

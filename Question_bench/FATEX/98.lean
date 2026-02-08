import Mathlib

/--
If $K$ be a number field, $A$ be a finite-type $K$-algebra, $f : A \to A$ be an endomorphism.
If $A$ is a domain and $f$ is not of finite order, then there exists a maximal ideal $m \subset A$
such that for all $n \in \mathbb{N}_+$, $f^{-n}(m) \ne m$.
-/
theorem exists_maximal_ideal_not_in_finite_order {K A : Type} [Field K] [NumberField K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] {f : A →ₐ[K] A} (hf : ∀ n > 0, f ^ n ≠ 1) :
    ∃ m : Ideal A, m.IsMaximal ∧ ∀ n > 0, m.comap (f ^ n) ≠ m := by
  sorry

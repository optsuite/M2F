import Mathlib

/--
Let $A$ be a finite-type $\mathbb{C}$-algebra, $n \in \mathbb{N}$, $n \ge 1$. If $A$ is a domain,
and $\mathrm{Aut}_\mathbb{C}\ A$ is isomorphic to $\mathrm{Aut}_\mathbb{C}\ \mathbb{C}[x_1, \dots, x_n]$,
then $A$ is isomorphic to $\mathbb{C}[x_1, \dots, x_n]$ as $\mathbb{C}$-algebras.
-/
theorem equiv_of_aut_equiv {A : Type} [CommRing A] [IsDomain A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] {n : ℕ} (hn : n ≥ 1)
    (e : (A ≃ₐ[ℂ] A) ≃* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)) :
    Nonempty (A ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ) := by
  sorry

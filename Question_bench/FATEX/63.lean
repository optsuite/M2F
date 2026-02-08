import Mathlib

/--
The universal property:
Given any commutative diagram
\[
\begin{tikzcd}
S \arrow[r, "a"] & A/I \\
R \arrow[u] \arrow[r, "b"] & A \arrow[u]
\end{tikzcd}
\]
where \( I \subset A \) is an ideal of square zero, there is a unique \( R \)-algebra map \( \alpha': S' \to A \) such that \( S' \to A \to A/I \) is equal to \( S' \to S \to A/I \).
-/
def UniversalProperty.liftOfSqZeroIdeal {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra R S'] (f : S' →ₐ[R] S) :=
  ∀ (A : Type) [CommRing A] [Algebra R A] (I : Ideal A) (g : S →ₐ[R] A⧸I),
  I^2 = 0 → (g.toRingHom.comp (algebraMap R S) = (Ideal.Quotient.mk I).comp (algebraMap R A)) →
  ∃! (g' : S' →ₐ[R] A), (Ideal.Quotient.mk I).comp g'.toRingHom  = g.comp f

/--
Let \( R \to S \) be a formally unramified ring map. Show there exists a surjection of \( R \)-algebras \( S' \to S \) whose kernel is an ideal of square zero with the following universal property:
Given any commutative diagram
\[
\begin{tikzcd}
S \arrow[r, "a"] & A/I \\
R \arrow[u] \arrow[r, "b"] & A \arrow[u]
\end{tikzcd}
\]
where \( I \subset A \) is an ideal of square zero, there is a unique \( R \)-algebra map \( \alpha': S' \to A \) such that \( S' \to A \to A/I \) is equal to \( S' \to S \to A/I \).
-/
theorem surjection_of_formally_unramified (R S : Type) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FormallyUnramified R S] :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra R S') (f : S' →ₐ[R] S), (RingHom.ker f) ^ 2 = 0 ∧ UniversalProperty.liftOfSqZeroIdeal f := by
  sorry

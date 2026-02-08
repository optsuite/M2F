import Mathlib

/--
Let \( R \to S \) be a ring map. Let \( I \subset R \) be an ideal. Assume
\begin{enumerate}
    \item \( I^{2} = 0 \),
    \item \( R \to S \) is flat, and
    \item \( R/I \to S/IS \) is formally smooth.
\end{enumerate}
Show \( R \to S \) is formally smooth.
-/
theorem formallySmooth_of_formallySmooth_quotient (R S : Type) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] (I : Ideal R) (h : I ^ 2 = 0)
    [Algebra.FormallySmooth (R ⧸ I) (S ⧸ (I.map (algebraMap R S)))] :
    Algebra.FormallySmooth R S := by
  sorry

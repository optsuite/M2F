import Mathlib

/--
A Noetherian topological ring in which the topology is defined by an ideal contained in the Jacobson radical is called a \textit{Zariski ring}.
Let \( A \) be a Noetherian ring, \( \mathfrak{a} \) an ideal of \( A \), and \( \widehat{A} \) the \( \mathfrak{a} \)-adic completion of $A$.
Prove that \( \widehat{A} \) is faithfully flat over \( A \) if and only if \( A \) is a Zariski ring for the \( \mathfrak{a} \)-topology.
-/
theorem adicCompletion_faithfullyFlat_iff (A : Type) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) : Module.FaithfullyFlat A (AdicCompletion I A) ↔ I ≤ Ring.jacobson A := by
  sorry

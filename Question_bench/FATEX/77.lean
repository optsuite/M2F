import Mathlib

/--
Let $A$ be a Noetherian ring, $P \subset Q$ prime ideals such that
$\operatorname{ht} P = h$, $\operatorname{ht} Q/P = d$, where $d > 1$.
Prove that there exist infinitely many intermediate primes $P'$, $P \subset P' \subset Q$
such that $\operatorname{ht} P' = h + 1$ and $\operatorname{ht} Q/P' = d - 1$.
-/
theorem infinite_intermediate_primes (R : Type) [CommRing R] (P Q : Ideal R) (le : P ≤ Q)
    [P.IsPrime] [Q.IsPrime] (h d : ℕ) (lt : 1 < d) (ht1 : P.height = h)
    (ht2 : (Q.map (Ideal.Quotient.mk P)).height = d) :
    {P' : Ideal R | P ≤ P' ∧ P' ≤ Q ∧ P'.IsPrime ∧ P'.height = h + 1 ∧
      (Q.map (Ideal.Quotient.mk P')).height = d - 1}.Infinite := by
  sorry

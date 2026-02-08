import Mathlib

/--
For a Noetherian domain \( R \), we say that an ideal \( I \subset R \) is invertible if
it is it not the zero ideal and there exists an ideal \( N \) such that \( N \cdot I \) is principal
and \( N \) is not the zero ideal.
-/
def Ideal.Invertible {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) : Prop :=
    I ≠ ⊥ ∧ ∃ (N : Ideal R), (N * I).IsPrincipal ∧ N ≠ ⊥

/--
Let $R$ be a Noetherian domain, and suppose that for every maximal ideal $P$ of $R$ the ring $R_P$ is factorial.
Let $I \subset R$ be an ideal. Prove that $I$ is an invertible module iff $I$ has pure codimension $1$.
(We say that an ideal $I$ in a ring $R$ has pure codimension $1$ if every associated prime ideal of $I$ has codimension $1$. We include the case when $I$ has no associated primes at all---that is, when $I = R$.)
-/
theorem invertible_iff_codimension_one (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h_ufd : ∀ (p : Ideal R), (h : p.IsMaximal) → UniqueFactorizationMonoid (Localization.AtPrime p))
    (I : Ideal R) : I.Invertible ↔ ∀ (p : associatedPrimes R I), ringKrullDim (R ⧸ p.1) = 1 := by
  sorry

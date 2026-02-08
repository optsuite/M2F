import Mathlib

open List

/-- A ring $R$ is said to be \textit{catenary} if for any pair of prime ideals $\mathfrak{p} \subset
  \mathfrak{q}$, there exists an integer bounding the lengths of all finite chains of prime ideals
  $\mathfrak{p} = \mathfrak{p}_0 \subset \mathfrak{p}_1 \subset \dots \subset \mathfrak{p}_e =
  \mathfrak{q}$ and all maximal such chains have the same length. -/
def IsCatenary (R : Type) [CommRing R] : Prop :=
  ∀ p q : PrimeSpectrum R, p ≤ q →
  ∃ n : ℕ, ∀ (l : LTSeries (PrimeSpectrum R)), l.head = p → l.last = q →
  (∀ l' : LTSeries (PrimeSpectrum R), l'.head = p → l'.last = q → l.toList <+ l'.toList → l' = l) →
  l.toList.length = n

/--
Let $A$ be a Noetherian UFD of dimension $d \leq 3$. Prove that $A$ is catenary.
-/
theorem IsCatenary.of_noetherian_ufd_of_dim_le_three {A : Type} [CommRing A] [IsNoetherianRing A]
    [IsDomain A] [UniqueFactorizationMonoid A] (h : ringKrullDim A ≤ 3) : IsCatenary A := by
  sorry

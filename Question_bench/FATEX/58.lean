import Mathlib

open TensorProduct

/--
Suppose that $(R, \mathfrak{P})$ is a local Noetherian ring,
and let $(S, \mathfrak{Q})$ be a local Noetherian $R$-algebra such that $\mathfrak{P}S \subseteq \mathfrak{Q}$.
If $M$ is a finitely generated $S$-module, show that $M$ is flat as an $R$-module
if $M / \mathfrak{P}^n M$ is flat as an $R / \mathfrak{P}^n$-module for every $n$.-/
theorem flat_of_flat_over_quotient (R S : Type) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] [IsNoetherianRing R] [IsNoetherianRing S] [Algebra R S]
    (h_map : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≤ IsLocalRing.maximalIdeal S)
    (M : Type) [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M] [Module.Finite S M]
    (h_flat_quotient : ∀ (n : ℕ), Module.Flat (R ⧸ (IsLocalRing.maximalIdeal R) ^ n) ((R ⧸ (IsLocalRing.maximalIdeal R) ^ n) ⊗[R] M)) :
    Module.Flat R M := by
  sorry

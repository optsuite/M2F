import Mathlib

open TensorProduct

/--
Let $A$ be a reduced local ring with residue field $k$ and finite set $\Sigma$ of minimal primes.
For each $\mathfrak{p}\in\Sigma$, set $K(\mathfrak{p})=\mathrm{Frac}(A/\mathfrak{p})$.
Let $P$ be a finitely generated module. Show that $P$ is free of rank $r$ if and only if
$\dim_k(P\otimes_A k) = r$ and $\dim_{K(\mathfrak{p})}(P\otimes_A K(\mathfrak{p})) = r$ for each $\mathfrak{p}\in\Sigma$.-/
theorem free_of_rank_iff (R : Type) [CommRing R] [IsLocalRing R] [IsReduced R]
    (h : (minimalPrimes R).Finite) (r : ℕ) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Free R M ∧ Module.rank R M = r ↔
    (Module.rank (IsLocalRing.ResidueField R) ((IsLocalRing.ResidueField R) ⊗[R] M) = r ∧
    ∀ p ∈ minimalPrimes R,
    Module.rank (FractionRing (R ⧸ p)) ((FractionRing (R ⧸ p)) ⊗[R] M) = r) := by
  sorry

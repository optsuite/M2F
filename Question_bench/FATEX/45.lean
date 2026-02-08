import Mathlib

/--
A linear map `f` between graded modules is a graded homomorphism if it respects the
grading structure.
-/
def IsGradedHom {R M N ι : Type} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (𝓜 : ι → Submodule R M) (𝒩 : ι → Submodule R N)
    (f : M →ₗ[R] N) : Prop := ∀ (i : ι) (x : 𝓜 i), f x ∈ 𝒩 i

/--
Let $k$ be a field and $A = k[x_1, \dots, x_r]$ the polynomial ring in $r$ variables. Let $M$ be a graded module over $A$, and let
\[
0 \to K \to L_{r-1} \to \cdots \to L_0 \to M \to 0
\]
be an exact sequence of graded homomorphisms of graded modules, such that $L_0, \dots, L_{r-1}$ are free. Then $K$ is free. {Gradings of modules are by $\mathbb{Z}_{\geq 0}$.}
-/
theorem free_of_free_resolution {k : Type} [Field k] {r : ℕ}
    (C : ChainComplex (ModuleCat.{0} (MvPolynomial (Fin r) k)) ℕ)
    (hC : ∀ (n : ℕ), n > (r + 1) → CategoryTheory.Limits.IsZero (C.X n))
    (𝓜 : ∀ (n : ℕ), (ℕ → Submodule (MvPolynomial (Fin r) k) (C.X n)))
    [hM : ∀ (n : ℕ), DirectSum.Decomposition (𝓜 n)]
    [hM' : ∀ (n : ℕ), SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule (Fin r) k) (𝓜 n)]
    (h_exact : C.Acyclic)
    (h_gr : ∀ (i j : ℕ), IsGradedHom (𝓜 i) (𝓜 j) (C.d i j).hom)
    (h_free : ∀ (n : ℕ), 1 ≤ n ∧ n ≤ r → Module.Free (MvPolynomial (Fin r) k) (C.X n)) :
    Module.Free (MvPolynomial (Fin r) k) (C.X (r + 1)) := by
  sorry

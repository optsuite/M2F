import Mathlib

variable {k A : Type} [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A] (f : A →ₐ[k] A) (ϕ : A →ₐ[k] k) (I : Ideal A)

/-- The set $\{ n \in \mathbb{N} \mid \left. \varphi \circ f^n \right|_I = 0 \right\rbrace \}$. -/
def zeroSet : Set ℕ := {n | ∀ x : I, (ϕ.comp (f ^ n)) (x : A) = 0}

/--
Let $k$ be field, $\mathrm{char}\ k=0$, $ A $ be a finite-type $k$-algebra, $f: A \to A$ be an \'etale endomorphsim, $\varphi: A \to k$, $I \subset A$ be a ideal.
If $A$ is a domain, then $$\left\lbrace  n \in \mathbb{N} \mid \left. \varphi \circ f^n \right|_I = 0 \right\rbrace $$ is either finite or contains an arithmetic progression with a positive common difference. -/
theorem zeroSet_finite_or_contain_arithmetic_progression (hf : f.FormallyEtale) :
    (zeroSet f ϕ I).Finite ∨ ∃ (d : ℕ+) (a : ℕ), ∀ n : ℕ, a + d * n ∈ zeroSet f ϕ I := by
  sorry

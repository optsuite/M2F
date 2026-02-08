import Mathlib

open Module

/--
Let $R$ be a Noetherian ring, $P$ be a countably generated projective $R$-module
such that $P_{\mathfrak{m}}$ has infinite rank for all maximal ideals $\mathfrak{m}$ of $R$.
Then $P$ is free.
-/
theorem free_of_countably_generated_projective_of_local_infinite_rank {R : Type} [CommRing R]
    [IsNoetherianRing R] (P : Type) [AddCommGroup P] [Module R P] [Projective R P]
    (hcg : ∃ s : Set P, s.Countable ∧ Submodule.span R s = ⊤)
    (hm : ∀ m : Ideal R, (_ : m.IsMaximal) →
      ¬ Module.Finite (Localization.AtPrime m) (LocalizedModule.AtPrime m P)) : Free R P := by
  sorry

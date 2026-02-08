import Mathlib

open Polynomial
/--Let $K$ be a finite extension of a field $F$, and let $f(x) \in K[x]$. Prove that there exists a
nonzero polynomial $g(x) \in K[x]$ such that $f(x)g(x) \in F[x]$.-/
theorem exists_mul_eq_map_algebraMap {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
    (f : K[X]) : ∃ g ≠ 0, ∃ h : F[X], f * g = h.map (algebraMap F K) := by
  by_cases hf : f = 0
  · refine ⟨1, one_ne_zero, 0, ?_⟩
    simp [hf]
  ·
    haveI : Algebra.IsAlgebraic F K := by infer_instance
    obtain ⟨gF, gF_ne, hgF⟩ :=
      Polynomial.exists_dvd_map_of_isAlgebraic (R:=F) (S:=K) (f:=f) hf
    rcases hgF with ⟨gK, hgK_eq⟩
    have hmap_ne : gF.map (algebraMap F K) ≠ 0 :=
      Polynomial.map_ne_zero (p:=gF) (f:=algebraMap F K) gF_ne
    have gK_ne : gK ≠ 0 := by
      intro hgK0
      apply hmap_ne
      simpa [hgK0] using hgK_eq
    refine ⟨gK, gK_ne, gF, hgK_eq.symm⟩

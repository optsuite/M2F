import Mathlib

open scoped Polynomial

/--
If $k$ is a field of characteristic zero, $n \in \mathbb{N}$, $n \ne 0$,
and $\phi \colon k[x_1, \dots, x_n] \to k[x_1, \dots, x_n]$ is given by $(x_1, \dots, x_n) \mapsto (f_1(x_1), \dots, f_n(x_n))$,
where $f_i(x_i) \in k[x_i]$ having degree at least two, then there is a point $a \in k^n$
such that for any non-zero polyminal $p \in k[x_1, \dots, x_n]$,
there exists $m \in \mathbb{N}$ such that $p(\phi^m(a)) \ne 0$. -/
theorem exists_point_not_in_zero_set {τ k : Type} [Finite τ] [Nonempty τ] [Field k] [CharZero k]
    {f : τ → k[X]} (hfd : ∀ i : τ, (f i).natDegree ≥ 2): ∃ a : τ → k,
    ∀ p : MvPolynomial τ k, p ≠ 0 →
    ∃ m : ℕ, (((MvPolynomial.aeval (fun i ↦ (f i).toMvPolynomial i)) ^ m) p).aeval a ≠ 0 := by
  sorry

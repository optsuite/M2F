import Mathlib

/--
The ring \(A = k[x,y]/(y^{2} - f(x))\),
where \(k\) is a field and \(f(x) = (x - t_{1})\ldots(x - t_{n})\).
-/
abbrev A {k : Type} [Field k] {n : ℕ} (t : (Fin n) → k) : Type := (MvPolynomial (Fin 2) k) ⧸ Ideal.span {(.X 1 ^ 2) - ∏ (m : Fin n), (.X 0 - .C (t m) : (MvPolynomial (Fin 2) k))}


/--
Show that the ring \(A = k[x,y]/(y^{2} - f(x))\) is a Dedekind domain and the class group of the ring \(A\) is not trivial,
where \(k\) is a field of characteristic not 2, \(f(x) = (x - t_{1})\ldots(x - t_{n})\)
with \(t_{1},\ldots,t_{n} \in k\) distinct and \(n \geq 3\) is an odd integer.-/
theorem isEmpty_isomorphism_UFD_of_quotient (k : Type) [Field k] (h_char : ¬ CharP k 2)
    (n : ℕ) (h_ge : n ≥ 3) (h_odd : Odd n) (t : (Fin n) → k) (h_inj : Function.Injective t) :
    ∃ _ : IsDedekindDomain (A t), Nontrivial (ClassGroup (A t)) := by
  sorry

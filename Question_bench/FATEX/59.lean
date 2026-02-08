import Mathlib

/--
Let \( k \) be a field, \( X \) and \( Y \) indeterminates, and suppose that \( \alpha \) is a positive irrational number.
Show the map \( v: k[X, Y] \rightarrow \mathbb{R} \cup \{\infty\} \) defined by
\[
v\left(\sum c_{n,m} X^n Y^m\right) = \min\{n + m\alpha \mid c_{n,m} \neq 0\}
\]
determines a valuation of \( k(X, Y) \) with value group \( \mathbb{Z} + \mathbb{Z}\alpha \).
-/
theorem exists_unique_valuation_eq (α : ℝ) (h_pos : α > 0) (h_irr : Irrational α)
    (k : Type) [Field k] : ∃! (v : AddValuation (FractionRing (MvPolynomial (Fin 2) k)) (WithTop ℝ)),
    ∀ (f : MvPolynomial (Fin 2) k), v (algebraMap _ _ f) = Finset.inf (Finset.image (fun s ↦ ((s 0 + α * s 1) : WithTop ℝ)) f.support) id := by
  sorry

import Mathlib

open scoped TensorProduct

/--
Let $A$ be the ring $k[[x_1, \dots, x_n]]$, where $k$ is a field, $n \in \mathbb{N}$, $n \ne 0$.
Show that there is \textbf{no} isomorphism
\[
A \otimes_k A \cong k[[x_1, \dots, x_n, y_1, \dots, y_n]].
\]
-/
theorem isEmpty_mvPowerSeries_tensor_mvPowerSeries_algEquiv
    {k : Type} [Field k] (n : ℕ) (hn : n ≠ 0) :
    IsEmpty ((MvPowerSeries (Fin n) k) ⊗[k] (MvPowerSeries (Fin n) k) ≃ₐ[k]
    (MvPowerSeries (Fin (n + n)) k)) := by
  sorry

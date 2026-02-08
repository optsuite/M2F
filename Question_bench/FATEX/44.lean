import Mathlib

open MvPolynomial

/-- Let $k$ be a field. Let $S$ be a finite type $k$-algebra. We say that $S$ is a
  \textit{global complete intersection over $k$} if there exists a presentation
  $S = k[x_1, \dots, x_n]/(f_1, \dots, f_c)$ such that $\dim(S) = n - c$. -/
class IsGlobalCompleteIntersection (k : Type) [Field k] (S : Type) [CommRing S] [Algebra k S] :
    Prop extends Algebra.FiniteType k S where
  isGlobalCompleteIntersection : ∃ n : ℕ, ∃ rs : List (MvPolynomial (Fin n) k),
    Nonempty (S ≃ₐ[k] (MvPolynomial (Fin n) k) ⧸ Ideal.ofList rs) ∧ ringKrullDim S + rs.length = n

/--
Let \( k \) be a field, and set \( A = k[X, Y, Z]/(X^2 - Y^2, Y^2 - Z^2, XY, YZ, ZX) \).
Show that \( A \) is not a global complete intersection. -/
theorem quot_x2_sub_y2_y2_sub_z2_xy_yz_zx_not_global_complete_intersection (k : Type) [Field k] :
    ¬ IsGlobalCompleteIntersection k (MvPolynomial (Fin 3) k ⧸ Ideal.span
    ({(X 0)^ 2 - (X 1)^2, (X 1)^2 - (X 2)^2, (X 0) * (X 1), (X 1) * (X 2), (X 2) * (X 0)} :
    Set (MvPolynomial (Fin 3) k))) := by
  sorry

import Mathlib

/--
Let \(k\) be any field. Suppose that \(A = k[[x,y]]/(f)\) and \(B = k[[u,v]]/(g)\),
where \(f = xy\) and \(g = uv + \delta\) with \(\delta \in (u,v)^{3}\). Show that \(A\) and \(B\) are isomorphic.
-/
theorem nonEmpty_ringEquiv_of_sub_in_cube (k : Type) [Field k]
    (g : MvPowerSeries (Fin 2) k) (hg : g - .X 0 * .X 1 ∈ (Ideal.span {MvPowerSeries.X 0, .X 1}) ^ 3) :
    Nonempty (((MvPowerSeries (Fin 2) k) ⧸ Ideal.span {(.X 0 * .X 1 : (MvPowerSeries (Fin 2) k))}) ≃+*
    ((MvPowerSeries (Fin 2) k) ⧸ Ideal.span {g})) := by
  sorry

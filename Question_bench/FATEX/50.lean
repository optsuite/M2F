import Mathlib

/--
Let \((A, \mathfrak{m}, K)\) be a complete local ring containing a field,
and suppose that \(\mathfrak{m}\) is finitely generated over \(A\). Then \(A\) is Noetherian.
-/
theorem isNoetherianRing_of_isLocalRing_of_field_inj_of_adicComplete_of_maximalIdeal_finite
    (R : Type) [CommRing R] [IsLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (k : Type) [Field k] [Algebra k R] [NoZeroSMulDivisors k R]
    (hfg : (IsLocalRing.maximalIdeal R).FG) : IsNoetherianRing R := by
  sorry

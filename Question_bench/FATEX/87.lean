import Mathlib

/--
There exists two commutative rings \(R, S\), such that \(R[x]\) is isomorphic to \(S[x]\) but \(R\) is not isomorphic to \(S\).
-/
theorem exists_polynomial_ringEquiv_isEmpty_ringEquiv :
    ∃ (R S : Type) (_ : CommRing R) (_ : CommRing S),
    Nonempty ((Polynomial R) ≃+* (Polynomial S)) ∧ IsEmpty (R ≃+* S) := by
  sorry

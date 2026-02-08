import Mathlib

/--
Let \( A \) be a commutative ring. Prove that every principal ideal of \( A \) is idempotent
if and only if every finitely generated ideal is a direct summand of \( A \).
-/
theorem principal_ideal_idempotent_iff_fg_ideal_is_direct_summand (A : Type) [CommRing A] :
    (∀ I : Ideal A, I.IsPrincipal → I ^ 2 = I) ↔
    (∀ I : Ideal A, I.FG → (∃ J : Ideal A, I ⊔ J = ⊤ ∧ I ⊓ J = ⊥ )) := by
  sorry

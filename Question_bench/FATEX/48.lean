import Mathlib

/--
A commutative ring \( A \) is \textit{absolutely flat} if every \( A \)-module is flat.
-/
class IsAbsolutelyFlat (R : Type) [CommRing R] : Prop where
  out ⦃P : Type⦄ [AddCommGroup P] [Module R P] : Module.Flat R P

/--
Prove that \( A \) is absolutely flat if and only if every principal ideal is idempotent.
-/
theorem isAbsolutelyFlat_iff_principal_ideal_idempotent (R : Type) [CommRing R] :
    IsAbsolutelyFlat R ↔ (∀ I : Ideal R, I.IsPrincipal → I ^ 2 = I) := by
  sorry

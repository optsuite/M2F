import Mathlib

/- If $R$ is a valuation ring, then an $R$-module $A$ is flat if it is torsion-free.-/
theorem flat_of_noZeroSMulDivisor {R A : Type} [CommRing R] [IsDomain R] [ValuationRing R] [AddCommGroup A]
    [Module R A] [NoZeroSMulDivisors R A] : Module.Flat R A := by
  have htors : Submodule.torsion R A = ⊥ :=
    (Submodule.noZeroSMulDivisors_iff_torsion_eq_bot (R := R) (M := A)).1 inferInstance
  exact (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout (R := R) (M := A)).2 htors

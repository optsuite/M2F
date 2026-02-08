import Mathlib

open Real

/- Prove that $\sin 1^{\circ}$ is algebraic over $\mathbb{Q}$.-/
theorem isAlgebraic_sin_pi_div_180 : IsAlgebraic ℚ (sin (π / 180)) := by
  have hZ : IsAlgebraic ℤ (sin (((1 / 180 : ℚ) : ℝ) * π)) := by
    simpa using (Real.isAlgebraic_sin_rat_mul_pi (1 / 180 : ℚ))
  have hinj : Function.Injective (algebraMap ℤ ℚ) := by
    intro a b h
    exact Int.cast_injective (by simpa using h)
  have hQ : IsAlgebraic ℚ (sin (((1 / 180 : ℚ) : ℝ) * π)) :=
    IsAlgebraic.extendScalars (R:=ℤ) (S:=ℚ) (A:=ℝ) hinj hZ
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hQ

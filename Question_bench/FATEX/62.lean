import Mathlib

/--
Let \( \varphi: R \to S \) be a smooth ring map. Let \( \sigma: S \to R \) be a left inverse to \( \varphi \).
Set \( I = \operatorname{Ker}(\sigma) \). If \( I / I^{2} \) is free,
show \( S^{\wedge} \cong R[[t_{1}, \ldots, t_{d}]] \) as \( R \)-algebras,
where \( S^{\wedge} \) is the \( I \)-adic completion of \( S \).
-/
theorem adicCompletion_equiv_of_smooth (R S : Type) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Smooth R S] (σ : S →+* R)
    (h : Function.LeftInverse σ (algebraMap R S)) (hf : Module.Free R σ.ker.Cotangent) :
    ∃ d : ℕ, Nonempty (AdicCompletion (RingHom.ker σ) S ≃ₐ[R] MvPowerSeries (Fin d) R) := by
  sorry

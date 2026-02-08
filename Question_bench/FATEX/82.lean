import Mathlib

open IsLocalRing

/--
Let \( A \) be a Noetherian complete local ring of dimension \( d \), of mixed characteristic
(i.e., $\mathrm{Char} A = 0$ and $\mathrm{Char} A / \mathfrak{m}$), and let \( p = \text{char}(A/\mathfrak{m}) \).
Assume that \( \text{ht}(p \cdot A) = 1 \).
Prove that \( A \) is a finitely generated module over a subring \( B \subset A \) such that
\[
B \cong C[[x_1, \dots, x_{d-1}]],
\]
where \( C \) is a discrete valuation ring (DVR). -/
theorem subring_iso_mvPowerSeries_over_DVR (d : ℕ) (A : Type) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] (dim : ringKrullDim A = d)
    {p : ℕ} (hp : p.Prime) [CharZero A] [CharP (ResidueField A) p]
    (ht : (Ideal.span {(p : A)}).height = 1) :
    ∃ B : Subring A, Module.Finite B A ∧
    ∃ (C : Type) (_ : CommRing C) (_ : IsDomain C), IsDiscreteValuationRing C ∧
    Nonempty (B ≃+* MvPowerSeries (Fin (d - 1)) C) := by
  sorry

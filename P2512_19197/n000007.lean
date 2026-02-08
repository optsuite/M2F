import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for n000007: the class of `P ^ k` is zero in the quotient by `(P ^ k)`. -/
lemma helperFor_n000007_mk_P_pow_eq_zero
    {𝕜 : Type*} [Field 𝕜] {P : Polynomial 𝕜} {k : ℕ} :
    Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) (P ^ k) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.subset_span ?_
  simp

/-- Helper for n000007: the class of `P` is nilpotent in the quotient by `(P ^ k)`. -/
lemma helperFor_n000007_isNilpotent_mk_P
    {𝕜 : Type*} [Field 𝕜] {P : Polynomial 𝕜} {k : ℕ} :
    IsNilpotent
      (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) P) := by
  refine ⟨k, ?_⟩
  rw [← (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜)))).map_pow P k]
  exact helperFor_n000007_mk_P_pow_eq_zero

/-- Helper for n000007: nilpotence of the class of `A * P` in the quotient by `(P ^ k)`. -/
lemma helperFor_n000007_isNilpotent_mk_mul_left
    {𝕜 : Type*} [Field 𝕜] {P : Polynomial 𝕜} {k : ℕ} (A : Polynomial 𝕜) :
    IsNilpotent
      (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) (A * P)) := by
  let I : Ideal (Polynomial 𝕜) := Ideal.span ({P ^ k} : Set (Polynomial 𝕜))
  have hnilP : IsNilpotent (Ideal.Quotient.mk I P) := by
    change IsNilpotent
      (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) P)
    exact helperFor_n000007_isNilpotent_mk_P (P := P) (k := k)
  have hnil : IsNilpotent ((Ideal.Quotient.mk I A) * (Ideal.Quotient.mk I P)) :=
    (Commute.all _ _).isNilpotent_mul_left hnilP
  change IsNilpotent (Ideal.Quotient.mk I (A * P))
  rw [(Ideal.Quotient.mk I).map_mul A P]
  exact hnil

/-- Helper for n000007: Bezout identity transported to the quotient ring. -/
lemma helperFor_n000007_bezout_identity_in_quotient
    {𝕜 : Type*} [Field 𝕜] {P A B : Polynomial 𝕜} {k : ℕ}
    (hAB : A * P + B * Polynomial.derivative P = 1) :
    (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) B) *
        (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜)))
          (Polynomial.derivative P))
      = 1 -
        (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜)))
          (A * P)) := by
  let I : Ideal (Polynomial 𝕜) := Ideal.span ({P ^ k} : Set (Polynomial 𝕜))
  have hAB' :
      Ideal.Quotient.mk I (A * P + B * Polynomial.derivative P) =
        Ideal.Quotient.mk I (1 : Polynomial 𝕜) := by
    exact congrArg (Ideal.Quotient.mk I) hAB
  rw [(Ideal.Quotient.mk I).map_add, (Ideal.Quotient.mk I).map_one] at hAB'
  have hAB'' :
      Ideal.Quotient.mk I (B * Polynomial.derivative P) + Ideal.Quotient.mk I (A * P) =
        (1 : Polynomial 𝕜 ⧸ I) := by
    calc
      Ideal.Quotient.mk I (B * Polynomial.derivative P) + Ideal.Quotient.mk I (A * P) =
          Ideal.Quotient.mk I (A * P) + Ideal.Quotient.mk I (B * Polynomial.derivative P) := by
            exact add_comm _ _
      _ = (1 : Polynomial 𝕜 ⧸ I) := hAB'
  have hsub :
      Ideal.Quotient.mk I (B * Polynomial.derivative P) =
        (1 : Polynomial 𝕜 ⧸ I) - Ideal.Quotient.mk I (A * P) := by
    exact (eq_sub_iff_add_eq).2 hAB''
  calc
    (Ideal.Quotient.mk I B) * (Ideal.Quotient.mk I (Polynomial.derivative P)) =
        Ideal.Quotient.mk I (B * Polynomial.derivative P) := by
          simpa using
            ((Ideal.Quotient.mk I).map_mul B (Polynomial.derivative P)).symm
    _ = 1 - Ideal.Quotient.mk I (A * P) := hsub

/-- n000007: Let 𝕜 be a field, let `P ∈ 𝕜[X]` be separable (i.e. `IsCoprime P P'`), let `k ≥ 1`,
and set `R = 𝕜[X] / (P^k)`. If `x` is the class of `X` in `R`, then `P'(x)` is a unit in `R`. -/
theorem derivative_isUnit_quotient_span_pow
    {𝕜 : Type*} [Field 𝕜] {P : Polynomial 𝕜}
    (hsep : IsCoprime P (Polynomial.derivative P)) {k : ℕ} (hk : 1 ≤ k) :
    IsUnit
      (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜)))
        (Polynomial.derivative P)) := by
  rcases hsep with ⟨A, B, hAB⟩
  let I : Ideal (Polynomial 𝕜) := Ideal.span ({P ^ k} : Set (Polynomial 𝕜))
  change IsUnit (Ideal.Quotient.mk I (Polynomial.derivative P))
  have hbez :
      (Ideal.Quotient.mk I B) * (Ideal.Quotient.mk I (Polynomial.derivative P)) =
        1 - Ideal.Quotient.mk I (A * P) := by
    change
      (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) B) *
          (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜)))
            (Polynomial.derivative P))
        = 1 -
          (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜)))
            (A * P))
    exact
      helperFor_n000007_bezout_identity_in_quotient (P := P) (A := A) (B := B) (k := k) hAB
  have hnil : IsNilpotent (Ideal.Quotient.mk I (A * P)) := by
    change IsNilpotent
      (Ideal.Quotient.mk (Ideal.span ({P ^ k} : Set (Polynomial 𝕜))) (A * P))
    exact helperFor_n000007_isNilpotent_mk_mul_left (P := P) (k := k) A
  have hunit_one_sub : IsUnit (1 - Ideal.Quotient.mk I (A * P)) :=
    IsNilpotent.isUnit_one_sub hnil
  have hunit_mul :
      IsUnit ((Ideal.Quotient.mk I B) * (Ideal.Quotient.mk I (Polynomial.derivative P))) := by
    rw [hbez]
    exact hunit_one_sub
  exact isUnit_of_mul_isUnit_right hunit_mul

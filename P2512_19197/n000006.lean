import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Helper for n000006: the coefficientwise map fixes `X^k`. -/
lemma helperFor_n000006_map_X_pow
    (K1 K2 : Type*) [Field K1] [Field K2] (k : Nat) (theta : RingEquiv K1 K2) :
    Polynomial.map theta.toRingHom ((Polynomial.X : Polynomial K1) ^ k) =
      ((Polynomial.X : Polynomial K2) ^ k) := by
  simp

/-- Helper for n000006: the coefficientwise map sends the ideal `(X^k)` to itself. -/
lemma helperFor_n000006_map_span_X_pow
    (K1 K2 : Type*) [Field K1] [Field K2] (k : Nat) (theta : RingEquiv K1 K2) :
    Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set (Polynomial K2)) =
      Ideal.map (Polynomial.mapEquiv theta).toRingHom
        (Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set (Polynomial K1))) := by
  symm
  simp [Ideal.map_span, Set.image_singleton]

/-- Helper for n000006: computation of the quotient equivalence on classes. -/
lemma helperFor_n000006_quotientEquiv_mk
    (K1 K2 : Type*) [Field K1] [Field K2] (k : Nat) (theta : RingEquiv K1 K2)
    (h :
      Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set (Polynomial K2)) =
        Ideal.map (Polynomial.mapEquiv theta).toRingHom
          (Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set (Polynomial K1)))) :
    forall f : Polynomial K1,
      (Ideal.quotientEquiv
            (Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set (Polynomial K1)))
            (Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set (Polynomial K2)))
            (Polynomial.mapEquiv theta) h)
          (Ideal.Quotient.mk _ f) =
        Ideal.Quotient.mk _ (Polynomial.map theta.toRingHom f) := by
  intro f
  simp

/-- n000006: A field isomorphism induces a ring isomorphism on the truncated
polynomial rings `K[epsilon]/(epsilon^k)`, acting coefficientwise by the given
isomorphism. -/
theorem truncatedPolynomialQuotient_iso
    (K1 K2 : Type*) [Field K1] [Field K2] (k : Nat) (hk : 1 ≤ k)
    (theta : RingEquiv K1 K2) :
    Exists fun phi :
        RingEquiv
          (Polynomial K1 ⧸ Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set (Polynomial K1)))
          (Polynomial K2 ⧸ Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set (Polynomial K2))) =>
      forall f : Polynomial K1,
        phi (Ideal.Quotient.mk _ f) =
          Ideal.Quotient.mk _ (Polynomial.map theta.toRingHom f) := by
  have _ : 1 ≤ k := hk
  let I1 : Ideal (Polynomial K1) :=
    Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set (Polynomial K1))
  let I2 : Ideal (Polynomial K2) :=
    Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set (Polynomial K2))
  have hI :
      I2 = Ideal.map (Polynomial.mapEquiv theta).toRingHom I1 := by
    simpa [I1, I2] using
      helperFor_n000006_map_span_X_pow (K1 := K1) (K2 := K2) (k := k) (theta := theta)
  let phi :
      RingEquiv (Polynomial K1 ⧸ I1) (Polynomial K2 ⧸ I2) :=
    Ideal.quotientEquiv I1 I2 (Polynomial.mapEquiv theta) hI
  refine ⟨phi, ?_⟩
  intro f
  simp [I1, I2, phi]

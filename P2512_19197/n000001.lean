import Mathlib
import P2512_19197.n000002
import P2512_19197.n000003
import P2512_19197.n000004
import P2512_19197.n000005
import P2512_19197.n000006

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- The quotient ring `K[X]/(P)` for a polynomial `P` over a field `K`. -/
abbrev PolynomialQuotient (K : Type u) [Field K] (P : Polynomial K) : Type u :=
  Polynomial K ⧸ Ideal.span ({P} : Set (Polynomial K))

/-- Helper for n000001: irreducible polynomials with nonzero derivative are separable. -/
lemma helperFor_n000001_separable_of_irreducible_derivative_ne_zero
    {K : Type*} [Field K] {P : Polynomial K} (hP : Irreducible P)
    (hder : P.derivative ≠ 0) : P.Separable := by
  exact (Polynomial.separable_iff_derivative_ne_zero hP).2 hder

/-- Helper for n000001: local structure and residue field of `K[X]/(P^k)`. -/
lemma helperFor_n000001_localRing_and_residueField_equiv
    (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) (hk : 0 < k) (hP : Irreducible P) :
    ∃ hR : IsLocalRing (PolynomialQuotient K (P ^ k)),
      Nonempty
        (IsLocalRing.ResidueField (PolynomialQuotient K (P ^ k)) ≃+*
          PolynomialQuotient K P) := by
  classical
  have hk1 : 1 ≤ k := Nat.succ_le_iff.2 hk
  have hlocal :=
    local_quotient_by_irreducible_power K P k hk1 hP
  rcases hlocal with ⟨hR, hmax_eq, _hpow, hres⟩
  let R := polynomialPowerQuotient K P k
  haveI : IsLocalRing R := hR
  have hmax_eq' : IsLocalRing.maximalIdeal R = quotientIdealByClassOfP K P k := by
    simpa using hmax_eq
  let e1 :
      IsLocalRing.ResidueField R ≃+* (R ⧸ quotientIdealByClassOfP K P k) :=
    Ideal.quotEquivOfEq hmax_eq'
  rcases hres with ⟨e2⟩
  refine ⟨?_, ?_⟩
  · simpa [R, polynomialPowerQuotient, polynomialPowerIdeal, PolynomialQuotient] using hR
  · refine ⟨?_⟩
    simpa [R, polynomialPowerQuotient, polynomialPowerIdeal, PolynomialQuotient] using
      (e1.trans e2)

/-- Helper for n000001: `K[X]/(P^k)` is a truncated polynomial ring over `K[X]/(P)`. -/
lemma helperFor_n000001_powerQuotient_equiv_truncatedPolynomial
    (K : Type*) [Field K] (P : Polynomial K) (k : ℕ) (hk : 0 < k)
    (hP : Irreducible P) (hder : P.derivative ≠ 0) :
    Nonempty
      (RingEquiv (PolynomialQuotient K (P ^ k))
        (Polynomial (PolynomialQuotient K P) ⧸
          Ideal.span ({(Polynomial.X : Polynomial (PolynomialQuotient K P)) ^ k} : Set _))) := by
  classical
  let I : Ideal (Polynomial K) := Ideal.span ({P ^ k} : Set (Polynomial K))
  let J : Ideal (Polynomial K) := Ideal.span ({P} : Set (Polynomial K))
  let R := (Polynomial K) ⧸ I
  let K0 := (Polynomial K) ⧸ J
  have hk1 : 1 ≤ k := Nat.succ_le_iff.2 hk
  have hsep : P.Separable :=
    helperFor_n000001_separable_of_irreducible_derivative_ne_zero hP hder
  have hIJ : I ≤ J := by
    simpa [I, J, polynomialPowerIdeal] using
      helperFor_n000002_polynomialPowerIdeal_le_spanP K P k hk1
  let pi : AlgHom K R K0 := Ideal.Quotient.factorₐ K hIJ
  have hpi :
      ∀ x : Polynomial K, pi (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := by
    intro x
    rfl
  have hsec :
      Exists fun s : AlgHom K K0 R => AlgHom.comp pi s = AlgHom.id K K0 := by
    simpa [I, J, R, K0] using
      (exists_alg_section_quotient_map (F := K) (P := P) hP hsep (k := k) hk1) pi hpi
  rcases hsec with ⟨s, hs⟩
  letI : Algebra K0 R := RingHom.toAlgebra s.toRingHom
  let eps : R := Ideal.Quotient.mk I P
  let phi0 : Polynomial K0 →ₐ[K0] R := Polynomial.aeval eps
  let I' : Ideal (Polynomial K0) :=
    Ideal.span ({(Polynomial.X : Polynomial K0) ^ k} : Set (Polynomial K0))
  have hPow : eps ^ k = 0 := by
    have hPk_mem : P ^ k ∈ I := by
      have hx : P ^ k ∈ ({P ^ k} : Set (Polynomial K)) := by
        simp
      exact Ideal.subset_span hx
    have hPk0 : Ideal.Quotient.mk I (P ^ k) = 0 := by
      exact (Ideal.Quotient.eq_zero_iff_mem).2 hPk_mem
    have hmap : Ideal.Quotient.mk I (P ^ k) = (Ideal.Quotient.mk I P) ^ k := by
      simpa using (Ideal.Quotient.mk I).map_pow P k
    calc
      eps ^ k = (Ideal.Quotient.mk I P) ^ k := by
        rfl
      _ = Ideal.Quotient.mk I (P ^ k) := by
        symm
        exact hmap
      _ = 0 := hPk0
  have hI' : ∀ a : Polynomial K0, a ∈ I' → phi0 a = 0 := by
    intro a ha
    rcases Ideal.mem_span_singleton'.1 ha with ⟨q, rfl⟩
    have hX : phi0 (Polynomial.X : Polynomial K0) = eps := by
      simp [phi0]
    have hXk : phi0 ((Polynomial.X : Polynomial K0) ^ k) = 0 := by
      calc
        phi0 ((Polynomial.X : Polynomial K0) ^ k) =
            (phi0 (Polynomial.X : Polynomial K0)) ^ k := by
              simpa using (map_pow phi0 (Polynomial.X : Polynomial K0) k)
        _ = eps ^ k := by
              simp [hX]
        _ = 0 := hPow
    calc
      phi0 (q * (Polynomial.X : Polynomial K0) ^ k) =
          phi0 q * phi0 ((Polynomial.X : Polynomial K0) ^ k) := by
            simp [map_mul]
      _ = 0 := by
            simp [hXk]
  let Phi : AlgHom K0 (Polynomial K0 ⧸ I') R :=
    Ideal.Quotient.liftₐ I' phi0 hI'
  have hPhi : Phi (Ideal.Quotient.mk I' Polynomial.X) = eps := by
    have hcomp :
        (Phi.comp (Ideal.Quotient.mkₐ K0 I')) = phi0 := by
      simpa [Phi] using
        (Ideal.Quotient.liftₐ_comp (I := I') (f := phi0) (hI := hI'))
    have hcompX :=
      congrArg (fun f : Polynomial K0 →ₐ[K0] R => f Polynomial.X) hcomp
    have hphi0X : phi0 Polynomial.X = eps := by
      simp [phi0]
    simpa [Ideal.Quotient.mkₐ_eq_mk, hphi0X] using hcompX
  -- Local structure of `R = K[X]/(P^k)` and identification of the maximal ideal.
  have hlocal := local_quotient_by_irreducible_power K P k hk1 hP
  rcases hlocal with ⟨hR, hmax_eq, _hpow, _hres⟩
  haveI : IsLocalRing R := by
    simpa [R, I, polynomialPowerQuotient, polynomialPowerIdeal] using hR
  have hmax_R : IsLocalRing.maximalIdeal R = Ideal.span ({eps} : Set R) := by
    have hmax_eq' :
        IsLocalRing.maximalIdeal R = quotientIdealByClassOfP K P k := by
      simpa [R, I, polynomialPowerQuotient, polynomialPowerIdeal] using hmax_eq
    have hquot :
        quotientIdealByClassOfP K P k = Ideal.span ({eps} : Set R) := by
      -- `quotientIdealByClassOfP` is defined as the span of the class of `P` in the quotient.
      simp [quotientIdealByClassOfP, eps, R, I, polynomialPowerQuotient, polynomialPowerIdeal]
    simpa [hquot] using hmax_eq'
  -- The residue map `R → K0` is the quotient map; its kernel is the maximal ideal.
  have hker_pi :
      RingHom.ker pi.toRingHom = quotientIdealByClassOfP K P k := by
    have hker0 :
        RingHom.ker (Ideal.Quotient.factor hIJ) =
          J.map (Ideal.Quotient.mk I) := by
      simpa using (Ideal.Quotient.factor_ker (I := I) (J := J) hIJ)
    have hker1 : RingHom.ker pi.toRingHom = J.map (Ideal.Quotient.mk I) := by
      -- `pi` is `Ideal.Quotient.factorₐ`, whose underlying ring hom is `Ideal.Quotient.factor`.
      simpa [pi, Ideal.Quotient.coe_factorₐ] using hker0
    simpa [J] using
      (hker1.trans (helperFor_n000002_quotientIdealByClassOfP_eq_map_spanP K P k).symm)
  have hker_pi_max : RingHom.ker pi.toRingHom = IsLocalRing.maximalIdeal R := by
    -- `maximalIdeal R` is the quotient ideal generated by the class of `P`.
    -- (This is part of `local_quotient_by_irreducible_power`.)
    have hmax_eq' :
        IsLocalRing.maximalIdeal R = quotientIdealByClassOfP K P k := by
      simpa [R, I, polynomialPowerQuotient, polynomialPowerIdeal] using hmax_eq
    simpa [hmax_eq'] using hker_pi
  have hpi_split : ∀ a : K0, pi.toRingHom (algebraMap K0 R a) = a := by
    intro a
    have hs_apply : pi (s a) = a := by
      have := congrArg (fun f : AlgHom K K0 K0 => f a) hs
      simpa [AlgHom.comp_apply] using this
    -- Here `algebraMap K0 R = s` by the definition of `RingHom.toAlgebra`.
    simpa [RingHom.algebraMap_toAlgebra (i := s.toRingHom)] using hs_apply
  have hPow_pred : eps ^ (k - 1) ≠ 0 := by
    -- If `eps^(k-1)=0` then `P^(k-1) ∈ (P^k)`, forcing `P` to be a unit (impossible).
    intro hz
    have hmk :
        Ideal.Quotient.mk I (P ^ (k - 1)) = 0 := by
      have hmap :
          Ideal.Quotient.mk I (P ^ (k - 1)) =
            (Ideal.Quotient.mk I P) ^ (k - 1) := by
        simpa using (Ideal.Quotient.mk I).map_pow P (k - 1)
      -- Unfold `eps` in `hz`, then rewrite via `hmap`.
      dsimp [eps] at hz
      rw [hmap]
      exact hz
    have hmem : P ^ (k - 1) ∈ I :=
      (Ideal.Quotient.eq_zero_iff_mem).1 hmk
    have hdiv : P ^ k ∣ P ^ (k - 1) := by
      -- Membership in a principal ideal is divisibility.
      simpa [I] using (Ideal.mem_span_singleton.mp hmem)
    have hle : k ≤ k - 1 :=
      (pow_dvd_pow_iff (a := P) (n := k) (m := k - 1) hP.ne_zero hP.1).1 hdiv
    cases k with
    | zero =>
        cases hk
    | succ k' =>
        -- Now `hle : succ k' ≤ k'`, contradiction.
        exact (Nat.not_succ_le_self k') (by simpa using hle)
  have hIso :
      ∃ e : AlgEquiv K0 (Polynomial K0 ⧸ I') R, e.toAlgHom = Phi := by
    exact
      truncatedPolynomialAlgHom_isIso (K := K0) (R := R) (k := k) (hk := hk)
        (pi := pi.toRingHom) (hpi := hpi_split) (hker := hker_pi_max)
        (eps := eps) (hmax := hmax_R) (hPow := hPow) (hPow_pred := hPow_pred) Phi hPhi
  rcases hIso with ⟨e, he⟩
  refine ⟨?_⟩
  simpa [R, K0, I', PolynomialQuotient, I, J] using e.toRingEquiv.symm

/-- Helper for n000001: truncated polynomial rings are functorial in the coefficient ring. -/
lemma helperFor_n000001_truncatedPolynomial_equiv_of_fieldEquiv
    (K1 K2 : Type*) [CommRing K1] [CommRing K2] (k : ℕ) (θ : RingEquiv K1 K2) :
    Nonempty
      (RingEquiv
        (Polynomial K1 ⧸ Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set _))
        (Polynomial K2 ⧸ Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set _))) := by
  let I1 : Ideal (Polynomial K1) :=
    Ideal.span ({(Polynomial.X : Polynomial K1) ^ k} : Set (Polynomial K1))
  let I2 : Ideal (Polynomial K2) :=
    Ideal.span ({(Polynomial.X : Polynomial K2) ^ k} : Set (Polynomial K2))
  have hI : I2 = Ideal.map (Polynomial.mapEquiv θ).toRingHom I1 := by
    symm
    simp [I1, I2, Ideal.map_span, Set.image_singleton]
  let phi : RingEquiv (Polynomial K1 ⧸ I1) (Polynomial K2 ⧸ I2) :=
    Ideal.quotientEquiv I1 I2 (Polynomial.mapEquiv θ) hI
  refine ⟨?_⟩
  exact phi

/-- n000001: Let `K` be a field, `P1`, `P2` irreducible polynomials over `K`, and `k` a positive integer.
If `P1` and `P2` are separable (`P_i' ≠ 0`), then the local rings `K[X]/(P1^k)` and `K[X]/(P2^k)`
are isomorphic iff their residue fields `K[X]/(P1)` and `K[X]/(P2)` are isomorphic. -/
theorem polynomialQuotientPower_iso_iff_polynomialQuotient_iso
    (K : Type*) [Field K]
    (P1 P2 : Polynomial K) (k : ℕ)
    (hk : 0 < k)
    (hP1 : Irreducible P1) (hP2 : Irreducible P2)
    (hsep1 : P1.derivative ≠ 0) (hsep2 : P2.derivative ≠ 0) :
    Nonempty (RingEquiv (PolynomialQuotient K (P1 ^ k)) (PolynomialQuotient K (P2 ^ k))) ↔
      Nonempty (RingEquiv (PolynomialQuotient K P1) (PolynomialQuotient K P2)) := by
  constructor
  · intro h
    rcases h with ⟨e⟩
    rcases helperFor_n000001_localRing_and_residueField_equiv K P1 k hk hP1 with ⟨hR1, hres1⟩
    rcases helperFor_n000001_localRing_and_residueField_equiv K P2 k hk hP2 with ⟨hR2, hres2⟩
    let R1 := PolynomialQuotient K (P1 ^ k)
    let R2 := PolynomialQuotient K (P2 ^ k)
    haveI : IsLocalRing R1 := hR1
    haveI : IsLocalRing R2 := hR2
    let f : IsLocalRing.ResidueField R1 ≃+* IsLocalRing.ResidueField R2 :=
      residueFieldEquivOfRingEquiv (R := R1) (S := R2) e
    rcases hres1 with ⟨e1⟩
    rcases hres2 with ⟨e2⟩
    refine ⟨?_⟩
    exact e1.symm.trans (f.trans e2)
  · intro h
    rcases
        helperFor_n000001_powerQuotient_equiv_truncatedPolynomial K P1 k hk hP1 hsep1 with
      ⟨e1⟩
    rcases
        helperFor_n000001_powerQuotient_equiv_truncatedPolynomial K P2 k hk hP2 hsep2 with
      ⟨e2⟩
    let K1 := (Polynomial K) ⧸ Ideal.span ({P1} : Set (Polynomial K))
    let K2 := (Polynomial K) ⧸ Ideal.span ({P2} : Set (Polynomial K))
    have hK : Nonempty (RingEquiv K1 K2) := by
      simpa [K1, K2, PolynomialQuotient] using h
    rcases hK with ⟨eK'⟩
    rcases
        (@helperFor_n000001_truncatedPolynomial_equiv_of_fieldEquiv K1 K2 _ _ k eK') with
      ⟨eTrunc0⟩
    have eTrunc :
        RingEquiv
          (Polynomial (PolynomialQuotient K P1) ⧸
            Ideal.span ({(Polynomial.X : Polynomial (PolynomialQuotient K P1)) ^ k} : Set _))
          (Polynomial (PolynomialQuotient K P2) ⧸
            Ideal.span ({(Polynomial.X : Polynomial (PolynomialQuotient K P2)) ^ k} : Set _)) := by
      simpa [K1, K2, PolynomialQuotient] using eTrunc0
    refine ⟨?_⟩
    exact e1.trans (eTrunc.trans e2.symm)

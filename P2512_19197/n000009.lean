import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The ideal `(P)` in `k[X]`. -/
abbrev polynomialIdeal (k : Type*) [CommRing k] (P : Polynomial k) :
    Ideal (Polynomial k) :=
  Ideal.span ({P} : Set (Polynomial k))

/-- The quotient ring `k[X]/(P)`. -/
abbrev polynomialQuotient (k : Type*) [CommRing k] (P : Polynomial k) :=
  (Polynomial k) ⧸ polynomialIdeal k P

/-- The class of `X` in the quotient ring `k[X]/(P)`. -/
abbrev polynomialQuotientX (k : Type*) [CommRing k] (P : Polynomial k) :
    polynomialQuotient k P :=
  Ideal.Quotient.mk (polynomialIdeal k P) Polynomial.X

/-- Hypotheses from the parent statement needed for inductive completion. -/
def inductiveCompletionHypotheses
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (P : Polynomial k)
    (π : R →+* polynomialQuotient k P) : Prop :=
  let I : Ideal R := RingHom.ker π
  IsAdicComplete I R ∧
    π.comp (algebraMap k R) = algebraMap k (polynomialQuotient k P) ∧
    ∃ ySeq : ℕ → R,
      π (ySeq 1) = polynomialQuotientX k P ∧
      (∀ n, ySeq (n + 1) ≡ ySeq n [SMOD (I ^ n • ⊤ : Submodule R R)]) ∧
      (∀ n, Polynomial.eval₂ (algebraMap k R) (ySeq n) P ≡ 0
        [SMOD (I ^ n • ⊤ : Submodule R R)])

/-- Helper for n000009: in `R`, the submodule `I^n • ⊤` equals the ideal `I^n`. -/
lemma helperForN000009_pow_smul_top_eq
    {R : Type*} [CommRing R] (I : Ideal R) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R R) = (I ^ n : Ideal R) := by
  simpa [Ideal.map_id] using
    (Ideal.smul_top_eq_map (R := R) (S := R) (I := I ^ n))

/-- Helper for n000009: successive congruences imply full Cauchy congruences. -/
lemma helperForN000009_cauchy_of_succ_smodEq
    {R : Type*} [CommRing R] (I : Ideal R) (f : ℕ → R)
    (h : ∀ n, f (n + 1) ≡ f n [SMOD (I ^ n • ⊤ : Submodule R R)]) :
    ∀ {m n}, m ≤ n → f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
  intro m n hmn
  rcases Nat.exists_eq_add_of_le hmn with ⟨t, rfl⟩
  induction t with
  | zero =>
      simpa using (SModEq.rfl : f m ≡ f m [SMOD (I ^ m • ⊤ : Submodule R R)])
  | succ t ih =>
      have hstep :
          f (m + t + 1) ≡ f (m + t) [SMOD (I ^ (m + t) • ⊤ : Submodule R R)] :=
        h (m + t)
      have hstep' :
          f (m + t) ≡ f (m + t + 1) [SMOD (I ^ m • ⊤ : Submodule R R)] := by
        apply SModEq.mono (Submodule.pow_smul_top_le (I := I) (M := R) (Nat.le_add_right m t))
        exact SModEq.symm hstep
      exact SModEq.trans (ih (Nat.le_add_right m t)) hstep'

/-- Helper for n000009: evaluation respects congruence modulo `I^n`. -/
lemma helperForN000009_eval2_smodEq_of_smodEq
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (P : Polynomial k) (I : Ideal R) (n : ℕ) {x y : R}
    (hxy : x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)]) :
    Polynomial.eval₂ (algebraMap k R) x P ≡
      Polynomial.eval₂ (algebraMap k R) y P [SMOD (I ^ n • ⊤ : Submodule R R)] := by
  have hxy' : x ≡ y [SMOD (I ^ n : Ideal R)] := by
    simpa [helperForN000009_pow_smul_top_eq (I := I) (n := n)] using hxy
  have h' :
      (P.map (algebraMap k R)).eval x ≡ (P.map (algebraMap k R)).eval y
        [SMOD (I ^ n : Ideal R)] :=
    SModEq.eval (I := I ^ n) hxy' (P.map (algebraMap k R))
  simpa [Polynomial.eval₂_eq_eval_map,
    helperForN000009_pow_smul_top_eq (I := I) (n := n)] using h'

/-- Helper for n000009: if `P(y)=0`, then `aeval y` kills the ideal `(P)`. -/
lemma helperForN000009_aeval_mem_polynomialIdeal
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (P : Polynomial k) (y : R)
    (hy : Polynomial.eval₂ (algebraMap k R) y P = 0) :
    ∀ q : Polynomial k, q ∈ polynomialIdeal k P → (Polynomial.aeval y q : R) = 0 := by
  intro q hq
  rcases (Ideal.mem_span_singleton'.1 hq) with ⟨r, rfl⟩
  have hP : (Polynomial.aeval y P : R) = 0 := by
    simpa [Polynomial.aeval_def] using hy
  calc
    (Polynomial.aeval y (r * P) : R)
        = Polynomial.aeval y r * Polynomial.aeval y P := by
            simp
    _ = 0 := by
            simp [hP]

/-- Helper for n000009: evaluation at `Xbar` equals the quotient map. -/
lemma helperForN000009_eval2_Xbar_eq_mk
    (k : Type*) [CommRing k] (P : Polynomial k) (f : Polynomial k) :
    Polynomial.eval₂ (algebraMap k (polynomialQuotient k P)) (polynomialQuotientX k P) f =
      Ideal.Quotient.mk (polynomialIdeal k P) f := by
  simpa [polynomialQuotientX, Ideal.Quotient.mkₐ_eq_mk] using
    (Polynomial.eval₂_algebraMap_X (A := polynomialQuotient k P) (p := f)
      (f := Ideal.Quotient.mkₐ k (polynomialIdeal k P)))

/-- n000009: (Inductive completion) Under the hypotheses of the parent statement,
there exists `y ∈ R` with `π(y) = Xbar` in `k[X]/(P)` and `P(y) = 0`, and the
assignment `Xbar ↦ y` defines a `k`-algebra map `s : k[X]/(P) → R` with
`π ∘ s = id`. -/
theorem inductive_completion
    (k R : Type*) [CommRing k] [CommRing R] [Algebra k R]
    (P : Polynomial k)
    (π : R →+* polynomialQuotient k P)
    (hparent : inductiveCompletionHypotheses k R P π) :
    ∃ y : R,
      π y = polynomialQuotientX k P ∧
      Polynomial.eval₂ (algebraMap k R) y P = 0 ∧
      ∃ s : polynomialQuotient k P →ₐ[k] R,
        s (polynomialQuotientX k P) = y ∧
        π.comp s.toRingHom = RingHom.id (polynomialQuotient k P) :=
  by
  classical
  let I : Ideal R := RingHom.ker π
  have hparent' :
      IsAdicComplete I R ∧
        π.comp (algebraMap k R) = algebraMap k (polynomialQuotient k P) ∧
        ∃ ySeq : ℕ → R,
          π (ySeq 1) = polynomialQuotientX k P ∧
          (∀ n, ySeq (n + 1) ≡ ySeq n [SMOD (I ^ n • ⊤ : Submodule R R)]) ∧
          (∀ n, Polynomial.eval₂ (algebraMap k R) (ySeq n) P ≡ 0
            [SMOD (I ^ n • ⊤ : Submodule R R)]) := by
    simpa [inductiveCompletionHypotheses, I] using hparent
  rcases hparent' with ⟨hcomplete, hcoeff, ySeq, hy1, hsucc, happrox⟩
  haveI : IsAdicComplete I R := hcomplete
  have hCauchy :
      ∀ {m n}, m ≤ n → ySeq m ≡ ySeq n [SMOD (I ^ m • ⊤ : Submodule R R)] :=
    helperForN000009_cauchy_of_succ_smodEq (I := I) (f := ySeq) hsucc
  have hpre : IsPrecomplete I R := (inferInstance : IsPrecomplete I R)
  obtain ⟨y, hy_congr⟩ :=
    IsPrecomplete.prec (I := I) (M := R) (f := ySeq) hpre hCauchy
  have hy1' : ySeq 1 ≡ y [SMOD (I ^ 1 • ⊤ : Submodule R R)] := hy_congr 1
  have hmem : ySeq 1 - y ∈ I := by
    have hmem' : ySeq 1 - y ∈ (I ^ 1 • ⊤ : Submodule R R) :=
      (SModEq.sub_mem).1 hy1'
    simpa [helperForN000009_pow_smul_top_eq (I := I) (n := 1)] using hmem'
  have hy_pi : π y = polynomialQuotientX k P := by
    have hker : ySeq 1 - y ∈ RingHom.ker π := by
      simpa [I] using hmem
    have hzero : π (ySeq 1 - y) = 0 := (RingHom.mem_ker).1 hker
    have hzero' : π (ySeq 1) - π y = 0 := by
      simpa using hzero
    have hpi1 : π (ySeq 1) = π y := sub_eq_zero.mp hzero'
    calc
      π y = π (ySeq 1) := hpi1.symm
      _ = polynomialQuotientX k P := hy1
  have hroot_mod :
      ∀ n, Polynomial.eval₂ (algebraMap k R) y P ≡ 0
        [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro n
    have h1 :
        Polynomial.eval₂ (algebraMap k R) y P ≡
          Polynomial.eval₂ (algebraMap k R) (ySeq n) P
            [SMOD (I ^ n • ⊤ : Submodule R R)] :=
      helperForN000009_eval2_smodEq_of_smodEq (P := P) (I := I) (n := n)
        (x := y) (y := ySeq n) (SModEq.symm (hy_congr n))
    exact SModEq.trans h1 (happrox n)
  have hhaus : IsHausdorff I R := (inferInstance : IsHausdorff I R)
  have hP : Polynomial.eval₂ (algebraMap k R) y P = 0 :=
    IsHausdorff.haus hhaus (x := Polynomial.eval₂ (algebraMap k R) y P) hroot_mod
  have hideal :
      ∀ q : Polynomial k, q ∈ polynomialIdeal k P → (Polynomial.aeval y q : R) = 0 :=
    helperForN000009_aeval_mem_polynomialIdeal (k := k) (R := R) (P := P) (y := y) hP
  let s : polynomialQuotient k P →ₐ[k] R :=
    Ideal.Quotient.liftₐ (polynomialIdeal k P) (Polynomial.aeval y) hideal
  have hs_comp :
      s.comp (Ideal.Quotient.mkₐ k (polynomialIdeal k P)) = Polynomial.aeval y := by
    simpa [s] using
      (Ideal.Quotient.liftₐ_comp (I := polynomialIdeal k P) (f := Polynomial.aeval y) hideal)
  have hsX : s (polynomialQuotientX k P) = y := by
    have hsX' :
        (s.comp (Ideal.Quotient.mkₐ k (polynomialIdeal k P))) Polynomial.X =
          Polynomial.aeval y Polynomial.X :=
      congrArg (fun f : Polynomial k →ₐ[k] R => f Polynomial.X) hs_comp
    simpa [polynomialQuotientX, Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_X] using hsX'
  have hpi_s : π.comp s.toRingHom = RingHom.id (polynomialQuotient k P) := by
    apply (Ideal.Quotient.ringHom_ext (R := Polynomial k) (I := polynomialIdeal k P))
    apply RingHom.ext
    intro f
    simp [RingHom.comp_apply]
    calc
      π (s (Ideal.Quotient.mk (polynomialIdeal k P) f)) =
          π (Polynomial.aeval y f) := by
            simp [s, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      _ = π (Polynomial.eval₂ (algebraMap k R) y f) := by
            simp [Polynomial.aeval_def]
      _ = Polynomial.eval₂ (π.comp (algebraMap k R)) (π y) f := by
            simpa using
              (Polynomial.hom_eval₂ (p := f) (f := algebraMap k R) (g := π) (x := y))
      _ = Polynomial.eval₂ (algebraMap k (polynomialQuotient k P)) (polynomialQuotientX k P) f := by
            simp [hcoeff, hy_pi]
      _ = Ideal.Quotient.mk (polynomialIdeal k P) f := by
            simpa using (helperForN000009_eval2_Xbar_eq_mk k P f)
  refine ⟨y, hy_pi, hP, ?_⟩
  refine ⟨s, hsX, hpi_s⟩

end

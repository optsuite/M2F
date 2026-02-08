import Mathlib

open UniqueFactorizationMonoid


/-- Elements outside a maximal ideal become units modulo any positive power of it. -/
lemma isUnit_quotient_mk_of_not_mem {A : Type*} [CommRing A] {P : Ideal A} (hP : P.IsMaximal)
    {n : ℕ} (hn : n ≠ 0) {x : A} (hx : x ∉ P) :
    IsUnit (Ideal.Quotient.mk (P ^ n) x) := by
  classical
  have hJtop : Ideal.span ({x} : Set A) ⊔ P ^ n = ⊤ := by
    by_contra hJtop
    obtain ⟨M, hMmax, hJM⟩ := Ideal.exists_le_maximal _ hJtop
    have hPn_le_M : P ^ n ≤ M := le_trans le_sup_right hJM
    have hP_le_M : P ≤ M := by
      have hrad : Ideal.radical (P ^ n) ≤ M :=
        (Ideal.IsPrime.radical_le_iff hMmax.isPrime).2 hPn_le_M
      have hradP : Ideal.radical (P ^ n) = P := by
        have hP_rad : Ideal.radical P = P := (Ideal.IsPrime.isRadical hP.isPrime).radical
        simpa [hP_rad] using (Ideal.radical_pow (I := P) (n := n) hn)
      simpa [hradP] using hrad
    have hMP : P = M := hP.eq_of_le hMmax.ne_top hP_le_M
    have hxmem : x ∈ M := hJM (Ideal.mem_sup_left (Ideal.mem_span_singleton_self x))
    exact hx (by simpa [hMP] using hxmem)
  have h1 : (1 : A) ∈ Ideal.span ({x} : Set A) ⊔ P ^ n :=
    (Ideal.eq_top_iff_one (I := Ideal.span ({x} : Set A) ⊔ P ^ n)).1 hJtop
  rcases (Submodule.mem_sup).1 h1 with ⟨y, hy, z, hz, hsum⟩
  rcases (Ideal.mem_span_singleton.mp hy) with ⟨a, rfl⟩
  have hsub : x * a - 1 = -z := by
    apply (sub_eq_iff_eq_add).2
    have hxa : x * a = 1 - z := (eq_sub_iff_add_eq).2 hsum
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hxa
  have hmem : x * a - 1 ∈ P ^ n := by
    have hz' : -z ∈ P ^ n := (Ideal.neg_mem_iff (I := P ^ n)).2 hz
    simpa [hsub] using hz'
  have hmk : Ideal.Quotient.mk (P ^ n) (x * a) = 1 :=
    (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := P ^ n) (x := x * a)).2 hmem
  refine
    IsUnit.of_mul_eq_one
      (a := Ideal.Quotient.mk (P ^ n) x)
      (b := Ideal.Quotient.mk (P ^ n) a) ?_
  calc
    Ideal.Quotient.mk (P ^ n) x * Ideal.Quotient.mk (P ^ n) a
        = Ideal.Quotient.mk (P ^ n) (x * a) := by
            symm
            simp
    _ = 1 := hmk

/-- Quotients by powers of nonzero prime ideals in a Dedekind domain are principal ideal rings. -/
lemma isPrincipalIdealRing_quot_prime_pow {A : Type*} [CommRing A] [IsDedekindDomain A]
    {P : Ideal A} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {n : ℕ} (hn : n ≠ 0) :
    IsPrincipalIdealRing (A ⧸ P ^ n) := by
  classical
  haveI : P.IsPrime := hP
  have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hP hP0
  haveI : IsPrincipalIdealRing (Localization.AtPrime P) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (S := A) (p := P) (hp0 := hP0)
  let f : Localization.AtPrime P →+* A ⧸ P ^ n :=
    IsLocalization.lift (M := P.primeCompl) (S := Localization.AtPrime P)
      (g := Ideal.Quotient.mk (P ^ n))
      (fun y => isUnit_quotient_mk_of_not_mem hPmax (n := n) hn (x := y) y.2)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨algebraMap A (Localization.AtPrime P) x, ?_⟩
    simp [f]
  exact IsPrincipalIdealRing.of_surjective f hf

/-- Let $A$ be a Dedekind domain and $\mathfrak{a} \neq 0$ an ideal in $A$. Show that every ideal in
 $A/\mathfrak{a}$ is principal. -/
theorem isPrincipalIdealRing_quot_of_isDedekind {A : Type} [CommRing A]
    [IsDedekindDomain A] (a : Ideal A) (ha : a ≠ ⊥) :
    IsPrincipalIdealRing (A ⧸ a) := by
  classical
  let e := IsDedekindDomain.quotientEquivPiFactors (I := a) ha
  have hfactor :
      ∀ P : (factors a).toFinset,
        IsPrincipalIdealRing (A ⧸ (P : Ideal A) ^ (Multiset.count (P : Ideal A) (factors a))) := by
    intro P
    have hprime : Prime (P : Ideal A) :=
      prime_of_factor _ (Multiset.mem_toFinset.mp P.prop)
    have hPprime : (P : Ideal A).IsPrime := Ideal.isPrime_of_prime hprime
    have hP0 : (P : Ideal A) ≠ ⊥ := by
      simpa using hprime.ne_zero
    have hn : Multiset.count (P : Ideal A) (factors a) ≠ 0 := by
      exact (Multiset.count_ne_zero).2 (Multiset.mem_toFinset.mp P.prop)
    exact isPrincipalIdealRing_quot_prime_pow (A := A) (P := (P : Ideal A)) hPprime hP0 hn
  have hprod :
      IsPrincipalIdealRing
        (∀ P : (factors a).toFinset,
          A ⧸ (P : Ideal A) ^ (Multiset.count (P : Ideal A) (factors a))) :=
    (isPrincipalIdealRing_pi_iff).2 hfactor
  letI :
      IsPrincipalIdealRing
        (∀ P : (factors a).toFinset,
          A ⧸ (P : Ideal A) ^ (Multiset.count (P : Ideal A) (factors a))) :=
    hprod
  exact IsPrincipalIdealRing.of_surjective (f := e.symm.toRingHom) e.symm.surjective

import Mathlib
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

local infixl:50 " ~ᵤ " => Associated

/-- If every element of a multiset is associated to `q`, then the product is associated to a power
of `q`. This is a convenient way to turn a UFD prime-factor multiset into a single power. -/
private lemma multiset_prod_associated_pow {M : Type*} [CommMonoid M] {q : M} :
    ∀ s : Multiset M, (∀ a ∈ s, a ~ᵤ q) → s.prod ~ᵤ q ^ s.card := by
  classical
  intro s
  refine s.induction_on (by simp) ?_
  intro a s ih hs
  have ha : a ~ᵤ q := hs a (by simp)
  have hs' : ∀ b ∈ s, b ~ᵤ q := fun b hb => hs b (by simp [hb])
  simpa [Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_assoc, mul_left_comm, mul_comm] using
    ha.mul_mul (ih hs')

private lemma multiset_prod_associated_pow_of_associated_or_isUnit {M : Type*} [CommMonoid M] {p : M} :
    ∀ s : Multiset M, (∀ a ∈ s, a ~ᵤ p ∨ IsUnit a) → ∃ n : ℕ, s.prod ~ᵤ p ^ n := by
  classical
  intro s
  refine s.induction_on ?_ ?_
  · intro _
    exact ⟨0, by simp⟩
  · intro a s ih hs
    have ha : a ~ᵤ p ∨ IsUnit a := hs a (by simp)
    have hs' : ∀ b ∈ s, b ~ᵤ p ∨ IsUnit b := fun b hb => hs b (by simp [hb])
    rcases ih hs' with ⟨n, hn⟩
    rcases ha with ha | ha
    · refine ⟨n + 1, ?_⟩
      simpa [Multiset.prod_cons, pow_succ, mul_assoc, mul_left_comm, mul_comm] using ha.mul_mul hn
    · refine ⟨n, ?_⟩
      have : a * s.prod ~ᵤ s.prod := associated_unit_mul_left (a := s.prod) (u := a) ha
      simpa [Multiset.prod_cons] using this.trans hn

/-- In a UFD where every prime element is associated to either `p` or `q`, any nonzero element not
divisible by `p` is associated to a power of `q`. -/
private lemma associated_pow_of_not_dvd {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {p q x : R} (_hp : Prime p)
    (h : ∀ {y : R}, Prime y → y ~ᵤ p ∨ y ~ᵤ q) (hx0 : x ≠ 0) (hx : ¬ p ∣ x) :
    ∃ n : ℕ, x ~ᵤ q ^ n := by
  classical
  obtain ⟨f, hf, hfx⟩ := UniqueFactorizationMonoid.exists_prime_factors x hx0
  have hqf : ∀ b ∈ f, b ~ᵤ q := by
    intro b hb
    have hb' : Prime b := hf b hb
    rcases h hb' with hbp | hbq
    · exfalso
      have hp_dvd_b : p ∣ b := by
        rcases hbp.symm with ⟨u, rfl⟩
        exact dvd_mul_of_dvd_left dvd_rfl _
      have hp_dvd_prod : p ∣ f.prod := dvd_trans hp_dvd_b (Multiset.dvd_prod hb)
      have hp_dvd_x : p ∣ x := (Associated.dvd_iff_dvd_right hfx).1 hp_dvd_prod
      exact hx hp_dvd_x
    · exact hbq
  refine ⟨f.card, ?_⟩
  exact hfx.symm.trans (multiset_prod_associated_pow (q := q) f hqf)

/-- With only two nonassociate prime elements up to associates, `p + q` must be a unit. -/
private lemma isUnit_add_of_primes {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {p q : R} (hp : Prime p) (hq : Prime q) (hpq : ¬ p ~ᵤ q)
    (h : ∀ {x : R}, Prime x → x ~ᵤ p ∨ x ~ᵤ q) :
    IsUnit (p + q) := by
  classical
  have hpq0 : p + q ≠ 0 := by
    intro h0
    apply hpq
    have : p = -q := eq_neg_of_add_eq_zero_left h0
    rw [this]
    exact Associated.neg_left (Associated.rfl : (q : R) ~ᵤ q)
  by_contra hunit
  obtain ⟨r, hr, hrdvd⟩ := WfDvdMonoid.exists_irreducible_factor (a := p + q) hunit hpq0
  have hr' : Prime r := (UniqueFactorizationMonoid.irreducible_iff_prime).1 hr
  rcases h hr' with hrp | hrq
  · have hp_dvd : p ∣ p + q := (Associated.dvd_iff_dvd_left hrp).1 hrdvd
    have hp_dvd_q : p ∣ q := by
      simpa [add_sub_cancel_left] using (dvd_sub hp_dvd dvd_rfl)
    exact hpq (Prime.associated_of_dvd hp hq hp_dvd_q)
  · have hq_dvd : q ∣ p + q := (Associated.dvd_iff_dvd_left hrq).1 hrdvd
    have hq_dvd_p : q ∣ p := by
      simpa [add_sub_cancel_right] using (dvd_sub hq_dvd dvd_rfl)
    exact hpq (Prime.associated_of_dvd hq hp hq_dvd_p).symm

/-- A nontrivial prime ideal of a UFD contains a prime element. -/
private lemma Ideal.IsPrime.exists_prime_mem_of_ne_bot {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {I : Ideal R} (hI : I.IsPrime) (hne : I ≠ ⊥) :
    ∃ x : R, Prime x ∧ x ∈ I := by
  classical
  obtain ⟨a, haI, ha0⟩ := I.ne_bot_iff.mp hne
  obtain ⟨f, hf, hfa⟩ := UniqueFactorizationMonoid.exists_prime_factors a ha0
  rcases hfa with ⟨u, hu⟩
  have hprod : f.prod ∈ I := by
    have : f.prod * (u : R) ∈ I := by simpa [hu] using haI
    simpa [mul_assoc] using I.mul_mem_right (↑u⁻¹) this
  rcases (hI.multiset_prod_mem_iff_exists_mem f).1 hprod with ⟨p, hp, hpI⟩
  exact ⟨p, hf p hp, hpI⟩

/-- In the two-prime situation, localizing at `(r)` yields a PID: any nonzero prime ideal in the
localization must be maximal, so all irreducibles are associated. -/
private lemma pid_localizationAtPrime_span_of_two_primes {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {r s : R} (hr : Prime r) (hs : Prime s) (hrs : ¬ r ~ᵤ s)
    (h : ∀ {x : R}, Prime x → x ~ᵤ r ∨ x ~ᵤ s)
    [(Ideal.span ({r} : Set R) : Ideal R).IsPrime] :
    IsPrincipalIdealRing (Localization.AtPrime (Ideal.span ({r} : Set R))) := by
  classical
  let P : Ideal R := Ideal.span ({r} : Set R)
  haveI : P.IsPrime := by
    simpa [P] using (inferInstance : (Ideal.span ({r} : Set R) : Ideal R).IsPrime)
  let S := Localization.AtPrime P
  have hs_not_mem : (s : R) ∉ P := by
    intro hsP
    have hr_dvd_s : r ∣ s := (Ideal.mem_span_singleton).1 hsP
    exact hrs (Prime.associated_of_dvd hr hs hr_dvd_s)
  have hsUnit : IsUnit (algebraMap R S s) := by
    simpa using IsLocalization.map_units (S := S) (M := P.primeCompl) (⟨s, hs_not_mem⟩ : P.primeCompl)

  have hmax_span :
      (Ideal.span ({algebraMap R S r} : Set S) : Ideal S) = IsLocalRing.maximalIdeal S := by
    have hmap :
        Ideal.map (algebraMap R S) P = IsLocalRing.maximalIdeal S := by
      simpa [S] using (Localization.AtPrime.map_eq_maximalIdeal (I := P) (R := R))
    simpa [P, Ideal.map_span, Set.image_singleton] using hmap

  have hr0 : (algebraMap R S r) ≠ 0 := by
    have hM : P.primeCompl ≤ nonZeroDivisors R := Ideal.primeCompl_le_nonZeroDivisors P
    intro hr0
    have : (r : R) = 0 :=
      (IsLocalization.to_map_eq_zero_iff (S := S) (M := P.primeCompl) hM).1 hr0
    exact hr.ne_zero this

  have hirr : Irreducible (algebraMap R S r) := by
    have hspan_prime : (Ideal.span ({algebraMap R S r} : Set S) : Ideal S).IsPrime := by
      have : (IsLocalRing.maximalIdeal S).IsPrime :=
        (IsLocalRing.maximalIdeal.isMaximal S).isPrime
      simpa [hmax_span] using this
    have hprime : Prime (algebraMap R S r) :=
      (Ideal.span_singleton_prime (p := algebraMap R S r) hr0).1 hspan_prime
    exact hprime.irreducible

  have hfactor :
      IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization S := by
    refine ⟨algebraMap R S r, hirr, ?_⟩
    intro x hx0
    rcases IsLocalization.exists_mk'_eq (S := S) P.primeCompl x with ⟨a, t, rfl⟩
    have ha0 : a ≠ 0 := IsLocalization.ne_zero_of_mk'_ne_zero (S := S) (x := a) (y := t) hx0
    obtain ⟨f, hf, hfa⟩ := UniqueFactorizationMonoid.exists_prime_factors a ha0
    let sf : Multiset S := f.map (algebraMap R S)
    have hsf : ∀ b ∈ sf, b ~ᵤ algebraMap R S r ∨ IsUnit b := by
      intro b hb
      rcases Multiset.mem_map.1 hb with ⟨c, hc, rfl⟩
      have hc' : Prime c := hf c hc
      rcases h hc' with hcr | hcs
      · exact Or.inl (Associated.map (algebraMap R S) hcr)
      · have hcs' : (algebraMap R S c) ~ᵤ (algebraMap R S s) :=
          Associated.map (algebraMap R S) hcs
        exact Or.inr (hcs'.symm.isUnit hsUnit)
    obtain ⟨n, hn⟩ :=
      multiset_prod_associated_pow_of_associated_or_isUnit (p := algebraMap R S r) sf hsf
    have hprod_eq : algebraMap R S f.prod = sf.prod := by
      simpa [sf] using (Multiset.prod_hom f (algebraMap R S).toMonoidHom).symm
    have hmap : sf.prod ~ᵤ algebraMap R S a := by
      have : (algebraMap R S) f.prod ~ᵤ (algebraMap R S) a :=
        Associated.map (algebraMap R S) hfa
      simpa [hprod_eq] using this
    have hmk : IsLocalization.mk' S a t ~ᵤ algebraMap R S a := by
      have htUnit : IsUnit (algebraMap R S (t : R)) := IsLocalization.map_units S t
      rcases htUnit with ⟨u, hu⟩
      refine ⟨u, ?_⟩
      rw [hu]
      exact IsLocalization.mk'_spec (S := S) a t
    refine ⟨n, ?_⟩
    exact (hmk.trans (hmap.symm.trans hn)).symm

  letI : IsDomain S := IsLocalization.isDomain_of_atPrime (S := S) (P := P)
  letI : IsDiscreteValuationRing S :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization (R := S) hfactor
  have : IsPrincipalIdealRing S := by infer_instance
  simpa [S, P] using this

/-- Let $R$ be a UFD with two nonassociate prime elements $p$ and $q$ such that every prime
element is an associate of either $p$ or $q$.  Prove that $R$ is a PID. -/
theorem isPrincipalIdealRing_of_associated_or_associated {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {p q : R} (hp : Prime p) (hq : Prime q) (hpq : ¬ Associated p q)
    (h : ∀ {x : R}, Prime x → Associated x p ∨ Associated x q) :
    IsPrincipalIdealRing R := by
  classical

  have hmax :
      ∀ (M : Ideal R), M.IsMaximal →
        M = Ideal.span ({p} : Set R) ∨ M = Ideal.span ({q} : Set R) := by
    intro M hM
    have hunit : IsUnit (p + q) := isUnit_add_of_primes hp hq hpq h
    have hMnebot : M ≠ ⊥ := by
      intro hbot
      subst hbot
      have hspanp_ne_top : (Ideal.span ({p} : Set R) : Ideal R) ≠ ⊤ := by
        intro ht
        exact hp.not_unit ((Ideal.span_singleton_eq_top).1 ht)
      have hboteq : (⊥ : Ideal R) = Ideal.span ({p} : Set R) :=
        Ideal.IsMaximal.eq_of_le hM hspanp_ne_top bot_le
      have : (p : R) = 0 := by
        have : p ∈ (⊥ : Ideal R) := by
          simpa [hboteq] using (Ideal.subset_span (by simp : p ∈ ({p} : Set R)))
        simpa using this
      exact hp.ne_zero this

    have hM' : M.IsPrime := hM.isPrime
    obtain ⟨r, hrprime, hrM⟩ := Ideal.IsPrime.exists_prime_mem_of_ne_bot (I := M) hM' hMnebot
    have hp_or_hq : p ∈ M ∨ q ∈ M := by
      rcases h hrprime with hrp | hrq
      · left
        rcases hrp with ⟨u, rfl⟩
        simpa [mul_assoc] using M.mul_mem_right (↑u) hrM
      · right
        rcases hrq with ⟨u, rfl⟩
        simpa [mul_assoc] using M.mul_mem_right (↑u) hrM

    have hnot_both : ¬ (p ∈ M ∧ q ∈ M) := by
      rintro ⟨hpM, hqM⟩
      have : p + q ∈ M := M.add_mem hpM hqM
      have htop : M = ⊤ := Ideal.eq_top_of_isUnit_mem (I := M) this hunit
      exact hM.ne_top htop

    rcases hp_or_hq with hpM | hqM
    · left
      have hspanp_le : Ideal.span ({p} : Set R) ≤ M := (Ideal.span_singleton_le_iff_mem (I := M)).2 hpM
      have hle : M ≤ Ideal.span ({p} : Set R) := by
        intro a ha
        by_cases ha0 : a = 0
        · simp [ha0]
        by_contra hpa
        have hpa' : ¬ p ∣ a := by
          simpa [Ideal.mem_span_singleton] using hpa
        rcases associated_pow_of_not_dvd (p := p) (q := q) hp h ha0 hpa' with ⟨n, han⟩
        rcases han with ⟨u, hu⟩
        have hqpow : q ^ n ∈ M := by
          have : a * (u : R) ∈ M := M.mul_mem_right (↑u) ha
          simpa [hu] using this
        have hqM' : q ∈ M := hM'.mem_of_pow_mem n hqpow
        exact hnot_both ⟨hpM, hqM'⟩
      exact le_antisymm hle hspanp_le
    · right
      have hspanq_le : Ideal.span ({q} : Set R) ≤ M := (Ideal.span_singleton_le_iff_mem (I := M)).2 hqM
      have hle : M ≤ Ideal.span ({q} : Set R) := by
        intro a ha
        by_cases ha0 : a = 0
        · simp [ha0]
        by_contra hqa
        have hswap : ∀ {x : R}, Prime x → x ~ᵤ q ∨ x ~ᵤ p := by
          intro x hx
          simpa [or_comm] using (h hx)
        have hqa' : ¬ q ∣ a := by
          simpa [Ideal.mem_span_singleton] using hqa
        rcases associated_pow_of_not_dvd (p := q) (q := p) hq hswap ha0 hqa' with ⟨n, han⟩
        rcases han with ⟨u, hu⟩
        have hppow : p ^ n ∈ M := by
          have : a * (u : R) ∈ M := M.mul_mem_right (↑u) ha
          simpa [hu] using this
        have hpM' : p ∈ M := hM'.mem_of_pow_mem n hppow
        exact hnot_both ⟨hpM', hqM⟩
      exact le_antisymm hle hspanq_le

  have hfinite : Finite (MaximalSpectrum R) := by
    classical
    have hMax :
        ∀ M : MaximalSpectrum R,
          M.asIdeal = Ideal.span ({p} : Set R) ∨ M.asIdeal = Ideal.span ({q} : Set R) :=
      fun M => hmax M.asIdeal M.isMaximal
    let f : MaximalSpectrum R → Fin 2 := fun M =>
      if M.asIdeal = Ideal.span ({p} : Set R) then 0 else 1
    have hf : Function.Injective f := by
      intro M N hMN
      by_cases hMp : M.asIdeal = Ideal.span ({p} : Set R)
      · have hNp : N.asIdeal = Ideal.span ({p} : Set R) := by
          by_contra hNp
          have hMN' := hMN
          simp [f, hMp, hNp] at hMN'
        ext
        simp [hMp, hNp]
      · have hMq : M.asIdeal = Ideal.span ({q} : Set R) := by
          rcases hMax M with hMp' | hMq
          · exact (hMp hMp').elim
          · exact hMq
        have hNp : N.asIdeal ≠ Ideal.span ({p} : Set R) := by
          intro hNp
          have hMN' := hMN
          simp [f, hMp, hNp] at hMN'
        have hNq : N.asIdeal = Ideal.span ({q} : Set R) := by
          rcases hMax N with hNp' | hNq
          · exact (hNp hNp').elim
          · exact hNq
        ext
        simp [hMq, hNq]
    exact Finite.of_injective f hf

  classical
  haveI : Finite (MaximalSpectrum R) := hfinite

  refine
    isPrincipalIdealRing_of_isPrincipalIdealRing_isLocalization_maximal (R := R)
      (Rₚ := fun P _ => Localization.AtPrime P) ?_
  intro P instP
  have hP : P = Ideal.span ({p} : Set R) ∨ P = Ideal.span ({q} : Set R) := hmax P instP
  rcases hP with rfl | rfl
  · -- The localization at `(p)` has a unique irreducible class, hence is a PID.
    simpa using
      (pid_localizationAtPrime_span_of_two_primes (R := R) (r := p) (s := q) hp hq hpq h)
  · have hswap : ∀ {x : R}, Prime x → x ~ᵤ q ∨ x ~ᵤ p := by
      intro x hx
      simpa [or_comm] using (h hx)
    have hqp : ¬ (q : R) ~ᵤ p := fun hqp => hpq hqp.symm
    simpa using
      (pid_localizationAtPrime_span_of_two_primes (R := R) (r := q) (s := p) hq hp hqp hswap)

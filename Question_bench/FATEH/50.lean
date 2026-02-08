import Mathlib

open MvPolynomial

-- `ℤ` is Jacobson: every prime ideal is an intersection of maximal ideals.
lemma int_isJacobsonRing : IsJacobsonRing ℤ := by
  classical
  refine (isJacobsonRing_iff_sInf_maximal).2 ?_
  intro I hI
  by_cases hIbot : I = ⊥
  · refine ⟨{J : Ideal ℤ | J.IsMaximal}, ?_, ?_⟩
    · intro J hJ
      exact Or.inl hJ
    · subst hIbot
      ext z
      constructor
      · intro hz
        have hz0 : z = 0 := by simpa using hz
        subst hz0
        exact (Ideal.mem_sInf).2 (by intro J hJ; exact Ideal.zero_mem J)
      · intro hz
        by_contra hz0
        have hz0' : z ≠ 0 := by
          simpa [Ideal.mem_bot] using hz0
        obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (z.natAbs + 1)
        have hpgt : z.natAbs < p := lt_of_lt_of_le (Nat.lt_succ_self _) hpge
        haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
        have hmax : (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ).IsMaximal := by
          simpa using (Int.ideal_span_isMaximal_of_prime p)
        have hzmem : z ∈ (Ideal.span ({(p : ℤ)} : Set ℤ) : Ideal ℤ) := by
          exact (Ideal.mem_sInf (s := {J : Ideal ℤ | J.IsMaximal})).1 hz (by simpa using hmax)
        have hdiv : (p : ℤ) ∣ z := (Ideal.mem_span_singleton).1 hzmem
        have hdiv' : p ∣ z.natAbs := (Int.natCast_dvd).1 hdiv
        have hzabs0 : z.natAbs = 0 := Nat.eq_zero_of_dvd_of_lt hdiv' hpgt
        exact hz0' (Int.natAbs_eq_zero.mp hzabs0)
  · have hmax : I.IsMaximal := Ideal.IsPrime.isMaximal hI hIbot
    refine ⟨{I}, ?_, ?_⟩
    · intro J hJ
      have hJ' : J = I := by simpa using hJ
      left
      simpa [hJ'] using hmax
    · simp

/-- Let $m$ be a maximal ideal of $\mathbb{Z}[x_1, \dots, x_n]$ and $F = \mathbb{Z}[x_1, \dots, x_n]
/m$. Show that $F$ cannot have characteristic $0$. -/
theorem not_charZero_mvPolynomial_quot {n : ℕ} (m : Ideal (MvPolynomial (Fin n) ℤ))
    [hm : m.IsMaximal] : ¬ CharZero (MvPolynomial (Fin n) ℤ ⧸ m) := by
  classical
  intro hCharZero
  haveI := hCharZero
  letI : IsJacobsonRing ℤ := int_isJacobsonRing
  let f : ℤ →+* (MvPolynomial (Fin n) ℤ ⧸ m) := (Ideal.Quotient.mk m).comp C
  letI : Field (MvPolynomial (Fin n) ℤ ⧸ m) := Ideal.Quotient.field m
  have hf : f.IsIntegral :=
    MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing (P := m)
  haveI : (⊥ : Ideal (MvPolynomial (Fin n) ℤ ⧸ m)).IsMaximal := Ideal.bot_isMaximal
  have hcomap : (Ideal.comap f ⊥).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (⊥)
  have hcomap_ne_bot : (Ideal.comap f ⊥ : Ideal ℤ) ≠ ⊥ := by
    intro hbot
    have hmax' : (⊥ : Ideal ℤ).IsMaximal := by
      exact hbot ▸ hcomap
    have hspan_ne_top : (Ideal.span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ) ≠ ⊤ := by
      have hnotunit : ¬ IsUnit (2 : ℤ) := by
        simp [Int.isUnit_iff]
      simpa [Ideal.span_singleton_eq_top] using hnotunit
    have hlt : (⊥ : Ideal ℤ) < Ideal.span ({(2 : ℤ)} : Set ℤ) := by
      refine lt_of_le_of_ne bot_le ?_
      intro hEq
      have : (2 : ℤ) = 0 := (Ideal.span_singleton_eq_bot).1 hEq.symm
      exact (by decide : (2 : ℤ) ≠ 0) this
    have htop : (Ideal.span ({(2 : ℤ)} : Set ℤ) : Ideal ℤ) = ⊤ :=
      hmax'.out.2 _ hlt
    exact hspan_ne_top htop
  obtain ⟨a, ha⟩ := (Submodule.IsPrincipal.principal (Ideal.comap f ⊥))
  have ha' : (Ideal.comap f ⊥ : Ideal ℤ) = Ideal.span ({a} : Set ℤ) := by
    exact ha
  have ha0 : a ≠ 0 := by
    intro h0
    apply hcomap_ne_bot
    rw [ha']
    simp [h0]
  have ha_mem : a ∈ Ideal.comap f ⊥ := by
    rw [ha']
    exact Ideal.mem_span_singleton_self a
  have ha_zero : f a = 0 := by
    have : f a ∈ (⊥ : Ideal (MvPolynomial (Fin n) ℤ ⧸ m)) := (Ideal.mem_comap).1 ha_mem
    exact (Ideal.mem_bot).1 this
  have : ((a : ℤ) : MvPolynomial (Fin n) ℤ ⧸ m) = 0 := by
    simpa [f] using ha_zero
  exact ha0 (Int.cast_injective (by simpa using this))

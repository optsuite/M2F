import Mathlib

/--
Let \( D \) be a unique factorization domain.
Prove that if every nonzero prime ideal of \( D \) is maximal, then \( D \) is a principal
ideal domain.
-/
-- A nonzero prime ideal in a UFD is principal once every such ideal is maximal.
lemma prime_ideal_isPrincipal {D : Type} [CommRing D] [IsDomain D] [UniqueFactorizationMonoid D]
    (h : ∀ P : Ideal D, [P.IsPrime] → P ≠ ⊥ → P.IsMaximal) {P : Ideal D}
    (hP : P.IsPrime) (hPne : P ≠ ⊥) : P.IsPrincipal := by
  classical
  obtain ⟨p, hpP, hpprime⟩ :=
    Ideal.IsPrime.exists_mem_prime_of_ne_bot (I := P) hP hPne
  have hp0 : (p : D) ≠ 0 := hpprime.ne_zero
  have hspan_ne_bot : Ideal.span ({p} : Set D) ≠ ⊥ := by
    intro hbot
    exact hp0 ((Ideal.span_singleton_eq_bot).1 hbot)
  haveI : (Ideal.span ({p} : Set D)).IsPrime :=
    (Ideal.span_singleton_prime (p := p) (α := D) hp0).2 hpprime
  have hspan_max : (Ideal.span ({p} : Set D)).IsMaximal := h _ hspan_ne_bot
  have hle : Ideal.span ({p} : Set D) ≤ P :=
    (Ideal.span_singleton_le_iff_mem (I := P)).2 hpP
  have hEq : Ideal.span ({p} : Set D) = P :=
    (Ideal.IsMaximal.eq_of_le hspan_max hP.ne_top hle)
  simpa [hEq] using (inferInstance : (Ideal.span ({p} : Set D)).IsPrincipal)

theorem isPrincipalIdealRing_of_isPrime_ne_bot_isMaximal {D : Type} [CommRing D] [IsDomain D]
    [UniqueFactorizationMonoid D]
    (h : ∀ P : Ideal D, [P.IsPrime] → P ≠ ⊥ → P.IsMaximal) : IsPrincipalIdealRing D := by
  classical
  refine IsPrincipalIdealRing.of_prime_ne_bot ?_
  intro P hP hPne
  exact prime_ideal_isPrincipal h hP hPne

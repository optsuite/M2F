import Mathlib

open Polynomial

/--
Let \( R \subset R' \) be an extension of integral domains, and let \( \overline{R} \) be the integral closure of \( R \) in \( R' \).
Show that for any two monic polynomials \( f, g \in R'[t] \) with \( f \cdot g \in R[t] \),
we have \( f, g \in \overline{R}[t] \).-/
-- A monic polynomial that lifts from `R` can be lifted to a monic polynomial over `R`.
lemma exists_monic_lift_of_mem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {p : S[X]} (hp : p ∈ lifts (algebraMap R S)) (hmon : p.Monic) :
    ∃ q : R[X], map (algebraMap R S) q = p ∧ q.Monic := by
  obtain ⟨q, hq, -, hqmon⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic (f := algebraMap R S) hp hmon
  exact ⟨q, hq, hqmon⟩

-- Coefficients of a monic divisor of a monic polynomial over `R` are integral over `R`.
lemma coeff_integral_of_dvd {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]
    {p : R[X]} {q : S[X]} (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p.map (algebraMap R S)) (i : ℕ) : IsIntegral R (q.coeff i) := by
  have hq' : IsIntegral R q.leadingCoeff := by
    simpa [hq.leadingCoeff] using (isIntegral_one : IsIntegral R (1 : S))
  exact Polynomial.isIntegral_coeff_of_dvd p q hp hq' H i

-- If all coefficients are integral over `R`, the polynomial lifts to the integral closure.
lemma mem_lifts_integralClosure_of_coeff_integral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] {q : S[X]} (hq : ∀ i, IsIntegral R (q.coeff i)) :
    q ∈ lifts (integralClosure R S).subtype := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  exact ⟨⟨q.coeff n, hq n⟩, rfl⟩

theorem mem_polynomial_integral_closure_of_prod_mem_polynomial (R S : Type) [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [NoZeroSMulDivisors R S] (f g : S[X])
    (mem : f * g ∈ lifts (algebraMap R S)) (hf : f.Monic) (hg : g.Monic) :
    f ∈ lifts (integralClosure R S).subtype ∧ g ∈ lifts (integralClosure R S).subtype := by
  have hfg_monic : (f * g).Monic := hf.mul hg
  obtain ⟨p, hp_map, hp_monic⟩ :=
    exists_monic_lift_of_mem (R := R) (S := S) (p := f * g) mem hfg_monic
  have hdiv_f : f ∣ p.map (algebraMap R S) := by
    refine ⟨g, ?_⟩
    simp [hp_map]
  have hdiv_g : g ∣ p.map (algebraMap R S) := by
    refine ⟨f, ?_⟩
    simp [hp_map, mul_comm]
  have hf_int : ∀ i, IsIntegral R (f.coeff i) := by
    intro i
    exact coeff_integral_of_dvd (R := R) (S := S) hp_monic hf hdiv_f i
  have hg_int : ∀ i, IsIntegral R (g.coeff i) := by
    intro i
    exact coeff_integral_of_dvd (R := R) (S := S) hp_monic hg hdiv_g i
  exact
    ⟨mem_lifts_integralClosure_of_coeff_integral (R := R) (S := S) hf_int,
      mem_lifts_integralClosure_of_coeff_integral (R := R) (S := S) hg_int⟩

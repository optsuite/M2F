import Mathlib

open Polynomial
/- Let \( E \) be a field of characteristic zero. Consider a prime \( q \) and an element \( b
\in E^\times \) that isn’t a \( q \)-th power. Let \( E' = E(a) \) with \( a^q = b \). Show that
\( X^q - b \) is reducible over \( E \) if and only if \( [E' : E] < q \)-/
theorem not_irreducible_iff_finrank_lt
    {E E' : Type} [Field E] [CharZero E] [Field E'] [Algebra E E'] {q : ℕ}
    [Fact q.Prime] {b : E} (_hb : b ≠ 0) (_not_pow : ∀ c : E, c ^ q ≠ b)
    {a : E'} (ha : a ^ q = algebraMap E E' b)
    (haE : ⊤ = IntermediateField.adjoin E {a}) :
    ¬ Irreducible (X ^ q - C b) ↔ Module.finrank E E' < q := by
  classical
  let P : Polynomial E := X ^ q - C b
  have hq : q ≠ 0 := (Fact.out : Nat.Prime q).ne_zero
  have hPmonic : P.Monic := by
    simpa [P] using (monic_X_pow_sub_C b hq)
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hPnatdeg : P.natDegree = q := by
    dsimp [P]
    exact (natDegree_X_pow_sub_C (R:=E) (n:=q) (r:=b))
  have hroot : Polynomial.aeval a P = 0 := by
    simp [P, aeval_X_pow, ha]
  -- `a` is integral since it satisfies the monic polynomial `P`.
  have hInt : IsIntegral E a := by
    refine ⟨P, hPmonic, ?_⟩
    simpa using hroot
  -- The extension is simple, so finrank is the minpoly degree.
  have hfinrank : Module.finrank E E' = (minpoly E a).natDegree := by
    calc
      Module.finrank E E' = Module.finrank E (⊤ : IntermediateField E E') := by
        symm
        exact (IntermediateField.finrank_top' (F:=E) (E:=E'))
      _ = Module.finrank E (IntermediateField.adjoin E {a}) := by
        rw [haE]
      _ = (minpoly E a).natDegree := by
        simpa using (IntermediateField.adjoin.finrank (K:=E) (L:=E') (x:=a) hInt)
  have hmin_dvd : minpoly E a ∣ P := minpoly.dvd E a hroot
  have hdeg_le : (minpoly E a).natDegree ≤ q := by
    have h := natDegree_le_of_dvd hmin_dvd hPne
    simpa [hPnatdeg] using h
  have hIrred_iff : Irreducible P ↔ (minpoly E a).natDegree = q := by
    constructor
    · intro hIrred
      have hEq : P = minpoly E a :=
        minpoly.eq_of_irreducible_of_monic hIrred hroot hPmonic
      calc
        (minpoly E a).natDegree = P.natDegree := by
          simp [hEq.symm]
        _ = q := by
          simp [hPnatdeg]
    · intro hdeg
      have hdeg' : P.natDegree ≤ (minpoly E a).natDegree := by
        rw [hPnatdeg, hdeg]
      have hEq : P = minpoly E a :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le
          (minpoly.monic hInt) hPmonic hmin_dvd hdeg'
      have hmin_irred : Irreducible (minpoly E a) := minpoly.irreducible hInt
      simpa [hEq] using hmin_irred
  constructor
  · intro hnot
    have hdeg_ne : (minpoly E a).natDegree ≠ q := by
      intro hdeg
      exact hnot ((hIrred_iff).2 hdeg)
    have hdeg_lt : (minpoly E a).natDegree < q := lt_of_le_of_ne hdeg_le hdeg_ne
    simpa [hfinrank] using hdeg_lt
  · intro hlt
    have hdeg_lt : (minpoly E a).natDegree < q := by
      simpa [hfinrank] using hlt
    intro hIrred
    have hdeg_eq : (minpoly E a).natDegree = q := (hIrred_iff).1 hIrred
    exact (ne_of_lt hdeg_lt) hdeg_eq

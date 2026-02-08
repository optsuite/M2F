import Mathlib

open Polynomial

/-- Let $k$ be a finite field of size $q$. Show that the number of degree-$19$ monic irreducible
polynomials over $k$ is $\frac{q^{19} - q}{19}$. -/
-- A reusable prime-degree counting statement; the proof needs the standard finite-field counting
-- formula for monic irreducible polynomials.
-- In a finite extension of prime degree, minimal polynomials have degree `1` or the full degree.
lemma minpoly_natDegree_eq_one_or_eq_prime {F E : Type} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] {n : ℕ} (hn : Nat.Prime n) (hfinrank : Module.finrank F E = n)
    (x : E) : (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = n := by
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral (R := F) (A := E) x
  have hdiv : (minpoly F x).natDegree ∣ n := by
    simpa [hfinrank] using (minpoly.degree_dvd (K := F) (L := E) (x := x) hx)
  by_cases hdeg : (minpoly F x).natDegree = 1
  · exact Or.inl hdeg
  · right
    have : n = (minpoly F x).natDegree := (hn.dvd_iff_eq hdeg).1 hdiv
    exact this.symm

theorem card_monic_irreducible_prime_natDegree {F : Type} [Field F] [Fintype F] (n : ℕ)
    (hn : Nat.Prime n) :
    Nat.card { P : F[X] | P.Monic ∧ Irreducible P ∧ P.natDegree = n } =
    (Fintype.card F ^ n - Fintype.card F) / n := by
  classical
  let p := ringChar F
  haveI : CharP F p := by infer_instance
  haveI : Fact p.Prime := ⟨CharP.prime_ringChar (R := F)⟩
  haveI : NeZero n := ⟨hn.ne_zero⟩
  let E := FiniteField.Extension F p n
  haveI : Fintype E := Fintype.ofFinite E
  have hfinrank : Module.finrank F E = n := by
    simpa using (FiniteField.finrank_extension (k := F) (p := p) (n := n))

  let S : Type := { x : E // (minpoly F x).natDegree = n }
  let T : Type := { P : F[X] // P.Monic ∧ Irreducible P ∧ P.natDegree = n }

  -- Elements of `E` have minimal polynomial degree `1` or `n`, so degree `n` means not in `F`.
  have hdeg_or : ∀ x : E, (minpoly F x).natDegree = 1 ∨ (minpoly F x).natDegree = n :=
    minpoly_natDegree_eq_one_or_eq_prime (F := F) (E := E) hn hfinrank
  have hdeg_iff_not_range :
      ∀ x : E, (minpoly F x).natDegree = n ↔ x ∉ (algebraMap F E).range := by
    intro x
    have hdeg1 :
        (minpoly F x).natDegree = 1 ↔ x ∈ (algebraMap F E).range := by
      simpa using (minpoly.natDegree_eq_one_iff (A := F) (B := E) (x := x))
    constructor
    · intro hx hxrange
      have h1 : (minpoly F x).natDegree = 1 := (hdeg1).2 hxrange
      exact hn.ne_one (hx.symm.trans h1)
    · intro hxnot
      cases hdeg_or x with
      | inl h1 =>
          exact (hxnot ((hdeg1).1 h1)).elim
      | inr hn' => exact hn'

  have hcardS : Fintype.card S = Fintype.card E - Fintype.card F := by
    classical
    letI : Fintype { x : E // x ∈ (algebraMap F E).range } :=
      Set.fintypeRange (algebraMap F E)
    letI : Fintype { x : E // ∃ x_1, (algebraMap F E) x_1 = x } :=
      Set.fintypeRange (algebraMap F E)
    have hset :
        { x : E | (minpoly F x).natDegree = n } = { x : E | x ∉ (algebraMap F E).range } := by
      ext x
      exact hdeg_iff_not_range x
    have hcardS' : Fintype.card S = Fintype.card { x : E // x ∉ (algebraMap F E).range } := by
      simpa [S] using (Fintype.card_congr (Equiv.setCongr hset))
    have hcardCompl :
        Fintype.card { x : E // x ∉ (algebraMap F E).range } =
          Fintype.card E - Fintype.card { x : E // x ∈ (algebraMap F E).range } := by
      classical
      simpa using
        (Fintype.card_subtype_compl (p := fun x : E => x ∈ (algebraMap F E).range))
    have hcardRange :
        Fintype.card { x : E // ∃ x_1, (algebraMap F E) x_1 = x } = Fintype.card F := by
      classical
      simpa [Set.range] using
        (Set.card_range_of_injective (f := algebraMap F E)
          (FaithfulSMul.algebraMap_injective F E))
    calc
      Fintype.card S =
          Fintype.card E - Fintype.card { x : E // x ∈ (algebraMap F E).range } :=
        hcardS'.trans hcardCompl
      _ = Fintype.card E - Fintype.card F := by
        simp [hcardRange]

  -- Minimal-polynomial map from degree-`n` elements to monic irreducibles of degree `n`.
  let f : S → T := fun x => by
    have hx : IsIntegral F (x : E) :=
      Algebra.IsIntegral.isIntegral (R := F) (A := E) x
    exact ⟨minpoly F (x : E), minpoly.monic hx, minpoly.irreducible hx, x.property⟩

  have hsurj : Function.Surjective f := by
    intro P
    rcases P.property with ⟨hmonic, hirr, hdeg⟩
    haveI : Fact (Irreducible (P : F[X])) := ⟨hirr⟩
    have hfinrankP : Module.finrank F (AdjoinRoot (P : F[X])) = n := by
      simpa [hdeg] using
        (PowerBasis.finrank (AdjoinRoot.powerBasis' (R := F) (g := (P : F[X])) hmonic))
    have hnonempty :
        Nonempty (AdjoinRoot (P : F[X]) →ₐ[F] E) := by
      have hdiv : Module.finrank F (AdjoinRoot (P : F[X])) ∣ Module.finrank F E := by
        simp [hfinrankP, hfinrank]
      exact
        (FiniteField.nonempty_algHom_iff_finrank_dvd (K := AdjoinRoot (P : F[X])) (L := E)).2 hdiv
    obtain ⟨ϕ⟩ := hnonempty
    let x : E := ϕ (AdjoinRoot.root (P : F[X]))
    have hxminpoly : minpoly F x = P := by
      have hxroot : Polynomial.aeval x (P : F[X]) = 0 := by
        simp [x]
      exact (minpoly.eq_of_irreducible_of_monic hirr hxroot hmonic).symm
    refine ⟨⟨x, ?_⟩, ?_⟩
    · simp [hxminpoly, hdeg]
    · apply Subtype.ext
      simp [f, hxminpoly]

  haveI : Finite T := Finite.of_surjective f hsurj
  haveI : Fintype T := Fintype.ofFinite T

  have hfiber_of_x : ∀ x : S, Fintype.card { y : S // f y = f x } = n := by
    intro x
    let P : F[X] := minpoly F (x : E)
    have hdegP : P.natDegree = n := by
      simpa [P] using x.property
    have hxint : IsIntegral F (x : E) :=
      Algebra.IsIntegral.isIntegral (R := F) (A := E) x
    have hmonic : P.Monic := minpoly.monic hxint
    have hirr : Irreducible P := minpoly.irreducible hxint
    have hset : { y : E | minpoly F y = P } = P.rootSet E := by
      ext y
      constructor
      · intro hy
        have hy' : minpoly F y = P := by
          simpa using hy
        have hy0 : Polynomial.aeval y P = 0 := by
          calc
            Polynomial.aeval y P = Polynomial.aeval y (minpoly F y) := by simp [hy']
            _ = 0 := minpoly.aeval F y
        exact (Polynomial.mem_rootSet).2 ⟨hmonic.ne_zero, hy0⟩
      · intro hy
        have hy0 : Polynomial.aeval y P = 0 := (Polynomial.mem_rootSet).1 hy |>.2
        exact (minpoly.eq_of_irreducible_of_monic hirr hy0 hmonic).symm
    have hcardRoot : Fintype.card (P.rootSet E) = P.natDegree := by
      have hsep : P.Separable := PerfectField.separable_of_irreducible hirr
      have hsplit : (Polynomial.map (algebraMap F E) P).Splits := by
        simpa [P] using (IsGalois.splits (F := F) (E := E) (x := (x : E)))
      simpa using (Polynomial.card_rootSet_eq_natDegree (K := E) hsep hsplit)
    have hcardFiberE : Fintype.card { y : E // minpoly F y = P } = n := by
      have : Fintype.card { y : E // minpoly F y = P } = Fintype.card (P.rootSet E) := by
        classical
        simpa using (Fintype.card_congr (Equiv.setCongr hset))
      simpa [P, hdegP] using this.trans hcardRoot
    have hcardFiberS :
        Fintype.card { y : S // f y = f x } = Fintype.card { y : E // minpoly F y = P } := by
      classical
      refine Fintype.card_congr ?_
      refine
        { toFun := fun y =>
            ⟨y.1, by
              have hy' : minpoly F (y.1 : E) = minpoly F (x : E) := by
                simpa [f] using congrArg Subtype.val y.2
              simpa [P] using hy'⟩
          invFun := fun y =>
            ⟨⟨y.1, by simp [P, y.2, hdegP]⟩, by
              apply Subtype.ext
              simp [f, P, y.2]⟩
          left_inv := by
            intro y
            ext
            rfl
          right_inv := by
            intro y
            ext
            rfl }
    exact hcardFiberS.trans hcardFiberE

  have hfiber : ∀ t : T, Fintype.card { y : S // f y = t } = n := by
    intro t
    obtain ⟨x, rfl⟩ := hsurj t
    simpa using hfiber_of_x x

  have hcardS' : Fintype.card S = n * Fintype.card T := by
    classical
    have hcardSigma :
        Fintype.card S = ∑ t : T, Fintype.card { y : S // f y = t } := by
      simpa [Fintype.card_sigma] using
        (Fintype.card_congr (Equiv.sigmaFiberEquiv f)).symm
    have hcardSigma' : Fintype.card S = ∑ _t : T, n := by
      simpa [hfiber] using hcardSigma
    simpa [Nat.mul_comm] using hcardSigma'

  have hcardS_nat : Nat.card S = Fintype.card F ^ n - Fintype.card F := by
    have hcardE : Fintype.card E = Fintype.card F ^ n := by
      simpa [Nat.card_eq_fintype_card] using
        (FiniteField.natCard_extension (k := F) (p := p) (n := n))
    simpa [Nat.card_eq_fintype_card, hcardE] using hcardS

  have hcardT_nat : Nat.card T = (Fintype.card F ^ n - Fintype.card F) / n := by
    have hmul :
        Fintype.card F ^ n - Fintype.card F = n * Nat.card T := by
      have hcardS_nat' : Nat.card S = n * Nat.card T := by
        simpa [Nat.card_eq_fintype_card] using hcardS'
      calc
        Fintype.card F ^ n - Fintype.card F = Nat.card S := hcardS_nat.symm
        _ = n * Nat.card T := hcardS_nat'
    have hdiv : (Fintype.card F ^ n - Fintype.card F) / n = Nat.card T :=
      Nat.div_eq_of_eq_mul_right hn.pos hmul
    exact hdiv.symm

  simpa [T] using hcardT_nat

theorem card_monic_and_irreducible_and_natDegree_eq_19 {F : Type} (q : ℕ) [Field F]
    [Fintype F] (hF : Fintype.card F = q) :
    Nat.card { P : F[X] | P.Monic ∧ Irreducible P ∧ P.natDegree = 19 } =
    (q ^ 19 - q) / 19 := by
  classical
  have hprime : Nat.Prime 19 := by decide
  simpa [hF] using (card_monic_irreducible_prime_natDegree (F := F) 19 hprime)

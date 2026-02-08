import Mathlib

open scoped NumberField

/-- Modulo `3`, the Eisenstein norm form `a^2 + a*b + b^2` never takes the value `2`. -/
lemma eisenstein_form_ne_two_mod_three (a b : ZMod 3) :
    a ^ 2 + a * b + b ^ 2 ≠ (2 : ZMod 3) := by
  revert a b
  native_decide

/-- The quadratic form `a^2 - a*b + b^2` is nonnegative on integers. -/
lemma eisenstein_norm_nonneg (a b : ℤ) : 0 ≤ a ^ 2 - a * b + b ^ 2 := by
  -- Work in `ℝ` and complete the square:
  -- `a^2 - a*b + b^2 = (a - b/2)^2 + (3/4) * b^2 ≥ 0`.
  have h₁ : (0 : ℝ) ≤ ((a : ℝ) - (b : ℝ) / 2) ^ 2 := sq_nonneg _
  have h₂ : (0 : ℝ) ≤ (3 / 4 : ℝ) * (b : ℝ) ^ 2 := by
    have : (0 : ℝ) ≤ (b : ℝ) ^ 2 := sq_nonneg _
    nlinarith
  have h : (0 : ℝ) ≤ ((a : ℝ) - (b : ℝ) / 2) ^ 2 + (3 / 4 : ℝ) * (b : ℝ) ^ 2 :=
    add_nonneg h₁ h₂
  have h' : (0 : ℝ) ≤ ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
    -- `ring` normalizes the completed-square identity.
    simpa [pow_two] using (show (0 : ℝ) ≤ (a : ℝ) ^ 2 - (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2 by
      -- Rewrite the RHS as the completed square and apply `h`.
      have : (a : ℝ) ^ 2 - (a : ℝ) * (b : ℝ) + (b : ℝ) ^ 2 =
          ((a : ℝ) - (b : ℝ) / 2) ^ 2 + (3 / 4 : ℝ) * (b : ℝ) ^ 2 := by
        ring
      simpa [this] using h)
  have h'' :
      ((0 : ℤ) : ℝ) ≤ ((a ^ 2 - a * b + b ^ 2 : ℤ) : ℝ) := by
    simpa using h'
  exact (Int.cast_le).1 h''

/-- Show that a prime $p$ can be written as $p = a^2+ab+b^2$ with $a,b \in \mathbb{Z}$ if and only
if $p=3$ or $p \equiv 1 \pmod 3$. -/
theorem exists_sum_two_squares_iff_mod_three_eq_one (p : ℕ) (hp : p.Prime) :
    (∃ a b : ℤ, a ^ 2 + a * b + b ^ 2 = p) ↔ p = 3 ∨ p % 3 = 1 := by
  classical
  constructor
  · rintro ⟨a, b, hab⟩
    have hnot2 : p % 3 ≠ 2 := by
      intro hp2
      have hZ : ((a : ZMod 3) ^ 2 + (a : ZMod 3) * (b : ZMod 3) + (b : ZMod 3) ^ 2) =
          (p : ZMod 3) := by
        -- Cast the defining equality to `ZMod 3`.
        simpa using congrArg (fun x : ℤ => (x : ZMod 3)) hab
      have hpZ : (p : ZMod 3) = (2 : ZMod 3) := by
        -- `ZMod` equality is equivalent to equality of remainders.
        exact (ZMod.natCast_eq_natCast_iff' p 2 3).2 (by simp [hp2])
      exact eisenstein_form_ne_two_mod_three (a := (a : ZMod 3)) (b := (b : ZMod 3)) (by
        simp [hZ, hpZ])
    -- Since `p` is prime, `p % 3` cannot be `2`; the only possibilities are `0` and `1`.
    have hlt : p % 3 < 3 := Nat.mod_lt p (by decide)
    have hcases : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by
      have hle2 : p % 3 ≤ 2 := Nat.lt_succ_iff.mp hlt
      rcases Nat.lt_or_eq_of_le hle2 with hlt2 | hEq2
      · have hle1 : p % 3 ≤ 1 := Nat.lt_succ_iff.mp hlt2
        rcases Nat.lt_or_eq_of_le hle1 with hlt1 | hEq1
        · left
          exact (Nat.lt_one_iff.mp hlt1)
        · right; left; exact hEq1
      · right; right; exact hEq2
    rcases hcases with h0 | h1 | h2
    · left
      have hp3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
      have h' := (Nat.dvd_prime hp).1 hp3
      rcases h' with h' | h'
      · -- `3 ≠ 1`
        cases (by decide : (3 : ℕ) ≠ 1) h'
      · simpa [eq_comm] using h'
    · right; exact h1
    · exfalso; exact hnot2 h2
  · rintro (rfl | hp1)
    · refine ⟨1, 1, by norm_num⟩
    · -- Use the arithmetic of `𝓞 (ℚ(ζ₃))`, where norms are exactly `a^2 - a*b + b^2`.
      have hp_ne3 : p ≠ 3 := by
        intro hp3
        subst hp3
        -- `3 % 3 = 0 ≠ 1`
        have hp1' := hp1
        simp at hp1'
      have hp_not_dvd3 : ¬ p ∣ 3 := by
        intro hpd
        have h' := (Nat.dvd_prime Nat.prime_three).1 hpd
        rcases h' with h' | h'
        · exact hp.ne_one h'
        · exact hp_ne3 h'

      -- Set up the third cyclotomic field `K = ℚ(ζ₃)` and its ring of integers.
      let K := CyclotomicField 3 ℚ
      haveI : NumberField K := IsCyclotomicExtension.numberField {3} ℚ K
      let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
      haveI : IsPrincipalIdealRing (𝓞 K) := IsCyclotomicExtension.Rat.three_pid (K := K)
      haveI : Fact (Nat.Prime p) := ⟨hp⟩

      -- Choose a prime ideal `P` above `(p)` in `𝓞 K`.
      let pIdeal : Ideal ℤ := Ideal.span ({(p : ℤ)} : Set ℤ)
      haveI : pIdeal.IsMaximal := Int.ideal_span_isMaximal_of_prime p
      obtain ⟨⟨P, hPprime, hPlies⟩⟩ := pIdeal.nonempty_primesOver (S := 𝓞 K)
      haveI : P.IsPrime := hPprime
      haveI : P.LiesOver pIdeal := hPlies

      -- For `p ∤ 3`, the inertia degree is the order of `p` modulo `3`.
      have hpZ1 : (p : ZMod 3) = (1 : ZMod 3) := by
        exact (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simp [hp1])
      have horder : orderOf (p : ZMod 3) = 1 := by
        simp [hpZ1]
      have hinertia : pIdeal.inertiaDeg P = 1 := by
        simpa [horder] using
          (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd (m := 3) (p := p) (K := K) (P := P)
              hp_not_dvd3)

      -- Hence `absNorm P = p`.
      have habsP : Ideal.absNorm P = p := by
        have habsPow :
            Ideal.absNorm P = p ^ Module.finrank (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K ⧸ P) := by
          simpa [pIdeal] using
            (Ideal.absNorm_eq_pow_inertiaDeg' (R := 𝓞 K) (P := P) (p := p) hp)
        have hdeg :
            pIdeal.inertiaDeg P = Module.finrank (ℤ ⧸ pIdeal) (𝓞 K ⧸ P) := by
          simp
        have hinertia_finrank : Module.finrank (ℤ ⧸ pIdeal) (𝓞 K ⧸ P) = 1 := by
          simpa [hdeg] using hinertia
        have hinertia_finrank' :
            Module.finrank (ℤ ⧸ Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K ⧸ P) = 1 := by
          simpa [pIdeal] using hinertia_finrank
        simpa [hinertia_finrank'] using habsPow

      -- Since `𝓞 K` is a PID, `P` is principal, say `P = (g)`.
      haveI : P.IsPrincipal := IsPrincipalIdealRing.principal P
      let g : 𝓞 K := Submodule.IsPrincipal.generator P
      have hPg : Ideal.span ({g} : Set (𝓞 K)) = P := by
        simp [g]
      have habs_g : Ideal.absNorm (Ideal.span ({g} : Set (𝓞 K))) = p := by
        simpa [hPg] using habsP
      have hnorm_g_natAbs : (Algebra.norm ℤ g).natAbs = p := by
        simpa [Ideal.absNorm_span_singleton] using habs_g

      -- Express `g` in the integral power basis `1, ζ₃`.
      let pb : PowerBasis ℤ (𝓞 K) := hζ.integralPowerBasisOfPrimePow (p := 3) (k := 1)
      have hpb_gen : pb.gen = hζ.toInteger := by
        simp [pb]
      have hpb_dim : pb.dim = 2 := by
        -- `φ(3) = 2`
        have hdim : pb.dim = Nat.totient (3 ^ 1) := by
          simp [pb]
        have hphi : Nat.totient (3 ^ 1) = 2 := by
          simpa using (Nat.totient_prime_pow Nat.prime_three (by decide : 0 < 1))
        exact hdim.trans hphi

      -- Coefficients of `g` on the basis `{1, ζ₃}`.
      let e : Fin pb.dim ≃ Fin 2 := finCongr hpb_dim
      let a : ℤ := (pb.basis.repr g) (e.symm 0)
      let b : ℤ := (pb.basis.repr g) (e.symm 1)
      have hg_ab : g = a + b * pb.gen := by
        classical
        -- Expand `g` using `basis.sum_repr` and reindex the sum to `Fin 2` using `pb.dim = 2`.
        have hg : g = ∑ x : Fin pb.dim, (pb.basis.repr g x) • pb.basis x := by
          exact (pb.basis.sum_repr g).symm
        have hs :
            (∑ x : Fin pb.dim, (pb.basis.repr g x) • pb.basis x) =
              ∑ i : Fin 2, (pb.basis.repr g (e.symm i)) • pb.basis (e.symm i) := by
          simpa using
            (Fintype.sum_equiv e
              (fun x : Fin pb.dim => (pb.basis.repr g x) • pb.basis x)
              (fun i : Fin 2 => (pb.basis.repr g (e.symm i)) • pb.basis (e.symm i))
              (fun _ => rfl))
        -- Expand the `Fin 2`-sum and simplify `pb.basis i = pb.gen ^ (i : ℕ)`.
        have hg' :
            g = ∑ i : Fin 2, (pb.basis.repr g (e.symm i)) • pb.basis (e.symm i) := by
          exact hg.trans hs
        simpa [a, b, e, pb.basis_eq_pow, Fin.sum_univ_two, zsmul_eq_mul, pow_zero, pow_one] using hg'

      -- Compute `Algebra.norm ℤ g` in terms of `a,b`.
      have hnorm_g : Algebra.norm ℤ g = a ^ 2 - a * b + b ^ 2 := by
        -- Use the left-multiplication matrix in the power basis.
        -- In dimension `2` with minpoly `X^2 + X + 1`, the multiplication-by-ζ matrix is
        -- `![![0, -1], ![1, -1]]`, hence for `a + b*ζ` it is `![![a, -b], ![b, a - b]]`.
        have hminpoly : pb.minpolyGen = (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial ℤ) := by
          -- `minpolyGen = minpoly = cyclotomic 3 = X^2 + X + 1`.
          have h₁ : pb.minpolyGen = minpoly ℤ pb.gen := by
            exact PowerBasis.minpolyGen_eq pb
          -- `pb.gen` is a primitive `3`rd root of unity.
          have h₂ : minpoly ℤ pb.gen = Polynomial.cyclotomic 3 ℤ := by
            -- `pb.gen = hζ.toInteger` and `minpoly` of `ζ₃` is cyclotomic; transport to `𝓞 K`.
            have hc :
                Polynomial.cyclotomic 3 ℤ = minpoly ℤ (IsCyclotomicExtension.zeta 3 ℚ K) :=
              Polynomial.cyclotomic_eq_minpoly hζ (by decide : 0 < 3)
            have hc' : Polynomial.cyclotomic 3 ℤ = minpoly ℤ (hζ.toInteger : K) := by
              -- Rewrite the primitive root `ζ₃` as the coercion of `hζ.toInteger`.
              simpa using (hc.trans (by rw [← hζ.coe_toInteger]))
            -- Transport `minpoly` from `K` to `𝓞 K`.
            have hc'' : Polynomial.cyclotomic 3 ℤ = minpoly ℤ (hζ.toInteger : 𝓞 K) := by
              simpa using (hc'.trans (by rw [NumberField.RingOfIntegers.minpoly_coe (K := K) hζ.toInteger]))
            simpa [hpb_gen] using hc''.symm
          -- Assemble.
          -- (The `simp` normalizes `cyclotomic 3 ℤ` to `X^2 + X + 1`.)
          -- `pb.minpolyGen = cyclotomic 3 ℤ = X^2 + X + 1`.
          calc
            pb.minpolyGen = Polynomial.cyclotomic 3 ℤ := by simp [h₂]
            _ = Polynomial.X ^ 2 + Polynomial.X + 1 := by
              simp [Polynomial.cyclotomic_three]
        have hminpoly_minpoly : minpoly ℤ pb.gen = Polynomial.X ^ 2 + Polynomial.X + 1 := by
          have h₁ : pb.minpolyGen = minpoly ℤ pb.gen := by
            exact PowerBasis.minpolyGen_eq pb
          exact h₁.symm.trans hminpoly
        have hMgen :
            Matrix.reindex e e (Algebra.leftMulMatrix pb.basis pb.gen) =
              ![![ (0 : ℤ), (-1 : ℤ)], ![ (1 : ℤ), (-1 : ℤ)]] := by
          -- Evaluate `pb.leftMulMatrix` at `dim = 2` and the above `minpolyGen`, after reindexing.
          ext i j
          fin_cases i
          all_goals fin_cases j
          all_goals
            (simp [Matrix.reindex_apply, e, PowerBasis.leftMulMatrix, hpb_dim, hminpoly_minpoly]
              ; try simp [Polynomial.coeff_one])
        have hM :
            Matrix.reindex e e (Algebra.leftMulMatrix pb.basis (a + b * pb.gen)) =
              ![![a, -b], ![b, a - b]] := by
          classical
          let ψ : Matrix (Fin pb.dim) (Fin pb.dim) ℤ ≃ₐ[ℤ] Matrix (Fin 2) (Fin 2) ℤ :=
            Matrix.reindexAlgEquiv ℤ ℤ e
          have hψ_gen :
              ψ (Algebra.leftMulMatrix pb.basis pb.gen) =
                ![![ (0 : ℤ), (-1 : ℤ)], ![ (1 : ℤ), (-1 : ℤ)]] := by
            simpa [ψ] using hMgen
          have hψ_a :
              ψ (Algebra.leftMulMatrix pb.basis (a : 𝓞 K)) =
                algebraMap ℤ (Matrix (Fin 2) (Fin 2) ℤ) a := by
            simp [ψ]
          have hψ_b :
              ψ (Algebra.leftMulMatrix pb.basis (b : 𝓞 K)) =
                algebraMap ℤ (Matrix (Fin 2) (Fin 2) ℤ) b := by
            simp [ψ]
          have : ψ (Algebra.leftMulMatrix pb.basis (a + b * pb.gen)) =
              ![![a, -b], ![b, a - b]] := by
            -- Expand using multiplicativity/additivity, then compute in `Matrix (Fin 2) (Fin 2) ℤ`.
            have hadd :
                (Algebra.leftMulMatrix pb.basis) (↑a + ↑b * pb.gen) =
                  (Algebra.leftMulMatrix pb.basis) (↑a) +
                    (Algebra.leftMulMatrix pb.basis) (↑b * pb.gen) := by
              simp
            have hmul :
                (Algebra.leftMulMatrix pb.basis) (↑b * pb.gen) =
                  (Algebra.leftMulMatrix pb.basis) (↑b) *
                    (Algebra.leftMulMatrix pb.basis) pb.gen := by
              simp
            -- Rewrite using these algebra-morphism properties.
            rw [hadd]
            have haddψ :
                ψ ((Algebra.leftMulMatrix pb.basis) ↑a + (Algebra.leftMulMatrix pb.basis) (↑b * pb.gen)) =
                  ψ ((Algebra.leftMulMatrix pb.basis) ↑a) +
                    ψ ((Algebra.leftMulMatrix pb.basis) (↑b * pb.gen)) := by
              simp
            rw [haddψ]
            rw [hmul]
            have hmulψ :
                ψ ((Algebra.leftMulMatrix pb.basis) ↑b * (Algebra.leftMulMatrix pb.basis) pb.gen) =
                  ψ ((Algebra.leftMulMatrix pb.basis) ↑b) *
                    ψ ((Algebra.leftMulMatrix pb.basis) pb.gen) := by
              simp
            rw [hmulψ]
            rw [hψ_a, hψ_b, hψ_gen]
            have cast_apply (z : ℤ) (i j : Fin 2) :
                ((z : Matrix (Fin 2) (Fin 2) ℤ) i j) = if i = j then z else 0 := by
              simpa using
                (Matrix.algebraMap_matrix_apply
                  (R := ℤ) (α := ℤ) (n := Fin 2) (r := z) (i := i) (j := j))
            ext i j
            fin_cases i
            all_goals fin_cases j
            all_goals
              simp [Matrix.mul_apply, Matrix.add_apply, cast_apply, sub_eq_add_neg]
          simpa [ψ] using this
        -- Now take determinants.
        -- Replace `g` by its `a + b*pb.gen` expansion, then compute the determinant of a `2×2` matrix.
        rw [hg_ab, Algebra.norm_eq_matrix_det pb.basis]
        -- Reindex the determinant to `Fin 2` using `pb.dim = 2`.
        rw [← Matrix.det_reindex_self e (Algebra.leftMulMatrix pb.basis (a + b * pb.gen))]
        rw [hM, Matrix.det_fin_two]
        simp
        ring

      have hform_natAbs : (a ^ 2 - a * b + b ^ 2).natAbs = p := by
        simpa [hnorm_g] using hnorm_g_natAbs

      have hform_nonneg : 0 ≤ a ^ 2 - a * b + b ^ 2 := eisenstein_norm_nonneg a b
      have hform_int : (a ^ 2 - a * b + b ^ 2 : ℤ) = p := by
        -- Cast the `natAbs` equality back to `ℤ` using nonnegativity.
        have : ((a ^ 2 - a * b + b ^ 2).natAbs : ℤ) = p := by exact_mod_cast hform_natAbs
        simpa [Int.natAbs_of_nonneg hform_nonneg] using this

      -- Convert `a^2 - a*b + b^2 = p` to the requested `a^2 + a*b' + b'^2 = p` by `b' = -b`.
      refine ⟨a, -b, ?_⟩
      -- Clean up the coercion `(p : ℕ)` to `(p : ℤ)` on the RHS.
      -- `ring` takes care of the quadratic-form identity.
      have : a ^ 2 + a * (-b) + (-b) ^ 2 = (a ^ 2 - a * b + b ^ 2 : ℤ) := by ring
      simpa [this, hform_int]

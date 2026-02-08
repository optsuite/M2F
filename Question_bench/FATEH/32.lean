import Mathlib

open Polynomial

/- The Galois group of the splitting field of $x^4 - 2x^2 - 2$ over $\mathbb{Q}$ is the
dihedral group with eight elements-/
-- Eisenstein at 2 on the integral model gives irreducibility over ℚ.
lemma irreducible_X4_sub_2X2_sub_2 : Irreducible (X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]) := by
  classical
  -- Work over ℤ and use Gauss's lemma to pass to ℚ.
  let qZ : ℤ[X] := C (2 : ℤ) * X ^ 2 + C (2 : ℤ)
  let pZ : ℤ[X] := X ^ 4 - qZ
  let P : Ideal ℤ := Ideal.span ({2} : Set ℤ)
  have hP : P.IsPrime := by
    have hp : Prime (2 : ℤ) := (Nat.prime_iff_prime_int).1 (by decide : Nat.Prime 2)
    simpa [P] using
      (Ideal.span_singleton_prime (α := ℤ) (p := (2 : ℤ)) (by decide : (2 : ℤ) ≠ 0)).2 hp
  have hdeg_q_le : degree qZ ≤ (2 : ℕ) := by
    refine degree_add_le_of_degree_le ?_ ?_
    · simpa [mul_comm] using
        (degree_C_mul_X_pow_le (R := ℤ) (n := 2) (a := (2 : ℤ)))
    ·
      have hdegC : degree (C (2 : ℤ) : ℤ[X]) ≤ (0 : ℕ) := by
        simpa using (degree_C_le (a := (2 : ℤ)))
      exact hdegC.trans (by
        decide)
  have hdeg_q_lt : degree qZ < (4 : ℕ) :=
    lt_of_le_of_lt hdeg_q_le
      (WithBot.coe_lt_coe.mpr (by decide : (2 : ℕ) < (4 : ℕ)))
  have hmonic : pZ.Monic := by
    -- `pZ = X^4 - (2*X^2 + 2)` and the lower term has degree < 4.
    simpa [pZ] using (monic_X_pow_sub (p := qZ) (n := 4) hdeg_q_lt)
  have hprim : pZ.IsPrimitive := hmonic.isPrimitive
  have hfl : pZ.leadingCoeff ∉ P := by
    -- Leading coefficient is 1, which is not divisible by 2.
    have hnot : (1 : ℤ) ∉ P := by
      simp [P, Ideal.mem_span_singleton]
    simpa [hmonic.leadingCoeff, P] using hnot
  have hfP : ∀ n : ℕ, (↑n < degree pZ) → pZ.coeff n ∈ P := by
    intro n hn
    have hn' : n < 4 := by
      -- `degree pZ = 4` since the lower terms have degree < 4.
      have hdeg_pZ : degree pZ = (4 : WithBot ℕ) := by
        have hlt :
            degree (-qZ) < degree ((X : ℤ[X]) ^ 4) := by
          simpa [degree_neg] using hdeg_q_lt
        simpa [pZ, sub_eq_add_neg] using
          (degree_add_eq_left_of_degree_lt hlt)
      simpa [hdeg_pZ] using hn
    -- Enumerate the small degrees.
    interval_cases n
    ·
      simp [pZ, qZ, P, Ideal.mem_span_singleton]
    · simp [pZ, qZ, P]
    ·
      simp [pZ, qZ, P, Ideal.mem_span_singleton]
    · simp [pZ, qZ, P]
  have hfd0 : 0 < degree pZ := by
    have hdeg_pZ : degree pZ = (4 : WithBot ℕ) := by
      have hlt :
          degree (-qZ) < degree ((X : ℤ[X]) ^ 4) := by
        simpa [degree_neg] using hdeg_q_lt
      simpa [pZ, sub_eq_add_neg] using
        (degree_add_eq_left_of_degree_lt hlt)
    simp [hdeg_pZ]
  have h0 : pZ.coeff 0 ∉ P ^ 2 := by
    -- The constant term is -2, which is not divisible by 4.
    intro hmem
    have hmem' : pZ.coeff 0 ∈ (Ideal.span ({(4 : ℤ)} : Set ℤ)) := by
      simpa [P, Ideal.span_singleton_pow] using hmem
    have hdiv : (4 : ℤ) ∣ (-2 : ℤ) := by
      simpa [pZ, qZ, Ideal.mem_span_singleton] using hmem'
    exact (by decide : ¬ (4 : ℤ) ∣ (-2 : ℤ)) hdiv
  have hirrZ : Irreducible pZ :=
    Polynomial.irreducible_of_eisenstein_criterion hP hfl hfP hfd0 h0 hprim
  have hirrQ :
      Irreducible (pZ.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).1 hirrZ
  simpa [pZ, qZ, sub_sub] using hirrQ

-- A degree computation used to control the number of roots in the splitting field.
lemma natDegree_X4_sub_2X2_sub_2 : (X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]).natDegree = 4 := by
  have hdegX : (X ^ 4 : ℚ[X]).natDegree = 4 := by simp
  have hdegq : (2 * X ^ 2 + 2 : ℚ[X]).natDegree = 2 := by
    have h1 : (C (2 : ℚ) * X ^ 2 : ℚ[X]).natDegree = 2 := by
      simpa using
        (natDegree_C_mul_X_pow (R := ℚ) (n := 2) (a := (2 : ℚ)) (by decide))
    have hlt : (C (2 : ℚ) : ℚ[X]).natDegree < (C (2 : ℚ) * X ^ 2 : ℚ[X]).natDegree := by
      simp [h1]
    have h2' : (C (2 : ℚ) * X ^ 2 + C (2 : ℚ) : ℚ[X]).natDegree = 2 := by
      have h2 :=
        natDegree_add_eq_left_of_natDegree_lt
          (p := (C (2 : ℚ) * X ^ 2 : ℚ[X])) (q := (C (2 : ℚ) : ℚ[X])) hlt
      simpa [h1] using h2
    exact h2'
  have hneg : (-(2 * X ^ 2 + 2 : ℚ[X])).natDegree = 2 := by
    calc
      (-(2 * X ^ 2 + 2 : ℚ[X])).natDegree = (2 * X ^ 2 + 2 : ℚ[X]).natDegree := by
        exact natDegree_neg (2 * X ^ 2 + 2 : ℚ[X])
      _ = 2 := hdegq
  have hlt : (-(2 * X ^ 2 + 2 : ℚ[X])).natDegree < (X ^ 4 : ℚ[X]).natDegree := by
    rw [hneg, hdegX]
    decide
  have h :=
    natDegree_add_eq_left_of_natDegree_lt
      (p := (X ^ 4 : ℚ[X])) (q := (-(2 * X ^ 2 + 2 : ℚ[X]))) hlt
  calc
    (X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]).natDegree
        = (X ^ 4 + -(2 * X ^ 2 + 2) : ℚ[X]).natDegree := by
            simp [sub_eq_add_neg, add_comm, add_left_comm]
    _ = (X ^ 4 : ℚ[X]).natDegree := h
    _ = 4 := hdegX

-- A quadratic degree computation for the resolvent `X^2 - 2X - 2`.
lemma natDegree_X2_sub_2X_sub_2 : (X ^ 2 - 2 * X - 2 : ℚ[X]).natDegree = 2 := by
  have hdeg1 : (X ^ 2 + (-2 : ℚ[X])).natDegree = 2 := by
    simpa using (natDegree_X_pow_add_C (R := ℚ) (n := 2) (r := -2))
  have hdeg2 : (-(2 * X : ℚ[X])).natDegree = 1 := by
    calc
      (-(2 * X : ℚ[X])).natDegree = (2 * X : ℚ[X]).natDegree := by
        simpa using (natDegree_neg (2 * X : ℚ[X]))
      _ = 1 := by
        have h1 : (C (2 : ℚ) * X : ℚ[X]).natDegree = 1 := by
          simpa using (natDegree_C_mul_X (R := ℚ) (a := (2 : ℚ)) (by decide))
        simpa [mul_comm] using h1
  have hlt : (-(2 * X : ℚ[X])).natDegree < (X ^ 2 + (-2 : ℚ[X])).natDegree := by
    rw [hdeg2, hdeg1]
    decide
  have h :=
    natDegree_add_eq_left_of_natDegree_lt
      (p := (X ^ 2 + (-2 : ℚ[X]))) (q := (-(2 * X : ℚ[X]))) hlt
  calc
    (X ^ 2 - 2 * X - 2 : ℚ[X]).natDegree
        = (X ^ 2 + (-2 : ℚ[X]) + -(2 * X) : ℚ[X]).natDegree := by
            ring_nf
    _ = (X ^ 2 + (-2 : ℚ[X])).natDegree := h
    _ = 2 := hdeg1

-- The quadratic tower used to build a degree-8 comparison field.
noncomputable abbrev aux_q : ℚ[X] := X ^ 2 - 2 * X - 2
abbrev aux_F : Type := AdjoinRoot aux_q
noncomputable abbrev aux_u : aux_F := AdjoinRoot.root aux_q
noncomputable abbrev aux_r : aux_F[X] := X ^ 2 - C aux_u
abbrev aux_K : Type := AdjoinRoot aux_r
-- Note: `aux_s = X^2 + 2`.
noncomputable abbrev aux_s : aux_K[X] := X ^ 2 - C (-2 : aux_K)
abbrev aux_E : Type := AdjoinRoot aux_s

-- The defining relation for `aux_u` gives `aux_u * (2 - aux_u) = -2`.
lemma aux_u_mul_two_sub_aux_u : (aux_u : aux_F) * (2 - aux_u) = (-2 : aux_F) := by
  have h : aeval aux_u aux_q = (0 : aux_F) := by
    simpa [aux_q] using (AdjoinRoot.aeval_eq (f := aux_q) (p := aux_q))
  have h' : aux_u ^ 2 - 2 * aux_u - 2 = (0 : aux_F) := by
    simpa [aux_q] using h
  have h'' : aux_u ^ 2 = 2 * aux_u + 2 := by
    have h''' : aux_u ^ 2 - (2 * aux_u + 2) = (0 : aux_F) := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    exact sub_eq_zero.mp h'''
  calc
    (aux_u : aux_F) * (2 - aux_u) = 2 * aux_u - aux_u ^ 2 := by ring
    _ = 2 * aux_u - (2 * aux_u + 2) := by simpa [h'']
    _ = (-2 : aux_F) := by ring

-- The explicit quadratic tower has total degree 8 over ℚ.
lemma auxField_finrank_eq_8 : Module.finrank ℚ aux_E = 8 := by
  classical
  have hqdeg : aux_q.natDegree = 2 := by
    simpa [aux_q] using natDegree_X2_sub_2X_sub_2
  have hq0 : aux_q ≠ 0 := by
    intro hq
    have : (0 : ℕ) = 2 := by simpa [aux_q, hq] using hqdeg
    exact (by decide : (0 : ℕ) ≠ 2) this
  have hdeg_q : (aux_q : ℚ[X]).degree ≠ 0 := by
    simpa [degree_eq_natDegree hq0, hqdeg] using
      (show (2 : WithBot ℕ) ≠ 0 from by decide)
  haveI : Nontrivial aux_F := AdjoinRoot.nontrivial (R := ℚ) (f := aux_q) hdeg_q
  have hF : Module.finrank ℚ aux_F = 2 := by
    simpa [AdjoinRoot.powerBasis, hqdeg] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis (K := ℚ) (f := aux_q) hq0))
  have hrdeg : aux_r.natDegree = 2 := by
    simpa [aux_r] using (natDegree_X_pow_sub_C (R := aux_F) (n := 2) (r := aux_u))
  have hmonic_r : aux_r.Monic := by
    simpa [aux_r] using (monic_X_pow_sub_C (R := aux_F) (a := aux_u) (n := 2) (by decide))
  have hnotunit_r : ¬ IsUnit aux_r := by
    intro hunit
    have h1 : aux_r = 1 := (Monic.isUnit_iff hmonic_r).1 hunit
    have hdeg1 :
        aux_r.natDegree = 0 := by
      simpa [h1] using (Polynomial.natDegree_one : (1 : aux_F[X]).natDegree = 0)
    have : (2 : ℕ) = 0 := by
      simpa [hrdeg] using hdeg1
    exact (by decide : (2 : ℕ) ≠ 0) this
  have hspan_r : (Ideal.span ({aux_r} : Set aux_F[X])) ≠ ⊤ := by
    intro htop
    exact hnotunit_r ((Ideal.span_singleton_eq_top).1 htop)
  haveI : Nontrivial aux_K := by
    simpa [aux_K, AdjoinRoot] using
      (Ideal.Quotient.nontrivial_iff (R := aux_F[X])
        (I := Ideal.span ({aux_r} : Set aux_F[X]))).2 hspan_r
  have hK : Module.finrank aux_F aux_K = 2 := by
    simpa [AdjoinRoot.powerBasis', hrdeg] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis' (R := aux_F) (g := aux_r) hmonic_r))
  have hsdeg : aux_s.natDegree = 2 := by
    simpa [aux_s] using (natDegree_X_pow_sub_C (R := aux_K) (n := 2) (r := (-2 : aux_K)))
  have hmonic_s : aux_s.Monic := by
    simpa [aux_s] using
      (monic_X_pow_sub_C (R := aux_K) (a := (-2 : aux_K)) (n := 2) (by decide))
  have hE : Module.finrank aux_K aux_E = 2 := by
    simpa [AdjoinRoot.powerBasis', hsdeg] using
      (PowerBasis.finrank (AdjoinRoot.powerBasis' (R := aux_K) (g := aux_s) hmonic_s))
  haveI : Module.Free ℚ aux_F :=
    Module.Free.of_basis (AdjoinRoot.powerBasis (K := ℚ) (f := aux_q) hq0).basis
  haveI : Module.Free aux_F aux_K :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (R := aux_F) (g := aux_r) hmonic_r).basis
  haveI : Module.Free aux_K aux_E :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (R := aux_K) (g := aux_s) hmonic_s).basis
  have hFK : Module.finrank ℚ aux_K = 4 := by
    have h := (Module.finrank_mul_finrank (F := ℚ) (K := aux_F) (A := aux_K))
    have h' : (2 : ℕ) * 2 = Module.finrank ℚ aux_K := by
      simpa [hF, hK] using h
    simpa using h'.symm
  have hFE : Module.finrank ℚ aux_E = 8 := by
    have h := (Module.finrank_mul_finrank (F := ℚ) (K := aux_K) (A := aux_E))
    have h' :
        (Module.finrank ℚ aux_K) * (Module.finrank aux_K aux_E) =
          Module.finrank ℚ aux_E := by
      simpa using h
    have h'' : (4 : ℕ) * 2 = Module.finrank ℚ aux_E := by
      simpa [hFK, hE] using h'
    simpa using h''.symm
  exact hFE

-- Eisenstein at 2 on `X^2 - 2X - 2` gives irreducibility over ℚ.
lemma aux_q_irreducible : Irreducible (aux_q : ℚ[X]) := by
  classical
  let pZ : ℤ[X] := X ^ 2 - 2 * X - 2
  let P : Ideal ℤ := Ideal.span ({2} : Set ℤ)
  have hP : P.IsPrime := by
    have hp : Prime (2 : ℤ) := (Nat.prime_iff_prime_int).1 (by decide : Nat.Prime 2)
    simpa [P] using
      (Ideal.span_singleton_prime (α := ℤ) (p := (2 : ℤ)) (by decide : (2 : ℤ) ≠ 0)).2 hp
  have hpZ : pZ = X ^ 2 - (2 * X + (2 : ℤ[X])) := by ring
  have hdeg_q : degree (2 * X + (2 : ℤ[X])) < (2 : WithBot ℕ) := by
    have hdeg1 : degree (2 * X + (2 : ℤ[X])) ≤ (1 : ℕ) := by
      refine degree_add_le_of_degree_le ?_ ?_
      · simpa using
          (degree_C_mul_X_pow_le (R := ℤ) (n := 1) (a := (2 : ℤ)))
      ·
        have hdegC : degree (C (2 : ℤ) : ℤ[X]) ≤ (0 : ℕ) := by
          simpa using (degree_C_le (a := (2 : ℤ)))
        exact hdegC.trans (by
          simpa using (show (0 : ℕ) ≤ (1 : ℕ) from by decide))
    exact lt_of_le_of_lt hdeg1 (WithBot.coe_lt_coe.mpr (by decide : (1 : ℕ) < 2))
  have hdeg_pZ : degree pZ = (2 : WithBot ℕ) := by
    have hdegX : degree ((X : ℤ[X]) ^ 2) = (2 : WithBot ℕ) := by
      simpa using (degree_X_pow (R := ℤ) (n := 2))
    have hdeg_q'' :
        degree (-(2 * X + (2 : ℤ[X]))) < (2 : WithBot ℕ) := by
      rw [degree_neg]
      exact hdeg_q
    have hdeg_q' :
        degree (-(2 * X + (2 : ℤ[X]))) < degree ((X : ℤ[X]) ^ 2) := by
      simpa [hdegX] using hdeg_q''
    have h := degree_add_eq_left_of_degree_lt hdeg_q'
    calc
      degree pZ = degree (X ^ 2 + -(2 * X + (2 : ℤ[X]))) := by
        rw [hpZ, sub_eq_add_neg]
      _ = degree ((X : ℤ[X]) ^ 2) := h
      _ = (2 : WithBot ℕ) := hdegX
  have hmonic : pZ.Monic := by
    have h := monic_X_pow_sub (p := (2 * X + (2 : ℤ[X]))) (n := 2) hdeg_q
    simpa [hpZ] using h
  have hprim : pZ.IsPrimitive := hmonic.isPrimitive
  have hfl : pZ.leadingCoeff ∉ P := by
    have hnot : (1 : ℤ) ∉ P := by
      simpa [P, Ideal.mem_span_singleton] using
        (show ¬ (2 : ℤ) ∣ (1 : ℤ) from by decide)
    simpa [hmonic.leadingCoeff, P] using hnot
  have hfP : ∀ n : ℕ, (↑n < degree pZ) → pZ.coeff n ∈ P := by
    intro n hn
    have hn' : n < 2 := by
      simpa [hdeg_pZ] using hn
    interval_cases n
    ·
      have : (2 : ℤ) ∣ (-2 : ℤ) := by decide
      simpa [pZ, P, Ideal.mem_span_singleton] using this
    ·
      have : (2 : ℤ) ∣ (-2 : ℤ) := by decide
      simpa [pZ, P, Ideal.mem_span_singleton] using this
  have hfd0 : 0 < degree pZ := by
    simpa [hdeg_pZ] using
      (show (0 : WithBot ℕ) < (2 : WithBot ℕ) from by
        simpa using (show (0 : ℕ) < (2 : ℕ) from by decide))
  have h0 : pZ.coeff 0 ∉ P ^ 2 := by
    intro hmem
    have hmem' : pZ.coeff 0 ∈ (Ideal.span ({(4 : ℤ)} : Set ℤ)) := by
      simpa [P, Ideal.span_singleton_pow] using hmem
    have hdiv : (4 : ℤ) ∣ (-2 : ℤ) := by
      simpa [pZ, Ideal.mem_span_singleton] using hmem'
    exact (by decide : ¬ (4 : ℤ) ∣ (-2 : ℤ)) hdiv
  have hirrZ : Irreducible pZ :=
    Polynomial.irreducible_of_eisenstein_criterion hP hfl hfP hfd0 h0 hprim
  have hirrQ :
      Irreducible (pZ.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).1 hirrZ
  simpa [pZ, aux_q] using hirrQ

-- The base quadratic field `aux_F` has degree 2 over ℚ.
lemma aux_F_finrank_eq_2 : Module.finrank ℚ aux_F = 2 := by
  classical
  have hqdeg : aux_q.natDegree = 2 := by
    simpa [aux_q] using natDegree_X2_sub_2X_sub_2
  have hq0 : aux_q ≠ 0 := by
    intro hq
    have : (0 : ℕ) = 2 := by simpa [aux_q, hq] using hqdeg
    exact (by decide : (0 : ℕ) ≠ 2) this
  have hdeg_q : (aux_q : ℚ[X]).degree ≠ 0 := by
    simpa [degree_eq_natDegree hq0, hqdeg] using
      (show (2 : WithBot ℕ) ≠ 0 from by decide)
  haveI : Nontrivial aux_F := AdjoinRoot.nontrivial (R := ℚ) (f := aux_q) hdeg_q
  simpa [AdjoinRoot.powerBasis, hqdeg] using
    (PowerBasis.finrank (AdjoinRoot.powerBasis (K := ℚ) (f := aux_q) hq0))

-- The element `aux_u` is not a square in `aux_F`.
lemma aux_u_no_square [Fact (Irreducible aux_q)] : ∀ b : aux_F, b ^ 2 ≠ (aux_u : aux_F) := by
  classical
  have hF : Module.finrank ℚ aux_F = 2 := aux_F_finrank_eq_2
  haveI : FiniteDimensional ℚ aux_F :=
    FiniteDimensional.of_finrank_eq_succ (K := ℚ) (V := aux_F) (n := 1) (by
      simpa [hF])
  let p : ℚ[X] := X ^ 4 - 2 * X ^ 2 - 2
  have haux : aeval (aux_u : aux_F) aux_q = (0 : aux_F) := by
    simpa [aux_q] using (AdjoinRoot.aeval_eq (f := aux_q) (p := aux_q))
  have haux' : (aux_u : aux_F) ^ 2 - 2 * aux_u - 2 = (0 : aux_F) := by
    simpa [aux_q] using haux
  intro b hb
  have hb4 : b ^ 4 = (aux_u : aux_F) ^ 2 := by
    calc
      b ^ 4 = (b ^ 2) ^ 2 := by simp [pow_succ, mul_assoc]
      _ = (aux_u : aux_F) ^ 2 := by simpa [hb]
  have hroot : aeval b p = (0 : aux_F) := by
    simp [aeval_def, p, hb, hb4, haux']
  have hdiv : minpoly ℚ b ∣ p := minpoly.dvd ℚ b hroot
  have h_integral : IsIntegral ℚ b :=
    (IsAlgebraic.of_finite (R := ℚ) (A := aux_F) b).isIntegral
  have hmin_irr : Irreducible (minpoly ℚ b) := minpoly.irreducible h_integral
  have hp_irr : Irreducible p := by
    simpa [p] using irreducible_X4_sub_2X2_sub_2
  have hassoc : Associated (minpoly ℚ b) p :=
    Irreducible.associated_of_dvd hmin_irr hp_irr hdiv
  have hdiv' : p ∣ minpoly ℚ b := hassoc.symm.dvd
  have hdeg : (minpoly ℚ b).natDegree = 4 := by
    have hmin_ne0 : minpoly ℚ b ≠ 0 := minpoly.ne_zero h_integral
    have hp_ne0 : p ≠ 0 := hp_irr.ne_zero
    have hle1 : (minpoly ℚ b).natDegree ≤ p.natDegree := natDegree_le_of_dvd hdiv hp_ne0
    have hle2 : p.natDegree ≤ (minpoly ℚ b).natDegree := natDegree_le_of_dvd hdiv' hmin_ne0
    have hdeg' : (minpoly ℚ b).natDegree = p.natDegree := le_antisymm hle1 hle2
    simpa [p, natDegree_X4_sub_2X2_sub_2] using hdeg'
  have hle : (minpoly ℚ b).natDegree ≤ Module.finrank ℚ aux_F :=
    minpoly.natDegree_le (K := ℚ) (L := aux_F) (x := b)
  have hle' : (4 : ℕ) ≤ 2 := by
    simpa [hdeg, hF] using hle
  exact (by decide : ¬ (4 : ℕ) ≤ 2) hle'

-- A concrete real embedding of `aux_F` sending `aux_u` to `1 + √3`.
noncomputable def aux_F_to_Real : aux_F →+* ℝ := by
  refine AdjoinRoot.lift (algebraMap ℚ ℝ) (1 + Real.sqrt 3) ?_
  simp [aux_q]
  ring_nf
  have h0 : (0 : ℝ) ≤ 3 := by norm_num
  have hsq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    calc
      (Real.sqrt 3) ^ 2 = Real.sqrt 3 * Real.sqrt 3 := by simp [pow_two]
      _ = 3 := Real.mul_self_sqrt h0
  linarith

-- Lift the real embedding across the second adjunction to `aux_K`.
noncomputable def aux_K_to_Real : aux_K →+* ℝ := by
  refine AdjoinRoot.lift aux_F_to_Real (Real.sqrt (1 + Real.sqrt 3)) ?_
  simp [aux_r, aux_F_to_Real]
  have h0 : (0 : ℝ) ≤ 1 + Real.sqrt 3 := by
    have : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    nlinarith
  have hsq : (Real.sqrt (1 + Real.sqrt 3)) ^ 2 = (1 + Real.sqrt 3) := by
    calc
      (Real.sqrt (1 + Real.sqrt 3)) ^ 2 =
          Real.sqrt (1 + Real.sqrt 3) * Real.sqrt (1 + Real.sqrt 3) := by
            simp [pow_two]
      _ = 1 + Real.sqrt 3 := Real.mul_self_sqrt h0
  linarith

-- Irreducibility of the quadratic defining `aux_K`.
lemma aux_r_irreducible [Fact (Irreducible aux_q)] : Irreducible (aux_r : aux_F[X]) := by
  classical
  have hno : ∀ b : aux_F, b ^ 2 ≠ (aux_u : aux_F) := aux_u_no_square
  simpa [aux_r] using
    (X_pow_sub_C_irreducible_of_prime (K := aux_F) (p := 2) (hp := by decide)
      (a := (aux_u : aux_F)) hno)

-- Irreducibility of the quadratic defining `aux_E` via a real-embedding argument.
lemma aux_s_irreducible [Fact (Irreducible aux_q)] [Fact (Irreducible aux_r)] :
    Irreducible (aux_s : aux_K[X]) := by
  classical
  have hno : ∀ b : aux_K, b ^ 2 ≠ (-2 : aux_K) := by
    intro b hb
    have hb' : (aux_K_to_Real b) ^ 2 = (-2 : ℝ) := by
      have hb'' : aux_K_to_Real (b ^ 2) = aux_K_to_Real (-2) := by
        exact congrArg aux_K_to_Real hb
      have hb''' : aux_K_to_Real (b ^ 2) = (aux_K_to_Real b) ^ 2 := by
        calc
          aux_K_to_Real (b ^ 2) = aux_K_to_Real (b * b) := by
            simp only [pow_two]
          _ = aux_K_to_Real b * aux_K_to_Real b := by
            exact (aux_K_to_Real.map_mul b b)
          _ = (aux_K_to_Real b) ^ 2 := by
            simp only [pow_two]
      calc
        (aux_K_to_Real b) ^ 2 = aux_K_to_Real (b ^ 2) := hb'''.symm
        _ = aux_K_to_Real (-2) := hb''
        _ = (-2 : ℝ) := by
          have h2 : aux_K_to_Real (2 : aux_K) = (2 : ℝ) := by
            have h2' : (2 : aux_K) = 1 + 1 := by norm_num
            calc
              aux_K_to_Real (2 : aux_K) = aux_K_to_Real (1 + 1) := by
                rw [h2']
              _ = aux_K_to_Real 1 + aux_K_to_Real 1 := by
                exact aux_K_to_Real.map_add 1 1
              _ = (1 : ℝ) + (1 : ℝ) := by
                simp
              _ = (2 : ℝ) := by norm_num
          calc
            aux_K_to_Real (-2 : aux_K) = -aux_K_to_Real (2 : aux_K) := by
              exact aux_K_to_Real.map_neg (2 : aux_K)
            _ = (-2 : ℝ) := by
              simp [h2]
    have hnonneg : 0 ≤ (aux_K_to_Real b) ^ 2 := sq_nonneg _
    have hneg : (-2 : ℝ) < 0 := by norm_num
    have hlt : (-2 : ℝ) < (aux_K_to_Real b) ^ 2 := lt_of_lt_of_le hneg hnonneg
    exact (ne_of_gt hlt) hb'
  simpa [aux_s] using
    (X_pow_sub_C_irreducible_of_prime (K := aux_K) (p := 2) (hp := by decide)
      (a := (-2 : aux_K)) hno)

noncomputable instance aux_F_field : Field aux_F := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  infer_instance

noncomputable instance aux_K_field : Field aux_K := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  infer_instance

noncomputable instance aux_E_field : Field aux_E := by
  classical
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  infer_instance

noncomputable instance aux_K_algebra : Algebra ℚ aux_K := by
  infer_instance

noncomputable instance aux_E_algebra : Algebra ℚ aux_E := by
  classical
  letI : Algebra ℚ aux_K := by infer_instance
  exact (AdjoinRoot.instAlgebra (R := aux_K) (S := ℚ) (f := aux_s))

noncomputable instance aux_K_algebra_aux_E : Algebra aux_K aux_E := by
  classical
  infer_instance

noncomputable instance aux_F_algebra_aux_E : Algebra aux_F aux_E := by
  classical
  letI : Algebra aux_F aux_K := by infer_instance
  exact (AdjoinRoot.instAlgebra (R := aux_K) (S := aux_F) (f := aux_s))

noncomputable instance aux_E_charZero : CharZero aux_E := by
  classical
  simpa using (Algebra.charZero_of_charZero (R := ℚ) (A := aux_E))

-- `aux_E` is a splitting field of `X^4 - 2X^2 - 2`.
set_option maxHeartbeats 800000 in
lemma aux_E_isSplittingField_p
    [Fact (Irreducible aux_q)] [Fact (Irreducible aux_r)] [Fact (Irreducible aux_s)] :
    Polynomial.IsSplittingField ℚ aux_E
      (X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]) := by
  classical
  let p : ℚ[X] := X ^ 4 - 2 * X ^ 2 - 2
  let uE : aux_E := algebraMap aux_F aux_E aux_u
  let r : aux_E := algebraMap aux_K aux_E (AdjoinRoot.root aux_r)
  let s : aux_E := AdjoinRoot.root aux_s
  let a : aux_E := s / r
  have hu_mul : uE * (2 - uE) = (-2 : aux_E) := by
    let f : aux_F →+* aux_E := algebraMap aux_F aux_E
    have h := congrArg f aux_u_mul_two_sub_aux_u
    have h2 : f (2 : aux_F) = (2 : aux_E) := by
      have h2' : (2 : aux_F) = 1 + 1 := by norm_num
      calc
        f (2 : aux_F) = f (1 + 1) := by
          rw [h2']
        _ = f 1 + f 1 := by
          exact f.map_add 1 1
        _ = (1 : aux_E) + (1 : aux_E) := by simp
        _ = (2 : aux_E) := by norm_num
    have hL : f (aux_u * (2 - aux_u)) = uE * (2 - uE) := by
      calc
        f (aux_u * (2 - aux_u)) = f aux_u * f (2 - aux_u) := by
          exact f.map_mul _ _
        _ = uE * (f (2 : aux_F) - f aux_u) := by
          dsimp [uE]
          rw [f.map_sub]
        _ = uE * (2 - uE) := by
          dsimp [uE]
          rw [h2]
    have hR : f (-2 : aux_F) = (-2 : aux_E) := by
      simpa [h2] using (f.map_neg (2 : aux_F))
    have h1 : uE * (2 - uE) = f (-2 : aux_F) := by
      exact hL.symm.trans h
    exact h1.trans hR
  have hrE : r ^ 2 = uE := by
    have h := AdjoinRoot.eval₂_root (f := aux_r)
    have h' :
        (AdjoinRoot.root aux_r : aux_K) ^ 2 - (algebraMap aux_F aux_K aux_u) = 0 := by
      simpa [aux_r] using h
    have h'' : (AdjoinRoot.root aux_r : aux_K) ^ 2 = (algebraMap aux_F aux_K aux_u) :=
      sub_eq_zero.mp h'
    have hmap := congrArg (algebraMap aux_K aux_E) h''
    simpa [r, uE] using hmap
  have hsE : s ^ 2 = (-2 : aux_E) := by
    have h := AdjoinRoot.eval₂_root (f := aux_s)
    have h' : s ^ 2 - (-2 : aux_E) = 0 := by
      simpa [s, aux_s] using h
    exact sub_eq_zero.mp h'
  have hu_ne0 : uE ≠ 0 := by
    intro hu0
    have : (-2 : aux_E) = 0 := by simpa [hu0] using hu_mul.symm
    have h2 : (2 : aux_E) ≠ 0 := by
      exact (Nat.cast_ne_zero.mpr (by decide))
    exact (neg_ne_zero.mpr h2) this
  have hr_ne0 : r ≠ 0 := by
    intro hr0
    apply hu_ne0
    simpa [hr0] using hrE.symm
  have ha2 : a ^ 2 = 2 - uE := by
    have hdiv : (-2 : aux_E) / uE = 2 - uE := by
      have h' := congrArg (fun x => x / uE) hu_mul
      have h'' : uE * (2 - uE) / uE = 2 - uE := mul_div_cancel_left₀ (2 - uE) hu_ne0
      have h''' : 2 - uE = (-2 : aux_E) / uE := by
        exact h''.symm.trans h'
      exact h'''.symm
    calc
      a ^ 2 = (s ^ 2) / (r ^ 2) := by simp [a, div_pow]
      _ = (-2 : aux_E) / uE := by simpa [hsE, hrE]
      _ = 2 - uE := hdiv
  have hu_eq : uE ^ 2 - 2 * uE - 2 = (0 : aux_E) := by
    have h' : 2 * uE - uE ^ 2 = (-2 : aux_E) := by
      calc
        2 * uE - uE ^ 2 = uE * (2 - uE) := by ring_nf
        _ = (-2 : aux_E) := hu_mul
    calc
      uE ^ 2 - 2 * uE - 2 = -(2 * uE - uE ^ 2) - 2 := by ring_nf
      _ = -(-2 : aux_E) - 2 := by simp [h']
      _ = 0 := by ring_nf
  have hsplit_r : (X ^ 2 - C uE : aux_E[X]).Splits := by
    have h :
        Splits ((X ^ 2 - C uE : aux_E[X]).map (RingHom.id aux_E)) := by
      apply Polynomial.splits_of_natDegree_eq_two (i := RingHom.id aux_E) (x := r)
      · simpa using (natDegree_X_pow_sub_C (R := aux_E) (n := 2) (r := uE))
      · simp [hrE]
    simpa using h
  have hsplit_a : (X ^ 2 - C (2 - uE) : aux_E[X]).Splits := by
    have h :
        Splits ((X ^ 2 - C (2 - uE) : aux_E[X]).map (RingHom.id aux_E)) := by
      apply Polynomial.splits_of_natDegree_eq_two (i := RingHom.id aux_E) (x := a)
      · simpa using (natDegree_X_pow_sub_C (R := aux_E) (n := 2) (r := 2 - uE))
      · simp [ha2]
    simpa using h
  have hsplit_prod :
      ((X ^ 2 - C uE : aux_E[X]) * (X ^ 2 - C (2 - uE))).Splits :=
    Polynomial.Splits.mul hsplit_r hsplit_a
  have hfactor :
      p.map (algebraMap ℚ aux_E) =
        (X ^ 2 - C uE : aux_E[X]) * (X ^ 2 - C (2 - uE)) := by
    -- Expand and use the defining relation for `uE`.
    have h' :
        (X ^ 2 - C uE : aux_E[X]) * (X ^ 2 - C (2 - uE)) =
          X ^ 4 - X ^ 2 * C (2 - uE) - C uE * X ^ 2 + C uE * C (2 - uE) := by
      ring
    have hmid :
        (X ^ 4 - X ^ 2 * C (2 - uE) - C uE * X ^ 2 + C uE * C (2 - uE) : aux_E[X]) =
          X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := by
      calc
        X ^ 4 - X ^ 2 * C (2 - uE) - C uE * X ^ 2 + C uE * C (2 - uE)
            = X ^ 4 - (C (2 - uE) + C uE) * X ^ 2 + C uE * C (2 - uE) := by
                ring
        _ = X ^ 4 - C ((2 - uE) + uE) * X ^ 2 + C (uE * (2 - uE)) := by
                rw [← C_add, ← C_mul]
        _ = X ^ 4 - C (2 : aux_E) * X ^ 2 + C (uE * (2 - uE)) := by
                simp [sub_add_cancel]
        _ = X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := by
                rfl
    have h'' : (C (uE * (2 - uE)) : aux_E[X]) = C (-2 : aux_E) := by
      simpa [hu_mul] using (congrArg C hu_mul)
    have hconst :
        (X ^ 4 - 2 * X ^ 2 - 2 : aux_E[X]) =
          X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := by
      calc
        (X ^ 4 - 2 * X ^ 2 - 2 : aux_E[X]) =
            (X ^ 4 - 2 * X ^ 2 : aux_E[X]) + (-2 : aux_E[X]) := by
              simpa using
                (sub_eq_add_neg (a := (X ^ 4 - 2 * X ^ 2 : aux_E[X])) (b := (2 : aux_E[X])))
        _ = (X ^ 4 - 2 * X ^ 2 : aux_E[X]) + -(C (2 : aux_E)) := by
              rfl
        _ = X ^ 4 - 2 * X ^ 2 + C (-2 : aux_E) := by
              rw [← C_neg]
        _ = X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := by
              rw [← h'']
    have hprod :
        (X ^ 2 - C uE : aux_E[X]) * (X ^ 2 - C (2 - uE)) =
          X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := by
      calc
        (X ^ 2 - C uE : aux_E[X]) * (X ^ 2 - C (2 - uE)) =
            X ^ 4 - X ^ 2 * C (2 - uE) - C uE * X ^ 2 + C uE * C (2 - uE) := h'
        _ = X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := hmid
    calc
      p.map (algebraMap ℚ aux_E) = (X ^ 4 - 2 * X ^ 2 - 2 : aux_E[X]) := by
        simp [p]
      _ = X ^ 4 - 2 * X ^ 2 + C (uE * (2 - uE)) := hconst
      _ = (X ^ 2 - C uE : aux_E[X]) * (X ^ 2 - C (2 - uE)) := by
        exact hprod.symm
  have hsplit : Splits (p.map (algebraMap ℚ aux_E)) := by
    simpa [hfactor] using hsplit_prod
  let A : Subalgebra ℚ aux_E := Algebra.adjoin ℚ (p.rootSet aux_E)
  have hp_ne0 : p ≠ 0 := by
    have hp_irr : Irreducible p := by
      simpa [p] using irreducible_X4_sub_2X2_sub_2
    exact hp_irr.ne_zero
  have hr_root : r ∈ p.rootSet aux_E := by
    have hr4 : r ^ 4 = uE ^ 2 := by
      calc
        r ^ 4 = (r ^ 2) ^ 2 := by simp [pow_succ, mul_assoc]
        _ = uE ^ 2 := by simpa [hrE]
    have hroot : aeval r p = (0 : aux_E) := by
      simp [aeval_def, p, hrE, hr4, hu_eq]
    exact (Polynomial.mem_rootSet_of_ne hp_ne0).2 hroot
  have ha_root : a ∈ p.rootSet aux_E := by
    have ha4 : a ^ 4 = (2 - uE) ^ 2 := by
      calc
        a ^ 4 = (a ^ 2) ^ 2 := by simp [pow_succ, mul_assoc]
        _ = (2 - uE) ^ 2 := by simpa [ha2]
    have hcalc : (2 - uE) ^ 2 - 2 * (2 - uE) - 2 = uE ^ 2 - 2 * uE - 2 := by
      ring
    have hroot : aeval a p = (0 : aux_E) := by
      calc
        aeval a p = (2 - uE) ^ 2 - 2 * (2 - uE) - 2 := by
          simp [aeval_def, p, ha2, ha4]
        _ = 0 := by simpa [hcalc] using hu_eq
    exact (Polynomial.mem_rootSet_of_ne hp_ne0).2 hroot
  have hrA : r ∈ A := Algebra.subset_adjoin hr_root
  have haA : a ∈ A := Algebra.subset_adjoin ha_root
  have huA : uE ∈ A := by
    have hr2 : r ^ 2 ∈ A := Subalgebra.pow_mem A hrA 2
    simpa [hrE] using hr2
  have hsA : s ∈ A := by
    have : s = r * a := by
      have : r * (s / r) = s := by
        calc
          r * (s / r) = r * s / r := by
            simp [div_eq_mul_inv, mul_assoc]
          _ = s := by
            simpa using (mul_div_cancel_left₀ (b := s) (a := r) hr_ne0)
      simpa [a] using this.symm
    simpa [this] using (Subalgebra.mul_mem A hrA haA)
  -- Elements of `aux_F` map into `A`.
  have hF : ∀ x : aux_F, algebraMap aux_F aux_E x ∈ A := by
    intro x
    let fF : ℚ[X] →+* aux_E :=
      (algebraMap aux_F aux_E).comp (AdjoinRoot.mk aux_q)
    have hFq : ∀ q : ℚ[X], fF q ∈ A := by
      intro q
      refine Polynomial.induction_on q ?_ ?_ ?_
      · intro a
        simpa [fF, ← AdjoinRoot.algebraMap_eq] using (A.algebraMap_mem a)
      · intro p q hp hq
        simpa [fF] using (Subalgebra.add_mem A hp hq)
      · intro n a hn
        have hX : fF X ∈ A := by
          simpa [fF, uE] using huA
        have hmul :
            fF (C a * X ^ (n + 1)) = fF (C a * X ^ n) * fF X := by
          simp [fF, pow_succ, mul_assoc]
        simpa [hmul] using (Subalgebra.mul_mem A hn hX)
    refine AdjoinRoot.induction_on (f := aux_q) (x := x) ?_
    intro q
    simpa [fF] using hFq q
  -- Elements of `aux_K` map into `A`.
  have hK : ∀ x : aux_K, algebraMap aux_K aux_E x ∈ A := by
    intro x
    let fK : aux_F[X] →+* aux_E :=
      (algebraMap aux_K aux_E).comp (AdjoinRoot.mk aux_r)
    have hKq : ∀ q : aux_F[X], fK q ∈ A := by
      intro q
      refine Polynomial.induction_on q ?_ ?_ ?_
      · intro a
        have h1 : fK (C a) = (algebraMap aux_K aux_E) ((algebraMap aux_F aux_K) a) := by
          simp [fK, AdjoinRoot.algebraMap_eq]
        have h2 :
            (algebraMap aux_K aux_E) ((algebraMap aux_F aux_K) a) =
              (algebraMap aux_F aux_E) a := by
          rfl
        have h' : fK (C a) = (algebraMap aux_F aux_E) a := h1.trans h2
        simpa [h'] using hF a
      · intro p q hp hq
        simpa [fK] using (Subalgebra.add_mem A hp hq)
      · intro n a hn
        have hX : fK X ∈ A := by
          simpa [fK, r] using hrA
        have hmul :
            fK (C a * X ^ (n + 1)) = fK (C a * X ^ n) * fK X := by
          simp [fK, pow_succ, mul_assoc]
        simpa [hmul] using (Subalgebra.mul_mem A hn hX)
    refine AdjoinRoot.induction_on (f := aux_r) (x := x) ?_
    intro q
    simpa [fK] using hKq q
  -- Elements of `aux_E` lie in `A`.
  have hE : ∀ x : aux_E, x ∈ A := by
    intro x
    let fE : aux_K[X] →+* aux_E := AdjoinRoot.mk aux_s
    have hEq : ∀ q : aux_K[X], fE q ∈ A := by
      intro q
      refine Polynomial.induction_on q ?_ ?_ ?_
      · intro a
        have h' : fE (C a) = (algebraMap aux_K aux_E) a := by
          simp [fE, ← AdjoinRoot.algebraMap_eq]
        simpa [h'] using hK a
      · intro p q hp hq
        have h := Subalgebra.add_mem A hp hq
        simpa [fE.map_add] using h
      · intro n a hn
        have hX : fE X ∈ A := by
          simpa [fE, s] using hsA
        have hmul :
            fE (C a * X ^ (n + 1)) = fE (C a * X ^ n) * fE X := by
          simp [fE, pow_succ, mul_assoc]
        simpa [hmul] using (Subalgebra.mul_mem A hn hX)
    refine AdjoinRoot.induction_on (f := aux_s) (x := x) ?_
    intro q
    exact hEq q
  refine ⟨hsplit, ?_⟩
  -- Show the root set generates the whole field.
  apply (Algebra.eq_top_iff).2
  intro x
  exact hE x

-- The splitting field of `X^4 - 2X^2 - 2` has degree 8 over ℚ.
lemma finrank_splittingField_X4_sub_2X2_sub_2 :
    Module.finrank ℚ ((X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]).SplittingField) = 8 := by
  classical
  -- TODO: complete the explicit quadratic tower argument and compare with the splitting field.
  let p : ℚ[X] := X ^ 4 - 2 * X ^ 2 - 2
  -- The explicit quadratic tower has degree 8.
  have hE : Module.finrank ℚ aux_E = 8 := auxField_finrank_eq_8
  -- Start the field-instance tower from the Eisenstein irreducibility of `aux_q`.
  haveI : Fact (Irreducible aux_q) := ⟨aux_q_irreducible⟩
  haveI : Fact (Irreducible aux_r) := ⟨aux_r_irreducible⟩
  haveI : Fact (Irreducible aux_s) := ⟨aux_s_irreducible⟩
  have hsplit : Polynomial.IsSplittingField ℚ aux_E p := by
    simpa [p] using (aux_E_isSplittingField_p)
  -- Transfer finrank along the splitting-field equivalence.
  haveI : Polynomial.IsSplittingField ℚ aux_E p := hsplit
  have e : aux_E ≃ₐ[ℚ] p.SplittingField :=
    Polynomial.IsSplittingField.algEquiv (L := aux_E) p
  have hfinrank :
      Module.finrank ℚ aux_E = Module.finrank ℚ p.SplittingField :=
    LinearEquiv.finrank_eq (e.toLinearEquiv)
  calc
    Module.finrank ℚ p.SplittingField = Module.finrank ℚ aux_E := by
      simpa using hfinrank.symm
    _ = 8 := hE

-- A faithful dihedral action on the square, encoded on `ZMod 4`.
noncomputable def dihedralPerm : DihedralGroup 4 → Equiv.Perm (ZMod 4)
  | DihedralGroup.r i => Equiv.addLeft (-i)
  | DihedralGroup.sr i => Equiv.subLeft i

noncomputable def dihedralPermHom : DihedralGroup 4 →* Equiv.Perm (ZMod 4) where
  toFun := dihedralPerm
  map_one' := by
    ext x
    change dihedralPerm (DihedralGroup.r 0) x = x
    simp [dihedralPerm]
  map_mul' := by
    intro a b
    cases a <;> cases b <;>
      ext x <;> simp [dihedralPerm, add_assoc, add_comm, add_left_comm, sub_eq_add_neg]

-- The dihedral action on `ZMod 4` is faithful.
lemma dihedralPermHom_injective : Function.Injective dihedralPermHom := by
  intro a b h
  cases a <;> cases b
  ·
    have h0 := congrArg (fun f => f 0) h
    simp [dihedralPermHom, dihedralPerm] at h0
    simp [h0]
  ·
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp [dihedralPermHom, dihedralPerm, sub_eq_add_neg] at h0 h1
    have h1' := h1
    simp [h0] at h1'
    have h1'' : (1 : ZMod 4) = -1 := by
      simpa [eq_comm] using h1'
    exfalso
    exact (by decide : (1 : ZMod 4) ≠ -1) h1''
  ·
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp [dihedralPermHom, dihedralPerm, sub_eq_add_neg] at h0 h1
    have h1' := h1
    simp [h0] at h1'
    have h1'' : (1 : ZMod 4) = -1 := by
      simpa [eq_comm] using h1'
    exfalso
    exact (by decide : (1 : ZMod 4) ≠ -1) h1''
  ·
    have h0 := congrArg (fun f => f 0) h
    simp [dihedralPermHom, dihedralPerm, sub_eq_add_neg] at h0
    simp [h0]

-- A convenient dihedral subgroup of `S₄`.
lemma dihedral_to_perm_fin4_injective :
    ∃ g : DihedralGroup 4 →* Equiv.Perm (Fin 4), Function.Injective g := by
  classical
  let e : ZMod 4 ≃ Fin 4 := Fintype.equivFinOfCardEq (by simp)
  let g : DihedralGroup 4 →* Equiv.Perm (Fin 4) :=
    (e.permCongrHom.toMonoidHom).comp dihedralPermHom
  refine ⟨g, ?_⟩
  intro a b h
  apply dihedralPermHom_injective
  have h' :
      e.permCongrHom (dihedralPermHom a) = e.permCongrHom (dihedralPermHom b) := by
    simpa [g] using h
  exact e.permCongrHom.injective h'

-- Helper lemma reserved for the explicit Galois-group identification.
theorem nonempty_galois_mulEquiv_dihedralGroup_four_aux :
    Nonempty (Gal (X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]) ≃* DihedralGroup 4) := by
  classical
  let p : ℚ[X] := X ^ 4 - 2 * X ^ 2 - 2
  have hirr : Irreducible p := irreducible_X4_sub_2X2_sub_2
  have hsep : p.Separable := hirr.separable
  have hgal : IsGalois ℚ p.SplittingField := by
    simpa using
      (IsGalois.of_separable_splitting_field (F := ℚ) (E := p.SplittingField) (p := p) hsep)
  -- TODO: construct explicit automorphisms of the splitting field to identify the Galois group.
  -- This is the remaining step in the Galois group computation.
  have hmain : Nonempty (p.Gal ≃* DihedralGroup 4) := by
    -- The root set has four elements in the splitting field.
    have hdeg : p.natDegree = 4 := by
      simpa [p] using natDegree_X4_sub_2X2_sub_2
    have hcard :
        Fintype.card (p.rootSet p.SplittingField) = 4 := by
      have hcard' :
          Fintype.card (p.rootSet p.SplittingField) = p.natDegree := by
        simpa using
          (Polynomial.card_rootSet_eq_natDegree (K := p.SplittingField) hsep
            (SplittingField.splits p))
      simpa [hdeg] using hcard'
    -- Set up the faithful permutation representation on the four roots.
    haveI hsplit : Fact ((p.map (algebraMap ℚ p.SplittingField)).Splits) :=
      ⟨SplittingField.splits p⟩
    let eRoot : p.rootSet p.SplittingField ≃ Fin 4 := Fintype.equivFinOfCardEq hcard
    let f : p.Gal →* Equiv.Perm (Fin 4) :=
      (eRoot.permCongrHom.toMonoidHom).comp (Polynomial.Gal.galActionHom p p.SplittingField)
    have hf_inj : Function.Injective f := by
      intro x y hxy
      have h' :
          (Polynomial.Gal.galActionHom p p.SplittingField) x =
            (Polynomial.Gal.galActionHom p p.SplittingField) y := by
        apply eRoot.permCongrHom.injective
        simpa [f] using hxy
      exact (Polynomial.Gal.galActionHom_injective (p := p) (E := p.SplittingField)) h'
    -- Fix a standard Sylow 2-subgroup coming from the dihedral action.
    obtain ⟨g, hg_inj⟩ := dihedral_to_perm_fin4_injective
    -- TODO: compute `Nat.card p.Gal = 8`, show `MonoidHom.range f` is Sylow-2,
    -- compare with the dihedral Sylow via `Sylow.equiv`, and transport back.
    have hcardGal : Nat.card p.Gal = 8 := by
      have hfinrank : Module.finrank ℚ p.SplittingField = 8 := by
        simpa [p] using finrank_splittingField_X4_sub_2X2_sub_2
      simpa [hfinrank] using (Polynomial.Gal.card_of_separable (p := p) (F := ℚ) hsep)
    have hf_card : Nat.card (MonoidHom.range f) = 8 := by
      have hcongr :
          Nat.card p.Gal = Nat.card (MonoidHom.range f) :=
        Nat.card_congr (MonoidHom.ofInjective (f := f) hf_inj).toEquiv
      exact hcongr.symm.trans hcardGal
    have hg_card : Nat.card (MonoidHom.range g) = 8 := by
      have hcongr :
          Nat.card (DihedralGroup 4) = Nat.card (MonoidHom.range g) :=
        Nat.card_congr (MonoidHom.ofInjective (f := g) hg_inj).toEquiv
      have hD4 : Nat.card (DihedralGroup 4) = 8 := by
        simpa using (DihedralGroup.nat_card (n := 4))
      exact hcongr.symm.trans hD4
    have hcardS4 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      simpa using (Nat.card_perm (α := Fin 4))
    have hcardS4' : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
      simpa [Nat.card_eq_fintype_card] using hcardS4
    have hf_card' : Fintype.card (MonoidHom.range f) = 8 := by
      simpa [Nat.card_eq_fintype_card] using hf_card
    have hg_card' : Fintype.card (MonoidHom.range g) = 8 := by
      simpa [Nat.card_eq_fintype_card] using hg_card
    have hf_index : (MonoidHom.range f).index = 3 := by
      have hmul' : 8 * (MonoidHom.range f).index = 24 := by
        have h := (MonoidHom.range f).card_mul_index
        rw [hf_card, hcardS4] at h
        simpa using h
      have hpos : (0 : ℕ) < 8 := by decide
      refine (Nat.mul_left_cancel hpos ?_)
      calc
        8 * (MonoidHom.range f).index = 24 := hmul'
        _ = 8 * 3 := by simp
    have hg_index : (MonoidHom.range g).index = 3 := by
      have hmul' : 8 * (MonoidHom.range g).index = 24 := by
        have h := (MonoidHom.range g).card_mul_index
        rw [hg_card, hcardS4] at h
        simpa using h
      have hpos : (0 : ℕ) < 8 := by decide
      refine (Nat.mul_left_cancel hpos ?_)
      calc
        8 * (MonoidHom.range g).index = 24 := hmul'
        _ = 8 * 3 := by simp
    haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hpf_pgroup : IsPGroup 2 (MonoidHom.range f) := by
      refine IsPGroup.of_card (p := 2) (n := 3) ?_
      simpa using hf_card
    have hpg_pgroup : IsPGroup 2 (MonoidHom.range g) := by
      refine IsPGroup.of_card (p := 2) (n := 3) ?_
      simpa using hg_card
    have hpf_index_not : ¬ (2 : ℕ) ∣ (MonoidHom.range f).index := by
      simp [hf_index]
    have hpg_index_not : ¬ (2 : ℕ) ∣ (MonoidHom.range g).index := by
      simp [hg_index]
    let Pf : Sylow 2 (Equiv.Perm (Fin 4)) := IsPGroup.toSylow hpf_pgroup hpf_index_not
    let Pg : Sylow 2 (Equiv.Perm (Fin 4)) := IsPGroup.toSylow hpg_pgroup hpg_index_not
    have hPf : (Pf : Subgroup (Equiv.Perm (Fin 4))) = MonoidHom.range f := by rfl
    have hPg : (Pg : Subgroup (Equiv.Perm (Fin 4))) = MonoidHom.range g := by rfl
    have e_sylow : (MonoidHom.range f) ≃* (MonoidHom.range g) := by
      simpa [hPf, hPg] using (Sylow.equiv Pf Pg)
    refine ⟨(MonoidHom.ofInjective (f := f) hf_inj).trans
      (e_sylow.trans (MonoidHom.ofInjective (f := g) hg_inj).symm)⟩
  simpa [p] using hmain

theorem nonempty_galois_mulEquiv_dihedralGroup_four :
    Nonempty (Gal (X ^ 4 - 2 * X ^ 2 - 2 : ℚ[X]) ≃* DihedralGroup 4) := by
  classical
  simpa using nonempty_galois_mulEquiv_dihedralGroup_four_aux

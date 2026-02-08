import Mathlib

open Polynomial
/--
Prove that for any $a,b \in \mathbb{F}_{p^n}$, if $x^3+ax+b$ is irreducible then
$-4a^3-27b^2$ is a square in $\mathbb{F}_{p^n}$.
-/
-- A direct discriminant computation for the depressed cubic.
lemma cubic_discr_X3_aX_b {p n : ℕ} [Fact p.Prime] (a b : GaloisField p n) :
    (Cubic.discr (⟨1, 0, a, b⟩ : Cubic (GaloisField p n))) = -4 * a ^ 3 - 27 * b ^ 2 := by
  simp [Cubic.discr]

-- Irreducible depressed cubics have no roots in the base field.
lemma roots_eq_zero_of_irreducible_X3_aX_b {K : Type*} [Field K] (a b : K)
    (h : Irreducible (X ^ 3 + C a * X + C b)) :
    (X ^ 3 + C a * X + C b : K[X]).roots = 0 := by
  have hdeg : (X ^ 3 + C a * X + C b : K[X]).natDegree = 3 := by
    simpa using
      (Polynomial.natDegree_cubic (a := (1 : K)) (b := 0) (c := a) (d := b) (by simp))
  have hdeg2 : 2 ≤ (X ^ 3 + C a * X + C b : K[X]).natDegree := by
    simp [hdeg]
  have hdeg3 : (X ^ 3 + C a * X + C b : K[X]).natDegree ≤ 3 := by
    simp [hdeg]
  exact (Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three hdeg2 hdeg3).1 h

-- Frobenius fixed points in finite algebraic extensions lie in the base field.
lemma mem_range_algebraMap_of_frobenius_fixed {K L : Type*} [Field K] [Field L]
    [Algebra K L] [Fintype K] [Finite L] [Algebra.IsAlgebraic K L] [IsGalois K L]
    [FiniteDimensional K L]
    (x : L) (hx : FiniteField.frobeniusAlgEquivOfAlgebraic K L x = x) :
    x ∈ Set.range (algebraMap K L) := by
  classical
  have hx_fixed : ∀ f : Gal(L / K), f x = x := by
    intro f
    obtain ⟨n, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow K L).2 f
    have hxpow : ∀ m : ℕ,
        (FiniteField.frobeniusAlgEquivOfAlgebraic K L ^ m) x = x := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          simp [pow_succ, AlgEquiv.mul_apply, ih, hx]
    simpa using hxpow n.1
  exact (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := L) x).2 hx_fixed

theorem isSquare_discriminant_of_irreducible {p n : ℕ} [Fact p.Prime] (a b : GaloisField p n)
    (h_irr : Irreducible (X ^ 3 + C a * X + C b)) :
    IsSquare (- 4 * a ^ 3 - 27 * b ^ 2) := by
  classical
  let P : Cubic (GaloisField p n) := ⟨1, 0, a, b⟩
  have hdisc : P.discr = -4 * a ^ 3 - 27 * b ^ 2 := cubic_discr_X3_aX_b a b
  by_cases hchar : ringChar (GaloisField p n) = 2
  · simpa [hdisc] using
      (FiniteField.isSquare_of_char_two (F := GaloisField p n) hchar P.discr)
  by_cases hdisc0 : P.discr = 0
  · refine ⟨0, ?_⟩
    have hdisc0' : -(4 * a ^ 3) - 27 * b ^ 2 = 0 := by
      have : -4 * a ^ 3 - 27 * b ^ 2 = 0 := by
        simpa [hdisc] using hdisc0
      simpa [neg_mul] using this
    simp [hdisc0']
  let L := P.toPoly.SplittingField
  let KtoL : GaloisField p n →+* L := algebraMap _ _
  let _ := Fintype.ofFinite (GaloisField p n)
  let _ := Fintype.ofFinite L
  have hsplit : Splits (P.toPoly.map KtoL) := SplittingField.splits (P.toPoly)
  have ha : P.a ≠ 0 := by simp [P]
  obtain ⟨x, y, z, h3⟩ := (Cubic.splits_iff_roots_eq_three (P := P) (φ := KtoL) ha).1 hsplit
  have h3' : (P.toPoly.map KtoL).roots = ({x, y, z} : Multiset L) := by
    simpa [Cubic.map_roots] using h3
  let delta : L := KtoL P.a * KtoL P.a * (x - y) * (x - z) * (y - z)
  have hdiscr : KtoL P.discr = delta ^ 2 := by
    simpa [delta] using
      (Cubic.discr_eq_prod_three_roots (P := P) (φ := KtoL) (x := x) (y := y) (z := z) ha h3)
  have hroots_ne :=
    (Cubic.discr_ne_zero_iff_roots_ne (P := P) (φ := KtoL) (x := x) (y := y) (z := z) ha h3).1
      hdisc0
  have hxy : x ≠ y := hroots_ne.1
  have hxz : x ≠ z := hroots_ne.2.1
  have hyz_ne : y ≠ z := hroots_ne.2.2
  have hroots0 : (P.toPoly).roots = 0 := by
    simpa [P, Cubic.toPoly] using roots_eq_zero_of_irreducible_X3_aX_b a b h_irr
  have hp0 : P.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero (P := P) ha
  let frobenius : L ≃ₐ[GaloisField p n] L :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (GaloisField p n) L
  let frobeniusHom : L →+* L := frobenius.toRingHom
  have hmap_poly : (P.toPoly.map KtoL).map frobeniusHom = P.toPoly.map KtoL := by
    ext n
    simp [KtoL, frobeniusHom, AlgEquiv.commutes]
  have hroots_perm : (P.toPoly.map KtoL).roots.map frobeniusHom = (P.toPoly.map KtoL).roots := by
    have h := (hsplit.map_roots (i := frobeniusHom))
    simpa [hmap_poly] using h.symm
  have hno_fixed : ∀ r ∈ ({x, y, z} : Multiset L), frobenius r ≠ r := by
    intro r hr hfix
    have hr_range : r ∈ Set.range (algebraMap (GaloisField p n) L) :=
      mem_range_algebraMap_of_frobenius_fixed (K := GaloisField p n) (L := L) r hfix
    rcases hr_range with ⟨r0, rfl⟩
    have hr_mem' : (algebraMap (GaloisField p n) L r0) ∈ (P.toPoly.map KtoL).roots := by
      rw [h3']
      exact hr
    have hr_mem : (algebraMap (GaloisField p n) L r0) ∈ (P.toPoly).aroots L := by
      rw [Polynomial.aroots_def]
      exact hr_mem'
    have hr_aeval : aeval (algebraMap (GaloisField p n) L r0) P.toPoly = 0 :=
      (Polynomial.mem_aroots (p := P.toPoly) (S := L)).1 hr_mem |>.2
    have hr_root : (P.toPoly).IsRoot r0 :=
      Polynomial.isRoot_of_aeval_algebraMap_eq_zero (p := P.toPoly) (r := r0) (by
        simpa using hr_aeval)
    have hr_memK : r0 ∈ (P.toPoly).roots := (Polynomial.mem_roots hp0).2 hr_root
    simp [hroots0] at hr_memK
  have hx_mem : frobenius x ∈ ({x, y, z} : Multiset L) := by
    have hx' : x ∈ (P.toPoly.map KtoL).roots := by
      rw [h3']
      simp
    have hx_map : frobeniusHom x ∈ (P.toPoly.map KtoL).roots.map frobeniusHom :=
      Multiset.mem_map_of_mem _ hx'
    have hx_mem' : frobeniusHom x ∈ (P.toPoly.map KtoL).roots := by
      rw [← hroots_perm]
      exact hx_map
    rw [h3'] at hx_mem'
    simpa using hx_mem'
  have hx_cases : frobenius x = y ∨ frobenius x = z := by
    have hx' : frobenius x = x ∨ frobenius x = y ∨ frobenius x = z := by
      simpa using hx_mem
    rcases hx' with hx' | hx'
    · exact (hno_fixed x (by simp) hx').elim
    · exact hx'
  have hfrob_delta : frobenius delta = delta := by
    cases hx_cases with
    | inl hxy' =>
        have hy_mem : frobenius y ∈ ({x, y, z} : Multiset L) := by
          have hy' : y ∈ (P.toPoly.map KtoL).roots := by
            rw [h3']
            simp
          have hy_map : frobeniusHom y ∈ (P.toPoly.map KtoL).roots.map frobeniusHom :=
            Multiset.mem_map_of_mem _ hy'
          have hy_mem' : frobeniusHom y ∈ (P.toPoly.map KtoL).roots := by
            rw [← hroots_perm]
            exact hy_map
          rw [h3'] at hy_mem'
          simpa using hy_mem'
        have hy_cases : frobenius y = x ∨ frobenius y = z := by
          have hy' : frobenius y = x ∨ frobenius y = y ∨ frobenius y = z := by
            simpa using hy_mem
          rcases hy' with hy' | hy'
          · exact Or.inl hy'
          · rcases hy' with hy' | hy'
            · exact (hno_fixed y (by simp) hy').elim
            · exact Or.inr hy'
        have hyz' : frobenius y = z := by
          cases hy_cases with
          | inl hyx =>
              have hz_mem : frobenius z ∈ ({x, y, z} : Multiset L) := by
                have hz' : z ∈ (P.toPoly.map KtoL).roots := by
                  rw [h3']
                  simp
                have hz_map : frobeniusHom z ∈ (P.toPoly.map KtoL).roots.map frobeniusHom :=
                  Multiset.mem_map_of_mem _ hz'
                have hz_mem' : frobeniusHom z ∈ (P.toPoly.map KtoL).roots := by
                  rw [← hroots_perm]
                  exact hz_map
                rw [h3'] at hz_mem'
                simpa using hz_mem'
              have hz' : frobenius z = x ∨ frobenius z = y ∨ frobenius z = z := by
                simpa using hz_mem
              have hz_eq : frobenius z = z := by
                rcases hz' with hz' | hz'
                · have : z = y := by
                    apply frobenius.injective
                    simpa [hxy', hyx]
                  exact (hyz_ne this.symm).elim
                · rcases hz' with hz' | hz'
                  · have : z = x := by
                      apply frobenius.injective
                      simp [hxy', hz']
                    exact (hxz this.symm).elim
                  · exact hz'
              exact (hno_fixed z (by simp) hz_eq).elim
          | inr hyz_eq => exact hyz_eq
        have hzx' : frobenius z = x := by
          have hz_mem : frobenius z ∈ ({x, y, z} : Multiset L) := by
            have hz' : z ∈ (P.toPoly.map KtoL).roots := by
              rw [h3']
              simp
            have hz_map : frobeniusHom z ∈ (P.toPoly.map KtoL).roots.map frobeniusHom :=
              Multiset.mem_map_of_mem _ hz'
            have hz_mem' : frobeniusHom z ∈ (P.toPoly.map KtoL).roots := by
              rw [← hroots_perm]
              exact hz_map
            rw [h3'] at hz_mem'
            simpa using hz_mem'
          have hz' : frobenius z = x ∨ frobenius z = y ∨ frobenius z = z := by
            simpa using hz_mem
          rcases hz' with hz' | hz'
          · exact hz'
          · rcases hz' with hz' | hz'
            · have : z = x := by
                apply frobenius.injective
                simp [hxy', hz']
              exact (hxz this.symm).elim
            · exact (hno_fixed z (by simp) hz').elim
        have hFrobA : frobenius (KtoL P.a) = KtoL P.a := by
          simp [KtoL, AlgEquiv.commutes]
        calc
          frobenius delta =
              (KtoL P.a * KtoL P.a * (frobenius x - frobenius y) *
                (frobenius x - frobenius z) * (frobenius y - frobenius z)) := by
            simp [delta, map_mul, map_sub, hFrobA]
          _ = delta := by
            simp [delta, hxy', hyz', hzx']
            ring
    | inr hxz' =>
        have hy_mem : frobenius y ∈ ({x, y, z} : Multiset L) := by
          have hy' : y ∈ (P.toPoly.map KtoL).roots := by
            rw [h3']
            simp
          have hy_map : frobeniusHom y ∈ (P.toPoly.map KtoL).roots.map frobeniusHom :=
            Multiset.mem_map_of_mem _ hy'
          have hy_mem' : frobeniusHom y ∈ (P.toPoly.map KtoL).roots := by
            rw [← hroots_perm]
            exact hy_map
          rw [h3'] at hy_mem'
          simpa using hy_mem'
        have hy_cases : frobenius y = x ∨ frobenius y = z := by
          have hy' : frobenius y = x ∨ frobenius y = y ∨ frobenius y = z := by
            simpa using hy_mem
          rcases hy' with hy' | hy'
          · exact Or.inl hy'
          · rcases hy' with hy' | hy'
            · exact (hno_fixed y (by simp) hy').elim
            · exact Or.inr hy'
        have hyx' : frobenius y = x := by
          cases hy_cases with
          | inl hyx => exact hyx
          | inr hyz_eq =>
              have : x = y := by
                apply frobenius.injective
                simp [hxz', hyz_eq]
              exact (hxy this).elim
        have hzy' : frobenius z = y := by
          have hz_mem : frobenius z ∈ ({x, y, z} : Multiset L) := by
            have hz' : z ∈ (P.toPoly.map KtoL).roots := by
              rw [h3']
              simp
            have hz_map : frobeniusHom z ∈ (P.toPoly.map KtoL).roots.map frobeniusHom :=
              Multiset.mem_map_of_mem _ hz'
            have hz_mem' : frobeniusHom z ∈ (P.toPoly.map KtoL).roots := by
              rw [← hroots_perm]
              exact hz_map
            rw [h3'] at hz_mem'
            simpa using hz_mem'
          have hz' : frobenius z = x ∨ frobenius z = y ∨ frobenius z = z := by
            simpa using hz_mem
          rcases hz' with hz' | hz'
          · have : z = y := by
              apply frobenius.injective
              simpa [hxz', hyx']
            exact (hyz_ne this.symm).elim
          · rcases hz' with hz' | hz'
            · exact hz'
            · exact (hno_fixed z (by simp) hz').elim
        have hFrobA : frobenius (KtoL P.a) = KtoL P.a := by
          simp [KtoL, AlgEquiv.commutes]
        calc
          frobenius delta =
              (KtoL P.a * KtoL P.a * (frobenius x - frobenius y) *
                (frobenius x - frobenius z) * (frobenius y - frobenius z)) := by
            simp [delta, map_mul, map_sub, hFrobA]
          _ = delta := by
            simp [delta, hxz', hyx', hzy']
            ring
  have hdelta_mem : delta ∈ Set.range (algebraMap (GaloisField p n) L) :=
    mem_range_algebraMap_of_frobenius_fixed (K := GaloisField p n) (L := L) delta hfrob_delta
  rcases hdelta_mem with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  have hsq1 : d ^ 2 = P.discr := by
    apply (algebraMap (GaloisField p n) L).injective
    calc
      (algebraMap (GaloisField p n) L) (d ^ 2) = (algebraMap (GaloisField p n) L d) ^ 2 := by
        simp
      _ = delta ^ 2 := by simp [hd]
      _ = (algebraMap (GaloisField p n) L) P.discr := by
        simpa [KtoL] using hdiscr.symm
  have hsq : P.discr = d * d := by
    simpa [pow_two] using hsq1.symm
  simpa [hdisc] using hsq

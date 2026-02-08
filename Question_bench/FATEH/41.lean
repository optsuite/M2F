import Mathlib

open scoped Polynomial
open Polynomial

set_option maxHeartbeats 1000000


/-- Let $p$ be a prime integer. Suppose that the degree of every finite extension of a field $F$
 is divisible by $p$. Prove that the degree of every finite extension of $F$ is a power of $p$. -/
theorem exists_finrank_eq_pow_of_dvd_finrank {F : Type} [Field F] (p : ℕ) [Fact (Nat.Prime p)]
    (h : ∀ (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E],
    Module.finrank F E ≠ 1 → p ∣ Module.finrank F E)
    (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] :
    ∃ k, Module.finrank F E = p ^ k := by
  classical
  -- In the argument below, we repeatedly use that the *normal closure inside a (possibly infinite)
  -- Galois extension* is again a finite Galois extension. This lets us reduce the separable part
  -- to the finite Galois case where a Sylow argument applies.

  have hp : Nat.Prime p := Fact.out

  -- Finite Galois case: the extension degree is a p-power.
  have galois_finrank_eq_pow (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
      [IsGalois F K] : ∃ k, Module.finrank F K = p ^ k := by
    classical
    let G := Gal(K/F)
    have hcardG : Nat.card G = Module.finrank F K := by
      simpa using (IsGalois.card_aut_eq_finrank (F := F) (E := K))
    haveI : Finite G :=
      Nat.finite_of_card_ne_zero (hcardG ▸ (Module.finrank_pos : 0 < Module.finrank F K).ne')
    let P : Sylow p G := default
    let K₀ : IntermediateField F K :=
      IntermediateField.fixedField (F := F) (E := K) (P : Subgroup G)
    have hK₀ : Module.finrank F K₀ = (P : Subgroup G).index := by
      have h' : Module.finrank F K₀ = K₀.fixingSubgroup.index :=
        IntermediateField.finrank_eq_fixingSubgroup_index (k := F) (K := K) K₀
      have hfix : K₀.fixingSubgroup = (P : Subgroup G) := by
        simpa [K₀] using
          (IntermediateField.fixingSubgroup_fixedField (F := F) (E := K) (H := (P : Subgroup G)))
      simpa [hfix] using h'
    have hK₀_one : Module.finrank F K₀ = 1 := by
      by_contra hne
      have hpdiv : p ∣ Module.finrank F K₀ := h K₀ hne
      exact (P.not_dvd_index) (hK₀ ▸ hpdiv)
    have hK₀_bot : K₀ = ⊥ := (IntermediateField.finrank_eq_one_iff (F := F) (E := K)).1 hK₀_one
    have hPtop : (P : Subgroup G) = ⊤ := by
      have hfix : K₀.fixingSubgroup = (P : Subgroup G) := by
        simpa [K₀] using
          (IntermediateField.fixingSubgroup_fixedField (F := F) (E := K) (H := (P : Subgroup G)))
      have htop : K₀.fixingSubgroup = ⊤ := by simp [hK₀_bot]
      exact hfix.symm.trans htop
    have hG : IsPGroup p G := by
      have htop : IsPGroup p (⊤ : Subgroup G) :=
        (P.isPGroup').of_equiv (MulEquiv.subgroupCongr hPtop)
      exact htop.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hG
    refine ⟨k, ?_⟩
    exact hcardG.symm.trans hk

  -- Separable case: embed into the absolute separable closure, take normal closure there, then use
  -- the finite Galois case and divisibility.
  have separable_finrank_eq_pow (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K]
      [Algebra.IsSeparable F K] : ∃ k, Module.finrank F K = p ^ k := by
    classical
    -- Work inside a (absolute) separable closure `SeparableClosure F / F`, which is Galois and
    -- separably closed.
    let ι : K →ₐ[F] SeparableClosure F :=
      IsSepClosed.lift (K := F) (L := K) (M := SeparableClosure F)
    let K' : IntermediateField F (SeparableClosure F) := ι.fieldRange
    let e : K ≃ₐ[F] K' := AlgEquiv.ofInjectiveField ι
    haveI : FiniteDimensional F K' :=
      FiniteDimensional.of_injective e.symm.toLinearEquiv.toLinearMap e.symm.injective
    -- These instances are canonical, but can be expensive for typeclass search in this file.
    set_option synthInstance.maxHeartbeats 200000 in
    haveI : Algebra K' (SeparableClosure F) := by infer_instance
    set_option synthInstance.maxHeartbeats 200000 in
    haveI : IsScalarTower F K' (SeparableClosure F) := by infer_instance
    let L : IntermediateField F (SeparableClosure F) :=
      IntermediateField.normalClosure F (↥K') (SeparableClosure F)
    have hKL : K' ≤ L := by
      simpa [L] using (IntermediateField.le_normalClosure (F := F) (L := SeparableClosure F) K')
    letI : Algebra K' L := (IntermediateField.inclusion hKL).toRingHom.toAlgebra
    set_option synthInstance.maxHeartbeats 200000 in
    haveI : IsScalarTower F K' L := by infer_instance
    haveI : FiniteDimensional F L := by
      -- `normalClosure` stays finite-dimensional over the base.
      simpa [L] using (normalClosure.is_finiteDimensional F (↥K') (SeparableClosure F))
    haveI : IsGalois F L := by
      -- Since `SeparableClosure F / F` is Galois, so is the normal closure.
      simpa [L] using
        (inferInstance : IsGalois F (IntermediateField.normalClosure F (↥K') (SeparableClosure F)))
    obtain ⟨n, hn⟩ :=
      galois_finrank_eq_pow (K := L)
    have hdvd :
        Module.finrank F K' ∣ Module.finrank F L := by
      refine ⟨Module.finrank K' L, ?_⟩
      simpa using
        (Module.finrank_mul_finrank F K' L).symm
    have hdvd' : Module.finrank F K' ∣ p ^ n := by simpa [hn] using hdvd
    rcases (Nat.dvd_prime_pow hp).1 hdvd' with ⟨k, -, hk⟩
    refine ⟨k, ?_⟩
    -- Transfer the `finrank` statement back along the `F`-algebra equivalence `e`.
    have hfin : Module.finrank F K = Module.finrank F K' := e.toLinearEquiv.finrank_eq
    simpa [hfin] using hk

  -- Inseparable part: either exponential characteristic is `p` (so the inseparable degree is a
  -- `p`-power), or it is different from `p` (then `F` is perfect, hence every finite extension is
  -- separable and the inseparable degree is `1`).
  have finInsepDegree_eq_p_pow (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K] :
      ∃ k, Field.finInsepDegree F K = p ^ k := by
    classical
    obtain ⟨q, hqexp⟩ := ExpChar.exists F
    letI : ExpChar F q := hqexp
    cases hqexp with
    | zero =>
      -- In characteristic 0, every algebraic extension is separable.
      haveI : PerfectField F := PerfectField.ofCharZero
      haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
      haveI : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
      refine ⟨0, ?_⟩
      simpa [Field.finInsepDegree, pow_zero] using
        (Algebra.IsSeparable.finInsepDegree_eq (F := F) (E := K))
    | prime hq =>
      -- Exponential characteristic is a prime `q`.
      by_cases hqp : q = p
      · subst hqp
        exact finInsepDegree_eq_pow F K q
      · -- If `q ≠ p`, we show `F` is perfect by proving Frobenius is surjective (else we get a
        -- degree-`q` extension contradicting the hypothesis `h`).
        have hsurj : Function.Surjective (frobenius F q) := by
          by_contra hsurj
          obtain ⟨a : F, ha : ∀ b : F, (frobenius F q) b ≠ a⟩ := by
            simpa [Function.Surjective] using hsurj
          have ha' : ∀ b : F, b ^ q ≠ a := by
            intro b
            simpa using ha b
          let f : F[X] := X ^ q - C a
          have hf0 : f ≠ 0 := by
            simpa [f] using (X_pow_sub_C_ne_zero hq.pos a)
          have hirr : Irreducible f := by
            simpa [f] using (X_pow_sub_C_irreducible_of_prime hq ha')
          haveI : Fact (Irreducible f) := ⟨hirr⟩
          let pb := AdjoinRoot.powerBasis (K := F) (f := f) hf0
          haveI : FiniteDimensional F (AdjoinRoot f) :=
            pb.basis.finiteDimensional_of_finite
          have hfin : Module.finrank F (AdjoinRoot f) = q := by
            -- `finrank` is the dimension of the canonical power basis.
            simpa [pb, f, natDegree_X_pow_sub_C] using (PowerBasis.finrank pb)
          have hne : Module.finrank F (AdjoinRoot f) ≠ 1 := by
            simpa [hfin] using hq.ne_one
          have hpdiv : p ∣ Module.finrank F (AdjoinRoot f) := h (AdjoinRoot f) hne
          have : p = q :=
            (Nat.prime_dvd_prime_iff_eq hp hq).1 (hfin ▸ hpdiv)
          exact hqp this.symm
        haveI : PerfectRing F q := PerfectRing.ofSurjective F q hsurj
        haveI : PerfectField F := PerfectRing.toPerfectField F q
        haveI : Algebra.IsAlgebraic F K := Algebra.IsAlgebraic.of_finite F K
        haveI : Algebra.IsSeparable F K := Algebra.IsAlgebraic.isSeparable_of_perfectField
        refine ⟨0, ?_⟩
        simpa [Field.finInsepDegree, pow_zero] using
          (Algebra.IsSeparable.finInsepDegree_eq (F := F) (E := K))

  -- Put everything together via the tower law across the separable closure.
  let S : IntermediateField F E := separableClosure F E
  haveI : Algebra.IsSeparable F S := separableClosure.isSeparable F E
  obtain ⟨k₁, hk₁⟩ := separable_finrank_eq_pow (K := S)
  obtain ⟨k₂, hk₂⟩ := finInsepDegree_eq_p_pow (K := E)
  refine ⟨k₁ + k₂, ?_⟩
  have hmul :
      Module.finrank F E = Module.finrank F S * Field.finInsepDegree F E := by
    -- `Field.finInsepDegree` is defined as `finrank (separableClosure F E) E`.
    simpa [Field.finInsepDegree, S] using
      (Module.finrank_mul_finrank F (separableClosure F E) E).symm
  calc
    Module.finrank F E
        = Module.finrank F S * Field.finInsepDegree F E := hmul
    _ = p ^ k₁ * p ^ k₂ := by simp [hk₁, hk₂]
    _ = p ^ (k₁ + k₂) := (pow_add p k₁ k₂).symm

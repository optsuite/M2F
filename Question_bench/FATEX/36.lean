import Mathlib

/-- The annihilator of the domain module is contained in the annihilator of the Hom module. -/
lemma annihilator_le_annihilator_linearMap (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] :
    Module.annihilator R M ≤ Module.annihilator R (M →ₗ[R] N) := by
  intro r hr
  rw [Module.mem_annihilator] at hr ⊢
  intro f
  ext m
  have hm : r • m = 0 := hr m
  calc
    (r • f) m = r • f m := by simp
    _ = f (r • m) := (f.map_smul r m).symm
    _ = 0 := by simp [hm]

/-- Associated primes of a nonempty finite product are those of the factor. -/
lemma associatedPrimes_finPi_eq_succ (R : Type) [CommRing R]
    (N : Type) [AddCommGroup N] [Module R N] (n : ℕ) :
    associatedPrimes R (Fin n.succ → N) = associatedPrimes R N := by
  classical
  induction n with
  | zero =>
      have h0 : associatedPrimes R (Fin 0 → N) = ∅ := by
        simpa using (associatedPrimes.eq_empty_of_subsingleton (R := R) (M := (Fin 0 → N)))
      calc
        associatedPrimes R (Fin 1 → N)
            = associatedPrimes R (N × (Fin 0 → N)) := by
                symm
                simpa using
                  (LinearEquiv.AssociatedPrimes.eq
                    (Fin.consLinearEquiv (R := R) (M := fun _ : Fin 1 => N)))
        _ = associatedPrimes R N ∪ associatedPrimes R (Fin 0 → N) :=
              associatedPrimes.prod (R := R) (M := N) (M' := (Fin 0 → N))
        _ = associatedPrimes R N := by simp [h0]
  | succ n ih =>
      calc
        associatedPrimes R (Fin n.succ.succ → N)
            = associatedPrimes R (N × (Fin n.succ → N)) := by
                symm
                simpa using
                  (LinearEquiv.AssociatedPrimes.eq
                    (Fin.consLinearEquiv (R := R) (M := fun _ : Fin n.succ.succ => N)))
        _ = associatedPrimes R N ∪ associatedPrimes R (Fin n.succ → N) :=
              associatedPrimes.prod (R := R) (M := N) (M' := (Fin n.succ → N))
        _ = associatedPrimes R N ∪ associatedPrimes R N := by simp [ih]
        _ = associatedPrimes R N := by simp

/-- Associated primes of `Hom(R^n,N)` agree with those of `N` for `n ≥ 1`. -/
lemma associatedPrimes_linearMap_from_finPi_eq (R : Type) [CommRing R]
    (N : Type) [AddCommGroup N] [Module R N] (n : ℕ) :
    associatedPrimes R ((Fin n.succ → R) →ₗ[R] N) = associatedPrimes R N := by
  classical
  have h :=
    (LinearEquiv.AssociatedPrimes.eq
      (Module.piEquiv (ι := Fin n.succ) (R := R) (M := N))).symm
  -- Rewrite via the linear equivalence `Hom(R^n,N) ≃ N^n`.
  simpa [h] using (associatedPrimes_finPi_eq_succ (R := R) (N := N) n)

/-- Associated primes of `Hom(M,N)` are contained in those of `N` for finite `M`. -/
lemma associatedPrimes_linearMap_subset_associatedPrimes_codomain (R : Type) [CommRing R]
    (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] :
    associatedPrimes R (M →ₗ[R] N) ⊆ associatedPrimes R N := by
  classical
  by_cases hM : Subsingleton M
  · haveI : Subsingleton M := hM
    haveI : Subsingleton (M →ₗ[R] N) := by
      refine ⟨?_⟩
      intro f g
      ext m
      have hm : m = 0 := Subsingleton.elim m 0
      simp [hm]
    -- In the subsingleton case the associated primes set is empty.
    simp [associatedPrimes.eq_empty_of_subsingleton (R := R) (M := (M →ₗ[R] N))]
  · obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
    cases n with
    | zero =>
        -- A surjection from a subsingleton domain forces the codomain to be subsingleton.
        have hsub : Subsingleton M := (Function.Surjective.subsingleton (f := f) hf)
        exact (hM hsub).elim
    | succ n =>
        have hinj :
            Function.Injective (LinearMap.lcomp R N f) :=
          LinearMap.lcomp_injective_of_surjective (S := R) (N := N) f hf
        intro p hp
        have hp' :
            p ∈ associatedPrimes R ((Fin n.succ → R) →ₗ[R] N) :=
          (associatedPrimes.subset_of_injective (R := R) (M := (M →ₗ[R] N))
            (M' := ((Fin n.succ → R) →ₗ[R] N)) (f := LinearMap.lcomp R N f) hinj) hp
        -- Rewrite `Ass(Hom(R^n,N))` as `Ass(N)`.
        simpa [associatedPrimes_linearMap_from_finPi_eq (R := R) (N := N) n] using hp'

/-- If `ann(M) ≤ p`, then the localization `Mₚ` is nontrivial. -/
lemma nontrivial_localizedModule_atPrime_of_annihilator_le (R : Type) [CommRing R]
    [IsNoetherianRing R] (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {p : Ideal R} [p.IsPrime] (hann : Module.annihilator R M ≤ p) :
    Nontrivial (LocalizedModule.AtPrime p M) := by
  classical
  have hp :
      (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ Module.support R M := by
    have : Module.annihilator R M ≤ (⟨p, inferInstance⟩ : PrimeSpectrum R).asIdeal := by
      simpa using hann
    exact (Module.mem_support_iff_of_finite (R := R) (M := M)
      (p := ⟨p, inferInstance⟩)).2 this
  simpa using (Module.mem_support_iff (R := R) (M := M)
    (p := ⟨p, inferInstance⟩)).1 hp

/-- A `k`-linear functional on `M ⧸ mM` is also `R`-linear via the quotient action. -/
lemma dual_map_smul_residueField (R : Type) [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] (m : Ideal R)
    (g : Module.Dual (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)))
    (r : R) (x : M ⧸ m • (⊤ : Submodule R M)) :
    g (r • x) = r • g x := by
  refine Submodule.Quotient.induction_on (p := (m • (⊤ : Submodule R M))) x ?_
  intro m0
  have hx :
      r • (Submodule.Quotient.mk m0 : M ⧸ m • (⊤ : Submodule R M)) =
        (Ideal.Quotient.mk m r) •
          (Submodule.Quotient.mk m0 : M ⧸ m • (⊤ : Submodule R M)) := by
    calc
      r • (Submodule.Quotient.mk m0 : M ⧸ m • (⊤ : Submodule R M)) =
          (Submodule.Quotient.mk (p := (m • ⊤ : Submodule R M)) (r • m0)) := by
            simp
      _ = (Ideal.Quotient.mk m r) •
            (Submodule.Quotient.mk (p := (m • ⊤ : Submodule R M)) m0) := by
            exact
              (Module.Quotient.mk_smul_mk (I := m) (M := M) (r := r) (m := m0)).symm
  have hy :
      r • g (Submodule.Quotient.mk m0) =
        (Ideal.Quotient.mk m r) • g (Submodule.Quotient.mk m0) := by
    simp [Algebra.smul_def]
  have h := g.map_smul (Ideal.Quotient.mk m r) (Submodule.Quotient.mk m0)
  rw [hx, hy]
  exact h

/-- A nontrivial finite module over a local ring admits a nonzero map to the residue field. -/
lemma exists_nonzero_linearMap_to_residueField_of_local (R : Type) [CommRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Nontrivial M] :
    ∃ f : M →ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R), f ≠ 0 := by
  classical
  let m : Ideal R := IsLocalRing.maximalIdeal R
  letI : Field (R ⧸ m) := Ideal.Quotient.field (I := m)
  have hJ : m ≤ (Module.annihilator R M).jacobson := by
    simpa [m] using (IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M))
  have htop : (⊤ : Submodule R M) ≠ m • (⊤ : Submodule R M) :=
    Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator (M := M) hJ
  haveI : Nontrivial (M ⧸ m • (⊤ : Submodule R M)) := by
    simpa using (Submodule.Quotient.nontrivial_iff.mpr htop.symm)
  letI : Module (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M)) :=
    Module.instQuotientIdealSubmoduleHSMulTop M m
  haveI : Nontrivial (Module.Dual (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M))) := by
    infer_instance
  obtain ⟨g, hg⟩ := exists_ne (α := Module.Dual (R ⧸ m) (M ⧸ m • (⊤ : Submodule R M))) 0
  let to_res' : M ⧸ m • (⊤ : Submodule R M) →ₗ[R] (R ⧸ m) := {
    __ := g
    map_smul' := dual_map_smul_residueField (R := R) (M := M) (m := m) g }
  let to_res : M →ₗ[R] (R ⧸ m) := to_res'.comp (Submodule.mkQ (m • ⊤))
  have hg' : ∃ x, g x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hg
    apply LinearMap.ext
    intro x
    exact h x
  rcases hg' with ⟨x, hx⟩
  obtain ⟨m0, rfl⟩ := Submodule.mkQ_surjective (m • (⊤ : Submodule R M)) x
  refine ⟨to_res, ?_⟩
  intro hzero
  have : to_res m0 = 0 := by
    simpa using congrArg (fun f => f m0) hzero
  have : g (Submodule.Quotient.mk m0) = 0 := by
    simpa [to_res, to_res', LinearMap.comp_apply] using this
  exact hx this

/-- Local step: from `m ∈ Ass N` and a nonzero `M → k`, deduce `m ∈ Ass Hom(M,N)`. -/
lemma maximalIdeal_mem_associatedPrimes_linearMap_of_mem_associatedPrimes_codomain
    (R : Type) [CommRing R] [IsLocalRing R]
    (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (hmN : IsLocalRing.maximalIdeal R ∈ associatedPrimes R N)
    (hf : ∃ f : M →ₗ[R] (R ⧸ IsLocalRing.maximalIdeal R), f ≠ 0) :
    IsLocalRing.maximalIdeal R ∈ associatedPrimes R (M →ₗ[R] N) := by
  classical
  let m : Ideal R := IsLocalRing.maximalIdeal R
  let k : Type := R ⧸ m
  have hmN' : IsAssociatedPrime m N :=
    (AssociatePrimes.mem_iff (R := R) (M := N) (I := m)).1 hmN
  obtain ⟨hprime, ⟨i, hi⟩⟩ :=
    (isAssociatedPrime_iff_exists_injective_linearMap (I := m) (M := N)).1 hmN'
  rcases hf with ⟨f, hf⟩
  let g : M →ₗ[R] N := i ∘ₗ f
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    ext x
    have : g x = 0 := by simp [hg]
    have : i (f x) = 0 := by simpa [g, LinearMap.comp_apply] using this
    have : i (f x) = i 0 := by simpa using this
    exact hi this
  have hker : m = LinearMap.ker (LinearMap.toSpanSingleton R (M →ₗ[R] N) g) := by
    ext r
    constructor
    · intro hr
      apply (LinearMap.mem_ker).2
      ext x
      have hr0 : algebraMap R k r = 0 := by
        simpa [k, m] using
          (Ideal.Quotient.eq_zero_iff_mem (I := m) (a := r)).2 hr
      calc
        (r • g) x = r • g x := by simp
        _ = r • i (f x) := by rfl
        _ = i (r • f x) := by simp
        _ = i 0 := by
            have : r • f x = 0 := by
              calc
                r • f x = (algebraMap R k r) • f x := by
                  simpa using (algebraMap_smul (A := k) r (f x)).symm
                _ = 0 := by simp [hr0]
            simp [this]
        _ = 0 := by simp
    · intro hr
      by_contra hrm
      have hunit : IsUnit r :=
        (IsLocalRing.notMem_maximalIdeal (R := R) (x := r)).1 hrm
      have hrg : r • g = 0 := by
        have : (LinearMap.toSpanSingleton R (M →ₗ[R] N) g) r = 0 := by
          simpa [LinearMap.mem_ker] using hr
        simpa [LinearMap.toSpanSingleton_apply] using this
      have hg0 : g = 0 := (IsUnit.smul_eq_zero hunit).1 hrg
      exact hg hg0
  exact (AssociatePrimes.mem_iff (R := R) (M := (M →ₗ[R] N)) (I := m)).2
    ⟨hprime, ⟨g, hker⟩⟩

/-- Hard direction: from `p ∈ Ass N` and `ann(M) ≤ p` to `p ∈ Ass Hom(M,N)`. -/
lemma associatedPrimes_linearMap_superset_via_localization (R : Type) [CommRing R]
    [IsNoetherianRing R] (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    {p : Ideal R} (hp : p ∈ associatedPrimes R N)
    (hann : Module.annihilator R M ≤ p) :
    p ∈ associatedPrimes R (M →ₗ[R] N) := by
  classical
  have hprime : p.IsPrime :=
    (IsAssociatedPrime.isPrime
      ((AssociatePrimes.mem_iff (R := R) (M := N) (I := p)).1 hp))
  let Rₚ := Localization.AtPrime p
  let Mₚ := LocalizedModule.AtPrime p M
  let Nₚ := LocalizedModule.AtPrime p N
  haveI : p.IsPrime := hprime
  have hNₚ :
      IsLocalRing.maximalIdeal Rₚ ∈ associatedPrimes Rₚ Nₚ := by
    simpa using
      (Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes
        (R := R) (M := N) (p := p) hp)
  have hMₚ : Nontrivial Mₚ :=
    nontrivial_localizedModule_atPrime_of_annihilator_le (R := R) (M := M) (p := p) hann
  haveI : Nontrivial Mₚ := hMₚ
  obtain ⟨f, hf⟩ :=
    exists_nonzero_linearMap_to_residueField_of_local (R := Rₚ) (M := Mₚ)
  have hHomₚ :
      IsLocalRing.maximalIdeal Rₚ ∈ associatedPrimes Rₚ (Mₚ →ₗ[Rₚ] Nₚ) :=
    maximalIdeal_mem_associatedPrimes_linearMap_of_mem_associatedPrimes_codomain
      (R := Rₚ) (M := Mₚ) (N := Nₚ) (hmN := hNₚ) (hf := ⟨f, hf⟩)
  haveI : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  let e :
      LocalizedModule p.primeCompl (M →ₗ[R] N) ≃ₗ[R]
        LocalizedModule p.primeCompl M →ₗ[Localization p.primeCompl] LocalizedModule p.primeCompl N :=
    Module.FinitePresentation.linearEquivMapExtendScalars
      (R := R) (M := M) (N := N) (S := p.primeCompl)
  let f' : (M →ₗ[R] N) →ₗ[R] (Mₚ →ₗ[Rₚ] Nₚ) :=
    (e : _ ≃ₗ[R] _).toLinearMap ∘ₗ LocalizedModule.mkLinearMap p.primeCompl (M →ₗ[R] N)
  haveI : IsLocalizedModule p.primeCompl f' := by
    infer_instance
  have hEq' :
      Ideal.comap (algebraMap R Rₚ) ⁻¹' (associatedPrimes R (M →ₗ[R] N)) =
        associatedPrimes Rₚ (Mₚ →ₗ[Rₚ] Nₚ) := by
    simpa [Rₚ, Mₚ, Nₚ, f'] using
      (Module.associatedPrimes.preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
        (S := p.primeCompl) (R' := Rₚ) (f := f'))
  have hpre :
      Ideal.comap (algebraMap R Rₚ) (IsLocalRing.maximalIdeal Rₚ) ∈
        associatedPrimes R (M →ₗ[R] N) := by
    have hmem :
        IsLocalRing.maximalIdeal Rₚ ∈
          (Ideal.comap (algebraMap R Rₚ)) ⁻¹' (associatedPrimes R (M →ₗ[R] N)) := by
      simpa [hEq'.symm] using hHomₚ
    simpa using hmem
  simpa [Rₚ, Localization.AtPrime.comap_maximalIdeal] using hpre

/--
If \( R \) is Noetherian and \( M \) and \( N \) are finitely generated \( R \)-modules, show that
\[
\operatorname{Ass} \operatorname{Hom}_R(M, N) = \operatorname{Supp} M \cap \operatorname{Ass} N,
\]
where \( \operatorname{Supp} M \) is the set of all primes containing the annihilator of \( M \). -/
theorem associatedPrimes_hom_eq_support_inter_associatedPrimes (R : Type) [CommRing R]
    [IsNoetherianRing R] (M N : Type) [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Finite R N] : associatedPrimes R (M →ₗ[R] N) =
    {p | p ∈ associatedPrimes R N ∧ Module.annihilator R M ≤ p} := by
  classical
  ext p
  constructor
  · intro hp
    have hpN :
        p ∈ associatedPrimes R N :=
      (associatedPrimes_linearMap_subset_associatedPrimes_codomain (R := R) (M := M) (N := N)) hp
    have hprime : IsAssociatedPrime p (M →ₗ[R] N) :=
      (AssociatePrimes.mem_iff (R := R) (M := (M →ₗ[R] N)) (I := p)).1 hp
    have hann_hom : Module.annihilator R (M →ₗ[R] N) ≤ p := by
      simpa [Submodule.annihilator_top] using (IsAssociatedPrime.annihilator_le hprime)
    have hMann : Module.annihilator R M ≤ p :=
      (annihilator_le_annihilator_linearMap (R := R) (M := M) (N := N)).trans hann_hom
    exact ⟨hpN, hMann⟩
  · intro hp
    exact associatedPrimes_linearMap_superset_via_localization (R := R) (M := M) (N := N)
      (hp := hp.1) (hann := hp.2)

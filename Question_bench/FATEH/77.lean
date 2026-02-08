import Mathlib

/-- The residue-field map is already surjective on the image of `k`, hence on `R`. -/
lemma surjective_residue_comp_algebraMap_R {k R A : Type*} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra R A] [Algebra k A] [IsScalarTower k R A] [IsLocalRing A]
    (h : Function.Surjective ((IsLocalRing.residue A).comp (algebraMap k A))) :
    Function.Surjective ((IsLocalRing.residue A).comp (algebraMap R A)) := by
  intro y
  rcases h y with ⟨x, hx⟩
  refine ⟨algebraMap k R x, ?_⟩
  have hx' : (IsLocalRing.residue A) (algebraMap k A x) = y := by
    simpa [RingHom.comp_apply] using hx
  simpa [IsScalarTower.algebraMap_apply (R := k) (S := R) (A := A)] using hx'

/-- Units in `A` avoid the kernel of the residue map on `R`. -/
lemma mem_primeCompl_of_isUnit_residue_comp {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [IsLocalRing A] (r : R) (hr : IsUnit (algebraMap R A r))
    [hprime : (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).IsPrime] :
    r ∈ (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).primeCompl := by
  let f : R →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (algebraMap R A)
  change r ∈ (RingHom.ker f).primeCompl
  haveI : (RingHom.ker f).IsPrime := by
    simpa [f] using (inferInstance :
      (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).IsPrime)
  refine (Ideal.mem_primeCompl_iff (P := RingHom.ker f) (x := r)).2 ?_
  intro hr_in
  have hne : f r ≠ 0 := by
    simpa [f, RingHom.comp_apply] using
      (IsLocalRing.residue_ne_zero_iff_isUnit (x := algebraMap R A r)).2 hr
  have : f r = 0 := by
    simpa [RingHom.mem_ker] using hr_in
  exact hne this

/-- Elements outside the kernel of the residue map are units in `A`. -/
lemma isUnit_of_mem_primeCompl_residue_comp {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [IsLocalRing A] (r : R)
    [hprime : (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).IsPrime]
    (hr : r ∈ (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).primeCompl) :
    IsUnit (algebraMap R A r) := by
  let f : R →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (algebraMap R A)
  change r ∈ (RingHom.ker f).primeCompl at hr
  haveI : (RingHom.ker f).IsPrime := by
    simpa [f] using (inferInstance :
      (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).IsPrime)
  have hr' : r ∉ RingHom.ker f :=
    (Ideal.mem_primeCompl_iff (P := RingHom.ker f) (x := r)).1 hr
  have hne : f r ≠ 0 := by
    intro hfr
    exact hr' (by simpa [RingHom.mem_ker] using hfr)
  have hne' : (IsLocalRing.residue A) (algebraMap R A r) ≠ 0 := by
    simpa [f, RingHom.comp_apply] using hne
  exact (IsLocalRing.residue_ne_zero_iff_isUnit (x := algebraMap R A r)).1 hne'

/--Let \( k \) be a field, \( A \) a local \( k \)-algebra with maximal ideal \( \mathfrak{m} \).
Assume that \( A \) is a localization of a \( k \)-algebra \( R \) and that \( A / \mathfrak{m} = k
\). Prove that there exists maximal ideal \( \mathfrak{n} \) of \( R \) with \( R_{\mathfrak{n}} = A
\).-/
theorem exists_isMaximal_atPrime_of_bijective {k R A : Type} [Field k] [CommRing R] [CommRing A] [Algebra k R]
    [Algebra R A] [Algebra k A] [IsScalarTower k R A] [IsLocalRing A]
    (h : Function.Bijective <| (IsLocalRing.residue A).comp (algebraMap k A))
    (S : Submonoid R) [IsLocalization S A] :
    ∃ n : Ideal R, ∃ _ : n.IsMaximal, IsLocalization.AtPrime A n := by
  let f : R →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (algebraMap R A)
  let n : Ideal R := RingHom.ker f
  have hsurj : Function.Surjective f := by
    simpa [f] using
      (surjective_residue_comp_algebraMap_R (k := k) (R := R) (A := A) h.surjective)
  have hn : n.IsMaximal := by
    simpa [n] using (RingHom.ker_isMaximal_of_surjective f hsurj)
  haveI : n.IsPrime := hn.isPrime
  haveI : (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).IsPrime := by
    simpa [n, f] using (hn.isPrime)
  have hS : S ≤ n.primeCompl := by
    intro s hs
    have hsunit : IsUnit (algebraMap R A s) := by
      simpa using (IsLocalization.map_units (S := A) (M := S) ⟨s, hs⟩)
    simpa [n, f] using (mem_primeCompl_of_isUnit_residue_comp (r := s) hsunit)
  have h_units : ∀ r ∈ n.primeCompl, IsUnit (algebraMap R A r) := by
    intro r hr
    have hr' :
        r ∈ (RingHom.ker ((IsLocalRing.residue A).comp (algebraMap R A))).primeCompl := by
      simpa [n, f] using hr
    simpa using (isUnit_of_mem_primeCompl_residue_comp (r := r) hr')
  refine ⟨n, hn, ?_⟩
  have hloc : IsLocalization n.primeCompl A :=
    IsLocalization.of_le (M := S) (S := A) (N := n.primeCompl) hS h_units
  simpa [IsLocalization.AtPrime] using hloc

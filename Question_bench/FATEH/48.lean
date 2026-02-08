import Mathlib

noncomputable section
open scoped Cardinal

/-- Construct the permutation-induced automorphism of the transcendence basis in the adjoin. -/
noncomputable def adjoinPerm {ι : Type*} {v : ι → ℂ}
    (hv : IsTranscendenceBasis ℚ v) (e : Equiv.Perm ι) :
    Algebra.adjoin ℚ (Set.range v) ≃+* Algebra.adjoin ℚ (Set.range v) := by
  refine (hv.1.aevalEquiv.symm.toRingEquiv.trans
      (AlgEquiv.ofAlgHom (MvPolynomial.rename e) (MvPolynomial.rename e.symm) ?_ ?_).toRingEquiv
    ).trans hv.1.aevalEquiv.toRingEquiv
  · ext; simp
  · ext; simp

/-- `adjoinPerm` sends a basis element to its permuted counterpart. -/
lemma adjoinPerm_apply_X {ι : Type*} {v : ι → ℂ} (hv : IsTranscendenceBasis ℚ v)
    (e : Equiv.Perm ι) (i : ι) :
    adjoinPerm hv e (hv.1.aevalEquiv (MvPolynomial.X i)) =
      hv.1.aevalEquiv (MvPolynomial.X (e i)) := by
  have hsymm :
      ((↑(hv.1.aevalEquiv) : MvPolynomial ι ℚ ≃+* _).symm
        (hv.1.aevalEquiv (MvPolynomial.X i))) = MvPolynomial.X i := by
    simpa using
      (RingEquiv.symm_apply_apply (e := hv.1.aevalEquiv.toRingEquiv) (MvPolynomial.X i))
  simp [adjoinPerm, RingEquiv.trans_apply, hsymm, MvPolynomial.rename_X]

/-- Lift a permutation of a transcendence basis to a `ℚ`-algebra automorphism of `ℂ`. -/
noncomputable def permToAlgEquiv {ι : Type*} {v : ι → ℂ}
    (hv : IsTranscendenceBasis ℚ v) (e : Equiv.Perm ι) : ℂ ≃ₐ[ℚ] ℂ := by
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis (v:=v) hv
  refine AlgEquiv.ofRingEquiv (f :=
    IsAlgClosure.equivOfEquiv ℂ ℂ (adjoinPerm hv e)) ?_
  intro r
  simp

/-- `permToAlgEquiv` acts by permuting the basis elements. -/
lemma permToAlgEquiv_apply {ι : Type*} {v : ι → ℂ}
    (hv : IsTranscendenceBasis ℚ v) (e : Equiv.Perm ι) (i : ι) :
    permToAlgEquiv hv e (v i) = v (e i) := by
  classical
  letI := IsAlgClosed.isAlgClosure_of_transcendence_basis (v:=v) hv
  have hvi :
      algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ
        (hv.1.aevalEquiv (MvPolynomial.X i)) = v i := by
    simp
  have hvi' :
      algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ
        (hv.1.aevalEquiv (MvPolynomial.X (e i))) = v (e i) := by
    simp
  have hmap :=
    (IsAlgClosure.equivOfEquiv_algebraMap (L:=ℂ) (M:=ℂ)
      (hSR := adjoinPerm hv e) (s := hv.1.aevalEquiv (MvPolynomial.X i)))
  calc
    permToAlgEquiv hv e (v i)
        = IsAlgClosure.equivOfEquiv ℂ ℂ (adjoinPerm hv e) (v i) := by
            simp [permToAlgEquiv, AlgEquiv.ofRingEquiv_apply]
    _ = IsAlgClosure.equivOfEquiv ℂ ℂ (adjoinPerm hv e)
          (algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ
            (hv.1.aevalEquiv (MvPolynomial.X i))) := by
          simp [hvi]
    _ = algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ
          (adjoinPerm hv e (hv.1.aevalEquiv (MvPolynomial.X i))) := by
          simpa using hmap
    _ = algebraMap (Algebra.adjoin ℚ (Set.range v)) ℂ
          (hv.1.aevalEquiv (MvPolynomial.X (e i))) := by
          simp [adjoinPerm_apply_X]
    _ = v (e i) := hvi'

/-- The map `permToAlgEquiv` is injective. -/
lemma permToAlgEquiv_injective {ι : Type*} {v : ι → ℂ}
    (hv : IsTranscendenceBasis ℚ v) : Function.Injective (permToAlgEquiv hv) := by
  intro e₁ e₂ h
  apply Equiv.ext
  intro i
  have hv_inj : Function.Injective v := hv.1.injective
  have hval : v (e₁ i) = v (e₂ i) := by
    have := congrArg (fun f => f (v i)) h
    simpa [permToAlgEquiv_apply hv] using this
  exact hv_inj hval

/-- Prove that the cardinality $\mathrm{Aut}(\CC)$ (i.e. the group of field automorphism of $\CC$)
is infinite. -/
theorem infinite_complex_algEquiv : Infinite (ℂ ≃ₐ[ℚ] ℂ) := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hR : (#ℚ) ≤ ℵ₀ := by
    simp
  have hK : ℵ₀ < #ℂ := by
    simpa [Cardinal.mk_complex] using Cardinal.aleph0_lt_continuum
  have hcard : #ℂ = #s := by
    simpa using
      (IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
        (v' := (fun x : s => (x : ℂ))) (R:=ℚ) (K':=ℂ) hs hR hK)
  have hs_infinite : Infinite s := by
    have hs_card : ℵ₀ < #s := by
      simpa [hcard] using hK
    exact (Cardinal.infinite_iff).2 (le_of_lt hs_card)
  have : Infinite (Equiv.Perm s) := by infer_instance
  exact Infinite.of_injective (permToAlgEquiv hs) (permToAlgEquiv_injective hs)

end

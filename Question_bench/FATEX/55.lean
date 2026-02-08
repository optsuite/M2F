import Mathlib

universe u v w

/--
A module \( M \) over a ring \( R \) is \textit{stably free} if there exists a free finitely generated module \( F \) over \( R \) such that
\[
M \oplus F
\]
is a free module.
-/
def IsStablyFree (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] : Prop :=
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N),
    Module.Finite R N ∧ Module.Free R N ∧ Module.Free R (M × N)

/-- A free module is stably free by adding a free rank-one summand. -/
lemma stablyFree_of_free_via_self (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] : Module.Free R M → IsStablyFree R M := by
  intro hFree
  haveI := hFree
  refine ⟨R, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · infer_instance

/-- The range of a linear map from a finite module into a `finsupp` module is supported
on a finite set of indices. -/
lemma fg_range_le_supported_of_moduleFinite {R ι N : Type*} [CommRing R] [AddCommGroup N]
    [Module R N] [Module.Finite R N] (f : N →ₗ[R] (ι →₀ R)) :
    ∃ S : Finset ι, LinearMap.range f ≤ Finsupp.supported R R (S : Set ι) := by
  classical
  let P : Submodule R (ι →₀ R) := LinearMap.range f
  have hP : Module.Finite R P := by infer_instance
  obtain ⟨n, s, hs⟩ := (Module.Finite.exists_fin (R := R) (M := P))
  let S : Finset ι :=
    Finset.biUnion (Finset.univ : Finset (Fin n)) (fun i => (s i).1.support)
  let tset : Set (ι →₀ R) := (fun a : P => (a : ι →₀ R)) '' Set.range s
  refine ⟨S, ?_⟩
  have hspan :
      Submodule.span R tset = P := by
    have hmap :
        Submodule.map P.subtype (Submodule.span R (Set.range s)) = Submodule.span R tset := by
      simpa [tset] using
        (LinearMap.map_span (f := P.subtype) (s := Set.range s))
    have hmap' :
        Submodule.map P.subtype (Submodule.span R (Set.range s)) = P := by
      simp [hs]
    exact (hmap'.symm.trans hmap).symm
  have hle :
      P ≤ Finsupp.supported R R
        (⋃ x ∈ tset, x.support) := by
    have hspan' : Submodule.span R tset = P := hspan
    have hle' :
        Submodule.span R tset ≤ Finsupp.supported R R (⋃ x ∈ tset, x.support) :=
      Finsupp.span_le_supported_biUnion_support (R := R) (M := R) (s := tset)
    simpa [hspan'] using hle'
  have hsubset :
      (⋃ x ∈ tset, x.support) ⊆ (S : Set ι) := by
    intro a ha
    rcases Set.mem_iUnion.mp ha with ⟨x, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨hxrange, hxmem⟩
    rcases hxrange with ⟨y, hy, rfl⟩
    rcases hy with ⟨i, rfl⟩
    have hi : i ∈ (Finset.univ : Finset (Fin n)) := by simp
    have hsubset' :
        (s i).1.support ⊆ S := by
      exact Finset.subset_biUnion_of_mem (s := Finset.univ)
        (u := fun j => (s j).1.support) hi
    have hxmem' : a ∈ (s i).1.support := by
      simpa using hxmem
    have ha' : a ∈ S := hsubset' hxmem'
    simpa using ha'
  intro x hx
  have hx' : x ∈ Finsupp.supported R R (⋃ x ∈ tset, x.support) := hle hx
  exact (Finsupp.supported_mono (M := R) (R := R) hsubset) hx'

/-- If the left factor is not finitely generated, then the product is not finitely generated. -/
lemma not_moduleFinite_prod_of_not_left {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (h : ¬ Module.Finite R M) :
    ¬ Module.Finite R (M × N) := by
  intro hMN
  apply h
  haveI : Module.Finite R (M × N) := hMN
  have hsurj : Function.Surjective (LinearMap.fst R M N) := by
    intro m
    refine ⟨(m, 0), ?_⟩
    rfl
  exact Module.Finite.of_surjective (LinearMap.fst R M N) hsurj

/-- A free module which is not finitely generated has an infinite chosen basis index type. -/
lemma infinite_chooseBasisIndex_of_free_not_moduleFinite {R P : Type*} [CommRing R] [AddCommGroup P]
    [Module R P] [Nontrivial R] [Module.Free R P] (h : ¬ Module.Finite R P) :
    Infinite (Module.Free.ChooseBasisIndex R P) := by
  classical
  by_contra hfinite
  haveI : Finite (Module.Free.ChooseBasisIndex R P) :=
    Finite.of_not_infinite hfinite
  classical
  haveI : Fintype (Module.Free.ChooseBasisIndex R P) := Fintype.ofFinite _
  have : Module.Finite R P := Module.Finite.of_basis (Module.Free.chooseBasis R P)
  exact h this

/-- The image of `inr` in free coordinates is supported on finitely many indices. -/
lemma exists_finset_supporting_inr_range_in_free_coords {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Free R (M × N)] [Module.Finite R N] :
    ∃ S : Finset (Module.Free.ChooseBasisIndex R (M × N)),
      LinearMap.range
          ((Module.Free.chooseBasis R (M × N)).repr.toLinearMap.comp (LinearMap.inr R M N)) ≤
        Finsupp.supported R R (S : Set (Module.Free.ChooseBasisIndex R (M × N))) := by
  classical
  simpa using
    (fg_range_le_supported_of_moduleFinite
      (f := (Module.Free.chooseBasis R (M × N)).repr.toLinearMap.comp (LinearMap.inr R M N)))

/-- Split `ι →₀ R` into coordinates supported on a finite set and its complement. -/
noncomputable def finsupp_split_on_finset_support {R ι : Type*} [CommRing R] [DecidableEq ι]
    (S : Finset ι) :
    (ι →₀ R) ≃ₗ[R]
      ({ i // i ∈ (S : Set ι) } →₀ R) × ({ i // i ∉ (S : Set ι) } →₀ R) :=
  (Finsupp.domLCongr (Equiv.sumCompl (fun i => i ∈ (S : Set ι))).symm).trans
    (Finsupp.sumFinsuppLEquivProdFinsupp (R := R) (M := R))

/-- If a `finsupp` is supported on `S`, then its complement-coordinate part is zero
after splitting along `S`. -/
lemma finsupp_split_on_finset_support_snd_eq_zero_of_mem_supported
    {R ι : Type*} [CommRing R] [DecidableEq ι] (S : Finset ι) {x : ι →₀ R}
    (hx : x ∈ Finsupp.supported R R (S : Set ι)) :
    ((finsupp_split_on_finset_support (R:=R) (ι:=ι) S) x).2 = 0 := by
  classical
  ext i
  have hx' := (Finsupp.mem_supported' (R:=R) (p:=x) (s:= (S : Set ι))).1 hx
  have hxi : x i.1 = 0 := hx' i.1 i.property
  have hval :
      ((finsupp_split_on_finset_support (R:=R) (ι:=ι) S) x).2 i =
        x ((Equiv.sumCompl (fun j => j ∈ (S : Set ι)) (Sum.inr i))) := by
    simp [finsupp_split_on_finset_support, Finsupp.domLCongr_apply,
      Finsupp.equivMapDomain_apply]
  have hsum : (Equiv.sumCompl (fun j => j ∈ (S : Set ι)) (Sum.inr i)) = (i : ι) := rfl
  calc
    ((finsupp_split_on_finset_support (R:=R) (ι:=ι) S) x).2 i
        = x ((Equiv.sumCompl (fun j => j ∈ (S : Set ι)) (Sum.inr i))) := hval
    _ = x (i : ι) := by rw [hsum]
    _ = 0 := hxi

/-- If `π : M × N →ₗ V` is surjective and vanishes on the right summand, then
its restriction along `inl` is surjective. -/
lemma surjective_projection_to_complement_coords
    {R M N V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup V] [Module R V]
    (π : M × N →ₗ[R] V) (hπ : Function.Surjective π)
    (hπinr : π.comp (LinearMap.inr R M N) = 0) :
    Function.Surjective (π.comp (LinearMap.inl R M N)) := by
  intro v
  rcases hπ v with ⟨p, hp⟩
  refine ⟨p.1, ?_⟩
  have hπinr' : π (0, p.2) = 0 := by
    have := congrArg (fun f => f p.2) hπinr
    simpa using this
  have hpdecomp : p = (p.1, 0) + (0, p.2) := by
    ext <;> simp
  have hpdecomp' : π p = π ((p.1, 0) + (0, p.2)) := by
    exact congrArg π hpdecomp
  have hp' : π (p.1, 0) + π (0, p.2) = v := by
    calc
      π (p.1, 0) + π (0, p.2) = π ((p.1, 0) + (0, p.2)) := by
        simpa using (map_add π (p.1, 0) (0, p.2)).symm
      _ = π p := by simpa using hpdecomp'.symm
      _ = v := hp
  have hpinl : π (p.1, 0) = v := by
    have hp'' : π (p.1, 0) + 0 = v := by
      simpa [hπinr'] using hp'
    simpa using hp''
  simpa using hpinl

/-- A surjective map onto a projective module splits, giving `M ≃ ker ψ × V`. -/
theorem linearEquiv_ker_prod_of_projective_split_exists
    {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [Module.Projective R V]
    (ψ : M →ₗ[R] V) (hψ : Function.Surjective ψ) :
    ∃ e : M ≃ₗ[R] (LinearMap.ker ψ) × V, e = e := by
  classical
  have hσexists : ∃ σ : V →ₗ[R] M, ψ ∘ₗ σ = LinearMap.id :=
    ψ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hψ)
  let σ : V →ₗ[R] M := Classical.choose hσexists
  have hσ : ψ ∘ₗ σ = LinearMap.id := Classical.choose_spec hσexists
  have hσinj : Function.Injective σ := by
    intro v v' hv
    have hv1 : ψ (σ v) = v := by
      have := congrArg (fun f => f v) hσ
      simpa using this
    have hv2 : ψ (σ v') = v' := by
      have := congrArg (fun f => f v') hσ
      simpa using this
    calc
      v = ψ (σ v) := hv1.symm
      _ = ψ (σ v') := by simpa [hv]
      _ = v' := hv2
  have hdisj : Disjoint (LinearMap.ker ψ) (LinearMap.range σ) := by
    refine (disjoint_iff).2 ?_
    apply (Submodule.eq_bot_iff (p := LinearMap.ker ψ ⊓ LinearMap.range σ)).2
    intro x hx
    have hxker : x ∈ LinearMap.ker ψ := (Submodule.mem_inf.mp hx).1
    have hxrange : x ∈ LinearMap.range σ := (Submodule.mem_inf.mp hx).2
    rcases hxrange with ⟨v, rfl⟩
    have hxker' : ψ (σ v) = 0 := hxker
    have hv : v = 0 := by
      have hv' : ψ (σ v) = v := by
        have := congrArg (fun f => f v) hσ
        simpa using this
      exact hv'.symm.trans hxker'
    simpa [hv]
  have hcodisj : Codisjoint (LinearMap.ker ψ) (LinearMap.range σ) := by
    refine (Submodule.codisjoint_iff_exists_add_eq).2 ?_
    intro z
    refine ⟨z - σ (ψ z), σ (ψ z), ?_, ?_, ?_⟩
    · change ψ (z - σ (ψ z)) = 0
      have hσz : ψ (σ (ψ z)) = ψ z := by
        have := congrArg (fun f => f (ψ z)) hσ
        simpa using this
      calc
        ψ (z - σ (ψ z)) = ψ z - ψ (σ (ψ z)) := by simp
        _ = ψ z - ψ z := by simp [hσz]
        _ = 0 := sub_self _
    · exact ⟨ψ z, rfl⟩
    · simp
  have hcompl : IsCompl (LinearMap.ker ψ) (LinearMap.range σ) := ⟨hdisj, hcodisj⟩
  have e1 : (LinearMap.ker ψ × LinearMap.range σ) ≃ₗ[R] M :=
    Submodule.prodEquivOfIsCompl (LinearMap.ker ψ) (LinearMap.range σ) hcompl
  have e2 : (LinearMap.range σ) ≃ₗ[R] V :=
    (LinearEquiv.ofInjective σ hσinj).symm
  let e : M ≃ₗ[R] (LinearMap.ker ψ) × V :=
    e1.symm.trans (LinearEquiv.prodCongr (LinearEquiv.refl R (LinearMap.ker ψ)) e2)
  refine ⟨e, ?_⟩
  rfl

/-- The splitting equivalence `M ≃ ker ψ × V`. -/
noncomputable def linearEquiv_ker_prod_of_projective_split
    {R M V : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup V] [Module R V] [Module.Projective R V]
    (ψ : M →ₗ[R] V) (hψ : Function.Surjective ψ) :
    M ≃ₗ[R] (LinearMap.ker ψ) × V :=
  Classical.choose (linearEquiv_ker_prod_of_projective_split_exists (ψ := ψ) hψ)

/-- The kernel of the left projection is stably free when the right summand is killed. -/
lemma kernel_isStablyFree_via_supported_part
    {R : Type u} {M : Type v} {N : Type u} {U V : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Free R N] [AddCommGroup U] [Module R U]
    [Module.Free R U] [AddCommGroup V] [Module R V]
    (e : (M × N) ≃ₗ[R] (U × V))
    (hπinr :
      ((LinearMap.snd R U V).comp (LinearEquiv.toLinearMap e)).comp
        (LinearMap.inr R M N) = 0) :
    IsStablyFree R
      (↥(LinearMap.ker (((LinearMap.snd R U V).comp (LinearEquiv.toLinearMap e)).comp
        (LinearMap.inl R M N)))) := by
  classical
  let π : M × N →ₗ[R] V := (LinearMap.snd R U V).comp (LinearEquiv.toLinearMap e)
  let ψ : M →ₗ[R] V := π.comp (LinearMap.inl R M N)
  have hπinr' : π.comp (LinearMap.inr R M N) = 0 := by
    simpa [π] using hπinr
  let i : (LinearMap.ker ψ × N) →ₗ[R] M × N :=
    (LinearMap.prodMap (Submodule.subtype (LinearMap.ker ψ)) (LinearMap.id))
  let f : (LinearMap.ker ψ × N) →ₗ[R] U :=
    (LinearMap.fst R U V).comp ((LinearEquiv.toLinearMap e).comp i)
  have hf_surj : Function.Surjective f := by
    intro u
    let p : M × N := e.symm (u, 0)
    have hpe : e p = (u, 0) := by
      simpa [p] using e.apply_symm_apply (u, 0)
    have hπp : π p = 0 := by
      simpa [π, p, hpe]
    have hπinr_eval : π (LinearMap.inr R M N p.2) = 0 := by
      have := congrArg (fun f => f p.2) hπinr'
      simpa using this
    have hpdecomp : p = LinearMap.inl R M N p.1 + LinearMap.inr R M N p.2 := by
      ext <;> simp
    have hpdecomp' :
        LinearMap.inl R M N p.1 + LinearMap.inr R M N p.2 = p := by
      simpa using hpdecomp.symm
    have hπp' :
        π (LinearMap.inl R M N p.1) + π (LinearMap.inr R M N p.2) = 0 := by
      calc
        π (LinearMap.inl R M N p.1) + π (LinearMap.inr R M N p.2) =
            π (LinearMap.inl R M N p.1 + LinearMap.inr R M N p.2) := by
          simpa using
            (map_add π (LinearMap.inl R M N p.1) (LinearMap.inr R M N p.2)).symm
        _ = π p := by rw [hpdecomp']
        _ = 0 := hπp
    have hπinl : π (LinearMap.inl R M N p.1) = 0 := by
      have hπp'' : π (LinearMap.inl R M N p.1) + 0 = 0 := by
        calc
          π (LinearMap.inl R M N p.1) + 0 =
              π (LinearMap.inl R M N p.1) + π (LinearMap.inr R M N p.2) := by
            rw [← hπinr_eval]
          _ = 0 := hπp'
      simpa using hπp''
    have hψp1 : ψ p.1 = 0 := by
      simpa [ψ, LinearMap.comp_apply] using hπinl
    refine ⟨⟨⟨p.1, hψp1⟩, p.2⟩, ?_⟩
    have hi : i ⟨⟨p.1, hψp1⟩, p.2⟩ = p := by
      ext <;> simp [i]
    calc
      f ⟨⟨p.1, hψp1⟩, p.2⟩ = (e (i ⟨⟨p.1, hψp1⟩, p.2⟩)).1 := rfl
      _ = (e p).1 := by simp [hi]
      _ = u := by simpa [hpe]
  have hf_inj : Function.Injective f := by
    intro x y hxy
    have hπinr_eval : ∀ n, π (LinearMap.inr R M N n) = 0 := by
      intro n
      have := congrArg (fun f => f n) hπinr'
      simpa using this
    have hπx : π (i x) = 0 := by
      have hxker : ψ x.1 = 0 := x.1.property
      have hπinl : π (LinearMap.inl R M N (x.1 : M)) = 0 := by
        have hxker' := hxker
        dsimp [ψ] at hxker'
        simpa [LinearMap.comp_apply] using hxker'
      have hxdecomp :
          i x = LinearMap.inl R M N (x.1 : M) + LinearMap.inr R M N x.2 := by
        ext <;> simp [i]
      calc
        π (i x) =
            π (LinearMap.inl R M N (x.1 : M) + LinearMap.inr R M N x.2) := by
          rw [hxdecomp]
        _ = π (LinearMap.inl R M N (x.1 : M)) + π (LinearMap.inr R M N x.2) := by
          simpa using
            (map_add π (LinearMap.inl R M N (x.1 : M)) (LinearMap.inr R M N x.2))
        _ = 0 := by
          calc
            π (LinearMap.inl R M N (x.1 : M)) + π (LinearMap.inr R M N x.2) =
                0 + 0 := by rw [hπinl, hπinr_eval]
            _ = 0 := by simp
    have hπy : π (i y) = 0 := by
      have hyker : ψ y.1 = 0 := y.1.property
      have hπinl : π (LinearMap.inl R M N (y.1 : M)) = 0 := by
        have hyker' := hyker
        dsimp [ψ] at hyker'
        simpa [LinearMap.comp_apply] using hyker'
      have hydecomp :
          i y = LinearMap.inl R M N (y.1 : M) + LinearMap.inr R M N y.2 := by
        ext <;> simp [i]
      calc
        π (i y) =
            π (LinearMap.inl R M N (y.1 : M) + LinearMap.inr R M N y.2) := by
          rw [hydecomp]
        _ = π (LinearMap.inl R M N (y.1 : M)) + π (LinearMap.inr R M N y.2) := by
          simpa using
            (map_add π (LinearMap.inl R M N (y.1 : M)) (LinearMap.inr R M N y.2))
        _ = 0 := by
          calc
            π (LinearMap.inl R M N (y.1 : M)) + π (LinearMap.inr R M N y.2) =
                0 + 0 := by rw [hπinl, hπinr_eval]
            _ = 0 := by simp
    have hEx : e (i x) = (f x, 0) := by
      apply Prod.ext
      · rfl
      · simpa [π] using hπx
    have hEy : e (i y) = (f y, 0) := by
      apply Prod.ext
      · rfl
      · simpa [π] using hπy
    have hE : e (i x) = e (i y) := by
      calc
        e (i x) = (f x, 0) := hEx
        _ = (f y, 0) := by simpa [hxy]
        _ = e (i y) := hEy.symm
    have hI : i x = i y := e.injective hE
    have hx1m : (x.1 : M) = (y.1 : M) := by
      have hI1 := congrArg Prod.fst hI
      simpa [i] using hI1
    have hx2 : x.2 = y.2 := by
      have hI2 := congrArg Prod.snd hI
      simpa [i] using hI2
    apply Prod.ext
    · apply Subtype.ext
      exact hx1m
    · exact hx2
  have eKer : (LinearMap.ker ψ × N) ≃ₗ[R] U :=
    LinearEquiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hKerFree : Module.Free R (LinearMap.ker ψ × N) :=
    Module.Free.of_equiv eKer.symm
  refine ⟨N, inferInstance, inferInstance, ?_, ?_, hKerFree⟩
  · infer_instance
  · infer_instance

/-- A `finsupp` over an infinite index type absorbs any finite free summand. -/
theorem finsupp_absorbs_finite_summand_of_infinite_index_exists
    {R : Type u} {α β : Type w} [CommRing R] [Infinite α] [Finite β] :
    ∃ e : (α →₀ R) ≃ₗ[R] (β →₀ R) × (α →₀ R), e = e := by
  classical
  have hbeta_le : Cardinal.mk β ≤ Cardinal.mk α := by
    have hbeta_lt : Cardinal.mk β < Cardinal.aleph0 := Cardinal.mk_lt_aleph0
    have hbeta_le' : Cardinal.mk β ≤ Cardinal.aleph0 := le_of_lt hbeta_lt
    exact le_trans hbeta_le' (Cardinal.aleph0_le_mk α)
  have hcard : Cardinal.mk (Sum β α) = Cardinal.mk α := by
    have h := Cardinal.add_eq_right (Cardinal.aleph0_le_mk α) hbeta_le
    simpa [Cardinal.mk_sum] using h
  have hEquiv : Nonempty (Sum β α ≃ α) := (Cardinal.eq.1 hcard)
  let e : Sum β α ≃ α := Classical.choice hEquiv
  let e' : (α →₀ R) ≃ₗ[R] (β →₀ R) × (α →₀ R) :=
    (Finsupp.domLCongr e.symm).trans
      (Finsupp.sumFinsuppLEquivProdFinsupp (R := R) (M := R))
  refine ⟨e', ?_⟩
  rfl

/-- The absorbing equivalence on `finsupp` for infinite index types. -/
noncomputable def finsupp_absorbs_finite_summand_of_infinite_index
    {R : Type u} {α β : Type w} [CommRing R] [Infinite α] [Finite β] :
    (α →₀ R) ≃ₗ[R] (β →₀ R) × (α →₀ R) :=
  Classical.choose
    (finsupp_absorbs_finite_summand_of_infinite_index_exists
      (R := R) (α := α) (β := β))

/--
Prove that if $M$ is stably free and not finitely generated then $M$ is free.
-/
theorem stablyFree_iff_free_of_not_fg (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M]
    [Module R M] (h : ¬ Module.Finite R M) : Module.Free R M ↔ IsStablyFree R M := by
  constructor
  · exact stablyFree_of_free_via_self R M
  · intro hStablyFree
    classical
    cases subsingleton_or_nontrivial R with
    | inl hR =>
        haveI : Subsingleton R := hR
        simpa using (Module.Free.of_subsingleton' (R := R) (N := M))
    | inr hR =>
        haveI : Nontrivial R := hR
        rcases hStablyFree with ⟨N, _instN, _instMN, hNfinite, hNfree, hMNfree⟩
        haveI : Module.Free R N := hNfree
        haveI : Module.Free R (M × N) := hMNfree
        haveI : Module.Finite R N := hNfinite
        have hMNnotfinite : ¬ Module.Finite R (M × N) :=
          not_moduleFinite_prod_of_not_left (R := R) (M := M) (N := N) h
        have hIinf : Infinite (Module.Free.ChooseBasisIndex R (M × N)) :=
          infinite_chooseBasisIndex_of_free_not_moduleFinite (R := R) (P := M × N) hMNnotfinite
        obtain ⟨S, hS⟩ :=
          exists_finset_supporting_inr_range_in_free_coords (R := R) (M := M) (N := N)
        let ι := Module.Free.ChooseBasisIndex R (M × N)
        let U := ({ i // i ∈ (S : Set ι) } →₀ R)
        let V := ({ i // i ∉ (S : Set ι) } →₀ R)
        let e : (M × N) ≃ₗ[R] (U × V) :=
          (Module.Free.chooseBasis R (M × N)).repr.trans
            (finsupp_split_on_finset_support (R := R) (ι := ι) S)
        let π : (M × N) →ₗ[R] V :=
          (LinearMap.snd R U V).comp (LinearEquiv.toLinearMap e)
        let ψ : M →ₗ[R] V := π.comp (LinearMap.inl R M N)
        have hπinr : π.comp (LinearMap.inr R M N) = 0 := by
          ext n a
          have hn :
              ((Module.Free.chooseBasis R (M × N)).repr.toLinearMap.comp
                (LinearMap.inr R M N)) n ∈ Finsupp.supported R R (S : Set ι) :=
            hS ⟨n, rfl⟩
          have hzero :
              ((finsupp_split_on_finset_support (R := R) (ι := ι) S)
                ((Module.Free.chooseBasis R (M × N)).repr
                  (LinearMap.inr R M N n))).2 = 0 :=
            finsupp_split_on_finset_support_snd_eq_zero_of_mem_supported
              (R := R) (ι := ι) S (by simpa using hn)
          have hzero_eval :
              ((finsupp_split_on_finset_support (R := R) (ι := ι) S)
                ((Module.Free.chooseBasis R (M × N)).repr
                  (LinearMap.inr R M N n))).2 a = 0 := by
            have := congrArg (fun f => f a) hzero
            simpa using this
          simpa [π, e] using hzero_eval
        have hπsurj : Function.Surjective π := by
          intro v
          refine ⟨e.symm (0, v), ?_⟩
          simp [π]
        have hψsurj : Function.Surjective ψ :=
          surjective_projection_to_complement_coords π hπsurj hπinr
        haveI : Module.Free R V := inferInstance
        have eKerV : M ≃ₗ[R] (LinearMap.ker ψ) × V :=
          linearEquiv_ker_prod_of_projective_split ψ hψsurj
        have hKerStably : IsStablyFree R (LinearMap.ker ψ) := by
          simpa [π, ψ] using
            (kernel_isStablyFree_via_supported_part (e := e) (hπinr := hπinr))
        rcases hKerStably with
          ⟨Nker, _instNker, _instModNker, hNkerfinite, hNkerfree, hKerFree⟩
        haveI : Module.Free R Nker := hNkerfree
        haveI : Module.Finite R Nker := hNkerfinite
        haveI : Infinite ι := hIinf
        have hInfSet : (S : Set ι)ᶜ.Infinite :=
          (Set.Finite.infinite_compl (s := (S : Set ι)) S.finite_toSet)
        haveI : Infinite { i // i ∉ (S : Set ι) } := by
          simpa using (Set.infinite_coe_iff.2 hInfSet)
        let β := Module.Free.ChooseBasisIndex R Nker
        haveI : Finite β := by infer_instance
        let β' := ULift β
        haveI : Finite β' := by infer_instance
        let eNker : Nker ≃ₗ[R] (β →₀ R) := (Module.Free.chooseBasis R Nker).repr
        let eβ : (β' →₀ R) ≃ₗ[R] (β →₀ R) :=
          Finsupp.domLCongr (Equiv.ulift)
        let eNker' : Nker ≃ₗ[R] (β' →₀ R) := eNker.trans eβ.symm
        have eV : V ≃ₗ[R] (β' →₀ R) × V :=
          finsupp_absorbs_finite_summand_of_infinite_index
            (R := R) (α := { i // i ∉ (S : Set ι) }) (β := β')
        have eV' : V ≃ₗ[R] Nker × V :=
          eV.trans (LinearEquiv.prodCongr eNker'.symm (LinearEquiv.refl R V))
        have eV'' : V ≃ₗ[R] V × Nker :=
          eV'.trans (LinearEquiv.prodComm R Nker V)
        have eKerVN :
            (LinearMap.ker ψ × V) ≃ₗ[R] (LinearMap.ker ψ × Nker) × V := by
          have e1 :
              (LinearMap.ker ψ × V) ≃ₗ[R] (LinearMap.ker ψ × (V × Nker)) :=
            LinearEquiv.prodCongr (LinearEquiv.refl R (LinearMap.ker ψ)) eV''
          have e2 :
              (LinearMap.ker ψ × (V × Nker)) ≃ₗ[R] (LinearMap.ker ψ × (Nker × V)) :=
            LinearEquiv.prodCongr (LinearEquiv.refl R (LinearMap.ker ψ))
              (LinearEquiv.prodComm R V Nker)
          have e3 :
              (LinearMap.ker ψ × (Nker × V)) ≃ₗ[R] (LinearMap.ker ψ × Nker) × V :=
            (LinearEquiv.prodAssoc R (LinearMap.ker ψ) Nker V).symm
          exact e1.trans (e2.trans e3)
        haveI : Module.Free R (LinearMap.ker ψ × Nker) := hKerFree
        haveI : Module.Free R ((LinearMap.ker ψ × Nker) × V) := inferInstance
        have hKerVFree : Module.Free R (LinearMap.ker ψ × V) :=
          Module.Free.of_equiv eKerVN.symm
        exact Module.Free.of_equiv eKerV.symm

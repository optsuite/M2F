import Mathlib

open scoped TensorProduct

/-- Let $M$ be an $R$-module. The following are equivalent:

\begin{enumerate}
    \item $M$ is finitely generated.
    \item For every family $(Q_{\alpha})_{\alpha \in A}$ of $R$-modules, the canonical map
    $M \otimes_{R} \left( \prod_{\alpha} Q_{\alpha} \right) \to \prod_{\alpha} (M \otimes_{R}
    Q_{\alpha})$ is surjective.
\end{enumerate} -/
-- The canonical map is the standard `TensorProduct.piRightHom`.
private lemma canonicalMap_eq_piRightHom {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] {α : Type} (Q : α → Type)
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    LinearMap.pi (fun i => LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R)))
      = TensorProduct.piRightHom R R M Q := by
  ext m f i
  simp [TensorProduct.piRightHom_tmul]

-- A convenient pointwise formula for `piRightHom`.
private lemma piRightHom_apply {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] {α : Type} (Q : α → Type)
    [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    (x : M ⊗[R] (∀ i, Q i)) (i : α) :
    (TensorProduct.piRightHom R R M Q x) i
      = LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R)) x := by
  have h := congrArg (fun f => f x i) (canonicalMap_eq_piRightHom (M := M) (Q := Q)).symm
  simpa [LinearMap.pi_apply] using h

-- Linear equivalence `(Fin n → R) ⊗ X ≃ (Fin n → X)`.
noncomputable def freeTensorEquiv {R : Type} [CommRing R] (n : ℕ) (X : Type)
    [AddCommGroup X] [Module R X] :
    (Fin n → R) ⊗[R] X ≃ₗ[R] Fin n → X :=
  (TensorProduct.comm R (Fin n → R) X) ≪≫ₗ
    TensorProduct.piScalarRight R R X (Fin n)

-- Compatibility of `piRightHom` with the `freeTensorEquiv` coordinates.
private lemma freeTensorEquiv_comp_piRightHom {R : Type} [CommRing R]
    {α : Type} (Q : α → Type) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)]
    (n : ℕ) (i : α) :
    (freeTensorEquiv (R := R) n (Q i)).toLinearMap.comp
        ((LinearMap.proj i (φ := fun j => (Fin n → R) ⊗[R] Q j) (R := R)).comp
          (TensorProduct.piRightHom R R (Fin n → R) Q))
      =
        (LinearMap.compLeft (LinearMap.proj i (φ := Q) (R := R)) (Fin n)).comp
          (freeTensorEquiv (R := R) n (∀ j, Q j)).toLinearMap := by
  ext m f
  simp [freeTensorEquiv, TensorProduct.piRightHom_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, TensorProduct.comm_tmul, LinearMap.compLeft_apply]

-- For a finite free module, the canonical map is surjective by explicit coordinates.
private lemma surjective_piRightHom_free {R : Type} [CommRing R] (n : ℕ)
    {α : Type} (Q : α → Type) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R (Fin n → R) Q) := by
  classical
  intro y
  let eQ : (i : α) → ((Fin n → R) ⊗[R] Q i ≃ₗ[R] Fin n → Q i) :=
    fun i => freeTensorEquiv (R := R) n (Q i)
  let eDom : (Fin n → R) ⊗[R] (∀ i, Q i) ≃ₗ[R] Fin n → (∀ i, Q i) :=
    freeTensorEquiv (R := R) n (∀ i, Q i)
  let y' : ∀ i, Fin n → Q i := fun i => eQ i (y i)
  let x' : Fin n → (∀ i, Q i) := fun j i => y' i j
  refine ⟨eDom.symm x', ?_⟩
  funext i
  apply (eQ i).injective
  have hcomp :=
    LinearMap.congr_fun (freeTensorEquiv_comp_piRightHom (R := R) (Q := Q) n i) (eDom.symm x')
  have hcomp' :
      eQ i
          ((TensorProduct.piRightHom R R (Fin n → R) Q) (eDom.symm x') i)
        = fun j => x' j i := by
    simpa [eQ, eDom] using hcomp
  simpa [y', x'] using hcomp'

-- Push surjectivity along a surjective map from a finite free module.
private lemma surjective_piRightHom_of_surjective {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M] {n : ℕ}
    (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)
    {α : Type} (Q : α → Type) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)] :
    Function.Surjective (TensorProduct.piRightHom R R M Q) := by
  classical
  intro y
  have hrt : ∀ i, ∃ x, (LinearMap.rTensor (Q i) f) x = y i := fun i =>
    (LinearMap.rTensor_surjective (Q := Q i) (g := f) hf) (y i)
  classical
  choose y0 hy0 using hrt
  obtain ⟨x0, hx0⟩ := surjective_piRightHom_free (R := R) n Q y0
  refine ⟨LinearMap.rTensor (∀ i, Q i) f x0, ?_⟩
  funext i
  have hcomm :
      LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R))
          (LinearMap.rTensor (∀ i, Q i) f x0)
        =
      LinearMap.rTensor (Q i) f
          (LinearMap.lTensor (Fin n → R) (LinearMap.proj i (φ := Q) (R := R)) x0) := by
    have hmap :
        (LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R))).comp
            (LinearMap.rTensor (∀ i, Q i) f)
          =
        (LinearMap.rTensor (Q i) f).comp
            (LinearMap.lTensor (Fin n → R) (LinearMap.proj i (φ := Q) (R := R))) := by
      calc
        (LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R))).comp
            (LinearMap.rTensor (∀ i, Q i) f)
            = TensorProduct.map f (LinearMap.proj i (φ := Q) (R := R)) := by
              simpa [LinearMap.lTensor, LinearMap.rTensor]
                using (LinearMap.lTensor_comp_rTensor (M := Fin n → R) (P := M)
                  (N := (∀ i, Q i)) (Q := Q i)
                  (f := f) (g := LinearMap.proj i (φ := Q) (R := R)))
        _ =
          (LinearMap.rTensor (Q i) f).comp
            (LinearMap.lTensor (Fin n → R) (LinearMap.proj i (φ := Q) (R := R))) := by
              simpa [LinearMap.lTensor, LinearMap.rTensor] using
                (LinearMap.rTensor_comp_lTensor (M := Fin n → R) (P := M)
                  (N := (∀ i, Q i)) (Q := Q i)
                  (f := f) (g := LinearMap.proj i (φ := Q) (R := R))).symm
    exact LinearMap.congr_fun hmap x0
  calc
    TensorProduct.piRightHom R R M Q (LinearMap.rTensor (∀ i, Q i) f x0) i
        = LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R))
            (LinearMap.rTensor (∀ i, Q i) f x0) :=
          piRightHom_apply (R := R) (M := M) (Q := Q) _ _
    _ = LinearMap.rTensor (Q i) f
            (LinearMap.lTensor (Fin n → R) (LinearMap.proj i (φ := Q) (R := R)) x0) := hcomm
    _ = LinearMap.rTensor (Q i) f (TensorProduct.piRightHom R R (Fin n → R) Q x0 i) := by
          simp [piRightHom_apply (R := R) (M := Fin n → R) (Q := Q)]
    _ = LinearMap.rTensor (Q i) f (y0 i) := by
          have hx0i : (TensorProduct.piRightHom R R (Fin n → R) Q x0) i = y0 i := by
            simpa using congrArg (fun g => g i) hx0
          simp [hx0i]
    _ = y i := hy0 i

-- Use surjectivity for the family `Q := fun _ : M => R` to extract generators.
private lemma finite_of_surjective_family {R : Type} [CommRing R]
    {M : Type} [AddCommGroup M] [Module R M]
    (h : ∀ {α : Type} (Q : α → Type),
      ∀ [(a : α) → AddCommGroup (Q a)] [(a : α) → Module R (Q a)],
        Function.Surjective (LinearMap.pi
          (fun i => LinearMap.lTensor M (LinearMap.proj i (φ := Q) (R := R))))) :
    Module.Finite R M := by
  classical
  have hsurj : Function.Surjective (TensorProduct.piRightHom R R M (fun _ : M => R)) := by
    simpa [canonicalMap_eq_piRightHom (M := M) (Q := fun _ : M => R)] using
      (h (Q := fun _ : M => R))
  let target : M → M ⊗[R] R := fun m => m ⊗ₜ[R] (1 : R)
  obtain ⟨x, hx⟩ := hsurj target
  obtain ⟨S, hS⟩ := TensorProduct.exists_finsupp_left x
  have htop : (⊤ : Submodule R M) ≤ Submodule.span R (↑S.support : Set M) := by
    intro m _
    have hx_m : (TensorProduct.piRightHom R R M (fun _ : M => R) x) m = m ⊗ₜ[R] (1 : R) := by
      simpa [target] using congrArg (fun g => g m) hx
    have hx_m' : (TensorProduct.piRightHom R R M (fun _ : M => R)
        (S.sum fun m' f => (m' : M) ⊗ₜ[R] f)) m = m ⊗ₜ[R] (1 : R) := by
      simpa [hS] using hx_m
    have hx_m'' : m ⊗ₜ[R] (1 : R) =
        (TensorProduct.piRightHom R R M (fun _ : M => R)
          (S.sum fun m' f => (m' : M) ⊗ₜ[R] f)) m := by
      simpa using hx_m'.symm
    have hx_m''' : m ⊗ₜ[R] (1 : R) =
        (TensorProduct.piRightHom R R M (fun _ : M => R)
          (S.support.sum fun m' => (m' : M) ⊗ₜ[R] (S m'))) m := by
      simpa [Finsupp.sum] using hx_m''
    have hsum_support : m ⊗ₜ[R] (1 : R) =
        S.support.sum (fun m' => (m' : M) ⊗ₜ[R] (S m' m)) := by
      simpa [TensorProduct.piRightHom_tmul] using hx_m'''
    have hsum : m ⊗ₜ[R] (1 : R) =
        S.sum (fun m' f => (m' : M) ⊗ₜ[R] f m) := by
      simpa [Finsupp.sum] using hsum_support
    have hsum_m : (m : M) = S.sum (fun m' f => (f m) • m') := by
      have := congrArg (TensorProduct.rid R M) hsum
      simpa [Finsupp.sum, TensorProduct.rid_tmul] using this
    have hmem : S.sum (fun m' f => (f m) • m')
        ∈ Submodule.span R (↑S.support : Set M) := by
      have hmem' : (S.support.sum fun m' => (S m' m) • m')
          ∈ Submodule.span R (↑S.support : Set M) := by
        refine Submodule.sum_mem (p := Submodule.span R (↑S.support : Set M)) ?_
        intro m' hm'
        exact Submodule.smul_mem (Submodule.span R (↑S.support : Set M)) _
          (Submodule.subset_span hm')
      simpa [Finsupp.sum] using hmem'
    exact hsum_m ▸ hmem
  have htop' : (⊤ : Submodule R M) = Submodule.span R (↑S.support : Set M) :=
    le_antisymm htop (by exact le_top)
  have hfg : (⊤ : Submodule R M).FG := by
    have hfg_span : (Submodule.span R (↑S.support : Set M)).FG :=
      Submodule.fg_span (S.support.finite_toSet)
    simpa [htop'] using hfg_span
  exact (Module.finite_def).2 hfg

theorem finite_iff_surjective_linearMap {R : Type} [CommRing R]
    (M : Type) [AddCommGroup M] [Module R M] :
    Module.Finite R M ↔ ∀ {α : Type} (Q : α → Type),
    ∀ [(a : α) → AddCommGroup (Q a)] [(a : α) → Module R (Q a)],
        Function.Surjective (LinearMap.pi (
            fun i => LinearMap.lTensor M (
                LinearMap.proj i (φ := Q) (R := R)))) := by
  constructor
  · intro hM α Q _ _
    classical
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (R := R) (M := M)
    have hsurj := surjective_piRightHom_of_surjective (R := R) (M := M)
      (n := n) f hf (Q := Q)
    simpa [canonicalMap_eq_piRightHom (M := M) (Q := Q)] using hsurj
  · intro h
    exact finite_of_surjective_family (R := R) (M := M) h

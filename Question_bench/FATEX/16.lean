import Mathlib

/--
A Galois extension such that the degree of the extension is a power of a prime \( p \) is
called a p-extension.
-/
class IsPExtension (F E : Type*) [Field F] [Field E] [Algebra F E]
    (p : ℕ) : Prop extends IsGalois F E where
    rank_eq_pow : ∃ (n : ℕ), Module.rank F E = p ^ n

/-- A p-extension is finite-dimensional over the base field. -/
lemma IsPExtension.finiteDimensional (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ)
    [IsPExtension F E p] : FiniteDimensional F E := by
  classical
  obtain ⟨n, hn⟩ := (IsPExtension.rank_eq_pow (F := F) (E := E) (p := p))
  have hn' : Module.rank F E = (p ^ n : ℕ) := by
    simpa [Nat.cast_pow] using hn
  have hrank : Module.rank F E < Cardinal.aleph0 := by
    simpa [hn'] using (Cardinal.nat_lt_aleph0 (p ^ n))
  exact (Module.rank_lt_aleph0_iff (R := F) (M := E)).1 hrank

/-- A p-extension has p-power finrank. -/
lemma IsPExtension.exists_finrank_eq_pow (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ)
    [IsPExtension F E p] : ∃ n, Module.finrank F E = p ^ n := by
  classical
  obtain ⟨n, hn⟩ := (IsPExtension.rank_eq_pow (F := F) (E := E) (p := p))
  have hn' : Module.rank F E = (p ^ n : ℕ) := by
    simpa [Nat.cast_pow] using hn
  refine ⟨n, ?_⟩
  exact Module.finrank_eq_of_rank_eq (R := F) (M := E) (n := p ^ n) hn'

/-- A normal closure of a finite extension is finite-dimensional. -/
lemma finiteDimensional_of_isNormalClosure (F L E : Type) [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] (h : IsNormalClosure F L E) [FiniteDimensional F L] :
    FiniteDimensional F E := by
  classical
  -- Use algebraicity of `L/F` to identify the normal closure with `⊤`.
  have htop : IntermediateField.normalClosure F L E = (⊤ : IntermediateField F E) := by
    have h' := (Algebra.IsAlgebraic.isNormalClosure_iff (F := F) (K := L) (L := E)).1 h
    exact h'.2
  haveI : FiniteDimensional F (IntermediateField.normalClosure F L E) := inferInstance
  -- Transfer finite dimensionality along the top equivalence.
  have e : (IntermediateField.normalClosure F L E) ≃ₐ[F] E := by
    exact (IntermediateField.equivOfEq (F := F) (E := E) htop).trans
      (IntermediateField.topEquiv (F := F) (E := E))
  exact e.toLinearEquiv.finiteDimensional

/-- Adjoining the roots of a separable polynomial yields a separable intermediate field. -/
lemma isSeparable_adjoin_rootSet (F E : Type*) [Field F] [Field E] [Algebra F E]
    (p : Polynomial F)
    (hp : p.Separable) (hs : (p.map (algebraMap F E)).Splits) :
    Algebra.IsSeparable F (IntermediateField.adjoin F (p.rootSet E)) := by
  classical
  haveI : p.IsSplittingField F (IntermediateField.adjoin F (p.rootSet E)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (K := F) (L := E) (p := p) hs
  haveI : IsGalois F (IntermediateField.adjoin F (p.rootSet E)) :=
    IsGalois.of_separable_splitting_field (F := F)
      (E := IntermediateField.adjoin F (p.rootSet E)) (p := p) hp
  infer_instance

/-- A normal closure of a separable extension is Galois. -/
lemma isGalois_of_isNormalClosure_of_isSeparable (F E : Type*) [Field F] [Field E]
    [Algebra F E] (L : IntermediateField F E) (h : IsNormalClosure F L E)
    [Algebra.IsSeparable F L] : IsGalois F E := by
  classical
  letI : IsNormalClosure F L E := h
  haveI :
      ∀ x : L,
        Algebra.IsSeparable F (IntermediateField.adjoin F ((minpoly F x).rootSet E)) :=
    fun x => by
      have hx : (minpoly F x).Separable := by
        simpa [IsSeparable] using (Algebra.IsSeparable.isSeparable (F := F) x)
      simpa using
        (isSeparable_adjoin_rootSet (F := F) (E := E) (p := minpoly F x) hx (h.splits x))
  let S : IntermediateField F E :=
    ⨆ x : L, IntermediateField.adjoin F ((minpoly F x).rootSet E)
  have hsep_S : Algebra.IsSeparable F S := by
    simpa [S] using (inferInstance :
      Algebra.IsSeparable F (⨆ x : L, IntermediateField.adjoin F ((minpoly F x).rootSet E) :
        IntermediateField F E))
  haveI : Algebra.IsSeparable F (⊤ : IntermediateField F E) := by
    haveI : Algebra.IsSeparable F S := hsep_S
    simpa using
      (Algebra.IsSeparable.of_algHom (F := F) (E := (⊤ : IntermediateField F E)) (E' := S)
        (f := (IntermediateField.equivOfEq (F := F) (E := E) h.adjoin_rootSet).symm.toAlgHom))
  have hsepE : Algebra.IsSeparable F E := by
    simpa using
      (Algebra.IsSeparable.of_algHom (F := F) (E := E) (E' := (⊤ : IntermediateField F E))
        (f := (IntermediateField.topEquiv (F := F) (E := E)).symm.toAlgHom))
  have hnormal : Normal F E := by
    simpa using (IsNormalClosure.normal (F := F) (K := L) (L := E))
  exact (isGalois_iff (F := F) (E := E)).2 ⟨hsepE, hnormal⟩

/-- The Galois group of a p-extension is a p-group. -/
lemma isPGroup_gal_of_isPExtension (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ)
    [Fact p.Prime] [FiniteDimensional F E] [IsPExtension F E p] :
    IsPGroup p (Gal(E / F)) := by
  classical
  obtain ⟨n, hn⟩ := IsPExtension.exists_finrank_eq_pow (F := F) (E := E) (p := p)
  have hcard : Nat.card (Gal(E / F)) = p ^ n := by
    calc
      Nat.card (Gal(E / F)) = Module.finrank F E :=
        IsGalois.card_aut_eq_finrank (F := F) (E := E)
      _ = p ^ n := hn
  exact IsPGroup.of_card (p := p) (G := Gal(E / F)) (n := n) hcard

/-- A p-group Galois group forces the degree to be a p-power. -/
lemma rank_eq_pow_of_isPGroup_gal (F E : Type*) [Field F] [Field E] [Algebra F E] (p : ℕ)
    [Fact p.Prime] [FiniteDimensional F E] [IsGalois F E]
    (hG : IsPGroup p (Gal(E / F))) : ∃ n, Module.rank F E = p ^ n := by
  classical
  obtain ⟨n, hcard⟩ := (IsPGroup.exists_card_eq (p := p) (G := Gal(E / F)) hG)
  have hfinrank : Module.finrank F E = p ^ n := by
    calc
      Module.finrank F E = Nat.card (Gal(E / F)) := by
        symm
        exact IsGalois.card_aut_eq_finrank (F := F) (E := E)
      _ = p ^ n := hcard
  have hrank : Module.rank F E = (p : Cardinal) ^ n := by
    have hcast : Module.rank F E = (Module.finrank F E : ℕ) := by
      simpa [Module.finrank_eq_rank] using
        (Module.finrank_eq_rank (R := F) (M := E)).symm
    simpa [hfinrank, Nat.cast_pow] using hcast
  exact ⟨n, hrank⟩

/-- The regular wreath product of p-groups is a p-group. -/
lemma isPGroup_regularWreathProduct_of_isPGroup (p : ℕ) [Fact p.Prime] (D Q : Type*)
    [Group D] [Group Q] [Finite D] [Finite Q] (hD : IsPGroup p D) (hQ : IsPGroup p Q) :
    IsPGroup p (D ≀ᵣ Q) := by
  classical
  refine (IsPGroup.iff_card (p := p) (G := D ≀ᵣ Q)).2 ?_
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := p) (G := D)).1 hD
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p) (G := Q)).1 hQ
  refine ⟨m * p ^ n + n, ?_⟩
  calc
    Nat.card (D ≀ᵣ Q) = Nat.card D ^ Nat.card Q * Nat.card Q := by
      simpa using (RegularWreathProduct.card (D := D) (Q := Q))
    _ = (p ^ m) ^ (p ^ n) * p ^ n := by
      simp [hm, hn]
    _ = p ^ (m * p ^ n) * p ^ n := by
      simp [pow_mul]
    _ = p ^ (m * p ^ n + n) := by
      symm
      simp [pow_add]

/-- If a group surjects onto a p-group and its kernel is a p-group, then it is a p-group. -/
lemma isPGroup_of_surjective_ker (p : ℕ) {G Q : Type*} [Group G] [Group Q]
    (ϕ : G →* Q) (hϕ : Function.Surjective ϕ)
    (hker : IsPGroup p ϕ.ker) (hQ : IsPGroup p Q) : IsPGroup p G := by
  classical
  intro g
  obtain ⟨k, hk⟩ := hQ (ϕ g)
  have hker_mem : g ^ (p ^ k) ∈ ϕ.ker := by
    have : ϕ (g ^ (p ^ k)) = 1 := by
      simpa [map_pow] using hk
    simpa [MonoidHom.mem_ker] using this
  obtain ⟨n, hn⟩ := hker ⟨g ^ (p ^ k), hker_mem⟩
  have hn' : (g ^ (p ^ k)) ^ (p ^ n) = 1 := by
    exact congrArg Subtype.val hn
  have hpow : g ^ (p ^ k * p ^ n) = 1 := by
    simpa [pow_mul] using hn'
  have hpow' : g ^ (p ^ (k + n)) = 1 := by
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hpow
  exact ⟨k + n, hpow'⟩

/-- If an automorphism fixes every element of a set, it fixes the adjoin. -/
lemma fix_adjoin_of_fix_set (F E : Type*) [Field F] [Field E] [Algebra F E]
    (σ : Gal(E/F)) (S : Set E)
    (hS : ∀ x ∈ S, σ x = x) :
    ∀ x ∈ IntermediateField.adjoin F S, σ x = x := by
  intro x hx
  refine (IntermediateField.adjoin_induction (F := F) (E := E) (s := S)
    (p := fun x _ => σ x = x) (mem := ?_) (algebraMap := ?_)
      (add := ?_) (inv := ?_) (mul := ?_) hx)
  · intro x hx
    exact hS x hx
  · intro x
    simpa using (AlgEquiv.commutes σ x)
  · intro x y hx hy hx' hy'
    calc
      σ (x + y) = σ x + σ y := by
        simpa using (map_add (σ : E →ₐ[F] E) x y)
      _ = x + y := by simpa [hx', hy']
  · intro x hx hx'
    calc
      σ x⁻¹ = (σ x)⁻¹ := by
        simpa using (map_inv₀ (σ : E →ₐ[F] E) x)
      _ = x⁻¹ := by simpa [hx']
  · intro x y hx hy hx' hy'
    calc
      σ (x * y) = σ x * σ y := by
        simpa using (map_mul (σ : E →ₐ[F] E) x y)
      _ = x * y := by simpa [hx', hy']

/-- Kernel elements of `AlgEquiv.restrictNormalHom` fix the intermediate field pointwise. -/
lemma ker_restrictNormalHom_fixes
    (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    [Normal F K] [Normal F E]
    (σ : (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker) (k : K) :
    (σ : Gal(E/F)) (algebraMap K E k) = algebraMap K E k := by
  have hσ : (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)) σ = 1 := by
    exact σ.property
  have hσ' : (σ : Gal(E/F)).restrictNormal K = 1 := by
    simpa using hσ
  have hcomm :=
    (AlgEquiv.restrictNormal_commutes (χ := (σ : Gal(E/F))) (E := K) (x := k))
  -- Convert the commutation statement into a pointwise fixedness statement.
  simpa [hσ'] using hcomm.symm

/-- View a kernel element as a `K`-automorphism of `E`. -/
def kerToGalEK (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    [Normal F K] [Normal F E]
    (σ : (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker) : Gal(E/K) :=
  { (σ : Gal(E/F)) with
    commutes' := fun k =>
      ker_restrictNormalHom_fixes (F := F) (E := E) (K := K) σ k }

/-- Coercions of `kerToGalEK` agree with the original automorphism. -/
@[simp]
lemma kerToGalEK_apply (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    [Normal F K] [Normal F E]
    (σ : (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker) (x : E) :
    kerToGalEK (F := F) (E := E) (K := K) σ x = (σ : Gal(E/F)) x := rfl

/-- `kerToGalEK` sends the identity kernel element to `1`. -/
@[simp]
lemma kerToGalEK_one (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    [Normal F K] [Normal F E] :
    kerToGalEK (F := F) (E := E) (K := K)
        (1 : (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker) = 1 := by
  ext x
  rfl

/-- Restriction to `L` over `K` agrees with the original automorphism on elements of `L`. -/
lemma restrictNormalHom_apply_subtype (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (σ : Gal(E / K)) (y : L) :
    ((AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := L) σ) y : E) = σ (y : E) := by
  have h := (AlgEquiv.restrictNormal_commutes (F := K) (χ := σ) (E := L) (x := y))
  change
    algebraMap (↥L) E ((σ.restrictNormal (↥L)) y) = σ (algebraMap (↥L) E y)
  simpa using h

/-- The scalar tower `F → K → E` induced by intermediate fields. -/
instance isScalarTower_intermediateField (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L) : IsScalarTower F K E := by
  classical
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  -- Compare both maps through `L`.
  have hFLE := (IsScalarTower.algebraMap_eq (R := F) (S := L) (A := E))
  have hFLE' := congrArg (fun f => f x) hFLE
  have h : algebraMap K E (algebraMap F K x) = algebraMap L E (algebraMap F L x) := by
    rfl
  simpa [h] using hFLE'

/-- The scalar tower `K → L → E` induced by intermediate fields. -/
instance isScalarTower_intermediateField' (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L) : IsScalarTower K L E := by
  refine IsScalarTower.of_algebraMap_eq ?_
  intro x
  rfl

/-- Conjugating a kernel element by a section element stays in the kernel. -/
lemma ker_conj_mem (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    (π : Gal(E/F) →* Gal(K/F)) (s : Gal(K/F) → Gal(E/F)) (hs : ∀ q, π (s q) = q)
    (σ : π.ker) (q : Gal(K/F)) :
    π ((s q)⁻¹ * (σ : Gal(E/F)) * (s q)) = 1 := by
  have hσ : π (σ : Gal(E/F)) = 1 := σ.property
  calc
    π ((s q)⁻¹ * (σ : Gal(E/F)) * (s q)) =
        π (s q)⁻¹ * π (σ : Gal(E/F)) * π (s q) := by
          simp [map_mul, map_inv]
    _ = 1 := by
      simp [hs q, hσ]

/-- Conjugate a kernel element by a section element, as a kernel element. -/
def ker_conj (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    (π : Gal(E/F) →* Gal(K/F)) (s : Gal(K/F) → Gal(E/F)) (hs : ∀ q, π (s q) = q)
    (σ : π.ker) (q : Gal(K/F)) : π.ker :=
  ⟨(s q)⁻¹ * (σ : Gal(E/F)) * (s q),
    ker_conj_mem (F := F) (E := E) (K := K) (π := π) (s := s) (hs := hs) σ q⟩

/-- The map `kerToGalEK` respects multiplication. -/
lemma kerToGalEK_mul (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    [Normal F K] [Normal F E]
    (σ τ : (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker) :
    kerToGalEK (F := F) (E := E) (K := K) (σ * τ) =
      kerToGalEK (F := F) (E := E) (K := K) σ *
      kerToGalEK (F := F) (E := E) (K := K) τ := by
  ext x
  simp [kerToGalEK, AlgEquiv.mul_apply]

/-- Conjugation by a section element is multiplicative. -/
lemma ker_conj_mul (F E K : Type*) [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra F K] [Algebra K E] [IsScalarTower F K E]
    (π : Gal(E/F) →* Gal(K/F)) (s : Gal(K/F) → Gal(E/F)) (hs : ∀ q, π (s q) = q)
    (σ τ : π.ker) (q : Gal(K/F)) :
    ker_conj (F := F) (E := E) (K := K) (π := π) (s := s) (hs := hs) (σ * τ) q =
      ker_conj (F := F) (E := E) (K := K) (π := π) (s := s) (hs := hs) σ q *
      ker_conj (F := F) (E := E) (K := K) (π := π) (s := s) (hs := hs) τ q := by
  apply Subtype.ext
  ext x
  simp [ker_conj, AlgEquiv.mul_apply, mul_assoc]

/-- Kernel elements of the restriction map stabilize the intermediate field `L`. -/
lemma ker_maps_L (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (σ : (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
      Gal(E/F) →* Gal(K/F)).ker) :
    L.map ((σ : Gal(E/F)) : E →ₐ[F] E) = L := by
  classical
  let σK : Gal(E/K) := kerToGalEK (F := F) (E := E) (K := K) σ
  let σL : Gal(L/K) :=
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := L)) σK
  have hres : ∀ y : L, (σ : Gal(E/F)) (y : E) = (σL y : E) := by
    intro y
    have h :=
      restrictNormalHom_apply_subtype (F := F) (E := E) (L := L) (K := K) (σ := σK) (y := y)
    have h' : (σL y : E) = σK (y : E) := by
      simpa [σL] using h
    simpa [kerToGalEK_apply] using h'.symm
  refine le_antisymm ?_ ?_
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hxy : (σ : Gal(E/F)) (y : E) = (σL ⟨y, hy⟩ : E) := by
      simpa using (hres ⟨y, hy⟩)
    simpa [hxy] using (σL ⟨y, hy⟩).property
  · intro x hx
    let y : L := σL.symm ⟨x, hx⟩
    refine ⟨y, y.property, ?_⟩
    have hxy : (σ : Gal(E/F)) (y : E) = (σL y : E) := hres y
    have hxy' : (σL y : E) = x := by
      simpa [y] using congrArg Subtype.val (AlgEquiv.apply_symm_apply σL ⟨x, hx⟩)
    simpa [hxy, hxy'] 

/-- A section of the restriction map does not change the image of `L`. -/
lemma map_eq_map_section_of_restrict (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q)
    (σ : Gal(E/F)) :
    L.map ((σ : Gal(E/F)) : E →ₐ[F] E) =
      L.map ((s ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) σ) :
        Gal(E/F)) : E →ₐ[F] E) := by
  classical
  let π : Gal(E/F) →* Gal(K/F) :=
    AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)
  have hτ :
      π ((s (π σ))⁻¹ * σ) = 1 := by
    have hs' : π (s (π σ)) = π σ := hs (π σ)
    calc
      π ((s (π σ))⁻¹ * σ) = π (s (π σ))⁻¹ * π σ := by
        simp [map_mul, map_inv]
      _ = (π σ)⁻¹ * π σ := by
        simpa [hs']
      _ = 1 := by simp
  let τ : π.ker := ⟨(s (π σ))⁻¹ * σ, hτ⟩
  have hσ : (s (π σ)) * (τ : Gal(E/F)) = σ := by
    -- simplify using the definition of τ
    ext x
    simp [τ, AlgEquiv.mul_apply, mul_assoc]
  have hcomp :
      ((s (π σ) * (τ : Gal(E/F)) : Gal(E/F)) : E →ₐ[F] E) =
        (s (π σ) : E →ₐ[F] E).comp (τ : E →ₐ[F] E) := by
    ext x
    simp [AlgEquiv.mul_apply]
  calc
    L.map ((σ : Gal(E/F)) : E →ₐ[F] E) =
        L.map ((s (π σ) * (τ : Gal(E/F)) : Gal(E/F)) : E →ₐ[F] E) := by
          simpa [hσ]
    _ = (L.map (τ : E →ₐ[F] E)).map (s (π σ) : E →ₐ[F] E) := by
          simpa [hcomp] using
            (IntermediateField.map_map (E := L) (f := (τ : E →ₐ[F] E))
              (g := (s (π σ) : E →ₐ[F] E))).symm
    _ = L.map (s (π σ) : E →ₐ[F] E) := by
          simp [ker_maps_L (F := F) (E := E) (L := L) (K := K) τ]

/-- The section images of `L` generate the normal closure. -/
lemma iSup_map_section_eq_top (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L] [FiniteDimensional F L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q)
    (hπ : Function.Surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)))
    (h_normalClosure : IsNormalClosure F L E) :
    (⨆ q : Gal(K/F), L.map ((s q : Gal(E/F)) : E →ₐ[F] E)) = ⊤ := by
  classical
  have htop : IntermediateField.normalClosure F L E = (⊤ : IntermediateField F E) := by
    have h' :=
      (Algebra.IsAlgebraic.isNormalClosure_iff (F := F) (K := L) (L := E)).1 h_normalClosure
    exact h'.2
  have htop' :
      (⨆ σ : Gal(E/F), L.map ((σ : Gal(E/F)) : E →ₐ[F] E)) = ⊤ := by
    simpa [IntermediateField.normalClosure_def''] using htop
  have hmap :
      ∀ σ : Gal(E/F),
        L.map ((σ : Gal(E/F)) : E →ₐ[F] E) =
          L.map ((s ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) σ) :
            Gal(E/F)) : E →ₐ[F] E) :=
    map_eq_map_section_of_restrict (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
  have hmap' :
      (fun σ : Gal(E/F) => L.map ((σ : Gal(E/F)) : E →ₐ[F] E)) =
        fun σ : Gal(E/F) =>
          L.map ((s ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) σ) :
            Gal(E/F)) : E →ₐ[F] E) := by
    funext σ
    exact hmap σ
  have htop'' :
      (⨆ σ : Gal(E/F),
          L.map ((s ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) σ) :
            Gal(E/F)) : E →ₐ[F] E)) = ⊤ := by
    simpa [hmap'] using htop'
  have hsup :
      (⨆ q : Gal(K/F), L.map ((s q : Gal(E/F)) : E →ₐ[F] E)) =
        ⨆ σ : Gal(E/F),
          L.map ((s ((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) σ) :
            Gal(E/F)) : E →ₐ[F] E) := by
    simpa using
      (Function.Surjective.iSup_comp hπ
        (g := fun q : Gal(K/F) => L.map ((s q : Gal(E/F)) : E →ₐ[F] E))).symm
  simpa [hsup] using htop''

/-- The wreath-product map from the kernel, using a section of the restriction map. -/
noncomputable def kerToRegularWreath_of_section (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q) :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
      Gal(E/F) →* Gal(K/F)).ker → (Gal(L / K) ≀ᵣ Gal(K / F)) :=
  fun σ =>
    ⟨fun q =>
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := L))
          (kerToGalEK (F := F) (E := E) (K := K)
            (ker_conj (F := F) (E := E) (K := K)
              (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
              (s := s) (hs := hs) σ q)),
      1⟩

/-- The wreath-product map sends `1` to `1`. -/
lemma kerToRegularWreath_of_section_map_one (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q) :
    kerToRegularWreath_of_section (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs) 1 =
      (1 : Gal(L / K) ≀ᵣ Gal(K / F)) := by
  classical
  ext q
  · have hconj :
        ker_conj (F := F) (E := E) (K := K)
            (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
            (s := s) (hs := hs) (1 :
              (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
                Gal(E/F) →* Gal(K/F)).ker) q = 1 := by
      apply Subtype.ext
      simp [ker_conj, mul_assoc]
    -- Evaluate on `x : L` using restriction.
    simp [kerToRegularWreath_of_section, hconj]
  · simp [kerToRegularWreath_of_section]

/-- The wreath-product map preserves multiplication. -/
lemma kerToRegularWreath_of_section_map_mul (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q)
    (σ τ :
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
        Gal(E/F) →* Gal(K/F)).ker) :
    kerToRegularWreath_of_section (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
        (σ * τ) =
      kerToRegularWreath_of_section (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
        σ *
      kerToRegularWreath_of_section (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
        τ := by
  classical
  ext q
  · -- left component
    have hconj :
        ker_conj (F := F) (E := E) (K := K)
          (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
          (s := s) (hs := hs) (σ * τ) q =
          ker_conj (F := F) (E := E) (K := K)
            (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
            (s := s) (hs := hs) σ q *
          ker_conj (F := F) (E := E) (K := K)
            (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
            (s := s) (hs := hs) τ q := by
      simpa using
        (ker_conj_mul (F := F) (E := E) (K := K)
          (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
          (s := s) (hs := hs) σ τ q)
    have hker :
        kerToGalEK (F := F) (E := E) (K := K)
            (ker_conj (F := F) (E := E) (K := K)
              (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
              (s := s) (hs := hs) (σ * τ) q) =
          kerToGalEK (F := F) (E := E) (K := K)
              (ker_conj (F := F) (E := E) (K := K)
                (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
                (s := s) (hs := hs) σ q) *
          kerToGalEK (F := F) (E := E) (K := K)
              (ker_conj (F := F) (E := E) (K := K)
                (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
                (s := s) (hs := hs) τ q) := by
      simpa [hconj] using
        (kerToGalEK_mul (F := F) (E := E) (K := K)
          (ker_conj (F := F) (E := E) (K := K)
            (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
            (s := s) (hs := hs) σ q)
          (ker_conj (F := F) (E := E) (K := K)
            (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
            (s := s) (hs := hs) τ q))
    simp [kerToRegularWreath_of_section, hker]
  · -- right component
    simp [kerToRegularWreath_of_section]

/-- Package the wreath-product map as a monoid hom. -/
noncomputable def kerToRegularWreath_of_sectionHom (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q) :
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
      Gal(E/F) →* Gal(K/F)).ker →* (Gal(L / K) ≀ᵣ Gal(K / F)) :=
  { toFun :=
      kerToRegularWreath_of_section (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
    map_one' := kerToRegularWreath_of_section_map_one (F := F) (E := E) (L := L) (K := K)
      (s := s) (hs := hs)
    map_mul' := kerToRegularWreath_of_section_map_mul (F := F) (E := E) (L := L) (K := K)
      (s := s) (hs := hs) }

set_option maxHeartbeats 2000000 in
/-- If the wreath-product map sends a kernel element to `1`, the element is trivial. -/
lemma kerToRegularWreath_of_section_eq_one (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L] [FiniteDimensional F L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q)
    (hπ : Function.Surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)))
    (h_normalClosure : IsNormalClosure F L E)
    (σ :
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
        Gal(E/F) →* Gal(K/F)).ker)
    (hσ :
      kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
        σ = 1) :
    σ = 1 := by
  classical
  have hleft :
      ∀ q : Gal(K/F),
        (kerToRegularWreath_of_section (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)
          σ).left q = 1 := by
    intro q
    have := congrArg (fun t : Gal(L / K) ≀ᵣ Gal(K / F) => t.left q) hσ
    simpa [kerToRegularWreath_of_sectionHom, kerToRegularWreath_of_section] using this
  have hfixL :
      ∀ q (y : L),
        ((ker_conj (F := F) (E := E) (K := K)
          (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
          (s := s) (hs := hs) σ q : _ ) : Gal(E/F)) y = y := by
    intro q y
    have hq := hleft q
    -- Extract fixedness from the restriction to `L`.
    have hq' :
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := L))
          (kerToGalEK (F := F) (E := E) (K := K)
            (ker_conj (F := F) (E := E) (K := K)
              (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
              (s := s) (hs := hs) σ q)) = 1 := by
      simpa [kerToRegularWreath_of_section] using hq
    -- Use `restrictNormalHom_apply` to evaluate on `y`.
    have hq'' :
        (kerToGalEK (F := F) (E := E) (K := K)
          (ker_conj (F := F) (E := E) (K := K)
            (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
            (s := s) (hs := hs) σ q)) y = y := by
      have hq''L := congrArg (fun t : Gal(L / K) => t y) hq'
      have hq''L' : ((AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := L))
          (kerToGalEK (F := F) (E := E) (K := K)
            (ker_conj (F := F) (E := E) (K := K)
              (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
              (s := s) (hs := hs) σ q)) y : E) = y := by
        simpa using congrArg Subtype.val hq''L
      have h_apply :=
        restrictNormalHom_apply_subtype (F := F) (E := E) (L := L) (K := K)
          (σ := kerToGalEK (F := F) (E := E) (K := K)
            (ker_conj (F := F) (E := E) (K := K)
              (π := AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K))
              (s := s) (hs := hs) σ q))
          (y := y)
      simpa [h_apply] using hq''L'
    simpa [kerToGalEK_apply] using hq''
  have hfix_map :
      ∀ q (x : E), x ∈ L.map ((s q : Gal(E/F)) : E →ₐ[F] E) →
        (σ : Gal(E/F)) x = x := by
    intro q x hx
    rcases hx with ⟨y, hy, rfl⟩
    -- use the conjugation identity
    have hτ : ((s q)⁻¹ * (σ : Gal(E/F)) * (s q)) (y : E) = y := by
      simpa [ker_conj] using hfixL q ⟨y, hy⟩
    have hτ' : (s q)⁻¹ ((σ : Gal(E/F)) ((s q) y)) = y := by
      simpa [AlgEquiv.mul_apply] using hτ
    have := congrArg (fun z => (s q : Gal(E/F)) z) hτ'
    simpa using this
  have hgen :
      (⨆ q : Gal(K/F), L.map ((s q : Gal(E/F)) : E →ₐ[F] E)) = ⊤ :=
    iSup_map_section_eq_top (F := F) (E := E) (L := L) (K := K)
      (s := s) (hs := hs) (hπ := hπ) h_normalClosure
  -- Use adjoin induction to show `σ` fixes all of `E`.
  have hfix_all : ∀ x : E, (σ : Gal(E/F)) x = x := by
    intro x
    let S : Set E :=
      ⋃ q : Gal(K/F), (L.map ((s q : Gal(E/F)) : E →ₐ[F] E) : Set E)
    have hx : x ∈ IntermediateField.adjoin F S := by
      -- rewrite using `iSup_eq_adjoin`
      have hx' :
          x ∈ (⨆ q : Gal(K/F), L.map ((s q : Gal(E/F)) : E →ₐ[F] E)) := by
        simpa [hgen] using (by
          show x ∈ (⊤ : IntermediateField F E)
          simp)
      -- convert the iSup to an adjoin
      simpa [IntermediateField.iSup_eq_adjoin, S] using hx'
    have hS : ∀ x ∈ S, (σ : Gal(E/F)) x = x := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
      exact hfix_map q x hxq
    exact fix_adjoin_of_fix_set (F := F) (E := E) (σ := (σ : Gal(E/F))) (S := S) hS x hx
  -- conclude `σ = 1`
  apply Subtype.ext
  ext x
  exact hfix_all x

/-- The wreath-product map is injective. -/
lemma kerToRegularWreath_of_section_injective (F E : Type*) [Field F] [Field E] [Algebra F E]
    (L : IntermediateField F E) (K : IntermediateField F L)
    [Normal F K] [Normal F E] [Normal K L] [FiniteDimensional F L]
    (s : Gal(K/F) → Gal(E/F))
    (hs : ∀ q, (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)) (s q) = q)
    (hπ : Function.Surjective (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)))
    (h_normalClosure : IsNormalClosure F L E) :
    Function.Injective
      (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K) (s := s) (hs := hs)) := by
  intro σ τ hστ
  have hσ :
      (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
        (s := s) (hs := hs)) (σ * τ⁻¹) = 1 := by
    calc
      (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
        (s := s) (hs := hs)) (σ * τ⁻¹) =
          (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
            (s := s) (hs := hs)) σ *
          (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
            (s := s) (hs := hs)) τ⁻¹ := by
            simp
      _ = (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
            (s := s) (hs := hs)) τ *
          (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
            (s := s) (hs := hs)) τ⁻¹ := by
            simpa [hστ]
      _ = 1 := by
            simp
  have hσ' :
      σ * τ⁻¹ = (1 :
        (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
          Gal(E/F) →* Gal(K/F)).ker) := by
    exact
      kerToRegularWreath_of_section_eq_one (F := F) (E := E) (L := L) (K := K)
        (s := s) (hs := hs) (hπ := hπ) h_normalClosure (σ := σ * τ⁻¹) hσ
  -- finish
  have hσ'' : σ = τ := by
    -- rearrange in the group
    have := congrArg (fun g =>
      g * (τ : (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K) :
        Gal(E/F) →* Gal(K/F)).ker)) hσ'
    -- simplify the right-multiplication
    simpa [mul_assoc] using this
  exact hσ''

set_option synthInstance.maxHeartbeats 40000 in
/--
Let $p$ be a prime and let $F$ be a field.
Let $K$ be a finite Galois extension of $F$ whose Galois group is a $p$-group (i.e., the degree
$[K : F]$ is a power of $p$). Such an extension is called a \emph{$p$-extension} (note that
$p$-extensions are Galois by definition). Let $L$ be a $p$-extension of $K$. Prove that the
Galois closure of $L$ over $F$ is a $p$-extension of $F$.
-/
theorem normalClosure_isPExtension_of_isPExtension (F E : Type) [Field F] [Field E]
    [Algebra F E] (L : IntermediateField F E) (K : IntermediateField F L) (p : ℕ) (hp : p.Prime)
    [IsPExtension F K p] [IsGalois K L] [IsPExtension K L p]
    (h_normalClosure : IsNormalClosure F L E) : IsPExtension F E p := by
  classical
  -- Ensure a scalar tower structure for the intermediate fields.
  haveI : IsScalarTower F K L := by
    simpa using (IntermediateField.isScalarTower_mid' (K := F) (S := K) (L := L))
  -- Finite dimensionality in the tower F ⟶ K ⟶ L.
  haveI : FiniteDimensional F K :=
    IsPExtension.finiteDimensional (F := F) (E := K) (p := p)
  haveI : FiniteDimensional K L :=
    IsPExtension.finiteDimensional (F := K) (E := L) (p := p)
  haveI : FiniteDimensional F L := FiniteDimensional.trans F K L
  -- Finite dimensionality of the normal closure.
  haveI : FiniteDimensional F E := finiteDimensional_of_isNormalClosure F L E h_normalClosure
  -- Separability in the tower.
  haveI : Algebra.IsSeparable F K := (inferInstance : Algebra.IsSeparable F K)
  haveI : Algebra.IsSeparable K L := (inferInstance : Algebra.IsSeparable K L)
  haveI : Algebra.IsSeparable F L := Algebra.IsSeparable.trans (F := F) (E := K) (K := L)
  -- Build the p-extension structure; p-power rank remains.
  refine { toIsGalois := ?_, rank_eq_pow := ?_ }
  · exact isGalois_of_isNormalClosure_of_isSeparable (F := F) (E := E) (L := L) h_normalClosure
  ·
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : IsGalois F E :=
      isGalois_of_isNormalClosure_of_isSeparable (F := F) (E := E) (L := L) h_normalClosure
    have hG : IsPGroup p (Gal(E / F)) := by
      have hK : IsPGroup p (Gal(K / F)) :=
        isPGroup_gal_of_isPExtension (F := F) (E := K) (p := p)
      have hL : IsPGroup p (Gal(L / K)) :=
        isPGroup_gal_of_isPExtension (F := K) (E := L) (p := p)
      have hW : IsPGroup p (Gal(L / K) ≀ᵣ Gal(K / F)) :=
        isPGroup_regularWreathProduct_of_isPGroup (p := p)
          (D := Gal(L / K)) (Q := Gal(K / F)) hL hK
      -- Use the restriction map `Gal(E/F) → Gal(K/F)` and a kernel–quotient argument.
      let π : Gal(E / F) →* Gal(K / F) :=
        AlgEquiv.restrictNormalHom (F := F) (K₁ := E) (E := K)
      have hπ : Function.Surjective π :=
        AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K) (E := E)
      have hker : IsPGroup p π.ker := by
        classical
        -- Choose a section of the restriction map.
        let s : Gal(K/F) → Gal(E/F) := fun q => Classical.choose (hπ q)
        have hs : ∀ q, π (s q) = q := fun q => Classical.choose_spec (hπ q)
        have hinj :
            Function.Injective
              (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
                (s := s) (hs := hs)) :=
          kerToRegularWreath_of_section_injective (F := F) (E := E) (L := L) (K := K)
            (s := s) (hs := hs) (hπ := hπ) h_normalClosure
        exact hW.of_injective
          (kerToRegularWreath_of_sectionHom (F := F) (E := E) (L := L) (K := K)
            (s := s) (hs := hs)) hinj
      exact isPGroup_of_surjective_ker (p := p) (ϕ := π) hπ hker hK
    exact rank_eq_pow_of_isPGroup_gal (F := F) (E := E) (p := p) hG

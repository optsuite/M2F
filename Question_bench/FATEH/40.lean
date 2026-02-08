import Mathlib
import Question_bench.FATEH.«33»

open Polynomial

/- Let $K$ be the splitting field of a irreducible quintic polynomial $f(x) \in \mathbb{Q} [x]$
and let $\{\alpha_1, \dots, \alpha_5\}$ be zeros of $f(x)$ in $K$. Show that if $\mathbb{Q}
(\alpha_1, \alpha_2, \alpha_3) \neq K$, then $\\mathrm{Gal}(K/\mathbb{Q}) \cong S_5$.-/

/-!
### Auxiliary lemmas

We transport the hypotheses from an arbitrary splitting field to the canonical splitting field
`SplittingField f`, and then use the permutation representation of `f.Gal` on the set of roots.
-/

-- Transport three roots from an arbitrary splitting field to `SplittingField f`.
private lemma transport_three_roots {f : ℚ[X]} {K : Type*} [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K f] (hf1 : Irreducible f) (a₁ a₂ a₃ : K)
    (ha1 : a₁ ∈ rootSet f K ∧ a₂ ∈ rootSet f K ∧ a₃ ∈ rootSet f K)
    (ha2 : a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₃ ≠ a₁)
    (h : IntermediateField.adjoin ℚ {a₁, a₂, a₃} ≠ ⊤) :
    ∃ b₁ b₂ b₃ : SplittingField f,
      b₁ ∈ rootSet f (SplittingField f) ∧ b₂ ∈ rootSet f (SplittingField f) ∧
      b₃ ∈ rootSet f (SplittingField f) ∧
      (b₁ ≠ b₂ ∧ b₂ ≠ b₃ ∧ b₃ ≠ b₁) ∧
      IntermediateField.adjoin ℚ {b₁, b₂, b₃} ≠ (⊤ : IntermediateField ℚ (SplittingField f)) := by
  classical
  let e : K ≃ₐ[ℚ] SplittingField f :=
    Polynomial.IsSplittingField.algEquiv (K := ℚ) (L := K) f
  refine ⟨e a₁, e a₂, e a₃, ?_, ?_, ?_, ?_, ?_⟩
  · -- `e a₁` is still a root.
    have ha : aeval a₁ f = 0 :=
      (Polynomial.mem_rootSet_of_ne (p := f) (S := K) (hp := hf1.ne_zero)).1 ha1.1
    have hb : aeval (e a₁) f = 0 := by
      have hfun := congrArg (fun φ => φ f) (Polynomial.aeval_algEquiv e a₁)
      simpa [AlgHom.comp_apply, ha] using hfun
    exact (Polynomial.mem_rootSet_of_ne (p := f) (S := SplittingField f) (hp := hf1.ne_zero)).2 hb
  · have ha : aeval a₂ f = 0 :=
      (Polynomial.mem_rootSet_of_ne (p := f) (S := K) (hp := hf1.ne_zero)).1 ha1.2.1
    have hb : aeval (e a₂) f = 0 := by
      have hfun := congrArg (fun φ => φ f) (Polynomial.aeval_algEquiv e a₂)
      simpa [AlgHom.comp_apply, ha] using hfun
    exact (Polynomial.mem_rootSet_of_ne (p := f) (S := SplittingField f) (hp := hf1.ne_zero)).2 hb
  · have ha : aeval a₃ f = 0 :=
      (Polynomial.mem_rootSet_of_ne (p := f) (S := K) (hp := hf1.ne_zero)).1 ha1.2.2
    have hb : aeval (e a₃) f = 0 := by
      have hfun := congrArg (fun φ => φ f) (Polynomial.aeval_algEquiv e a₃)
      simpa [AlgHom.comp_apply, ha] using hfun
    exact (Polynomial.mem_rootSet_of_ne (p := f) (S := SplittingField f) (hp := hf1.ne_zero)).2 hb
  · -- Distinctness is preserved by `e`.
    refine ⟨?_, ?_, ?_⟩
    · exact fun h12 => ha2.1 (e.injective h12)
    · exact fun h23 => ha2.2.1 (e.injective h23)
    · exact fun h31 => ha2.2.2 (e.injective h31)
  · -- Properness of the intermediate field is preserved by `e`.
    intro htop
    have himage :
        (⇑(e.toAlgHom) '' ({a₁, a₂, a₃} : Set K)) =
          ({e a₁, e a₂, e a₃} : Set (SplittingField f)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        rcases hx with hx | hx | hx
        · refine ⟨a₁, ?_, ?_⟩
          · simp
          · simpa using hx.symm
        · refine ⟨a₂, ?_, ?_⟩
          · simp
          · simpa using hx.symm
        · refine ⟨a₃, ?_, ?_⟩
          · simp
          · simpa using hx.symm
    have hmapTop :
        IntermediateField.map e.toAlgHom (IntermediateField.adjoin ℚ ({a₁, a₂, a₃} : Set K)) =
          (⊤ : IntermediateField ℚ (SplittingField f)) := by
      rw [IntermediateField.adjoin_map (F := ℚ) (S := ({a₁, a₂, a₃} : Set K)) e.toAlgHom]
      rw [himage]
      exact htop
    have hadjoinTop : IntermediateField.adjoin ℚ ({a₁, a₂, a₃} : Set K) = (⊤ : IntermediateField ℚ K) := by
      have := congrArg (IntermediateField.comap e.toAlgHom) hmapTop
      simpa [IntermediateField.comap_map] using this
    exact h hadjoinTop

-- If a Galois automorphism fixes all roots, then it is the identity.
private lemma gal_eq_one_of_forall_mem_rootSet {f : ℚ[X]} (g : f.Gal)
    (hg : ∀ x : SplittingField f, x ∈ rootSet f (SplittingField f) → g x = x) :
    g = 1 := by
  classical
  have hfix :
      ∀ x : SplittingField f,
        x ∈ Algebra.adjoin ℚ (rootSet f (SplittingField f)) → g x = x := by
    intro x hx
    refine
      Algebra.adjoin_induction (R := ℚ) (A := SplittingField f) (s := rootSet f (SplittingField f))
        (p := fun x _ => g x = x) (mem := ?_) (algebraMap := ?_) (add := ?_) (mul := ?_) hx
    · intro x hx
      exact hg x hx
    · intro r
      simp
    · intro x y _ _ hx hy
      simp [map_add, hx, hy]
    · intro x y _ _ hx hy
      simp [map_mul, hx, hy]
  have hadjoin : Algebra.adjoin ℚ (rootSet f (SplittingField f)) = (⊤ : Subalgebra ℚ (SplittingField f)) := by
    simpa using (SplittingField.adjoin_rootSet (f := f))
  ext x
  have hx : x ∈ Algebra.adjoin ℚ (rootSet f (SplittingField f)) := by
    simp [hadjoin]
  exact hfix x hx

-- A nontrivial permutation of a 5-element type fixing 3 distinct points is a swap.
private lemma perm_isSwap_of_three_fixed {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 5) {τ : Equiv.Perm α}
    {x y z : α} (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hx : τ x = x) (hy : τ y = y) (hz : τ z = z) (hne : τ ≠ 1) :
    τ.IsSwap := by
  classical
  let fixed : Finset α := {x, y, z}
  have hsubset : fixed ⊆ Finset.univ \ τ.support := by
    intro t ht
    have ht' : t = x ∨ t = y ∨ t = z := by
      simpa [fixed, Finset.mem_insert, Finset.mem_singleton] using ht
    refine Finset.mem_sdiff.2 ⟨Finset.mem_univ t, ?_⟩
    have hfix : τ t = t := by
      rcases ht' with rfl | rfl | rfl <;> assumption
    simp [Equiv.Perm.mem_support, hfix]
  have hcard_fixed : fixed.card = 3 := by
    have hxz : x ≠ z := by simpa [ne_comm] using hzx
    have hy_notMem : y ∉ ({z} : Finset α) := by simp [hyz]
    have hcard_yz : (insert y ({z} : Finset α)).card = 2 := by
      simp [Finset.card_insert_of_notMem, hy_notMem]
    have hx_notMem : x ∉ (insert y ({z} : Finset α)) := by
      simp [hxy, hxz]
    have hcard_xyz : (insert x (insert y ({z} : Finset α))).card = 3 := by
      calc
        (insert x (insert y ({z} : Finset α))).card
            = (insert y ({z} : Finset α)).card + 1 :=
              Finset.card_insert_of_notMem hx_notMem
        _ = 3 := by simp [hcard_yz]
    simpa [fixed] using hcard_xyz
  have hle_fixed : fixed.card ≤ (Finset.univ \ τ.support).card :=
    Finset.card_le_card hsubset
  have hcard_diff : (Finset.univ \ τ.support).card = Fintype.card α - τ.support.card := by
    simpa using (Finset.card_univ_diff τ.support)
  have hle' : 3 ≤ Fintype.card α - τ.support.card := by
    have : fixed.card ≤ Fintype.card α - τ.support.card := by
      simpa [hcard_diff] using hle_fixed
    simpa [hcard_fixed] using this
  have hle_support : τ.support.card ≤ Fintype.card α := by
    simpa using (Finset.card_le_univ τ.support)
  have hsum : 3 + τ.support.card ≤ Fintype.card α :=
    (Nat.le_sub_iff_add_le hle_support).1 hle'
  have hsupport_le : τ.support.card ≤ 2 := by
    have h5 : (5 : Nat) = 3 + 2 := by decide
    have hsum' : 3 + τ.support.card ≤ 3 + 2 := by
      simpa [hcard, h5] using hsum
    exact Nat.le_of_add_le_add_left hsum'
  have hsupport_ge : 2 ≤ τ.support.card :=
    Equiv.Perm.two_le_card_support_of_ne_one hne
  have hsupport_eq : τ.support.card = 2 :=
    le_antisymm hsupport_le hsupport_ge
  exact (Equiv.Perm.card_support_eq_two).1 hsupport_eq

theorem nonempty_gal_mulEquiv_perm_fin_five {f : ℚ[X]} {K : Type} [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K f] (hf1 : Irreducible f) (hf2 : f.natDegree = 5) (a₁ a₂ a₃ : K)
    (ha1 : a₁ ∈ rootSet f K ∧ a₂ ∈ rootSet f K ∧ a₃ ∈ rootSet f K)
    (ha2 : a₁ ≠ a₂ ∧ a₂ ≠ a₃ ∧ a₃ ≠ a₁)
    (h : IntermediateField.adjoin ℚ {a₁, a₂, a₃} ≠ ⊤) :
    Nonempty (f.Gal ≃* (Equiv.Perm <| Fin 5)) := by
  classical
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hbne, hbtop⟩ :=
    transport_three_roots (f := f) (K := K) hf1 a₁ a₂ a₃ ha1 ha2 h
  let α : Type := rootSet f (SplittingField f)
  -- The root set in the splitting field has cardinality 5.
  have hfdeg : f.degree = 5 :=
    (degree_eq_iff_natDegree_eq (p := f) (n := 5) hf1.ne_zero).2 hf2
  have hcardα : Fintype.card α = 5 := by
    simpa [α, hfdeg] using (card_rootSet_eq_n (f := f) (n := 5) (hf := hfdeg) (hf' := hf1))
  -- The permutation representation on the root set.
  let ρ : f.Gal →* Equiv.Perm α := MulAction.toPermHom f.Gal α
  let H : Subgroup (Equiv.Perm α) := ρ.range

  -- Kernel triviality: if `ρ g = 1`, then `g = 1`.
  have hker : ∀ g : f.Gal, ρ g = 1 → g = 1 := by
    intro g hg
    have hg' : ∀ x : SplittingField f, x ∈ rootSet f (SplittingField f) → g x = x := by
      intro x hx
      have hx' : (⟨x, hx⟩ : α) = (⟨x, hx⟩ : α) := rfl
      have happly : (ρ g) (⟨x, hx⟩ : α) = (1 : Equiv.Perm α) (⟨x, hx⟩ : α) := by
        simp [hg]
      -- Unpack `ρ` as the action on the root set.
      have : g • (⟨x, hx⟩ : α) = (⟨x, hx⟩ : α) := by
        simpa [ρ, MulAction.toPermHom_apply] using happly
      exact congrArg Subtype.val this
    exact gal_eq_one_of_forall_mem_rootSet (f := f) g hg'
  have hρ_inj : Function.Injective ρ := by
    intro g₁ g₂ hEq
    have hEq' : ρ (g₂⁻¹ * g₁) = 1 := by
      calc
        ρ (g₂⁻¹ * g₁) = ρ g₂⁻¹ * ρ g₁ := by simp [map_mul]
        _ = (ρ g₂)⁻¹ * ρ g₁ := by simp
        _ = (ρ g₁)⁻¹ * ρ g₁ := by simp [hEq]
        _ = 1 := by simp
    have : g₂⁻¹ * g₁ = 1 := by
      exact hker (g₂⁻¹ * g₁) hEq'
    -- Rearrange.
    have : g₁ = g₂ := by
      calc
        g₁ = g₂ * 1 := (inv_mul_eq_iff_eq_mul).1 this
        _ = g₂ := by simp
    exact this

  -- Build a nontrivial element fixing `b₁,b₂,b₃`.
  let L : IntermediateField ℚ (SplittingField f) :=
    IntermediateField.adjoin ℚ ({b₁, b₂, b₃} : Set (SplittingField f))
  have hLtop : L ≠ ⊤ := hbtop
  have hsep : f.Separable := PerfectField.separable_of_irreducible hf1
  letI : IsGalois ℚ (SplittingField f) :=
    IsGalois.of_separable_splitting_field (p := f) hsep
  have hfixing_ne_bot : L.fixingSubgroup ≠ (⊥ : Subgroup (AlgEquiv ℚ (SplittingField f) (SplittingField f))) := by
    intro hbot
    have hfixed :
        IntermediateField.fixedField L.fixingSubgroup = (⊤ : IntermediateField ℚ (SplittingField f)) := by
      simp [hbot, IntermediateField.fixedField_bot]
    have hfixed' : IntermediateField.fixedField L.fixingSubgroup = L :=
      IsGalois.fixedField_fixingSubgroup (K := L)
    exact hLtop (by simpa [hfixed'] using hfixed)
  rcases (Subgroup.ne_bot_iff_exists_ne_one).1 hfixing_ne_bot with ⟨g, hgne⟩
  let σ : f.Gal := g.1
  have hσne : σ ≠ 1 := by
    intro hEq
    apply hgne
    exact Subtype.ext hEq
  have hgne' : (g : AlgEquiv ℚ (SplittingField f) (SplittingField f)) ≠ 1 :=
    fun hEq => hgne (Subtype.ext hEq)
  have hgfix :
      ∀ x : SplittingField f, x ∈ L →
        (σ : AlgEquiv ℚ (SplittingField f) (SplittingField f)) x = x :=
    (IntermediateField.mem_fixingSubgroup_iff (K := L)
        (σ := (σ : AlgEquiv ℚ (SplittingField f) (SplittingField f)))).1 g.2
  have hb₁L : b₁ ∈ L := (IntermediateField.subset_adjoin ℚ ({b₁, b₂, b₃} : Set (SplittingField f))) (by simp)
  have hb₂L : b₂ ∈ L := (IntermediateField.subset_adjoin ℚ ({b₁, b₂, b₃} : Set (SplittingField f))) (by simp)
  have hb₃L : b₃ ∈ L := (IntermediateField.subset_adjoin ℚ ({b₁, b₂, b₃} : Set (SplittingField f))) (by simp)
  have hgb₁ : σ b₁ = b₁ := hgfix b₁ hb₁L
  have hgb₂ : σ b₂ = b₂ := hgfix b₂ hb₂L
  have hgb₃ : σ b₃ = b₃ := hgfix b₃ hb₃L

  -- The image contains a swap.
  let r₁ : α := ⟨b₁, hb₁⟩
  let r₂ : α := ⟨b₂, hb₂⟩
  let r₃ : α := ⟨b₃, hb₃⟩
  have hr₁₂ : r₁ ≠ r₂ := by
    intro hEq
    exact hbne.1 (congrArg Subtype.val hEq)
  have hr₂₃ : r₂ ≠ r₃ := by
    intro hEq
    exact hbne.2.1 (congrArg Subtype.val hEq)
  have hr₃₁ : r₃ ≠ r₁ := by
    intro hEq
    exact hbne.2.2 (congrArg Subtype.val hEq)
  have hτfix₁ : (ρ σ) r₁ = r₁ := by
    change σ • r₁ = r₁
    ext
    simpa [r₁, hgb₁]
  have hτfix₂ : (ρ σ) r₂ = r₂ := by
    change σ • r₂ = r₂
    ext
    simpa [r₂, hgb₂]
  have hτfix₃ : (ρ σ) r₃ = r₃ := by
    change σ • r₃ = r₃
    ext
    simpa [r₃, hgb₃]
  have hτne : ρ σ ≠ 1 := by
    intro hEq
    have : σ = 1 := hker σ hEq
    exact hσne this
  have hswap : (ρ σ).IsSwap :=
    perm_isSwap_of_three_fixed (α := α) (hcard := hcardα) (τ := ρ σ)
      (x := r₁) (y := r₂) (z := r₃) hr₁₂ hr₂₃ hr₃₁ hτfix₁ hτfix₂ hτfix₃ hτne
  have hmem : (ρ σ) ∈ H := ⟨σ, rfl⟩

  -- The image subgroup is all of `Equiv.Perm α`, hence `ρ` is surjective.
  have hHtop : H = ⊤ := by
    classical
    -- Use the standard `Fintype` instance on a subgroup coming from decidable membership.
    letI : DecidablePred (fun p : Equiv.Perm α => p ∈ H) := Classical.decPred _
    letI : Fintype (↥H) := H.instFintypeSubtypeMemOfDecidablePred
    have hprime : (Fintype.card α).Prime := by
      have : (5 : Nat).Prime := by decide
      simpa [hcardα] using this
    -- Transitivity gives `Fintype.card α ∣ Fintype.card H`.
    have hdiv : Fintype.card α ∣ Fintype.card H := by
      have horbit : MulAction.orbit H r₁ = Set.univ := by
        -- Orbits under `H` and `f.Gal` coincide because `H` is the range of the action map.
        have horbitG : MulAction.orbit f.Gal r₁ = Set.univ :=
          rootSet_orbit_eq_univ (f := f) (hf' := hf1) r₁
        ext x
        constructor
        · intro _; trivial
        · intro _
          have hx' : x ∈ MulAction.orbit f.Gal r₁ := by
            simp [horbitG]
          rcases (MulAction.mem_orbit_iff (a₁ := r₁) (a₂ := x)).1 hx' with ⟨g', rfl⟩
          refine ⟨⟨ρ g', ⟨g', rfl⟩⟩, ?_⟩
          simp [H, ρ, MulAction.toPermHom_apply]
      have hmul :
          Fintype.card (MulAction.orbit H r₁) * Fintype.card (MulAction.stabilizer H r₁) =
            Fintype.card H := by
        simpa using
          (MulAction.card_orbit_mul_card_stabilizer_eq_card_group
            (α := H) (β := α) (b := r₁))
      have horb : Fintype.card (MulAction.orbit H r₁) = Fintype.card α := by
        simp [horbit]
      have hmul' :
          Fintype.card α * Fintype.card (MulAction.stabilizer H r₁) = Fintype.card H := by
        simpa [horb] using hmul
      exact ⟨Fintype.card (MulAction.stabilizer H r₁), hmul'.symm⟩
    exact
      Equiv.Perm.subgroup_eq_top_of_swap_mem (α := α) (H := H) (τ := ρ σ)
        hprime hdiv hmem hswap

  have hρ_surj : Function.Surjective ρ := by
    intro σ
    have : σ ∈ ρ.range := by
      simp [H, hHtop]
    rcases this with ⟨g', rfl⟩
    exact ⟨g', rfl⟩
  have hρ_bij : Function.Bijective ρ := ⟨hρ_inj, hρ_surj⟩
  let eρ : f.Gal ≃* Equiv.Perm α := MulEquiv.ofBijective ρ hρ_bij
  let eα : α ≃ Fin 5 := Fintype.equivFinOfCardEq hcardα
  refine ⟨eρ.trans (Equiv.permCongrHom eα)⟩

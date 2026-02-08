import Mathlib
import Rockafellar_convex_analysis.Chapters.Chap01.section05_part9

section Chap01
section Section05

/-- Precomposition with a linear map preserves convexity on `Set.univ`. -/
lemma convexFunctionOn_precomp_linearMap {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    ∀ g : (Fin m → Real) → EReal,
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real))) g →
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fun x => g (A x)) := by
  intro g hg
  refine
    (convexFunctionOn_univ_iff_strict_inequality (f := fun x => g (A x))).2 ?_
  intro x y α β t hx hy ht0 ht1
  have hstrict := (convexFunctionOn_univ_iff_strict_inequality (f := g)).1 hg
  have hlin : A ((1 - t) • x + t • y) = (1 - t) • A x + t • A y := by
    calc
      A ((1 - t) • x + t • y)
          = A ((1 - t) • x) + A (t • y) := by
              simp [A.map_add]
      _ = (1 - t) • A x + t • A y := by
              simp [A.map_smul]
  simpa [hlin] using hstrict (A x) (A y) α β t hx hy ht0 ht1

/-- Infimum over affine fibers of a linear map preserves convexity on `Set.univ`. -/
lemma convexFunctionOn_inf_fiber_linearMap {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    ∀ h : (Fin n → Real) → EReal,
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real)))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }) := by
  classical
  intro h hh
  refine
    (convexFunctionOn_univ_iff_strict_inequality
        (f := fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })).2 ?_
  intro y1 y2 α β t hfy1 hfy2 ht0 ht1
  set S1 : Set EReal :=
    { z : EReal | ∃ x : Fin n → Real, A x = y1 ∧ z = h x }
  set S2 : Set EReal :=
    { z : EReal | ∃ x : Fin n → Real, A x = y2 ∧ z = h x }
  set S12 : Set EReal :=
    { z : EReal |
      ∃ x : Fin n → Real, A x = (1 - t) • y1 + t • y2 ∧ z = h x }
  have hneS1 : S1.Nonempty := by
    by_contra hne
    have hS1 : S1 = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfy1' := hfy1
    simp [S1, hS1, sInf_empty] at hfy1'
  have hneS2 : S2.Nonempty := by
    by_contra hne
    have hS2 : S2 = ∅ := (Set.not_nonempty_iff_eq_empty).1 hne
    have hfy2' := hfy2
    simp [S2, hS2, sInf_empty] at hfy2'
  rcases exists_lt_of_csInf_lt (s := S1) hneS1 (by simpa [S1] using hfy1) with
    ⟨z1, hz1S1, hz1lt⟩
  rcases exists_lt_of_csInf_lt (s := S2) hneS2 (by simpa [S2] using hfy2) with
    ⟨z2, hz2S2, hz2lt⟩
  rcases hz1S1 with ⟨x1, hx1, rfl⟩
  rcases hz2S2 with ⟨x2, hx2, rfl⟩
  have hstrict := (convexFunctionOn_univ_iff_strict_inequality (f := h)).1 hh
  have hAx :
      A ((1 - t) • x1 + t • x2) = (1 - t) • y1 + t • y2 := by
    calc
      A ((1 - t) • x1 + t • x2)
          = A ((1 - t) • x1) + A (t • x2) := by
              simp [A.map_add]
      _ = (1 - t) • A x1 + t • A x2 := by
              simp [A.map_smul]
      _ = (1 - t) • y1 + t • y2 := by
              simp [hx1, hx2]
  have hmem : h ((1 - t) • x1 + t • x2) ∈ S12 := by
    refine ⟨(1 - t) • x1 + t • x2, hAx, rfl⟩
  have hle : sInf S12 ≤ h ((1 - t) • x1 + t • x2) := sInf_le hmem
  have hlt :
      h ((1 - t) • x1 + t • x2) <
        ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
    hstrict x1 x2 α β t hz1lt hz2lt ht0 ht1
  have hlt' : sInf S12 <
      ((1 - t : Real) : EReal) * (α : EReal) + ((t : Real) : EReal) * (β : EReal) :=
    lt_of_le_of_lt hle hlt
  simpa [S12] using hlt'

/-- Theorem 5.7: Let `A` be a linear transformation from `R^n` to `R^m`. Then, for each convex
function `g` on `R^m`, the function `gA` defined by `(gA)(x) = g(Ax)` is convex on `R^n`.
For each convex function `h` on `R^n`, the function `Ah` defined by
`(Ah)(y) = inf { h(x) | A x = y }` is convex on `R^m`. -/
theorem convexFunctionOn_linearMap_precomp_and_inf {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real)) :
    (∀ g : (Fin m → Real) → EReal,
      ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real))) g →
        ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fun x => g (A x)))
    ∧
    (∀ h : (Fin n → Real) → EReal,
      ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h →
        ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real)))
          (fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x })) := by
  refine ⟨?_, ?_⟩
  · exact convexFunctionOn_precomp_linearMap (A := A)
  · exact convexFunctionOn_inf_fiber_linearMap (A := A)

/-- Text 5.7.1: The function `Ah` in Theorem 5.7 is called the image of `h` under `A`. -/
noncomputable def imageUnderLinearMap {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (h : (Fin n → Real) → EReal) : (Fin m → Real) → EReal :=
  fun y => sInf { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x }

/-- Text 5.7.1: The function `gA` in Theorem 5.7 is called the inverse image of `g` under `A`. -/
def inverseImageUnderLinearMap {n m : Nat}
    (A : (Fin n → Real) →ₗ[Real] (Fin m → Real))
    (g : (Fin m → Real) → EReal) : (Fin n → Real) → EReal :=
  fun x => g (A x)

/-- The coordinate projection onto the first `m` components as a linear map. -/
def projectionLinearMap {n m : Nat} (hmn : m ≤ n) :
    (Fin n → Real) →ₗ[Real] (Fin m → Real) :=
  { toFun := fun x i => x ⟨i.1, lt_of_lt_of_le i.2 hmn⟩
    map_add' := by
      intro x y
      ext i
      rfl
    map_smul' := by
      intro c x
      ext i
      rfl }

/-- Coordinate-wise characterization of the projection fiber equation. -/
lemma projectionLinearMap_eq_iff {n m : Nat} (hmn : m ≤ n)
    (x : Fin n → Real) (y : Fin m → Real) :
    projectionLinearMap hmn x = y ↔
      ∀ i : Fin m, x ⟨i.1, lt_of_lt_of_le i.2 hmn⟩ = y i := by
  constructor
  · intro h i
    have h' := congrArg (fun f => f i) h
    simpa [projectionLinearMap] using h'
  · intro h
    ext i
    exact h i

/-- Text 5.7.2: Let `A` be the projection `x = (xi_1, ..., xi_m, xi_{m+1}, ..., xi_n) ↦
  (xi_1, ..., xi_m)`. Then `(Ah)(xi_1, ..., xi_m) = inf_{xi_{m+1}, ..., xi_n}
  h(xi_1, ..., xi_n)`. This is convex in `y = (xi_1, ..., xi_m)` when `h` is convex. -/
theorem convexFunctionOn_projection_inf {n m : Nat} (hmn : m ≤ n)
    {h : (Fin n → Real) → EReal}
    (hh : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) h) :
    ConvexFunctionOn (S := (Set.univ : Set (Fin m → Real)))
      (fun y =>
        sInf { z : EReal |
          ∃ x : Fin n → Real,
            (∀ i : Fin m, x ⟨i.1, lt_of_lt_of_le i.2 hmn⟩ = y i) ∧
              z = h x }) := by
  simpa [projectionLinearMap_eq_iff] using
    (convexFunctionOn_inf_fiber_linearMap (A := projectionLinearMap hmn) h hh)

/-- For a linear equivalence, the fiber over `y` is a singleton. -/
lemma exists_eq_of_linearEquiv_fiber {n m : Nat}
    (A : (Fin n → Real) ≃ₗ[Real] (Fin m → Real))
    (h : (Fin n → Real) → EReal) :
    ∀ (y : Fin m → Real) (z : EReal),
      (∃ x : Fin n → Real, A x = y ∧ z = h x) ↔ z = h (A.symm y) := by
  intro y z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x = A.symm y := by
      calc
        x = A.symm (A x) := (A.symm_apply_apply x).symm
        _ = A.symm y := by simp [hx]
    simp [hx']
  · intro hz
    refine ⟨A.symm y, ?_, hz⟩
    simp

/-- Text 5.7.3: Let `A` be a linear transformation from `R^n` to `R^m`. When `A` is
non-singular (so `n = m` and `A^{-1}` exists), for a convex function `h` on `R^n`,
`Ah = hA^{-1}`. -/
theorem imageUnderLinearMap_eq_inverseImage_under_symm {n m : Nat}
    (A : (Fin n → Real) ≃ₗ[Real] (Fin m → Real))
    {h : (Fin n → Real) → EReal} :
    imageUnderLinearMap A.toLinearMap h =
      inverseImageUnderLinearMap A.symm.toLinearMap h := by
  funext y
  have hset :
      { z : EReal | ∃ x : Fin n → Real, A x = y ∧ z = h x } = { h (A.symm y) } := by
    ext z
    constructor
    · intro hz
      have hz' := (exists_eq_of_linearEquiv_fiber (A := A) (h := h) y z).1 hz
      simpa using hz'
    · intro hz
      have hz' : z = h (A.symm y) := by simpa using hz
      exact (exists_eq_of_linearEquiv_fiber (A := A) (h := h) y z).2 hz'
  simp [imageUnderLinearMap, inverseImageUnderLinearMap, hset, sInf_singleton]

/-- Text 5.7.4 (Partial infimal convolution): Let `n = m + p` and write `x = (y, z)` with
`y ∈ ℝ^m` and `z ∈ ℝ^p`. For proper convex `f, g : ℝ^m × ℝ^p → (-∞, +∞]`, the partial
infimal convolution of `f` and `g` with respect to the `z`-variable is the function
`h(y, z) = inf_{u ∈ ℝ^p} { f(y, z - u) + g(y, u) }`. -/
noncomputable def partialInfimalConvolutionZ {m p : Nat}
    (f g : (Fin m → Real) × (Fin p → Real) → EReal) :
    (Fin m → Real) × (Fin p → Real) → EReal :=
  fun yz =>
    sInf { r : EReal | ∃ u : Fin p → Real, r = f (yz.1, yz.2 - u) + g (yz.1, u) }

/-- Right scalar multiple at `1` returns the original function. -/
lemma rightScalarMultiple_one_eq {n : Nat} {f : (Fin n → Real) → EReal}
    (hf : ConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f) :
    ∀ x : Fin n → Real, rightScalarMultiple f (1 : Real) x = f x := by
  intro x
  have hpos : 0 < (1 : Real) := by norm_num
  have hval :=
    rightScalarMultiple_pos (f := f) (lam := (1 : Real)) (_hf := hf) (hlam := hpos) (x := x)
  simpa using hval

/-- Split a lower bound on `f1 x + f2 x` into two pieces. -/
lemma exists_mu1_mu2_of_ge_sum {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2)
    {x : Fin n → Real} {μ : EReal} (hle : f1 x + f2 x ≤ μ) :
    ∃ μ1 μ2 : EReal, μ = μ1 + μ2 ∧ f1 x ≤ μ1 ∧ f2 x ≤ μ2 := by
  classical
  by_cases htop : f1 x = ⊤
  · have hbot2 : f2 x ≠ (⊥ : EReal) := hf2.2.2 x (by simp)
    have hsum : f1 x + f2 x = ⊤ := by
      simpa [htop] using (EReal.top_add_of_ne_bot (h := hbot2))
    have hmu : μ = ⊤ := by
      apply (top_le_iff).1
      simpa [hsum] using hle
    refine ⟨⊤, f2 x, ?_, ?_, ?_⟩
    · simpa [hmu] using (EReal.top_add_of_ne_bot (h := hbot2)).symm
    · simp [htop]
    · rfl
  · have hnotbot : f1 x ≠ (⊥ : EReal) := hf1.2.2 x (by simp)
    cases h1 : f1 x with
    | bot =>
        exfalso
        exact hnotbot h1
    | top =>
        exfalso
        exact htop h1
    | coe r =>
        refine ⟨f1 x, μ - f1 x, ?_, ?_, ?_⟩
        · have hsum : (r : EReal) + (μ - r) = μ := by
            have h := (EReal.sub_add_cancel (a := μ) (b := r))
            simpa [add_comm] using h
          have hsum' : f1 x + (μ - f1 x) = μ := by
            simpa [h1] using hsum
          exact hsum'.symm
        · simp [h1]
        · have hle' : f2 x + (r : EReal) ≤ μ := by
            simpa [h1, add_comm, add_left_comm, add_assoc] using hle
          have hb : (r : EReal) ≠ ⊥ ∨ μ ≠ ⊥ := Or.inl (by simp)
          have ht : (r : EReal) ≠ ⊤ ∨ μ ≠ ⊤ := Or.inl (by simp)
          have hle'' : f2 x ≤ μ - (r : EReal) := (EReal.le_sub_iff_add_le hb ht).2 hle'
          have hle''' : f2 x ≤ μ - f1 x := by
            simpa [h1] using hle''
          exact hle'''

/-- Membership in `F` is equivalent to the sum inequality. -/
lemma mem_F_iff_ge_sum {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ μ1 μ2 : EReal, μ = μ1 + μ2 ∧
              (lam, x, μ1) ∈ K1 ∧ (lam, x, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x : Fin n → Real} {μ : EReal}, (x, μ) ∈ F ↔ f1 x + f2 x ≤ μ := by
  classical
  simp [rightScalarMultiple_one_eq (hf := hf1.1), rightScalarMultiple_one_eq (hf := hf2.1)]
  intro x μ
  constructor
  · rintro ⟨μ1, μ2, hμ, hμ1, hμ2⟩
    have hsum : f1 x + f2 x ≤ μ1 + μ2 := add_le_add hμ1 hμ2
    simpa [hμ] using hsum
  · intro hle
    rcases
        exists_mu1_mu2_of_ge_sum (hf1 := hf1) (hf2 := hf2) (x := x) (μ := μ) hle with
      ⟨μ1, μ2, hμ, hμ1, hμ2⟩
    exact ⟨μ1, μ2, hμ, hμ1, hμ2⟩

/-- The infimum of the upper set `{μ | a ≤ μ}` is `a`. -/
lemma sInf_Ici_eq_self {a : EReal} : sInf { μ : EReal | a ≤ μ } = a := by
  refine le_antisymm ?_ ?_
  · exact sInf_le (by simp)
  · refine le_sInf ?_
    intro μ hμ
    exact hμ

/-- Text 5.8.0.1: Let `f1`, `f2` be proper convex functions on `ℝ^n`. Define
`K1 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f1 λ)(x) }` and
`K2 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f2 λ)(x) }`. Let
`K = { (λ, x, μ) | ∃ μ1 μ2, μ = μ1 + μ2, (λ, x, μ1) ∈ K1, (λ, x, μ2) ∈ K2 }`,
`F = { (x, μ) | (1, x, μ) ∈ K }`, and
`f x = inf { μ | (x, μ) ∈ F }`. Then `f = f1 + f2`. -/
theorem sum_properConvex_eq_inf_of_K {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ μ1 μ2 : EReal, μ = μ1 + μ2 ∧
              (lam, x, μ1) ∈ K1 ∧ (lam, x, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    let f : (Fin n → Real) → EReal :=
      fun x => sInf { μ : EReal | (x, μ) ∈ F }
    f = fun x => f1 x + f2 x := by
  classical
  funext x
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1)]
  have hset :
      { μ : EReal |
        ∃ μ1 μ2 : EReal, μ = μ1 + μ2 ∧ f1 x ≤ μ1 ∧ f2 x ≤ μ2 } =
        { μ : EReal | f1 x + f2 x ≤ μ } := by
    ext μ
    constructor
    · rintro ⟨μ1, μ2, hμ, hμ1, hμ2⟩
      have hsum : f1 x + f2 x ≤ μ1 + μ2 := add_le_add hμ1 hμ2
      simpa [hμ] using hsum
    · intro hle
      rcases
          exists_mu1_mu2_of_ge_sum (hf1 := hf1) (hf2 := hf2) (x := x) (μ := μ) hle with
        ⟨μ1, μ2, hμ, hμ1, hμ2⟩
      exact ⟨μ1, μ2, hμ, hμ1, hμ2⟩
  simp [hset, sInf_Ici_eq_self]

/-- Exact sums lie in `F`. -/
lemma mem_F_of_exact_sum {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
              μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                (lam, x1, μ1) ∈ K1 ∧ (lam, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x x1 x2 : Fin n → Real} {μ : EReal},
      x1 + x2 = x → μ = f1 x1 + f2 x2 → (x, μ) ∈ F := by
  classical
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1)]
  intro x x1 x2 hsum
  refine ⟨f1 x1, f2 x2, rfl, ?_⟩
  exact ⟨x1, x2, hsum.symm, le_rfl, le_rfl⟩

/-- Membership in `F` yields a split with a lower bound on `μ`. -/
lemma exists_sum_le_of_mem_F {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
              μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                (lam, x1, μ1) ∈ K1 ∧ (lam, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x : Fin n → Real} {μ : EReal}, (x, μ) ∈ F →
      ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ f1 x1 + f2 x2 ≤ μ := by
  classical
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1)]
  intro x μ μ1 μ2 hμ x1 x2 hsum hμ1 hμ2
  refine ⟨x1, x2, hsum.symm, ?_⟩
  have hsum_le : f1 x1 + f2 x2 ≤ μ1 + μ2 := add_le_add hμ1 hμ2
  simpa [hμ] using hsum_le

/-- The `sInf` defining `F` matches the infimal convolution set pointwise. -/
lemma sInf_F_eq_sInf_infimal_pointwise {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
              μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                (lam, x1, μ1) ∈ K1 ∧ (lam, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ x : Fin n → Real,
      sInf { μ : EReal | (x, μ) ∈ F } =
        sInf { z : EReal |
          ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ z = f1 x1 + f2 x2 } := by
  classical
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1)]
  intro x
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    intro z hz
    rcases hz with ⟨x1, x2, hsum, rfl⟩
    refine sInf_le ?_
    exact ⟨f1 x1, f2 x2, rfl, x1, x2, hsum.symm, le_rfl, le_rfl⟩
  · refine le_sInf ?_
    intro μ hμ
    rcases hμ with ⟨μ1, μ2, hμ, x1, x2, hsum, hμ1, hμ2⟩
    have hle' :
        sInf { z : EReal |
          ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧ z = f1 x1 + f2 x2 } ≤
          f1 x1 + f2 x2 := by
      refine sInf_le ?_
      exact ⟨x1, x2, hsum.symm, rfl⟩
    have hsum_le : f1 x1 + f2 x2 ≤ μ1 + μ2 := add_le_add hμ1 hμ2
    exact le_trans hle' (by simpa [hμ] using hsum_le)

/-- Text 5.8.0.2: Let `f1`, `f2` be proper convex functions on `ℝ^n`. Define
`K1 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f1 λ)(x) }` and
`K2 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f2 λ)(x) }`. Let
`K = { (λ, x, μ) | ∃ μ1 μ2 x1 x2, μ = μ1 + μ2, x = x1 + x2,
  (λ, x1, μ1) ∈ K1, (λ, x2, μ2) ∈ K2 }`,
`F = { (x, μ) | (1, x, μ) ∈ K }`, and
`f x = inf { μ | (x, μ) ∈ F }`. Then `f = f1 □ f2`. -/
theorem infimalConvolution_eq_inf_of_K {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
              μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                (lam, x1, μ1) ∈ K1 ∧ (lam, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    let f : (Fin n → Real) → EReal :=
      fun x => sInf { μ : EReal | (x, μ) ∈ F }
    f = infimalConvolution f1 f2 := by
  classical
  funext x
  simpa [infimalConvolution] using
    (sInf_F_eq_sInf_infimal_pointwise (hf1 := hf1) (hf2 := hf2) (x := x))

/-- Unpack membership in `F` for the pairwise convex hull construction. -/
lemma mem_F_iff_exists_pair {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
              ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
                lam = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                  (lam1, x1, μ1) ∈ K1 ∧ (lam2, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x : Fin n → Real} {μ : EReal}, (x, μ) ∈ F ↔
      ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
        ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
          (1 : ℝ) = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
            (0 ≤ lam1 ∧ rightScalarMultiple f1 lam1 x1 ≤ μ1) ∧
            (0 ≤ lam2 ∧ rightScalarMultiple f2 lam2 x2 ≤ μ2) := by
  classical
  simp

/-- Membership in `F` yields a weighted split with a lower bound on `μ`. -/
lemma exists_sum_le_of_mem_F_pair {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
              ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
                lam = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                  (lam1, x1, μ1) ∈ K1 ∧ (lam2, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x : Fin n → Real} {μ : EReal}, (x, μ) ∈ F →
      ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
        ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
          rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 ≤ μ := by
  classical
  intro K1 K2 K F x μ hmem
  rcases
      (mem_F_iff_exists_pair (f1 := f1) (f2 := f2) (x := x) (μ := μ)).1 hmem with
    ⟨lam1, lam2, hlam1, hlam2, μ1, μ2, x1, x2, hlam, hμ, hx, hK1, hK2⟩
  rcases hK1 with ⟨_, hμ1⟩
  rcases hK2 with ⟨_, hμ2⟩
  refine ⟨lam1, lam2, hlam1, hlam2, hlam.symm, x1, x2, hx.symm, ?_⟩
  have hsum_le :
      rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 ≤ μ1 + μ2 :=
    add_le_add hμ1 hμ2
  simpa [hμ] using hsum_le

/-- Exact weighted sums belong to `F`. -/
lemma mem_F_of_exact_sum_pair {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
              ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
                lam = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                  (lam1, x1, μ1) ∈ K1 ∧ (lam2, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x x1 x2 : Fin n → Real} {lam1 lam2 : ℝ},
      0 ≤ lam1 → 0 ≤ lam2 → lam1 + lam2 = 1 → x1 + x2 = x →
        (x, rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2) ∈ F := by
  classical
  intro K1 K2 K F x x1 x2 lam1 lam2 hlam1 hlam2 hsum hsumx
  refine
    (mem_F_iff_exists_pair (f1 := f1) (f2 := f2) (x := x)
        (μ := rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2)).2 ?_
  refine ⟨lam1, lam2, hlam1, hlam2, rightScalarMultiple f1 lam1 x1,
    rightScalarMultiple f2 lam2 x2, x1, x2, hsum.symm, rfl, hsumx.symm, ?_, ?_⟩
  · exact ⟨hlam1, le_rfl⟩
  · exact ⟨hlam2, le_rfl⟩

/-- The `sInf` defining `F` matches the pairwise `rightScalarMultiple` infimum. -/
lemma sInf_F_eq_sInf_rightScalarMultiple_pair {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
              ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
                lam = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                  (lam1, x1, μ1) ∈ K1 ∧ (lam2, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ x : Fin n → Real,
      sInf { μ : EReal | (x, μ) ∈ F } =
        sInf { z : EReal |
          ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
            ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
              z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 } := by
  classical
  intro K1 K2 K F x
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    intro z hz
    rcases hz with ⟨lam1, lam2, hlam1, hlam2, hsum, x1, x2, hsumx, rfl⟩
    refine sInf_le ?_
    exact
      mem_F_of_exact_sum_pair (f1 := f1) (f2 := f2) (x := x)
        (x1 := x1) (x2 := x2) (lam1 := lam1) (lam2 := lam2)
        hlam1 hlam2 hsum hsumx
  · refine le_sInf ?_
    intro μ hμ
    rcases
        exists_sum_le_of_mem_F_pair (f1 := f1) (f2 := f2) (x := x) (μ := μ) hμ with
      ⟨lam1, lam2, hlam1, hlam2, hsum, x1, x2, hsumx, hle⟩
    have hle' :
        sInf { z : EReal |
          ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
            ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
              z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 } ≤
          rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 := by
      refine sInf_le ?_
      exact ⟨lam1, lam2, hlam1, hlam2, hsum, x1, x2, hsumx, rfl⟩
    exact le_trans hle' hle

/-- The pairwise `rightScalarMultiple` infimum matches the `Fin 2` family form. -/
lemma sInf_pair_eq_sInf_infimalConvolutionFamily {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    ∀ x : Fin n → Real,
      sInf { z : EReal |
        ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
          ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
            z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 } =
        sInf { z : EReal |
          ∃ lam : Fin 2 → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            z = infimalConvolutionFamily
              (fun i => rightScalarMultiple (if i = 0 then f1 else f2) (lam i)) x } := by
  classical
  intro x
  let fi : Fin 2 → (Fin n → Real) → EReal := fun i => if i = 0 then f1 else f2
  let S : Set EReal :=
    { z : EReal |
      ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
        ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
          z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 }
  let Blam : (Fin 2 → Real) → Set EReal := fun lam =>
    { z : EReal |
      ∃ x' : Fin 2 → (Fin n → Real),
        (Finset.univ.sum (fun i => x' i) = x) ∧
        z = Finset.univ.sum (fun i => rightScalarMultiple (fi i) (lam i) (x' i)) }
  let B : Set EReal :=
    { z : EReal |
      ∃ lam : Fin 2 → Real,
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        z ∈ Blam lam }
  let A : Set EReal :=
    { z : EReal |
      ∃ lam : Fin 2 → Real,
        (∀ i, 0 ≤ lam i) ∧
        (Finset.univ.sum (fun i => lam i) = 1) ∧
        z = infimalConvolutionFamily (fun i => rightScalarMultiple (fi i) (lam i)) x }
  have hSB : S = B := by
    ext z
    constructor
    · rintro ⟨lam1, lam2, hlam1, hlam2, hsumlam, x1, x2, hsumx, rfl⟩
      refine ⟨(fun i : Fin 2 => if i = 0 then lam1 else lam2), ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hlam1, hlam2]
      · simp [Fin.sum_univ_two, hsumlam]
      · refine ⟨fun i : Fin 2 => if i = 0 then x1 else x2, ?_, ?_⟩
        · simp [Fin.sum_univ_two, hsumx]
        · simp [fi, Fin.sum_univ_two]
    · rintro ⟨lam, hlam, hsumlam, hzB⟩
      rcases hzB with ⟨x', hsumx, rfl⟩
      refine ⟨lam 0, lam 1, ?_, ?_, ?_, x' 0, x' 1, ?_, ?_⟩
      · exact hlam 0
      · exact hlam 1
      · simpa [Fin.sum_univ_two] using hsumlam
      · simpa [Fin.sum_univ_two] using hsumx
      · simp [fi, Fin.sum_univ_two]
  have hBA : sInf B = sInf A := by
    apply le_antisymm
    · refine le_sInf ?_
      intro z hz
      rcases hz with ⟨lam, hlam, hsumlam, rfl⟩
      have hle : sInf B ≤ sInf (Blam lam) := by
        refine le_sInf ?_
        intro z hz
        exact sInf_le ⟨lam, hlam, hsumlam, hz⟩
      simpa [infimalConvolutionFamily, Blam] using hle
    · refine le_sInf ?_
      intro z hz
      rcases hz with ⟨lam, hlam, hsumlam, hzB⟩
      have hA_le : sInf A ≤ sInf (Blam lam) := by
        refine sInf_le ?_
        refine ⟨lam, hlam, hsumlam, ?_⟩
        simp [infimalConvolutionFamily, Blam]
      have hle : sInf (Blam lam) ≤ z := sInf_le hzB
      exact le_trans hA_le hle
  calc
    sInf S = sInf B := by simp [hSB]
    _ = sInf A := hBA

/-- Text 5.8.0.3: Let `f1`, `f2` be proper convex functions on `ℝ^n`. Define
`K1 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f1 λ)(x) }` and
`K2 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f2 λ)(x) }`. Let
`K = { (λ, x, μ) | ∃ λ1, λ2 ≥ 0, ∃ μ1, μ2, x1, x2,
  λ = λ1 + λ2, μ = μ1 + μ2, x = x1 + x2,
  (λ1, x1, μ1) ∈ K1, (λ2, x2, μ2) ∈ K2 }`,
`F = { (x, μ) | (1, x, μ) ∈ K }`, and
`f x = inf { μ | (x, μ) ∈ F }`. Then `f = conv{f1, f2}`. -/
theorem convexHullFunctionPair_eq_inf_of_K {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
              ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
                lam = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                  (lam1, x1, μ1) ∈ K1 ∧ (lam2, x2, μ2) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    let f : (Fin n → Real) → EReal :=
      fun x => sInf { μ : EReal | (x, μ) ∈ F }
    f = convexHullFunctionFamily (fun i : Fin 2 => if i = 0 then f1 else f2) := by
  classical
  funext x
  let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
    { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
          0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
  let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
    { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
          0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
  let K : Set (ℝ × (Fin n → Real) × EReal) :=
    { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
          ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧
            ∃ μ1 μ2 : EReal, ∃ x1 x2 : Fin n → Real,
              lam = lam1 + lam2 ∧ μ = μ1 + μ2 ∧ x = x1 + x2 ∧
                (lam1, x1, μ1) ∈ K1 ∧ (lam2, x2, μ2) ∈ K2 }
  let F : Set ((Fin n → Real) × EReal) :=
    { p | ((1 : ℝ), p.1, p.2) ∈ K }
  change sInf { μ : EReal | (x, μ) ∈ F } =
    convexHullFunctionFamily (fun i : Fin 2 => if i = 0 then f1 else f2) x
  let fi : Fin 2 → (Fin n → Real) → EReal := fun i => if i = 0 then f1 else f2
  have hfi :
      ∀ i : Fin 2, ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) (fi i) := by
    intro i
    fin_cases i <;> simp [fi, hf1, hf2]
  have h1 :
      sInf { μ : EReal | (x, μ) ∈ F } =
        sInf { z : EReal |
          ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
            ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
              z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 } := by
    simpa [F, K, K1, K2] using
      (sInf_F_eq_sInf_rightScalarMultiple_pair (f1 := f1) (f2 := f2) (x := x))
  have h2 :
      sInf { z : EReal |
        ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
          ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
            z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 } =
        sInf { z : EReal |
          ∃ lam : Fin 2 → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            z = infimalConvolutionFamily
              (fun i => rightScalarMultiple (fi i) (lam i)) x } := by
    simpa [fi] using
      (sInf_pair_eq_sInf_infimalConvolutionFamily (f1 := f1) (f2 := f2) (x := x))
  have hconv :
      convexHullFunctionFamily fi x =
        sInf { z : EReal |
          ∃ lam : Fin 2 → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            z = infimalConvolutionFamily
              (fun i => rightScalarMultiple (fi i) (lam i)) x } := by
    simpa [fi] using
      (convexHullFunctionFamily_eq_sInf_infimalConvolution_rightScalarMultiple (f := fi) hfi x)
  calc
    sInf { μ : EReal | (x, μ) ∈ F } =
        sInf { z : EReal |
          ∃ lam1 lam2 : ℝ, 0 ≤ lam1 ∧ 0 ≤ lam2 ∧ lam1 + lam2 = 1 ∧
            ∃ x1 x2 : Fin n → Real, x1 + x2 = x ∧
              z = rightScalarMultiple f1 lam1 x1 + rightScalarMultiple f2 lam2 x2 } := h1
    _ =
        sInf { z : EReal |
          ∃ lam : Fin 2 → Real,
            (∀ i, 0 ≤ lam i) ∧
            (Finset.univ.sum (fun i => lam i) = 1) ∧
            z = infimalConvolutionFamily
              (fun i => rightScalarMultiple (fi i) (lam i)) x } := h2
    _ = convexHullFunctionFamily fi x := by
      simpa using hconv.symm

/-- Membership in `F` is equivalent to simultaneous lower bounds for `f1` and `f2`. -/
lemma mem_F_iff_ge_both {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            (lam, x, μ) ∈ K1 ∧ (lam, x, μ) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x : Fin n → Real} {μ : EReal}, (x, μ) ∈ F ↔ f1 x ≤ μ ∧ f2 x ≤ μ := by
  classical
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1), and_left_comm, and_comm]

/-- Membership in `F` is equivalent to a max lower bound. -/
lemma mem_F_iff_ge_max {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            (lam, x, μ) ∈ K1 ∧ (lam, x, μ) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    ∀ {x : Fin n → Real} {μ : EReal}, (x, μ) ∈ F ↔ max (f1 x) (f2 x) ≤ μ := by
  classical
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1)]

/-- The infimum of the upper set for the max is the max. -/
lemma sInf_ge_max_eq {n : Nat} {f1 f2 : (Fin n → Real) → EReal} :
    ∀ x : Fin n → Real,
      sInf { μ : EReal | max (f1 x) (f2 x) ≤ μ } = max (f1 x) (f2 x) := by
  intro x
  simpa using (sInf_Ici_eq_self (a := max (f1 x) (f2 x)))

/-- Text 5.8.0.4: Let `f1`, `f2` be proper convex functions on `ℝ^n`. Define
`K1 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f1 λ)(x) }` and
`K2 = { (λ, x, μ) | λ ≥ 0, μ ≥ (f2 λ)(x) }`. Let
`K = { (λ, x, μ) | (λ, x, μ) ∈ K1, (λ, x, μ) ∈ K2 }`,
`F = { (x, μ) | (1, x, μ) ∈ K }`, and
`f x = inf { μ | (x, μ) ∈ F }`. Then `f = max{f1, f2}`. -/
theorem max_properConvex_eq_inf_of_K {n : Nat} {f1 f2 : (Fin n → Real) → EReal}
    (hf1 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f1)
    (hf2 : ProperConvexFunctionOn (S := (Set.univ : Set (Fin n → Real))) f2) :
    let K1 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f1 lam x }
    let K2 : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            0 ≤ lam ∧ μ ≥ rightScalarMultiple f2 lam x }
    let K : Set (ℝ × (Fin n → Real) × EReal) :=
      { p | let lam := p.1; let x := p.2.1; let μ := p.2.2;
            (lam, x, μ) ∈ K1 ∧ (lam, x, μ) ∈ K2 }
    let F : Set ((Fin n → Real) × EReal) :=
      { p | ((1 : ℝ), p.1, p.2) ∈ K }
    let f : (Fin n → Real) → EReal :=
      fun x => sInf { μ : EReal | (x, μ) ∈ F }
    f = fun x => max (f1 x) (f2 x) := by
  classical
  funext x
  simp [rightScalarMultiple_one_eq (hf := hf1.1),
    rightScalarMultiple_one_eq (hf := hf2.1)]
  have hset :
      { μ : EReal | f1 x ≤ μ ∧ f2 x ≤ μ } =
        { μ : EReal | max (f1 x) (f2 x) ≤ μ } := by
    ext μ
    simp
  simp [hset, sInf_Ici_eq_self]

/-- Sum of pointwise convex combinations equals the convex combination of sums. -/
lemma sum_components_convex_combo {n m : Nat}
    (x' y' : Fin m → (Fin n → Real)) (t : Real) :
    Finset.univ.sum (fun i => (1 - t) • x' i + t • y' i) =
      (1 - t) • Finset.univ.sum (fun i => x' i) +
        t • Finset.univ.sum (fun i => y' i) := by
  have hsumx :
      Finset.univ.sum (fun i => (1 - t) • x' i) =
        (1 - t) • Finset.univ.sum (fun i => x' i) := by
    symm
    simpa using
      (Finset.smul_sum (s := Finset.univ) (f := fun i => x' i) (r := (1 - t)))
  have hsumy :
      Finset.univ.sum (fun i => t • y' i) =
        t • Finset.univ.sum (fun i => y' i) := by
    symm
    simpa using
      (Finset.smul_sum (s := Finset.univ) (f := fun i => y' i) (r := t))
  calc
    Finset.univ.sum (fun i => (1 - t) • x' i + t • y' i) =
        Finset.univ.sum (fun i => (1 - t) • x' i) +
          Finset.univ.sum (fun i => t • y' i) := by
            simp [Finset.sum_add_distrib]
    _ = (1 - t) • Finset.univ.sum (fun i => x' i) +
          t • Finset.univ.sum (fun i => y' i) := by
            simp [hsumx, hsumy]

/-- On a nonempty finite index, `iSup` preserves strict upper bounds. -/
lemma iSup_lt_of_forall_lt_fin {m : Nat} {a : Fin m → EReal} {r : EReal}
    (hm : 0 < m) (h : ∀ i, a i < r) : iSup a < r := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨i0, hi0⟩ := (exists_eq_ciSup_of_finite (f := a))
  have hlt := h i0
  simpa [hi0] using hlt

end Section05
end Chap01

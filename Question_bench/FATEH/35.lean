import Mathlib

open Polynomial IntermediateField Module

/- Let $D \in \mathbb{Z}$ be a squarefree integer and let $a \in \mathbb{Q}$ be a nonzero rational number.
Show that $\mathbb{Q}(\sqrt{a\sqrt D})$ cannot be a cyclic extension of degree $4$ over $\mathbb{Q}$.-/
namespace FATEH35

/-!
Helpers for the group-theoretic part: `Multiplicative (ZMod 4)` has an element of order `4`,
and any group isomorphic to it must also have such an element.
-/

lemma zmod4_orderOf_generator : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
  -- `ofAdd 1` corresponds to `1` in the additive group `ZMod 4`.
  simp [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

lemma pullback_has_order4 {G : Type*} [Group G] (e : G ≃* Multiplicative (ZMod 4)) :
    orderOf (e.symm (Multiplicative.ofAdd (1 : ZMod 4))) = 4 := by
  -- Orders are preserved by group isomorphisms.
  exact (MulEquiv.orderOf_eq e.symm (Multiplicative.ofAdd (1 : ZMod 4))).trans zmod4_orderOf_generator

/-!
Algebraic part: build the canonical involution on `AdjoinRoot` coming from `X ↦ -X`,
and show that any automorphism commuting with it has square `1`.
-/

noncomputable abbrev poly (d : ℤ) (a : ℚ) : ℚ[X] :=
  (a⁻¹ • X ^ 2) ^ 2 - C (d : ℚ)

lemma poly_eq (d : ℤ) (a : ℚ) :
    poly d a = (C ((a⁻¹ : ℚ) ^ 2) * X ^ 4 : ℚ[X]) - C (d : ℚ) := by
  simp [poly, pow_two, Polynomial.smul_eq_C_mul]
  ring

lemma poly_ne_zero {d : ℤ} {a : ℚ} (ha : a ≠ 0) : poly d a ≠ 0 := by
  intro h
  have hcoeff : (poly d a).coeff 4 = (a⁻¹ : ℚ) ^ 2 := by
    rw [poly_eq d a]
    -- Avoid rewriting `C (d : ℚ)` to `↑d`, since `simp` may then get stuck on `coeff`.
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow, coeff_C]
    simp
  have : (poly d a).coeff 4 = 0 := by
    have h' := congrArg (fun q : ℚ[X] => q.coeff 4) h
    have h'' : (0 : ℚ[X]).coeff 4 = 0 := by simp
    exact h'.trans h''
  have : (a⁻¹ : ℚ) ^ 2 = 0 := by simpa [hcoeff] using this
  exact (pow_ne_zero 2 (inv_ne_zero ha)) this

lemma natDegree_poly {d : ℤ} {a : ℚ} (ha : a ≠ 0) : (poly d a).natDegree = 4 := by
  have ha2 : ((a ^ 2)⁻¹ : ℚ) ≠ 0 := inv_ne_zero (pow_ne_zero 2 ha)
  have hpoly' : poly d a = (C ((a ^ 2)⁻¹) * X ^ 4 : ℚ[X]) - C (d : ℚ) := by
    simpa [pow_two] using (poly_eq d a)
  rw [hpoly']
  have h1 : (C ((a ^ 2)⁻¹) * X ^ 4 : ℚ[X]).natDegree = 4 := by
    simpa using (natDegree_C_mul_X_pow (R := ℚ) 4 ((a ^ 2)⁻¹) ha2)
  have hC : (C (d : ℚ) : ℚ[X]).natDegree = 0 := by
    by_cases hd0 : (d : ℚ) = 0 <;> simp [hd0]
  have hlt : (C (d : ℚ) : ℚ[X]).natDegree < (C ((a ^ 2)⁻¹) * X ^ 4 : ℚ[X]).natDegree := by
    rw [hC, h1]
    decide
  have := natDegree_sub_eq_left_of_natDegree_lt
    (p := (C ((a ^ 2)⁻¹) * X ^ 4 : ℚ[X])) (q := (C (d : ℚ) : ℚ[X])) hlt
  simpa [h1] using this

noncomputable def negRootAlgEquiv {d : ℤ} {a : ℚ} (ha : a ≠ 0) :
    AdjoinRoot (poly d a) ≃ₐ[ℚ] AdjoinRoot (poly d a) := by
  classical
  -- The construction works for all `a`, but we keep `ha` as an explicit parameter.
  have _ : a ≠ 0 := ha
  let α : AdjoinRoot (poly d a) := AdjoinRoot.root (poly d a)
  have h :
      (poly d a).eval₂ (Algebra.ofId ℚ (AdjoinRoot (poly d a))) (-α) =
        (0 : AdjoinRoot (poly d a)) := by
    -- `poly d a` is even, so `-α` is also a root.
    have hα :
        (poly d a).eval₂ (Algebra.ofId ℚ (AdjoinRoot (poly d a))) α =
          (0 : AdjoinRoot (poly d a)) := by
      simpa [α] using (AdjoinRoot.eval₂_root (f := poly d a))
    have hev :
        (poly d a).eval₂ (Algebra.ofId ℚ (AdjoinRoot (poly d a))) (-α) =
          (poly d a).eval₂ (Algebra.ofId ℚ (AdjoinRoot (poly d a))) α := by
      -- `simp` reduces to the constant term, which we discharge by rewriting `↑d` as `C (d : ℚ)`.
      simp [poly, pow_two]
      rw [← Polynomial.C_eq_intCast (R := ℚ) d]
      simp only [Polynomial.eval₂_C]
    exact hev.trans hα
  let f : AdjoinRoot (poly d a) →ₐ[ℚ] AdjoinRoot (poly d a) :=
    AdjoinRoot.liftAlgHom (poly d a) (Algebra.ofId ℚ (AdjoinRoot (poly d a))) (-α) h
  refine AlgEquiv.ofAlgHom f f ?_ ?_
  · ext
    simp [f, α]
  · ext
    simp [f, α]

@[simp] lemma negRootAlgEquiv_apply_root {d : ℤ} {a : ℚ} (ha : a ≠ 0) :
    negRootAlgEquiv (d := d) (a := a) ha (AdjoinRoot.root (poly d a)) =
      -(AdjoinRoot.root (poly d a)) := by
  simp [negRootAlgEquiv, poly]

lemma root_pow4_eq_scalar {d : ℤ} {a : ℚ} (ha : a ≠ 0) :
    (AdjoinRoot.root (poly d a) : AdjoinRoot (poly d a)) ^ 4 =
      algebraMap ℚ (AdjoinRoot (poly d a)) (a ^ 2 * (d : ℚ)) := by
  classical
  let A := AdjoinRoot (poly d a)
  let α : A := AdjoinRoot.root (poly d a)
  have hroot : (poly d a).eval₂ (AdjoinRoot.of (poly d a)) α = 0 := by
    simpa [α] using (AdjoinRoot.eval₂_root (f := poly d a))
  have hconst : eval₂ (AdjoinRoot.of (poly d a)) α (↑d : ℚ[X]) = (AdjoinRoot.of (poly d a)) (d : ℚ) := by
    rw [← Polynomial.C_eq_intCast (R := ℚ) d]
    simp only [Polynomial.eval₂_C]
  have h' :
      (AdjoinRoot.of (poly d a)) ((a ^ 2)⁻¹ : ℚ) * α ^ 4 - (AdjoinRoot.of (poly d a)) (d : ℚ) = 0 := by
    have hroot' :
        (AdjoinRoot.of (poly d a)) ((a ^ 2)⁻¹ : ℚ) * α ^ 4 -
            eval₂ (AdjoinRoot.of (poly d a)) α (↑d : ℚ[X]) = 0 := by
      simpa [poly_eq d a, α, inv_pow, pow_two] using hroot
    simpa [hconst] using hroot'
  have h2 :
      (AdjoinRoot.of (poly d a)) ((a ^ 2)⁻¹ : ℚ) * α ^ 4 = (AdjoinRoot.of (poly d a)) (d : ℚ) :=
    sub_eq_zero.mp h'
  have h3 := congrArg (fun x => (AdjoinRoot.of (poly d a)) (a ^ 2) * x) h2
  have ha2 : (a ^ 2 : ℚ) ≠ 0 := pow_ne_zero 2 ha
  have hinv :
      (AdjoinRoot.of (poly d a)) (a ^ 2 : ℚ) * (AdjoinRoot.of (poly d a)) ((a ^ 2)⁻¹ : ℚ) = (1 : A) := by
    -- rewrite as the image of `a^2 * (a^2)⁻¹ = 1` under the ring hom
    have :
        (AdjoinRoot.of (poly d a)) (a ^ 2 : ℚ) * (AdjoinRoot.of (poly d a)) ((a ^ 2)⁻¹ : ℚ) =
          (AdjoinRoot.of (poly d a)) ((a ^ 2 : ℚ) * (a ^ 2)⁻¹) := by
      simp
    simpa [this, ha2]
  have h3'' :
      ((AdjoinRoot.of (poly d a)) (a ^ 2 : ℚ) * (AdjoinRoot.of (poly d a)) ((a ^ 2)⁻¹ : ℚ)) * α ^ 4 =
        (AdjoinRoot.of (poly d a)) (a ^ 2 : ℚ) * (AdjoinRoot.of (poly d a)) (d : ℚ) := by
    -- rewrite `x * (y * z)` as `(x * y) * z`
    simpa [mul_assoc] using h3
  have hα4' :
      α ^ 4 = (AdjoinRoot.of (poly d a)) (a ^ 2 : ℚ) * (AdjoinRoot.of (poly d a)) (d : ℚ) := by
    have h3''' := h3''
    rw [hinv] at h3'''
    simpa using h3'''
  have : α ^ 4 = (AdjoinRoot.of (poly d a)) (a ^ 2 * (d : ℚ)) := by
    -- combine the product on the right into a single `of` using `map_mul`
    simpa using hα4'.trans
      (by
        symm
        simp)
  -- `algebraMap` is definitional for `AdjoinRoot`; we keep it in the statement.
  simpa [A, α] using this

private lemma alpha_pow6_eq {d : ℤ} {a : ℚ} (c0 : ℚ)
    (hα : (AdjoinRoot.root (poly d a) : AdjoinRoot (poly d a)) ^ 4 =
      algebraMap ℚ (AdjoinRoot (poly d a)) c0) :
    (AdjoinRoot.root (poly d a) : AdjoinRoot (poly d a)) ^ 6 =
      algebraMap ℚ (AdjoinRoot (poly d a)) c0 *
        (AdjoinRoot.root (poly d a) : AdjoinRoot (poly d a)) ^ 2 := by
  let A := AdjoinRoot (poly d a)
  let α : A := AdjoinRoot.root (poly d a)
  calc
    α ^ 6 = α ^ 4 * α ^ 2 := by
      simpa [pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (pow_add α 4 2)
    _ = algebraMap ℚ A c0 * α ^ 2 := by simp [hα, A, α]

private lemma beta_sq_eq_generic {A : Type*} [CommRing A] [Algebra ℚ A] (α : A) (c0 r s : ℚ)
    (hα : α ^ 4 = algebraMap ℚ A c0) :
    (r • α + s • α ^ 3 : A) ^ 2 = (r ^ 2 + c0 * s ^ 2) • α ^ 2 + algebraMap ℚ A (2 * r * s * c0) := by
  have h6 : α ^ 6 = algebraMap ℚ A c0 * α ^ 2 := by
    calc
      α ^ 6 = α ^ 4 * α ^ 2 := by
        simpa [pow_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using (pow_add α 4 2)
      _ = algebraMap ℚ A c0 * α ^ 2 := by simp [hα]
  -- Expand the square first, then rewrite `α^4` and `α^6` using `hα` and `h6`.
  simp [pow_two, add_mul, mul_add, Algebra.smul_def]
  ring_nf
  simp [hα, h6]
  ring_nf
  -- `ring_nf` leaves a harmless `2` vs `algebraMap 2` mismatch (because `map_ofNat` isn't `[simp]`).
  simp [map_ofNat (algebraMap ℚ A) 2]

private lemma beta_pow4_eq_generic {A : Type*} [CommRing A] [Algebra ℚ A] (α : A) (c0 r s : ℚ)
    (hα : α ^ 4 = algebraMap ℚ A c0) :
    (r • α + s • α ^ 3 : A) ^ 4 =
      algebraMap ℚ A ((r ^ 2 + c0 * s ^ 2) ^ 2 * c0 + (2 * r * s * c0) ^ 2) +
        (2 * (r ^ 2 + c0 * s ^ 2) * (2 * r * s * c0)) • α ^ 2 := by
  let u : ℚ := r ^ 2 + c0 * s ^ 2
  let v : ℚ := 2 * r * s * c0
  have hβ2 :
      (r • α + s • α ^ 3 : A) ^ 2 = u • α ^ 2 + algebraMap ℚ A v := by
    simpa [u, v] using beta_sq_eq_generic (A := A) α c0 r s hα
  calc
    (r • α + s • α ^ 3 : A) ^ 4 = ((r • α + s • α ^ 3 : A) ^ 2) ^ 2 := by
      simpa [show (2 * 2 : ℕ) = 4 by decide] using (pow_mul (r • α + s • α ^ 3 : A) 2 2)
    _ = (u • α ^ 2 + algebraMap ℚ A v) ^ 2 := by simp [hβ2]
    _ = _ := by
      simp [pow_two, add_mul, mul_add, Algebra.smul_def]
      ring_nf
      simp [hα, u, v]
      ring_nf
      simp [map_ofNat (algebraMap ℚ A) 2, pow_two]
      ring_nf

private lemma beta_sq_eq {d : ℤ} {a : ℚ} (c0 r s : ℚ)
    (hα : (AdjoinRoot.root (poly d a) : AdjoinRoot (poly d a)) ^ 4 =
      algebraMap ℚ (AdjoinRoot (poly d a)) c0) :
    let A := AdjoinRoot (poly d a)
    let α : A := AdjoinRoot.root (poly d a)
    ((r • α + s • α ^ 3 : A) ^ 2) =
      (r ^ 2 + c0 * s ^ 2) • α ^ 2 + algebraMap ℚ A (2 * r * s * c0) := by
  intro A α
  have hα' : (α : A) ^ 4 = algebraMap ℚ A c0 := by
    simpa [A, α] using hα
  simpa using beta_sq_eq_generic (A := A) α c0 r s hα'

private lemma beta_pow4_eq {d : ℤ} {a : ℚ} (c0 r s : ℚ)
    (hα : (AdjoinRoot.root (poly d a) : AdjoinRoot (poly d a)) ^ 4 =
      algebraMap ℚ (AdjoinRoot (poly d a)) c0) :
    let A := AdjoinRoot (poly d a)
    let α : A := AdjoinRoot.root (poly d a)
    ((r • α + s • α ^ 3 : A) ^ 4) =
      algebraMap ℚ A ((r ^ 2 + c0 * s ^ 2) ^ 2 * c0 + (2 * r * s * c0) ^ 2) +
        (2 * (r ^ 2 + c0 * s ^ 2) * (2 * r * s * c0)) • α ^ 2 := by
  intro A α
  have hα' : (α : A) ^ 4 = algebraMap ℚ A c0 := by
    simpa [A, α] using hα
  simpa using beta_pow4_eq_generic (A := A) α c0 r s hα'

set_option maxHeartbeats 3000000 in
lemma commutes_negRoot_sq_eq_one {d : ℤ} (hd : Squarefree d) {a : ℚ} (ha : a ≠ 0) :
    ∀ σ : (AdjoinRoot (poly d a) ≃ₐ[ℚ] AdjoinRoot (poly d a)),
      Commute σ (negRootAlgEquiv (d := d) (a := a) ha) → σ * σ = 1 := by
  classical
  intro σ hcomm
  let p : ℚ[X] := poly d a
  let A := AdjoinRoot p
  let α : A := AdjoinRoot.root p
  let τ : A ≃ₐ[ℚ] A := negRootAlgEquiv (d := d) (a := a) ha
  let β : A := σ α

  have hτ_root : τ α = -α := by
    simp [p, A, α, τ]
  have hτβ : τ β = -β := by
    have h := congrArg (fun e => e α) hcomm
    -- expand composition and use `τ α = -α`
    have : σ (τ α) = τ (σ α) := by simpa [AlgEquiv.mul_apply] using h
    -- rewrite the left-hand side as `-β`
    simpa [β, hτ_root] using this.symm

  have hn : p.natDegree = 4 := by
    simpa [p] using (natDegree_poly (d := d) (a := a) ha)
  have hf : p ≠ 0 := by
    simpa [p] using (poly_ne_zero (d := d) (a := a) ha)
  haveI : Nontrivial A := by
    -- `AdjoinRoot p` is nontrivial since `deg p = 4`.
    refine AdjoinRoot.nontrivial (R := ℚ) p ?_
    -- `p.degree = 4`, hence nonzero.
    rw [degree_eq_natDegree hf, hn]
    decide
  let pb : PowerBasis ℚ A := AdjoinRoot.powerBasis (K := ℚ) (f := p) hf
  have hdim : pb.dim = 4 := by
    simp [pb, AdjoinRoot.powerBasis, hn]
  let e : Fin pb.dim ≃ Fin 4 := (Fin.castOrderIso hdim).toEquiv
  let b : Basis (Fin 4) ℚ A := pb.basis.reindex e
  have hbasis : ∀ i : Fin 4, b i = α ^ (i : ℕ) := by
    intro i
    -- unfold the reindexed basis and use `basis_eq_pow`;
    -- the cast equivalence preserves the underlying natural number.
    have hi : ((e.symm i : Fin pb.dim) : ℕ) = (i : ℕ) := by
      simp [e]
    simpa [b, e, pb, α, Basis.reindex_apply, hi] using (pb.basis_eq_pow (e.symm i))

  -- Coefficients of `β` in the power basis.
  let c : Fin 4 →₀ ℚ := b.repr β
  have hβ_decomp : β = ∑ i : Fin 4, c i • b i := by
    -- avoid `simp` rewriting the goal to `True`
    change β = ∑ i : Fin 4, (b.repr β) i • b i
    exact (b.sum_repr β).symm

  have hτ_basis : ∀ i : Fin 4, τ (b i) = ((-1 : ℚ) ^ (i : ℕ)) • b i := by
    intro i
    -- Since `i : Fin 4`, we can reduce to the four cases `i = 0,1,2,3`.
    fin_cases i
    · simp [hbasis, A]
    · simp [hbasis, hτ_root, A, Algebra.smul_def]
    · simp [hbasis, hτ_root, A, Algebra.smul_def, pow_two]
    · simp [hbasis, hτ_root, A, Algebra.smul_def, pow_succ, mul_assoc]

  -- `τ β = -β` forces the `1` and `α^2` coefficients to vanish, so `β = r•α + s•α^3`.
  have hc0 : c 0 = 0 := by
    -- compute the `0`-th coordinate of `τ β = -β`
    have h0 := congrArg (fun z => b.coord (0 : Fin 4) z) hτβ
    have h0' : (b.coord (0 : Fin 4)) (τ β) = (b.coord (0 : Fin 4)) (-β) := by
      simpa using h0
    have hβ' : τ β = ∑ i : Fin 4, c i • τ (b i) := by
      calc
        τ β = τ (∑ i : Fin 4, c i • b i) := by simp [hβ_decomp]
        _ = ∑ i : Fin 4, τ (c i • b i) := by simp [map_sum]
        _ = ∑ i : Fin 4, c i • τ (b i) := by
          simp
    have hcoord_left : b.coord (0 : Fin 4) (τ β) = c 0 := by
      have hβ4 : τ β = c 0 • τ (b 0) + c 1 • τ (b 1) + c 2 • τ (b 2) + c 3 • τ (b 3) := by
        simpa [Fin.sum_univ_four, add_assoc] using hβ'
      have hτb0 : τ (b 0) = b 0 := by simpa using (hτ_basis 0)
      have hτb1 : τ (b 1) = -b 1 := by simpa using (hτ_basis 1)
      have hτb2 : τ (b 2) = b 2 := by simpa using (hτ_basis 2)
      have hτb3 : τ (b 3) = -b 3 := by
        have h := hτ_basis (3 : Fin 4)
        norm_num at h
        simpa [Algebra.smul_def] using h
      -- now the `0`-th coordinate only sees the `b 0` term
      -- (all other basis vectors have `0`-th coordinate `0`)
      rw [hβ4, hτb0, hτb1, hτb2, hτb3]
      have hb00 : b.coord (0 : Fin 4) (b 0) = (1 : ℚ) := by simp
      have hb01 : b.coord (0 : Fin 4) (b 1) = (0 : ℚ) := by simp
      have hb02 : b.coord (0 : Fin 4) (b 2) = (0 : ℚ) := by simp
      have hb03 : b.coord (0 : Fin 4) (b 3) = (0 : ℚ) := by simp
      -- now compute using linearity of `b.coord 0`
      simp
    have hcoord_right : b.coord (0 : Fin 4) (-β) = -c 0 := by
      simp [c]
    have h0'' := h0'
    -- rewrite both sides using the computed coordinates
    rw [hcoord_left] at h0''
    rw [hcoord_right] at h0''
    have : c 0 = -c 0 := h0''
    linarith
  have hc2 : c 2 = 0 := by
    have h2 := congrArg (fun z => b.coord (2 : Fin 4) z) hτβ
    have h2' : (b.coord (2 : Fin 4)) (τ β) = (b.coord (2 : Fin 4)) (-β) := by
      simpa using h2
    have hβ' : τ β = ∑ i : Fin 4, c i • τ (b i) := by
      calc
        τ β = τ (∑ i : Fin 4, c i • b i) := by simp [hβ_decomp]
        _ = ∑ i : Fin 4, τ (c i • b i) := by simp [map_sum]
        _ = ∑ i : Fin 4, c i • τ (b i) := by
          simp
    have hcoord_left : b.coord (2 : Fin 4) (τ β) = c 2 := by
      have hβ4 : τ β = c 0 • τ (b 0) + c 1 • τ (b 1) + c 2 • τ (b 2) + c 3 • τ (b 3) := by
        simpa [Fin.sum_univ_four, add_assoc] using hβ'
      have hτb0 : τ (b 0) = b 0 := by simpa using (hτ_basis 0)
      have hτb1 : τ (b 1) = -b 1 := by simpa using (hτ_basis 1)
      have hτb2 : τ (b 2) = b 2 := by simpa using (hτ_basis 2)
      have hτb3 : τ (b 3) = -b 3 := by
        have h := hτ_basis (3 : Fin 4)
        norm_num at h
        simpa [Algebra.smul_def] using h
      -- now the `2`-th coordinate only sees the `b 2` term
      rw [hβ4, hτb0, hτb1, hτb2, hτb3]
      have hb20 : b.coord (2 : Fin 4) (b 0) = (0 : ℚ) := by simp
      have hb21 : b.coord (2 : Fin 4) (b 1) = (0 : ℚ) := by simp
      have hb22 : b.coord (2 : Fin 4) (b 2) = (1 : ℚ) := by simp
      have hb23 : b.coord (2 : Fin 4) (b 3) = (0 : ℚ) := by simp
      simp
    have hcoord_right : b.coord (2 : Fin 4) (-β) = -c 2 := by
      simp [c]
    have h2'' := h2'
    rw [hcoord_left] at h2''
    rw [hcoord_right] at h2''
    have : c 2 = -c 2 := h2''
    linarith

  let r : ℚ := c 1
  let s : ℚ := c 3
  have hβrs : β = r • α + s • α ^ 3 := by
    have hβ_decomp4 := hβ_decomp
    -- expand the `Fin 4` sum explicitly
    rw [Fin.sum_univ_four] at hβ_decomp4
    have h := hβ_decomp4
    rw [hc0, hc2] at h
    -- first remove the `0`-terms, to avoid rewriting `b 0` and `b 2`.
    rw [zero_smul] at h
    rw [zero_smul] at h
    rw [zero_add] at h
    rw [add_zero] at h
    -- rewrite `b 1` and `b 3` to powers of `α`.
    rw [hbasis 1, hbasis 3] at h
    -- simplify the coercions `(1 : Fin 4 : ℕ)` and `(3 : Fin 4 : ℕ)` before using `pow_one`.
    have h1 : ((1 : Fin 4) : ℕ) = 1 := by decide
    have h3 : ((3 : Fin 4) : ℕ) = 3 := by decide
    rw [h1, h3] at h
    rw [pow_one] at h
    simpa [r, s] using h

  -- Relation `α^4 = a^2*d`, and its transport along `σ`.
  have hα4 : α ^ 4 = algebraMap ℚ A (a ^ 2 * (d : ℚ)) := by
    simpa [p, A, α] using (root_pow4_eq_scalar (d := d) (a := a) ha)
  have hβ4 : β ^ 4 = α ^ 4 := by
    calc
      β ^ 4 = (σ α) ^ 4 := rfl
      _ = σ (α ^ 4) := by simp [map_pow]
      _ = σ (algebraMap ℚ A (a ^ 2 * (d : ℚ))) := by simp [hα4]
      _ = algebraMap ℚ A (a ^ 2 * (d : ℚ)) := by
        -- `σ` fixes the image of the base field.
        exact σ.commutes (a ^ 2 * (d : ℚ))
      _ = α ^ 4 := by simp [hα4]

  have hd0 : (d : ℚ) ≠ 0 := by
    exact_mod_cast hd.ne_zero
  have hc0' : (a ^ 2 * (d : ℚ)) ≠ 0 := mul_ne_zero (pow_ne_zero 2 ha) hd0

  -- Compute `β^4` explicitly from `β = r•α + s•α^3`, then compare the `α^2` coefficient.
  have hβ4_exp :
      β ^ 4 =
        algebraMap ℚ A ((r ^ 2 + (a ^ 2 * (d : ℚ)) * s ^ 2) ^ 2 * (a ^ 2 * (d : ℚ)) +
          (2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2) +
          (2 * (r ^ 2 + (a ^ 2 * (d : ℚ)) * s ^ 2) * (2 * r * s * (a ^ 2 * (d : ℚ)))) • α ^ 2 := by
    have :=
      beta_pow4_eq (d := d) (a := a) (c0 := (a ^ 2 * (d : ℚ))) r s (by simpa [p, A, α] using hα4)
    simpa [β, hβrs, p, A, α] using this

  have hcoeff2 :
      2 * (r ^ 2 + (a ^ 2 * (d : ℚ)) * s ^ 2) * (2 * r * s * (a ^ 2 * (d : ℚ))) = 0 := by
    have hb0 : (b (0 : Fin 4) : A) = 1 := by simpa using (hbasis 0)
    have hb2 : (α ^ (2 : ℕ) : A) = b (2 : Fin 4) := by simpa using (hbasis 2).symm
    have hEq :
        (algebraMap ℚ A ((r ^ 2 + a ^ 2 * (d : ℚ) * s ^ 2) ^ 2 * (a ^ 2 * (d : ℚ)) +
              (2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2) +
            (2 * (r ^ 2 + a ^ 2 * (d : ℚ) * s ^ 2) * (2 * r * s * (a ^ 2 * (d : ℚ)))) • α ^ 2) =
          α ^ 4 := by
      simpa [hβ4_exp] using (hβ4_exp.symm.trans hβ4)
    have h := congrArg (b.coord (2 : Fin 4)) hEq
    -- coordinate `2` reads off the `α^2` coefficient
    set v : ℚ :=
        2 * (r ^ 2 + a ^ 2 * (d : ℚ) * s ^ 2) * (2 * r * s * (a ^ 2 * (d : ℚ))) with hv
    have hα2 : b.coord (2 : Fin 4) (α ^ (2 : ℕ)) = (1 : ℚ) := by
      -- `b 2 = α^2`
      simp [hb2]
    have hcoord_algebraMap : ∀ t : ℚ, b.coord (2 : Fin 4) (algebraMap ℚ A t) = (0 : ℚ) := by
      intro t
      -- `algebraMap` lands in the span of `1 = b 0`, so the `b 2`-coordinate is `0`.
      have hb0' : (1 : A) = b (0 : Fin 4) := hb0.symm
      calc
        b.coord (2 : Fin 4) (algebraMap ℚ A t)
            = b.coord (2 : Fin 4) (t • (1 : A)) := by
              have ht : (t • (1 : A) : A) = algebraMap ℚ A t := by
                simp [Algebra.smul_def]
              simpa using congrArg (b.coord (2 : Fin 4)) ht.symm
        _ = b.coord (2 : Fin 4) (t • b (0 : Fin 4)) := by simp [hb0']
        _ = t • b.coord (2 : Fin 4) (b (0 : Fin 4)) := by
              simp
        _ = 0 := by simp
    have hcoord_right : b.coord (2 : Fin 4) (α ^ 4) = 0 := by
      -- `α^4` is a scalar, hence has zero `b 2`-coordinate.
      calc
        b.coord (2 : Fin 4) (α ^ 4) = b.coord (2 : Fin 4) (algebraMap ℚ A (a ^ 2 * (d : ℚ))) := by
          simp [hα4]
        _ = 0 := hcoord_algebraMap (a ^ 2 * (d : ℚ))
    have hcoord_left :
        b.coord (2 : Fin 4)
            (algebraMap ℚ A
                ((r ^ 2 + a ^ 2 * (d : ℚ) * s ^ 2) ^ 2 * (a ^ 2 * (d : ℚ)) +
                  (2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2) +
              v • α ^ 2) = v := by
      -- linearity + `b 2 = α^2`
      have : b.coord (2 : Fin 4) (v • (α ^ (2 : ℕ))) = (v : ℚ) := by
        calc
          b.coord (2 : Fin 4) (v • (α ^ (2 : ℕ))) = v • b.coord (2 : Fin 4) (α ^ (2 : ℕ)) := by
            simp
          _ = v := by simp [hα2]
      calc
        b.coord (2 : Fin 4)
            (algebraMap ℚ A
                ((r ^ 2 + a ^ 2 * (d : ℚ) * s ^ 2) ^ 2 * (a ^ 2 * (d : ℚ)) +
                  (2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2) +
              v • α ^ 2)
            =
            b.coord (2 : Fin 4)
                (algebraMap ℚ A
                    ((r ^ 2 + a ^ 2 * (d : ℚ) * s ^ 2) ^ 2 * (a ^ 2 * (d : ℚ)) +
                      (2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2)) +
              b.coord (2 : Fin 4) (v • α ^ 2) := by
                simp
        _ = 0 + b.coord (2 : Fin 4) (v • α ^ 2) := by
              -- the scalar term has zero `b 2`-coordinate
              rw [hcoord_algebraMap]
        _ = b.coord (2 : Fin 4) (v • α ^ 2) := by simp
        _ = v := by
              -- `α ^ 2` is definitionaly `α ^ (2 : ℕ)`.
              simpa using this
    have hv0 : v = 0 := by
      -- rewrite the equality of coordinates using the computed left/right sides
      have h' := h
      -- now read off `v` from the left-hand side and `0` from the right-hand side
      rw [hcoord_left] at h'
      rw [hcoord_right] at h'
      exact h'
    -- unfold `v`
    simpa [hv] using hv0

  have hprod :
      (r ^ 2 + (a ^ 2 * (d : ℚ)) * s ^ 2) * (2 * r * s * (a ^ 2 * (d : ℚ))) = 0 := by
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp (by simpa [mul_assoc] using hcoeff2)).resolve_left h2

  -- Show the first factor is nonzero; otherwise `β = 0`, contradicting `α ≠ 0`.
  have hu_ne : (r ^ 2 + (a ^ 2 * (d : ℚ)) * s ^ 2) ≠ 0 := by
    intro hu
    -- under `hu`, the explicit formula for `β^4` collapses to a pure scalar, so we can compare
    -- it with `β^4 = α^4 = c0`.
    have hβ4_v2 :
        β ^ 4 = algebraMap ℚ A ((2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2) := by
      simpa [hu] using hβ4_exp
    have hEq :
        algebraMap ℚ A ((2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2) =
          algebraMap ℚ A (a ^ 2 * (d : ℚ)) := by
      simpa [hβ4_v2] using (hβ4.trans hα4)
    have hinj : Function.Injective (algebraMap ℚ A) :=
      Module.Basis.algebraMap_injective (b := b)
    have hv2 :
        (2 * r * s * (a ^ 2 * (d : ℚ))) ^ 2 = (a ^ 2 * (d : ℚ)) := hinj hEq
    have hc0_nonneg : 0 ≤ (a ^ 2 * (d : ℚ)) := by
      -- rewrite `0 ≤ (2*r*s*c0)^2` as `0 ≤ c0` using `hv2`
      simpa using (hv2 ▸ sq_nonneg (2 * r * s * (a ^ 2 * (d : ℚ))))
    have hr0 : r = 0 := by
      have hr2 : r ^ 2 = 0 := by
        have hs2 : 0 ≤ (a ^ 2 * (d : ℚ)) * s ^ 2 := mul_nonneg hc0_nonneg (sq_nonneg s)
        have hr2' : 0 ≤ r ^ 2 := sq_nonneg r
        have : r ^ 2 + (a ^ 2 * (d : ℚ)) * s ^ 2 = 0 := by simp [hu]
        exact (add_eq_zero_iff_of_nonneg hr2' hs2).1 this |>.1
      simpa using (sq_eq_zero_iff.mp hr2)
    have hs0 : s = 0 := by
      have : (a ^ 2 * (d : ℚ)) * s ^ 2 = 0 := by
        simpa [hr0, hu] using hu
      have : s ^ 2 = 0 := (mul_eq_zero.mp this).resolve_left hc0'
      simpa using (sq_eq_zero_iff.mp this)
    have hβ0 : (β : A) = 0 := by
      simp [β, hβrs, hr0, hs0, r, s]
    have hα0 : α = 0 := by
      simpa [β] using congrArg σ.symm hβ0
    have : (a ^ 2 * (d : ℚ)) = 0 := by
      -- from `α=0`, the relation `α^4 = c0` forces `c0=0`
      have : (algebraMap ℚ A) (a ^ 2 * (d : ℚ)) = 0 := by simpa [hα0] using hα4.symm
      have hinj : Function.Injective (algebraMap ℚ A) :=
        Module.Basis.algebraMap_injective (b := b)
      have : (algebraMap ℚ A) (a ^ 2 * (d : ℚ)) = algebraMap ℚ A 0 := by simpa using this
      exact hinj this
    exact hc0' this

  have hv_zero : (2 * r * s * (a ^ 2 * (d : ℚ))) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hu_ne
  have hrs : r = 0 ∨ s = 0 := by
    have h2 : (2 : ℚ) ≠ 0 := by norm_num
    have h2c0 : (2 * (a ^ 2 * (d : ℚ))) ≠ 0 := mul_ne_zero h2 hc0'
    have : (2 * (a ^ 2 * (d : ℚ))) * (r * s) = 0 := by
      -- just reassociate/commute in the commutative monoid `ℚ`.
      calc
        (2 * (a ^ 2 * (d : ℚ))) * (r * s) = 2 * r * s * (a ^ 2 * (d : ℚ)) := by
          ac_rfl
        _ = 0 := hv_zero
    exact (mul_eq_zero.mp this).resolve_left h2c0 |> mul_eq_zero.mp

  have hsq_root : (σ * σ) α = α := by
    rcases hrs with hr0 | hs0
    · -- `r = 0`
      set c0 : ℚ := a ^ 2 * (d : ℚ)
      have hc0 : c0 ≠ 0 := hc0'
      have hβs : β = s • α ^ 3 := by
        have : β = (0 : ℚ) • α + s • α ^ 3 := by simpa [r, hr0] using hβrs
        simpa using this
      -- From `β^4 = α^4`, we obtain `s^4 * c0^2 = 1`.
      have hs4 : s ^ 4 * c0 ^ 2 = 1 := by
        have hβ4' : β ^ 4 = algebraMap ℚ A c0 := by
          simpa [c0, hα4] using (hβ4.trans hα4)
        have hβ4'' : β ^ 4 = algebraMap ℚ A (s ^ 4 * c0 ^ 3) := by
          calc
            β ^ 4 = (s • α ^ 3) ^ 4 := by simp [hβs]
            _ = (s ^ 4) • (α ^ 3) ^ 4 := by simpa using (smul_pow s (α ^ 3) 4)
            _ = (s ^ 4) • α ^ 12 := by
              have hpow : (α ^ 3 : A) ^ 4 = α ^ 12 := by
                simpa using (pow_mul α 3 4).symm
              simp [hpow]
            _ = (s ^ 4) • (α ^ 4) ^ 3 := by
              -- `12 = 4 * 3`
              simpa using congrArg (fun t : A => (s ^ 4) • t) (pow_mul α 4 3)
            _ = (s ^ 4) • (algebraMap ℚ A c0) ^ 3 := by simp [c0, hα4]
            _ = (s ^ 4) • algebraMap ℚ A (c0 ^ 3) := by
              simp
            _ = algebraMap ℚ A (s ^ 4) * algebraMap ℚ A (c0 ^ 3) := by simp [Algebra.smul_def]
            _ = algebraMap ℚ A (s ^ 4 * c0 ^ 3) := by simp [map_mul]
        have hEq : algebraMap ℚ A (s ^ 4 * c0 ^ 3) = algebraMap ℚ A c0 :=
          (hβ4''.symm.trans hβ4')
        have hinj : Function.Injective (algebraMap ℚ A) :=
          Module.Basis.algebraMap_injective (b := b)
        have hEq' : s ^ 4 * c0 ^ 3 = c0 := hinj hEq
        -- cancel one `c0` and use `c0 ^ 3 * c0⁻¹ = c0 ^ 2`
        have hEq'' : s ^ 4 * c0 ^ 3 * c0⁻¹ = c0 * c0⁻¹ := by
          simpa [mul_assoc] using congrArg (fun t : ℚ => t * c0⁻¹) hEq'
        have hc0inv : c0 * c0⁻¹ = (1 : ℚ) := by simp [hc0]
        have hc0pow : c0 ^ 3 * c0⁻¹ = c0 ^ 2 := by
          calc
            c0 ^ 3 * c0⁻¹ = (c0 ^ 2 * c0) * c0⁻¹ := by
              simp [pow_succ, mul_assoc]
            _ = c0 ^ 2 * (c0 * c0⁻¹) := by simp [mul_assoc]
            _ = c0 ^ 2 := by simp [hc0inv]
        have : s ^ 4 * c0 ^ 2 = 1 := by
          -- rewrite `c0 ^ 3 * c0⁻¹` as `c0 ^ 2`
          have := hEq''
          -- reassociate to expose `c0 ^ 3 * c0⁻¹`
          -- and then simplify.
          have : s ^ 4 * (c0 ^ 3 * c0⁻¹) = 1 := by
            simpa [mul_assoc, hc0inv] using this
          simpa [hc0pow, mul_assoc] using this
        exact this
      -- Now compute `σ (σ α)` from `β = s•α^3`.
      have : (σ * σ) α = (s ^ 4 * c0 ^ 2) • α := by
        -- `σ * σ` sends `α` to `σ β`.
        have hσσ : (σ * σ) α = σ β := by simp [AlgEquiv.mul_apply, β]
        -- compute `σ β` using `β = s•α^3`
        -- and reduce `β^3` using `α^4 = c0`.
        calc
          (σ * σ) α = σ β := hσσ
          _ = σ (s • α ^ 3) := by simp [hβs]
          _ = s • σ (α ^ 3) := by simp
          _ = s • (σ α) ^ 3 := by simp [map_pow]
          _ = s • β ^ 3 := by simp [β]
          _ = s • (s • α ^ 3) ^ 3 := by simp [hβs]
          _ = s • ((s ^ 3) • (α ^ 3) ^ 3) := by simpa using congrArg (fun x => s • x) (smul_pow s (α ^ 3) 3)
          _ = (s * s ^ 3) • (α ^ 3) ^ 3 := by
            simp [smul_smul]
          _ = (s ^ 4) • (α ^ 3) ^ 3 := by
            have hs : s * s ^ 3 = s ^ 4 := by
              calc
                s * s ^ 3 = s ^ 3 * s := by exact (mul_comm s (s ^ 3))
                _ = s ^ 4 := by simp [pow_succ]
            simp [hs]
          _ = (s ^ 4) • α ^ 9 := by
            have hpow : (α ^ 3 : A) ^ 3 = α ^ 9 := by
              simpa using (pow_mul α 3 3).symm
            simp [hpow]
          _ = (s ^ 4) • ((α ^ 4) ^ 2 * α) := by
            have hα9 : (α : A) ^ 9 = (α ^ 4) ^ 2 * α := by
              have h9 : 4 * 2 + 1 = 9 := by decide
              calc
                α ^ 9 = α ^ (4 * 2 + 1) := by simp [h9]
                _ = α ^ (4 * 2) * α ^ 1 := by
                  simpa using (pow_add α (4 * 2) 1)
                _ = (α ^ 4) ^ 2 * α := by
                  rw [pow_mul]
                  simp [pow_one]
            simpa using congrArg (fun t : A => (s ^ 4) • t) hα9
          _ = (s ^ 4) • ((algebraMap ℚ A c0) ^ 2 * α) := by simp [c0, hα4]
          _ = (s ^ 4) • ((algebraMap ℚ A (c0 ^ 2)) * α) := by
            simp [(algebraMap ℚ A).map_pow c0 2]
          _ = (s ^ 4 * c0 ^ 2) • α := by
            simp [Algebra.smul_def, mul_assoc, map_mul, mul_comm]
      -- Finish using `hs4`.
      rw [this, hs4]
      simp
    · -- `s = 0`
      have hβr : β = r • α := by
        simpa [hs0] using hβrs
      have hr4 : r ^ 4 = 1 := by
        set c0 : ℚ := a ^ 2 * (d : ℚ)
        have hc0 : c0 ≠ 0 := hc0'
        have hβ4' : β ^ 4 = algebraMap ℚ A c0 := by
          simpa [c0, hα4] using (hβ4.trans hα4)
        have hβ4'' : β ^ 4 = algebraMap ℚ A (r ^ 4 * c0) := by
          calc
            β ^ 4 = (r • α) ^ 4 := by simp [hβr]
            _ = (r ^ 4) • (α ^ 4) := by simpa using (smul_pow r α 4)
            _ = (r ^ 4) • (algebraMap ℚ A c0) := by simp [c0, hα4]
            _ = algebraMap ℚ A (r ^ 4) * algebraMap ℚ A c0 := by simp [Algebra.smul_def]
            _ = algebraMap ℚ A (r ^ 4 * c0) := by simp [map_mul]
        have hEq : algebraMap ℚ A (r ^ 4 * c0) = algebraMap ℚ A c0 :=
          (hβ4''.symm.trans hβ4')
        have hinj : Function.Injective (algebraMap ℚ A) :=
          Module.Basis.algebraMap_injective (b := b)
        have hEq' : r ^ 4 * c0 = c0 := hinj hEq
        have := congrArg (fun t : ℚ => t * c0⁻¹) hEq'
        simpa [mul_assoc, hc0, mul_left_comm, mul_comm] using this
      have hr2 : r ^ 2 = 1 := by
        have : (r ^ 2) ^ 2 = 1 := by
          calc
            (r ^ 2) ^ 2 = r ^ 4 := by
              simpa using (pow_mul r 2 2).symm
            _ = 1 := hr4
        have : r ^ 2 = 1 ∨ r ^ 2 = -1 := (sq_eq_one_iff).1 this
        cases this with
        | inl h => exact h
        | inr h =>
          have : (0 : ℚ) ≤ r ^ 2 := sq_nonneg r
          have : (0 : ℚ) ≤ -1 := by simpa [h] using this
          exact (show False from by linarith) |>.elim
      -- compute `(σ * σ) α` from `β = r • α`.
      have hσa : σ α = r • α := by simpa [β] using hβr
      calc
        (σ * σ) α = σ (σ α) := by simp [AlgEquiv.mul_apply]
        _ = σ (r • α) := by simp [hσa]
        _ = r • σ α := by simp
        _ = r • (r • α) := by simp [hσa]
        _ = (r ^ 2) • α := by
          -- `r • (r • α) = (r * r) • α = r^2 • α`
          simp [smul_smul, pow_two]
        _ = α := by simp [hr2]

  have h_alg :
      ((σ * σ : A ≃ₐ[ℚ] A).toAlgHom) = (1 : A ≃ₐ[ℚ] A).toAlgHom := by
    ext
    simpa [AlgEquiv.mul_apply] using hsq_root
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun f : A →ₐ[ℚ] A => f x) h_alg

end FATEH35

theorem isEmpty_adjoinRoot_zMod_four {d : ℤ} (hd : Squarefree d) {a : ℚ} (ha : a ≠ 0) :
    IsEmpty ((AdjoinRoot ((a⁻¹ • X ^ 2) ^ 2 - C (d : ℚ)) ≃ₐ[ℚ]
      AdjoinRoot ((a⁻¹ • X ^ 2) ^ 2 - C (d : ℚ))) ≃* Multiplicative (ZMod 4)) := by
  classical
  refine ⟨fun e => ?_⟩
  let p : ℚ[X] := FATEH35.poly d a
  let A := AdjoinRoot p
  have hab : ∀ x y : (A ≃ₐ[ℚ] A), x * y = y * x := by
    intro x y
    apply e.injective
    simpa using (mul_comm (e x) (e y))
  let g : (A ≃ₐ[ℚ] A) := e.symm (Multiplicative.ofAdd (1 : ZMod 4))
  have hg : orderOf g = 4 := by
    -- avoid `simpa` unfolding away the goal; `g` is definitional.
    dsimp [g]
    exact (FATEH35.pullback_has_order4 (G := (A ≃ₐ[ℚ] A)) e)
  let τ : (A ≃ₐ[ℚ] A) := FATEH35.negRootAlgEquiv (d := d) (a := a) ha
  have hcomm : Commute g τ := hab g τ
  have hsquare : g * g = 1 := by
    exact FATEH35.commutes_negRoot_sq_eq_one (d := d) hd (a := a) ha g hcomm
  -- contradiction: an element of order `4` cannot have square `1`
  have : orderOf g ≤ 2 := by
    have : g ^ 2 = 1 := by simpa [pow_two] using hsquare
    exact orderOf_le_of_pow_eq_one (by decide : 0 < (2 : ℕ)) this
  have : (4 : ℕ) ≤ 2 := by
    rw [← hg]
    exact this
  exact (Nat.not_succ_le_self 3) (by
    exact le_trans this (by decide : (2 : ℕ) ≤ 3))

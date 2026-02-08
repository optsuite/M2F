import Mathlib

open Matrix
open scoped BigOperators

namespace SylowGL2

variable {K : Type*} [Field K] [DecidableEq K]

/-- The subgroup of `GL₂(K)` consisting of matrices `[[1, x], [0, 1]]`. -/
def unipotentUpper : Subgroup (GL (Fin 2) K) :=
  (Matrix.GeneralLinearGroup.upperRightHom (R := K)).toMonoidHom.range

/-- A diagonal matrix `diag(a, d)` as an element of `GL₂(K)` with explicit inverse. -/
def diagGL (a d : K) (ha : a ≠ 0) (hd : d ≠ 0) : GL (Fin 2) K :=
  ⟨!![a, 0; 0, d], !![a⁻¹, 0; 0, d⁻¹], by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd],
  by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ha, hd]⟩

omit [DecidableEq K] in
/-- Conjugation of `upperRightHom x` by a diagonal matrix stays in `upperRightHom`. -/
lemma diagGL_conj_upperRightHom (a d : K) (ha : a ≠ 0) (hd : d ≠ 0) (x : K) :
    diagGL (K := K) a d ha hd * Matrix.GeneralLinearGroup.upperRightHom (R := K) x *
        (diagGL (K := K) a d ha hd)⁻¹
      = Matrix.GeneralLinearGroup.upperRightHom (R := K) ((a / d) * x) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diagGL, Matrix.GeneralLinearGroup.upperRightHom, Matrix.mul_apply, Fin.sum_univ_two,
      ha, hd, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm]

/-- `upperRightHom 1` acts on the finite part of `OnePoint K` by translation. -/
lemma upperRightHom_one_smul_coe (k : K) :
    (Matrix.GeneralLinearGroup.upperRightHom (R := K) (1 : K)) • (k : OnePoint K) =
      ((k + 1 : K) : OnePoint K) := by
  simp [OnePoint.smul_some_eq_ite, div_eq_inv_mul]

/-- The orbit of `∞` under the action of `GL₂(K)` on `OnePoint K` is all of `OnePoint K`. -/
lemma orbit_infty_eq_top :
    MulAction.orbit (GL (Fin 2) K) (OnePoint.infty : OnePoint K) = ⊤ := by
  ext c
  constructor
  · intro _; trivial
  · intro _
    cases c with
    | infty =>
        refine ⟨1, by simp⟩
    | coe k =>
        let gk : GL (Fin 2) K :=
          ⟨!![k, 1; 1, 0], !![0, 1; 1, -k], by simp [one_fin_two], by simp [one_fin_two]⟩
        refine ⟨gk, ?_⟩
        simp [gk, OnePoint.smul_infty_eq_ite]

/-- The normalizer of `unipotentUpper` is the stabilizer of `∞` in the action on `OnePoint K`. -/
lemma normalizer_unipotentUpper_eq_stabilizer_infty :
    (unipotentUpper (K := K)).normalizer =
      MulAction.stabilizer (GL (Fin 2) K) (OnePoint.infty : OnePoint K) := by
  classical
  let U : Subgroup (GL (Fin 2) K) := unipotentUpper (K := K)
  have hU_fix_infty (u : GL (Fin 2) K) (hu : u ∈ U) :
      u • (OnePoint.infty : OnePoint K) = OnePoint.infty := by
    rcases hu with ⟨x, rfl⟩
    exact
      (OnePoint.smul_infty_eq_self_iff (g := Matrix.GeneralLinearGroup.upperRightHom (R := K) x)).2
        (by simp)

  -- `upperRightHom 1` fixes only `∞`.
  have upperRightHom_one_fixed_iff (c : OnePoint K) :
      (Matrix.GeneralLinearGroup.upperRightHom (R := K) (1 : K)) • c = c ↔
        c = (OnePoint.infty : OnePoint K) := by
    cases c with
    | infty =>
        -- `upperRightHom 1` is upper triangular, so it fixes `∞`.
        simp [OnePoint.smul_infty_eq_self_iff]
    | coe k =>
        constructor
        · intro h
          have h' : ((k + 1 : K) : OnePoint K) = (k : OnePoint K) := by
            -- Avoid `simp` turning this into `False`; we only rewrite the action.
            have h' := h
            rw [upperRightHom_one_smul_coe (K := K) k] at h'
            exact h'
          have hk : (k + 1 : K) = k := by
            exact (OnePoint.some_eq_iff (k + 1) k).1 h'
          have : (1 : K) = 0 := by
            have hk' : k + (1 : K) = k + 0 := by
              calc
                k + (1 : K) = k := hk
                _ = k + 0 := by simp
            exact add_left_cancel hk'
          exact (one_ne_zero this).elim
        · intro hk
          exact False.elim ((OnePoint.coe_ne_infty k) hk)

  -- First inclusion: normalizer ⊆ stabilizer.
  have hN_le :
      U.normalizer ≤ MulAction.stabilizer (GL (Fin 2) K) (OnePoint.infty : OnePoint K) := by
    intro g hg
    have hu1 : Matrix.GeneralLinearGroup.upperRightHom (R := K) (1 : K) ∈ U := by
      refine ⟨Multiplicative.ofAdd (1 : K), rfl⟩
    have hu1_conj : g * Matrix.GeneralLinearGroup.upperRightHom (R := K) (1 : K) * g⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hg _).1 hu1
    have hfix :
        (g * Matrix.GeneralLinearGroup.upperRightHom (R := K) (1 : K) * g⁻¹) •
            (OnePoint.infty : OnePoint K) = OnePoint.infty :=
      hU_fix_infty _ hu1_conj
    have hu1_fixes : Matrix.GeneralLinearGroup.upperRightHom (R := K) (1 : K) •
        (g⁻¹ • (OnePoint.infty : OnePoint K)) = g⁻¹ • (OnePoint.infty : OnePoint K) := by
      have := congrArg (fun t => g⁻¹ • t) hfix
      simpa [smul_smul, mul_assoc] using this
    have : g⁻¹ • (OnePoint.infty : OnePoint K) = OnePoint.infty := by
      have :=
        (upperRightHom_one_fixed_iff (c := g⁻¹ • (OnePoint.infty : OnePoint K))).1 hu1_fixes
      simpa using this
    have : g • (OnePoint.infty : OnePoint K) = OnePoint.infty := by
      simpa [smul_smul] using (congrArg (fun t => g • t) this).symm
    simpa [MulAction.mem_stabilizer_iff] using this

  -- Second inclusion: stabilizer ⊆ normalizer.
  have hStab_le :
      MulAction.stabilizer (GL (Fin 2) K) (OnePoint.infty : OnePoint K) ≤ U.normalizer := by
    intro g hg
    have hgfix : g • (OnePoint.infty : OnePoint K) = OnePoint.infty := by
      simpa [MulAction.mem_stabilizer_iff] using hg
    have hg10 : g 1 0 = 0 := (OnePoint.smul_infty_eq_self_iff (g := g)).1 hgfix
    have hdet : Matrix.det (g : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
      simpa using g.det_ne_zero
    have hprod : g 0 0 * g 1 1 ≠ 0 := by
      simpa [det_fin_two, hg10] using hdet
    have hg00 : g 0 0 ≠ 0 := by
      intro h; exact hprod (by simp [h])
    have hg11 : g 1 1 ≠ 0 := by
      intro h; exact hprod (by simp [h])

    -- Decompose `g` into diagonal part times translation part.
    let D : GL (Fin 2) K := diagGL (K := K) (g 0 0) (g 1 1) hg00 hg11
    let t : K := (g 0 0)⁻¹ * g 0 1
    let T : GL (Fin 2) K := Matrix.GeneralLinearGroup.upperRightHom (R := K) t
    have hDecomp : g = D * T := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [D, T, t, diagGL, Matrix.mul_apply,
          Fin.sum_univ_two, hg10, hg00, mul_comm]

    -- The diagonal part normalizes `U` by the explicit conjugation formula.
    have hD : D ∈ U.normalizer := by
      refine (Subgroup.mem_normalizer_iff (H := U) (g := D)).2 ?_
      intro h
      constructor
      · intro hh
        rcases hh with ⟨x, rfl⟩
        let xK : K := Multiplicative.toAdd x
        refine ⟨Multiplicative.ofAdd (((g 0 0) / (g 1 1)) * xK), ?_⟩
        -- The conjugate is again in the range, with scaled parameter.
        simpa [xK, D, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm] using
          (diagGL_conj_upperRightHom (K := K) (g 0 0) (g 1 1) hg00 hg11 xK).symm
      · intro hh
        rcases hh with ⟨x, hx⟩
        let xK : K := Multiplicative.toAdd x
        have hx' :
            Matrix.GeneralLinearGroup.upperRightHom (R := K) xK = D * h * D⁻¹ := by
          simpa [xK] using hx
        have hx_h : D⁻¹ * Matrix.GeneralLinearGroup.upperRightHom (R := K) xK * D = h := by
          calc
            D⁻¹ * Matrix.GeneralLinearGroup.upperRightHom (R := K) xK * D =
                D⁻¹ * (D * h * D⁻¹) * D := by simp [hx', mul_assoc]
            _ = h := by simp [mul_assoc]
        -- Use the conjugation formula again, in the reverse direction.
        let y : K := ((g 1 1) / (g 0 0)) * xK
        have hxy' :=
          diagGL_conj_upperRightHom (K := K) (g 0 0) (g 1 1) hg00 hg11 y
        have hyparam : ((g 0 0) / (g 1 1)) * y = xK := by
          -- `(g00/g11) * ((g11/g00) * xK) = xK`.
          simp [y, xK, div_eq_inv_mul, mul_assoc, mul_left_comm, mul_comm, hg00, hg11]
        have hxy :
            D * Matrix.GeneralLinearGroup.upperRightHom (R := K) y * D⁻¹ =
              Matrix.GeneralLinearGroup.upperRightHom (R := K) xK := by
          simpa [D, hyparam] using hxy'
        have hy :
            D⁻¹ * Matrix.GeneralLinearGroup.upperRightHom (R := K) xK * D =
              Matrix.GeneralLinearGroup.upperRightHom (R := K) y := by
          have := congrArg (fun z => D⁻¹ * z * D) hxy
          simpa [mul_assoc] using this.symm
        -- Now `h = upperRightHom y`, so it lies in the range.
        refine ⟨Multiplicative.ofAdd y, ?_⟩
        -- `toMonoidHom (ofAdd y) = upperRightHom y`.
        have hyh : Matrix.GeneralLinearGroup.upperRightHom (R := K) y = h :=
          hy.symm.trans hx_h
        simpa using hyh

    -- The translation part lies in `U`, hence in the normalizer.
    have hT : T ∈ U.normalizer := by
      have hTmem : T ∈ U := by
        refine ⟨Multiplicative.ofAdd t, rfl⟩
      exact (Subgroup.le_normalizer (H := U)) hTmem

    have : D * T ∈ U.normalizer := U.normalizer.mul_mem hD hT
    simpa [hDecomp] using this

  -- Combine inclusions.
  ext g
  constructor
  · intro hg; exact hN_le hg
  · intro hg; exact hStab_le hg

end SylowGL2

/-- Prove that the number of Sylow $p$-subgroups of $\operatorname{GL}_2(\mathbb{F}_p)$ is $p + 1$.
-/
theorem card_sylow_gl_two_eq_add_one (p : ℕ) [Fact p.Prime] :
    Nat.card (Sylow p <| GL (Fin 2) (ZMod p)) = p + 1 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  let G := GL (Fin 2) (ZMod p)
  let U : Subgroup G := SylowGL2.unipotentUpper (K := ZMod p)

  -- `U` has cardinality `p` (it is the range of an injective character of the additive group).
  have card_U : Nat.card U = p := by
    have hinj :
        Function.Injective (Matrix.GeneralLinearGroup.upperRightHom (R := ZMod p)).toMonoidHom := by
      intro a b hab
      exact (Matrix.GeneralLinearGroup.injective_upperRightHom (R := ZMod p)) (by simpa using hab)
    -- `ofInjective` identifies the range with its domain.
    calc
      Nat.card U = Nat.card (Multiplicative (ZMod p)) := by
        simpa [U, SylowGL2.unipotentUpper] using
          (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm)
      _ = Nat.card (ZMod p) := rfl
      _ = p := by simp

  have card_U_f : Fintype.card U = p := by
    simpa [Nat.card_eq_fintype_card] using card_U

  -- `|GL₂(Fₚ)| = (p^2 - 1) * (p^2 - p)`.
  have card_G : Nat.card G = (p ^ 2 - 1) * (p ^ 2 - p) := by
    simpa [G, ZMod.card, Fin.prod_univ_two, pow_zero, pow_one] using
      (Matrix.card_GL_field (n := 2) (𝔽 := ZMod p))
  have card_G_f : Fintype.card G = (p ^ 2 - 1) * (p ^ 2 - p) := by
    simpa [Nat.card_eq_fintype_card] using card_G

  -- Compute `U.index`.
  have index_U : U.index = (p ^ 2 - 1) * (p - 1) := by
    have hmul : Fintype.card U * U.index = Fintype.card G := by
      simpa [Nat.card_eq_fintype_card] using (Subgroup.card_mul_index (H := U) (G := G))
    have : p * U.index = (p ^ 2 - 1) * (p ^ 2 - p) := by
      simpa [card_U_f, card_G_f] using hmul
    have hp0 : 0 < p := (Fact.out : Nat.Prime p).pos
    have hsub : p ^ 2 - p = p * (p - 1) := by
      simpa [pow_two] using (Nat.mul_sub_left_distrib p p 1).symm
    have : p * U.index = p * ((p ^ 2 - 1) * (p - 1)) := by
      simpa [hsub, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using this
    exact Nat.mul_left_cancel hp0 this

  have not_dvd_index_U : ¬ p ∣ U.index := by
    have hp : Nat.Prime p := Fact.out
    -- `p ∤ p^2 - 1`.
    have hp_not_dvd_sq_sub_one : ¬ p ∣ p ^ 2 - 1 := by
      intro h
      have hp_dvd_sq : p ∣ p ^ 2 := by
        rw [pow_two]
        exact Nat.dvd_mul_right p p
      have : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub hp_dvd_sq h
      have hle : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
      have : p ∣ 1 := by
        simpa [Nat.sub_sub_self hle] using this
      exact hp.not_dvd_one this
    -- `p ∤ p - 1`.
    have hp_not_dvd_sub_one : ¬ p ∣ p - 1 := by
      intro h
      have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
      have hle : p ≤ p - 1 := Nat.le_of_dvd hpos h
      exact (Nat.not_lt_of_ge hle) (Nat.sub_lt hp.pos (Nat.succ_pos 0))
    intro h
    have : p ∣ p ^ 2 - 1 ∨ p ∣ p - 1 := by
      have hmul : p ∣ (p ^ 2 - 1) * (p - 1) := by simpa [index_U] using h
      exact (Nat.Prime.dvd_mul hp).1 hmul
    exact this.elim hp_not_dvd_sq_sub_one hp_not_dvd_sub_one

  -- Build a Sylow `p`-subgroup from `U`.
  have hU : IsPGroup p U :=
      IsPGroup.of_card (p := p) (G := (↥U)) (n := 1) (by simpa [pow_one] using card_U)
  let P : Sylow p G := hU.toSylow not_dvd_index_U

  -- Identify the normalizer of `P` and compute its index.
  have hnorm :
      P.normalizer = MulAction.stabilizer G (OnePoint.infty : OnePoint (ZMod p)) := by
    have : (P : Subgroup G) = U := rfl
    simpa [this] using
      SylowGL2.normalizer_unipotentUpper_eq_stabilizer_infty (K := ZMod p)

  have hstab_index : (MulAction.stabilizer G (OnePoint.infty : OnePoint (ZMod p))).index = p + 1 := by
    have hOrbit : MulAction.orbit G (OnePoint.infty : OnePoint (ZMod p)) = ⊤ :=
      SylowGL2.orbit_infty_eq_top (K := ZMod p)
    have hIndex :
        (MulAction.stabilizer G (OnePoint.infty : OnePoint (ZMod p))).index =
          (MulAction.orbit G (OnePoint.infty : OnePoint (ZMod p))).ncard := by
      simpa using
        (MulAction.index_stabilizer (G := G) (x := (OnePoint.infty : OnePoint (ZMod p))))
    have hOrbitCard :
        (MulAction.orbit G (OnePoint.infty : OnePoint (ZMod p))).ncard = p + 1 := by
      -- The orbit is the whole space, and `OnePoint (ZMod p)` has `p + 1` elements.
      simp [hOrbit, Set.ncard_univ, OnePoint, Fintype.card_option, ZMod.card]
    exact hIndex.trans hOrbitCard

  calc
    Nat.card (Sylow p G) = P.normalizer.index := P.card_eq_index_normalizer
    _ = (MulAction.stabilizer G (OnePoint.infty : OnePoint (ZMod p))).index := by simp [hnorm]
    _ = p + 1 := hstab_index

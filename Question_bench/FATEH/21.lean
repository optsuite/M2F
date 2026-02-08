import Mathlib

/- Prove that the order of Aut(Z_3 × Z_9) is 108.-/
namespace FATEH21

open scoped BigOperators

abbrev G := ZMod 3 × ZMod 9

-- Reduction mod 3 on `ZMod 9` (a ring hom, hence also an additive hom).
noncomputable def red : ZMod 9 →+* ZMod 3 :=
  ZMod.castHom (show 3 ∣ 9 by decide) (ZMod 3)

-- Multiplication-by-3 embedding `ZMod 3 →+ ZMod 9` (image = `{0,3,6}`).
noncomputable def mulThree : ZMod 3 →+ ZMod 9 :=
  ZMod.lift 3
    ⟨(AddMonoidHom.mulLeft (3 : ZMod 9)).comp (Int.castAddHom (ZMod 9)), by
      -- `3 ↦ 3 * 3 = 9 = 0` in `ZMod 9`.
      decide
    ⟩

@[simp] lemma mulThree_intCast (k : ℤ) :
    mulThree (k : ZMod 3) = (3 : ZMod 9) * (k : ZMod 9) := by
  simpa [mulThree, AddMonoidHom.mulLeft] using
    (ZMod.lift_coe (n := 3)
      (f := ⟨(AddMonoidHom.mulLeft (3 : ZMod 9)).comp (Int.castAddHom (ZMod 9)), mulThree._proof_2⟩)
      k)

@[simp] lemma mulThree_natCast (k : ℕ) :
    mulThree (k : ZMod 3) = (3 * k : ℕ) := by
  -- Reduce to the integer statement.
  simpa [Nat.cast_mul] using (mulThree_intCast (k := (k : ℤ)))

@[simp] lemma red_mulThree (z : ZMod 3) : red (mulThree z) = 0 := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  -- Everything in the image is a multiple of `3`, hence is `0` mod `3`.
  calc
    red (mulThree (k : ZMod 3)) = red ((3 : ZMod 9) * (k : ZMod 9)) := by
      simp [mulThree_intCast]
    _ = red (3 : ZMod 9) * red (k : ZMod 9) := by
      simp [map_mul]
    _ = 0 := by
      have h3 : red (3 : ZMod 9) = 0 := by
        simp [red]
        decide
      simp [h3]

@[simp] lemma mulThree_eq_zero_iff (z : ZMod 3) : mulThree z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    -- Unfold `mulThree` on an integer representative.
    have hk9 : ((3 * k : ℤ) : ZMod 9) = 0 := by
      simpa [mulThree_intCast, Int.cast_mul, mul_assoc] using hz
    have hdiv9 : (9 : ℤ) ∣ 3 * k := (ZMod.intCast_zmod_eq_zero_iff_dvd (3 * k) 9).1 hk9
    have hdiv3 : (3 : ℤ) ∣ k := by
      have : (3 : ℤ) * 3 ∣ (3 : ℤ) * k := by
        simpa [show (9 : ℤ) = (3 : ℤ) * 3 by decide, mul_assoc] using hdiv9
      exact Int.dvd_of_mul_dvd_mul_left (by decide : (3 : ℤ) ≠ 0) this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd k 3).2 hdiv3
  · rintro rfl
    simp [mulThree]

lemma mulThree_injective : Function.Injective mulThree := by
  intro x y hxy
  have h : mulThree (x - y) = 0 := by
    simpa [map_sub] using congrArg (fun t => t - mulThree y) hxy
  have : x - y = 0 := (mulThree_eq_zero_iff (z := x - y)).1 h
  exact sub_eq_zero.mp this

-- Every element killed by `3` in `ZMod 9` is a multiple of `3`, hence lies in the image of `mulThree`.
lemma exists_mulThree_eq_of_three_nsmul_eq_zero (t : ZMod 9) (ht : (3 : ℕ) • t = 0) :
    ∃ z : ZMod 3, mulThree z = t := by
  classical
  haveI : NeZero (9 : ℕ) := ⟨by decide⟩
  -- Convert the equation to a divisibility statement about `t.val`.
  have ht' : ((3 : ZMod 9) * t) = 0 := by
    simpa [nsmul_eq_mul] using ht
  have ht'' : ((3 * t.val : ℕ) : ZMod 9) = 0 := by
    -- Rewrite `t` using its `val` representative.
    simpa [ZMod.natCast_zmod_val, Nat.cast_mul, mul_assoc] using ht'
  have hdiv9 : 9 ∣ 3 * t.val := (ZMod.natCast_eq_zero_iff (3 * t.val) 9).1 ht''
  have hdiv3 : 3 ∣ t.val := by
    have : 3 * 3 ∣ 3 * t.val := by
      simpa [Nat.mul_assoc]
        using (show 9 ∣ 3 * t.val by simpa [show 9 = 3 * 3 by decide] using hdiv9)
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).1 this
  refine ⟨(t.val / 3 : ℕ), ?_⟩
  -- Now `t.val = 3 * (t.val / 3)`, so `mulThree (t.val / 3) = t`.
  have htval : 3 * (t.val / 3) = t.val := by
    simpa using (Nat.mul_div_cancel' (n := 3) (m := t.val) hdiv3)
  -- Finish by rewriting `t` as `t.val`.
  simp [mulThree_natCast, htval]

-- Elements in the image of `mulThree` are `3`-multiples in `ZMod 9`.
lemma exists_three_nsmul_eq_mulThree (z : ZMod 3) :
    ∃ y : ZMod 9, (3 : ℕ) • y = mulThree z := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨(k : ZMod 9), ?_⟩
  simp [mulThree_intCast, nsmul_eq_mul]

-- `addOrderOf` is preserved by additive equivalences.
lemma addOrderOf_addEquiv_eq {A B : Type*} [AddMonoid A] [AddMonoid B] (e : A ≃+ B) (x : A) :
    addOrderOf (e x) = addOrderOf x := by
  simp

abbrev Params := (ZMod 3)ˣ × (ZMod 9)ˣ × ZMod 3 × ZMod 3

-- Build an automorphism from parameters:
-- `(x,y) ↦ (a*x + b*(y mod 3), 3*(c*x) + d*y)`.
noncomputable def paramsToAddAut : Params → AddAut G := by
  classical
  intro p
  rcases p with ⟨a, d, b, c⟩
  -- The forward additive map.
  let f : G →+ G :=
    { toFun := fun xy =>
        ( (a : ZMod 3) * xy.1 + b * red xy.2
        , mulThree (c * xy.1) + (d : ZMod 9) * xy.2 )
      map_zero' := by simp [red, mulThree]
      map_add' := by
        intro x y
        ext <;> simp [mul_add, add_assoc, add_comm, add_left_comm] }
  -- A candidate inverse (computed by solving the triangular system).
  let d3 : (ZMod 3)ˣ := ZMod.unitsMap (show 3 ∣ 9 by decide) d
  let g : G → G := fun xy =>
    let yRed : ZMod 3 := (d3⁻¹ : (ZMod 3)ˣ) * red xy.2
    let x : ZMod 3 := (a⁻¹ : (ZMod 3)ˣ) * (xy.1 - b * yRed)
    let y : ZMod 9 := (d⁻¹ : (ZMod 9)ˣ) * (xy.2 - mulThree (c * x))
    (x, y)
  have hg_left : Function.LeftInverse g f := by
    intro xy
    rcases xy with ⟨x, y⟩
    -- Match the internal `let`-bindings of `g (f (x,y))`.
    let yRed : ZMod 3 := (d3⁻¹ : (ZMod 3)ˣ) * red (mulThree (c * x) + (d : ZMod 9) * y)
    let x' : ZMod 3 := (a⁻¹ : (ZMod 3)ˣ) * (((a : ZMod 3) * x + b * red y) - b * yRed)
    let y' : ZMod 9 := (d⁻¹ : (ZMod 9)ˣ) *
      ((mulThree (c * x) + (d : ZMod 9) * y) - mulThree (c * x'))
    have hg_def : g (f (x, y)) = (x', y') := by
      rfl
    have hd3 : (d3 : ZMod 3) = red (d : ZMod 9) := by
      simp [d3, red, ZMod.unitsMap_val]
    have hyRed : yRed = red y := by
      have hred : red (mulThree (c * x) + (d : ZMod 9) * y) = (d3 : ZMod 3) * red y := by
        calc
          red (mulThree (c * x) + (d : ZMod 9) * y)
              = red (mulThree (c * x)) + red ((d : ZMod 9) * y) := by
                  simp [map_add]
          _ = 0 + (red (d : ZMod 9) * red y) := by
                  simp [red_mulThree, map_mul]
          _ = (d3 : ZMod 3) * red y := by
                  simp [hd3]
      calc
        yRed = (d3⁻¹ : (ZMod 3)ˣ) * ((d3 : ZMod 3) * red y) := by
          dsimp [yRed]
          rw [hred]
        _ = red y := by
          have hmul : ((d3⁻¹ : (ZMod 3)ˣ) : ZMod 3) * (d3 : ZMod 3) = 1 :=
            congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) (inv_mul_cancel d3)
          calc
            ((d3⁻¹ : (ZMod 3)ˣ) : ZMod 3) * ((d3 : ZMod 3) * red y)
                = (((d3⁻¹ : (ZMod 3)ˣ) : ZMod 3) * (d3 : ZMod 3)) * red y := by
                    exact (mul_assoc ((d3⁻¹ : (ZMod 3)ˣ) : ZMod 3) (d3 : ZMod 3) (red y)).symm
            _ = red y := by
              rw [hmul]
              exact one_mul _
    have hx' : x' = x := by
      dsimp [x']
      rw [hyRed]
      have hsub : ((a : ZMod 3) * x + b * red y) - b * red y = (a : ZMod 3) * x := by
        ring
      -- Cancel the unit `a`.
      have hmul : ((a⁻¹ : (ZMod 3)ˣ) : ZMod 3) * (a : ZMod 3) = 1 :=
        congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) (inv_mul_cancel a)
      -- Now finish by associativity.
      calc
        ((a⁻¹ : (ZMod 3)ˣ) : ZMod 3) * (((a : ZMod 3) * x + b * red y) - b * red y)
            = ((a⁻¹ : (ZMod 3)ˣ) : ZMod 3) * ((a : ZMod 3) * x) := by
                rw [hsub]
        _ = (((a⁻¹ : (ZMod 3)ˣ) : ZMod 3) * (a : ZMod 3)) * x := by
              exact (mul_assoc ((a⁻¹ : (ZMod 3)ˣ) : ZMod 3) (a : ZMod 3) x).symm
        _ = x := by
              rw [hmul]
              exact one_mul _
    have hy' : y' = y := by
      dsimp [y']
      rw [hx']
      have hsub :
          (mulThree (c * x) + (d : ZMod 9) * y) - mulThree (c * x) = (d : ZMod 9) * y := by
        ring
      have hmul : ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) * (d : ZMod 9) = 1 :=
        congrArg (fun u : (ZMod 9)ˣ => (u : ZMod 9)) (inv_mul_cancel d)
      calc
        ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) *
            ((mulThree (c * x) + (d : ZMod 9) * y) - mulThree (c * x))
            = ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) * ((d : ZMod 9) * y) := by
                rw [hsub]
        _ = (((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) * (d : ZMod 9)) * y := by
              exact (mul_assoc ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) (d : ZMod 9) y).symm
        _ = y := by
              rw [hmul]
              exact one_mul _
    simp [hg_def, hx', hy']
  have hg_right : Function.RightInverse g f := by
    intro xy
    rcases xy with ⟨x, y⟩
    -- Match the internal `let`-bindings of `g (x,y)`.
    let yRed : ZMod 3 := (d3⁻¹ : (ZMod 3)ˣ) * red y
    let x' : ZMod 3 := (a⁻¹ : (ZMod 3)ˣ) * (x - b * yRed)
    let y' : ZMod 9 := (d⁻¹ : (ZMod 9)ˣ) * (y - mulThree (c * x'))
    have hg_def : g (x, y) = (x', y') := by
      rfl
    have hredy' : red y' = yRed := by
      have hd3_inv : red ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) = (d3⁻¹ : (ZMod 3)ˣ) := by
        simp [d3, red, ZMod.unitsMap_val]
      dsimp [y', yRed]
      -- `red` is a ring hom, so distribute over `(*)` and `(-)`.
      -- The `mulThree`-term vanishes under `red`.
      calc
        red (((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) * (y - mulThree (c * x')))
            = red ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9) * (red y - red (mulThree (c * x'))) := by
                simp [map_mul, map_sub]
        _ = (d3⁻¹ : (ZMod 3)ˣ) * (red y - 0) := by
              rw [hd3_inv]
              have hsub : red y - red (mulThree (c * x')) = red y - 0 :=
                congrArg (fun t => red y - t) (red_mulThree (z := c * x'))
              rw [hsub]
        _ = (d3⁻¹ : (ZMod 3)ˣ) * red y := by
              ring
    have hf_def :
        f (x', y') =
          ( (a : ZMod 3) * x' + b * red y'
          , mulThree (c * x') + (d : ZMod 9) * y' ) := by
      rfl
    -- Now simplify the two coordinates separately.
    have hf_fst : ((f (x', y')).1 : ZMod 3) = x := by
      -- `red y'` is exactly the intermediate `yRed`.
      have ha : ((a : ZMod 3) * ((a⁻¹ : (ZMod 3)ˣ) : ZMod 3)) = 1 :=
        congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) (mul_inv_cancel a)
      have hf_fst0 : (f (x', y')).1 = (a : ZMod 3) * x' + b * red y' :=
        congrArg Prod.fst hf_def
      -- Use `hf_def` and `hredy'` to reduce to a ring identity.
      rw [hf_fst0]
      rw [hredy']
      dsimp [x']
      ring_nf
      rw [ha]
      simp
    have hf_snd : ((f (x', y')).2 : ZMod 9) = y := by
      have hd : ((d : ZMod 9) * ((d⁻¹ : (ZMod 9)ˣ) : ZMod 9)) = 1 :=
        congrArg (fun u : (ZMod 9)ˣ => (u : ZMod 9)) (mul_inv_cancel d)
      have hf_snd0 : (f (x', y')).2 = mulThree (c * x') + (d : ZMod 9) * y' :=
        congrArg Prod.snd hf_def
      rw [hf_snd0]
      dsimp [y']
      ring_nf
      rw [hd]
      simp
    have : f (g (x, y)) = (x, y) := by
      simp [hg_def, Prod.ext_iff, hf_fst, hf_snd]
    simpa using this
  exact AddEquiv.ofBijective f ⟨hg_left.injective, hg_right.surjective⟩

-- Extract parameters from an automorphism.
noncomputable def addAutToParams : AddAut G → Params := by
  classical
  intro f
  -- `a` comes from the first coordinate of `f (1,0)`;
  -- it must be nonzero because `3G` is characteristic.
  let a0 : ZMod 3 := (f (1, 0)).1
  have ha0 : a0 ≠ 0 := by
    intro ha0
    have hy0 : (3 : ℕ) • (f (1, 0)).2 = 0 := by
      -- `3 • f(1,0) = f(3 • (1,0)) = 0`.
      have h : (3 : ℕ) • (((1, 0) : G)) = 0 := by
        ext <;> decide
      have : (3 : ℕ) • (f (1, 0) : G) = 0 := by
        calc
          (3 : ℕ) • (f (1, 0) : G) = f ((3 : ℕ) • ((1, 0) : G)) := by
            simpa using (f.toAddMonoidHom.map_nsmul ((1, 0) : G) 3).symm
          _ = f 0 := by
            simpa using congrArg f h
          _ = 0 := by
            simp
      simpa using congrArg Prod.snd this
    obtain ⟨z, hz⟩ := exists_mulThree_eq_of_three_nsmul_eq_zero (t := (f (1, 0)).2) hy0
    obtain ⟨y, hy⟩ := exists_three_nsmul_eq_mulThree z
    -- If `a0 = 0`, then `f(1,0)` is a `3`-multiple, hence so is `(1,0)` by applying `f⁻¹`.
    have hmem : ∃ g : G, (3 : ℕ) • g = (f (1, 0) : G) := by
      refine ⟨(0, y), ?_⟩
      ext
      · simp [a0, ha0]
      · simpa [hz] using hy
    have : ∃ g : G, (3 : ℕ) • g = ((1, 0) : G) := by
      rcases hmem with ⟨g, hg⟩
      refine ⟨f.symm g, ?_⟩
      -- Apply `f⁻¹` to the equation `3 • g = f(1,0)`.
      have h' : f.symm ((3 : ℕ) • g) = ((1, 0) : G) := by
        simpa using congrArg f.symm hg
      calc
        (3 : ℕ) • f.symm g = f.symm ((3 : ℕ) • g) := by
          simpa using (f.symm.toAddMonoidHom.map_nsmul g 3).symm
        _ = ((1, 0) : G) := h'
    rcases this with ⟨g, hg⟩
    -- But any `3`-multiple has first component `0`.
    have hg1 : (3 : ℕ) • (g.1 : ZMod 3) = (1 : ZMod 3) := by
      simpa using congrArg Prod.fst hg
    have hg0 : (3 : ℕ) • (g.1 : ZMod 3) = 0 := by
      have h3 : (3 : ZMod 3) = 0 := by decide
      rw [nsmul_eq_mul]
      simp [h3]
    have : (1 : ZMod 3) = 0 := by
      calc
        (1 : ZMod 3) = (3 : ℕ) • (g.1 : ZMod 3) := by simpa using hg1.symm
        _ = 0 := hg0
    exact one_ne_zero this
  let a : (ZMod 3)ˣ := Units.mk0 a0 ha0
  -- `b` is the first coordinate of `f(0,1)`.
  let b : ZMod 3 := (f (0, 1)).1
  -- `d` is the second coordinate of `f(0,1)`; it has additive order 9, hence is a unit in `ZMod 9`.
  let d0 : ZMod 9 := (f (0, 1)).2
  have hd0_order : addOrderOf d0 = 9 := by
    -- Use the order computation in the product.
    have hprod :
        addOrderOf (f (0, 1) : G) = 9 := by
      calc
        addOrderOf (f ((0, 1) : G)) = addOrderOf ((0, 1) : G) := by
          simp
        _ = 9 := by
          simp [Prod.addOrderOf_mk]
    -- Now extract the second coordinate order from the lcm formula.
    have h_lcm :
        Nat.lcm (addOrderOf (b : ZMod 3)) (addOrderOf d0) = 9 := by
      have hη : f (0, 1) = ((b, d0) : G) := by
        dsimp [b, d0]
      have hprod' : addOrderOf ((b, d0) : G) = 9 := by
        simpa [hη] using hprod
      simpa [Nat.lcm, Prod.addOrderOf_mk] using hprod'
    have hb3 : addOrderOf (b : ZMod 3) ∣ 3 := by
      simpa using (addOrderOf_dvd_card (x := (b : ZMod 3)))
    have hd9 : addOrderOf d0 ∣ 9 := by
      simpa using (addOrderOf_dvd_card (x := d0))
    have hnot : ¬ addOrderOf d0 ∣ 3 := by
      intro h
      have : Nat.lcm (addOrderOf (b : ZMod 3)) (addOrderOf d0) ∣ 3 := Nat.lcm_dvd hb3 h
      have : (9 : ℕ) ∣ 3 := by simp [h_lcm] at this
      exact (by decide : ¬ (9 : ℕ) ∣ 3) this
    -- Since `addOrderOf d0 ∣ 9` and does not divide `3`, it must be `9`.
    rcases (Nat.dvd_prime_pow (p := 3) (m := 2) (pp := by decide)).1 hd9 with ⟨k, hk, hk'⟩
    -- `addOrderOf d0 = 3^k` with `k ≤ 2`.
    have : k = 2 := by
      cases k with
      | zero =>
          exfalso
          have : (3 ^ 0 : ℕ) ∣ 3 := by simp
          exact hnot (by simp [hk'])
      | succ k =>
          cases k with
          | zero =>
              exfalso
              have : (3 ^ 1 : ℕ) ∣ 3 := by simp
              exact hnot (by simp [hk'])
          | succ k =>
              -- `k.succ.succ ≤ 2` forces `k = 0`.
              have hk1 : Nat.succ k ≤ 1 := (Nat.succ_le_succ_iff).1 hk
              have hk0 : k ≤ 0 := (Nat.succ_le_succ_iff).1 hk1
              have : k = 0 := Nat.le_antisymm hk0 (Nat.zero_le _)
              simp [this]
    -- Conclude.
    subst this
    simp [hk']
  have hd0_coprime : Nat.Coprime d0.val 9 := by
    have hformula : addOrderOf d0 = (9 : ℕ) / Nat.gcd 9 d0.val := by
      -- `addOrderOf (a : ZMod n) = n / gcd n a`.
      simpa [ZMod.natCast_zmod_val] using
        (ZMod.addOrderOf_coe (a := d0.val) (n := 9) (n0 := (by decide : (9 : ℕ) ≠ 0)))
    have hdiv : (9 : ℕ) / Nat.gcd 9 d0.val = 9 :=
      hformula.symm.trans hd0_order
    have hgcd : Nat.gcd 9 d0.val = 1 := by
      have h := (Nat.div_eq_self).1 hdiv
      exact h.resolve_left (by decide)
    simp [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, hgcd]
  let d : (ZMod 9)ˣ := ZMod.unitOfCoprime d0.val hd0_coprime
  -- `c` comes from the second coordinate of `f(1,0)`, which is killed by `3`.
  let y0 : ZMod 9 := (f (1, 0)).2
  have hy0 : (3 : ℕ) • y0 = 0 := by
    have h : (3 : ℕ) • (((1, 0) : G)) = 0 := by
      ext <;> decide
    have : (3 : ℕ) • (f (1, 0) : G) = 0 := by
      calc
        (3 : ℕ) • (f (1, 0) : G) = f ((3 : ℕ) • ((1, 0) : G)) := by
          simpa using (f.toAddMonoidHom.map_nsmul ((1, 0) : G) 3).symm
        _ = f 0 := by
          simpa using congrArg f h
        _ = 0 := by
          simp
    simpa [y0] using congrArg Prod.snd this
  let c : ZMod 3 := Classical.choose (exists_mulThree_eq_of_three_nsmul_eq_zero (t := y0) hy0)
  exact ⟨a, d, b, c⟩

-- The two parameterizations are inverses.
lemma addAutToParams_paramsToAddAut (p : Params) : addAutToParams (paramsToAddAut p) = p := by
  classical
  rcases p with ⟨a, d, b, c⟩
  ext
  · -- `a`
    simp [addAutToParams, paramsToAddAut, red]
  · -- `d`
    simp [addAutToParams, paramsToAddAut, red, ZMod.coe_unitOfCoprime]
  · -- `b`
    simp [addAutToParams, paramsToAddAut, red]
  · -- `c`
    apply mulThree_injective
    -- Keep `mulThree` folded so `Classical.choose_spec` can rewrite.
    simp [addAutToParams, paramsToAddAut, red]
    simpa using
      (Classical.choose_spec (p := fun z : ZMod 3 => mulThree z = mulThree c) (h := ?_))

lemma paramsToAddAut_addAutToParams (f : AddAut G) : paramsToAddAut (addAutToParams f) = f := by
  classical
  let g : AddAut G := paramsToAddAut (addAutToParams f)
  change g = f
  have hg10 : g (1, 0) = f (1, 0) := by
    ext
    · simp [g, addAutToParams, paramsToAddAut, red]
    ·
      simp [g, addAutToParams, paramsToAddAut, red, ZMod.coe_unitOfCoprime]
      simpa using
        (Classical.choose_spec (p := fun z : ZMod 3 => mulThree z = (f (1, 0)).2) (h := ?_))
  have hg01 : g (0, 1) = f (0, 1) := by
    ext <;>
      simp [g, addAutToParams, paramsToAddAut, red, ZMod.coe_unitOfCoprime]
  -- Equality of additive equivalences follows from equality of functions.
  refine AddEquiv.ext ?_
  intro xy
  rcases xy with ⟨x, y⟩
  have hxy :
      ((x, y) : G) =
        (x.val : ℕ) • ((1, 0) : G) + (y.val : ℕ) • ((0, 1) : G) := by
    ext <;> simp
  have hfxy :
      f (x, y) =
        (x.val : ℕ) • f (1, 0) + (y.val : ℕ) • f (0, 1) := by
    have hx :
        f ((x.val : ℕ) • ((1, 0) : G)) = (x.val : ℕ) • f (1, 0) := by
      simpa using (f.toAddMonoidHom.map_nsmul ((1, 0) : G) x.val)
    have hy :
        f ((y.val : ℕ) • ((0, 1) : G)) = (y.val : ℕ) • f (0, 1) := by
      simpa using (f.toAddMonoidHom.map_nsmul ((0, 1) : G) y.val)
    -- Rewrite using `hxy`, then distribute with `map_add`.
    calc
      f (x, y) = f ((x.val : ℕ) • ((1, 0) : G) + (y.val : ℕ) • ((0, 1) : G)) := by
        exact congrArg f hxy
      _ = (x.val : ℕ) • f (1, 0) + (y.val : ℕ) • f (0, 1) := by
        rw [map_add, hx, hy]
  have hgxy :
      g (x, y) =
        (x.val : ℕ) • g (1, 0) + (y.val : ℕ) • g (0, 1) := by
    have hx :
        g ((x.val : ℕ) • ((1, 0) : G)) = (x.val : ℕ) • g (1, 0) := by
      simpa using (g.toAddMonoidHom.map_nsmul ((1, 0) : G) x.val)
    have hy :
        g ((y.val : ℕ) • ((0, 1) : G)) = (y.val : ℕ) • g (0, 1) := by
      simpa using (g.toAddMonoidHom.map_nsmul ((0, 1) : G) y.val)
    calc
      g (x, y) = g ((x.val : ℕ) • ((1, 0) : G) + (y.val : ℕ) • ((0, 1) : G)) := by
        exact congrArg g hxy
      _ = (x.val : ℕ) • g (1, 0) + (y.val : ℕ) • g (0, 1) := by
        rw [map_add, hx, hy]
  calc
    g (x, y) = (x.val : ℕ) • g (1, 0) + (y.val : ℕ) • g (0, 1) := hgxy
    _ = (x.val : ℕ) • f (1, 0) + (y.val : ℕ) • f (0, 1) := by
      simp [hg10, hg01]
    _ = f (x, y) := by
      simpa using hfxy.symm

noncomputable def addAutEquivParams : AddAut G ≃ Params :=
  { toFun := addAutToParams
    invFun := fun p => paramsToAddAut p
    left_inv := paramsToAddAut_addAutToParams
    right_inv := addAutToParams_paramsToAddAut }

lemma card_params_eq_108 : Nat.card Params = 108 := by
  -- `| (ZMod 3)ˣ | = φ(3) = 2`, `| (ZMod 9)ˣ | = φ(9) = 6`, and `|ZMod 3| = 3`.
  simp [Params, ZMod.card_units_eq_totient]
  decide

end FATEH21

theorem card_addAut_eq_108 : Nat.card (AddAut <| ZMod 3 × ZMod 9) = 108 := by
  classical
  -- Reduce to the parameter type and count.
  simpa [FATEH21.G, FATEH21.Params] using
    (Nat.card_congr (FATEH21.addAutEquivParams : AddAut FATEH21.G ≃ FATEH21.Params)).trans
      FATEH21.card_params_eq_108

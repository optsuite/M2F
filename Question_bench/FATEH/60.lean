import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Int.Basic

set_option maxHeartbeats 1000000

open Polynomial

open scoped Classical

open Equiv Equiv.Perm Subgroup Fintype

lemma perm_fin3_isSolvable : IsSolvable (Equiv.Perm (Fin 3)) := by
  classical
  have hA : IsSolvable (alternatingGroup (Fin 3)) := by
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      simpa using (nat_card_alternatingGroup (α := Fin 3))
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    letI : IsCyclic (alternatingGroup (Fin 3)) :=
      isCyclic_of_prime_card (α := alternatingGroup (Fin 3)) (p := 3) hcard
    haveI : IsMulCommutative (alternatingGroup (Fin 3)) := ⟨IsCyclic.commutative⟩
    refine isSolvable_of_comm (G := alternatingGroup (Fin 3)) ?_
    intro a b
    simp [mul_comm]
  have hZ : IsSolvable ℤˣ := by
    refine isSolvable_of_comm (G := ℤˣ) ?_
    intro a b
    simpa [mul_comm]
  haveI : IsSolvable (alternatingGroup (Fin 3)) := hA
  haveI : IsSolvable ℤˣ := hZ
  refine solvable_of_ker_le_range (f := (alternatingGroup (Fin 3)).subtype) (g := Equiv.Perm.sign)
    ?_
  intro σ hσ
  exact ⟨⟨σ, hσ⟩, rfl⟩

section

variable (a : ℤ)

noncomputable def f : ℚ[X] :=
  X ^ 6 + C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 + C 1

noncomputable def gZ : ℤ[X] :=
  X ^ 3 + C (3 * (a - 1)) * X + C 3

noncomputable def g : ℚ[X] :=
  (gZ a).map (algebraMap ℤ ℚ)

lemma gZ_monic : (gZ a).Monic := by
  -- `gZ a = X^3 + (C (3*(a-1)) * X + C 3)` and `degree (...) < 3`.
  have hle : degree (C (3 * (a - 1)) * X + C 3 : ℤ[X]) ≤ (1 : WithBot ℕ) := by
    have hp : degree (C (3 * (a - 1)) * X : ℤ[X]) ≤ (1 : WithBot ℕ) := by
      simpa using (degree_C_mul_X_le (R := ℤ) (a := (3 * (a - 1))))
    have hq : degree (C 3 : ℤ[X]) ≤ (1 : WithBot ℕ) :=
      degree_C_le.trans (by decide)
    exact (degree_add_le _ _).trans (max_le hp hq)
  have hlt : degree (C (3 * (a - 1)) * X + C 3 : ℤ[X]) < (3 : WithBot ℕ) :=
    lt_of_le_of_lt hle (by decide)
  simpa [gZ, add_assoc] using (monic_X_pow_add (p := (C (3 * (a - 1)) * X + C 3)) (n := 3) hlt)

lemma gZ_natDegree : (gZ a).natDegree = 3 := by
  have hdeg_p : degree (C (3 * (a - 1)) * X + C 3 : ℤ[X]) < (3 : WithBot ℕ) := by
    have hle : degree (C (3 * (a - 1)) * X + C 3 : ℤ[X]) ≤ (1 : WithBot ℕ) := by
      have hp : degree (C (3 * (a - 1)) * X : ℤ[X]) ≤ (1 : WithBot ℕ) := by
        simpa using (degree_C_mul_X_le (R := ℤ) (a := (3 * (a - 1))))
      have hq : degree (C 3 : ℤ[X]) ≤ (1 : WithBot ℕ) :=
        degree_C_le.trans (by decide)
      exact (degree_add_le _ _).trans (max_le hp hq)
    exact lt_of_le_of_lt hle (by decide)
  have hx3 : degree ((X : ℤ[X]) ^ 3) = (3 : WithBot ℕ) := by simp
  have hdeg : degree ((X : ℤ[X]) ^ 3 + (C (3 * (a - 1)) * X + C 3)) = (3 : WithBot ℕ) := by
    have hlt : degree (C (3 * (a - 1)) * X + C 3 : ℤ[X]) < degree ((X : ℤ[X]) ^ 3) := by
      simpa [hx3] using hdeg_p
    simpa using (degree_add_eq_left_of_degree_lt hlt)
  -- Rearrange to `gZ a`.
  have : degree (gZ a) = (3 : WithBot ℕ) := by
    simpa [gZ, add_assoc] using hdeg
  exact natDegree_eq_of_degree_eq_some (p := gZ a) (n := 3) (by simpa using this)

lemma g_monic : (g a).Monic := by
  -- `g` is obtained from the monic `gZ` by mapping coefficients `ℤ → ℚ`.
  simpa [g] using (gZ_monic a).map (algebraMap ℤ ℚ)

lemma g_natDegree : (g a).natDegree = 3 := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := by
    intro m n h
    exact Int.cast_injective (by simpa using h)
  have hmap : ((gZ a).map (Int.castRingHom ℚ)).natDegree = 3 := by
    simpa [natDegree_map_eq_of_injective hinj] using gZ_natDegree a
  simpa [g] using hmap

lemma f_natDegree : (f a).natDegree = 6 := by
  have hdeg_p :
      degree (C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 + C 1 : ℚ[X]) <
        (6 : WithBot ℕ) := by
    have hle :
        degree (C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 + C 1 : ℚ[X]) ≤
          (4 : WithBot ℕ) := by
      have h4 : degree (C (3 * a : ℚ) * X ^ 4 : ℚ[X]) ≤ (4 : WithBot ℕ) := by
        simpa using (degree_C_mul_X_pow_le (R := ℚ) 4 (3 * a : ℚ))
      have h3 : degree (C 3 * X ^ 3 : ℚ[X]) ≤ (4 : WithBot ℕ) := by
        exact (degree_C_mul_X_pow_le (R := ℚ) 3 (3 : ℚ)).trans (by decide)
      have h2 : degree (C (3 * a : ℚ) * X ^ 2 : ℚ[X]) ≤ (4 : WithBot ℕ) := by
        exact (degree_C_mul_X_pow_le (R := ℚ) 2 (3 * a : ℚ)).trans (by decide)
      have h0 : degree (C 1 : ℚ[X]) ≤ (4 : WithBot ℕ) :=
        degree_C_le.trans (by decide)
      have hle₁ :
          degree (C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 : ℚ[X]) ≤ (4 : WithBot ℕ) :=
        (degree_add_le _ _).trans (max_le h4 h3)
      have hle₂ :
          degree (C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 : ℚ[X]) ≤
            (4 : WithBot ℕ) :=
        (degree_add_le _ _).trans (max_le hle₁ h2)
      exact (degree_add_le _ _).trans (max_le hle₂ h0)
    exact lt_of_le_of_lt hle (by decide)
  have hx6 : degree ((X : ℚ[X]) ^ 6) = (6 : WithBot ℕ) := by simp
  have hdeg : degree ((X : ℚ[X]) ^ 6 + (C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 + C 1)) =
      (6 : WithBot ℕ) := by
    have hlt :
        degree (C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 + C 1 : ℚ[X]) <
          degree ((X : ℚ[X]) ^ 6) := by
      simpa [hx6] using hdeg_p
    simpa using (degree_add_eq_left_of_degree_lt hlt)
  have : degree (f a) = (6 : WithBot ℕ) := by
    simpa [f, add_assoc] using hdeg
  exact natDegree_eq_of_degree_eq_some (p := f a) (n := 6) (by simpa using this)

/-- The cubic resolvent `g` is irreducible over `ℚ`. -/
lemma g_irreducible : Irreducible (g a) := by
  classical
  -- Use Eisenstein's criterion at the prime ideal `(3) ⊆ ℤ`.
  let P : Ideal ℤ := Ideal.span ({(3 : ℤ)} : Set ℤ)
  have hPne : P ≠ ⊤ := by
    simpa [P] using (Ideal.span_singleton_ne_top (α := ℤ) (x := (3 : ℤ)) (by
      simp [Int.isUnit_iff] : ¬ IsUnit (3 : ℤ)))
  have hPprime : P.IsPrime := by
    have hprime3 : Prime (3 : ℤ) := by
      exact (Int.prime_iff_natAbs_prime.2 (by decide : Nat.Prime 3))
    exact (Ideal.span_singleton_prime (α := ℤ) (p := (3 : ℤ)) (by decide)).2 hprime3
  have hgZ_monic : (gZ a).Monic := gZ_monic a
  have hgZ_natDegree : (gZ a).natDegree = 3 := gZ_natDegree a
  have hgZ_eis : (gZ a).IsEisensteinAt P := by
    -- `gZ a = X^3 + 3(a-1)X + 3` is Eisenstein at `(3)`.
    refine Polynomial.Monic.isEisensteinAt_of_mem_of_notMem hgZ_monic hPne ?_ ?_
    · intro n hn
      have hn' : n < 3 := by simpa [hgZ_natDegree] using hn
      cases n with
      | zero =>
        -- constant coefficient `3`
        simp [P, gZ, Ideal.mem_span_singleton]
      | succ n =>
        cases n with
        | zero =>
          -- coefficient of `X` is `3 * (a - 1)`
          simp [P, gZ, Ideal.mem_span_singleton]
        | succ n =>
          cases n with
          | zero =>
            -- coefficient of `X^2` is `0`
            simp [P, gZ, Ideal.mem_span_singleton]
          | succ n =>
            -- `n ≥ 3` contradicts `n < 3`
            exfalso
            have : 3 ≤ Nat.succ (Nat.succ (Nat.succ n)) :=
              Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))
            exact (Nat.not_lt_of_ge this) hn'
    · -- `3 ∉ (3)^2`
      have hP2 : P ^ 2 = Ideal.span ({(9 : ℤ)} : Set ℤ) := by
        simpa [P] using (Ideal.span_singleton_pow (s := (3 : ℤ)) 2)
      -- membership in `span {9}` is `9 ∣ 3`, contradiction.
      simpa [hP2, P, gZ, Ideal.mem_span_singleton] using (by decide : ¬ (9 : ℤ) ∣ (3 : ℤ))
  have hgZ_prim : (gZ a).IsPrimitive := hgZ_monic.isPrimitive
  have hgZ_deg : 0 < (gZ a).natDegree := by simpa [hgZ_natDegree] using (show 0 < (3 : ℕ) by decide)
  have hgZ_irred : Irreducible (gZ a) :=
    (Polynomial.IsEisensteinAt.irreducible hgZ_eis hPprime hgZ_prim hgZ_deg)
  -- Transfer irreducibility along `ℤ → ℚ` using Gauss's lemma.
  have : Irreducible ((gZ a).map (Int.castRingHom ℚ)) :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hgZ_prim).1 hgZ_irred
  simpa [g] using this

end

/-- `S₂` is solvable (indeed, cyclic of order `2`). -/
lemma perm_fin2_isSolvable : IsSolvable (Equiv.Perm (Fin 2)) := by
  classical
  have hcard : Nat.card (Equiv.Perm (Fin 2)) = 2 := by
    simpa using (Fintype.card_perm (α := Fin 2))
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : IsCyclic (Equiv.Perm (Fin 2)) :=
    isCyclic_of_prime_card (α := Equiv.Perm (Fin 2)) (p := 2) hcard
  haveI : IsMulCommutative (Equiv.Perm (Fin 2)) := ⟨IsCyclic.commutative⟩
  refine isSolvable_of_comm (G := Equiv.Perm (Fin 2)) ?_
  intro a b
  simpa using (mul_comm a b)

/-- Quadratic Galois groups are solvable, via the embedding into permutations of (at most) two roots. -/
lemma quad_gal_isSolvable (K : Type*) [Field K] [CharZero K] (y : K) :
    IsSolvable ((X ^ 2 - C y * X + 1 : K[X]).Gal) := by
  classical
  let p : K[X] := X ^ 2 - C y * X + 1
  let E := p.SplittingField
  haveI : Fact ((p.map (algebraMap K E)).Splits) := ⟨SplittingField.splits p⟩
  -- `Gal(p)` embeds into permutations of the roots in a splitting field.
  have hinj₁ : Function.Injective (Polynomial.Gal.galActionHom p E) :=
    Polynomial.Gal.galActionHom_injective p E
  -- The root set has cardinality at most `2`.
  have hcard : Fintype.card (p.rootSet E) ≤ 2 := by
    -- `rootSet` is `roots.toFinset`, so its size is bounded by `roots.card`,
    -- and `roots.card ≤ natDegree` for maps.
    have h1 :
        Fintype.card (p.rootSet E) = (p.map (algebraMap K E)).roots.toFinset.card := by
      classical
      simp [Polynomial.rootSet_def]
    have h2 :
        (p.map (algebraMap K E)).roots.toFinset.card ≤ (p.map (algebraMap K E)).roots.card := by
      simpa using Multiset.toFinset_card_le ((p.map (algebraMap K E)).roots)
    have h3 : (p.map (algebraMap K E)).roots.card ≤ p.natDegree := by
      simpa using (Polynomial.card_roots_map_le_natDegree (f := algebraMap K E) p)
    have hpdeg : p.natDegree = 2 := by
      have : (X ^ 2 - C y * X + 1 : K[X]).natDegree = 2 := by
        have hle : degree (-C y * X + (1 : K[X])) ≤ (1 : WithBot ℕ) := by
          have hp : degree (-C y * X : K[X]) ≤ (1 : WithBot ℕ) := by
            simpa [mul_assoc] using (degree_C_mul_X_le (R := K) (a := (-y)))
          have hq : degree (1 : K[X]) ≤ (1 : WithBot ℕ) := by
            simpa using (degree_C_le (a := (1 : K)))
          exact (degree_add_le _ _).trans (max_le hp (hq.trans (by decide)))
        have hlt : degree (-C y * X + (1 : K[X])) < (2 : WithBot ℕ) :=
          lt_of_le_of_lt hle (by decide)
        have hx2 : degree ((X : K[X]) ^ 2) = (2 : WithBot ℕ) := by simp
        have hdeg : degree ((X : K[X]) ^ 2 + (-C y * X + (1 : K[X]))) = (2 : WithBot ℕ) := by
          have hlt' : degree (-C y * X + (1 : K[X])) < degree ((X : K[X]) ^ 2) := by
            simpa [hx2] using hlt
          simpa using (degree_add_eq_left_of_degree_lt hlt')
        have : degree (X ^ 2 - C y * X + 1 : K[X]) = (2 : WithBot ℕ) := by
          simpa [sub_eq_add_neg, add_assoc] using hdeg
        exact natDegree_eq_of_degree_eq_some (p := (X ^ 2 - C y * X + 1 : K[X])) (n := 2)
          (by simpa using this)
      simpa [p] using this
    have : (p.map (algebraMap K E)).roots.toFinset.card ≤ 2 :=
      h2.trans (h3.trans (by simpa [hpdeg]))
    simpa [h1] using this
  have hEmb : Nonempty (p.rootSet E ↪ Fin 2) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hcard
  let ι : p.rootSet E ↪ Fin 2 := Classical.choice hEmb
  have hinj₂ : Function.Injective (Equiv.Perm.viaEmbeddingHom ι) :=
    Equiv.Perm.viaEmbeddingHom_injective ι
  haveI : IsSolvable (Equiv.Perm (Fin 2)) := perm_fin2_isSolvable
  refine solvable_of_solvable_injective (f := (Equiv.Perm.viaEmbeddingHom ι).comp
    (Polynomial.Gal.galActionHom p E)) (hinj₂.comp hinj₁)

/--For a positive integer $a$, consider the polynomial $$ f_a = x^6 + 3ax^4 + 3x^3 + 3ax^2 + 1.
 $$ Let $F$ be the splitting field of $f_a$. Show that its Galois group is solvable.-/

theorem isSolvable_X_pow_six_add_gal {a : ℤ} (ha : a > 0) : IsSolvable
    (X ^ 6 + C (3 * a : ℚ) * X ^ 4 + C 3 * X ^ 3 + C (3 * a : ℚ) * X ^ 2 + C 1 : ℚ[X]).Gal := by
  classical
  -- Introduce `f` and the cubic resolvent `g`.
  let fa : ℚ[X] := f a
  let ga : ℚ[X] := g a
  have hga_irred : Irreducible ga := by
    simpa [ga] using g_irreducible a
  have hga_monic : ga.Monic := by
    simpa [ga] using g_monic a
  -- Apply Abel–Ruffini's solvable tower lemma with `p=g`, `q=f`.
  refine gal_isSolvable_tower ga fa ?_ ?_ ?_
  · -- `g` splits in the splitting field of `f`.
    let L := fa.SplittingField
    -- Make typeclass inference see the instances for the `let`-abbreviation `L`.
    letI : Field L := by
      dsimp [L]
      infer_instance
    letI : CharZero L := by
      dsimp [L]
      infer_instance
    letI : Algebra ℚ L := by
      dsimp [L]
      infer_instance
    have hf_split : (fa.map (algebraMap ℚ L)).Splits := SplittingField.splits fa
    have hdeg : (fa.map (algebraMap ℚ L)).degree ≠ 0 := by
      apply degree_ne_of_natDegree_ne
      have hn : (fa.map (algebraMap ℚ L)).natDegree = 6 := by
        simpa [fa, natDegree_map_eq_of_injective (algebraMap ℚ L).injective] using f_natDegree a
      simpa [hn]
    classical
    let x : L := Polynomial.rootOfSplits (f := fa.map (algebraMap ℚ L)) hf_split hdeg
    have hx : aeval x fa = 0 := by
      -- convert `eval` statement from `rootOfSplits` into `aeval`
      have hx' : (fa.map (algebraMap ℚ L)).eval x = 0 := by
        simpa using
          Polynomial.eval_rootOfSplits (f := fa.map (algebraMap ℚ L)) hf_split hdeg
      simpa [Polynomial.aeval_def, Polynomial.eval, Polynomial.eval₂_map] using hx'
    have hx0 : x ≠ 0 := by
      intro hx0
      have : aeval (0 : L) fa = 0 := by simpa [hx0] using hx
      simpa [fa, f, Polynomial.aeval_def] using this
    -- key identity: `f(x) = x^3 * g(x + x⁻¹)`
    have hga' : ga = (X ^ 3 + C (3 * (a - 1) : ℚ) * X + C 3 : ℚ[X]) := by
      -- `simp` reduces the maps; then normalize `C 3` vs `3`.
      simp [ga, g, gZ, add_assoc]
      have hC3 : (C (3 : ℚ) : ℚ[X]) = (3 : ℚ[X]) := by
        simpa using (C_eq_natCast (R := ℚ) 3)
      simpa [hC3]      
    have hidentity : aeval x fa = x ^ 3 * aeval (x + x⁻¹) ga := by
      -- Rewrite `ga` once to avoid looping simp.
      rw [hga']
      simp [fa, f, Polynomial.aeval_def]
      have haeval (t : L) : eval₂ (algebraMap ℚ L) t (a : ℚ[X]) = (a : L) := by
        calc
          eval₂ (algebraMap ℚ L) t (a : ℚ[X]) = eval₂ (algebraMap ℚ L) t (C (a : ℚ)) := by
            exact
              congrArg (fun p : ℚ[X] => eval₂ (algebraMap ℚ L) t p) ((C_eq_intCast (R := ℚ) a).symm)
          _ = algebraMap ℚ L (a : ℚ) := by
            simpa using (eval₂_C (f := algebraMap ℚ L) (x := t) (a := (a : ℚ)))
          _ = (a : L) := by simp
      simp [haeval]
      field_simp [hx0]
      ring
    have hy : aeval (x + x⁻¹) ga = 0 := by
      have : x ^ 3 * aeval (x + x⁻¹) ga = 0 := by simpa [hidentity] using hx
      have hx3 : x ^ 3 ≠ 0 := pow_ne_zero 3 hx0
      exact (mul_eq_zero.mp this).resolve_left hx3
    -- Identify `g` as the minpoly of `y = x + x⁻¹`, hence it splits in `L` by normality.
    let y : L := x + x⁻¹
    have hmin : minpoly ℚ y = ga := by
      symm
      refine minpoly.eq_of_irreducible_of_monic hga_irred ?_ hga_monic
      simpa [y] using hy
    have hsplit : (minpoly ℚ y).map (algebraMap ℚ L) |>.Splits := by
      have hnorm : Normal ℚ L := SplittingField.instNormal fa
      simpa using (Normal.splits (F := ℚ) (K := L) hnorm y)
    simpa [hmin, fa, ga] using hsplit
  · -- `g.Gal` is solvable (it embeds into `S₃`).
    let K := ga.SplittingField
    haveI : Fact ((ga.map (algebraMap ℚ K)).Splits) := ⟨SplittingField.splits ga⟩
    have hcard : Fintype.card (ga.rootSet K) = 3 := by
      -- `g` is separable in characteristic zero and splits in its splitting field.
      have hgsep : ga.Separable := hga_irred.separable
      have := Polynomial.card_rootSet_eq_natDegree (K := K) hgsep (SplittingField.splits ga)
      have hdeg : ga.natDegree = 3 := by simpa [ga] using g_natDegree a
      simpa [hdeg] using this
    let e : ga.rootSet K ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
    haveI : IsSolvable (Equiv.Perm (Fin 3)) := perm_fin3_isSolvable
    refine solvable_of_solvable_injective (f :=
      (Equiv.Perm.viaEmbeddingHom e.toEmbedding).comp (Polynomial.Gal.galActionHom ga K)) ?_
    exact (Equiv.Perm.viaEmbeddingHom_injective e.toEmbedding).comp
      (Polynomial.Gal.galActionHom_injective ga K)
  · -- Over `K = g.SplittingField`, `f` factors into three solvable quadratics.
    let K := ga.SplittingField
    -- Make typeclass inference see the instances for the `let`-abbreviation `K`.
    letI : Field K := by
      dsimp [K]
      infer_instance
    letI : CharZero K := by
      dsimp [K]
      infer_instance
    letI : Algebra ℚ K := by
      dsimp [K]
      infer_instance
    letI : CommRing K := by
      dsimp [K]
      infer_instance
    let gK : K[X] := ga.map (algebraMap ℚ K)
    let fK : K[X] := fa.map (algebraMap ℚ K)
    have hgK_split : gK.Splits := SplittingField.splits ga
    have hgK_monic : gK.Monic := by simpa [gK] using (hga_monic.map (algebraMap ℚ K))
    have hgK_card : gK.roots.card = 3 := by
      have h := (hgK_split.natDegree_eq_card_roots : gK.natDegree = gK.roots.card)
      have hn : gK.natDegree = 3 := by
        -- `gK` is a cubic in `K[X]`
        simpa [gK, ga, natDegree_map_eq_of_injective (algebraMap ℚ K).injective] using g_natDegree a
      simpa [hn] using h.symm
    obtain ⟨y₁, y₂, y₃, hyroots⟩ := (Multiset.card_eq_three).1 hgK_card
    have hgK_fact : gK = (X - C y₁) * (X - C y₂) * (X - C y₃) := by
      have hgK_prod : gK = (gK.roots.map (X - C ·)).prod := by
        simpa using hgK_split.eq_prod_roots_of_monic hgK_monic
      -- rewrite the roots as `{y₁,y₂,y₃}`
      simpa [hyroots, gK, mul_assoc, mul_left_comm, mul_comm] using hgK_prod
    have hgaQ : ga = (X ^ 3 + C (3 * (a - 1) : ℚ) * X + C 3 : ℚ[X]) := by
      simp [ga, g, gZ, add_assoc]
      have hC3 : (C (3 : ℚ) : ℚ[X]) = (3 : ℚ[X]) := by
        simpa using (C_eq_natCast (R := ℚ) 3)
      simpa [hC3]
    have hgK_def : gK = (X ^ 3 + C (algebraMap ℚ K (3 * (a - 1) : ℚ)) * X + C 3 : K[X]) := by
      -- `gK` is obtained by mapping the explicit cubic for `ga`.
      -- First rewrite `ga` using `hgaQ`, then simplify the `map`.
      simpa [gK, hgaQ, add_assoc, mul_assoc] using congrArg (fun p : ℚ[X] => p.map (algebraMap ℚ K)) hgaQ
    -- Vieta relations coming from the explicit cubic form.
    have hg_eq :
        (X ^ 3 + C (algebraMap ℚ K (3 * (a - 1) : ℚ)) * X + C 3 : K[X]) =
          (X - C y₁) * (X - C y₂) * (X - C y₃) := by
      simpa using hgK_def.symm.trans hgK_fact
    have hcoeff2_prod :
        ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 2 = -(y₁ + y₂ + y₃) := by
      have hp12_2 : ((X - C y₁) * (X - C y₂) : K[X]).coeff 2 = 1 := by
        have h := (coeff_mul_X_sub_C (p := (X - C y₁ : K[X])) (r := y₂) (a := 1))
        simpa [sub_eq_add_neg, Polynomial.coeff_X] using h
      have hp12_1 : ((X - C y₁) * (X - C y₂) : K[X]).coeff 1 = -(y₁ + y₂) := by
        have h := (coeff_mul_X_sub_C (p := (X - C y₁ : K[X])) (r := y₂) (a := 0))
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Polynomial.coeff_X] using h
      have h2 :=
        (coeff_mul_X_sub_C (p := ((X - C y₁) * (X - C y₂) : K[X])) (r := y₃) (a := 1))
      have h2' :
          ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 2 = (-(y₁ + y₂) - (1 : K) * y₃) := by
        simpa [mul_assoc, hp12_1, hp12_2] using h2
      calc
        ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 2 = (-(y₁ + y₂) - (1 : K) * y₃) := h2'
        _ = -(y₁ + y₂ + y₃) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hcoeff1_prod :
        ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 1 =
          y₁ * y₂ + y₁ * y₃ + y₂ * y₃ := by
      have hp12_1 : ((X - C y₁) * (X - C y₂) : K[X]).coeff 1 = -(y₁ + y₂) := by
        have h := (coeff_mul_X_sub_C (p := (X - C y₁ : K[X])) (r := y₂) (a := 0))
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, Polynomial.coeff_X] using h
      have hp12_0 : ((X - C y₁) * (X - C y₂) : K[X]).coeff 0 = y₁ * y₂ := by
        simp
      have h1 :=
        (coeff_mul_X_sub_C (p := ((X - C y₁) * (X - C y₂) : K[X])) (r := y₃) (a := 0))
      have h1' :
          ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 1 = (y₁ * y₂ - (-(y₁ + y₂)) * y₃) := by
        simpa [mul_assoc, hp12_0, hp12_1] using h1
      calc
        ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 1 = (y₁ * y₂ - (-(y₁ + y₂)) * y₃) := h1'
        _ = y₁ * y₂ + y₁ * y₃ + y₂ * y₃ := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, add_mul, mul_add, mul_assoc]
    have hcoeff0_prod :
        ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 0 = -(y₁ * y₂ * y₃) := by
      -- Constant coefficient via evaluation at `0`.
      simp [coeff_zero_eq_eval_zero, mul_assoc]
    have hsum : y₁ + y₂ + y₃ = 0 := by
      have hcoeff2 := congrArg (fun p : K[X] => p.coeff 2) hg_eq
      have haCoeff1 : (a : K[X]).coeff 1 = (0 : K) := by
        have h : (a : K[X]) = C (a : K) := (C_eq_intCast (R := K) a).symm
        have h' : (a : K[X]).coeff 1 = (C (a : K) : K[X]).coeff 1 := by
          simpa using congrArg (fun p : K[X] => p.coeff 1) h
        calc
          (a : K[X]).coeff 1 = (C (a : K) : K[X]).coeff 1 := h'
          _ = 0 := by
            rw [Polynomial.coeff_C]
            simp
      have hOneCoeff1 : (1 : K[X]).coeff 1 = (0 : K) := by
        rw [(C_1 (R := K)).symm]
        rw [Polynomial.coeff_C]
        simp
      have hleft2 :
          (X ^ 3 + C (algebraMap ℚ K (3 * (a - 1) : ℚ)) * X + C 3 : K[X]).coeff 2 = 0 := by
        simp
        simpa [haCoeff1, hOneCoeff1]
      have hrhs2 : ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 2 = 0 := by
        calc
          ((X - C y₁) * (X - C y₂) * (X - C y₃) : K[X]).coeff 2 =
              (X ^ 3 + C (algebraMap ℚ K (3 * (a - 1) : ℚ)) * X + C 3 : K[X]).coeff 2 := by
            simpa using hcoeff2.symm
          _ = 0 := hleft2
      have hs : -(y₁ + y₂ + y₃) = (0 : K) := by
        -- rewrite `coeff 2` using `hcoeff2_prod`
        simpa [hcoeff2_prod] using hrhs2
      exact neg_eq_zero.mp hs
    have hpair :
        y₁ * y₂ + y₁ * y₃ + y₂ * y₃ = algebraMap ℚ K (3 * (a - 1) : ℚ) := by
      have hcoeff1 := congrArg (fun p : K[X] => p.coeff 1) hg_eq
      have hleft1 :
          (X ^ 3 + C (algebraMap ℚ K (3 * ((a : ℚ) - 1))) * X + C 3 : K[X]).coeff 1 =
            algebraMap ℚ K (3 * (a - 1) : ℚ) := by
        simp
      have ht : algebraMap ℚ K (3 * (a - 1) : ℚ) = y₁ * y₂ + y₁ * y₃ + y₂ * y₃ := by
        simpa [hleft1, hcoeff1_prod] using hcoeff1
      simpa [add_assoc, add_left_comm, add_comm] using ht.symm
    have hprod : y₁ * y₂ * y₃ = -algebraMap ℚ K (3 : ℚ) := by
      have hcoeff0 := congrArg (fun p : K[X] => p.coeff 0) hg_eq
      -- constant coefficient gives `3 = -(y₁y₂y₃)`
      have hleft0 :
          (X ^ 3 + C (algebraMap ℚ K (3 * ((a : ℚ) - 1))) * X + C 3 : K[X]).coeff 0 = (3 : K) := by
        simp
      have h0 : (3 : K) = -(y₁ * y₂ * y₃) := by
        simpa [hleft0, hcoeff0_prod] using hcoeff0
      have h0' : y₁ * y₂ * y₃ = -(3 : K) := by
        simpa using (congrArg Neg.neg h0).symm
      simpa using h0'
    -- Expand the product of the three quadratics and rewrite using the Vieta relations.
    have hfK_fact :
        fK =
          (X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1) := by
      -- Compare coefficients (the polynomials have degree ≤ 6).
      let q1 : K[X] := X ^ 2 - C y₁ * X + 1
      let q2 : K[X] := X ^ 2 - C y₂ * X + 1
      let q3 : K[X] := X ^ 2 - C y₃ * X + 1
      have hfK_natDegree : fK.natDegree = 6 := by
        simpa [fK, fa, natDegree_map_eq_of_injective (algebraMap ℚ K).injective] using f_natDegree a
      have hq_natDegree (y : K) : (X ^ 2 - C y * X + 1 : K[X]).natDegree = 2 := by
        have hle : degree (-C y * X + (1 : K[X])) ≤ (1 : WithBot ℕ) := by
          have hp : degree (-C y * X : K[X]) ≤ (1 : WithBot ℕ) := by
            simpa [mul_assoc] using (degree_C_mul_X_le (R := K) (a := (-y)))
          have hq : degree (1 : K[X]) ≤ (1 : WithBot ℕ) := by
            simpa using (degree_C_le (a := (1 : K)))
          exact (degree_add_le _ _).trans (max_le hp (hq.trans (by decide)))
        have hlt : degree (-C y * X + (1 : K[X])) < (2 : WithBot ℕ) :=
          lt_of_le_of_lt hle (by decide)
        have hx2 : degree ((X : K[X]) ^ 2) = (2 : WithBot ℕ) := by simp
        have hdeg : degree ((X : K[X]) ^ 2 + (-C y * X + (1 : K[X]))) = (2 : WithBot ℕ) := by
          have hlt' : degree (-C y * X + (1 : K[X])) < degree ((X : K[X]) ^ 2) := by
            simpa [hx2] using hlt
          simpa using (degree_add_eq_left_of_degree_lt hlt')
        have : degree (X ^ 2 - C y * X + 1 : K[X]) = (2 : WithBot ℕ) := by
          simpa [sub_eq_add_neg, add_assoc] using hdeg
        exact natDegree_eq_of_degree_eq_some (p := (X ^ 2 - C y * X + 1 : K[X])) (n := 2)
          (by simpa using this)
      have hprod_natDegree_le :
          (q1 * q2 * q3).natDegree ≤ 6 := by
        have h12 : (q1 * q2).natDegree ≤ 4 := by
          simpa [q1, q2, hq_natDegree y₁, hq_natDegree y₂] using
            (natDegree_mul_le (p := q1) (q := q2))
        have h123 :
            ((q1 * q2) * q3).natDegree ≤ 6 := by
          have h := natDegree_mul_le (p := q1 * q2) (q := q3)
          have : (q1 * q2).natDegree + q3.natDegree ≤ 6 := by
            have hq3le : q3.natDegree ≤ 2 := by
              simpa [q3] using (le_of_eq (hq_natDegree y₃))
            simpa using Nat.add_le_add h12 hq3le
          exact h.trans this
        simpa [mul_assoc] using h123
      have mul_coeff_two (p q : K[X]) :
          (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
        classical
        rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
        simp [Finset.sum_range_succ]
      have mul_coeff_three (p q : K[X]) :
          (p * q).coeff 3 =
            p.coeff 0 * q.coeff 3 + p.coeff 1 * q.coeff 2 + p.coeff 2 * q.coeff 1 + p.coeff 3 * q.coeff 0 := by
        classical
        rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
        simp [Finset.sum_range_succ]
      have mul_coeff_four (p q : K[X]) :
          (p * q).coeff 4 =
            p.coeff 0 * q.coeff 4 + p.coeff 1 * q.coeff 3 + p.coeff 2 * q.coeff 2 + p.coeff 3 * q.coeff 1 +
              p.coeff 4 * q.coeff 0 := by
        classical
        rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
        simp [Finset.sum_range_succ]
      have mul_coeff_five (p q : K[X]) :
          (p * q).coeff 5 =
            p.coeff 0 * q.coeff 5 + p.coeff 1 * q.coeff 4 + p.coeff 2 * q.coeff 3 + p.coeff 3 * q.coeff 2 +
              p.coeff 4 * q.coeff 1 + p.coeff 5 * q.coeff 0 := by
        classical
        rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
        simp [Finset.sum_range_succ]
      have mul_coeff_six (p q : K[X]) :
          (p * q).coeff 6 =
            p.coeff 0 * q.coeff 6 + p.coeff 1 * q.coeff 5 + p.coeff 2 * q.coeff 4 + p.coeff 3 * q.coeff 3 +
              p.coeff 4 * q.coeff 2 + p.coeff 5 * q.coeff 1 + p.coeff 6 * q.coeff 0 := by
        classical
        rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_eq_map]
        simp [Finset.sum_range_succ]
      ext n
      cases n with
      | zero =>
        -- `n = 0`
        simp [fK, fa, f, q1, q2, q3, Polynomial.coeff_one]
      | succ n =>
        cases n with
        | zero =>
          -- `n = 1`
          have hq12_0 : (q1 * q2).coeff 0 = (1 : K) := by simp [q1, q2]
          have hq12_1 : (q1 * q2).coeff 1 = -(y₁ + y₂) := by
            have hq1_0 : q1.coeff 0 = (1 : K) := by simp [q1]
            have hq1_1 : q1.coeff 1 = -y₁ := by simp [q1, Polynomial.coeff_one]
            have hq2_0 : q2.coeff 0 = (1 : K) := by simp [q2]
            have hq2_1 : q2.coeff 1 = -y₂ := by simp [q2, Polynomial.coeff_one]
            have h :
                (q1 * q2).coeff 1 = q1.coeff 0 * q2.coeff 1 + q1.coeff 1 * q2.coeff 0 := by
              simpa using (mul_coeff_one (p := q1) (q := q2))
            have h' : (q1 * q2).coeff 1 = -y₂ + -y₁ := by
              simpa [hq1_0, hq1_1, hq2_0, hq2_1] using h
            calc
              (q1 * q2).coeff 1 = -y₂ + -y₁ := h'
              _ = -y₁ + -y₂ := by simpa using (add_comm (-y₂) (-y₁))
              _ = -(y₁ + y₂) := by simpa using (neg_add y₁ y₂).symm
          have hq123_1 : (q1 * q2 * q3).coeff 1 = -(y₁ + y₂ + y₃) := by
            have hq3_0 : q3.coeff 0 = (1 : K) := by simp [q3]
            have hq3_1 : q3.coeff 1 = -y₃ := by simp [q3, Polynomial.coeff_one]
            have h :
                (q1 * q2 * q3).coeff 1 =
                  (q1 * q2).coeff 0 * q3.coeff 1 + (q1 * q2).coeff 1 * q3.coeff 0 := by
              simpa using (mul_coeff_one (p := q1 * q2) (q := q3))
            have h' : (q1 * q2 * q3).coeff 1 = -y₃ + -(y₁ + y₂) := by
              simpa [hq12_0, hq12_1, hq3_0, hq3_1] using h
            calc
              (q1 * q2 * q3).coeff 1 = -y₃ + -(y₁ + y₂) := h'
              _ = -(y₁ + y₂) + -y₃ := by simpa using (add_comm (-y₃) (-(y₁ + y₂)))
              _ = -((y₁ + y₂) + y₃) := by simpa using (neg_add (y₁ + y₂) y₃).symm
              _ = -(y₁ + y₂ + y₃) := by simp [add_assoc]
          have hRq : (q1 * q2 * q3).coeff 1 = 0 := by
            calc
              (q1 * q2 * q3).coeff 1 = -(y₁ + y₂ + y₃) := hq123_1
              _ = 0 := by simpa [hsum]
          have hR :
              ((X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)).coeff 1 = 0 := by
            simpa [q1, q2, q3] using hRq
          have hL : fK.coeff 1 = 0 := by
            simp [fK, fa, f, Polynomial.coeff_one]
            have ha_poly : (↑a : K[X]) = C (a : K) := by
              simpa using (C_eq_intCast (R := K) a).symm
            have hconst : (C 3 * (↑a : K[X]) : K[X]) = C ((3 : K) * (a : K)) := by
              rw [ha_poly]
              simpa using (C_mul (a := (3 : K)) (b := (a : K))).symm
            have hcoeff4 : (C 3 * (↑a : K[X]) * X ^ 4).coeff 1 = 0 := by
              rw [hconst]
              rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 4 1]
              simp
            have hcoeff2 : (C 3 * (↑a : K[X]) * X ^ 2).coeff 1 = 0 := by
              rw [hconst]
              rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 2 1]
              simp
            simpa [hcoeff4, hcoeff2]
          simpa [hR, hL]
        | succ n =>
          cases n with
          | zero =>
            -- `n = 2`
            have hq12_0 : (q1 * q2).coeff 0 = (1 : K) := by simp [q1, q2]
            have hq12_1 : (q1 * q2).coeff 1 = -(y₁ + y₂) := by
              have hq1_0 : q1.coeff 0 = (1 : K) := by simp [q1]
              have hq1_1 : q1.coeff 1 = -y₁ := by simp [q1, Polynomial.coeff_one]
              have hq2_0 : q2.coeff 0 = (1 : K) := by simp [q2]
              have hq2_1 : q2.coeff 1 = -y₂ := by simp [q2, Polynomial.coeff_one]
              have h :
                  (q1 * q2).coeff 1 = q1.coeff 0 * q2.coeff 1 + q1.coeff 1 * q2.coeff 0 := by
                simpa using (mul_coeff_one (p := q1) (q := q2))
              have h' : (q1 * q2).coeff 1 = -y₂ + -y₁ := by
                simpa [hq1_0, hq1_1, hq2_0, hq2_1] using h
              calc
                (q1 * q2).coeff 1 = -y₂ + -y₁ := h'
                _ = -y₁ + -y₂ := by simpa using (add_comm (-y₂) (-y₁))
                _ = -(y₁ + y₂) := by simpa using (neg_add y₁ y₂).symm
            have hq12_2 : (q1 * q2).coeff 2 = (2 : K) + y₁ * y₂ := by
              have h := mul_coeff_two (p := q1) (q := q2)
              have h' : (q1 * q2).coeff 2 = (1 : K) + y₁ * y₂ + 1 := by
                simpa [q1, q2, sub_eq_add_neg, Polynomial.coeff_one] using h
              calc
                (q1 * q2).coeff 2 = (1 : K) + y₁ * y₂ + 1 := h'
                _ = (2 : K) + y₁ * y₂ := by ring_nf
            have hq123_2 :
                (q1 * q2 * q3).coeff 2 = (3 : K) + (y₁ * y₂ + y₁ * y₃ + y₂ * y₃) := by
              have h := mul_coeff_two (p := q1 * q2) (q := q3)
              have hq3_0 : q3.coeff 0 = (1 : K) := by simp [q3]
              have hq3_1 : q3.coeff 1 = -y₃ := by simp [q3, Polynomial.coeff_one]
              have hq3_2 : q3.coeff 2 = (1 : K) := by simp [q3, Polynomial.coeff_one]
              have h' :
                  (q1 * q2 * q3).coeff 2 =
                    (q1 * q2).coeff 0 * q3.coeff 2 + (q1 * q2).coeff 1 * q3.coeff 1 +
                        (q1 * q2).coeff 2 * q3.coeff 0 := by
                simpa using h
              have h'' :
                  (q1 * q2 * q3).coeff 2 = (1 : K) + -((-y₂ + -y₁) * y₃) + ((2 : K) + y₁ * y₂) := by
                simpa [hq12_0, hq12_1, hq12_2, hq3_0, hq3_1, hq3_2] using h'
              calc
                (q1 * q2 * q3).coeff 2 = (1 : K) + -((-y₂ + -y₁) * y₃) + ((2 : K) + y₁ * y₂) := h''
                _ = (3 : K) + (y₁ * y₂ + y₁ * y₃ + y₂ * y₃) := by ring_nf
            have h3 : (3 : ℚ) + (3 * (a - 1) : ℚ) = (3 * a : ℚ) := by ring
            have hRq : (q1 * q2 * q3).coeff 2 = algebraMap ℚ K (3 * a : ℚ) := by
              calc
                (q1 * q2 * q3).coeff 2 = (3 : K) + (y₁ * y₂ + y₁ * y₃ + y₂ * y₃) := hq123_2
                _ = (3 : K) + algebraMap ℚ K (3 * (a - 1) : ℚ) := by simpa [hpair]
                _ = algebraMap ℚ K (3 * a : ℚ) := by
                  calc
                    (3 : K) + algebraMap ℚ K (3 * (a - 1) : ℚ) =
                        algebraMap ℚ K (3 : ℚ) + algebraMap ℚ K (3 * (a - 1) : ℚ) := by simp
                    _ = algebraMap ℚ K ((3 : ℚ) + (3 * (a - 1) : ℚ)) := by
                      simpa using (map_add (algebraMap ℚ K) (3 : ℚ) (3 * (a - 1) : ℚ)).symm
                    _ = algebraMap ℚ K (3 * a : ℚ) := by simpa [h3]
            have hR :
                ((X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)).coeff 2 =
                  algebraMap ℚ K (3 * a : ℚ) := by
              simpa [q1, q2, q3] using hRq
            rw [hR]
            simp [fK, fa, f, Polynomial.coeff_one]
            have ha_poly : (↑a : K[X]) = C (a : K) := by
              simpa using (C_eq_intCast (R := K) a).symm
            have hconst : (C 3 * (↑a : K[X]) : K[X]) = C ((3 : K) * (a : K)) := by
              rw [ha_poly]
              simpa using (C_mul (a := (3 : K)) (b := (a : K))).symm
            have hcoeff4 : (C 3 * (↑a : K[X]) * X ^ 4).coeff 2 = 0 := by
              rw [hconst]
              rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 4 2]
              simp
            have hcoeff2 : (C 3 * (↑a : K[X]) * X ^ 2).coeff 2 = (3 : K) * (a : K) := by
              rw [hconst]
              rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 2 2]
              simp
            have hone : (1 : K[X]).coeff 2 = 0 := by
              simp [Polynomial.coeff_one]
            simpa [hcoeff4, hcoeff2, hone]
          | succ n =>
            cases n with
            | zero =>
              -- `n = 3`
              have hL3 : fK.coeff 3 = (3 : K) := by
                simp [fK, fa, f, Polynomial.coeff_one]
                have ha_poly : (↑a : K[X]) = C (a : K) := by
                  simpa using (C_eq_intCast (R := K) a).symm
                have hconst : (C 3 * (↑a : K[X]) : K[X]) = C ((3 : K) * (a : K)) := by
                  rw [ha_poly]
                  simpa using (C_mul (a := (3 : K)) (b := (a : K))).symm
                have hcoeff4 : (C 3 * (↑a : K[X]) * X ^ 4).coeff 3 = 0 := by
                  rw [hconst]
                  rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 4 3]
                  simp
                have hcoeff2 : (C 3 * (↑a : K[X]) * X ^ 2).coeff 3 = 0 := by
                  rw [hconst]
                  rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 2 3]
                  simp
                simpa [hcoeff4, hcoeff2]
              have hq3_0 : q3.coeff 0 = (1 : K) := by simp [q3]
              have hq3_1 : q3.coeff 1 = -y₃ := by simp [q3, Polynomial.coeff_one]
              have hq3_2 : q3.coeff 2 = (1 : K) := by simp [q3, Polynomial.coeff_one]
              have hq3_3 : q3.coeff 3 = (0 : K) := by simp [q3, Polynomial.coeff_one]
              have hr12_0 : (q1 * q2).coeff 0 = (1 : K) := by simp [q1, q2]
              have hr12_1 : (q1 * q2).coeff 1 = -(y₁ + y₂) := by
                have h :
                    (q1 * q2).coeff 1 = q1.coeff 0 * q2.coeff 1 + q1.coeff 1 * q2.coeff 0 := by
                  simpa using (mul_coeff_one (p := q1) (q := q2))
                have hq1_0 : q1.coeff 0 = (1 : K) := by simp [q1]
                have hq1_1 : q1.coeff 1 = -y₁ := by simp [q1, Polynomial.coeff_one]
                have hq2_0 : q2.coeff 0 = (1 : K) := by simp [q2]
                have hq2_1 : q2.coeff 1 = -y₂ := by simp [q2, Polynomial.coeff_one]
                have h' : (q1 * q2).coeff 1 = -y₂ + -y₁ := by
                  simpa [hq1_0, hq1_1, hq2_0, hq2_1] using h
                calc
                  (q1 * q2).coeff 1 = -y₂ + -y₁ := h'
                  _ = -y₁ + -y₂ := by simpa using (add_comm (-y₂) (-y₁))
                  _ = -(y₁ + y₂) := by simpa using (neg_add y₁ y₂).symm
              have hr12_2 : (q1 * q2).coeff 2 = (2 : K) + y₁ * y₂ := by
                have h := mul_coeff_two (p := q1) (q := q2)
                have h' : (q1 * q2).coeff 2 = (1 : K) + y₁ * y₂ + 1 := by
                  simpa [q1, q2, sub_eq_add_neg, Polynomial.coeff_one] using h
                calc
                  (q1 * q2).coeff 2 = (1 : K) + y₁ * y₂ + 1 := h'
                  _ = (2 : K) + y₁ * y₂ := by ring_nf
              have hr12_3 : (q1 * q2).coeff 3 = -(y₁ + y₂) := by
                have h := mul_coeff_three (p := q1) (q := q2)
                have hq1_0 : q1.coeff 0 = (1 : K) := by simp [q1]
                have hq1_1 : q1.coeff 1 = -y₁ := by simp [q1, Polynomial.coeff_one]
                have hq1_2 : q1.coeff 2 = (1 : K) := by simp [q1, Polynomial.coeff_one]
                have hq1_3 : q1.coeff 3 = (0 : K) := by simp [q1, Polynomial.coeff_one]
                have hq2_0 : q2.coeff 0 = (1 : K) := by simp [q2]
                have hq2_1 : q2.coeff 1 = -y₂ := by simp [q2, Polynomial.coeff_one]
                have hq2_2 : q2.coeff 2 = (1 : K) := by simp [q2, Polynomial.coeff_one]
                have hq2_3 : q2.coeff 3 = (0 : K) := by simp [q2, Polynomial.coeff_one]
                have h' : (q1 * q2).coeff 3 = -y₁ + -y₂ := by
                  simpa [hq1_0, hq1_1, hq1_2, hq1_3, hq2_0, hq2_1, hq2_2, hq2_3] using h
                calc
                  (q1 * q2).coeff 3 = -y₁ + -y₂ := h'
                  _ = -(y₁ + y₂) := by simpa using (neg_add y₁ y₂).symm
              have hR3q : (q1 * q2 * q3).coeff 3 = (3 : K) := by
                have h := mul_coeff_three (p := q1 * q2) (q := q3)
                have h' :
                    (q1 * q2 * q3).coeff 3 =
                      (q1 * q2).coeff 0 * q3.coeff 3 + (q1 * q2).coeff 1 * q3.coeff 2 +
                        (q1 * q2).coeff 2 * q3.coeff 1 + (q1 * q2).coeff 3 * q3.coeff 0 := by
                  simpa using h
                have h'' : (q1 * q2 * q3).coeff 3 = -((2 : K) * (y₁ + y₂ + y₃)) - (y₁ * y₂ * y₃) := by
                  have : (q1 * q2 * q3).coeff 3 =
                      -(y₁ + y₂) + ((2 : K) + y₁ * y₂) * (-y₃) + -(y₁ + y₂) := by
                    simpa [hr12_0, hr12_1, hr12_2, hr12_3, hq3_0, hq3_1, hq3_2, hq3_3, add_assoc] using h'
                  calc
                    (q1 * q2 * q3).coeff 3 =
                        -(y₁ + y₂) + ((2 : K) + y₁ * y₂) * (-y₃) + -(y₁ + y₂) := this
                    _ = -((2 : K) * (y₁ + y₂ + y₃)) - (y₁ * y₂ * y₃) := by
                      ring_nf
                calc
                  (q1 * q2 * q3).coeff 3 = -((2 : K) * (y₁ + y₂ + y₃)) - (y₁ * y₂ * y₃) := h''
                  _ = -(y₁ * y₂ * y₃) := by simp [hsum]
                  _ = (3 : K) := by simpa [hprod]
              have hR3 :
                  ((X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)).coeff 3 =
                    (3 : K) := by
                simpa [q1, q2, q3] using hR3q
              simpa [hL3, hR3]
            | succ n =>
              cases n with
              | zero =>
                -- `n = 4`
                have hq3_0 : q3.coeff 0 = (1 : K) := by simp [q3]
                have hq3_1 : q3.coeff 1 = -y₃ := by simp [q3, Polynomial.coeff_one]
                have hq3_2 : q3.coeff 2 = (1 : K) := by simp [q3, Polynomial.coeff_one]
                have hq3_3 : q3.coeff 3 = (0 : K) := by simp [q3, Polynomial.coeff_one]
                have hq3_4 : q3.coeff 4 = (0 : K) := by simp [q3, Polynomial.coeff_one]

                have hr12_2 : (q1 * q2).coeff 2 = (2 : K) + y₁ * y₂ := by
                  have h := mul_coeff_two (p := q1) (q := q2)
                  have h' : (q1 * q2).coeff 2 = (1 : K) + y₁ * y₂ + 1 := by
                    simpa [q1, q2, sub_eq_add_neg, Polynomial.coeff_one] using h
                  calc
                    (q1 * q2).coeff 2 = (1 : K) + y₁ * y₂ + 1 := h'
                    _ = (2 : K) + y₁ * y₂ := by ring_nf
                have hr12_3 : (q1 * q2).coeff 3 = -(y₁ + y₂) := by
                  have h := mul_coeff_three (p := q1) (q := q2)
                  have hq1_0 : q1.coeff 0 = (1 : K) := by simp [q1]
                  have hq1_1 : q1.coeff 1 = -y₁ := by simp [q1, Polynomial.coeff_one]
                  have hq1_2 : q1.coeff 2 = (1 : K) := by simp [q1, Polynomial.coeff_one]
                  have hq1_nat : q1.natDegree = 2 := by simpa [q1] using hq_natDegree y₁
                  have hq1_3 : q1.coeff 3 = (0 : K) := by
                    refine coeff_eq_zero_of_natDegree_lt ?_
                    simpa [hq1_nat] using (by decide : 2 < 3)
                  have hq2_0 : q2.coeff 0 = (1 : K) := by simp [q2]
                  have hq2_1 : q2.coeff 1 = -y₂ := by simp [q2, Polynomial.coeff_one]
                  have hq2_2 : q2.coeff 2 = (1 : K) := by simp [q2, Polynomial.coeff_one]
                  have hq2_nat : q2.natDegree = 2 := by simpa [q2] using hq_natDegree y₂
                  have hq2_3 : q2.coeff 3 = (0 : K) := by
                    refine coeff_eq_zero_of_natDegree_lt ?_
                    simpa [hq2_nat] using (by decide : 2 < 3)
                  have h' : (q1 * q2).coeff 3 = -y₁ + -y₂ := by
                    have h0 :
                        (q1 * q2).coeff 3 =
                          q1.coeff 0 * q2.coeff 3 + q1.coeff 1 * q2.coeff 2 + q1.coeff 2 * q2.coeff 1 +
                            q1.coeff 3 * q2.coeff 0 := by
                      simpa using h
                    -- rewrite the vanishing coefficients and simplify.
                    rw [hq1_0, hq1_1, hq1_2, hq1_3, hq2_0, hq2_1, hq2_2, hq2_3] at h0
                    simpa using h0
                  calc
                    (q1 * q2).coeff 3 = -y₁ + -y₂ := h'
                    _ = -(y₁ + y₂) := by simpa using (neg_add y₁ y₂).symm
                have hr12_4 : (q1 * q2).coeff 4 = (1 : K) := by
                  have h := mul_coeff_four (p := q1) (q := q2)
                  -- all terms except `coeff 2 * coeff 2` vanish
                  simpa [q1, q2, sub_eq_add_neg, Polynomial.coeff_one] using h

                have hq123_4 :
                    (q1 * q2 * q3).coeff 4 = (3 : K) + (y₁ * y₂ + y₁ * y₃ + y₂ * y₃) := by
                  have h := mul_coeff_four (p := q1 * q2) (q := q3)
                  have h' :
                      (q1 * q2 * q3).coeff 4 =
                        (q1 * q2).coeff 0 * q3.coeff 4 + (q1 * q2).coeff 1 * q3.coeff 3 +
                          (q1 * q2).coeff 2 * q3.coeff 2 + (q1 * q2).coeff 3 * q3.coeff 1 +
                            (q1 * q2).coeff 4 * q3.coeff 0 := by
                    simpa using h
                  have h'' :
                      (q1 * q2 * q3).coeff 4 =
                        (q1 * q2).coeff 2 * q3.coeff 2 + (q1 * q2).coeff 3 * q3.coeff 1 + (q1 * q2).coeff 4 * q3.coeff 0 := by
                    simpa [hq3_3, hq3_4] using h'
                  calc
                    (q1 * q2 * q3).coeff 4 =
                        (q1 * q2).coeff 2 * q3.coeff 2 + (q1 * q2).coeff 3 * q3.coeff 1 + (q1 * q2).coeff 4 * q3.coeff 0 := h''
                    _ = (3 : K) + (y₁ * y₂ + y₁ * y₃ + y₂ * y₃) := by
                      simp [hr12_2, hr12_3, hr12_4, hq3_0, hq3_1, hq3_2]
                      ring_nf

                have h3 : (3 : ℚ) + (3 * (a - 1) : ℚ) = (3 * a : ℚ) := by ring
                have hRq : (q1 * q2 * q3).coeff 4 = algebraMap ℚ K (3 * a : ℚ) := by
                  calc
                    (q1 * q2 * q3).coeff 4 = (3 : K) + (y₁ * y₂ + y₁ * y₃ + y₂ * y₃) := hq123_4
                    _ = (3 : K) + algebraMap ℚ K (3 * (a - 1) : ℚ) := by simpa [hpair]
                    _ = algebraMap ℚ K (3 * a : ℚ) := by
                      calc
                        (3 : K) + algebraMap ℚ K (3 * (a - 1) : ℚ) =
                            algebraMap ℚ K (3 : ℚ) + algebraMap ℚ K (3 * (a - 1) : ℚ) := by simp
                        _ = algebraMap ℚ K ((3 : ℚ) + (3 * (a - 1) : ℚ)) := by
                          simpa using (map_add (algebraMap ℚ K) (3 : ℚ) (3 * (a - 1) : ℚ)).symm
                        _ = algebraMap ℚ K (3 * a : ℚ) := by simpa [h3]
                have hR :
                    ((X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)).coeff 4 =
                      algebraMap ℚ K (3 * a : ℚ) := by
                  simpa [q1, q2, q3] using hRq
                rw [hR]
                simp [fK, fa, f, Polynomial.coeff_one]
                have ha_poly : (↑a : K[X]) = C (a : K) := by
                  simpa using (C_eq_intCast (R := K) a).symm
                have hconst : (C 3 * (↑a : K[X]) : K[X]) = C ((3 : K) * (a : K)) := by
                  rw [ha_poly]
                  simpa using (C_mul (a := (3 : K)) (b := (a : K))).symm
                have hcoeff4 : (C 3 * (↑a : K[X]) * X ^ 4).coeff 4 = (3 : K) * (a : K) := by
                  rw [hconst]
                  rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 4 4]
                  simp
                have hcoeff3 : (C 3 * X ^ 3 : K[X]).coeff 4 = 0 := by
                  rw [Polynomial.coeff_C_mul_X_pow (3 : K) 3 4]
                  simp
                have hcoeff2 : (C 3 * (↑a : K[X]) * X ^ 2).coeff 4 = 0 := by
                  rw [hconst]
                  rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 2 4]
                  simp
                have hone : (1 : K[X]).coeff 4 = 0 := by simp [Polynomial.coeff_one]
                simpa [hcoeff4, hcoeff3, hcoeff2, hone]
              | succ n =>
                cases n with
                | zero =>
                  -- `n = 5`
                  have hq3_0 : q3.coeff 0 = (1 : K) := by simp [q3]
                  have hq3_1 : q3.coeff 1 = -y₃ := by simp [q3, Polynomial.coeff_one]
                  have hq3_2 : q3.coeff 2 = (1 : K) := by simp [q3, Polynomial.coeff_one]
                  have hq3_3 : q3.coeff 3 = (0 : K) := by simp [q3, Polynomial.coeff_one]
                  have hq3_4 : q3.coeff 4 = (0 : K) := by simp [q3, Polynomial.coeff_one]
                  have hq3_5 : q3.coeff 5 = (0 : K) := by simp [q3, Polynomial.coeff_one]

                  have hr12_3 : (q1 * q2).coeff 3 = -(y₁ + y₂) := by
                    have h := mul_coeff_three (p := q1) (q := q2)
                    have hq1_0 : q1.coeff 0 = (1 : K) := by simp [q1]
                    have hq1_1 : q1.coeff 1 = -y₁ := by simp [q1, Polynomial.coeff_one]
                    have hq1_2 : q1.coeff 2 = (1 : K) := by simp [q1, Polynomial.coeff_one]
                    have hq1_3 : q1.coeff 3 = (0 : K) := by simp [q1, Polynomial.coeff_one]
                    have hq2_0 : q2.coeff 0 = (1 : K) := by simp [q2]
                    have hq2_1 : q2.coeff 1 = -y₂ := by simp [q2, Polynomial.coeff_one]
                    have hq2_2 : q2.coeff 2 = (1 : K) := by simp [q2, Polynomial.coeff_one]
                    have hq2_3 : q2.coeff 3 = (0 : K) := by simp [q2, Polynomial.coeff_one]
                    have h' : (q1 * q2).coeff 3 = -y₁ + -y₂ := by
                      simpa [hq1_0, hq1_1, hq1_2, hq1_3, hq2_0, hq2_1, hq2_2, hq2_3] using h
                    calc
                      (q1 * q2).coeff 3 = -y₁ + -y₂ := h'
                      _ = -(y₁ + y₂) := by simpa using (neg_add y₁ y₂).symm
                  have hr12_4 : (q1 * q2).coeff 4 = (1 : K) := by
                    have h := mul_coeff_four (p := q1) (q := q2)
                    simpa [q1, q2, sub_eq_add_neg, Polynomial.coeff_one] using h
                  have hr12_5 : (q1 * q2).coeff 5 = 0 := by
                    have hle : (q1 * q2).natDegree ≤ 4 := by
                      simpa [q1, q2, hq_natDegree y₁, hq_natDegree y₂] using
                        (natDegree_mul_le (p := q1) (q := q2))
                    exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle (by decide : 4 < 5))

                  have hq123_5 : (q1 * q2 * q3).coeff 5 = 0 := by
                    have h := mul_coeff_five (p := q1 * q2) (q := q3)
                    have h' :
                        (q1 * q2 * q3).coeff 5 =
                          (q1 * q2).coeff 0 * q3.coeff 5 + (q1 * q2).coeff 1 * q3.coeff 4 + (q1 * q2).coeff 2 * q3.coeff 3 +
                            (q1 * q2).coeff 3 * q3.coeff 2 + (q1 * q2).coeff 4 * q3.coeff 1 + (q1 * q2).coeff 5 * q3.coeff 0 := by
                      simpa using h
                    have h'' :
                        (q1 * q2 * q3).coeff 5 =
                          (q1 * q2).coeff 3 * q3.coeff 2 + (q1 * q2).coeff 4 * q3.coeff 1 + (q1 * q2).coeff 5 * q3.coeff 0 := by
                      simpa [hq3_3, hq3_4, hq3_5] using h'
                    have : (q1 * q2 * q3).coeff 5 = -(y₁ + y₂ + y₃) := by
                      calc
                        (q1 * q2 * q3).coeff 5 =
                            (q1 * q2).coeff 3 * q3.coeff 2 + (q1 * q2).coeff 4 * q3.coeff 1 +
                              (q1 * q2).coeff 5 * q3.coeff 0 := h''
                        _ = -(y₁ + y₂ + y₃) := by
                          simp [hr12_3, hr12_4, hr12_5, hq3_0, hq3_1, hq3_2]
                          ring_nf
                    simpa [this, hsum]

                  have hR :
                      ((X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)).coeff 5 = 0 := by
                    simpa [q1, q2, q3] using hq123_5
                  have hL : fK.coeff 5 = 0 := by
                    simp [fK, fa, f, Polynomial.coeff_one]
                    have ha_poly : (↑a : K[X]) = C (a : K) := by
                      simpa using (C_eq_intCast (R := K) a).symm
                    have hconst : (C 3 * (↑a : K[X]) : K[X]) = C ((3 : K) * (a : K)) := by
                      rw [ha_poly]
                      simpa using (C_mul (a := (3 : K)) (b := (a : K))).symm
                    have hcoeff4 : (C 3 * (↑a : K[X]) * X ^ 4).coeff 5 = 0 := by
                      rw [hconst]
                      rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 4 5]
                      simp
                    have hcoeff3 : (C 3 * X ^ 3 : K[X]).coeff 5 = 0 := by
                      rw [Polynomial.coeff_C_mul_X_pow (3 : K) 3 5]
                      simp
                    have hcoeff2 : (C 3 * (↑a : K[X]) * X ^ 2).coeff 5 = 0 := by
                      rw [hconst]
                      rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 2 5]
                      simp
                    have hone : (1 : K[X]).coeff 5 = 0 := by simp [Polynomial.coeff_one]
                    simpa [hcoeff4, hcoeff3, hcoeff2, hone]
                  simpa [hR, hL]
                | succ n =>
                  cases n with
                  | zero =>
                    -- `n = 6`
                    have hq3_0 : q3.coeff 0 = (1 : K) := by simp [q3]
                    have hq3_1 : q3.coeff 1 = -y₃ := by simp [q3, Polynomial.coeff_one]
                    have hq3_2 : q3.coeff 2 = (1 : K) := by simp [q3, Polynomial.coeff_one]
                    have hq3_3 : q3.coeff 3 = (0 : K) := by simp [q3, Polynomial.coeff_one]
                    have hq3_4 : q3.coeff 4 = (0 : K) := by simp [q3, Polynomial.coeff_one]
                    have hq3_5 : q3.coeff 5 = (0 : K) := by simp [q3, Polynomial.coeff_one]
                    have hq3_6 : q3.coeff 6 = (0 : K) := by simp [q3, Polynomial.coeff_one]

                    have hr12_4 : (q1 * q2).coeff 4 = (1 : K) := by
                      have h := mul_coeff_four (p := q1) (q := q2)
                      simpa [q1, q2, sub_eq_add_neg, Polynomial.coeff_one] using h
                    have hr12_5 : (q1 * q2).coeff 5 = 0 := by
                      have hle : (q1 * q2).natDegree ≤ 4 := by
                        simpa [q1, q2, hq_natDegree y₁, hq_natDegree y₂] using
                          (natDegree_mul_le (p := q1) (q := q2))
                      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle (by decide : 4 < 5))
                    have hr12_6 : (q1 * q2).coeff 6 = 0 := by
                      have hle : (q1 * q2).natDegree ≤ 4 := by
                        simpa [q1, q2, hq_natDegree y₁, hq_natDegree y₂] using
                          (natDegree_mul_le (p := q1) (q := q2))
                      exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hle (by decide : 4 < 6))

                    have hq123_6 : (q1 * q2 * q3).coeff 6 = 1 := by
                      have h := mul_coeff_six (p := q1 * q2) (q := q3)
                      have h' :
                          (q1 * q2 * q3).coeff 6 =
                            (q1 * q2).coeff 0 * q3.coeff 6 + (q1 * q2).coeff 1 * q3.coeff 5 + (q1 * q2).coeff 2 * q3.coeff 4 +
                              (q1 * q2).coeff 3 * q3.coeff 3 + (q1 * q2).coeff 4 * q3.coeff 2 + (q1 * q2).coeff 5 * q3.coeff 1 +
                                (q1 * q2).coeff 6 * q3.coeff 0 := by
                        simpa using h
                      have h'' : (q1 * q2 * q3).coeff 6 = (q1 * q2).coeff 4 * q3.coeff 2 := by
                        simpa [hq3_3, hq3_4, hq3_5, hq3_6, hr12_5, hr12_6] using h'
                      simpa [h'' , hr12_4, hq3_2]

                    have hR :
                        ((X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)).coeff 6 = 1 := by
                      simpa [q1, q2, q3] using hq123_6
                    rw [hR]
                    simp [fK, fa, f, Polynomial.coeff_one]
                    have ha_poly : (↑a : K[X]) = C (a : K) := by
                      simpa using (C_eq_intCast (R := K) a).symm
                    have hconst : (C 3 * (↑a : K[X]) : K[X]) = C ((3 : K) * (a : K)) := by
                      rw [ha_poly]
                      simpa using (C_mul (a := (3 : K)) (b := (a : K))).symm
                    have hcoeff4 : (C 3 * (↑a : K[X]) * X ^ 4).coeff 6 = 0 := by
                      rw [hconst]
                      rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 4 6]
                      simp
                    have hcoeff3 : (C 3 * X ^ 3 : K[X]).coeff 6 = 0 := by
                      rw [Polynomial.coeff_C_mul_X_pow (3 : K) 3 6]
                      simp
                    have hcoeff2 : (C 3 * (↑a : K[X]) * X ^ 2).coeff 6 = 0 := by
                      rw [hconst]
                      rw [Polynomial.coeff_C_mul_X_pow ((3 : K) * (a : K)) 2 6]
                      simp
                    have hone : (1 : K[X]).coeff 6 = 0 := by simp [Polynomial.coeff_one]
                    simpa [hcoeff4, hcoeff3, hcoeff2, hone]
                  | succ n =>
                    -- For `n ≥ 7`, both sides have coefficient `0`.
                    have hn6 :
                        6 < Nat.succ
                            (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))) := by
                      have :
                          7 ≤ Nat.succ
                                (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))) :=
                        Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ
                          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))))))
                      exact lt_of_lt_of_le (by decide : 6 < 7) this
                    have hlt_left :
                        fK.natDegree <
                          Nat.succ
                            (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))) := by
                      simpa [hfK_natDegree] using hn6
                    have hlt_right :
                        (q1 * q2 * q3).natDegree <
                          Nat.succ
                            (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n)))))) := by
                      exact lt_of_le_of_lt hprod_natDegree_le hn6
                    rw [coeff_eq_zero_of_natDegree_lt hlt_left, coeff_eq_zero_of_natDegree_lt hlt_right]
    -- Each quadratic factor has solvable Galois group, hence so does the product.
    have hy₁ : IsSolvable ((X ^ 2 - C y₁ * X + 1 : K[X]).Gal) := quad_gal_isSolvable K y₁
    have hy₂ : IsSolvable ((X ^ 2 - C y₂ * X + 1 : K[X]).Gal) := quad_gal_isSolvable K y₂
    have hy₃ : IsSolvable ((X ^ 2 - C y₃ * X + 1 : K[X]).Gal) := quad_gal_isSolvable K y₃
    have hprod_solv :
        IsSolvable
          (((X ^ 2 - C y₁ * X + 1 : K[X]) * (X ^ 2 - C y₂ * X + 1) *
                (X ^ 2 - C y₃ * X + 1)).Gal) := by
      simpa [mul_assoc] using
        gal_mul_isSolvable (gal_mul_isSolvable hy₁ hy₂) hy₃
    have hsolv : IsSolvable fK.Gal := by
      classical
      let qprod : K[X] :=
        (X ^ 2 - C y₁ * X + 1) * (X ^ 2 - C y₂ * X + 1) * (X ^ 2 - C y₃ * X + 1)
      haveI : IsSplittingField K fK.SplittingField qprod := by
        simpa [qprod, hfK_fact] using (inferInstance : IsSplittingField K fK.SplittingField fK)
      let e : fK.SplittingField ≃ₐ[K] qprod.SplittingField :=
        Polynomial.IsSplittingField.algEquiv (K := K) (L := fK.SplittingField) qprod
      haveI : IsSolvable (qprod.SplittingField ≃ₐ[K] qprod.SplittingField) := by
        simpa [qprod, Polynomial.Gal] using hprod_solv
      exact
        solvable_of_solvable_injective (f := (AlgEquiv.autCongr e).toMonoidHom)
          (AlgEquiv.autCongr e).injective
    simpa [fK] using hsolv

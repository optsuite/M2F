import Mathlib

open IntermediateField AdjoinRoot Polynomial

namespace FATEH42

section

variable (K L : Type) [Field K] [Field L] [Algebra K L]

lemma card_aut_L_eq_four
    (f : (L ≃ₐ[K] L) ≃* Multiplicative (ZMod 2 × ZMod 2)) :
    Nat.card (L ≃ₐ[K] L) = 4 := by
  classical
  simpa using (Nat.card_congr f.toEquiv)

lemma finrank_L_adjoinRoot_eq_two (c : Lˣ) :
    Module.finrank L (AdjoinRoot (X ^ 2 - C c.1)) = 2 := by
  classical
  have hp0 : (X ^ 2 - C c.1 : L[X]) ≠ 0 :=
    (monic_X_pow_sub_C c.1 (by decide : (2 : ℕ) ≠ 0)).ne_zero
  -- `AdjoinRoot.powerBasis` has dimension `natDegree (X^2 - C c) = 2`.
  simpa [natDegree_X_pow_sub_C] using
    (PowerBasis.finrank (AdjoinRoot.powerBasis (K := L) (f := X ^ 2 - C c.1) hp0))

lemma root_not_mem_algebraMap (c : Lˣ) (hcs : ¬ IsSquare c.1)
    [Fact (Irreducible (X ^ 2 - C c.1))] :
    (AdjoinRoot.root (X ^ 2 - C c.1 : L[X])) ∉
      Set.range (algebraMap L (AdjoinRoot (X ^ 2 - C c.1))) := by
  classical
  intro hroot
  rcases hroot with ⟨x, hx⟩
  have hsq : IsSquare c.1 := by
    refine ⟨x, ?_⟩
    -- Compare squares using `root^2 = c`.
    have hroot_sq :
        (AdjoinRoot.root (X ^ 2 - C c.1 : L[X])) ^ 2 =
          algebraMap L (AdjoinRoot (X ^ 2 - C c.1)) c.1 := by
      simpa [AdjoinRoot.algebraMap_eq] using (root_X_pow_sub_C_pow (K := L) 2 c.1)
    have :
        algebraMap L (AdjoinRoot (X ^ 2 - C c.1)) (x ^ 2) =
          algebraMap L (AdjoinRoot (X ^ 2 - C c.1)) c.1 := by
      calc
        algebraMap L (AdjoinRoot (X ^ 2 - C c.1)) (x ^ 2)
            = (algebraMap L (AdjoinRoot (X ^ 2 - C c.1)) x) ^ 2 := by
                simp [map_pow]
        _ = (AdjoinRoot.root (X ^ 2 - C c.1 : L[X])) ^ 2 := by
          exact congrArg (fun y => y ^ 2) hx
        _ = algebraMap L (AdjoinRoot (X ^ 2 - C c.1)) c.1 := hroot_sq
    have hxmul : x * x = c.1 :=
      (algebraMap L (AdjoinRoot (X ^ 2 - C c.1))).injective (by simpa [pow_two] using this)
    simpa [pow_two] using hxmul.symm
  exact hcs hsq

end

end FATEH42

set_option maxHeartbeats 800000 in
/--Let \( K \) be a field with \( \operatorname{char}(K) \neq 2 \). Consider Galois extensions
\( L/K \) with \( \operatorname{Gal}(L/K) \cong (\mathbb{Z}/2\mathbb{Z})^2 \). Let \( c \in L^\times
\) be a nonsquare, and let \( E = K(\sqrt{c}) \). Prove that \( E \) is Galois over \( K \) if and
only if for each \( \sigma \in \operatorname{Gal}(L/K) \), the ratio \( \sigma(c)/c \) is a square
in \( L \).-/
theorem isGalois_adjoin_iff_isSquare (K L : Type) [Field K] [Field L] (h : ¬ CharP K 2) [Algebra K L] [IsGalois K L]
    (f : (L ≃ₐ[K] L) ≃* Multiplicative (ZMod 2 × ZMod 2)) (c : Lˣ) (hc : c.1 ≠ 0)
    (hcs : ¬ IsSquare c.1) [Fact (Irreducible (X ^ 2 - C c.1))] :
    IsGalois K (AdjoinRoot (X ^ 2 - C c.1)) ↔ ∀ σ : (L ≃ₐ[K] L), IsSquare (σ c / c) := by
  classical
  haveI : Finite (L ≃ₐ[K] L) :=
    Finite.of_equiv (Multiplicative (ZMod 2 × ZMod 2)) f.toEquiv.symm
  haveI : FiniteDimensional K L := IsGalois.finiteDimensional_of_finite (F := K) (E := L)
  let E : Type := AdjoinRoot (X ^ 2 - C c.1)
  let α : E := AdjoinRoot.root (X ^ 2 - C c.1 : L[X])
  haveI : FiniteDimensional L E := by
    classical
    let p : L[X] := X ^ 2 - C c.1
    have hpMonic : p.Monic := monic_X_pow_sub_C c.1 (by decide : (2 : ℕ) ≠ 0)
    let b : Module.Basis (Fin p.natDegree) L E := by
      simpa [E, p] using (AdjoinRoot.powerBasisAux' (R := L) (g := p) hpMonic)
    exact Module.Basis.finiteDimensional_of_finite b
  haveI : FiniteDimensional K E := by
    -- `E` is finite over `L`, hence finite over `K`.
    exact FiniteDimensional.trans K L E
  have hα_sq : α ^ 2 = algebraMap L E c.1 := by
    simpa [α, AdjoinRoot.algebraMap_eq] using (root_X_pow_sub_C_pow (K := L) 2 c.1)
  have hα_ne : (α : E) ≠ 0 := by
    intro h0
    have : algebraMap L E c.1 = 0 := by simpa [h0] using hα_sq.symm
    have : c.1 = 0 := (algebraMap L E).injective (by simp [this])
    exact hc this
  have hα_not_mem : (α : E) ∉ Set.range (algebraMap L E) := by
    simpa [E, α] using (FATEH42.root_not_mem_algebraMap (L := L) c hcs)
  have h2K : (2 : K) ≠ 0 := by
    intro h2
    exact h (CharTwo.of_one_ne_zero_of_two_eq_zero (one_ne_zero : (1 : K) ≠ 0) (by simpa using h2))
  have h2L : (2 : L) ≠ 0 := by
    intro h2
    apply h2K
    apply (algebraMap K L).injective
    have hmap : algebraMap K L (2 : K) = (2 : L) := by
      simpa using (map_natCast (algebraMap K L) 2)
    simpa [hmap] using h2
  have h2E : (2 : E) ≠ 0 := by
    intro h2
    apply h2L
    apply (algebraMap L E).injective
    have hmap : algebraMap L E (2 : L) = (2 : E) := by
      simpa using (map_natCast (algebraMap L E) 2)
    simpa [hmap] using h2

  constructor
  · intro hGal
    letI : IsGalois K E := hGal
    intro σ
    let τ : (E ≃ₐ[K] E) := σ.liftNormal E
    have hτL : ∀ x : L, τ (algebraMap L E x) = algebraMap L E (σ x) := by
      intro x
      simp [τ]
    have hτL_symm : ∀ x : L, τ.symm (algebraMap L E x) = algebraMap L E (σ.symm x) := by
      intro x
      have := congrArg τ.symm (hτL (σ.symm x))
      simpa using this.symm
    have hτα_not_mem : τ α ∉ Set.range (algebraMap L E) := by
      intro hmem
      rcases hmem with ⟨x, hx⟩
      have : (α : E) ∈ Set.range (algebraMap L E) := by
        refine ⟨σ.symm x, ?_⟩
        calc
          algebraMap L E (σ.symm x) = τ.symm (algebraMap L E x) := by
            simpa using (hτL_symm x).symm
          _ = τ.symm (τ α) := by simp [hx]
          _ = (α : E) := by simp
      exact hα_not_mem this

    -- Every element of `E` can be reduced to degree `< 2`, hence written as `a + b * α`.
    have exists_add_mul_root :
        ∀ x : E, ∃ a b : L, x = algebraMap L E a + algebraMap L E b * α := by
      intro x
      refine AdjoinRoot.induction_on (f := (X ^ 2 - C c.1 : L[X]))
        (C := fun x : E => ∃ a b : L, x = algebraMap L E a + algebraMap L E b * α) x ?_
      intro q
      let p : L[X] := (X ^ 2 - C c.1)
      have hpMonic : p.Monic := monic_X_pow_sub_C c.1 (by decide : (2 : ℕ) ≠ 0)
      have hpne1 : p ≠ 1 := by
        intro hp
        have := congrArg Polynomial.natDegree hp
        simp [p] at this
      have hmk :
          (AdjoinRoot.mk p q : E) = AdjoinRoot.mk p (q %ₘ p) := by
        have := (AdjoinRoot.mk_leftInverse (g := p) hpMonic) (AdjoinRoot.mk p q)
        -- `modByMonicHom_mk` identifies the chosen representative with `%ₘ`.
        simpa [AdjoinRoot.modByMonicHom_mk] using this.symm
      have hdeg : (q %ₘ p).natDegree < 2 := by
        have hlt : (q %ₘ p).natDegree < p.natDegree :=
          Polynomial.natDegree_modByMonic_lt q hpMonic hpne1
        simpa [p, natDegree_X_pow_sub_C] using hlt
      have hlin :
          (q %ₘ p) = C ((q %ₘ p).coeff 0) + C ((q %ₘ p).coeff 1) * X := by
        ext n; cases n with
        | zero =>
          simp
        | succ n =>
          cases n with
          | zero =>
            simp
          | succ n =>
            have hdeg' : (q %ₘ p).natDegree < n.succ.succ := by
              exact lt_of_lt_of_le hdeg (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n)))
            have hcoeff :
                (q %ₘ p).coeff n.succ.succ = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt hdeg'
            simp [hcoeff]
      refine ⟨(q %ₘ p).coeff 0, (q %ₘ p).coeff 1, ?_⟩
      -- Rewrite `q` to the reduced representative and then evaluate the linear polynomial.
      calc
        (AdjoinRoot.mk p q : E) = AdjoinRoot.mk p (q %ₘ p) := hmk
        _ = AdjoinRoot.mk p (C ((q %ₘ p).coeff 0) + C ((q %ₘ p).coeff 1) * X) := by
          simpa using congrArg (AdjoinRoot.mk p) hlin
        _ = algebraMap L E ((q %ₘ p).coeff 0) + algebraMap L E ((q %ₘ p).coeff 1) * α := by
          -- Avoid `simp` recursion by rewriting with `mk`'s ring hom properties.
          set a0 : L := (q %ₘ p).coeff 0
          set a1 : L := (q %ₘ p).coeff 1
          have hadd :
              (AdjoinRoot.mk p (C a0 + C a1 * X) : E) =
                AdjoinRoot.mk p (C a0) + AdjoinRoot.mk p (C a1 * X) := by
              exact (AdjoinRoot.mk p).map_add (C a0) (C a1 * X)
          have hC0 : (AdjoinRoot.mk p (C a0) : E) = algebraMap L E a0 := by
              simp [E, p, AdjoinRoot.algebraMap_eq]
          have hCX : (AdjoinRoot.mk p (C a1 * X) : E) = algebraMap L E a1 * α := by
            calc
              (AdjoinRoot.mk p (C a1 * X) : E)
                  = (AdjoinRoot.mk p (C a1) : E) * AdjoinRoot.mk p X := by
                      exact (AdjoinRoot.mk p).map_mul (C a1) X
              _ = algebraMap L E a1 * α := by
                      simp [E, α, p, AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
          -- Put the pieces together.
          have hlin_eval :
                (AdjoinRoot.mk p (C a0 + C a1 * X) : E) =
                  algebraMap L E a0 + algebraMap L E a1 * α := by
              calc
                (AdjoinRoot.mk p (C a0 + C a1 * X) : E)
                    = AdjoinRoot.mk p (C a0) + AdjoinRoot.mk p (C a1 * X) := hadd
                _ = algebraMap L E a0 + algebraMap L E a1 * α := by
                    simp [hC0, hCX]
          simpa [a0, a1] using hlin_eval

    obtain ⟨a, b, hab⟩ := exists_add_mul_root (τ α)
    have hb_ne : b ≠ 0 := by
      intro hb
      have : τ α ∈ Set.range (algebraMap L E) := by
        refine ⟨a, ?_⟩
        simp [hab, hb]
      exact hτα_not_mem this

    have hτ_sq : (τ α) ^ 2 = algebraMap L E (σ c.1) := by
      -- Apply `τ` to `α^2 = c` and use that `τ` restricts to `σ` on `L`.
      calc
        (τ α) ^ 2 = τ (α ^ 2) := by simp
        _ = τ (algebraMap L E c.1) := by simp [hα_sq]
        _ = algebraMap L E (σ c.1) := by simpa using (hτL c.1)

    have hMul :
        algebraMap L E (2 * a * b) * α =
          algebraMap L E (σ c.1 - (a ^ 2 + b ^ 2 * c.1)) := by
      -- Expand `(a + bα)^2` and isolate the `α`-term.
      have h1 :
          (algebraMap L E a + algebraMap L E b * α) ^ 2 = algebraMap L E (σ c.1) := by
        simpa [hab] using hτ_sq
      have hring :
          (algebraMap L E a + algebraMap L E b * α) ^ 2 =
            (algebraMap L E a) ^ 2 + (2 * (algebraMap L E a) * (algebraMap L E b)) * α +
              (algebraMap L E b) ^ 2 * (α ^ 2) := by
        ring
      have h2 :
          (algebraMap L E a) ^ 2 + (2 * (algebraMap L E a) * (algebraMap L E b)) * α +
              (algebraMap L E b) ^ 2 * (α ^ 2) =
            algebraMap L E (σ c.1) := by
        simpa [hring] using h1
      -- Replace `α^2` by `c`, and then subtract the constant terms.
      have h3 :
          (2 * (algebraMap L E a) * (algebraMap L E b)) * α =
            algebraMap L E (σ c.1) -
              ((algebraMap L E a) ^ 2 + (algebraMap L E b) ^ 2 * (α ^ 2)) := by
        -- Rearrange `h2` into the form `B + (A + C) = D`, then use `eq_sub_iff_add_eq`.
        refine (eq_sub_iff_add_eq).2 ?_
        -- `ac_rfl` handles the commutative rebracketing/reordering of addition.
        calc
          (2 * (algebraMap L E a) * (algebraMap L E b)) * α +
                ((algebraMap L E a) ^ 2 + (algebraMap L E b) ^ 2 * (α ^ 2))
              =
                (algebraMap L E a) ^ 2 + (2 * (algebraMap L E a) * (algebraMap L E b)) * α +
                  (algebraMap L E b) ^ 2 * (α ^ 2) := by
                ac_rfl
          _ = algebraMap L E (σ c.1) := h2
      have h4 :
          (2 * (algebraMap L E a) * (algebraMap L E b)) * α =
            algebraMap L E (σ c.1) -
              ((algebraMap L E a) ^ 2 + (algebraMap L E b) ^ 2 * algebraMap L E c.1) := by
        simpa [hα_sq, mul_assoc] using h3
      -- Rewrite the scalar coefficients back in `L`.
      have h5 :
          (algebraMap L E (2 * a * b)) * α =
            algebraMap L E (σ c.1) -
              algebraMap L E (a ^ 2 + b ^ 2 * c.1) := by
        have hmap2 : algebraMap L E (2 : L) = (2 : E) := by
          simpa using (map_natCast (algebraMap L E) 2)
        have hcoeff :
            algebraMap L E (2 * a * b) = 2 * algebraMap L E a * algebraMap L E b := by
          calc
            algebraMap L E (2 * a * b)
                = algebraMap L E (2 : L) * algebraMap L E a * algebraMap L E b := by
                    simp [map_mul, mul_assoc]
            _ = (2 : E) * algebraMap L E a * algebraMap L E b := by
                    simp [hmap2, mul_assoc]
            _ = 2 * algebraMap L E a * algebraMap L E b := rfl
        have hconst :
            (algebraMap L E a) ^ 2 + (algebraMap L E b) ^ 2 * algebraMap L E c.1 =
              algebraMap L E (a ^ 2 + b ^ 2 * c.1) := by
          simp [map_add, map_mul, map_pow]
        -- Rewrite `h4` with these scalar identities.
        have h4' :
            (algebraMap L E (2 * a * b)) * α =
              algebraMap L E (σ c.1) -
                algebraMap L E (a ^ 2 + b ^ 2 * c.1) := by
          have h4a :
              (2 * algebraMap L E a * algebraMap L E b) * α =
                algebraMap L E (σ c.1) -
                  ((algebraMap L E a) ^ 2 + (algebraMap L E b) ^ 2 * algebraMap L E c.1) := by
            simpa [mul_assoc] using h4
          have h4b := h4a
          -- Replace the scalar coefficient by `algebraMap (2ab)`.
          -- (`hcoeff` is written in the direction that `rw` can use.)
          rw [← hcoeff] at h4b
          -- Replace the constant term by `algebraMap (a^2 + b^2*c)`.
          rw [hconst] at h4b
          exact h4b
        exact h4'
      simpa [map_sub] using h5

    have h2ab : (2 * a * b : L) = 0 := by
      by_contra hne
      have hne' : (algebraMap L E (2 * a * b)) ≠ 0 := by
        intro h0
        exact hne ((algebraMap L E).injective (by simpa using h0))
      -- Divide the identity `algebraMap (2ab) * α = algebraMap s` by `algebraMap (2ab)`.
      have : (α : E) ∈ Set.range (algebraMap L E) := by
        refine ⟨(σ c.1 - (a ^ 2 + b ^ 2 * c.1)) / (2 * a * b), ?_⟩
        -- Turn `algebraMap (s / (2ab))` into `(algebraMap s) * (algebraMap (2ab))⁻¹` and rewrite via `hMul`.
        calc
          algebraMap L E ((σ c.1 - (a ^ 2 + b ^ 2 * c.1)) / (2 * a * b))
              = algebraMap L E (σ c.1 - (a ^ 2 + b ^ 2 * c.1)) / algebraMap L E (2 * a * b) := by
                  simp [map_div₀]
          _ = algebraMap L E (σ c.1 - (a ^ 2 + b ^ 2 * c.1)) * (algebraMap L E (2 * a * b))⁻¹ := by
                  simp [div_eq_mul_inv]
          _ = (algebraMap L E (2 * a * b) * (α : E)) * (algebraMap L E (2 * a * b))⁻¹ := by
                  simp [hMul.symm, mul_assoc]
          _ = (α : E) := by
                  -- Cancel `algebraMap (2ab)` using `hne'`, without expanding `2ab`.
                  let d : E := algebraMap L E (2 * a * b)
                  have hd : d ≠ 0 := by
                    simpa [d] using hne'
                  -- Rewrite the expression in terms of `d`.
                  have : (d * (α : E)) * d⁻¹ = (α : E) := by
                    calc
                      (d * (α : E)) * d⁻¹ = (α : E) * (d * d⁻¹) := by
                        simp [mul_assoc, mul_comm]
                      _ = (α : E) := by
                        simp [hd]
                  simpa [d, mul_assoc] using this
      exact hα_not_mem this

    have ha_zero : a = 0 := by
      -- `2ab = 0` with `b ≠ 0` and `2 ≠ 0` gives `a = 0`.
      have hb' : (b : L) ≠ 0 := hb_ne
      have h2a : (2 * a : L) = 0 := by
        have h' := congrArg (fun t : L => t * b⁻¹) h2ab
        simp [mul_assoc, hb'] at h'
        simpa [mul_assoc] using h'
      have h' := congrArg (fun t : L => t * (2 : L)⁻¹) h2a
      simp [mul_assoc, h2L] at h'
      simpa using h'

    have hb_sq : b ^ 2 = (σ c / c : L) := by
      -- Using `a = 0`, compare squares to get `b^2 * c = σ c`.
      have hE :
          algebraMap L E (b ^ 2 * c.1) = algebraMap L E (σ c.1) := by
        -- Start from `(τ α)^2 = σ(c)` and rewrite `τ α = b * α`.
        have hab' : τ α = algebraMap L E b * α := by
          simp [hab, ha_zero]
        calc
          algebraMap L E (b ^ 2 * c.1)
              = (algebraMap L E b) ^ 2 * algebraMap L E c.1 := by
                  simp [map_mul, pow_two, mul_left_comm, mul_comm]
          _ = (algebraMap L E b) ^ 2 * (α ^ 2) := by simp [hα_sq]
          _ = (algebraMap L E b * α) ^ 2 := by ring
          _ = (τ α) ^ 2 := by simp [hab']
          _ = algebraMap L E (σ c.1) := hτ_sq
      have hb2c : b ^ 2 * c.1 = σ c.1 := (algebraMap L E).injective hE
      have h' := congrArg (fun t : L => t * (c.1)⁻¹) hb2c
      -- `c` is a unit, hence `c.1 ≠ 0`, so we can cancel.
      simpa [div_eq_mul_inv, mul_assoc, hc] using h'

    exact ⟨b, by simpa [pow_two] using hb_sq.symm⟩

  · intro hs
    -- Construct enough distinct `K`-algebra endomorphisms of `E` to force Galoisness.
    have hs' : ∀ σ : (L ≃ₐ[K] L), ∃ u : L, u ^ 2 = (σ c / c : L) := by
      intro σ
      rcases hs σ with ⟨u, hu⟩
      exact ⟨u, by simpa [pow_two] using hu.symm⟩
    choose u hu using hs'
    haveI : Fintype (E →ₐ[K] E) := by
      classical
      dsimp [E]
      infer_instance

    have hcardAut : Nat.card (L ≃ₐ[K] L) = 4 := FATEH42.card_aut_L_eq_four (K := K) (L := L) f
    have hfinrankKL : Module.finrank K L = 4 := by
      -- `L/K` is Galois, so `|Aut(L/K)| = [L:K]`.
      have hcard_fin : Nat.card (L ≃ₐ[K] L) = Module.finrank K L := by
        simpa using (IsGalois.card_aut_eq_finrank (F := K) (E := L))
      simpa [hcard_fin] using hcard_fin.symm.trans hcardAut
    have hfinrankLE : Module.finrank L E = 2 := by
      simpa [E] using (FATEH42.finrank_L_adjoinRoot_eq_two (L := L) c)
    have hfinrankKE : Module.finrank K E = 8 := by
      calc
        Module.finrank K E = Module.finrank K L * Module.finrank L E := by
          simpa [E] using (Module.finrank_mul_finrank K L E).symm
        _ = 4 * 2 := by simp [hfinrankKL, hfinrankLE]
        _ = 8 := by decide

    -- For each `σ` and choice of sign, build a `K`-algebra endomorphism of `E`.
    let Φ : Bool × (L ≃ₐ[K] L) → (E →ₐ[K] E) := fun bs =>
      let b : Bool := bs.1
      let σ : (L ≃ₐ[K] L) := bs.2
      let iσ : L →ₐ[K] E := (IsScalarTower.toAlgHom K L E).comp σ.toAlgHom
      let sgn : E := if b then (-1 : E) else (1 : E)
      let x : E := sgn * algebraMap L E (u σ) * α
      have hx : Polynomial.eval₂ (↑iσ) x (X ^ 2 - C c.1 : L[X]) = 0 := by
        have hsgn : sgn ^ 2 = (1 : E) := by
          cases b <;> simp [sgn, E]
        have hu_mul : (u σ) ^ 2 * c.1 = σ c.1 := by
          have hmul : (σ c / c : L) * c.1 = σ c.1 := by
            -- In the unit group, `(σ c / c) * c = σ c`.
            exact div_mul_cancel₀ (σ c : L) hc
          have h' : (u σ) ^ 2 * c.1 = (σ c / c : L) * c.1 := by
            rw [hu σ]
          exact h'.trans hmul
        have hx_sq : x ^ 2 = algebraMap L E (σ c.1) := by
          -- Expand `x = (sgn * algebraMap (u σ)) * α` and use commutativity of `E`.
          let y : E := sgn * algebraMap L E (u σ)
          have hx' : x = y * α := by
            simp [x, y, mul_assoc]
          calc
            x ^ 2 = (y * α) ^ 2 := by simp [hx']
            _ = y ^ 2 * (α ^ 2) := by
                simp [mul_pow]
            _ = (sgn ^ 2 * (algebraMap L E (u σ)) ^ 2) * (α ^ 2) := by
                simp [y, mul_pow, mul_assoc]
            _ = ((algebraMap L E (u σ)) ^ 2) * (α ^ 2) := by
                  simp [hsgn]
              _ = algebraMap L E ((u σ) ^ 2) * algebraMap L E c.1 := by
                  simp [map_pow, hα_sq]
              _ = algebraMap L E (((u σ) ^ 2) * c.1) := by
                  simp [map_mul]
              _ = algebraMap L E (σ c.1) := by
                  simp [hu_mul]
        -- `eval₂` at `x` vanishes since `x^2 = iσ(c)`.
        have : iσ c.1 = algebraMap L E (σ c.1) := by
          simp [iσ, AlgHom.comp_apply]
        -- `eval₂ (X^2 - C c) = x^2 - iσ(c)`.
        simp [Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, hx_sq, this, sub_eq_add_neg]
      AdjoinRoot.liftAlgHom (X ^ 2 - C c.1 : L[X]) iσ x hx

    have hΦ_inj : Function.Injective Φ := by
      rintro ⟨b, σ⟩ ⟨b', σ'⟩ hΦ
      -- First recover `σ = σ'` by comparing on `L`.
      have hσ :
          σ = σ' := by
        ext x
        have hx :
            Φ ⟨b, σ⟩ (algebraMap L E x) = Φ ⟨b', σ'⟩ (algebraMap L E x) := by
          simp [hΦ]
        -- `liftAlgHom` agrees with `iσ` on `L`.
        have hxE :
            algebraMap L E (σ x) = algebraMap L E (σ' x) := by
          simpa [Φ, E, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_of, AlgHom.comp_apply] using hx
        exact (algebraMap L E).injective hxE
      cases hσ
      -- Now compare images of `α` to recover the Bool sign.
      have hroot :
          Φ ⟨b, σ⟩ α = Φ ⟨b', σ⟩ α := by simp [hΦ]
      have hroot' :
          (if b = true then (-1 : E) else (1 : E)) * (algebraMap L E (u σ) * α) =
            (if b' = true then (-1 : E) else (1 : E)) * (algebraMap L E (u σ) * α) := by
        simpa [Φ, E, α, AdjoinRoot.algebraMap_eq, AdjoinRoot.liftAlgHom_root, mul_assoc] using hroot
      have hu_ne : u σ ≠ 0 := by
        intro hu0
        have : (σ c / c : L) = 0 := by
          calc
            (σ c / c : L) = (u σ) ^ 2 := (hu σ).symm
            _ = 0 := by simp [hu0]
        have hσc : (σ c : L) ≠ 0 := by
          intro h0
          have : (c : L) = 0 := by
            have h0' := congrArg σ.symm h0
            simp at h0'
          exact (Units.ne_zero c) this
        exact (div_ne_zero hσc hc) this
      have hs_ne : algebraMap L E (u σ) * (α : E) ≠ 0 := by
        exact mul_ne_zero (by
          intro h0
          exact hu_ne ((algebraMap L E).injective (by simpa using h0))) hα_ne
      cases b <;> cases b' <;> try (simp at hroot'; exact rfl)
      · -- `s = -s` forces `s = 0`, contradiction.
        have hs_eq' :
            algebraMap L E (u σ) * (α : E) = (-1 : E) * (algebraMap L E (u σ) * α) := by
          simpa [mul_assoc] using hroot'
        have hs_eq :
            algebraMap L E (u σ) * (α : E) = -(algebraMap L E (u σ) * α) := by
          simpa [E, neg_one_mul] using hs_eq'
        have hs_sum : algebraMap L E (u σ) * (α : E) + algebraMap L E (u σ) * (α : E) = 0 := by
          have := congrArg (fun t : E => t + algebraMap L E (u σ) * α) hs_eq
          simpa [add_assoc, add_left_comm, add_comm] using this
        have hs_mul : (2 : E) * (algebraMap L E (u σ) * (α : E)) = 0 := by
          simpa [two_mul] using hs_sum
        have hs0 : algebraMap L E (u σ) * (α : E) = 0 :=
          (mul_eq_zero.mp hs_mul).resolve_left h2E
        exact (hs_ne hs0).elim
      · -- `-s = s` forces `s = 0`, contradiction.
        have hs_eq' :
            (-1 : E) * (algebraMap L E (u σ) * α) = algebraMap L E (u σ) * (α : E) := by
          simpa [mul_assoc] using hroot'
        have hs_eq :
            -(algebraMap L E (u σ) * α) = algebraMap L E (u σ) * (α : E) := by
          simpa [E, neg_one_mul] using hs_eq'
        have hs_sum : algebraMap L E (u σ) * (α : E) + algebraMap L E (u σ) * (α : E) = 0 := by
          have := congrArg (fun t : E => t + algebraMap L E (u σ) * α) hs_eq.symm
          simpa [add_assoc, add_left_comm, add_comm] using this
        have hs_mul : (2 : E) * (algebraMap L E (u σ) * (α : E)) = 0 := by
          simpa [two_mul] using hs_sum
        have hs0 : algebraMap L E (u σ) * (α : E) = 0 :=
          (mul_eq_zero.mp hs_mul).resolve_left h2E
        exact (hs_ne hs0).elim

    have hLower : 8 ≤ Nat.card (E →ₐ[K] E) := by
      classical
      letI : Fintype (L ≃ₐ[K] L) := Fintype.ofFinite (L ≃ₐ[K] L)
      letI : Fintype (Bool × (L ≃ₐ[K] L)) := inferInstance
      have hle : Fintype.card (Bool × (L ≃ₐ[K] L)) ≤ Fintype.card (E →ₐ[K] E) :=
        Fintype.card_le_of_injective Φ hΦ_inj
      have hcardProd : Fintype.card (Bool × (L ≃ₐ[K] L)) = 8 := by
        have hcardAut' : Fintype.card (L ≃ₐ[K] L) = 4 := by
          simpa [Nat.card_eq_fintype_card] using hcardAut
        simp [Fintype.card_prod, hcardAut']
      -- Convert the Fintype inequality back to `Nat.card`.
      simpa [Nat.card_eq_fintype_card, hcardProd] using hle

    have hUpper : Nat.card (E →ₐ[K] E) ≤ Module.finrank K E := by
      simpa using (card_algHom_le_finrank K E E)

    have hcardAlgHom : Nat.card (E →ₐ[K] E) = Module.finrank K E := by
      apply le_antisymm hUpper
      -- `finrank K E = 8 ≤ Nat.card (E →ₐ[K] E)`.
      simpa [hfinrankKE] using hLower

    have hcardAutE : Nat.card (E ≃ₐ[K] E) = Module.finrank K E := by
      -- Use `algEquivEquivAlgHom` to turn `AlgEquiv` into `AlgHom`.
      have hcongr : Nat.card (E ≃ₐ[K] E) = Nat.card (E →ₐ[K] E) :=
        Nat.card_congr (algEquivEquivAlgHom K E).toEquiv
      exact hcongr.trans hcardAlgHom

    -- Conclude via the cardinality criterion.
    exact IsGalois.of_card_aut_eq_finrank (F := K) (E := E) (by simpa using hcardAutE)

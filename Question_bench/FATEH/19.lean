import Mathlib

namespace FATEH19

open Equiv Equiv.Perm

/-- A monoid hom `ℤˣ →* Equiv.Perm (Fin 2)` sending `-1` to the transposition `swap 0 1`.

This is a convenient, explicit "parity corrector" used to turn any permutation into an even one
after adding two extra points. -/
noncomputable def unitsToPermFin2 : ℤˣ →* Equiv.Perm (Fin 2) where
  toFun u := if u = 1 then 1 else Equiv.swap (0 : Fin 2) 1
  map_one' := by simp
  map_mul' := by
    intro u v
    rcases Int.units_eq_one_or u with rfl | rfl <;>
      rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp

@[simp]
theorem sign_unitsToPermFin2 (u : ℤˣ) : Equiv.Perm.sign (unitsToPermFin2 u) = u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [unitsToPermFin2]
  ·
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    simp [unitsToPermFin2, Equiv.Perm.sign_swap h01]

/-- The underlying hom `Equiv.Perm α →* Equiv.Perm (α ⊕ Fin 2)` for `evenifyPerm`. -/
noncomputable def evenifyPermAux (α : Type*) [Fintype α] [DecidableEq α] :
    Equiv.Perm α →* Equiv.Perm (α ⊕ Fin 2) where
  toFun σ := Equiv.Perm.sumCongr σ (unitsToPermFin2 (Equiv.Perm.sign σ))
  map_one' := by simp [unitsToPermFin2]
  map_mul' := by
    intro σ τ
    simp [Equiv.Perm.sumCongr_mul]

/-- Turn any permutation into an even permutation by appending a parity correction on `Fin 2`. -/
noncomputable def evenifyPerm (α : Type*) [Fintype α] [DecidableEq α] :
    Equiv.Perm α →* alternatingGroup (α ⊕ Fin 2) :=
  (evenifyPermAux α).codRestrict (alternatingGroup (α ⊕ Fin 2)) (by
    intro σ
    -- The total sign is `sign σ * sign σ = 1`.
    simp [evenifyPermAux, Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_sumCongr,
      Int.units_mul_self])

@[simp]
theorem evenifyPerm_coe (α : Type*) [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    ((evenifyPerm α σ : alternatingGroup (α ⊕ Fin 2)) : Equiv.Perm (α ⊕ Fin 2)) =
      evenifyPermAux α σ :=
  rfl

/-- `evenifyPerm` is injective: restricting to `Sum.inl` recovers the original permutation. -/
theorem evenifyPerm_injective (α : Type*) [Fintype α] [DecidableEq α] :
    Function.Injective (evenifyPerm α) := by
  intro σ τ hστ
  have hσt : evenifyPermAux α σ = evenifyPermAux α τ := congrArg Subtype.val hστ
  ext x
  have hx :
      evenifyPermAux α σ (Sum.inl x) = evenifyPermAux α τ (Sum.inl x) :=
    congrArg (fun p : Equiv.Perm (α ⊕ Fin 2) => p (Sum.inl x)) hσt
  simpa [evenifyPermAux] using hx

end FATEH19

/-- Prove that any finite group is isomorphic to a subgroup of $A_n$ for some $n$. -/
theorem exists_subgroup_alternatingGroup_mulEquiv {G : Type} [Group G] [Finite G] :
    ∃ (n : ℕ) (H : Subgroup (alternatingGroup (Fin n))), Nonempty (G ≃* H) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : DecidableEq G := Classical.decEq G
  -- Cayley embedding `G →* Perm G` from the regular action.
  let cayley : G →* Equiv.Perm G := MulAction.toPermHom G G
  have hcayley : Function.Injective cayley := MulAction.toPerm_injective
  -- Evenify, then transport along a `Fintype` equivalence to `Fin n`.
  let n : ℕ := Fintype.card (G ⊕ Fin 2)
  let e : (G ⊕ Fin 2) ≃ Fin n := Fintype.equivFin (G ⊕ Fin 2)
  let f : G →* alternatingGroup (Fin n) :=
    (Equiv.altCongrHom e).toMonoidHom.comp ((FATEH19.evenifyPerm G).comp cayley)
  have hf : Function.Injective f :=
    (Equiv.altCongrHom e).injective.comp ((FATEH19.evenifyPerm_injective G).comp hcayley)
  refine ⟨n, f.range, ?_⟩
  exact ⟨MonoidHom.ofInjective hf⟩

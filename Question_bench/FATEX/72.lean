import Mathlib

/-- The krull dimension of module, defined as `krullDim` of its support. -/
noncomputable def Module.supportDim (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] : WithBot ℕ∞ :=
  Order.krullDim (Module.support R M)

section

open CategoryTheory Abelian

variable {R : Type} [CommRing R]

instance : CategoryTheory.HasExt.{0} (ModuleCat.{0} R) :=
  CategoryTheory.hasExt_of_enoughProjectives (ModuleCat R)

noncomputable def moduleDepth (N M : ModuleCat.{0} R) : ℕ∞ :=
  sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (CategoryTheory.Abelian.Ext.{0} N M i)}

noncomputable def Ideal.depth (I : Ideal R) (M : ModuleCat.{0} R) : ℕ∞ :=
  moduleDepth (ModuleCat.of R (R ⧸ I)) M

noncomputable def IsLocalRing.depth [IsLocalRing R] (M : ModuleCat.{0} R) : ℕ∞ :=
  (IsLocalRing.maximalIdeal R).depth M

class ModuleCat.IsCohenMacaulay [IsLocalRing R] (M : ModuleCat.{0} R) : Prop where
  depth_eq_dim : Subsingleton M ∨ Module.supportDim R M = IsLocalRing.depth M

variable (R)

class Module.IsCohenMacaulay (M : Type) [AddCommGroup M] [Module R M] : Prop where
  depth_eq_dim : ∀ p : Ideal R, ∀ (_ : p.IsPrime), (ModuleCat.of (Localization.AtPrime p)
    (LocalizedModule.AtPrime p M)).IsCohenMacaulay

end

open TensorProduct

/--
Let \( R \) be a Noetherian ring. Let \( M \) be a Cohen-Macaulay module over \( R \).
Then \( M \otimes_R R[x_1, \dots, x_n] \) is a Cohen-Macaulay module over \( R[x_1, \dots, x_n] \).
-/
theorem isCohenMacaulay_extendScalars_over_mvPolynomial_of_isCohenMacaulay
    (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    [IsNoetherianRing R] [Module.IsCohenMacaulay R M] (n : ℕ) :
    Module.IsCohenMacaulay (MvPolynomial (Fin n) R) ((MvPolynomial (Fin n) R) ⊗[R] M) := by
  sorry

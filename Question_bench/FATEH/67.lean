import Mathlib

open Polynomial

noncomputable section

instance : Fact (Nat.Prime 7) := by decide

abbrev K := ZMod 7
abbrev f : Polynomial K := X ^ (3 : ℕ) - 2
abbrev F := AdjoinRoot f

-- `X^3 - 2` has no root in `ZMod 7`, so it is irreducible.
lemma irreducible_X_pow_sub_C_zmod7 : Irreducible (f : Polynomial K) := by
  have h : ∀ b : K, b ^ (3 : ℕ) ≠ (2 : K) := by decide
  simpa using (X_pow_sub_C_irreducible_of_prime (K:=K) (p:=3) (by decide) h)

-- The tensor product is finite over `ZMod 7`, hence Artinian.
lemma isArtinian_tensorProduct_adjoinRoot : IsArtinianRing (TensorProduct K F F) := by
  classical
  have hmonic : (f : Polynomial K).Monic := by
    simpa using (monic_X_pow_sub_C (2 : K) (by decide : (3 : ℕ) ≠ 0))
  have hfinite : Module.Finite K F := by
    simpa using (Polynomial.Monic.finite_adjoinRoot (R:=K) (g:=f) hmonic)
  haveI : Module.Finite K F := hfinite
  haveI : Module.Finite K (TensorProduct K F F) := by infer_instance
  haveI : IsArtinianRing K := by infer_instance
  exact IsArtinianRing.of_finite K (TensorProduct K F F)

-- Base change of a separable field extension is reduced.
lemma isReduced_tensorProduct_adjoinRoot : IsReduced (TensorProduct K F F) := by
  classical
  have h_irred : Irreducible (f : Polynomial K) := irreducible_X_pow_sub_C_zmod7
  letI : Fact (Irreducible (f : Polynomial K)) := ⟨h_irred⟩
  have hmonic : (f : Polynomial K).Monic := by
    simpa using (monic_X_pow_sub_C (2 : K) (by decide : (3 : ℕ) ≠ 0))
  have hfinite : Module.Finite K F := by
    simpa using (Polynomial.Monic.finite_adjoinRoot (R:=K) (g:=f) hmonic)
  haveI : Module.Finite K F := hfinite
  haveI : Algebra.IsAlgebraic K F := by infer_instance
  haveI : PerfectField K := by infer_instance
  haveI : Algebra.IsSeparable K F := by infer_instance
  haveI : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  haveI : Algebra.EssFiniteType K F := by infer_instance
  haveI : Algebra.FormallyUnramified F (TensorProduct K F F) := by infer_instance
  haveI : Algebra.EssFiniteType F (TensorProduct K F F) := by infer_instance
  simpa using
    (Algebra.FormallyUnramified.isReduced_of_field (K:=F) (A:=TensorProduct K F F))

/-
Prove that the prime ideals of $\mathbb{F}_7[\alpha] \otimes_{\mathbb{F}_7} \mathbb{F}_7[\alpha]$ are principal, where $\alpha^3 = 2$.
-/
theorem isPrincipal_of_ideal_tensor_zMod_seven
    (p : Ideal (TensorProduct (ZMod 7) (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7)))
    (AdjoinRoot (X ^ 3 - 2 : Polynomial (ZMod 7))))) [p.IsPrime] : p.IsPrincipal := by
  classical
  haveI : IsArtinianRing (TensorProduct K F F) := isArtinian_tensorProduct_adjoinRoot
  haveI : IsReduced (TensorProduct K F F) := isReduced_tensorProduct_adjoinRoot
  haveI : IsSemisimpleRing (TensorProduct K F F) :=
    IsArtinianRing.isSemisimpleRing_of_isReduced (R:=TensorProduct K F F)
  haveI : IsPrincipalIdealRing (TensorProduct K F F) := by infer_instance
  simpa using (IsPrincipalIdealRing.principal p)

end

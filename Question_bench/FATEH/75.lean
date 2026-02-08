import Mathlib

/--Suppose \( A \) and \( B \) are commutative rings containing a field \( k \), with \( B \)
finitely generated over \( k \) as a ring. If \( \varphi : A \to B \) is a ring homomorphism with
\( \varphi|_k = \text{Id} \) and if \( Q \subset B \) is a maximal ideal, prove that \( \varphi^{-1}
(Q) \subset A \) is a maximal ideal.-/
-- Transport `IsField` along a ring equivalence.
lemma isField_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : IsField S) : IsField R := by
  classical
  refine { exists_pair_ne := ?_, mul_comm := ?_, mul_inv_cancel := ?_ }
  · rcases h.exists_pair_ne with ⟨x, y, hxy⟩
    refine ⟨e.symm x, e.symm y, ?_⟩
    intro h'
    apply hxy
    simpa using congrArg e h'
  · intro x y
    apply e.injective
    simpa [map_mul] using h.mul_comm (e x) (e y)
  · intro a ha
    have ha' : e a ≠ 0 := by
      intro h0
      apply ha
      exact e.injective (by simpa using h0)
    rcases h.mul_inv_cancel ha' with ⟨b, hb⟩
    refine ⟨e.symm b, ?_⟩
    apply e.injective
    simpa [map_mul] using hb

-- Residue fields of maximal ideals of finite type k-algebras are finite over k.
lemma residue_field_module_finite {B k : Type*} [CommRing B] [Field k] [Algebra k B]
    [Algebra.FiniteType k B] (Q : Ideal B) [Q.IsMaximal] :
    Module.Finite k (B ⧸ Q) := by
  classical
  letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
  simpa using
    (finite_of_algHom_finiteType_of_isJacobsonRing (K := k) (L := B ⧸ Q) (A := B ⧸ Q)
      (f := AlgHom.id k (B ⧸ Q)))

theorem comap_isMaximal_of_finiteType {A B k : Type} [CommRing A] [CommRing B] [Field k] [Algebra k A] [Algebra k B]
    [Algebra.FiniteType k B] (φ : A →ₐ[k] B) (Q : Ideal B) [hQ : Q.IsMaximal] :
    (Ideal.comap φ Q).IsMaximal := by
  classical
  letI : Field (B ⧸ Q) := Ideal.Quotient.field Q
  have hfinite : Module.Finite k (B ⧸ Q) := residue_field_module_finite (B := B) (k := k) Q
  haveI : Module.Finite k (B ⧸ Q) := hfinite
  haveI : Algebra.IsAlgebraic k (B ⧸ Q) := by infer_instance
  let ψ : A →ₐ[k] (B ⧸ Q) := (Ideal.Quotient.mkₐ k Q).comp φ
  have hker : RingHom.ker ψ = Ideal.comap φ Q := by
    ext x; simp [ψ, Ideal.Quotient.eq_zero_iff_mem]
  have hrange_field : IsField (AlgHom.range ψ) := by
    simpa using (Subalgebra.isField_of_algebraic (A := AlgHom.range ψ))
  have hquot_field : IsField (A ⧸ RingHom.ker ψ) := by
    exact isField_of_ringEquiv (Ideal.quotientKerEquivRange ψ).toRingEquiv hrange_field
  have hmax : (RingHom.ker ψ).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient (RingHom.ker ψ)).2 hquot_field
  simpa [hker] using hmax

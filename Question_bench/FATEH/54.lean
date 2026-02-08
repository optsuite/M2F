import Mathlib
import Question_bench.FATEH.«45»

open IntermediateField RatFunc
open scoped Polynomial

noncomputable section

abbrev K := GaloisField 2 2
abbrev L := RatFunc K

set_option maxHeartbeats 400000 in
-- Higher limit needed for simp+ring normalization of polynomial compositions.
lemma comp_X_pow_four_add_X {L : Type*} [Field L] [CharP L 2] (t : L) :
    (Polynomial.X ^ 4 + Polynomial.X : L[X]).comp (Polynomial.X + Polynomial.C t)
      = Polynomial.X ^ 4 + Polynomial.X + Polynomial.C (t ^ 4 + t) := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hpow : (Polynomial.X + Polynomial.C t) ^ 4 =
      (Polynomial.X : L[X]) ^ 4 + (Polynomial.C t) ^ 4 := by
    simpa using (add_pow_char_pow (R := L[X]) (p := 2) (n := 2)
      (x := (Polynomial.X : L[X])) (y := Polynomial.C t))
  simp [Polynomial.comp, hpow, Polynomial.C_add, Polynomial.C_pow]
  ring

set_option maxHeartbeats 400000 in
-- Higher limit needed for simp+ring normalization on the splitting-field proof.
/-- Let $\mathbb{F}_4$ be the field with $4$ elements, $t$ a transcendental over $\mathbb{F}_4$,
and $F =\mathbb{F}_4(t^4 + t)$ and $K =\mathbb{F}_4(t)$. Show that $K$ is Galois over $F$. -/
theorem isGalois_galoisField_adjoin_X_pow_four_add_X :
    IsGalois (GaloisField 2 2)⟮(X ^ 4 + X : RatFunc (GaloisField 2 2))⟯
    (RatFunc (GaloisField 2 2)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  haveI : Fintype K := Fintype.ofFinite K
  change IsGalois (K⟮(RatFunc.X ^ 4 + RatFunc.X : L)⟯) L
  let F : IntermediateField K L := K⟮(RatFunc.X ^ 4 + RatFunc.X : L)⟯
  change IsGalois F L
  let t : F :=
    ⟨RatFunc.X ^ 4 + RatFunc.X,
      (IntermediateField.subset_adjoin (F := K) ({RatFunc.X ^ 4 + RatFunc.X} : Set L)) (by simp)⟩
  have ht : (algebraMap F L t) = (RatFunc.X ^ 4 + RatFunc.X : L) := by
    simp [t]
  let P : F[X] := Polynomial.X ^ 4 + Polynomial.X - Polynomial.C t
  have hsep : P.Separable := by
    simpa [P, sub_eq_add_neg] using
      (Polynomial.separable_C_mul_X_pow_add_C_mul_X_add_C' (R := F) (p := 2) (n := 4)
        (a := (1 : F)) (b := (1 : F)) (c := (-t)) (hn := by decide)
        (hb := (isUnit_one : IsUnit (1 : F))))
  have hsplit : (P.map (algebraMap F L)).Splits := by
    have hcard : Fintype.card K = 4 := by
      simpa [Nat.card_eq_fintype_card] using
        (GaloisField.card (p := 2) (n := 2) (by decide))
    have hsplitK : (Polynomial.X ^ 4 - Polynomial.X : K[X]).Splits := by
      have h := (FiniteField.splits_X_pow_card_sub_X (K := K) (p := 2))
      simpa [hcard] using h
    have hsplitL :
        (Polynomial.map (algebraMap K L) (Polynomial.X ^ 4 - Polynomial.X : K[X])).Splits :=
      Polynomial.Splits.map (i := algebraMap K L) hsplitK
    have hsplitL' : (Polynomial.X ^ 4 + Polynomial.X : L[X]).Splits := by
      simpa [CharTwo.sub_eq_add] using hsplitL
    have hcomp :
        (P.map (algebraMap F L)) =
          (Polynomial.X ^ 4 + Polynomial.X : L[X]).comp
            (Polynomial.X + Polynomial.C (RatFunc.X)) := by
      have hcomp' :
          (Polynomial.X ^ 4 + Polynomial.X : L[X]).comp (Polynomial.X + Polynomial.C (RatFunc.X)) =
            Polynomial.X ^ 4 + Polynomial.X + Polynomial.C ((RatFunc.X : L) ^ 4 + RatFunc.X) := by
        simpa using (comp_X_pow_four_add_X (t := (RatFunc.X : L)))
      have hPmap :
          (P.map (algebraMap F L)) =
            Polynomial.X ^ 4 + Polynomial.X + Polynomial.C ((RatFunc.X : L) ^ 4 + RatFunc.X) := by
        simp [P, ht, CharTwo.sub_eq_add]
      exact hPmap.trans hcomp'.symm
    simpa [hcomp] using
      (Polynomial.Splits.comp_X_add_C
        (f := (Polynomial.X ^ 4 + Polynomial.X : L[X])) hsplitL' (RatFunc.X))
  have hroot : IntermediateField.adjoin F (P.rootSet L) = ⊤ := by
    have hmonic : P.Monic := by
      have hdeg : (Polynomial.X - Polynomial.C t : F[X]).degree < 4 := by
        simp [Polynomial.degree_X_sub_C, show (1 : WithBot ℕ) < 4 from by decide]
      have h := (Polynomial.monic_X_pow_add (n := 4) (p := (Polynomial.X - Polynomial.C t)) hdeg)
      simpa [P, sub_eq_add_neg, add_assoc] using h
    have hPmap_ne : P.map (algebraMap F L) ≠ 0 := (hmonic.map (algebraMap F L)).ne_zero
    have hXroot : (RatFunc.X : L) ∈ P.rootSet L := by
      refine (Polynomial.mem_rootSet'.2 ?_)
      refine ⟨hPmap_ne, ?_⟩
      simp [P, ht, Polynomial.aeval_add, Polynomial.aeval_sub, Polynomial.aeval_X_pow,
        Polynomial.aeval_X, Polynomial.aeval_C]
    have hsubset : ({RatFunc.X} : Set L) ⊆ P.rootSet L := by
      intro x hx
      have hx' : x = RatFunc.X := by simpa [Set.mem_singleton_iff] using hx
      simpa [hx'] using hXroot
    have htop : IntermediateField.adjoin F ({RatFunc.X} : Set L) = ⊤ := by
      have hprim : IntermediateField.adjoin K ({RatFunc.X} : Set L) = ⊤ := by
        dsimp [L]
        exact ratfunc_adjoin_X_eq_top (F := K)
      exact
        (IntermediateField.adjoin_eq_top_of_adjoin_eq_top (F := K) (E := F) (K := L)
          (S := ({RatFunc.X} : Set L)) hprim)
    apply top_unique
    have hle :
        IntermediateField.adjoin F ({RatFunc.X} : Set L) ≤
          IntermediateField.adjoin F (P.rootSet L) := by
      refine (IntermediateField.adjoin_le_iff (F := F) (E := L)).2 ?_
      intro x hx
      exact IntermediateField.subset_adjoin (F := F) (S := P.rootSet L) (hsubset hx)
    simpa [htop] using hle
  haveI : P.IsSplittingField F L :=
    (isSplittingField_iff_intermediateField (K := F) (L := L) (p := P)).2 ⟨hsplit, hroot⟩
  exact IsGalois.of_separable_splitting_field (p := P) hsep

end

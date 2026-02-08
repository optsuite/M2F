import Mathlib

open IntermediateField
open scoped Polynomial

/-! Helper lemmas for the uniqueness of the quadratic extension. -/

/-- Adjoining a nonzero scalar multiple of `i` gives the same intermediate field. -/
lemma adjoin_scalar_mul_i_eq (F : Type) [Field F] (i : AlgebraicClosure F) {b : F} (hb : b ≠ 0) :
    F⟮(algebraMap F (AlgebraicClosure F) b) * i⟯ = F⟮i⟯ := by
  classical
  apply le_antisymm
  · refine (IntermediateField.adjoin_simple_le_iff).2 ?_
    have hi_mem : i ∈ F⟮i⟯ := IntermediateField.mem_adjoin_simple_self (F := F) (α := i)
    have hb_mem : (algebraMap F (AlgebraicClosure F) b) ∈ F⟮i⟯ := by
      exact IntermediateField.algebraMap_mem (S := F⟮i⟯) b
    exact IntermediateField.mul_mem F⟮i⟯ hb_mem hi_mem
  · refine (IntermediateField.adjoin_simple_le_iff).2 ?_
    have hbi_mem :
        (algebraMap F (AlgebraicClosure F) b) * i ∈
          F⟮(algebraMap F (AlgebraicClosure F) b) * i⟯ :=
      IntermediateField.mem_adjoin_simple_self
        (F := F) (α := (algebraMap F (AlgebraicClosure F) b) * i)
    have hb_mem :
        (algebraMap F (AlgebraicClosure F) b) ∈
          F⟮(algebraMap F (AlgebraicClosure F) b) * i⟯ := by
      exact
        IntermediateField.algebraMap_mem
          (S := F⟮(algebraMap F (AlgebraicClosure F) b) * i⟯) b
    have hb_inv :
        (algebraMap F (AlgebraicClosure F) b)⁻¹ ∈
          F⟮(algebraMap F (AlgebraicClosure F) b) * i⟯ :=
      IntermediateField.inv_mem _ hb_mem
    have hmul :
        (algebraMap F (AlgebraicClosure F) b)⁻¹ *
            ((algebraMap F (AlgebraicClosure F) b) * i) ∈
          F⟮(algebraMap F (AlgebraicClosure F) b) * i⟯ :=
      IntermediateField.mul_mem _ hb_inv hbi_mem
    have hbne : (algebraMap F (AlgebraicClosure F) b) ≠ 0 := by
      exact
        (FaithfulSMul.algebraMap_eq_zero_iff (R := F) (A := AlgebraicClosure F) (r := b)).not.mpr hb
    simpa [inv_mul_cancel_left₀ hbne] using hmul

/-- In a quadratic simple extension, any element is linear in the generator. -/
lemma exists_add_mul_of_mem_adjoin_square (F : Type) [Field F] {β α : AlgebraicClosure F}
    (hβ2 : β ^ 2 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)))
    (hβ : ¬ β ∈ (⊥ : IntermediateField F (AlgebraicClosure F)))
    (hα : α ∈ F⟮β⟯) :
    ∃ u v : F, α = algebraMap F (AlgebraicClosure F) u +
      algebraMap F (AlgebraicClosure F) v * β := by
  classical
  obtain ⟨a, ha⟩ := (IntermediateField.mem_bot).1 hβ2
  have hβalg : IsAlgebraic F β :=
    (Algebra.IsAlgebraic.isAlgebraic (R := F) (A := AlgebraicClosure F) β)
  have hβint : IsIntegral F β := IsAlgebraic.isIntegral hβalg
  have hdiv : minpoly F β ∣ (Polynomial.X ^ 2 - Polynomial.C a) := by
    apply minpoly.dvd
    simp [ha]
  have hdeg_le : (minpoly F β).natDegree ≤ 2 := by
    have hne : (Polynomial.X ^ 2 - Polynomial.C a : F[X]) ≠ 0 :=
      (Polynomial.monic_X_pow_sub_C a (by decide)).ne_zero
    have hdeg := Polynomial.natDegree_le_of_dvd hdiv hne
    simpa [Polynomial.natDegree_X_pow_sub_C] using hdeg
  have hdeg_ge : 2 ≤ (minpoly F β).natDegree := by
    have hβrange : β ∉ (algebraMap F (AlgebraicClosure F)).range := by
      intro h
      exact hβ ((IntermediateField.mem_bot).2 h)
    exact
      (minpoly.two_le_natDegree_iff (A := F) (B := AlgebraicClosure F) (x := β) hβint).2 hβrange
  have hdeg : (minpoly F β).natDegree = 2 := le_antisymm hdeg_le hdeg_ge
  let pb := IntermediateField.adjoin.powerBasis (K := F) (x := β) hβint
  have hdim : pb.dim = 2 := by
    simp [pb, hdeg]
  let x : F⟮β⟯ := ⟨α, hα⟩
  obtain ⟨f, hfdeg, hfx⟩ := pb.exists_eq_aeval x
  have hfdeg' : f.natDegree < 2 := by
    simpa [hdim] using hfdeg
  have hαeq : α = Polynomial.aeval β f := by
    have h' :
        (IntermediateField.val (S := F⟮β⟯) (K := F) (L := AlgebraicClosure F)) x =
          (IntermediateField.val (S := F⟮β⟯) (K := F) (L := AlgebraicClosure F))
            (Polynomial.aeval pb.gen f) :=
      congrArg
        (fun y => (IntermediateField.val (S := F⟮β⟯) (K := F) (L := AlgebraicClosure F)) y) hfx
    have hright :
        (IntermediateField.val (S := F⟮β⟯) (K := F) (L := AlgebraicClosure F))
            (Polynomial.aeval pb.gen f) =
          Polynomial.aeval β f := by
      simpa [pb] using
        (Polynomial.aeval_algHom_apply
          (IntermediateField.val (S := F⟮β⟯) (K := F) (L := AlgebraicClosure F)) pb.gen f).symm
    simpa [x, hright] using h'
  have hsum :
      Polynomial.aeval β f =
        algebraMap F (AlgebraicClosure F) (f.coeff 0) +
          algebraMap F (AlgebraicClosure F) (f.coeff 1) * β := by
    simpa [Finset.sum_range_succ, Finset.sum_range_one, Algebra.smul_def, pow_zero, pow_one,
      mul_comm, mul_left_comm, mul_assoc] using
      (Polynomial.aeval_eq_sum_range' (p := f) (n := 2) (hn := hfdeg') (x := β))
  refine ⟨f.coeff 0, f.coeff 1, ?_⟩
  simpa [hαeq] using hsum

/-- In characteristic not `2`, a witness forces `α^4` to be a negative square from `F`. -/
lemma neg_square_of_adjoin_eq (F : Type) [Field F] {α : AlgebraicClosure F}
    (h4 : α ^ 4 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)))
    (h2 : ¬ α ^ 2 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)))
    (hEq : F⟮α⟯ = F⟮α ^ 2⟯) (_hchar : (2 : F) ≠ 0) :
    ∃ b : F, b ≠ 0 ∧ α ^ 4 = -(algebraMap F (AlgebraicClosure F) b) ^ 2 := by
  classical
  set β : AlgebraicClosure F := α ^ 2
  have hβ2eq : β ^ 2 = α ^ 4 := by
    calc
      β ^ 2 = (α ^ 2) ^ 2 := by simp [β]
      _ = α ^ (2 * 2) := by simpa using (pow_mul α 2 2).symm
      _ = α ^ 4 := by simp
  have hβ2 : β ^ 2 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) := by
    simpa [hβ2eq] using h4
  have hβ_not : ¬ β ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) := by
    simpa [β] using h2
  have hα_mem : α ∈ F⟮β⟯ := by
    simpa [β, hEq] using (IntermediateField.mem_adjoin_simple_self (F := F) (α := α))
  obtain ⟨u, v, hαuv⟩ :=
    exists_add_mul_of_mem_adjoin_square (F := F) (β := β) (α := α) hβ2 hβ_not hα_mem
  obtain ⟨a, ha⟩ := (IntermediateField.mem_bot).1 hβ2
  have hβ2' : β ^ 2 = algebraMap F (AlgebraicClosure F) a := ha.symm
  set u' : AlgebraicClosure F := algebraMap F (AlgebraicClosure F) u
  set v' : AlgebraicClosure F := algebraMap F (AlgebraicClosure F) v
  set a' : AlgebraicClosure F := algebraMap F (AlgebraicClosure F) a
  have hsq :
      β = u' ^ 2 + v' ^ 2 * a' + (2 : AlgebraicClosure F) * u' * v' * β := by
    calc
      β = α ^ 2 := by simp [β]
      _ = (u' + v' * β) ^ 2 := by simp [hαuv, u', v']
      _ =
          u' ^ 2 + v' ^ 2 * β ^ 2 +
            (2 : AlgebraicClosure F) * u' * v' * β := by
        ring
      _ =
          u' ^ 2 + v' ^ 2 * a' +
            (2 : AlgebraicClosure F) * u' * v' * β := by
        simp [a', hβ2']
  have hmul :
      (1 - (2 : AlgebraicClosure F) * u' * v') * β = u' ^ 2 + v' ^ 2 * a' := by
    have hsq'' :
        β - (2 : AlgebraicClosure F) * u' * v' * β = u' ^ 2 + v' ^ 2 * a' := by
      calc
        β - (2 : AlgebraicClosure F) * u' * v' * β =
            (u' ^ 2 + v' ^ 2 * a' + (2 : AlgebraicClosure F) * u' * v' * β) -
              (2 : AlgebraicClosure F) * u' * v' * β := by
          nth_rewrite 1 [hsq]
          rfl
        _ = u' ^ 2 + v' ^ 2 * a' := by
          ring
    calc
      (1 - (2 : AlgebraicClosure F) * u' * v') * β =
          β - (2 : AlgebraicClosure F) * u' * v' * β := by
        ring
      _ = u' ^ 2 + v' ^ 2 * a' := hsq''
  set c : F := 1 - 2 * u * v
  set d : F := u ^ 2 + v ^ 2 * a
  have hmul' :
      (algebraMap F (AlgebraicClosure F) c) * β =
        algebraMap F (AlgebraicClosure F) d := by
    simpa [c, d, u', v', a'] using hmul
  have hc : c = 0 := by
    by_contra hc
    have hc' :
        (algebraMap F (AlgebraicClosure F) c : AlgebraicClosure F) ≠ 0 := by
      exact
        (FaithfulSMul.algebraMap_eq_zero_iff (R := F) (A := AlgebraicClosure F) (r := c)).not.mpr hc
    have hβ_eq :
        β =
          (algebraMap F (AlgebraicClosure F) c)⁻¹ *
            algebraMap F (AlgebraicClosure F) d := by
      calc
        β =
            (algebraMap F (AlgebraicClosure F) c)⁻¹ *
              ((algebraMap F (AlgebraicClosure F) c) * β) := by
          symm
          simpa [mul_assoc] using (inv_mul_cancel_left₀ hc' β)
        _ =
            (algebraMap F (AlgebraicClosure F) c)⁻¹ *
              algebraMap F (AlgebraicClosure F) d := by
          simp [hmul']
    have hβ_mem : β ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) := by
      have hc_mem :
          (algebraMap F (AlgebraicClosure F) c)⁻¹ ∈
            (⊥ : IntermediateField F (AlgebraicClosure F)) := by
        have hc_mem' :
            (algebraMap F (AlgebraicClosure F) c) ∈
              (⊥ : IntermediateField F (AlgebraicClosure F)) :=
          IntermediateField.algebraMap_mem
            (S := (⊥ : IntermediateField F (AlgebraicClosure F))) c
        exact IntermediateField.inv_mem _ hc_mem'
      have hd_mem :
          algebraMap F (AlgebraicClosure F) d ∈
            (⊥ : IntermediateField F (AlgebraicClosure F)) :=
        IntermediateField.algebraMap_mem
          (S := (⊥ : IntermediateField F (AlgebraicClosure F))) d
      have hβ_mem' :
          (algebraMap F (AlgebraicClosure F) c)⁻¹ *
              algebraMap F (AlgebraicClosure F) d ∈
            (⊥ : IntermediateField F (AlgebraicClosure F)) :=
        IntermediateField.mul_mem _ hc_mem hd_mem
      simpa [hβ_eq] using hβ_mem'
    exact hβ_not hβ_mem
  have h2uv : (2 : F) * u * v = 1 := by
    have h' : 1 - 2 * u * v = 0 := by simpa [c] using hc
    exact (sub_eq_zero.mp h').symm
  have hv : v ≠ 0 := by
    intro hv
    have h2uv' : (0 : F) = 1 := by
      calc
        (0 : F) = (2 : F) * u * v := by simp [hv]
        _ = 1 := h2uv
    exact zero_ne_one h2uv'
  have hu : u ≠ 0 := by
    intro hu
    have h2uv' : (0 : F) = 1 := by
      calc
        (0 : F) = (2 : F) * u * v := by simp [hu]
        _ = 1 := h2uv
    exact zero_ne_one h2uv'
  have h2uv' :
      (2 : AlgebraicClosure F) * u' * v' = 1 := by
    have h2uv_map :=
      congrArg (fun t => (algebraMap F (AlgebraicClosure F)) t) h2uv
    have h2uv_map' :
        (algebraMap F (AlgebraicClosure F) 2) * u' * v' = 1 := by
      simpa [u', v', mul_assoc] using h2uv_map
    simpa [u', v'] using h2uv_map'
  have hsq' : β = u' ^ 2 + v' ^ 2 * a' + β := by
    simpa [h2uv'] using hsq
  have hcoeff' : u' ^ 2 + v' ^ 2 * a' = 0 := by
    have h' := congrArg (fun t => t - β) hsq'
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, eq_comm] using h'
  have hcoeff_map :
      algebraMap F (AlgebraicClosure F) (u ^ 2 + v ^ 2 * a) = 0 := by
    simpa [u', v', a', mul_comm, mul_left_comm, mul_assoc] using hcoeff'
  have hcoeffF : u ^ 2 + v ^ 2 * a = 0 := by
    exact
      (FaithfulSMul.algebraMap_eq_zero_iff (R := F) (A := AlgebraicClosure F)
        (r := u ^ 2 + v ^ 2 * a)).1 hcoeff_map
  have hcoeffF' : v ^ 2 * a = -u ^ 2 := by
    have h' : v ^ 2 * a + u ^ 2 = 0 := by simpa [add_comm] using hcoeffF
    exact eq_neg_of_add_eq_zero_left h'
  have hcoeffF'' : a = -(u / v) ^ 2 := by
    have hv2 : v ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 hv
    calc
      a = (v ^ 2)⁻¹ * (v ^ 2 * a) := by
        symm
        simpa [mul_assoc] using (inv_mul_cancel_left₀ hv2 a)
      _ = (v ^ 2)⁻¹ * (-u ^ 2) := by
        simp [hcoeffF']
      _ = -(u / v) ^ 2 := by
        simp [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]
  set b : F := u / v
  have hb : b ≠ 0 := by
    intro hb
    have h' : u = 0 ∨ v = 0 := (div_eq_zero_iff).1 (by simpa [b] using hb)
    exact h'.elim hu hv
  have hβ2'' : β ^ 2 = -(algebraMap F (AlgebraicClosure F) b) ^ 2 := by
    calc
      β ^ 2 = algebraMap F (AlgebraicClosure F) a := hβ2'
      _ = -(algebraMap F (AlgebraicClosure F) b) ^ 2 := by
        simp [b, hcoeffF'']
  refine ⟨b, hb, ?_⟩
  simpa [hβ2eq] using hβ2''

/-- If a witness `α` exists, it generates the same field as any fixed `i` with `i^2 = -1`. -/
lemma adjoin_of_witness_eq_fixed_i (F : Type) [Field F] {i α : AlgebraicClosure F}
    (hi : i ^ 2 = -1)
    (h4 : α ^ 4 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)))
    (h2 : ¬ α ^ 2 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)))
    (hEq : F⟮α⟯ = F⟮α ^ 2⟯) :
    F⟮α⟯ = F⟮i⟯ := by
  classical
  by_cases hchar : (2 : F) = 0
  · -- In characteristic `2`, the hypotheses force `α^2 ∈ F`, contradicting `h2`.
    exfalso
    set β : AlgebraicClosure F := α ^ 2
    have hβ2eq : β ^ 2 = α ^ 4 := by
      calc
        β ^ 2 = (α ^ 2) ^ 2 := by simp [β]
        _ = α ^ (2 * 2) := by simpa using (pow_mul α 2 2).symm
        _ = α ^ 4 := by simp
    have hβ2 : β ^ 2 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) := by
      simpa [hβ2eq] using h4
    have hβ_not : ¬ β ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) := by
      simpa [β] using h2
    have hα_mem : α ∈ F⟮β⟯ := by
      simpa [β, hEq] using (IntermediateField.mem_adjoin_simple_self (F := F) (α := α))
    obtain ⟨u, v, hαuv⟩ :=
      exists_add_mul_of_mem_adjoin_square (F := F) (β := β) (α := α) hβ2 hβ_not hα_mem
    obtain ⟨a, ha⟩ := (IntermediateField.mem_bot).1 hβ2
    have hβ2' : β ^ 2 = algebraMap F (AlgebraicClosure F) a := ha.symm
    have hsq :
        β =
          (algebraMap F (AlgebraicClosure F) u) ^ 2 +
            (algebraMap F (AlgebraicClosure F) v) ^ 2 *
              algebraMap F (AlgebraicClosure F) a := by
      calc
        β = α ^ 2 := by simp [β]
        _ = (algebraMap F (AlgebraicClosure F) u +
              algebraMap F (AlgebraicClosure F) v * β) ^ 2 := by
          simp [hαuv]
        _ =
            (algebraMap F (AlgebraicClosure F) u) ^ 2 +
              (algebraMap F (AlgebraicClosure F) v) ^ 2 * β ^ 2 +
              (2 : AlgebraicClosure F) *
                (algebraMap F (AlgebraicClosure F) u) *
                  (algebraMap F (AlgebraicClosure F) v) * β := by
          ring
        _ =
            (algebraMap F (AlgebraicClosure F) u) ^ 2 +
              (algebraMap F (AlgebraicClosure F) v) ^ 2 *
                algebraMap F (AlgebraicClosure F) a := by
          have hchar' : (2 : AlgebraicClosure F) = 0 := by
            change algebraMap F (AlgebraicClosure F) (2 : F) = 0
            exact
              (FaithfulSMul.algebraMap_eq_zero_iff (R := F) (A := AlgebraicClosure F)
                (r := (2 : F))).2 hchar
          simp [hβ2', hchar']
    have hβ_mem : β ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) := by
      refine (IntermediateField.mem_bot).2 ?_
      refine ⟨u ^ 2 + v ^ 2 * a, ?_⟩
      have : β =
          algebraMap F (AlgebraicClosure F) (u ^ 2 + v ^ 2 * a) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hsq
      exact this.symm
    exact hβ_not hβ_mem
  · -- In characteristic not `2`, solve `α^4 = -(b^2)` and compare squares.
    obtain ⟨b, hb, hα4⟩ :=
      neg_square_of_adjoin_eq (F := F) (α := α) h4 h2 hEq hchar
    have hsq : (α ^ 2) ^ 2 = (algebraMap F (AlgebraicClosure F) b * i) ^ 2 := by
      calc
        (α ^ 2) ^ 2 = α ^ (2 * 2) := by simpa using (pow_mul α 2 2).symm
        _ = α ^ 4 := by simp
        _ = -(algebraMap F (AlgebraicClosure F) b) ^ 2 := hα4
        _ = (algebraMap F (AlgebraicClosure F) b * i) ^ 2 := by
          simp [mul_pow, hi, mul_comm]
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsq with hpos | hneg
    · have hfield : F⟮α ^ 2⟯ = F⟮i⟯ := by
        simpa [hpos] using (adjoin_scalar_mul_i_eq (F := F) (i := i) (b := b) hb)
      simpa [hEq] using hfield
    · have hb' : (-b : F) ≠ 0 := by
        exact neg_ne_zero.mpr hb
      have hneg' :
          α ^ 2 =
            algebraMap F (AlgebraicClosure F) (-b) * i := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hneg
      have hfield : F⟮α ^ 2⟯ = F⟮i⟯ := by
        simpa [hneg'] using (adjoin_scalar_mul_i_eq (F := F) (i := i) (b := -b) hb')
      simpa [hEq] using hfield
/-- Show that there is at most one extension \( F(\alpha) \) of a field \( F \) such that
\( \alpha^4 \in F \), \( \alpha^2 \notin F \), and \( F(\alpha) = F(\alpha^2) \). -/
theorem exists_eq_adjoin_and_pow_four_mem_bot_and_not_pow_two_mem_bot (F : Type) [Field F] :
    Subsingleton {M : IntermediateField F (AlgebraicClosure F) //
    ∃ α : AlgebraicClosure F, M = F⟮α⟯ ∧ α ^ 4 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) ∧
    ¬ α ^ 2 ∈ (⊥ : IntermediateField F (AlgebraicClosure F)) ∧ F⟮α⟯ = F⟮α ^ 2⟯} := by
  classical
  refine ⟨?_⟩
  rintro ⟨M, hM⟩ ⟨N, hN⟩
  have hdeg :
      (Polynomial.X ^ 2 + 1 : (AlgebraicClosure F)[X]).degree ≠ 0 := by
    have hdeg' :
        (Polynomial.X ^ 2 + 1 : (AlgebraicClosure F)[X]).degree = 2 := by
      simpa using
        (Polynomial.degree_X_pow_add_C (R := AlgebraicClosure F) (n := 2)
          (a := (1 : AlgebraicClosure F)) (by decide))
    simp [hdeg']
  obtain ⟨i, hi⟩ :=
    IsAlgClosed.exists_root (p := (Polynomial.X ^ 2 + 1 : (AlgebraicClosure F)[X])) hdeg
  have hi' : i ^ 2 = -1 := by
    have hEval : i ^ 2 + 1 = 0 := by
      simpa [Polynomial.IsRoot] using
        (hi : (Polynomial.X ^ 2 + 1 : (AlgebraicClosure F)[X]).IsRoot i)
    exact eq_neg_of_add_eq_zero_left hEval
  rcases hM with ⟨α, rfl, h4, h2, hEq⟩
  rcases hN with ⟨β, rfl, h4', h2', hEq'⟩
  have hMi : (F⟮α⟯ : IntermediateField F (AlgebraicClosure F)) = F⟮i⟯ :=
    adjoin_of_witness_eq_fixed_i (F := F) hi' h4 h2 hEq
  have hNi : (F⟮β⟯ : IntermediateField F (AlgebraicClosure F)) = F⟮i⟯ :=
    adjoin_of_witness_eq_fixed_i (F := F) hi' h4' h2' hEq'
  simp [hMi, hNi]

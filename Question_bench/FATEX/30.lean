import Mathlib

open scoped Polynomial

namespace integrallyClosedIn_of_complement_multiplicatively_closed

variable {B : Type*} [CommRing B] {A : Subring B}

/-- If `x ∉ A` and `x * y ∈ A`, then `y ∈ A` by contrapositive of multiplicative closure. -/
lemma mul_mem_left_iff (h : ∀ (x y : B), x ∉ A → y ∉ A → x * y ∉ A)
    {x y : B} (hx : x ∉ A) (hxy : x * y ∈ A) : y ∈ A := by
  classical
  by_contra hy
  exact (h x y hx hy) hxy

/-- One step of `divX`: if `eval₂` is in `A` and `x ∉ A`, then so is `eval₂` of `divX`. -/
lemma eval2_divX_mem_of_eval2_mem (h : ∀ (x y : B), x ∉ A → y ∉ A → x * y ∉ A)
    {x : B} {p : A[X]} (hx : x ∉ A)
    (hp : Polynomial.eval₂ (algebraMap A B) x p ∈ A) :
    Polynomial.eval₂ (algebraMap A B) x (Polynomial.divX p) ∈ A := by
  have hmem' :
      Polynomial.eval₂ (algebraMap A B) x
        (Polynomial.divX p * Polynomial.X + Polynomial.C (p.coeff 0)) ∈ A := by
    simpa [Polynomial.divX_mul_X_add] using hp
  have hcoeff : algebraMap A B (p.coeff 0) ∈ A := by
    simpa [Algebra.algebraMap_ofSubring] using (SetLike.coe_mem (p.coeff 0))
  have hmul : Polynomial.eval₂ (algebraMap A B) x (Polynomial.divX p * Polynomial.X) ∈ A := by
    have hsub := A.sub_mem hmem' hcoeff
    simpa [Polynomial.eval₂_add, Polynomial.eval₂_C] using hsub
  have hmul' : Polynomial.eval₂ (algebraMap A B) x (Polynomial.divX p) * x ∈ A := by
    simpa [Polynomial.eval₂_mul, Polynomial.eval₂_X] using hmul
  have hmul'' : x * Polynomial.eval₂ (algebraMap A B) x (Polynomial.divX p) ∈ A := by
    simpa [mul_comm] using hmul'
  exact mul_mem_left_iff (h := h) hx hmul''

/-- Iterating `divX` keeps `eval₂` in `A` when the original evaluation is `0`. -/
lemma eval2_iterate_divX_mem (h : ∀ (x y : B), x ∉ A → y ∉ A → x * y ∉ A)
    {x : B} {p : A[X]} (hx : x ∉ A)
    (hp : Polynomial.eval₂ (algebraMap A B) x p = 0) :
    ∀ k, Polynomial.eval₂ (algebraMap A B) x (Nat.iterate Polynomial.divX k p) ∈ A := by
  intro k
  induction k with
  | zero =>
      simpa [Nat.iterate, hp] using (A.zero_mem : (0 : B) ∈ A)
  | succ k hk =>
      have hstep :=
        eval2_divX_mem_of_eval2_mem (h := h) (x := x)
          (p := Nat.iterate Polynomial.divX k p) hx hk
      have hiter :
          Polynomial.divX (Nat.iterate Polynomial.divX k p) =
            Nat.iterate Polynomial.divX k.succ p := by
        simpa using
          (congrArg (fun g => g p)
            (Function.iterate_succ' (f := Polynomial.divX) k)).symm
      simpa [hiter] using hstep

/-- Coefficients of iterated `divX` shift by the number of iterations. -/
lemma coeff_iterate_divX (p : A[X]) (k n : ℕ) :
    (Nat.iterate Polynomial.divX k p).coeff n = p.coeff (n + k) := by
  induction k generalizing p n with
  | zero =>
      simp [Nat.iterate]
  | succ k hk =>
      have := hk (p := Polynomial.divX p) (n := n)
      simpa [Nat.iterate, Polynomial.coeff_divX, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using this

/-- After `natDegree - 1` steps, a monic polynomial of positive degree becomes `X + C (coeff _)`. -/
lemma iterate_divX_eq_X_add_C {p : A[X]} (hp : p.Monic) (hn : 0 < p.natDegree) :
    Nat.iterate Polynomial.divX (p.natDegree - 1) p =
      Polynomial.X + Polynomial.C (p.coeff (p.natDegree - 1)) := by
  classical
  ext n
  cases n with
  | zero =>
      simp [coeff_iterate_divX, Polynomial.coeff_X, Polynomial.coeff_C]
  | succ n =>
      cases n with
      | zero =>
          have hpred : 1 + (p.natDegree - 1) = p.natDegree := by
            simpa [Nat.succ_eq_add_one, Nat.add_comm] using (Nat.succ_pred_eq_of_pos hn)
          simp [coeff_iterate_divX, hpred, hp.coeff_natDegree, Polynomial.coeff_X,
            Polynomial.coeff_C]
      | succ n =>
          have hpred : p.natDegree = (p.natDegree - 1) + 1 := by
            simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hn).symm
          have h1 : 1 < n.succ.succ := by
            exact Nat.succ_lt_succ (Nat.succ_pos _)
          have hlt : p.natDegree < n.succ.succ + (p.natDegree - 1) := by
            calc
              p.natDegree = (p.natDegree - 1) + 1 := hpred
              _ < (p.natDegree - 1) + n.succ.succ := by
                exact Nat.add_lt_add_left h1 _
              _ = n.succ.succ + (p.natDegree - 1) := by
                simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
          have hcoeff0 : p.coeff (n.succ.succ + (p.natDegree - 1)) = 0 := by
            exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
          simp [coeff_iterate_divX, hcoeff0, Polynomial.coeff_X, Polynomial.coeff_C]

end integrallyClosedIn_of_complement_multiplicatively_closed

/--
Let \( A \) be a subring of a ring \( B \), such that the set \( B \setminus A \) is closed under multiplication.
Show that \( A \) is integrally closed in \( B \).
-/
theorem integrallyClosedIn_of_complement_multiplicatively_closed (B : Type) [CommRing B] (A : Subring B)
    (h : ∀ (x y : B), x ∉ A → y ∉ A → x * y ∉ A) : IsIntegrallyClosedIn A B := by
  classical
  refine (isIntegrallyClosedIn_iff).2 ?_
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    simpa [Algebra.algebraMap_ofSubring] using hxy
  · intro x hx
    have hxA : x ∈ A := by
      by_contra hxA
      rcases hx with ⟨p, hpmonic, hpeval⟩
      by_cases hdeg0 : p.natDegree = 0
      · have hp1 : p = (1 : A[X]) := by
          have hcoeff : p.coeff 0 = 1 := by
            simpa [hdeg0] using hpmonic.coeff_natDegree
          have hpC : p = Polynomial.C (p.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
          simpa [hcoeff] using hpC
        have h10 : (1 : B) = 0 := by
          have : Polynomial.eval₂ (algebraMap A B) x (1 : A[X]) = 0 := by
            simpa [hp1] using hpeval
          simpa using this
        have h01 : (0 : B) = 1 := h10.symm
        haveI := subsingleton_of_zero_eq_one h01
        have hxmem : x ∈ A := by
          have hx0 : x = (0 : B) := by
            simpa using (Subsingleton.elim x (0 : B))
          simpa [hx0] using (A.zero_mem : (0 : B) ∈ A)
        exact hxA hxmem
      · have hpos : 0 < p.natDegree := Nat.pos_of_ne_zero hdeg0
        have hmem_iter :
            ∀ k,
              Polynomial.eval₂ (algebraMap A B) x (Nat.iterate Polynomial.divX k p) ∈ A :=
          integrallyClosedIn_of_complement_multiplicatively_closed.eval2_iterate_divX_mem
            (A := A) (B := B) (h := h) hxA hpeval
        set q := Nat.iterate Polynomial.divX (p.natDegree - 1) p
        have hqmem : Polynomial.eval₂ (algebraMap A B) x q ∈ A := by
          simpa [q] using hmem_iter (p.natDegree - 1)
        have hqeq :
            q = Polynomial.X + Polynomial.C (p.coeff (p.natDegree - 1)) := by
          simpa [q] using
            (integrallyClosedIn_of_complement_multiplicatively_closed.iterate_divX_eq_X_add_C
              (A := A) (p := p) hpmonic hpos)
        have hlin :
            Polynomial.eval₂ (algebraMap A B) x
              (Polynomial.X + Polynomial.C (p.coeff (p.natDegree - 1))) ∈ A := by
          simpa [hqeq] using hqmem
        have hlin' : x + algebraMap A B (p.coeff (p.natDegree - 1)) ∈ A := by
          simpa [Polynomial.eval₂_add, Polynomial.eval₂_X, Polynomial.eval₂_C] using hlin
        have hcoeff : algebraMap A B (p.coeff (p.natDegree - 1)) ∈ A := by
          simpa [Algebra.algebraMap_ofSubring] using
            (SetLike.coe_mem (p.coeff (p.natDegree - 1)))
        have hxmem : x ∈ A := by
          have := A.sub_mem hlin' hcoeff
          simpa [add_sub_cancel] using this
        exact hxA hxmem
    refine ⟨⟨x, hxA⟩, ?_⟩
    simp [Algebra.algebraMap_ofSubring]

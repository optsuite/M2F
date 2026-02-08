import Mathlib

open Ideal
open scoped Pointwise
/-
Let $A$ be a Noetherian ring and let $x \in A$ be an element which is
neither a unit nor a zero-divisor. Prove that the ideals $xA$ and $x^nA$
for $n = 1, 2, \dots$ have the same prime divisors:
\[
\operatorname{Ass}_A(A/xA) = \operatorname{Ass}_A(A/x^nA).
\]
-/
-- Multiplying a principal ideal by `a` just multiplies its generator.
lemma smul_span_singleton_eq_span_singleton_mul {A : Type*} [CommRing A] (a b : A) :
    a • (Ideal.span ({b} : Set A)) = (Ideal.span ({a * b} : Set A)) := by
  calc
    a • (Ideal.span ({b} : Set A)) =
        (Ideal.span ({a} : Set A)) • (Ideal.span ({b} : Set A)) := by
          simpa using
            (Submodule.ideal_span_singleton_smul (r := a)
              (N := (Ideal.span ({b} : Set A)))).symm
    _ = (Ideal.span ({a} : Set A)) * (Ideal.span ({b} : Set A)) := by
          rfl
    _ = (Ideal.span ({a * b} : Set A)) := by
          simp [Ideal.span_singleton_mul_span_singleton]

-- A power of a non-zero-divisor gives an inclusion on associated primes.
lemma associatedPrimes_subset_pow {A : Type*} [CommRing A] [IsNoetherianRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (k : ℕ) :
    associatedPrimes A (A ⧸ span {x}) ⊆ associatedPrimes A (A ⧸ span {x ^ (k + 1)}) := by
  have hxpow : x ^ k ∈ nonZeroDivisors A := by
    simpa using (nonZeroDivisors A).pow_mem hx k
  have hmul : (x ^ k) • (Ideal.span ({x} : Set A)) = Ideal.span ({x ^ (k + 1)} : Set A) := by
    simpa [pow_succ] using
      (smul_span_singleton_eq_span_singleton_mul (a := x ^ k) (b := x))
  have hsubset :
      associatedPrimes A (A ⧸ span {x}) ⊆
        associatedPrimes A (A ⧸ (x ^ k • (Ideal.span ({x} : Set A)))) :=
    associatedPrimes.subset_of_injective
      (f := Ideal.mulQuot (x ^ k) (Ideal.span ({x} : Set A)))
      (Ideal.mulQuot_injective (I := Ideal.span ({x} : Set A)) (a := x ^ k) hxpow)
  rw [← hmul]
  exact hsubset

-- The exact sequence from multiplication by `x` bounds associated primes of successive quotients.
lemma associatedPrimes_pow_succ_subset {A : Type*} [CommRing A] [IsNoetherianRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (k : ℕ) :
    associatedPrimes A (A ⧸ span {x ^ (k + 1)}) ⊆
      associatedPrimes A (A ⧸ span {x ^ k}) ∪ associatedPrimes A (A ⧸ span {x}) := by
  have hmul : x • (Ideal.span ({x ^ k} : Set A)) = Ideal.span ({x ^ (k + 1)} : Set A) := by
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using
      (smul_span_singleton_eq_span_singleton_mul (a := x) (b := x ^ k))
  have hsubset :
      associatedPrimes A (A ⧸ (x • Ideal.span ({x ^ k} : Set A))) ⊆
        associatedPrimes A (A ⧸ span {x ^ k}) ∪ associatedPrimes A (A ⧸ span {x}) :=
    associatedPrimes.subset_union_of_exact
      (f := Ideal.mulQuot x (Ideal.span ({x ^ k} : Set A)))
      (g := Ideal.quotOfMul x (Ideal.span ({x ^ k} : Set A)))
      (Ideal.mulQuot_injective (I := Ideal.span ({x ^ k} : Set A)) (a := x) hx)
      (Ideal.exact_mulQuot_quotOfMul (a := x) (I := Ideal.span ({x ^ k} : Set A)))
  rw [← hmul]
  exact hsubset

theorem associatedPrimes_quot_span_eq_quot_span_pow {A : Type} [CommRing A] [IsNoetherianRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (hx' : ¬ IsUnit x) (n : ℕ) (h : n ≥ 1) :
    associatedPrimes A (A ⧸ span {x}) = associatedPrimes A (A ⧸ span {x ^ n}) := by
  classical
  have _ := hx'
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos 0) h))
  induction k with
  | zero =>
      rw [pow_one]
  | succ k ih =>
      refine le_antisymm ?_ ?_
      · simpa using associatedPrimes_subset_pow (x := x) (hx := hx) (k := k.succ)
      · have hsubset := associatedPrimes_pow_succ_subset (x := x) (hx := hx) (k := k.succ)
        simpa [← ih] using hsubset

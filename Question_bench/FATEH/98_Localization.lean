import Question_bench.FATEH.«98_Elementary»

open RingTheory

/-!
# Principal class prime ⇒ complete intersection (localization bookkeeping)

This file isolates the `Localization.AtPrime` bookkeeping used in the principal-class scaffolding.
-/

namespace PrincipalClass

section AtPrimeBookkeeping

variable {A : Type*} [CommRing A]
variable (P : Ideal A) [P.IsPrime]

local notation "Aₚ" => Localization.AtPrime P
local notation "ι" => (algebraMap A Aₚ)
local notation "Pₚ" => (Ideal.map ι P : Ideal Aₚ)

/-- Step A：map `P = Ideal.ofList b` to `Aₚ`. -/
lemma map_ofList_eq_ofList_map (b : List A) (hbP : P = Ideal.ofList b) :
    Pₚ = Ideal.ofList (b.map ι) := by
  simp [hbP]

/-- Step B：in `Aₚ`, the image of `P` is the maximal ideal. -/
lemma map_eq_maximalIdeal_atPrime :
    Pₚ = IsLocalRing.maximalIdeal Aₚ := by
  simpa using (Localization.AtPrime.map_eq_maximalIdeal (I := P))

/-- Step B': the mapped ideal `Pₚ` is prime. -/
lemma map_isPrime_atPrime : (Pₚ).IsPrime := by
  simpa using
    (Ideal.isPrime_map_of_isLocalizationAtPrime (q := P) (S := Aₚ) (p := P) (hpq := le_rfl))

local instance : (Pₚ).IsPrime := map_isPrime_atPrime (A := A) (P := P)

/-- Step C：`primeHeight` is invariant under `AtPrime` localization at `P`. -/
lemma primeHeight_map_atPrime :
    (Pₚ).primeHeight = P.primeHeight := by
  have h₁ :
      (Ideal.comap ι (Pₚ : Ideal Aₚ)).primeHeight = (Pₚ : Ideal Aₚ).primeHeight := by
    simpa using
      (IsLocalization.primeHeight_comap (S := P.primeCompl) (A := Aₚ) (J := (Pₚ : Ideal Aₚ)))
  have hdisj : Disjoint (P.primeCompl : Set A) (P : Set A) := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]
  have hcomap : Ideal.comap ι (Pₚ : Ideal Aₚ) = P := by
    simpa using
      (IsLocalization.comap_map_of_isPrime_disjoint (M := P.primeCompl) (S := Aₚ) (I := P)
        (hI := (by infer_instance : P.IsPrime)) hdisj)
  have : P.primeHeight = (Pₚ : Ideal Aₚ).primeHeight := by
    simpa [hcomap] using h₁
  simpa using this.symm

end AtPrimeBookkeeping

end PrincipalClass

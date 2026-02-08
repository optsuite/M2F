import Mathlib
import Rockafellar_convex_analysis.Chapters.Chap01.section03_part1

open scoped BigOperators
open scoped Pointwise

section Chap01
section Section03

/-- Fiberwise addition over a real scalar coordinate preserves convexity. -/
lemma convex_fiberwise_add_real {n : ℕ}
    {K1 K2 : Set (Real × (Fin n → Real))}
    (hK1 : Convex Real K1) (hK2 : Convex Real K2) :
    Convex Real
      {p : Real × (Fin n → Real) |
        ∃ x1 x2 : Fin n → Real,
          p.2 = x1 + x2 ∧ (p.1, x1) ∈ K1 ∧ (p.1, x2) ∈ K2} := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨x1, x2, hp_sum, hp1, hp2⟩
  rcases hq with ⟨y1, y2, hq_sum, hq1, hq2⟩
  refine ⟨a • x1 + b • y1, a • x2 + b • y2, ?_, ?_, ?_⟩
  · calc
      (a • p + b • q).2 = a • p.2 + b • q.2 := by simp
      _ = a • (x1 + x2) + b • (y1 + y2) := by simp [hp_sum, hq_sum]
      _ = (a • x1 + b • y1) + (a • x2 + b • y2) := by
        symm
        exact
          smul_add_smul_add_eq (z1 := x1) (z1' := y1) (z2 := x2) (z2' := y2)
  · have hcombo : a • (p.1, x1) + b • (q.1, y1) ∈ K1 :=
      hK1 hp1 hq1 ha hb hab
    simpa using hcombo
  · have hcombo : a • (p.1, x2) + b • (q.1, y2) ∈ K2 :=
      hK2 hp2 hq2 ha hb hab
    simpa using hcombo

/-- Fiberwise addition on the real coordinate preserves convexity. -/
lemma convex_fiberwise_add_real_left {n : ℕ}
    {K1 K2 : Set (Real × (Fin n → Real))}
    (hK1 : Convex Real K1) (hK2 : Convex Real K2) :
    Convex Real
      {p : Real × (Fin n → Real) |
        ∃ r1 r2 : Real,
          p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2} := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨r1, r2, hp_sum, hp1, hp2⟩
  rcases hq with ⟨s1, s2, hq_sum, hq1, hq2⟩
  refine ⟨a • r1 + b • s1, a • r2 + b • s2, ?_, ?_, ?_⟩
  · calc
      (a • p + b • q).1 = a • p.1 + b • q.1 := by simp
      _ = a * (r1 + r2) + b * (s1 + s2) := by simp [hp_sum, hq_sum]
      _ = (a * r1 + b * s1) + (a * r2 + b * s2) := by ring
      _ = (a • r1 + b • s1) + (a • r2 + b • s2) := by simp
  · have hcombo : a • (r1, p.2) + b • (s1, q.2) ∈ K1 :=
      hK1 hp1 hq1 ha hb hab
    simpa using hcombo
  · have hcombo : a • (r2, p.2) + b • (s2, q.2) ∈ K2 :=
      hK2 hp2 hq2 ha hb hab
    simpa using hcombo

/-- Text 3.6.7: For convex sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`, `K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`,
and `K = { (λ, x) | ∃ x1 x2, x = x1 + x2 ∧ (λ, x1) ∈ K1 ∧ (λ, x2) ∈ K2 }`.
Then `K` is convex. -/
theorem convex_coneSet_add {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ x1 x2 : Fin n → Real,
            p.2 = x1 + x2 ∧ (p.1, x1) ∈ K1 ∧ (p.1, x2) ∈ K2}
      Convex Real K) := by
  simpa using
    (convex_fiberwise_add_real
      (K1 := {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1})
      (K2 := {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2})
      (hK1 := by simpa using (convex_coneSet_of_convex (hC := hC1)))
      (hK2 := by simpa using (convex_coneSet_of_convex (hC := hC2))))

/-- Text 3.6.8: For convex sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`, `K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`,
and `K = { (λ, x) | ∃ λ1 λ2, λ = λ1 + λ2, (λ1, x) ∈ K1, (λ2, x) ∈ K2 }`.
Then `(1, x) ∈ K` iff `x ∈ C1 # C2`. -/
theorem coneSet_inverseAddition_iff {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (_hC1 : Convex Real C1) (_hC2 : Convex Real C2) (x : Fin n → Real) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real,
            p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
      (1, x) ∈ K ↔ x ∈ C1 # C2) := by
  dsimp
  constructor
  · rintro ⟨r1, r2, hsum, hr1, hr2⟩
    rcases hr1 with ⟨hr1_nonneg, hx1⟩
    rcases hr2 with ⟨hr2_nonneg, hx2⟩
    refine Set.mem_sUnion.2 ?_
    refine ⟨(r1 • C1) ∩ (r2 • C2), ?_, ?_⟩
    · refine ⟨r1, r2, hr1_nonneg, hr2_nonneg, ?_, rfl⟩
      exact hsum.symm
    · exact ⟨hx1, hx2⟩
  · intro hx
    rcases Set.mem_sUnion.1 hx with ⟨S, hS, hxS⟩
    rcases hS with ⟨r1, r2, hr1, hr2, hsum, rfl⟩
    rcases hxS with ⟨hx1, hx2⟩
    refine ⟨r1, r2, ?_, ?_, ?_⟩
    · exact hsum.symm
    · exact ⟨hr1, hx1⟩
    · exact ⟨hr2, hx2⟩

/-- Text 3.6.9: For convex sets `C1` and `C2`, let
`K1 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C1 }`, `K2 = { (λ, x) | 0 ≤ λ ∧ x ∈ λ • C2 }`,
and `K = { (λ, x) | ∃ λ1 λ2, λ = λ1 + λ2, (λ1, x) ∈ K1, (λ2, x) ∈ K2 }`.
Then `K` is convex. -/
theorem convex_coneSet_inverseAddition {n : ℕ} {C1 C2 : Set (Fin n → Real)}
    (hC1 : Convex Real C1) (hC2 : Convex Real C2) :
    (let K1 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1}
      let K2 : Set (Real × (Fin n → Real)) :=
        {p | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2}
      let K : Set (Real × (Fin n → Real)) :=
        {p |
          ∃ r1 r2 : Real,
            p.1 = r1 + r2 ∧ (r1, p.2) ∈ K1 ∧ (r2, p.2) ∈ K2}
      Convex Real K) := by
  simpa using
    (convex_fiberwise_add_real_left
      (K1 := {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C1})
      (K2 := {p : Real × (Fin n → Real) | 0 ≤ p.1 ∧ p.2 ∈ p.1 • C2})
      (hK1 := by simpa using (convex_coneSet_of_convex (hC := hC1)))
      (hK2 := by simpa using (convex_coneSet_of_convex (hC := hC2))))

end Section03
end Chap01

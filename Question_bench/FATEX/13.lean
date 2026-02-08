import Mathlib

/-
Let $(R,+,\cdot)$ be a (not necessarily commutative) ring.
If we know that $R$ is not a field and $x^2=x$ for any $x\in R,$
where $x$ is not invertible. Prove that $x^2=x$ for any $x.$
-/

/-- If `(1 - x)^2 = 1 - x`, then `x^2 = x`. -/
lemma sq_eq_self_of_one_sub_sq_eq_one_sub {R : Type} [Ring R] (x : R)
    (h : (1 - x) ^ 2 = (1 - x)) : x^2 = x := by
  have h' : (1 - x) * (1 - x) = (1 - x) := by
    simpa [pow_two] using h
  have h'' : x * x + (-x + (-x + 1)) = -x + 1 := by
    simpa [mul_sub, sub_mul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add, add_mul] using h'
  have h2' := congrArg (fun t => t + x) h''
  have h3 : x * x + (-x + 1) = 1 := by
    convert h2' using 1 <;> abel
  have h4 : x * x - x = 0 := by
    have h3' : x * x - x + 1 = 0 + 1 := by
      simpa [sub_eq_add_neg, add_assoc] using h3
    exact add_right_cancel h3'
  have h5 : x * x = x := by
    exact sub_eq_zero.mp h4
  simpa [pow_two] using h5

/-- In a subsingleton ring, every element is idempotent. -/
lemma sq_eq_self_of_subsingleton {R : Type} [Ring R] [Subsingleton R] (x : R) : x^2 = x := by
  simpa using (Subsingleton.elim (x^2) x)

/-- `x^2 = x` iff `x * (1 - x) = 0`. -/
lemma sq_eq_self_iff_mul_one_sub_eq_zero {R : Type} [Ring R] (x : R) :
    x^2 = x ↔ x * (1 - x) = 0 := by
  constructor
  · intro h
    have h' : x * x = x := by
      simpa [pow_two] using h
    calc
      x * (1 - x) = x * 1 - x * x := by
        simp [mul_sub]
      _ = x - x := by
        simp [h', mul_one]
      _ = 0 := by
        simp
  · intro h
    have h' : x * 1 - x * x = 0 := by
      simpa [mul_sub] using h
    have h'' : x - x * x = 0 := by
      simpa [mul_one] using h'
    have hx : x = x * x := sub_eq_zero.mp h''
    have hx' : x * x = x := hx.symm
    simpa [pow_two] using hx'

/-- If the product of two units is zero, then `0 = 1`. -/
lemma zero_eq_one_of_isUnit_mul_eq_zero {R : Type} [Ring R] {a b : R}
    (ha : IsUnit a) (hb : IsUnit b) (hab : a * b = 0) : (0 : R) = 1 := by
  have ha0 : a = 0 := (IsUnit.mul_left_eq_zero hb).1 hab
  have h0 : IsUnit (0 : R) := by
    simpa [ha0] using ha
  exact (isUnit_zero_iff.mp h0)

/-- If `0 ≠ 1`, then the product of two units is nonzero. -/
lemma mul_ne_zero_of_isUnit {R : Type} [Ring R] {a b : R}
    (htriv : (0 : R) ≠ 1) (ha : IsUnit a) (hb : IsUnit b) : a * b ≠ 0 := by
  intro hab
  exact htriv (zero_eq_one_of_isUnit_mul_eq_zero ha hb hab)

/-- If the ring is not a subsingleton, then `0 ≠ 1`. -/
lemma zero_ne_one_of_not_subsingleton {R : Type} [Ring R] (hsubs : ¬ Subsingleton R) :
    (0 : R) ≠ 1 := by
  intro h01
  apply hsubs
  haveI : Subsingleton R := subsingleton_of_zero_eq_one h01
  infer_instance

/-- If `x` and `1 - x` are units and every nonunit is idempotent, then any nonunit is zero. -/
lemma nonunit_eq_zero_of_units_one_sub {R : Type} [Ring R] {x : R} (hx : IsUnit x)
    (hux : IsUnit (1 - x)) (h2 : ∀ z : R, ¬ IsUnit z → z^2 = z) :
    ∀ {y : R}, ¬ IsUnit y → y = 0 := by
  intro y hy
  have hy_idem : y^2 = y := h2 y hy
  rcases hx with ⟨u, hu⟩
  rcases hux with ⟨v, hv⟩
  have hyu : ¬ IsUnit (y * (u : R)) := by
    intro hyu
    have : IsUnit y := (Units.isUnit_mul_units (a := y) u).1 hyu
    exact hy this
  have hyv : ¬ IsUnit (y * (v : R)) := by
    intro hyv
    have : IsUnit y := (Units.isUnit_mul_units (a := y) v).1 hyv
    exact hy this
  have hyu_idem : (y * (u : R))^2 = y * (u : R) := h2 _ hyu
  have hyv_idem : (y * (v : R))^2 = y * (v : R) := h2 _ hyv
  have hyu_idem' : (y * (u : R)) * (y * (u : R)) = y * (u : R) := by
    simpa [pow_two] using hyu_idem
  have hyv_idem' : (y * (v : R)) * (y * (v : R)) = y * (v : R) := by
    simpa [pow_two] using hyv_idem
  have hyu_eq : y * (u : R) * y = y := by
    have h := congrArg (fun t => t * (↑u⁻¹ : R)) hyu_idem'
    simpa [mul_assoc] using h
  have hyv_eq : y * (v : R) * y = y := by
    have h := congrArg (fun t => t * (↑v⁻¹ : R)) hyv_idem'
    simpa [mul_assoc] using h
  have hv' : (v : R) = 1 - (u : R) := by
    simpa [hu] using hv
  have huv_aux : (u : R) + (1 + -(u : R)) = (1 : R) := by
    abel
  have huv : (u : R) + (v : R) = 1 := by
    calc
      (u : R) + (v : R) = (u : R) + (1 - (u : R)) := by
        simp [hv']
      _ = 1 := by
        simp [sub_eq_add_neg, huv_aux]
  have hyuv : y * (u : R) + y * (v : R) = y := by
    calc
      y * (u : R) + y * (v : R) = y * ((u : R) + (v : R)) := by
        symm
        simp [mul_add]
      _ = y := by
        simp [huv]
  have hsum' : y * (u : R) * y + y * (v : R) * y = y + y := by
    simp [hyu_eq, hyv_eq]
  have hsum : y * y = y + y := by
    calc
      y * y = (y * (u : R) + y * (v : R)) * y := by
        simp [hyuv]
      _ = y * (u : R) * y + y * (v : R) * y := by
        simp [add_mul, mul_assoc]
      _ = y + y := hsum'
  have hy_idem' : y * y = y := by
    simpa [pow_two] using hy_idem
  have hsum1 : y = y + y := by
    calc
      y = y * y := hy_idem'.symm
      _ = y + y := hsum
  have hsum2 : y + 0 = y + y := by
    simpa using hsum1
  have hy0 : 0 = y := add_left_cancel hsum2
  exact hy0.symm

/-- If every nonzero element is a unit in a commutative ring, then the ring is a field. -/
lemma isField_of_isUnit_of_ne_zero {R : Type} [CommRing R] (htriv : (0 : R) ≠ 1)
    (hunit : ∀ {a : R}, a ≠ 0 → IsUnit a) : IsField R := by
  refine { exists_pair_ne := ?_, mul_comm := ?_, mul_inv_cancel := ?_ }
  · exact ⟨0, 1, htriv⟩
  · exact mul_comm
  · intro a ha
    exact (hunit ha).exists_right_inv

theorem sq_eq_self_of_not_unit {R : Type} [CommRing R] (h : ¬ IsField R)
    (h2 : ∀ x : R, ¬ IsUnit x → x^2 = x) (x : R) : x^2 = x := by
  by_cases hx : IsUnit x
  · by_cases h1 : x = 1
    · simp [h1]
    · by_cases hux : IsUnit (1 - x)
      · by_cases htriv : (0 : R) = 1
        ·
          haveI : Subsingleton R := subsingleton_of_zero_eq_one htriv
          exact sq_eq_self_of_subsingleton (R := R) x
        ·
          have hunit : ∀ {a : R}, a ≠ 0 → IsUnit a := by
            classical
            intro a ha
            by_contra haunit
            have hzero :
                a = 0 := nonunit_eq_zero_of_units_one_sub (x := x) hx hux h2 haunit
            exact ha hzero
          have hfield : IsField R := isField_of_isUnit_of_ne_zero (R := R) htriv hunit
          exact (h hfield).elim
      ·
        have hsq : (1 - x) ^ 2 = (1 - x) := h2 (1 - x) hux
        exact sq_eq_self_of_one_sub_sq_eq_one_sub x hsq
  · exact h2 x hx

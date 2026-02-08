import Mathlib

/- Let $R$ be a ring with $1 \neq 0$.\nFor two elements $a,b \in R$, if $1-ab$ is a unit,
then $1-ba$ is a unit. -/
theorem isUnit_one_sub_mul {R : Type} [Ring R] [Nontrivial R] {a b : R} (h : IsUnit (1 - a * b)) :
    IsUnit (1 - b * a) := by
  rcases h with ⟨u, hu⟩
  refine ⟨⟨1 - b * a, 1 + b * (↑(u⁻¹) : R) * a, ?_, ?_⟩, rfl⟩
  ·
    set x : R := (↑(u⁻¹) : R) * a with hxdef
    have hx : x - a * (b * x) = a := by
      have : (1 - a * b) * x = a := by
        subst x
        calc
          (1 - a * b) * ((↑(u⁻¹) : R) * a) = (↑u : R) * ((↑(u⁻¹) : R) * a) := by
            simp [hu]
          _ = a := by simp
      have : x - (a * b) * x = a := by
        simpa [sub_mul, one_mul] using this
      simpa [mul_assoc] using this
    subst x
    have hbx : b * (↑u⁻¹ * a) - b * (a * (b * (↑u⁻¹ * a))) = b * a := by
      simpa [mul_sub, mul_assoc] using congrArg (fun t : R => b * t) hx
    calc
      (1 - b * a) * (1 + b * ↑u⁻¹ * a) = (1 - b * a) * (1 + b * (↑u⁻¹ * a)) := by
        simp [mul_assoc]
      _ = 1 := by
        simp [mul_add, sub_mul, mul_assoc, hbx]
  ·
    set x : R := (↑(u⁻¹) : R) * a with hxdef
    have hx : x - x * (b * a) = a := by
      have : (↑(u⁻¹) : R) * ((1 - a * b) * a) = a := by
        calc
          (↑(u⁻¹) : R) * ((1 - a * b) * a) = (↑(u⁻¹) : R) * ((↑u : R) * a) := by
            simp [hu]
          _ = a := by
            calc
              (↑(u⁻¹) : R) * ((↑u : R) * a) = ((↑(u⁻¹) : R) * (↑u : R)) * a := by
                simp
              _ = a := by simp
      subst x
      have : (↑(u⁻¹) : R) * (a - a * (b * a)) = a := by
        simpa [sub_mul, one_mul, mul_assoc] using this
      simpa [mul_sub, mul_assoc] using this
    subst x
    have hbx : b * (↑u⁻¹ * a) - b * (↑u⁻¹ * a * (b * a)) = b * a := by
      simpa [mul_sub, mul_assoc] using congrArg (fun t : R => b * t) hx
    have hbx' : b * (↑u⁻¹ * a) - b * (↑u⁻¹ * (a * (b * a))) = b * a := by
      simpa [mul_assoc] using hbx
    calc
      (1 + b * ↑u⁻¹ * a) * (1 - b * a) = (1 + b * (↑u⁻¹ * a)) * (1 - b * a) := by
        simp [mul_assoc]
      _ = 1 := by
        have hb_eq : b * (↑u⁻¹ * a) = b * a + b * (↑u⁻¹ * (a * (b * a))) :=
          (sub_eq_iff_eq_add).1 hbx'
        simp [add_mul, mul_sub, mul_assoc]
        simp [hb_eq]

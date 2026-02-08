import Mathlib

/--
Prove that $\mathbb{Q}/\mathbb{Z}$ has no proper subgroups of finite index.
-/
theorem eq_top_of_finiteIndex (H : AddSubgroup (ℚ ⧸ (Int.castAddHom ℚ).range)) (h_fin : H.FiniteIndex) :
    H = ⊤ := by
  letI : DivisibleBy ℚ ℕ := AddGroup.divisibleByNatOfDivisibleByInt ℚ
  letI : DivisibleBy (ℚ ⧸ (Int.castAddHom ℚ).range) ℕ :=
    QuotientAddGroup.divisibleBy (B := (Int.castAddHom ℚ).range)
  apply (eq_top_iff).2
  intro x _
  have h_index_ne : H.index ≠ 0 := (AddSubgroup.finiteIndex_iff (H := H)).1 h_fin
  have h_surj :
      Function.Surjective (fun y : (ℚ ⧸ (Int.castAddHom ℚ).range) => H.index • y) :=
    DivisibleBy.surjective_smul
      (A := (ℚ ⧸ (Int.castAddHom ℚ).range)) (α := ℕ) (n := H.index) h_index_ne
  rcases h_surj x with ⟨y, rfl⟩
  exact AddSubgroup.nsmul_index_mem H y

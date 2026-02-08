import Mathlib

open scoped BigOperators

/-- If `A` vanishes on and below the diagonal, then `(A ^ (k+1)) i j = 0` whenever the column index
`j` is at most `k` steps above the row index `i` (measured in `Fin.val`). -/
lemma pow_apply_eq_zero_of_val_le_add {S : Type*} [Semiring S] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) S) (hA : ∀ i j : Fin n, i ≥ j → A i j = 0) :
    ∀ k : ℕ, ∀ i j : Fin n, j.val ≤ i.val + k → (A ^ k.succ) i j = 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro i j hj
      have hij : i ≥ j := (Fin.le_iff_val_le_val).2 (by simpa using hj)
      simpa using (hA i j hij)
  | succ k ih =>
      intro i j hj
      -- Expand `A^(k+2) = A * A^(k+1)` entrywise and show each summand is zero.
      rw [pow_succ' A k.succ]
      simp [Matrix.mul_apply]
      refine Finset.sum_eq_zero ?_
      intro l hl
      by_cases hil : i ≥ l
      · have hAi : A i l = 0 := hA i l hil
        simp [hAi]
      · have hil' : i < l := lt_of_not_ge hil
        have hlt : i.val + 1 ≤ l.val := Nat.succ_le_of_lt ((Fin.lt_def).1 hil')
        have hbound : i.val + k.succ ≤ l.val + k := by
          have := Nat.add_le_add_right hlt k
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using this
        have hj' : j.val ≤ l.val + k := le_trans hj hbound
        have hPow : (A ^ k.succ) l j = 0 := ih l j hj'
        rw [hPow]
        simp

/-- For any `i j : Fin n`, we have `j.val ≤ i.val + (n-1)`. -/
lemma val_le_add_pred_for_all_indices (n : ℕ) (i j : Fin n) : j.val ≤ i.val + (n - 1) := by
  have hj : j.val ≤ n - 1 := Nat.le_sub_one_of_lt j.isLt
  exact le_trans hj (Nat.le_add_left (n - 1) i.val)

/-- Let $S$ be any ring and let $n>2$ be an integer.
Propose a proof that if $A$ is any strictly upper triangular matrix in $M_n(S)$, then $A^n = 0$.
(A strictly upper triangular matrix is one whose entries on and below the main diagonal are all
zero.) -/
theorem pow_eq_zero_of_strictly_upper_triangle {S : Type} [Ring S] (n : ℕ) (hn : 2 < n)
    (A : Matrix (Fin n) (Fin n) S) (hA : ∀ (i : Fin n), ∀ (j : Fin n), i ≥ j → A i j = 0) :
    A ^ n = 0 := by
  classical
  have hnpos : 0 < n := lt_trans (by decide : 0 < 2) hn
  have hn1 : 1 ≤ n := Nat.succ_le_of_lt hnpos
  have hnsub : n - 1 + 1 = n := Nat.sub_add_cancel hn1
  ext i j
  have hzero : (A ^ (n - 1).succ) i j = 0 :=
    pow_apply_eq_zero_of_val_le_add A hA (n - 1) i j (val_le_add_pred_for_all_indices n i j)
  have : (A ^ n) i j = 0 := by
    simpa [Nat.succ_eq_add_one, hnsub] using hzero
  simpa [Matrix.zero_apply] using this

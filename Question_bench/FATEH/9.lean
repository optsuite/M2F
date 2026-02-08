import Mathlib

namespace DihedralGroup

variable {n : ℕ}

-- Rotations in the center must commute with a reflection; for odd `n` this forces the rotation to
-- be trivial.
lemma r_mem_center_iff (hn : Odd n) (i : ZMod n) :
    r i ∈ Subgroup.center (DihedralGroup n) ↔ i = 0 := by
  constructor
  · intro hi
    have hcomm := (Subgroup.mem_center_iff.mp hi) (sr (0 : ZMod n))
    have hsr : sr i = sr (-i) := by
      simpa using hcomm
    have hneg : i = -i := by
      exact sr.inj hsr
    have hadd : i + i = 0 := by
      simpa using (eq_neg_iff_add_eq_zero).1 hneg
    exact (ZMod.add_self_eq_zero_iff_eq_zero hn).1 hadd
  · intro hi
    subst hi
    simp

-- Reflections cannot be central when `n` is odd and `3 ≤ n` (they would force `1 = -1` in `ZMod n`).
lemma sr_not_mem_center (hn : Odd n) (h : n ≥ 3) (i : ZMod n) :
    sr i ∉ Subgroup.center (DihedralGroup n) := by
  intro hi
  have hcomm := (Subgroup.mem_center_iff.mp hi) (r (1 : ZMod n))
  have hiz : i - 1 = i + 1 := by
    have hsr : sr (i - 1) = sr (i + 1) := by
      simpa using hcomm
    exact sr.inj hsr
  have hneg1 : (- (1 : ZMod n)) = (1 : ZMod n) := by
    have h' : ((-i) + (i - 1)) = ((-i) + (i + 1)) :=
      congrArg (fun t : ZMod n => (-i) + t) hiz
    have h'' : ((-i) + i) + (- (1 : ZMod n)) = ((-i) + i) + (1 : ZMod n) := by
      simpa [sub_eq_add_neg, add_assoc] using h'
    simpa using h''
  have hone_lt : 1 < n := Nat.lt_of_lt_of_le (by decide : 1 < 3) h
  have hone : (1 : ZMod n) ≠ 0 := by
    intro h10
    have hn1 : n = 1 := (ZMod.one_eq_zero_iff).1 h10
    exact (ne_of_gt hone_lt) hn1
  have hne : (1 : ZMod n) ≠ - (1 : ZMod n) := ZMod.ne_neg_self hn hone
  exact hne (by simpa using hneg1.symm)

-- For odd `n ≥ 3`, the center of `DihedralGroup n` is trivial.
lemma center_eq_bot_of_odd (hn : Odd n) (h : n ≥ 3) :
    Subgroup.center (DihedralGroup n) = (⊥ : Subgroup (DihedralGroup n)) := by
  ext x
  cases x with
  | r i =>
    constructor
    · intro hx
      have hi0 : i = 0 := (r_mem_center_iff (n := n) hn i).1 hx
      subst hi0
      simp
    · intro hx
      have hx' : r i = (1 : DihedralGroup n) := by
        simpa using hx
      have hi0 : i = 0 := by
        apply r.inj
        calc
          r i = (1 : DihedralGroup n) := hx'
          _ = r 0 := (one_def (n := n))
      exact (r_mem_center_iff (n := n) hn i).2 hi0
  | sr i =>
    constructor
    · intro hx
      exact (sr_not_mem_center (n := n) hn h i hx).elim
    · intro hx
      have hx' : (sr i : DihedralGroup n) = 1 := by
        simpa using hx
      have : False := by
        have hsr : (sr i : DihedralGroup n) = r 0 := by
          calc
            (sr i : DihedralGroup n) = 1 := hx'
            _ = r 0 := (one_def (n := n))
        cases hsr
      exact this.elim

/-- If \( n \) is odd and \( n \geq 3 \), show that the identity is the only element of
\( D_{2n} \) which commutes with all elements of \( D_{2n} \). -/
theorem centralizer_eq_bot {n : ℕ} (hn : Odd n) (h : n ≥ 3) :
    Subgroup.centralizer ⊤ = (⊥ : Subgroup (DihedralGroup n)) := by
  simp [Subgroup.centralizer_univ, center_eq_bot_of_odd (n := n) hn h]

end DihedralGroup

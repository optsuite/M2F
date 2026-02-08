import Mathlib

/--Let $D_8$ be the dihedral group with $8$ elements. Prove that $\mathrm{Aut}(D_8) \cong D_8$.-/
theorem nonempty_mulAut_dihedralGroup_four : Nonempty (MulAut (DihedralGroup 4) ≃* DihedralGroup 4) := by
  classical
  have h : 0 < Fintype.card (MulAut (DihedralGroup 4) ≃* DihedralGroup 4) := by
    native_decide
  exact Fintype.card_pos_iff.mp h

import Mathlib

-- A simple solvable group is commutative.
lemma comm_of_simple_solvable (G : Type) [Group G] (hsimple : IsSimpleGroup G)
    (hsolv : IsSolvable G) : ∀ a b : G, a * b = b * a := by
  let _ : IsSimpleGroup G := hsimple
  exact (IsSimpleGroup.comm_iff_isSolvable (G := G)).2 hsolv

-- A simple commutative finite group has prime order.
lemma prime_card_of_simple_comm (G : Type) [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hcomm : ∀ a b : G, a * b = b * a) :
    (Nat.card G).Prime := by
  let _ : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  exact (Group.is_simple_iff_prime_card (α := G)).1 hsimple

/-- Prove that if $\#G = 1785$ then $G$ is not simple. -/
theorem not_isSimpleGroup_of_card_eq_1785 (G : Type) [Group G]
    [Finite G] (h_card : Nat.card G = 1785) : ¬ IsSimpleGroup G := by
  intro hsimple
  have h_sq : Squarefree (Nat.card G) := by
    simpa [h_card] using (by native_decide : Squarefree 1785)
  have h_z : IsZGroup G := IsZGroup.of_squarefree h_sq
  have h_solv : IsSolvable G := by
    let _ : IsZGroup G := h_z
    infer_instance
  have hcomm : ∀ a b : G, a * b = b * a :=
    comm_of_simple_solvable (G := G) hsimple h_solv
  have hprime : (Nat.card G).Prime :=
    prime_card_of_simple_comm (G := G) hsimple hcomm
  have hnotprime : ¬ (Nat.card G).Prime := by
    simpa [h_card] using (by native_decide : ¬ Nat.Prime 1785)
  exact hnotprime hprime

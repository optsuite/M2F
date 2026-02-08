import Mathlib

/- If $F$ is a field that is not perfect, show that $F$ has a nontrivial purely inseparable
extension.-/
-- If `F` is not perfect, its relative perfect closure inside the algebraic closure is nontrivial.
lemma perfectClosure_ne_bot_of_not_perfect {F : Type} [Field F] (h : ¬ PerfectField F) :
    (perfectClosure F (AlgebraicClosure F)) ≠ ⊥ := by
  intro hbot
  have : PerfectField F :=
    perfectField_of_perfectClosure_eq_bot (F := F) (E := AlgebraicClosure F) hbot
  exact h this

theorem exists_isPurelyInseparable_and_bot_lt {F : Type} [Field F] (h : ¬ PerfectField F) :
    ∃ E : IntermediateField F (AlgebraicClosure F), IsPurelyInseparable F E ∧ ⊥ < E := by
  refine ⟨perfectClosure F (AlgebraicClosure F), inferInstance, ?_⟩
  exact (bot_lt_iff_ne_bot).2 (perfectClosure_ne_bot_of_not_perfect (F := F) h)

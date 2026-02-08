import Mathlib

open Polynomial

/-- Prove that $k[x,y]$ is not a Dedekind ring. -/
theorem not_isDedekindRing_mvPolynomial_fin_two {k : Type} [Field k] :
    ¬ IsDedekindRing (MvPolynomial (Fin 2) k) := by
  classical
  let evalX : MvPolynomial (Fin 2) k →+* MvPolynomial (Fin 1) k :=
    MvPolynomial.eval₂Hom (MvPolynomial.C)
      (fun i : Fin 2 => if i = 0 then (0 : MvPolynomial (Fin 1) k) else MvPolynomial.X 0)
  let eval0' : MvPolynomial (Fin 1) k →+* k :=
    MvPolynomial.eval₂Hom (RingHom.id k) (fun _ : Fin 1 => 0)
  let eval0 : MvPolynomial (Fin 2) k →+* k := eval0'.comp evalX
  let p1 : Ideal (MvPolynomial (Fin 2) k) := RingHom.ker evalX
  let p2 : Ideal (MvPolynomial (Fin 2) k) := RingHom.ker eval0
  have hp1 : p1.IsPrime := by
    dsimp [p1]
    simpa using (RingHom.ker_isPrime evalX)
  have hp2 : p2.IsPrime := by
    dsimp [p2]
    simpa using (RingHom.ker_isPrime eval0)
  have hp1_ne_bot : p1 ≠ ⊥ := by
    intro hbot
    have hx : (MvPolynomial.X (0:Fin 2) : MvPolynomial (Fin 2) k) ∈ p1 := by
      dsimp [p1]
      exact (RingHom.mem_ker).2 (by simp [evalX])
    have hx0 : (MvPolynomial.X (0:Fin 2) : MvPolynomial (Fin 2) k) = 0 := by
      have hx0 := hx
      simp [hbot] at hx0
    exact (MvPolynomial.X_ne_zero (s := (0:Fin 2)) (R := k)) hx0
  have hbot_lt_p1 : (⊥ : Ideal (MvPolynomial (Fin 2) k)) < p1 :=
    bot_lt_iff_ne_bot.mpr hp1_ne_bot
  have hp1_le_p2 : p1 ≤ p2 := by
    intro f hf
    have hf' : evalX f = 0 := (RingHom.mem_ker).1 hf
    exact (RingHom.mem_ker).2 (by simp [eval0, hf', eval0'])
  have hx1_in_p2 : (MvPolynomial.X (1:Fin 2) : MvPolynomial (Fin 2) k) ∈ p2 := by
    dsimp [p2]
    exact (RingHom.mem_ker).2 (by simp [eval0, eval0', evalX])
  have hx1_notin_p1 :
      (MvPolynomial.X (1:Fin 2) : MvPolynomial (Fin 2) k) ∉ p1 := by
    intro hx
    have hx' : evalX (MvPolynomial.X (1:Fin 2)) = 0 := (RingHom.mem_ker).1 hx
    have hx'' :
        (MvPolynomial.X (0:Fin 1) : MvPolynomial (Fin 1) k) = 0 := by
      have hx'' := hx'
      simp [evalX] at hx''
    exact (MvPolynomial.X_ne_zero (s := (0:Fin 1)) (R := k)) hx''
  have hp1_lt_p2 : p1 < p2 := by
    refine lt_of_le_of_ne hp1_le_p2 ?_
    intro hEq
    have : (MvPolynomial.X (1:Fin 2) : MvPolynomial (Fin 2) k) ∈ p1 := by
      simpa [hEq] using hx1_in_p2
    exact hx1_notin_p1 this
  intro hDed
  haveI : Ring.DimensionLEOne (MvPolynomial (Fin 2) k) := hDed.toDimensionLEOne
  haveI : p1.IsPrime := hp1
  haveI : p2.IsPrime := hp2
  exact (Ring.DimensionLEOne.not_lt_lt (R := MvPolynomial (Fin 2) k) (⊥) p1 p2)
    ⟨hbot_lt_p1, hp1_lt_p2⟩

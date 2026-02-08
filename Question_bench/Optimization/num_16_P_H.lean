import Mathlib

open Matrix Set Finset Real Convex Function Gradient InnerProductSpace
set_option linter.style.longLine false

class OriginalProblem where
  n_var : ℕ
  constraints : (Fin n_var → ℝ) → Prop
  objective : (Fin n_var → ℝ) → ℝ

class OptProblem extends OriginalProblem where
  n_eqs : ℕ
  eq_constraints : (Fin n_var → ℝ) → (Fin n_eqs → ℝ)
  n_ieqs : ℕ
  ieq_constraints : (Fin n_var → ℝ) → (Fin n_ieqs → ℝ)
  constraints := fun x => eq_constraints x = 0 ∧ ieq_constraints x ≤ 0
  h_constraints : constraints =  fun x => eq_constraints x = 0 ∧ ieq_constraints x ≤ 0 := by simp

class LP extends OptProblem where
  c : Fin n_var → ℝ
  A_eq : Matrix (Fin n_eqs) (Fin n_var) ℝ
  b_eq : Fin n_eqs → ℝ
  A_ieq : Matrix (Fin n_ieqs) (Fin n_var) ℝ
  b_ieq : Fin n_ieqs → ℝ
  objective := fun x => c ⬝ᵥ x
  eq_constraints := fun x => A_eq *ᵥ x - b_eq
  ieq_constraints := fun x => A_ieq *ᵥ x - b_ieq
  h_objective : objective = fun x => c ⬝ᵥ x := by simp
  h_eq : eq_constraints = fun x => A_eq *ᵥ x - b_eq := by simp
  h_ieq : ieq_constraints = fun x => A_ieq *ᵥ x - b_ieq := by simp

class SDP extends OriginalProblem where
  c : Fin n_var → ℝ
  n_eqs : ℕ
  A_eq : Matrix (Fin n_eqs) (Fin n_var) ℝ
  b_eq : Fin n_eqs → ℝ
  eq_constraints := fun x => A_eq *ᵥ x - b_eq
  n_ieqs : ℕ
  A_sd : Fin n_var → Matrix (Fin n_ieqs) (Fin n_ieqs) ℝ
  B_sd : Matrix (Fin n_ieqs) (Fin n_ieqs) ℝ
  ieq_constraints := fun x => ∑ i, x i • A_sd i + B_sd
  constraints := fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef
  h_constraints : constraints =  fun x => eq_constraints x = 0 ∧ (ieq_constraints x).PosDef := by
simp
  objective := fun x => c ⬝ᵥ x
  h_objective : objective = fun x => c ⬝ᵥ x := by simp

def subequivlance (p q : OriginalProblem) : Prop :=
  ∀ (x : Fin p.n_var → ℝ), (p.constraints x) →
  ∃ (y : Fin q.n_var → ℝ), (q.constraints y) ∧
  q.objective y = p.objective x

def equivalence (p q : OriginalProblem) : Prop :=
  subequivlance p q ∧ subequivlance q p

class DualProblem (p : OptProblem) where
  dual_objective : (Fin p.n_eqs → ℝ) → (Fin p.n_ieqs → ℝ) → EReal
  dual_domain : Set ((Fin p.n_eqs → ℝ) × (Fin p.n_ieqs → ℝ))
  h_objective : dual_objective = fun lam mu => (⨅ x : (Fin p.n_var → ℝ), ((lam ⬝ᵥ p.eq_constraints x) + (mu ⬝ᵥ p.ieq_constraints x) + p.objective x).toEReal) := by
simp
  h_domain : dual_domain = {(lam, mu) | dual_objective lam mu ≠ ⊥ ∧ mu ≥ 0} := by simp


/-Consider the problem
\[
\begin{array}{ll}
\text{minimize} & \|Ax - b\|_1 / (c^T x + d) \\
\text{subject to} & \|x\|_\infty \leq 1,
\end{array}
\]
where \( A \in \mathbb{R}^{m \times n},  b \in \mathbb{R}^m,  c \in \mathbb{R}^n \), and \( d \in \mathbb{R} \). We assume that \( d > \|c\|_1 \), which implies that \( c^T x + d > 0 \) for all feasible \( x
\).

Show that it is equivalent to the convex optimization problem
\[
\begin{array}{ll}
\text{minimize} & \|Ay - bt\|_1 \\
\text{subject to} & \|y\|_\infty \leq t \\
& c^T y + dt = 1,
\end{array}
\]
with variables \( y \in \mathbb{R}^n,  t \in \mathbb{R} \).


-/
noncomputable section

variable (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) (d : ℝ)

noncomputable def P : OriginalProblem where
  n_var := n
  constraints := fun x => ∀ i, |x i| ≤ 1
  objective := fun x => ∑ i, |(A *ᵥ x - b) i| / (c ⬝ᵥ x + d)

noncomputable def Q : OriginalProblem where
  n_var := n + 1
  constraints := fun y => ∀ i, |y i| ≤ y (-1) ∧
  let y' : Fin n → ℝ:= fun i => y (Fin.ofNat (n+1) i.toNat)
  c ⬝ᵥ y' + d * y (-1) = 1
  objective := fun y => let y' : Fin n → ℝ:= fun i => y (Fin.ofNat (n+1) i.toNat)
  ∑ i, |(A *ᵥ y' - y (-1) • b) i|

/-- Projection of a `Fin (n+1)` vector onto its first `n` coordinates. -/
abbrev num_16_P_H_yproj (y : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => y i.castSucc

/-- Scaling identity for the ℓ1 residual in the objective. -/
lemma num_16_P_H_sum_abs_smul (t : ℝ) (x : Fin n → ℝ) :
    ∑ i, |(A *ᵥ (t • x) - t • b) i| = |t| * ∑ i, |(A *ᵥ x - b) i| := by
  classical
  calc
    ∑ i, |(A *ᵥ (t • x) - t • b) i|
        = ∑ i, |t * (A *ᵥ x - b) i| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have h : t * (A *ᵥ x) i - t * b i = t * ((A *ᵥ x) i - b i) := by ring
            simp [mulVec_smul, Pi.smul_apply, smul_eq_mul, h, abs_mul]
    _ = ∑ i, |t| * |(A *ᵥ x - b) i| := by simp [abs_mul]
    _ = |t| * ∑ i, |(A *ᵥ x - b) i| := by
          simpa using
            (Finset.mul_sum (s:=Finset.univ) (f:=fun i => |(A *ᵥ x - b) i|) (a:=|t|)).symm

/-- Dot-product bound from an ℓ∞ constraint. -/
lemma num_16_P_H_abs_dotProduct_le_sum_abs {x : Fin n → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    |c ⬝ᵥ x| ≤ ∑ i, |c i| := by
  classical
  have h1 : |c ⬝ᵥ x| ≤ ∑ i, |c i * x i| := by
    simpa [dotProduct] using
      (Finset.abs_sum_le_sum_abs (f:=fun i => c i * x i) (s:=Finset.univ))
  have h2 : ∑ i, |c i * x i| ≤ ∑ i, |c i| := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hxi : |x i| ≤ 1 := hx i
    calc
      |c i * x i| = |c i| * |x i| := by simp [abs_mul, mul_comm]
      _ ≤ |c i| * 1 := by
            exact mul_le_mul_of_nonneg_left hxi (abs_nonneg (c i))
      _ = |c i| := by simp
  exact le_trans h1 h2

/-- Positivity of the denominator `c ⬝ᵥ x + d` under the ℓ∞ constraint. -/
lemma num_16_P_H_denom_pos (hcd : d > ∑ i, |c i|) {x : Fin n → ℝ} (hx : ∀ i, |x i| ≤ 1) :
    0 < c ⬝ᵥ x + d := by
  classical
  have hbound : |c ⬝ᵥ x| ≤ ∑ i, |c i| :=
    num_16_P_H_abs_dotProduct_le_sum_abs (n:=n) (c:=c) (x:=x) hx
  have hneg : -(∑ i, |c i|) ≤ c ⬝ᵥ x := by
    have h1 : -(∑ i, |c i|) ≤ -|c ⬝ᵥ x| := neg_le_neg hbound
    exact le_trans h1 (neg_abs_le (c ⬝ᵥ x))
  have hcd' : 0 < d + (-(∑ i, |c i|)) := by
    have : 0 < d - ∑ i, |c i| := by linarith
    simpa [sub_eq_add_neg] using this
  have h2 : d + (-(∑ i, |c i|)) ≤ c ⬝ᵥ x + d := by
    have := add_le_add_left hneg d
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact lt_of_lt_of_le hcd' h2

/-- Forward direction: construct a `Q` feasible point from a `P` feasible point. -/
lemma num_16_P_H_subequivlance_P_Q (hcd : d > ∑ i, |c i|) :
    subequivlance (P n m A b c d) (Q n m A b c d) := by
  classical
  intro x hxP
  have hx : ∀ i, |x i| ≤ 1 := by simpa [P] using hxP
  let t : ℝ := (c ⬝ᵥ x + d)⁻¹
  have hden : 0 < c ⬝ᵥ x + d :=
    num_16_P_H_denom_pos (n:=n) (c:=c) (d:=d) hcd (x:=x) hx
  have htpos : 0 < t := by simpa [t] using (inv_pos.mpr hden)
  have ht_nonneg : 0 ≤ t := le_of_lt htpos
  let y : Fin (n + 1) → ℝ :=
    fun i => Fin.lastCases (motive:=fun _ => ℝ) t (fun i => t * x i) i
  have hlast : (-1 : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    simp
  have hy_last : y (-1) = t := by
    rw [hlast]
    dsimp [y]
    exact
      (Fin.lastCases_last (n:=n) (motive:=fun _ => ℝ) (last:=t) (cast:=fun i => t * x i))
  have hyproj : num_16_P_H_yproj (n:=n) y = t • x := by
    ext i
    simp [num_16_P_H_yproj, y, Fin.lastCases_castSucc, Pi.smul_apply, smul_eq_mul]
  have hconstraint : c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * y (-1) = 1 := by
    have hne : c ⬝ᵥ x + d ≠ 0 := ne_of_gt hden
    calc
      c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * y (-1)
          = c ⬝ᵥ (t • x) + d * t := by simp [hyproj, hy_last]
      _ = t * (c ⬝ᵥ x) + d * t := by
            simp [dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
      _ = t * (c ⬝ᵥ x + d) := by ring
      _ = 1 := by simp [t, hne]
  have hbound : ∀ i, |y i| ≤ t := by
    intro i
    cases i using Fin.lastCases with
    | last =>
        have hlast' : y (Fin.last n) = t := by
          simpa [hlast] using hy_last
        have : |t| ≤ t := by simpa [abs_of_nonneg ht_nonneg]
        simpa [hlast'] using this
    | cast i =>
        have hxi : |x i| ≤ 1 := hx i
        calc
          |y (i.castSucc)| = |t * x i| := by
                simp [y, Fin.lastCases_castSucc]
          _ = |t| * |x i| := by simp [abs_mul]
          _ ≤ |t| * 1 := by
                exact mul_le_mul_of_nonneg_left hxi (abs_nonneg t)
          _ = t := by simp [abs_of_nonneg ht_nonneg]
  refine ⟨y, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_⟩
    · simpa [hy_last] using hbound i
    · simpa [num_16_P_H_yproj] using hconstraint
  ·
    let s : ℝ := ∑ i, |(A *ᵥ x - b) i|
    have hQ : (Q n m A b c d).objective y = t * s := by
      have hQ' :
          (Q n m A b c d).objective y =
            ∑ i, |(A *ᵥ (fun i : Fin n => y i.castSucc) - y (-1) • b) i| := by
        simp [Q]
      have hQ'' :
          (Q n m A b c d).objective y =
            ∑ i, |(A *ᵥ num_16_P_H_yproj (n:=n) y - y (-1) • b) i| := by
        simpa [num_16_P_H_yproj] using hQ'
      calc
        (Q n m A b c d).objective y
            = ∑ i, |(A *ᵥ num_16_P_H_yproj (n:=n) y - y (-1) • b) i| := hQ''
        _ = ∑ i, |(A *ᵥ (t • x) - t • b) i| := by simp [hyproj, hy_last]
        _ = |t| * s := by
              simpa [s] using
                (num_16_P_H_sum_abs_smul (n:=n) (m:=m) (A:=A) (b:=b) t x)
        _ = t * s := by simp [abs_of_nonneg ht_nonneg]
    have hP : (P n m A b c d).objective x = t * s := by
      calc
        (P n m A b c d).objective x
            = ∑ i, |(A *ᵥ x - b) i| / (c ⬝ᵥ x + d) := by simp [P]
        _ = ∑ i, |(A *ᵥ x - b) i| * (c ⬝ᵥ x + d)⁻¹ := by simp [div_eq_mul_inv]
        _ = s * (c ⬝ᵥ x + d)⁻¹ := by
              symm
              simpa [s] using
                (Finset.sum_mul (s:=Finset.univ)
                  (f:=fun i => |(A *ᵥ x - b) i|) (a:=(c ⬝ᵥ x + d)⁻¹))
        _ = t * s := by simp [t, mul_comm, mul_left_comm, mul_assoc]
    calc
      (Q n m A b c d).objective y = t * s := hQ
      _ = (P n m A b c d).objective x := by symm; exact hP

/-- Backward direction: construct a `P` feasible point from a `Q` feasible point. -/
lemma num_16_P_H_subequivlance_Q_P :
    subequivlance (Q n m A b c d) (P n m A b c d) := by
  classical
  intro y hyQ
  have hy :
      ∀ i : Fin (n + 1), |y i| ≤ y (-1 : Fin (n + 1)) ∧
        c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * y (-1 : Fin (n + 1)) = 1 := by
    simpa [Q, num_16_P_H_yproj] using hyQ
  let t : ℝ := y (-1 : Fin (n + 1))
  have ht_nonneg : 0 ≤ t := by
    have h := (hy (-1 : Fin (n + 1))).1
    have h0 : 0 ≤ |y (-1 : Fin (n + 1))| := abs_nonneg _
    have : 0 ≤ y (-1 : Fin (n + 1)) := le_trans h0 h
    simpa [t] using this
  have ht_ne : t ≠ 0 := by
    intro ht0
    have hy_zero : ∀ i, y i = 0 := by
      intro i
      have hbound : |y i| ≤ t := by simpa [t] using (hy i).1
      have hbound0 : |y i| ≤ 0 := by simpa [ht0] using hbound
      have habs0 : |y i| = 0 := le_antisymm hbound0 (abs_nonneg _)
      exact (abs_eq_zero.mp habs0)
    have hyproj_zero : num_16_P_H_yproj (n:=n) y = 0 := by
      ext i
      simp [num_16_P_H_yproj, hy_zero]
    have hEq : c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * t = 1 :=
      (hy (-1 : Fin (n + 1))).2
    have : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * t := by symm; exact hEq
        _ = 0 := by simp [hyproj_zero, ht0]
    exact one_ne_zero this
  have ht_pos : 0 < t := lt_of_le_of_ne ht_nonneg (Ne.symm ht_ne)
  let x : Fin n → ℝ := t⁻¹ • num_16_P_H_yproj (n:=n) y
  have hyproj_bound : ∀ i, |num_16_P_H_yproj (n:=n) y i| ≤ t := by
    intro i
    have h := (hy (i.castSucc)).1
    simpa [num_16_P_H_yproj, t] using h
  have hx_bound : ∀ i, |x i| ≤ 1 := by
    intro i
    have h := hyproj_bound i
    have ht_inv_nonneg : 0 ≤ t⁻¹ := inv_nonneg.mpr ht_nonneg
    calc
      |x i| = |t⁻¹ * num_16_P_H_yproj (n:=n) y i| := by
            simp [x, Pi.smul_apply, smul_eq_mul]
      _ = |t⁻¹| * |num_16_P_H_yproj (n:=n) y i| := by simp [abs_mul]
      _ ≤ |t⁻¹| * t := by
            exact mul_le_mul_of_nonneg_left h (abs_nonneg _)
      _ = 1 := by
            calc
              |t⁻¹| * t = t⁻¹ * t := by simp [abs_of_nonneg ht_inv_nonneg]
              _ = 1 := by simp [ht_ne]
  have hxP : (P n m A b c d).constraints x := by
    simpa [P] using hx_bound
  have hyproj_eq : num_16_P_H_yproj (n:=n) y = t • x := by
    ext i
    simp [x, Pi.smul_apply, smul_eq_mul, ht_ne]
  have hEq : c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * t = 1 :=
    (hy (-1 : Fin (n + 1))).2
  have hden : c ⬝ᵥ x + d = t⁻¹ := by
    have hEq' : t * (c ⬝ᵥ x + d) = 1 := by
      calc
        t * (c ⬝ᵥ x + d) = t * (c ⬝ᵥ x) + d * t := by ring
        _ = c ⬝ᵥ (t • x) + d * t := by
              simp [dotProduct_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
        _ = c ⬝ᵥ num_16_P_H_yproj (n:=n) y + d * t := by simp [hyproj_eq]
        _ = 1 := hEq
    calc
      c ⬝ᵥ x + d = (t⁻¹ * t) * (c ⬝ᵥ x + d) := by
            simp [ht_ne, mul_assoc]
      _ = t⁻¹ * (t * (c ⬝ᵥ x + d)) := by simp [mul_assoc]
      _ = t⁻¹ * 1 := by simp [hEq']
      _ = t⁻¹ := by simp
  let s : ℝ := ∑ i, |(A *ᵥ x - b) i|
  have hQ : (Q n m A b c d).objective y = t * s := by
    calc
      (Q n m A b c d).objective y
          = ∑ i, |(A *ᵥ num_16_P_H_yproj (n:=n) y - t • b) i| := by
                have htdef : y (-1 : Fin (n + 1)) = t := by rfl
                simp [Q, num_16_P_H_yproj, htdef]
      _ = ∑ i, |(A *ᵥ (t • x) - t • b) i| := by simp [hyproj_eq]
      _ = |t| * s := by
            simpa [s] using
              (num_16_P_H_sum_abs_smul (n:=n) (m:=m) (A:=A) (b:=b) t x)
      _ = t * s := by simp [abs_of_nonneg ht_nonneg]
  have hP : (P n m A b c d).objective x = t * s := by
    calc
      (P n m A b c d).objective x
          = ∑ i, |(A *ᵥ x - b) i| / (c ⬝ᵥ x + d) := by simp [P]
      _ = ∑ i, |(A *ᵥ x - b) i| / t⁻¹ := by simp [hden]
      _ = ∑ i, |(A *ᵥ x - b) i| * t := by simp [div_eq_mul_inv]
      _ = t * s := by
            have hsum : ∑ i, |(A *ᵥ x - b) i| * t = s * t := by
              symm
              simpa [s] using
                (Finset.sum_mul (s:=Finset.univ)
                  (f:=fun i => |(A *ᵥ x - b) i|) (a:=t))
            simpa [mul_comm, s] using hsum
  refine ⟨x, hxP, ?_⟩
  calc
    (P n m A b c d).objective x = t * s := hP
    _ = (Q n m A b c d).objective y := by symm; exact hQ

theorem num_16_P_H (hcd : d > ∑ i, |c i|) :
  let P := P n m A b c d
  let Q := Q n m A b c d
  equivalence P Q:= by
  classical
  dsimp
  unfold equivalence
  constructor
  · exact num_16_P_H_subequivlance_P_Q (n:=n) (m:=m) (A:=A) (b:=b) (c:=c) (d:=d) hcd
  · exact num_16_P_H_subequivlance_Q_P (n:=n) (m:=m) (A:=A) (b:=b) (c:=c) (d:=d)

end

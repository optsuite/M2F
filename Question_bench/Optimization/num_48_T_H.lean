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


/-Consider the quadratically constrained quadratic program: $$\label{qcqp}\begin{aligned} \min_x \quad & x^\top Q_0 x - 2b_0^\top x \\    \text{subject to} \quad & x^\top Q_i x - 2 b_i^\top x + c_i \le 0, \quad i=1,\ldots, m.  \end{aligned} $$  Directly write the semidefinite programming (SDP) relaxation of problem
\eqref{qcqp}.

-/
noncomputable section

variable (n : ℕ) (Q0 : Matrix (Fin n) (Fin n) ℝ) (b0 : Fin n → ℝ) (m : ℕ) (Qi : Fin m → Matrix (Fin n) (Fin n) ℝ) (bi : Fin m → Fin n → ℝ) (ci : Fin m →
ℝ)

def P : OriginalProblem where
  n_var := n
  constraints := fun x => ∀ i, x ⬝ᵥ Qi i *ᵥ x - 2 * (bi i) ⬝ᵥ x + ci i ≤ 0
  objective := fun x => x ⬝ᵥ Q0 *ᵥ x - 2 * b0 ⬝ᵥ x

/-- Decode vectorized indices for the lifted `(n+1)×(n+1)` matrix. -/
abbrev Q_decode (n : ℕ) : Fin ((n + 1) * (n + 1)) → Fin (n + 1) × Fin (n + 1) :=
  (finProdFinEquiv : Fin (n + 1) × Fin (n + 1) ≃ Fin ((n + 1) * (n + 1))).symm

/-- Objective coefficients for the SDP relaxation in vectorized form. -/
abbrev Q_c (n : ℕ) (Q0 : Matrix (Fin n) (Fin n) ℝ) (b0 : Fin n → ℝ) :
    Fin ((n + 1) * (n + 1)) → ℝ :=
  fun k =>
    match Q_decode n k with
    | (i, j) =>
      Fin.cases
        (Fin.cases 0 (fun j => -2 * b0 j) j)
        (fun i => Fin.cases 0 (fun j => Q0 i j) j)
        i

/-- Standard basis matrices for reconstructing the lifted matrix from its vectorization. -/
abbrev Q_A_sd (n : ℕ) : Fin ((n + 1) * (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun k =>
    let ij := Q_decode n k
    Matrix.stdBasisMatrix ij.1 ij.2 (1 : ℝ)

def Q (n : ℕ) (Q0 : Matrix (Fin n) (Fin n) ℝ) (b0 : Fin n → ℝ) (m : ℕ) (Qi : Fin m → Matrix (Fin n) (Fin n) ℝ) (bi : Fin m → Fin n → ℝ) (ci : Fin m → ℝ) : SDP :=
  let N := n + 1
  let k00 : Fin (N * N) :=
    (finProdFinEquiv : Fin N × Fin N ≃ Fin (N * N)) (0, 0)
  { n_var := N * N
    c := Q_c n Q0 b0
    n_eqs := 1
    A_eq := fun _ k => if k = k00 then 1 else 0
    b_eq := fun _ => 1
    n_ieqs := N
    A_sd := Q_A_sd n
    B_sd := (1 : Matrix (Fin N) (Fin N) ℝ) }

/-- Lift `x` into the homogenized vector `(1, x)` in `Fin (n+1)`. -/
abbrev num_48_T_H_liftVec (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => Fin.cases 1 (fun j => x j) i

/-- Reconstruct the lifted matrix from its vectorized coefficients. -/
lemma num_48_T_H_reconstruct_sum_stdBasisMatrix
    (f : Fin ((n + 1) * (n + 1)) → ℝ) :
    (∑ k, f k • Matrix.stdBasisMatrix (Q_decode n k).1 (Q_decode n k).2 (1 : ℝ))
      = fun i j =>
          f ((finProdFinEquiv :
            Fin (n + 1) × Fin (n + 1) ≃ Fin ((n + 1) * (n + 1))) (i, j)) := by
  classical
  ext i j
  let e : Fin (n + 1) × Fin (n + 1) ≃ Fin ((n + 1) * (n + 1)) := finProdFinEquiv
  let k0 : Fin ((n + 1) * (n + 1)) := e (i, j)
  have hk0 : Q_decode n k0 = (i, j) := by
    simp [Q_decode, e, k0]
  have hsum :
      (∑ k, f k *
        (if (Q_decode n k).1 = i ∧ (Q_decode n k).2 = j then (1 : ℝ) else 0)) = f k0 := by
    classical
    have hzero :
        ∀ b ∈ (Finset.univ : Finset (Fin ((n + 1) * (n + 1)))), b ≠ k0 →
          f b * (if (Q_decode n b).1 = i ∧ (Q_decode n b).2 = j then (1 : ℝ) else 0) = 0 := by
      intro b hb hne
      have hneq : ¬ ((Q_decode n b).1 = i ∧ (Q_decode n b).2 = j) := by
        intro h
        have hb' : b = k0 := by
          have hpair : Q_decode n b = (i, j) := by
            cases h with
            | intro h1 h2 =>
              exact (Prod.ext_iff (x := Q_decode n b) (y := (i, j))).2 ⟨h1, h2⟩
          have hb0 : e (Q_decode n b) = b := by
            simpa [Q_decode, e] using (Equiv.apply_symm_apply e b)
          have hb1 : e (Q_decode n b) = e (i, j) := congrArg (fun p => e p) hpair
          have hb' : b = e (i, j) := hb0.symm.trans hb1
          simpa [k0] using hb'
        exact hne hb'
      by_cases h' : (Q_decode n b).1 = i ∧ (Q_decode n b).2 = j
      · exact (hneq h').elim
      · calc
          f b * (if (Q_decode n b).1 = i ∧ (Q_decode n b).2 = j then (1 : ℝ) else 0)
              = f b * 0 := by rw [if_neg h']
          _ = 0 := by simp
    simpa [hk0] using
      (Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset (Fin ((n + 1) * (n + 1)))))
        (f := fun k =>
          f k * (if (Q_decode n k).1 = i ∧ (Q_decode n k).2 = j then (1 : ℝ) else 0))
        (a := k0) (by simp) hzero)
  simpa [Matrix.sum_apply, Matrix.stdBasisMatrix, Matrix.single, smul_eq_mul] using hsum

/-- The rank-one matrix `vecMulVec v v` is positive semidefinite. -/
lemma num_48_T_H_vecMulVec_posSemidef (v : Fin (n + 1) → ℝ) :
    (Matrix.vecMulVec v v).PosSemidef := by
  simpa using (Matrix.posSemidef_vecMulVec_self_star (a := v))

/-- The lifted vector satisfies the SDP constraints. -/
lemma num_48_T_H_constraints_lift (x : Fin n → ℝ) :
    let v := num_48_T_H_liftVec (n := n) x
    let y : Fin ((n + 1) * (n + 1)) → ℝ :=
      fun k => Matrix.vecMulVec v v (Q_decode n k).1 (Q_decode n k).2
    (Q n Q0 b0 m Qi bi ci).toOriginalProblem.constraints y := by
  classical
  dsimp
  set v : Fin (n + 1) → ℝ := num_48_T_H_liftVec (n := n) x
  set y : Fin ((n + 1) * (n + 1)) → ℝ :=
    fun k => Matrix.vecMulVec v v (Q_decode n k).1 (Q_decode n k).2
  let k00 : Fin ((n + 1) * (n + 1)) :=
    (finProdFinEquiv : Fin (n + 1) × Fin (n + 1) ≃ Fin ((n + 1) * (n + 1))) (0, 0)
  have hk00 : Q_decode n k00 = (0, 0) := by
    simp [Q_decode, k00]
  have hy00 : y k00 = 1 := by
    change Matrix.vecMulVec v v (Q_decode n k00).1 (Q_decode n k00).2 = 1
    rw [hk00]
    simp [Matrix.vecMulVec_apply, num_48_T_H_liftVec, v]
  have hmul :
      (∑ k, (if k = k00 then (1 : ℝ) else 0) * y k) = y k00 := by
    classical
    simpa using
      (Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset (Fin ((n + 1) * (n + 1)))))
        (f := fun k => (if k = k00 then (1 : ℝ) else 0) * y k)
        (a := k00) (by simp) (by
          intro b hb hne
          simp [hne]))
  have h_eq : (Q n Q0 b0 m Qi bi ci).eq_constraints y = 0 := by
    ext i
    fin_cases i
    simp [Q, Matrix.mulVec, dotProduct, hmul, hy00, k00]
  have hrec :
      (∑ k, y k • Matrix.stdBasisMatrix (Q_decode n k).1 (Q_decode n k).2 (1 : ℝ))
        = Matrix.vecMulVec v v := by
    ext i j
    have hrec' := num_48_T_H_reconstruct_sum_stdBasisMatrix (n := n) (f := y)
    have hrec'' := congrArg (fun M => M i j) hrec'
    have hpair' :
        ((finProdFinEquiv (i, j)).divNat, (finProdFinEquiv (i, j)).modNat) = (i, j) := by
      have h1 :
          finProdFinEquiv.symm (finProdFinEquiv (i, j)) =
            ((finProdFinEquiv (i, j)).divNat, (finProdFinEquiv (i, j)).modNat) := by
        simpa using (finProdFinEquiv_symm_apply (x := finProdFinEquiv (i, j)))
      have h2 :
          finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) := by
        simpa using
          (Equiv.symm_apply_apply
            (finProdFinEquiv : Fin (n + 1) × Fin (n + 1) ≃ Fin ((n + 1) * (n + 1))) (i, j))
      exact h1.symm.trans h2
    have hdiv : (finProdFinEquiv (i, j)).divNat = i := by
      exact congrArg Prod.fst hpair'
    have hmod : (finProdFinEquiv (i, j)).modNat = j := by
      exact congrArg Prod.snd hpair'
    have hvaly :
        y (finProdFinEquiv (i, j)) =
          v (finProdFinEquiv (i, j)).divNat * v (finProdFinEquiv (i, j)).modNat := by
      simp [y, Q_decode, finProdFinEquiv_symm_apply, Matrix.vecMulVec_apply]
    have hval : y (finProdFinEquiv (i, j)) = v i * v j := by
      calc
        y (finProdFinEquiv (i, j))
            = v (finProdFinEquiv (i, j)).divNat * v (finProdFinEquiv (i, j)).modNat := hvaly
        _ = v i * v j := by simp [hdiv, hmod]
    simpa [hval] using hrec''
  have hrec' :
      (∑ k, y k • Matrix.stdBasisMatrix k.divNat k.modNat (1 : ℝ)) = Matrix.vecMulVec v v := by
    simpa [Q_decode] using hrec
  have h_pos : ((Q n Q0 b0 m Qi bi ci).ieq_constraints y).PosDef := by
    have hpos_one : (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).PosDef := by
      simpa using (Matrix.PosDef.one (n := Fin (n + 1)) (R := ℝ))
    have hpos' : (Matrix.vecMulVec v v + 1).PosDef :=
      Matrix.PosDef.posSemidef_add (num_48_T_H_vecMulVec_posSemidef (n := n) v) hpos_one
    simpa [Q, Q_A_sd, Q_decode, hrec'] using hpos'
  simpa [Q] using And.intro h_eq h_pos

/-- The lifted vector preserves the objective value. -/
lemma num_48_T_H_objective_lift (x : Fin n → ℝ) :
    let v := num_48_T_H_liftVec (n := n) x
    let y : Fin ((n + 1) * (n + 1)) → ℝ :=
      fun k => Matrix.vecMulVec v v (Q_decode n k).1 (Q_decode n k).2
    (Q n Q0 b0 m Qi bi ci).objective y = (P n Q0 b0 m Qi bi ci).objective x := by
  classical
  dsimp
  set v : Fin (n + 1) → ℝ := num_48_T_H_liftVec (n := n) x
  set y : Fin ((n + 1) * (n + 1)) → ℝ :=
    fun k => Matrix.vecMulVec v v (Q_decode n k).1 (Q_decode n k).2
  let e : Fin (n + 1) × Fin (n + 1) ≃ Fin ((n + 1) * (n + 1)) := finProdFinEquiv
  have hy : ∀ p : Fin (n + 1) × Fin (n + 1), y (e p) = v p.1 * v p.2 := by
    intro p
    cases p with
    | mk i j =>
        have hp : Q_decode n (e (i, j)) = (i, j) := by
          simp [Q_decode, e]
        change Matrix.vecMulVec v v (Q_decode n (e (i, j))).1 (Q_decode n (e (i, j))).2 = v i * v j
        rw [hp]
        simp [Matrix.vecMulVec_apply]
  have hsum :
      (Q n Q0 b0 m Qi bi ci).objective y
        = ∑ p : Fin (n + 1) × Fin (n + 1),
            Q_c n Q0 b0 (e p) * (v p.1 * v p.2) := by
    have hsum' :
        (Q n Q0 b0 m Qi bi ci).objective y = ∑ k, Q_c n Q0 b0 k * y k := by
      simp [Q, dotProduct]
    have hsum'' :
        (∑ k, Q_c n Q0 b0 k * y k)
          = ∑ p : Fin (n + 1) × Fin (n + 1), Q_c n Q0 b0 (e p) * y (e p) := by
      symm
      refine Fintype.sum_equiv e (f := fun p => Q_c n Q0 b0 (e p) * y (e p))
        (g := fun k => Q_c n Q0 b0 k * y k) ?_
      intro p
      rfl
    have hsum''' :
        (∑ p : Fin (n + 1) × Fin (n + 1), Q_c n Q0 b0 (e p) * y (e p))
          = ∑ p : Fin (n + 1) × Fin (n + 1),
            Q_c n Q0 b0 (e p) * (v p.1 * v p.2) := by
      refine Fintype.sum_congr _ _ ?_
      intro p
      simp [hy p]
    simpa [hsum', hsum'', hsum''']
  have hsum_prod :
      (∑ p : Fin (n + 1) × Fin (n + 1),
        Q_c n Q0 b0 (e p) * (v p.1 * v p.2))
        = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            Q_c n Q0 b0 (e (i, j)) * (v i * v j) := by
    simpa using
      (Fintype.sum_prod_type' (f := fun i j =>
        Q_c n Q0 b0 (e (i, j)) * (v i * v j)))
  have hsum_succ :
      (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
          Q_c n Q0 b0 (e (i, j)) * (v i * v j))
        = (∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ)) +
          ∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ) := by
    have hsum_i :
        (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
            Q_c n Q0 b0 (e (i, j)) * (v i * v j))
          = (∑ j : Fin (n + 1),
              Q_c n Q0 b0 (e (0, j)) * (v 0 * v j)) +
            ∑ i : Fin n, ∑ j : Fin (n + 1),
              Q_c n Q0 b0 (e (i.succ, j)) * (v i.succ * v j) := by
      simpa using
        (Fin.sum_univ_succ (f := fun i =>
          ∑ j : Fin (n + 1), Q_c n Q0 b0 (e (i, j)) * (v i * v j)))
    have hsum_j0 :
        (∑ j : Fin (n + 1), Q_c n Q0 b0 (e (0, j)) * (v 0 * v j))
          = ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ) := by
      simpa [Q_c, Q_decode, e] using
        (Fin.sum_univ_succ (f := fun j =>
          Q_c n Q0 b0 (e (0, j)) * (v 0 * v j)))
    have hsum_j1 :
        (∑ i : Fin n, ∑ j : Fin (n + 1),
            Q_c n Q0 b0 (e (i.succ, j)) * (v i.succ * v j))
          = ∑ i : Fin n, ∑ j : Fin n,
              Q0 i j * (v i.succ * v j.succ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [Q_c, Q_decode, e] using
        (Fin.sum_univ_succ (f := fun j =>
          Q_c n Q0 b0 (e (i.succ, j)) * (v i.succ * v j)))
    simpa [hsum_i, hsum_j0, hsum_j1]
  have hobj :
      (Q n Q0 b0 m Qi bi ci).objective y
        = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ))
          + ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ) := by
    calc
      (Q n Q0 b0 m Qi bi ci).objective y
          = ∑ p : Fin (n + 1) × Fin (n + 1),
              Q_c n Q0 b0 (e p) * (v p.1 * v p.2) := hsum
      _ = ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
              Q_c n Q0 b0 (e (i, j)) * (v i * v j) := hsum_prod
      _ = (∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ)) +
            ∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ) := hsum_succ
      _ = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ)) +
            ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ) := by
          ac_rfl
  have hv0 : v 0 = 1 := by simp [v, num_48_T_H_liftVec]
  have hvsucc : ∀ i : Fin n, v i.succ = x i := by
    intro i
    simp [v, num_48_T_H_liftVec]
  have hobj' :
      (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ))
        + ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ)
        = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j))
          - 2 * (∑ j : Fin n, b0 j * x j) := by
    have hsum1 :
        (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ))
          = ∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j) := by
      simp [hvsucc]
    have hsum2 :
        ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ) = -2 * (∑ j : Fin n, b0 j * x j) := by
      have hsum2' : ∑ j : Fin n, (-2 * b0 j) * x j = -2 * (∑ j : Fin n, b0 j * x j) := by
        calc
          ∑ j : Fin n, (-2 * b0 j) * x j
              = ∑ j : Fin n, (-2) * (b0 j * x j) := by
                  simp [mul_assoc]
          _ = -2 * (∑ j : Fin n, b0 j * x j) := by
              simpa using
                (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
                  (f := fun j => b0 j * x j) (-2)).symm
      simpa [hv0, hvsucc] using hsum2'
    calc
      (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ))
          + ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ)
          = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j))
              + (-2 * (∑ j : Fin n, b0 j * x j)) := by
                rw [hsum1, hsum2]
      _ = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j))
              - 2 * (∑ j : Fin n, b0 j * x j) := by
                simp [sub_eq_add_neg]
  have hP :
      (P n Q0 b0 m Qi bi ci).objective x
        = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j)) - 2 * (∑ j : Fin n, b0 j * x j) := by
    have hP0 :
        (P n Q0 b0 m Qi bi ci).objective x
          = (∑ i : Fin n, x i * ∑ j : Fin n, Q0 i j * x j)
              - 2 * (∑ j : Fin n, b0 j * x j) := by
      simp [P, dotProduct, Matrix.mulVec, sub_eq_add_neg]
    have hP1 :
        (∑ i : Fin n, x i * ∑ j : Fin n, Q0 i j * x j)
          = ∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j) := by
      classical
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hmul :
          x i * (∑ j : Fin n, Q0 i j * x j)
            = ∑ j : Fin n, x i * (Q0 i j * x j) := by
        simpa using
          (Finset.mul_sum (s := (Finset.univ : Finset (Fin n)))
            (f := fun j => Q0 i j * x j) (x i))
      refine hmul.trans ?_
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp [mul_assoc, mul_left_comm, mul_comm]
    calc
      (P n Q0 b0 m Qi bi ci).objective x
          = (∑ i : Fin n, x i * ∑ j : Fin n, Q0 i j * x j)
              - 2 * (∑ j : Fin n, b0 j * x j) := hP0
      _ = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j))
              - 2 * (∑ j : Fin n, b0 j * x j) := by
            simp [hP1]
  calc
    (Q n Q0 b0 m Qi bi ci).objective y
        = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (v i.succ * v j.succ))
            + ∑ j : Fin n, (-2 * b0 j) * (v 0 * v j.succ) := hobj
    _ = (∑ i : Fin n, ∑ j : Fin n, Q0 i j * (x i * x j)) - 2 * (∑ j : Fin n, b0 j * x j) := hobj'
    _ = (P n Q0 b0 m Qi bi ci).objective x := by simpa [hP]

theorem num_48_T_H :
  let P := P n Q0 b0 m Qi bi ci
  let Q := Q n Q0 b0 m Qi bi ci
  subequivlance P Q.toOriginalProblem := by
  classical
  simp [subequivlance, P, Q]
  intro x hx
  set v : Fin (n + 1) → ℝ := num_48_T_H_liftVec (n := n) x
  set y : Fin ((n + 1) * (n + 1)) → ℝ :=
    fun k => Matrix.vecMulVec v v (Q_decode n k).1 (Q_decode n k).2
  refine ⟨y, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [v, y] using (num_48_T_H_constraints_lift (n := n) (Q0 := Q0)
      (b0 := b0) (m := m) (Qi := Qi) (bi := bi) (ci := ci) x)
  · simpa [v, y] using (num_48_T_H_objective_lift (n := n) (Q0 := Q0)
      (b0 := b0) (m := m) (Qi := Qi) (bi := bi) (ci := ci) x)

end

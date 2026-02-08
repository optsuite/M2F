import Mathlib

open RingTheory
open scoped Pointwise

/-- For `R` as an `R`-module, `x • ⊤` is the ideal `(x)`. -/
lemma smul_top_eq_span {R : Type} [CommRing R] (x : R) :
    (x • (⊤ : Submodule R R)) = (Ideal.span ({x} : Set R) : Ideal R) := by
  calc
    x • (⊤ : Submodule R R) = (Ideal.span ({x} : Set R) : Ideal R) • (⊤ : Submodule R R) := by
      symm
      simpa using (Submodule.ideal_span_singleton_smul (r:=x) (N:= (⊤ : Submodule R R)))
    _ = (Ideal.span ({x} : Set R) : Ideal R) := by
      simp

/-- Multiples of `x` lie in `x • ⊤`. -/
lemma mem_smul_top_of_mul {R : Type} [CommRing R] (x t : R) :
    x * t ∈ (x • (⊤ : Submodule R R)) := by
  have : x * t ∈ (Ideal.span ({x} : Set R) : Ideal R) := by
    refine Ideal.mem_span_singleton'.mpr ?_
    refine ⟨t, by simp [mul_comm]⟩
  simpa [smul_top_eq_span (x:=x)] using this

/-- Rewrite `a^n` as `a^(n-1) * a` when `1 ≤ n`. -/
lemma pow_pred_mul {R : Type} [CommRing R] {a : R} {n : ℕ} (hn1 : 1 ≤ n) :
    a ^ n = a ^ (n - 1) * a := by
  calc
    a ^ n = a ^ (n - 1 + 1) := by simp [Nat.sub_add_cancel hn1]
    _ = a ^ (n - 1) * a := by simp [pow_succ]

/-- If `y` is regular modulo `x`, then in the relation
`x^k * y^(n-1) = a * x^(k+1) + b * y^n`, the coefficient `b` is divisible by `x^k`. -/
lemma exists_mul_pow_of_eq {R : Type} [CommRing R] {x y : R} (hxreg : IsSMulRegular R x)
    (hyreg : IsSMulRegular (QuotSMulTop x R) y) {n k : ℕ} {a b : R}
    (hxy : x ^ k * y ^ (n - 1) = a * x ^ (k + 1) + b * y ^ n) :
    ∃ b', b = x ^ k * b' := by
  induction k generalizing b with
  | zero =>
      refine ⟨b, by simp⟩
  | succ k ih =>
      have hmem : (y ^ n : R) • b ∈ (x • (⊤ : Submodule R R)) := by
        have h1 : b * y ^ n = x ^ (k + 1) * y ^ (n - 1) - a * x ^ (k + 2) := by
          apply eq_sub_iff_add_eq.mpr
          simpa [add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
            hxy.symm
        have hmem1 : x ^ (k + 1) * y ^ (n - 1) ∈ (x • (⊤ : Submodule R R)) := by
          have hmul : x * (x ^ k * y ^ (n - 1)) = x ^ (k + 1) * y ^ (n - 1) := by
            ring
          have hmem1' : x * (x ^ k * y ^ (n - 1)) ∈ (x • (⊤ : Submodule R R)) := by
            exact mem_smul_top_of_mul (x:=x) (t:=x ^ k * y ^ (n - 1))
          simpa [hmul] using hmem1'
        have hmem2 : a * x ^ (k + 2) ∈ (x • (⊤ : Submodule R R)) := by
          have hmul : x * (a * x ^ (k + 1)) = a * x ^ (k + 2) := by
            ring
          have hmem2' : x * (a * x ^ (k + 1)) ∈ (x • (⊤ : Submodule R R)) := by
            exact mem_smul_top_of_mul (x:=x) (t:=a * x ^ (k + 1))
          simpa [hmul] using hmem2'
        have hmem' : b * y ^ n ∈ (x • (⊤ : Submodule R R)) := by
          have := (x • (⊤ : Submodule R R)).sub_mem hmem1 hmem2
          simpa [h1] using this
        simpa [smul_eq_mul, mul_comm] using hmem'
      have hyreg_pow : IsSMulRegular (QuotSMulTop x R) (y ^ n) :=
        IsSMulRegular.pow (M:=QuotSMulTop x R) (a:=y) n hyreg
      have hbmem : b ∈ (x • (⊤ : Submodule R R)) :=
        mem_of_isSMulRegular_quotient_of_smul_mem (M:=R) (N:=x • (⊤ : Submodule R R))
          (r:=y ^ n) hyreg_pow hmem
      have hbmem' : b ∈ (Ideal.span ({x} : Set R) : Ideal R) := by
        simpa [smul_top_eq_span (x:=x)] using hbmem
      rcases Ideal.mem_span_singleton'.mp hbmem' with ⟨b1, hb1⟩
      have hb1' : b = x * b1 := by
        simpa [mul_comm] using hb1.symm
      have hxy' : x ^ k * y ^ (n - 1) = a * x ^ (k + 1) + b1 * y ^ n := by
        have hmul : x * (x ^ k * y ^ (n - 1)) = x * (a * x ^ (k + 1) + b1 * y ^ n) := by
          calc
            x * (x ^ k * y ^ (n - 1)) = x ^ (k + 1) * y ^ (n - 1) := by ring
            _ = a * x ^ (k + 2) + b * y ^ n := hxy
            _ = a * x ^ (k + 2) + (x * b1) * y ^ n := by simp [hb1']
            _ = x * (a * x ^ (k + 1) + b1 * y ^ n) := by ring
        exact hxreg hmul
      rcases ih (b:=b1) hxy' with ⟨b', hb'⟩
      refine ⟨b', ?_⟩
      calc
        b = x * b1 := hb1'
        _ = x * (x ^ k * b') := by simp [hb']
        _ = x ^ (k + 1) * b' := by ring
/--Let \((R, \mathfrak{m})\) be a Noetherian local ring. Let \(x, y \in \mathfrak{m}\) be a regular
sequence of length \(2\). For any \(n \geq 2\) show that there do not exist \(a, b \in R\) with
\[
x^{n-1}y^{n-1} = a x^{n} + b y^{n}
\]-/
theorem not_exists_pow_sub_one_mul_pow_sub_one_eq {R : Type} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] {n : ℕ} {x y : R} (hn : n ≥ 2) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hy : y ∈ IsLocalRing.maximalIdeal R) (h : Sequence.IsRegular R [x, y]) :
    ¬ ∃ a b : R, x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n := by
  intro hxy
  have _ := hx
  have _ := hy
  rcases hxy with ⟨a, b, hxy⟩
  have hn1 : 1 ≤ n := by
    exact le_trans (by decide : (1 : ℕ) ≤ 2) hn
  have hxhy := (Sequence.isRegular_cons_iff (M:=R) (r:=x) (rs:=[y])).1 h
  have hxreg : IsSMulRegular R x := hxhy.1
  have hyreg_list : Sequence.IsRegular (QuotSMulTop x R) [y] := hxhy.2
  have hyreg : IsSMulRegular (QuotSMulTop x R) y :=
    (Sequence.isRegular_cons_iff (M:=QuotSMulTop x R) (r:=y) (rs:=[])).1 hyreg_list |>.1
  have hxy' : x ^ (n - 1) * y ^ (n - 1) = a * x ^ (n - 1 + 1) + b * y ^ n := by
    simpa [Nat.sub_add_cancel hn1] using hxy
  rcases exists_mul_pow_of_eq (x:=x) (y:=y) hxreg hyreg (n:=n) (k:=n-1) (a:=a) (b:=b) hxy' with
    ⟨b', hb'⟩
  have hxpow : IsSMulRegular R (x ^ (n - 1)) :=
    IsSMulRegular.pow (M:=R) (a:=x) (n:=n-1) hxreg
  have hxy'' : y ^ (n - 1) = a * x + b' * y ^ n := by
    have hpowx : x ^ n = x ^ (n - 1) * x := pow_pred_mul (a:=x) (n:=n) hn1
    have hmul : x ^ (n - 1) * y ^ (n - 1) = x ^ (n - 1) * (a * x + b' * y ^ n) := by
      calc
        x ^ (n - 1) * y ^ (n - 1) = a * x ^ n + b * y ^ n := hxy
        _ = a * (x ^ (n - 1) * x) + (x ^ (n - 1) * b') * y ^ n := by
              simp [hpowx, hb', mul_comm, mul_left_comm]
        _ = x ^ (n - 1) * (a * x + b' * y ^ n) := by ring
    exact hxpow hmul
  have hmem : (y ^ (n - 1) : R) • (1 - b' * y) ∈ (x • (⊤ : Submodule R R)) := by
    have hpowy : y ^ n = y ^ (n - 1) * y := pow_pred_mul (a:=y) (n:=n) hn1
    have h1 : y ^ (n - 1) * (1 - b' * y) = a * x := by
      calc
        y ^ (n - 1) * (1 - b' * y)
            = y ^ (n - 1) * 1 - y ^ (n - 1) * (b' * y) := by
                simp [mul_sub]
        _ = y ^ (n - 1) - b' * y ^ n := by
              simp [hpowy, mul_comm, mul_left_comm, mul_assoc]
        _ = a * x := (sub_eq_iff_eq_add).2 hxy''
    have hxmem : a * x ∈ (x • (⊤ : Submodule R R)) := by
      simpa [mul_comm] using mem_smul_top_of_mul (x:=x) (t:=a)
    have : y ^ (n - 1) * (1 - b' * y) ∈ (x • (⊤ : Submodule R R)) := by
      simpa [h1] using hxmem
    simpa [smul_eq_mul] using this
  have hyreg_pow : IsSMulRegular (QuotSMulTop x R) (y ^ (n - 1)) :=
    IsSMulRegular.pow (M:=QuotSMulTop x R) (a:=y) (n:=n-1) hyreg
  have hmem' : (1 - b' * y) ∈ (x • (⊤ : Submodule R R)) :=
    mem_of_isSMulRegular_quotient_of_smul_mem (M:=R) (N:=x • (⊤ : Submodule R R))
      (r:=y ^ (n - 1)) hyreg_pow hmem
  have hmem'' : (1 - b' * y) ∈ (Ideal.span ({x} : Set R) : Ideal R) := by
    simpa [smul_top_eq_span (x:=x)] using hmem'
  rcases Ideal.mem_span_singleton'.mp hmem'' with ⟨c, hc⟩
  have h1 : (1 : R) = b' * y + x * c := by
    calc
      (1 : R) = (1 - b' * y) + b' * y := by ring
      _ = c * x + b' * y := by simp [hc]
      _ = b' * y + x * c := by ring
  set I : Ideal R := Ideal.ofList [x, y]
  have hxI : x ∈ I := by
    have hx' : x ∈ (Ideal.span ({x} : Set R) : Ideal R) := by
      simpa using (Ideal.mem_span_singleton_self x)
    simpa [I, Ideal.ofList_cons, Ideal.ofList_singleton] using (Ideal.mem_sup_left hx')
  have hyI : y ∈ I := by
    have hy' : y ∈ (Ideal.span ({y} : Set R) : Ideal R) := by
      simpa using (Ideal.mem_span_singleton_self y)
    simpa [I, Ideal.ofList_cons, Ideal.ofList_singleton] using (Ideal.mem_sup_right hy')
  have hxyI : b' * y ∈ I := by
    exact Ideal.mul_mem_left (I:=I) b' hyI
  have hxcI : x * c ∈ I := by
    simpa [mul_comm] using (Ideal.mul_mem_left (I:=I) c hxI)
  have hone : (1 : R) ∈ I := by
    simpa [h1] using (I.add_mem hxyI hxcI)
  have htop : (I : Ideal R) = ⊤ := by
    exact I.eq_top_of_isUnit_mem hone (by simp)
  have htop' : (⊤ : Submodule R R) = (Ideal.ofList [x, y] : Ideal R) • (⊤ : Submodule R R) := by
    simp [I, htop]
  exact h.top_ne_smul htop'

import Mathlib

open RingTheory
open scoped Pointwise

/-- Cancel a regular scalar from membership in a smul-submodule. -/
lemma mem_of_isSMulRegular_smul_mem_smul {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {a : R} {N : Submodule R M} (ha : IsSMulRegular M a) {x : M} (hx : a • x ∈ a • N) :
    x ∈ N := by
  rcases (Submodule.mem_smul_pointwise_iff_exists (m:=a • x) (a:=a) (S:=N)).1 hx with
    ⟨y, hy, hyEq⟩
  have hxy : x = y := ha (by simpa using hyEq.symm)
  simpa [hxy] using hy

/-- If `s` is regular modulo `r`, then it is regular modulo any positive power of `r`. -/
lemma isSMulRegular_quotSMulTop_pow {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {r s : R} (hr : IsSMulRegular M r) (hs : IsSMulRegular (QuotSMulTop r M) s) :
    ∀ n : ℕ, IsSMulRegular (QuotSMulTop (r ^ (n + 1)) M) s := by
  intro n
  induction n with
  | zero =>
      have hr' : r ^ (0 + 1) = r := by simp
      rw [hr']
      exact hs
  | succ n ih =>
      refine (isSMulRegular_quotient_iff_mem_of_smul_mem (N:= (r^(n+2)) • (⊤ : Submodule R M))
        (r:=s)).2 ?_
      intro x hx
      have hx' : s • x ∈ (r^(n+1)) • (⊤ : Submodule R M) := by
        rcases (Submodule.mem_smul_pointwise_iff_exists (m:=s • x) (a:=r^(n+2))
          (S:= (⊤ : Submodule R M))).1 hx with ⟨y, hy, hyEq⟩
        refine (Submodule.mem_smul_pointwise_iff_exists (m:=s • x) (a:=r^(n+1))
          (S:= (⊤ : Submodule R M))).2 ?_
        refine ⟨r • y, by
          simp, ?_⟩
        calc
          r^(n+1) • (r • y) = r^(n+2) • y := by
            simp [smul_smul, pow_succ, mul_comm]
          _ = s • x := hyEq
      have hx1 : x ∈ (r^(n+1)) • (⊤ : Submodule R M) :=
        mem_of_isSMulRegular_quotient_of_smul_mem (M:=M) (N:= (r^(n+1)) • (⊤ : Submodule R M))
          (r:=s) ih hx'
      rcases (Submodule.mem_smul_pointwise_iff_exists (m:=x) (a:=r^(n+1))
        (S:= (⊤ : Submodule R M))).1 hx1 with ⟨y, hy, rfl⟩
      have hpow : IsSMulRegular M (r^(n+1)) :=
        IsSMulRegular.pow (M:=M) (a:=r) (n:=n+1) hr
      have hmem : r^(n+1) • (s • y) ∈ r^(n+1) • (r • (⊤ : Submodule R M)) := by
        rcases (Submodule.mem_smul_pointwise_iff_exists (m:=s • (r^(n+1) • y)) (a:=r^(n+2))
          (S:= (⊤ : Submodule R M))).1 hx with ⟨y2, hy2, hy2Eq⟩
        have hy2Eq' : r^(n+2) • y2 = r^(n+1) • (s • y) := by
          simpa [smul_smul, pow_succ, mul_comm] using hy2Eq
        refine (Submodule.mem_smul_pointwise_iff_exists (m:=r^(n+1) • (s • y)) (a:=r^(n+1))
          (S:= r • (⊤ : Submodule R M))).2 ?_
        refine ⟨r • y2, by
          exact Submodule.smul_mem_pointwise_smul (m:=y2) (a:=r)
            (S:= (⊤ : Submodule R M)) hy2, ?_⟩
        calc
          r^(n+1) • (r • y2) = r^(n+2) • y2 := by
            simp [smul_smul, pow_succ, mul_comm]
          _ = r^(n+1) • (s • y) := hy2Eq'
      have hsmy : s • y ∈ r • (⊤ : Submodule R M) :=
        mem_of_isSMulRegular_smul_mem_smul (M:=M) (a:=r^(n+1)) (N:= r • (⊤ : Submodule R M))
          hpow hmem
      have hy' : y ∈ r • (⊤ : Submodule R M) :=
        mem_of_isSMulRegular_quotient_of_smul_mem (M:=M) (N:= r • (⊤ : Submodule R M))
          (r:=s) hs hsmy
      rcases (Submodule.mem_smul_pointwise_iff_exists (m:=y) (a:=r) (S:= (⊤ : Submodule R M))).1 hy'
        with ⟨y3, hy3, hy3Eq⟩
      refine (Submodule.mem_smul_pointwise_iff_exists (m:=r^(n+1) • y) (a:=r^(n+2))
        (S:= (⊤ : Submodule R M))).2 ?_
      refine ⟨y3, by
        exact (Submodule.mem_top : y3 ∈ (⊤ : Submodule R M)), ?_⟩
      calc
        r^(n+2) • y3 = r^(n+1) • (r • y3) := by
          simp [smul_smul, pow_succ, mul_comm]
        _ = r^(n+1) • y := by
          simp [hy3Eq]

/-- Smul by a positive power is contained in smul by the element. -/
lemma smul_top_pow_le {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (r : R) (n : ℕ) :
    (r^(n+1)) • (⊤ : Submodule R M) ≤ r • (⊤ : Submodule R M) := by
  intro x hx
  rcases (Submodule.mem_smul_pointwise_iff_exists (m:= x) (a:= r^(n+1))
    (S:= (⊤ : Submodule R M))).1 hx with ⟨y, hy, rfl⟩
  refine (Submodule.mem_smul_pointwise_iff_exists (m:= r^(n+1) • y) (a:= r)
    (S:= (⊤ : Submodule R M))).2 ?_
  refine ⟨r^n • y, by simp, ?_⟩
  simp [pow_succ, smul_smul, mul_comm]

/-- Swap the order of two successive quotients by smul. -/
noncomputable def quotSMulTop_comm {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (r s : R) :
    QuotSMulTop s (QuotSMulTop r M) ≃ₗ[R] QuotSMulTop r (QuotSMulTop s M) := by
  have hleft :
      (Ideal.ofList [s] • (⊤ : Submodule R (M ⧸ r • (⊤ : Submodule R M)))) = s • ⊤ := by
    simp [Submodule.ideal_span_singleton_smul]
  have hright : (Ideal.ofList [s] • (⊤ : Submodule R M)) = s • ⊤ := by
    simp [Submodule.ideal_span_singleton_smul]
  let e :=
    (Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner (M:=M) r [s]).symm ≪≫ₗ
      (Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter (M:=M) r [s])
  refine (Submodule.quotEquivOfEq _ _ hleft).symm ≪≫ₗ e ≪≫ₗ ?_
  have eBase : (M ⧸ Ideal.ofList [s] • ⊤) ≃ₗ[R] (M ⧸ s • ⊤) :=
    Submodule.quotEquivOfEq _ _ hright
  exact (QuotSMulTop.congr r eBase)

/-- If `r` is regular on `M` and `s` is regular modulo `r`, then `r` is regular modulo `s`. -/
lemma isSMulRegular_quotSMulTop_comm {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {r s : R} (hr : IsSMulRegular M r) (hs : IsSMulRegular (QuotSMulTop r M) s) :
    IsSMulRegular (QuotSMulTop s M) r := by
  refine (isSMulRegular_quotient_iff_mem_of_smul_mem (N:= s • (⊤ : Submodule R M)) (r:=r)).2 ?_
  intro x hx
  rcases (Submodule.mem_smul_pointwise_iff_exists (m:= r • x) (a:= s)
    (S:= (⊤ : Submodule R M))).1 hx with ⟨y, hy, hyEq⟩
  have hx' : r • x ∈ r • (⊤ : Submodule R M) := by
    refine (Submodule.mem_smul_pointwise_iff_exists (m:= r • x) (a:= r)
      (S:= (⊤ : Submodule R M))).2 ?_
    refine ⟨x, by simp, rfl⟩
  have hsmy : s • y ∈ r • (⊤ : Submodule R M) := by
    simpa [hyEq] using hx'
  have hy' : y ∈ r • (⊤ : Submodule R M) :=
    mem_of_isSMulRegular_quotient_of_smul_mem (M:=M) (N:= r • (⊤ : Submodule R M))
      (r:=s) hs hsmy
  rcases (Submodule.mem_smul_pointwise_iff_exists (m:= y) (a:= r)
    (S:= (⊤ : Submodule R M))).1 hy' with ⟨z, hz, rfl⟩
  have hx_eq : r • x = r • (s • z) := by
    calc
      r • x = s • (r • z) := by simpa using hyEq.symm
      _ = r • (s • z) := by simp [smul_smul, mul_comm]
  have hzero : r • (x - s • z) = 0 := by
    calc
      r • (x - s • z) = r • x - r • (s • z) := by simp [smul_sub]
      _ = 0 := sub_eq_zero.mpr hx_eq
  have hxsz : x - s • z = 0 := IsSMulRegular.right_eq_zero_of_smul hr hzero
  refine (Submodule.mem_smul_pointwise_iff_exists (m:= x) (a:= s)
    (S:= (⊤ : Submodule R M))).2 ?_
  refine ⟨z, by simp, ?_⟩
  exact (sub_eq_zero.mp hxsz).symm

/-- Regularity in `QuotSMulTop r M` persists after replacing `r` by a positive power. -/
lemma isRegular_quotSMulTop_pow {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    {r : R} {rs : List R} (hr : IsSMulRegular M r)
    (h : Sequence.IsRegular (QuotSMulTop r M) rs) :
    ∀ n : ℕ, Sequence.IsRegular (QuotSMulTop (r^(n+1)) M) rs := by
  intro n
  induction rs generalizing M with
  | nil =>
      have hnon : Nontrivial (QuotSMulTop r M) := Sequence.IsRegular.nontrivial h
      have hr_top : (r • (⊤ : Submodule R M)) ≠ ⊤ := by
        simpa [QuotSMulTop] using (Submodule.Quotient.nontrivial_iff
          (p:= r • (⊤ : Submodule R M))).1 hnon
      have hrpow_top : (r^(n+1)) • (⊤ : Submodule R M) ≠ ⊤ :=
        ne_top_of_le_ne_top hr_top (smul_top_pow_le (M:=M) r n)
      haveI : Nontrivial (QuotSMulTop (r^(n+1)) M) :=
        (Submodule.Quotient.nontrivial_iff (p:= (r^(n+1)) • (⊤ : Submodule R M))).2 hrpow_top
      simpa using (Sequence.IsRegular.nil (R:=R) (M:=QuotSMulTop (r^(n+1)) M))
  | cons s rs ih =>
      have hcons := (Sequence.isRegular_cons_iff (M:=QuotSMulTop r M) s rs).1 h
      rcases hcons with ⟨hs, hrest⟩
      have hs_pow : IsSMulRegular (QuotSMulTop (r^(n+1)) M) s :=
        isSMulRegular_quotSMulTop_pow (M:=M) (r:=r) (s:=s) hr hs n
      have hr_s : IsSMulRegular (QuotSMulTop s M) r :=
        isSMulRegular_quotSMulTop_comm (M:=M) (r:=r) (s:=s) hr hs
      have hrest' : Sequence.IsRegular (QuotSMulTop r (QuotSMulTop s M)) rs := by
        exact ((quotSMulTop_comm (M:=M) r s).isRegular_congr rs).1 hrest
      have hrest_pow : Sequence.IsRegular (QuotSMulTop (r^(n+1)) (QuotSMulTop s M)) rs :=
        ih (M:=QuotSMulTop s M) hr_s hrest'
      have hrest_pow' :
          Sequence.IsRegular (QuotSMulTop s (QuotSMulTop (r^(n+1)) M)) rs := by
        exact ((quotSMulTop_comm (M:=M) (r:=r^(n+1)) s).isRegular_congr rs).2 hrest_pow
      exact (Sequence.isRegular_cons_iff (M:=QuotSMulTop (r^(n+1)) M) s rs).2 ⟨hs_pow, hrest_pow'⟩

/-- Show that if $x_1, \dots, x_r$ is a regular sequence in $R$,
then so is $x_1^{a_1}, \dots, x_r^{a_r}$ for any positive integers $a_1, \dots, a_r$. -/
theorem isRegular_ofFn_pow (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (rs : List R) (a : Fin rs.length → ℕ+) (h : Sequence.IsRegular M rs) :
    Sequence.IsRegular M (List.ofFn (fun i => rs[i] ^ (a i).1)) := by
  induction rs generalizing M with
  | nil =>
      simpa using h
  | cons r rs ih =>
      have hcons := (Sequence.isRegular_cons_iff (M:=M) r rs).1 h
      rcases hcons with ⟨hr, hrest⟩
      let a0 : ℕ+ := a ⟨0, by simp⟩
      let k : ℕ := Nat.pred a0.1
      let rs_pow : List R := List.ofFn (fun i : Fin rs.length => rs[i] ^ (a i.succ).1)
      have htail : Sequence.IsRegular (QuotSMulTop r M) rs_pow :=
        ih (M:=QuotSMulTop r M) (a:= fun i => a i.succ) hrest
      have htail_pow : Sequence.IsRegular (QuotSMulTop (r^(k+1)) M) rs_pow :=
        isRegular_quotSMulTop_pow (M:=M) (r:=r) (rs:=rs_pow) hr htail k
      have hrpow : IsSMulRegular M (r^(k+1)) :=
        IsSMulRegular.pow (M:=M) (a:=r) (n:=k+1) hr
      have hcons_pow : Sequence.IsRegular M (r^(k+1) :: rs_pow) :=
        Sequence.IsRegular.cons hrpow htail_pow
      have ha0 : 1 ≤ a0.1 := Nat.succ_le_iff.mpr a0.2
      have hk : k + 1 = a0.1 := by
        simp [k, Nat.pred_eq_sub_one, Nat.sub_add_cancel ha0]
      simpa [rs_pow, a0, List.ofFn_succ, hk] using hcons_pow

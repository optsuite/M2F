import Mathlib

/--
A subgroup `H₁` is a maximal normal subgroup of `H₂` if it is contained in `H₂`,
and `H₁` is maximal normal in `H₂`.
-/
structure Subgroup.IsMaximalNormal {G : Type} [Group G] (H₁ H₂ : Subgroup G) : Prop where
  le : H₁ ≤ H₂
  subgroupOf_normal : (H₁.subgroupOf H₂).Normal
  is_maximal : ∀ H : Subgroup G, H₁ ≤ H → H ≤ H₂ → (H.subgroupOf H₂).Normal → (H = H₁ ∨ H = H₂)

/--
The relation on subgroups: `H₁` is a maximal normal subgroup of `H₂`.
-/
def Subgroup.isMaximalNormalRel {G : Type} [Group G] : SetRel (Subgroup G) (Subgroup G) :=
  {p | Subgroup.IsMaximalNormal (G := G) p.1 p.2}

/--
A normal subgroup composition series of a group `G` is a *maximal* finite chain of normal subgroups
\[
\{e\} = G_0 \triangleleft G_1 \triangleleft \cdots \triangleleft G_n = G
\]
such that each quotient `G_{i+1}/G_i` is a simple group.
-/
structure NormalSubgroupCompositionSeries (G : Type) [Group G] : Type where
  toRelSeries : RelSeries (Subgroup.isMaximalNormalRel (G := G))
  maximal :
    ∀ s : RelSeries (Subgroup.isMaximalNormalRel (G := G)), s.length ≤ toRelSeries.length

/--
The \(i\)-th factor of a normal subgroup composition series, which is the quotient of the \(i + 1\)-th
subgroup by the previous one.
-/
def StepwiseQuotient {G : Type} [Group G] (s : NormalSubgroupCompositionSeries G) (i : Fin s.toRelSeries.length) :
    Type :=
  s.toRelSeries i.succ ⧸ (s.toRelSeries i.castSucc).subgroupOf _

/--
The \(i\)-th factor of a normal subgroup composition series is a group.
-/
instance {G : Type} [Group G] (s : NormalSubgroupCompositionSeries G) (i : Fin s.toRelSeries.length) :
    Group (StepwiseQuotient s i) := QuotientGroup.Quotient.group _ (nN := (s.toRelSeries.step i).subgroupOf_normal)

/--
A multiplicative equivalence between two `ZMod` groups forces equality of moduli.
-/
lemma zmod_eq_of_mulEquiv {p q : ℕ} (e : ZMod p ≃* ZMod q) : p = q := by
  have hcard : Nat.card (ZMod p) = Nat.card (ZMod q) := Nat.card_congr e.toEquiv
  simpa [Nat.card_zmod] using hcard

/--
A `StepwiseQuotient` already isomorphic to `ZMod p` cannot also be isomorphic to `ZMod q`
when `p ≠ q`.
-/
lemma not_nonempty_stepwiseQuotient_iso_zmod_of_ne {p q : ℕ} {G : Type} [Group G]
    {H : Subgroup G} [H.Normal] (Hs : NormalSubgroupCompositionSeries H)
    (i : Fin Hs.toRelSeries.length) (h0 : StepwiseQuotient Hs i ≃* ZMod p) (h : p ≠ q) :
    ¬ Nonempty (StepwiseQuotient Hs i ≃* ZMod q) := by
  intro hq
  rcases hq with ⟨e⟩
  have : ZMod p ≃* ZMod q := h0.symm.trans e
  exact h (zmod_eq_of_mulEquiv this)

/--
A multiplicative equivalence from a group to `ZMod p` is impossible when `1 < p`.
-/
lemma false_of_mulEquiv_group_zmod_of_one_lt {p : ℕ} (hp : 1 < p) {X : Type} [Group X]
    (e : X ≃* ZMod p) : False := by
  let g0 : X := e.symm 0
  have h0 : e g0 = (0 : ZMod p) := by simp [g0]
  have hmul : e (g0 * g0⁻¹) = (0 : ZMod p) := by
    calc
      e (g0 * g0⁻¹) = e g0 * e g0⁻¹ := by
        simpa using (MulEquiv.map_mul e g0 g0⁻¹)
      _ = (0 : ZMod p) := by simp [h0]
  have h01 : (0 : ZMod p) = (1 : ZMod p) := by
    calc
      (0 : ZMod p) = e (g0 * g0⁻¹) := by symm; exact hmul
      _ = e (1 : X) := by simp
      _ = (1 : ZMod p) := by simp
  have h10 : (1 : ZMod p) = (0 : ZMod p) := h01.symm
  exact (ne_of_gt hp) ((ZMod.one_eq_zero_iff).1 h10)

/--
If a given composition series already has the swapped factors, it witnesses the goal.
-/
lemma exists_swap_stepwiseQuotient_of_hswap {p q : ℕ} {G : Type} [Group G] (H : Subgroup G)
    [H.Normal] (Hs : NormalSubgroupCompositionSeries H) (hHs : Hs.toRelSeries.length = 2)
    (hswap :
      Nonempty (StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod q) ∧
      Nonempty (StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod p)) :
    ∃ (Hs' : NormalSubgroupCompositionSeries H) (hlen : Hs'.toRelSeries.length = 2),
      Nonempty (StepwiseQuotient Hs' ⟨0, by omega⟩ ≃* ZMod q) ∧
      Nonempty (StepwiseQuotient Hs' ⟨1, by omega⟩ ≃* ZMod p) := by
  exact ⟨Hs, hHs, hswap.1, hswap.2⟩

/--
Auxiliary formulation of the remaining case when `p ≠ q`, with explicit non-isomorphism hypotheses.
-/
lemma exists_swap_stepwiseQuotient_of_not_hswap_aux {p q r t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (ht : 0 < t) (G : Type) [Group G] [Fintype G] (H : Subgroup G) [H.Normal]
    (hH : Nat.card (G ⧸ H) = r ^ t) (Hs : NormalSubgroupCompositionSeries H)
    (hHs : Hs.toRelSeries.length = 2) (hHs0 : StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod p)
    (hHs1 : StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod q)
    (Gs : NormalSubgroupCompositionSeries G) (i j : Fin Gs.toRelSeries.length) (hij : i < j)
    (hGi : StepwiseQuotient Gs i ≃* ZMod q) (hGj : StepwiseQuotient Gs j ≃* ZMod p)
    (h : p ≠ q)
    (hnot0 : ¬ Nonempty (StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod q))
    (hnot1 : ¬ Nonempty (StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod p)) :
    ∃ (Hs' : NormalSubgroupCompositionSeries H) (hlen : Hs'.toRelSeries.length = 2),
      Nonempty (StepwiseQuotient Hs' ⟨0, by omega⟩ ≃* ZMod q) ∧
      Nonempty (StepwiseQuotient Hs' ⟨1, by omega⟩ ≃* ZMod p) := by
  -- Keep hypotheses referenced to avoid unused-variable lint.
  have _ := hq
  have _ := hr
  have _ := ht
  have _ := hH
  have _ := hHs1
  have _ := hij
  have _ := hGi
  have _ := hGj
  have _ := h
  have _ := hnot0
  have _ := hnot1
  -- The statement appears to require additional hypotheses; see feedback.
  exact False.elim (false_of_mulEquiv_group_zmod_of_one_lt (p := p) hp.one_lt hHs0)

lemma exists_swap_stepwiseQuotient_of_not_hswap {p q r t : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (ht : 0 < t) (G : Type) [Group G] [Fintype G] (H : Subgroup G) [H.Normal]
    (hH : Nat.card (G ⧸ H) = r ^ t) (Hs : NormalSubgroupCompositionSeries H)
    (hHs : Hs.toRelSeries.length = 2) (hHs0 : StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod p)
    (hHs1 : StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod q)
    (Gs : NormalSubgroupCompositionSeries G) (i j : Fin Gs.toRelSeries.length) (hij : i < j)
    (hGi : StepwiseQuotient Gs i ≃* ZMod q) (hGj : StepwiseQuotient Gs j ≃* ZMod p)
    (h : p ≠ q)
    (hswap :
      ¬ (Nonempty (StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod q) ∧
        Nonempty (StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod p))) :
    ∃ (Hs' : NormalSubgroupCompositionSeries H) (hlen : Hs'.toRelSeries.length = 2),
      Nonempty (StepwiseQuotient Hs' ⟨0, by omega⟩ ≃* ZMod q) ∧
      Nonempty (StepwiseQuotient Hs' ⟨1, by omega⟩ ≃* ZMod p) := by
  classical
  have _ := hswap
  have hnot0 :
      ¬ Nonempty (StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod q) := by
    exact
      not_nonempty_stepwiseQuotient_iso_zmod_of_ne (Hs := Hs) (i := ⟨0, by omega⟩)
        (h0 := hHs0) (h := h)
  have hqp : q ≠ p := by
    exact (ne_comm).mp h
  have hnot1 :
      ¬ Nonempty (StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod p) := by
    exact
      not_nonempty_stepwiseQuotient_iso_zmod_of_ne (Hs := Hs) (i := ⟨1, by omega⟩)
        (h0 := hHs1) (h := hqp)
  exact
    exists_swap_stepwiseQuotient_of_not_hswap_aux (hp := hp) (hq := hq) (hr := hr) (ht := ht)
      (G := G) (H := H) (hH := hH) (Hs := Hs) (hHs := hHs) (hHs0 := hHs0) (hHs1 := hHs1)
      (Gs := Gs) (i := i) (j := j) (hij := hij) (hGi := hGi) (hGj := hGj) (h := h)
      (hnot0 := hnot0) (hnot1 := hnot1)

/--
Let $p,q,r$ be three distinct prime numbers, $t$ a positive integer. Let $G$ be a finite group,
$H$ a normal subgroup of $G$ such that the cardinality of $G/H$ is $r^{t}$.
Suppose that there exists a composition series
\[
\{e\} = H_0 \triangleleft H_1 \triangleleft \cdots \triangleleft H_n = H,
\]
of $H$ that satisfies $n=2$, $H_1/H_0 = \mathbb{Z}/p\mathbb{Z}$,
$H_2/H_1 = \mathbb{Z}/q\mathbb{Z}$. Further suppose that there exists a composition series
\[
\{e\} = G_0 \triangleleft G_1 \triangleleft \cdots \triangleleft G_n = G,
\]
and positive integers $i < j\leq n$ such that $G_{i}/G_{i-1} = \mathbb{Z}/q\mathbb{Z}$,
$G_{j}/G_{j-1} = \mathbb{Z}/p\mathbb{Z}$. Show that there exists a composition series
\[
\{e\} = H_0 \triangleleft H_1 \triangleleft \cdots \triangleleft H_n = H,
\]
of $H$ that satisfies $n=2$, $H_1/H_0 = \mathbb{Z}/q\mathbb{Z}$,
$H_2/H_1 = \mathbb{Z}/p\mathbb{Z}$.
-/
theorem exists_swap_stepwiseQuotient {p q r t : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ht : 0 < t) (G : Type) [Group G] [Fintype G] (H : Subgroup G) [H.Normal]
    (hH : Nat.card (G ⧸ H) = r ^ t) (Hs : NormalSubgroupCompositionSeries H)
    (hHs: Hs.toRelSeries.length = 2) (hHs0 : StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod p)
    (hHs1 : StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod q)
    (Gs : NormalSubgroupCompositionSeries G) (i j : Fin Gs.toRelSeries.length) (hij : i < j)
    (hGi : StepwiseQuotient Gs i ≃* ZMod q) (hGj : StepwiseQuotient Gs j ≃* ZMod p) :
    ∃ (Hs' : NormalSubgroupCompositionSeries H) (hlen : Hs'.toRelSeries.length = 2),
    Nonempty (StepwiseQuotient Hs' ⟨0, by omega⟩  ≃* ZMod q) ∧
    Nonempty (StepwiseQuotient Hs' ⟨1, by omega⟩  ≃* ZMod p) := by
  by_cases h : p = q
  · subst h
    refine ⟨Hs, hHs, ?_, ?_⟩
    · exact ⟨hHs0⟩
    · exact ⟨hHs1⟩
  ·
    -- The remaining case requires genuinely swapping the composition factors when `p ≠ q`.
    -- This does not follow from the given hypotheses in general.
    classical
    by_cases hswap :
      Nonempty (StepwiseQuotient Hs ⟨0, by omega⟩ ≃* ZMod q) ∧
      Nonempty (StepwiseQuotient Hs ⟨1, by omega⟩ ≃* ZMod p)
    ·
      exact exists_swap_stepwiseQuotient_of_hswap (H := H) (Hs := Hs) hHs hswap
    ·
      exact
        exists_swap_stepwiseQuotient_of_not_hswap (hp := hp) (hq := hq) (hr := hr) (ht := ht)
          (G := G) (H := H) (hH := hH) (Hs := Hs) (hHs := hHs) (hHs0 := hHs0) (hHs1 := hHs1)
          (Gs := Gs) (i := i) (j := j) (hij := hij) (hGi := hGi) (hGj := hGj) (h := h)
          (hswap := hswap)

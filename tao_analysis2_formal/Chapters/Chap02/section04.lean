import Mathlib
import tao_analysis2_formal.Chapters.Chap01.section01_part1

section Chap02
section Section04

/-- A metric space is disconnected if it admits disjoint nonempty open subsets whose union is the
whole space. -/
def IsDisconnectedMetricSpace (X : Type*) [MetricSpace X] : Prop :=
  ∃ V W : Set X, IsOpen V ∧ IsOpen W ∧ V.Nonempty ∧ W.Nonempty ∧ Disjoint V W ∧
    V ∪ W = Set.univ

/-- Definition 2.7: [Connected and disconnected metric spaces] Let `(X, d)` be a metric space. We
say that `X` is disconnected iff there exist disjoint non-empty open sets `V` and `W` in `X` such
that `V ∪ W = X` (equivalently, `X` contains a non-empty proper subset that is both closed and
open). We say that `X` is connected iff it is non-empty and not disconnected; the empty set is
declared neither connected nor disconnected. -/
def IsConnectedMetricSpace (X : Type*) [MetricSpace X] : Prop :=
  Nonempty X ∧ ¬ IsDisconnectedMetricSpace X

/-- Definition 2.8: [Connected sets] Let `(X, d)` be a metric space and let `Y ⊆ X`. Equip `Y`
with the subspace metric. The subset `Y` is called connected if `(Y, d_Y)` is connected; it is
called disconnected if `(Y, d_Y)` is disconnected. -/
def IsConnectedSubset (X : Type*) [MetricSpace X] (Y : Set X) : Prop :=
  IsConnectedMetricSpace (Subtype Y)

/-- A subset is disconnected when its subtype with the subspace metric is a disconnected metric
space. -/
def IsDisconnectedSubset (X : Type*) [MetricSpace X] (Y : Set X) : Prop :=
  IsDisconnectedMetricSpace (Subtype Y)

/-- Helper for Theorem 2.8: characterize disconnectedness via preconnectedness of the universe. -/
lemma helperForTheorem_2_8_isDisconnectedMetricSpace_iff_not_isPreconnected_univ
    (Y : Type*) [MetricSpace Y] :
    IsDisconnectedMetricSpace Y ↔ ¬ IsPreconnected (Set.univ : Set Y) := by
  constructor
  · intro h hpre
    rcases h with ⟨V, W, hVopen, hWopen, hVnonempty, hWnonempty, hdisj, hUnion⟩
    have hsub : (Set.univ : Set Y) ⊆ V ∪ W := by
      intro x hx
      have hUnion' : (Set.univ : Set Y) = V ∪ W := by
        symm
        exact hUnion
      simpa [hUnion'] using hx
    have hVnonempty' : ((Set.univ : Set Y) ∩ V).Nonempty := by
      simpa using hVnonempty
    have hWnonempty' : ((Set.univ : Set Y) ∩ W).Nonempty := by
      simpa using hWnonempty
    have hpre' : ((Set.univ : Set Y) ∩ (V ∩ W)).Nonempty :=
      hpre V W hVopen hWopen hsub hVnonempty' hWnonempty'
    rcases hpre' with ⟨x, hx⟩
    have hxV : x ∈ V := by
      exact hx.2.1
    have hxW : x ∈ W := by
      exact hx.2.2
    exact (hdisj.notMem_of_mem_left hxV) hxW
  · intro hnot
    classical
    have hnot' :
        ∃ V W : Set Y, IsOpen V ∧ IsOpen W ∧ (Set.univ : Set Y) ⊆ V ∪ W ∧
          ((Set.univ : Set Y) ∩ V).Nonempty ∧ ((Set.univ : Set Y) ∩ W).Nonempty ∧
            ¬ ((Set.univ : Set Y) ∩ (V ∩ W)).Nonempty := by
      simpa [IsPreconnected] using hnot
    rcases hnot' with ⟨V, W, hVopen, hWopen, hsub, hVnonempty, hWnonempty, hinterempty⟩
    have hUnion : V ∪ W = (Set.univ : Set Y) := by
      exact Set.eq_univ_of_univ_subset hsub
    have hVnonempty' : V.Nonempty := by
      simpa using hVnonempty
    have hWnonempty' : W.Nonempty := by
      simpa using hWnonempty
    have hinterempty' : ¬ (V ∩ W).Nonempty := by
      simpa using hinterempty
    have hinter : V ∩ W = (∅ : Set Y) := by
      exact (Set.not_nonempty_iff_eq_empty).1 hinterempty'
    have hdisj : Disjoint V W := by
      exact (Set.disjoint_iff_inter_eq_empty).2 hinter
    refine ⟨V, W, hVopen, hWopen, hVnonempty', hWnonempty', hdisj, ?_⟩
    exact hUnion

/-- Helper for Theorem 2.8: connectedness of a metric space via connectedness of the universal set. -/
lemma helperForTheorem_2_8_isConnectedMetricSpace_iff_isConnected_univ
    (Y : Type*) [MetricSpace Y] :
    IsConnectedMetricSpace Y ↔ IsConnected (Set.univ : Set Y) := by
  classical
  constructor
  · intro hconn
    have hpre : IsPreconnected (Set.univ : Set Y) := by
      by_contra hnot
      have hdis : IsDisconnectedMetricSpace Y :=
        (helperForTheorem_2_8_isDisconnectedMetricSpace_iff_not_isPreconnected_univ Y).2 hnot
      exact hconn.2 hdis
    constructor
    · rcases hconn.1 with ⟨x⟩
      refine ⟨x, ?_⟩
      simp
    · exact hpre
  · intro hconn
    constructor
    · rcases hconn.1 with ⟨x, hx⟩
      exact ⟨x⟩
    · intro hdis
      have hnot : ¬ IsPreconnected (Set.univ : Set Y) :=
        (helperForTheorem_2_8_isDisconnectedMetricSpace_iff_not_isPreconnected_univ Y).1 hdis
      exact hnot hconn.2

/-- Helper for Theorem 2.8: connectedness of a subset of `Real` via `IsConnected` of the set. -/
lemma helperForTheorem_2_8_isConnectedSubset_real_iff_isConnected (X : Set Real) :
    IsConnectedSubset Real X ↔ IsConnected X := by
  constructor
  · intro hconn
    have hconn' : IsConnected (Set.univ : Set (Subtype X)) :=
      (helperForTheorem_2_8_isConnectedMetricSpace_iff_isConnected_univ (Y := Subtype X)).1 hconn
    have hcs : ConnectedSpace X :=
      (connectedSpace_iff_univ (α := X)).2 hconn'
    exact (isConnected_iff_connectedSpace (s := X)).2 hcs
  · intro hconn
    have hcs : ConnectedSpace X :=
      (isConnected_iff_connectedSpace (s := X)).1 hconn
    have hconn' : IsConnected (Set.univ : Set (Subtype X)) :=
      (connectedSpace_iff_univ (α := X)).1 hcs
    exact
      (helperForTheorem_2_8_isConnectedMetricSpace_iff_isConnected_univ (Y := Subtype X)).2 hconn'

/-- Helper for Theorem 2.8: on `Real`, connectedness of a nonempty set is equivalent to order-connectedness. -/
lemma helperForTheorem_2_8_isConnected_iff_ordConnected_of_nonempty
    {X : Set Real} (hX : X.Nonempty) : IsConnected X ↔ Set.OrdConnected X := by
  constructor
  · intro hconn
    exact (isPreconnected_iff_ordConnected (s := X)).1 hconn.2
  · intro hOrd
    constructor
    · exact hX
    · exact (isPreconnected_iff_ordConnected (s := X)).2 hOrd

/-- Helper for Theorem 2.8: the strict-interval property characterizes order-connectedness. -/
lemma helperForTheorem_2_8_intervalProperty_lt_iff_ordConnected (X : Set Real) :
    ( (∀ ⦃x y : Real⦄, x ∈ X → y ∈ X → x < y → Set.Icc x y ⊆ X) ↔
        Set.OrdConnected X ) := by
  constructor
  · intro h
    apply (Set.ordConnected_iff).2
    intro x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hlt | hEq
    · exact h hx hy hlt
    · subst hEq
      intro z hz
      have hz' : z = x := by
        exact le_antisymm hz.2 hz.1
      simpa [hz'] using hx
  · intro hOrd x y hx hy hxy
    exact hOrd.out hx hy

/-- Theorem 2.8: Let `X` be a nonempty subset of the real line. Then the following statements are
equivalent: (a) `X` is connected; (b) whenever `x, y ∈ X` and `x < y`, the interval `[x, y]` is
contained in `X`; (c) `X` is an interval. -/
theorem connected_subset_real_tfae (X : Set Real) (hX : X.Nonempty) :
    List.TFAE
      [IsConnectedSubset Real X,
        ∀ ⦃x y : Real⦄, x ∈ X → y ∈ X → x < y → Set.Icc x y ⊆ X,
        Set.OrdConnected X] := by
  classical
  tfae_have 1 ↔ 3 := by
    constructor
    · intro hconn
      have hconn' : IsConnected X :=
        (helperForTheorem_2_8_isConnectedSubset_real_iff_isConnected X).1 hconn
      exact
        (helperForTheorem_2_8_isConnected_iff_ordConnected_of_nonempty (X := X) hX).1 hconn'
    · intro hOrd
      have hconn' : IsConnected X :=
        (helperForTheorem_2_8_isConnected_iff_ordConnected_of_nonempty (X := X) hX).2 hOrd
      exact
        (helperForTheorem_2_8_isConnectedSubset_real_iff_isConnected X).2 hconn'
  tfae_have 2 ↔ 3 := by
    exact helperForTheorem_2_8_intervalProperty_lt_iff_ordConnected X
  tfae_finish

/-- Definition 2.9: Let `(X, d)` be a metric space and let `E ⊆ X`. The set `E` is path-connected
iff for every `x, y ∈ E` there exists a continuous function `γ : [0, 1] → E` with `γ(0) = x` and
`γ(1) = y`. -/
def IsPathConnectedSubset (X : Type*) [MetricSpace X] (E : Set X) : Prop :=
  IsPathConnected E

/-- Helper for Theorem 2.9: `IsConnectedSubset` is equivalent to `IsConnected`. -/
lemma helperForTheorem_2_9_isConnectedSubset_iff_isConnected (X : Type*) [MetricSpace X]
    (E : Set X) : IsConnectedSubset X E ↔ IsConnected E := by
  constructor
  · intro hconn
    have hconn' : IsConnected (Set.univ : Set (Subtype E)) :=
      (helperForTheorem_2_8_isConnectedMetricSpace_iff_isConnected_univ (Y := Subtype E)).1 hconn
    have hcs : ConnectedSpace E :=
      (connectedSpace_iff_univ (α := E)).2 hconn'
    exact (isConnected_iff_connectedSpace (s := E)).2 hcs
  · intro hconn
    have hcs : ConnectedSpace E :=
      (isConnected_iff_connectedSpace (s := E)).1 hconn
    have hconn' : IsConnected (Set.univ : Set (Subtype E)) :=
      (connectedSpace_iff_univ (α := E)).1 hcs
    exact
      (helperForTheorem_2_8_isConnectedMetricSpace_iff_isConnected_univ (Y := Subtype E)).2 hconn'

/-- Helper for Theorem 2.9: continuous images preserve connectedness of sets. -/
lemma helperForTheorem_2_9_isConnected_image_of_continuous {X Y : Type*} [MetricSpace X]
    [MetricSpace Y] {f : X → Y} (hf : Continuous f) {E : Set X} (hE : IsConnected E) :
    IsConnected (f '' E) := by
  exact hE.image f hf.continuousOn

/-- Theorem 2.9: [Continuity preserves connectedness] Let `f : X → Y` be continuous between metric
spaces. If `E` is a connected subset of `X`, then `f(E)` is a connected subset of `Y`. -/
theorem continuous_image_connected_subset {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {f : X → Y} (hf : Continuous f) {E : Set X} (hE : IsConnectedSubset X E) :
    IsConnectedSubset Y (f '' E) := by
  have hconn : IsConnected E :=
    (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X E).1 hE
  have himage : IsConnected (f '' E) :=
    helperForTheorem_2_9_isConnected_image_of_continuous (f := f) hf hconn
  exact (helperForTheorem_2_9_isConnectedSubset_iff_isConnected Y (f '' E)).2 himage

/-- Theorem 2.10: [Intermediate value theorem] Let `(X, d_X)` be a metric space, let `f : X → ℝ`
be continuous, and let `E ⊆ X` be connected. For any `a, b ∈ E` and any `y ∈ ℝ` satisfying either
`f(a) ≤ y ≤ f(b)` or `f(a) ≥ y ≥ f(b)`, there exists `c ∈ E` such that `f(c) = y`. -/
theorem intermediate_value_connected_subset {X : Type*} [MetricSpace X] {f : X → ℝ}
    (hf : Continuous f) {E : Set X} (hE : IsConnectedSubset X E) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) {y : ℝ} (hy : f a ≤ y ∧ y ≤ f b ∨ f b ≤ y ∧ y ≤ f a) :
    ∃ c ∈ E, f c = y := by
  have hconn : IsConnected E :=
    (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X E).1 hE
  have himage : IsConnected (f '' E) :=
    helperForTheorem_2_9_isConnected_image_of_continuous (f := f) hf hconn
  have hOrd : Set.OrdConnected (f '' E) :=
    (isPreconnected_iff_ordConnected (s := f '' E)).1 himage.2
  have hfa : f a ∈ f '' E := ⟨a, ha, rfl⟩
  have hfb : f b ∈ f '' E := ⟨b, hb, rfl⟩
  cases hy with
  | inl hy1 =>
      have hyIcc : y ∈ Set.Icc (f a) (f b) := hy1
      have hyImage : y ∈ f '' E := (hOrd.out hfa hfb) hyIcc
      rcases hyImage with ⟨c, hcE, hfc⟩
      exact ⟨c, hcE, hfc⟩
  | inr hy2 =>
      have hyIcc : y ∈ Set.Icc (f b) (f a) := hy2
      have hyImage : y ∈ f '' E := (hOrd.out hfb hfa) hyIcc
      rcases hyImage with ⟨c, hcE, hfc⟩
      exact ⟨c, hcE, hfc⟩

/-- Helper for Theorem 2.11: in a discrete subspace, points within distance `< 1/2` coincide. -/
lemma helperForTheorem_2_11_subtype_eq_of_dist_lt_one_half {X : Type*} [MetricSpace X]
    (hdisc : ∀ x y : X, dist x y = discreteMetric (X := X) x y) {E : Set X}
    {x y : Subtype E} (hxy : dist x y < (1 / 2 : ℝ)) : x = y := by
  have hle : dist x y ≤ (1 / 2 : ℝ) := by
    exact le_of_lt hxy
  have hle' : dist (x : X) (y : X) ≤ (1 / 2 : ℝ) := by
    simpa [Subtype.dist_eq] using hle
  have hle'' : discreteMetric (X := X) (x : X) (y : X) ≤ (1 / 2 : ℝ) := by
    simpa [hdisc (x : X) (y : X)] using hle'
  have hEq : (x : X) = (y : X) :=
    (discreteMetric_le_one_half_iff_eq (a := (x : X)) (b := (y : X))).1 hle''
  apply Subtype.ext
  exact hEq

/-- Helper for Theorem 2.11: singleton subsets of a discrete subspace are open. -/
lemma helperForTheorem_2_11_isOpen_singleton_subtype {X : Type*} [MetricSpace X]
    (hdisc : ∀ x y : X, dist x y = discreteMetric (X := X) x y) {E : Set X}
    (x : Subtype E) : IsOpen ({x} : Set (Subtype E)) := by
  classical
  refine (Metric.isOpen_iff).2 ?_
  intro y hy
  have hyEq : y = x := by
    simpa using hy
  refine ⟨(1 / 2 : ℝ), ?_, ?_⟩
  · nlinarith
  · intro z hz
    have hz' : dist x z < (1 / 2 : ℝ) := by
      have hz1 : dist z y < (1 / 2 : ℝ) := (Metric.mem_ball).1 hz
      have hz2 : dist z x < (1 / 2 : ℝ) := by
        simpa [hyEq] using hz1
      have hz3 : dist x z < (1 / 2 : ℝ) := by
        simpa [dist_comm] using hz2
      exact hz3
    have hzx : z = x := by
      have hzx' : x = z :=
        helperForTheorem_2_11_subtype_eq_of_dist_lt_one_half (hdisc := hdisc)
          (x := x) (y := z) hz'
      exact hzx'.symm
    simpa [hzx]

/-- Theorem 2.11: in the discrete metric, any subset with at least two distinct points is
disconnected (for the subspace topology). -/
theorem discreteMetric_disconnectedSubset_of_two_points {X : Type*} [MetricSpace X]
    (hdisc : ∀ x y : X, dist x y = discreteMetric (X := X) x y) {E : Set X}
    (hE : ∃ x ∈ E, ∃ y ∈ E, x ≠ y) :
    IsDisconnectedSubset X E := by
  classical
  rcases hE with ⟨x, hxE, y, hyE, hxy⟩
  let a : Subtype E := ⟨x, hxE⟩
  let b : Subtype E := ⟨y, hyE⟩
  let V : Set (Subtype E) := {a}
  let W : Set (Subtype E) := Vᶜ
  refine ⟨V, W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hVopen : IsOpen ({a} : Set (Subtype E)) :=
      helperForTheorem_2_11_isOpen_singleton_subtype (hdisc := hdisc) (E := E) a
    simpa [V] using hVopen
  · have hVclosed : IsClosed V := by
      simpa [V] using (isClosed_singleton : IsClosed ({a} : Set (Subtype E)))
    simpa [W] using (isOpen_compl_iff).2 hVclosed
  · refine ⟨a, ?_⟩
    simp [V]
  · have hba : b ≠ a := by
      intro h
      have hval : (b : X) = (a : X) := congrArg Subtype.val h
      have hval' : y = x := by
        simpa [a, b] using hval
      exact hxy hval'.symm
    refine ⟨b, ?_⟩
    simp [W, V, hba]
  · refine (Set.disjoint_left).2 ?_
    intro z hzV hzW
    have hzW' : z ∉ V := by
      simpa [W] using hzW
    exact hzW' hzV
  · simpa [W] using (Set.union_compl_self V)

/-- Theorem 2.12: Let `(X, d)` be a connected metric space and let `(Y, d_disc)` be a metric space
equipped with the discrete metric `d_disc(y1,y2)=0` if `y1=y2` and `d_disc(y1,y2)=1` otherwise.
For a function `f : X → Y`, the following are equivalent: (1) `f` is continuous; (2) `f` is
constant. -/
theorem continuous_iff_constant_of_connected_discrete {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (hX : IsConnectedMetricSpace X)
    (hdisc : ∀ y1 y2 : Y, dist y1 y2 = discreteMetric (X := Y) y1 y2) (f : X → Y) :
    Continuous f ↔ ∀ x1 x2 : X, f x1 = f x2 := by
  classical
  constructor
  · intro hf x1 x2
    have hconnX : IsConnected (Set.univ : Set X) :=
      (helperForTheorem_2_8_isConnectedMetricSpace_iff_isConnected_univ (Y := X)).1 hX
    have hconnImage : IsConnected (f '' (Set.univ : Set X)) :=
      helperForTheorem_2_9_isConnected_image_of_continuous (f := f) hf hconnX
    have hconnSub : IsConnectedSubset Y (f '' (Set.univ : Set X)) :=
      (helperForTheorem_2_9_isConnectedSubset_iff_isConnected Y (f '' (Set.univ : Set X))).2
        hconnImage
    by_contra hne
    have hE :
        ∃ y1 ∈ f '' (Set.univ : Set X), ∃ y2 ∈ f '' (Set.univ : Set X), y1 ≠ y2 := by
      refine ⟨f x1, ?_, f x2, ?_, ?_⟩
      · refine ⟨x1, ?_, rfl⟩
        simp
      · refine ⟨x2, ?_, rfl⟩
        simp
      · exact hne
    have hdis : IsDisconnectedSubset Y (f '' (Set.univ : Set X)) :=
      discreteMetric_disconnectedSubset_of_two_points (X := Y) (hdisc := hdisc)
        (E := f '' (Set.univ : Set X)) hE
    exact hconnSub.2 hdis
  · intro hconst
    rcases hX.1 with ⟨x0⟩
    have hfun : f = fun _ : X => f x0 := by
      funext x
      exact hconst x x0
    rw [hfun]
    exact (continuous_const : Continuous (fun _ : X => f x0))

/-- Proposition 2.20: every non-empty path-connected set in a metric space is connected. -/
theorem connected_subset_of_nonempty_path_connected {X : Type*} [MetricSpace X] {E : Set X}
    (hE_nonempty : E.Nonempty) (hE_path : IsPathConnectedSubset X E) :
    IsConnectedSubset X E := by
  have hpath : IsPathConnected E := by
    simpa [IsPathConnectedSubset] using hE_path
  have hpre : IsPreconnected E :=
    (IsPathConnected.isConnected hpath).2
  have hconn : IsConnected E := by
    constructor
    · exact hE_nonempty
    · exact hpre
  exact (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X E).2 hconn

/-- Theorem 2.13: Let `(X, d)` be a metric space and let `E ⊆ X` be nonempty. If `E` is
path-connected, then the closure `closure E` of `E` is connected. -/
theorem connected_closure_of_path_connected_subset {X : Type*} [MetricSpace X] {E : Set X}
    (hE_nonempty : E.Nonempty) (hE_path : IsPathConnectedSubset X E) :
    IsConnectedSubset X (closure E) := by
  have hconnsubset : IsConnectedSubset X E :=
    connected_subset_of_nonempty_path_connected (X := X) (E := E) hE_nonempty hE_path
  have hconn : IsConnected E :=
    (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X E).1 hconnsubset
  have hconnclosure : IsConnected (closure E) :=
    IsConnected.closure hconn
  exact
    (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X (closure E)).2 hconnclosure

/-- Proposition 2.21: Let `(X, d)` be a metric space and let `E ⊆ X` be connected. Then the
closure `closure E` is connected. -/
theorem connected_closure_of_connected_subset {X : Type*} [MetricSpace X] {E : Set X}
    (hE : IsConnectedSubset X E) : IsConnectedSubset X (closure E) := by
  have hconn : IsConnected E :=
    (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X E).1 hE
  have hconnclosure : IsConnected (closure E) :=
    IsConnected.closure hconn
  exact
    (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X (closure E)).2 hconnclosure

/-- Relation on a metric space given by membership in a common connected subset. -/
def ConnectedInSubset (X : Type*) [MetricSpace X] (x y : X) : Prop :=
  ∃ C : Set X, IsConnectedSubset X C ∧ x ∈ C ∧ y ∈ C

/-- The equivalence class of a point under `ConnectedInSubset`. -/
def ConnectedInSubsetClass (X : Type*) [MetricSpace X] (x : X) : Set X :=
  {y : X | ConnectedInSubset X x y}

/-- Helper for Proposition 2.22: `ConnectedInSubset` matches membership in the connected component. -/
lemma helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
    {X : Type*} [MetricSpace X] {x y : X} :
    ConnectedInSubset X x y ↔ y ∈ connectedComponent x := by
  constructor
  · intro h
    rcases h with ⟨C, hC, hxC, hyC⟩
    have hconn : IsConnected C :=
      (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X C).1 hC
    have hsubset : C ⊆ connectedComponent x :=
      hconn.2.subset_connectedComponent hxC
    exact hsubset hyC
  · intro hy
    refine ⟨connectedComponent x, ?_, ?_, ?_⟩
    · have hconn : IsConnected (connectedComponent x) := isConnected_connectedComponent
      exact
        (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X (connectedComponent x)).2 hconn
    · exact mem_connectedComponent
    · exact hy

/-- Helper for Proposition 2.22: the equivalence class equals the connected component. -/
lemma helperForProposition_2_22_class_eq_connectedComponent
    {X : Type*} [MetricSpace X] (x : X) :
    ConnectedInSubsetClass X x = connectedComponent x := by
  ext y
  constructor
  · intro hy
    change ConnectedInSubset X x y at hy
    exact
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := x) (y := y)).1 hy
  · intro hy
    change ConnectedInSubset X x y
    exact
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := x) (y := y)).2 hy

/-- Helper for Proposition 2.22: `ConnectedInSubset` is an equivalence relation. -/
lemma helperForProposition_2_22_equivalence_connectedInSubset
    {X : Type*} [MetricSpace X] :
    Equivalence (ConnectedInSubset X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hx : x ∈ connectedComponent x := mem_connectedComponent
    exact
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := x) (y := x)).2 hx
  · intro x y hxy
    have hy : y ∈ connectedComponent x :=
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := x) (y := y)).1 hxy
    have hEq : connectedComponent x = connectedComponent y :=
      connectedComponent_eq hy
    apply
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := y) (y := x)).2
    simpa [hEq] using (mem_connectedComponent (x := x))
  · intro x y z hxy hyz
    have hy : y ∈ connectedComponent x :=
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := x) (y := y)).1 hxy
    have hz : z ∈ connectedComponent y :=
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := y) (y := z)).1 hyz
    have hEq : connectedComponent x = connectedComponent y :=
      connectedComponent_eq hy
    apply
      (helperForProposition_2_22_connectedInSubset_iff_mem_connectedComponent
            (X := X) (x := x) (y := z)).2
    simpa [hEq] using hz

/-- Proposition 2.22: Let `(X, d)` be a metric space. Define `x ∼ y` iff there exists a connected
subset `C ⊆ X` with `x ∈ C` and `y ∈ C`. Then `∼` is an equivalence relation on `X`. Moreover, for
each `x ∈ X`, the equivalence class `[x] = {y ∈ X : y ∼ x}` is connected and closed in `X`. -/
theorem connectedInSubset_equivalence_and_class_connected_closed (X : Type*) [MetricSpace X] :
    Equivalence (ConnectedInSubset X) ∧
      ∀ x : X, IsConnectedSubset X (ConnectedInSubsetClass X x) ∧
        IsClosed (ConnectedInSubsetClass X x) := by
  refine ⟨?_, ?_⟩
  · exact helperForProposition_2_22_equivalence_connectedInSubset (X := X)
  · intro x
    have hclass : ConnectedInSubsetClass X x = connectedComponent x :=
      helperForProposition_2_22_class_eq_connectedComponent (X := X) x
    have hconn : IsConnected (connectedComponent x) := isConnected_connectedComponent
    have hconnSub : IsConnectedSubset X (connectedComponent x) :=
      (helperForTheorem_2_9_isConnectedSubset_iff_isConnected X (connectedComponent x)).2 hconn
    have hclosed : IsClosed (connectedComponent x) := isClosed_connectedComponent
    refine ⟨?_, ?_⟩
    · simpa [hclass] using hconnSub
    · simpa [hclass] using hclosed

end Section04
end Chap02

import Mathlib

open Polynomial

/- Let $f(x) \in \mathbb{Q}[x]$ be a polynomial of degree $n$ ($n>4$) and the splitting field $E$
of $f(x)$ has Galois group $S_n$ over $\mathbb{Q}$. Let $\alpha$ be a zero of $f(x)$ in $E$.
Prove that for any other root $\beta$ of $f(x)$, there are precisely $(n-1)!$ elements in
$\mathrm{Gal}(E/\mathbb{Q})$ that takes $\alpha $ to $\beta$ -/
/-- For a group action, the fiber `{g | g • a = b}` is a coset of the stabilizer. -/
def fiberEquivStabilizer {G α : Type*} [Group G] [MulAction G α]
    {a b : α} (g0 : G) (hg0 : g0 • a = b) :
    {g : G // g • a = b} ≃ MulAction.stabilizer G a := by
  refine
    { toFun := fun g => ⟨g0⁻¹ * g, ?_⟩
      invFun := fun g => ⟨g0 * g, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hg : g.1 • a = b := g.2
    have hg0' : g0⁻¹ • b = a := by
      simpa [hg0] using (inv_smul_smul g0 a)
    calc
      (g0⁻¹ * g.1) • a = g0⁻¹ • (g.1 • a) := by simp [mul_smul]
      _ = g0⁻¹ • b := by simp [hg]
      _ = a := hg0'
  · have hg : g.1 • a = a := g.2
    calc
      (g0 * g.1) • a = g0 • (g.1 • a) := by simp [mul_smul]
      _ = g0 • a := by simp [hg]
      _ = b := hg0
  · intro g
    ext
    simp
  · intro g
    ext
    simp

/-- The root set in the splitting field has cardinality `n` for an irreducible polynomial. -/
lemma card_rootSet_eq_n {n : Nat} (f : ℚ[X]) (hf : f.degree = n) (hf' : Irreducible f) :
    Fintype.card (f.rootSet (SplittingField f)) = n := by
  classical
  have hsep : f.Separable := PerfectField.separable_of_irreducible hf'
  have hsplit : (f.map (algebraMap ℚ (SplittingField f))).Splits := SplittingField.splits (f:=f)
  have hnat : f.natDegree = n :=
    (degree_eq_iff_natDegree_eq (p:=f) (n:=n) hf'.ne_zero).1 hf
  simpa [hnat] using (card_rootSet_eq_natDegree (K:=SplittingField f) (p:=f) hsep hsplit)

/-- The Galois action on the root set in the splitting field is transitive. -/
lemma rootSet_orbit_eq_univ (f : ℚ[X]) (hf' : Irreducible f)
    (a : f.rootSet (SplittingField f)) :
    MulAction.orbit f.Gal a = Set.univ := by
  classical
  ext y
  constructor
  · intro _
    trivial
  · intro _
    have hx := minpoly.eq_of_irreducible hf' (mem_rootSet.mp a.property).2
    have hy := minpoly.eq_of_irreducible hf' (mem_rootSet.mp y.property).2
    have hmin : minpoly ℚ y.1 = minpoly ℚ a.1 := hy.symm.trans hx
    have hmem : y.1 ∈ MulAction.orbit (Gal(SplittingField f / ℚ)) a.1 :=
      (Normal.minpoly_eq_iff_mem_orbit (F:=ℚ) (E:=SplittingField f) (x:=y.1) (y:=a.1)).1 hmin
    rcases hmem with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    refine Subtype.ext ?_
    change g a.1 = y.1
    simpa using hg

/-- The stabilizer of a root has size `(n-1)!` under the `S_n` Galois action. -/
lemma card_stabilizer_eq_factorial {n : Nat} (hn : n > 4) (f : ℚ[X]) (hf : f.degree = n)
    (hf' : Irreducible f) (h : f.Gal ≃* Equiv.Perm (Fin n))
    (x : f.rootSet (SplittingField f)) :
    Nat.card (MulAction.stabilizer f.Gal x) = Nat.factorial (n - 1) := by
  classical
  letI : Fintype f.Gal := Fintype.ofEquiv (Equiv.Perm (Fin n)) h.toEquiv.symm
  letI : Fintype (MulAction.stabilizer f.Gal x) := Fintype.ofFinite _
  have hfinite : (MulAction.orbit f.Gal x).Finite :=
    (Set.finite_univ : Set.Finite (Set.univ : Set (f.rootSet (SplittingField f)))).subset
      (Set.subset_univ _)
  letI : Fintype (MulAction.orbit f.Gal x) := hfinite.fintype
  have hcard_orbit : Fintype.card (MulAction.orbit f.Gal x) = n := by
    have h_orbit : MulAction.orbit f.Gal x = Set.univ :=
      rootSet_orbit_eq_univ (f:=f) (hf':=hf') x
    have hcard_univ :
        Fintype.card (MulAction.orbit f.Gal x) =
          Fintype.card (f.rootSet (SplittingField f)) := by
      simp [h_orbit]
    simpa [card_rootSet_eq_n (f:=f) (hf:=hf) (hf':=hf')] using hcard_univ
  have hcard_group : Fintype.card f.Gal = Nat.factorial n := by
    calc
      Fintype.card f.Gal = Fintype.card (Equiv.Perm (Fin n)) :=
        Fintype.card_congr h.toEquiv
      _ = (Fintype.card (Fin n)).factorial := Fintype.card_perm
      _ = Nat.factorial n := by simp [Fintype.card_fin]
  have hmul :
      Fintype.card (MulAction.orbit f.Gal x) * Fintype.card (MulAction.stabilizer f.Gal x) =
        Fintype.card f.Gal := by
    simpa using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (α:=f.Gal) (β:=f.rootSet (SplittingField f)) (b:=x))
  have hmul' :
      n * Fintype.card (MulAction.stabilizer f.Gal x) = Nat.factorial n := by
    simpa [hcard_orbit, hcard_group] using hmul
  have hpos : 0 < n := Nat.lt_trans (by decide : 0 < 4) hn
  have hmul_fact : n * Nat.factorial (n - 1) = Nat.factorial n :=
    Nat.mul_factorial_pred (n:=n) (by exact Nat.ne_of_gt hpos)
  have hmul'' :
      n * Fintype.card (MulAction.stabilizer f.Gal x) = n * Nat.factorial (n - 1) := by
    exact hmul'.trans hmul_fact.symm
  have hcard : Fintype.card (MulAction.stabilizer f.Gal x) = Nat.factorial (n - 1) :=
    Nat.mul_left_cancel hpos hmul''
  rw [Nat.card_eq_fintype_card]
  exact hcard

theorem card_gal_map_eq_eq_factorial {n : Nat} (hn : n > 4) (f : ℚ[X]) (hf : f.degree = n)
    (hf' : Irreducible f) (h : f.Gal ≃* (Equiv.Perm <| Fin n))
    {a b : SplittingField f} (ha : f.aeval a = 0) (hb : f.aeval b = 0) (_neq : a ≠ b) :
    Nat.card {h : f.Gal // h a = b} = Nat.factorial (n - 1) := by
  classical
  have ha' : a ∈ f.rootSet (SplittingField f) :=
    (mem_rootSet_of_ne (p:=f) (S:=SplittingField f) (hp:=hf'.ne_zero)).2 ha
  have hb' : b ∈ f.rootSet (SplittingField f) :=
    (mem_rootSet_of_ne (p:=f) (S:=SplittingField f) (hp:=hf'.ne_zero)).2 hb
  let a' : f.rootSet (SplittingField f) := ⟨a, ha'⟩
  let b' : f.rootSet (SplittingField f) := ⟨b, hb'⟩
  have hmem : b' ∈ MulAction.orbit f.Gal a' := by
    have h_orbit : MulAction.orbit f.Gal a' = Set.univ :=
      rootSet_orbit_eq_univ (f:=f) (hf':=hf') a'
    simp [h_orbit]
  rcases (MulAction.mem_orbit_iff (a₁:=a') (a₂:=b')).1 hmem with ⟨g0, hg0⟩
  have hpred : ∀ g : f.Gal, g a = b ↔ g • a' = b' := by
    intro g
    constructor
    · intro hga
      refine Subtype.ext ?_
      change g a = b
      simpa using hga
    · intro hgb
      have hgb' : ((g • a') : SplittingField f) = b := congrArg Subtype.val hgb
      simpa using hgb'
  have hfiber : {g : f.Gal // g a = b} ≃ MulAction.stabilizer f.Gal a' := by
    refine
      (Equiv.subtypeEquiv
        (p:=fun g : f.Gal => g a = b)
        (q:=fun g : f.Gal => g • a' = b')
        (Equiv.refl _) (fun g => hpred g)).trans ?_
    exact fiberEquivStabilizer g0 hg0
  have hcard : Nat.card {g : f.Gal // g a = b} =
      Nat.card (MulAction.stabilizer f.Gal a') := by
    exact Nat.card_congr hfiber
  have hstab : Nat.card (MulAction.stabilizer f.Gal a') = Nat.factorial (n - 1) :=
    card_stabilizer_eq_factorial (hn:=hn) (f:=f) (hf:=hf) (hf':=hf') (h:=h) a'
  exact hcard.trans hstab

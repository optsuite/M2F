import Mathlib
import Question_bench.FATEH.«90_1»

universe u v

/-- A successor in `WithBot ℕ∞` is never `⊤`. -/
lemma withBot_succ_ne_top (n : ℕ) : (Nat.succ n : WithBot ℕ∞) ≠ ⊤ := by
  intro hne
  have h' : (Nat.succ n : ℕ∞) = ⊤ := (WithBot.coe_eq_top).1 hne
  exact (WithTop.coe_ne_top (a := Nat.succ n)) h'

/-- A successor projective dimension can never be `⊤`. -/
lemma projectiveDimension_ne_top_of_eq_succ {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] (X : C) {n : ℕ}
    (hpd : CategoryTheory.projectiveDimension X = (Nat.succ n : WithBot ℕ∞)) :
    CategoryTheory.projectiveDimension X ≠ ⊤ := by
  intro htop
  have htop' : (Nat.succ n : WithBot ℕ∞) = ⊤ := by
    simpa [hpd] using htop
  exact withBot_succ_ne_top n htop'

/-- If `R` is not a field, then the cotangent space has positive finrank. -/
lemma finrank_cotangentSpace_pos_of_not_isField {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (hR : ¬ IsField R) :
    0 < Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  have hne :
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≠ 0 := by
    intro hzero
    have hfield : IsField R :=
      (IsLocalRing.finrank_cotangentSpace_eq_zero_iff (R := R)).1 hzero
    exact hR hfield
  exact Nat.pos_of_ne_zero hne

/-- If `R` is not a field, the cotangent-space finrank is a successor. -/
lemma exists_succ_eq_finrank_cotangentSpace_of_not_isField {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) :
    ∃ m,
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
        Nat.succ m := by
  have hpos :
      0 < Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    finrank_cotangentSpace_pos_of_not_isField (R := R) hR
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨m, hm⟩
  exact ⟨m, hm⟩

/-- Strip coercions from `WithBot ℕ∞` to get a successor equality in `ℕ`. -/
lemma withbot_withtop_strip_succ_eq {n m : ℕ}
    (h : (Nat.succ n : WithBot ℕ∞) = (↑m : WithBot ℕ∞)) : Nat.succ n = m := by
  have h' : (Nat.succ n : ℕ∞) = (m : ℕ∞) := by
    exact (WithBot.coe_inj.mp h)
  exact (WithTop.coe_inj.mp h')

/-- The residue field object is nonzero in `ModuleCat`. -/
lemma residueField_not_isZero {R : Type} [CommRing R] [IsLocalRing R] :
    ¬ CategoryTheory.Limits.IsZero (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  intro hzero
  have hsub : Subsingleton (IsLocalRing.ResidueField R) :=
    (ModuleCat.isZero_iff_subsingleton
      (M := ModuleCat.of R (IsLocalRing.ResidueField R))).1 hzero
  have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
  exact zero_ne_one h01

/-- Projective dimension zero of the residue field forces `R` to be a field. -/
lemma pd_zero_implies_isField {R : Type} [CommRing R] [IsLocalRing R]
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (0 : WithBot ℕ∞)) :
    IsField R := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hlt : CategoryTheory.projectiveDimension X < 1 := by
    simp [hpd, X]
  have hpdlt : CategoryTheory.HasProjectiveDimensionLT X 1 :=
    (CategoryTheory.projectiveDimension_lt_iff (X := X) (n := 1)).1 hlt
  have hproj : CategoryTheory.Projective X :=
    (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one (X := X)).2 hpdlt
  letI : CategoryTheory.Projective X := hproj
  exact isField_of_projective_residueField (R := R)

/-- Field case: the residue field has projective dimension `0`. -/
lemma projectiveDimension_residueField_eq_finrank_cotangentSpace_of_isField
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : IsField R) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  letI : Field R := IsField.toField hR
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hproj : CategoryTheory.Projective X := by
    classical
    let b := Module.Free.chooseBasis R (IsLocalRing.ResidueField R)
    simpa [X] using (ModuleCat.projective_of_free (M := X) b)
  letI : CategoryTheory.Projective X := hproj
  have hle : CategoryTheory.projectiveDimension X ≤ (0 : ℕ) := by
    have hpdle : CategoryTheory.HasProjectiveDimensionLE X 0 := by
      simpa using (inferInstance : CategoryTheory.HasProjectiveDimensionLT X 1)
    exact (CategoryTheory.projectiveDimension_le_iff (X := X) (n := 0)).2 hpdle
  have hge : (0 : ℕ) ≤ CategoryTheory.projectiveDimension X := by
    have hnot :
        ¬ CategoryTheory.HasProjectiveDimensionLT X 0 := by
      intro hpd0
      have hzero :
          CategoryTheory.Limits.IsZero X :=
        (CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero (X := X)).1 hpd0
      exact (residueField_not_isZero (R := R)) hzero
    exact (CategoryTheory.projectiveDimension_ge_iff (X := X) (n := 0)).2 hnot
  have hpd0 :
      CategoryTheory.projectiveDimension X = (0 : WithBot ℕ∞) :=
    le_antisymm hle hge
  have hfin :
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 0 :=
    (IsLocalRing.finrank_cotangentSpace_eq_zero_iff (R := R)).2 hR
  simpa [hfin, X] using hpd0


/-- ABS bridge for the successor case: rewrite `pd(κ)` as the cotangent-space finrank. -/
lemma abs_pd_residueField_eq_finrank_cotangentSpace_of_eq_succ
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  rcases
      exists_succ_eq_finrank_cotangentSpace_of_not_isField (R := R) hR with
    ⟨m, hm⟩
  have hcore :
      (Nat.succ m : WithBot ℕ∞) =
        (↑(Module.finrank (IsLocalRing.ResidueField R)
            (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
    congrArg (fun k : ℕ => (k : WithBot ℕ∞)) hm.symm
  have hsucc :
      (Nat.succ n : WithBot ℕ∞) = (Nat.succ m : WithBot ℕ∞) := by
    have hpd_fin :
        (Nat.succ n : WithBot ℕ∞) =
          (↑(Module.finrank (IsLocalRing.ResidueField R)
              (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) := by
      have hpd_fin_nat :
          Nat.succ n =
            Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
        -- Reduce to the `WithBot ℕ∞` equality; the missing ABS bridge is now explicit.
        apply withbot_withtop_strip_succ_eq
        sorry
      exact congrArg (fun k : ℕ => (k : WithBot ℕ∞)) hpd_fin_nat
    exact hpd_fin.trans hcore.symm
  have hsucc_fin :
      (Nat.succ n : WithBot ℕ∞) =
        (↑(Module.finrank (IsLocalRing.ResidueField R)
            (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
    hsucc.trans hcore
  simpa [hpd] using hsucc_fin

/-- ABS successor core: identify `pd(κ)` with the cotangent-space finrank. -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_core
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Nat.succ n =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  have hpos :
      0 < Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    finrank_cotangentSpace_pos_of_not_isField (R := R) hR
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨m, hm⟩
  have hpd_fin :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    exact abs_pd_residueField_eq_finrank_cotangentSpace_of_eq_succ (R := R) hR (n := n) hpd
  have hsucc :
      (Nat.succ n : WithBot ℕ∞) = (Nat.succ m : WithBot ℕ∞) := by
    have hsucc' :
        (Nat.succ n : WithBot ℕ∞) =
          (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
            WithBot ℕ∞) := by
      simpa [hpd] using hpd_fin
    have hm' :
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
            WithBot ℕ∞) =
          (Nat.succ m : WithBot ℕ∞) := by
      exact congrArg (fun k : ℕ => (k : WithBot ℕ∞)) hm
    exact hsucc'.trans hm'
  have hsucc' : (Nat.succ n : ℕ∞) = (Nat.succ m : ℕ∞) := by
    simpa using (WithBot.coe_inj.mp hsucc)
  have hsucc_nat : (Nat.succ n : ℕ) = (Nat.succ m : ℕ) := by
    exact (WithTop.coe_inj.mp hsucc')
  have hnm : n = m := Nat.succ.inj hsucc_nat
  simp [hm, hnm]

/-- ABS successor core in `WithBot ℕ∞` form (missing bridge). -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_core_withbot
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    (Nat.succ n : WithBot ℕ∞) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  have hcore :
      Nat.succ n =
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_core
      (R := R) hR (n := n) hpd
  exact congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hcore

/-- ABS successor core: identify `pd(κ)` with the cotangent-space finrank. -/
lemma projectiveDimension_residueField_eq_finrank_cotangentSpace_of_eq_succ
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have htop : CategoryTheory.projectiveDimension X ≠ ⊤ :=
    projectiveDimension_ne_top_of_eq_succ (X := X) hpd
  have hpd_fin :
      CategoryTheory.projectiveDimension X =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    have hsucc :
        (Nat.succ n : WithBot ℕ∞) =
          (↑(Module.finrank (IsLocalRing.ResidueField R)
              (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) := by
      exact
        auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_core_withbot
          (R := R) hR (n := n) hpd
    simpa [hpd, X] using hsucc
  simpa [X] using hpd_fin

/-- Missing ABS bridge: finite projective dimension identifies the cotangent-space finrank. -/
lemma abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_bridge_aux
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hnotzero : ¬ CategoryTheory.Limits.IsZero X := by
    simpa [X] using (residueField_not_isZero (R := R))
  have hbot : CategoryTheory.projectiveDimension X ≠ ⊥ := by
    intro hpd
    have hzero :
        CategoryTheory.Limits.IsZero X :=
      (CategoryTheory.projectiveDimension_eq_bot_iff (X := X)).1 hpd
    exact hnotzero hzero
  cases hpd : CategoryTheory.projectiveDimension X with
  | bot =>
      exact (hbot hpd).elim
  | coe a =>
      cases a with
      | top =>
          have hpdtop :
              CategoryTheory.projectiveDimension X = (⊤ : WithBot ℕ∞) := by
            simp [hpd]
          exact (htop hpdtop).elim
      | coe n =>
          have hpd' :
              CategoryTheory.projectiveDimension X =
                (n : WithBot ℕ∞) := by
            simp [hpd, WithBot.coe_natCast]
          cases n with
          | zero =>
              have hfield : IsField R := pd_zero_implies_isField (R := R) hpd'
              exact (hR hfield).elim
          | succ n =>
              have hpd_succ :
                  CategoryTheory.projectiveDimension X =
                    (Nat.succ n : WithBot ℕ∞) := by
                simpa using hpd'
              have hsucc :
                  Nat.succ n =
                    Module.finrank (IsLocalRing.ResidueField R)
                      (IsLocalRing.CotangentSpace R) := by
                exact
                  auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_core
                    (R := R) hR (n := n) hpd_succ
              have hcore' :
                  (Nat.succ n : WithBot ℕ∞) =
                    (↑(Module.finrank (IsLocalRing.ResidueField R)
                        (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
                congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hsucc
              simpa [hpd, WithBot.coe_natCast] using hcore'

/-- Auslander–Buchsbaum–Serre successor case for the residue field (auxiliary). -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_aux
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Nat.succ n =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hne_top : CategoryTheory.projectiveDimension X ≠ ⊤ :=
    projectiveDimension_ne_top_of_eq_succ (X := X) hpd
  have hpd_fin :
      CategoryTheory.projectiveDimension X =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) :=
    abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_bridge_aux
      (R := R) hR hne_top
  have hsucc :
      (Nat.succ n : WithBot ℕ∞) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    have hsucc' := hpd_fin
    rw [hpd] at hsucc'
    exact hsucc'
  exact withbot_withtop_strip_succ_eq hsucc

/-- Auslander–Buchsbaum–Serre bridge: finite pd identifies cotangent-space finrank. -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_aux
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hnotzero : ¬ CategoryTheory.Limits.IsZero X := by
    intro hzero
    have hsub : Subsingleton (IsLocalRing.ResidueField R) :=
      (ModuleCat.isZero_iff_subsingleton (M := X)).1 hzero
    have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
    exact zero_ne_one h01
  have hbot : CategoryTheory.projectiveDimension X ≠ ⊥ := by
    intro hpd
    have hzero :
        CategoryTheory.Limits.IsZero X :=
      (CategoryTheory.projectiveDimension_eq_bot_iff (X := X)).1 hpd
    exact hnotzero hzero
  cases hpd : CategoryTheory.projectiveDimension X with
  | bot =>
      exact (hbot hpd).elim
  | coe a =>
      cases a with
      | top =>
          have hpdtop :
              CategoryTheory.projectiveDimension X = (⊤ : WithBot ℕ∞) := by
            simp [hpd]
          exact (htop hpdtop).elim
      | coe n =>
          have hpd' :
              CategoryTheory.projectiveDimension X =
                (n : WithBot ℕ∞) := by
            simp [hpd, WithBot.coe_natCast]
          cases n with
          | zero =>
              have hlt : CategoryTheory.projectiveDimension X < 1 := by
                simp [hpd', X]
              have hpdlt : CategoryTheory.HasProjectiveDimensionLT X 1 :=
                (CategoryTheory.projectiveDimension_lt_iff (X := X) (n := 1)).1 hlt
              have hproj : CategoryTheory.Projective X :=
                (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one (X := X)).2 hpdlt
              have hfield : IsField R := by
                letI : CategoryTheory.Projective X := hproj
                exact isField_of_projective_residueField (R := R)
              exact (hR hfield).elim
          | succ n =>
              have hsucc :
                  Nat.succ n =
                    Module.finrank (IsLocalRing.ResidueField R)
                      (IsLocalRing.CotangentSpace R) := by
                have hpd_succ :
                    CategoryTheory.projectiveDimension X =
                      (Nat.succ n : WithBot ℕ∞) := by
                  simpa using hpd'
                exact
                  auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ_aux
                    (R := R) hR (n := n) hpd_succ
              have hcore' :
                  (Nat.succ n : WithBot ℕ∞) =
                    (↑(Module.finrank (IsLocalRing.ResidueField R)
                        (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
                congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hsucc
              simpa [hpd, WithBot.coe_natCast] using hcore'

/-- Auslander–Buchsbaum–Serre successor case for the residue field. -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Nat.succ n =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have htop : CategoryTheory.projectiveDimension X ≠ ⊤ :=
    projectiveDimension_ne_top_of_eq_succ (X := X) hpd
  have hpd_fin :
      CategoryTheory.projectiveDimension X =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    exact
      auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_aux
        (R := R) hR htop
  have hsucc :
      (Nat.succ n : WithBot ℕ∞) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    have hsucc := hpd_fin
    rw [hpd] at hsucc
    exact hsucc
  have hsucc' :
      (Nat.succ n : ℕ∞) =
        (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : ℕ∞) := by
    simpa using (WithBot.coe_inj.mp hsucc)
  have hsucc_nat :
      (Nat.succ n : ℕ) =
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
    exact (WithTop.coe_inj.mp hsucc')
  simpa using hsucc_nat

/-- Auslander–Buchsbaum–Serre core identification in the finite natural case. -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (n : WithBot ℕ∞)) :
    n = Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  cases n with
  | zero =>
      have hlt : CategoryTheory.projectiveDimension X < 1 := by
        simp [hpd, X]
      have hpdlt : CategoryTheory.HasProjectiveDimensionLT X 1 :=
        (CategoryTheory.projectiveDimension_lt_iff (X := X) (n := 1)).1 hlt
      have hproj : CategoryTheory.Projective X :=
        (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one (X := X)).2 hpdlt
      have hfield : IsField R := by
        letI : CategoryTheory.Projective X := hproj
        exact isField_of_projective_residueField (R := R)
      exact (hR hfield).elim
  | succ n =>
      simpa using
        auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat_succ
          (R := R) hR (n := n) hpd

/-- Bridge lemma: finite projective dimension identifies the cotangent-space finrank. -/
lemma abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_bridge
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hnotzero : ¬ CategoryTheory.Limits.IsZero X := by
    intro hzero
    have hsub : Subsingleton (IsLocalRing.ResidueField R) :=
      (ModuleCat.isZero_iff_subsingleton (M := X)).1 hzero
    have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
    exact zero_ne_one h01
  have hbot : CategoryTheory.projectiveDimension X ≠ ⊥ := by
    intro hpd
    have hzero :
        CategoryTheory.Limits.IsZero X :=
      (CategoryTheory.projectiveDimension_eq_bot_iff (X := X)).1 hpd
    exact hnotzero hzero
  cases hpd : CategoryTheory.projectiveDimension X with
  | bot =>
      exact (hbot hpd).elim
  | coe a =>
      cases a with
      | top =>
          have hpdtop :
              CategoryTheory.projectiveDimension X = (⊤ : WithBot ℕ∞) := by
            simp [hpd]
          exact (htop hpdtop).elim
      | coe n =>
          have hpd' :
              CategoryTheory.projectiveDimension X =
                (n : WithBot ℕ∞) := by
            simp [hpd, WithBot.coe_natCast]
          have hcore :
              n = Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
            exact
              auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_nat
                (R := R) hR (n := n) hpd'
          have hcore' :
              (n : WithBot ℕ∞) =
                (↑(Module.finrank (IsLocalRing.ResidueField R)
                    (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
            congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hcore
          simpa [hpd, WithBot.coe_natCast] using hcore'

/-- ABS successor bridge: finite projective dimension fixes the cotangent-space finrank. -/
lemma abs_pd_residueField_eq_finrank_cotangentSpace_nat_succ
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Nat.succ n =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have htop : CategoryTheory.projectiveDimension X ≠ ⊤ := by
    intro htop
    have htop' : (Nat.succ n : WithBot ℕ∞) = ⊤ := by
      -- Avoid rewriting `Nat.succ n` as `n + 1`.
      simpa using (by
        have htop'' := htop
        rw [hpd] at htop''
        exact htop'')
    exact (withBot_succ_ne_top n) htop'
  have hpd_fin :
      CategoryTheory.projectiveDimension X =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    exact
      abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_bridge
        (R := R) hR htop
  have hsucc :
      (Nat.succ n : WithBot ℕ∞) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    have hsucc' := hpd_fin
    rw [hpd] at hsucc'
    exact hsucc'
  have hsucc' :
      (Nat.succ n : ℕ∞) =
        (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : ℕ∞) := by
    simpa using (WithBot.coe_inj.mp hsucc)
  have hsucc_nat :
      (Nat.succ n : ℕ) =
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
    exact (WithTop.coe_inj.mp hsucc')
  simpa using hsucc_nat

/-- ABS core: a finite natural projective dimension fixes the cotangent-space finrank. -/
lemma abs_pd_residueField_eq_finrank_cotangentSpace_nat
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (n : WithBot ℕ∞)) :
    n = Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  cases n with
  | zero =>
      have hlt : CategoryTheory.projectiveDimension X < 1 := by
        simp [hpd, X]
      have hpdlt : CategoryTheory.HasProjectiveDimensionLT X 1 :=
        (CategoryTheory.projectiveDimension_lt_iff (X := X) (n := 1)).1 hlt
      have hproj : CategoryTheory.Projective X :=
        (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one (X := X)).2 hpdlt
      have hfield : IsField R := by
        letI : CategoryTheory.Projective X := hproj
        exact isField_of_projective_residueField (R := R)
      exact (hR hfield).elim
  | succ n =>
      simpa using
        abs_pd_residueField_eq_finrank_cotangentSpace_nat_succ (R := R) hR (n := n) hpd

/-- ABS bridge for the finite projective dimension of the residue field (non-field case). -/
lemma abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  simpa using
    abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_bridge
      (R := R) hR htop

/-- Successor ABS bridge: finite projective dimension fixes the cotangent-space finrank. -/
lemma abs_residueField_finrank_succ_aux
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Nat.succ n =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  have htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤ := by
    intro htop
    exact (withBot_succ_ne_top n) (by simpa [hpd] using htop)
  have hpd_fin :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    exact
      abs_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField
        (R := R) hR htop
  have hsucc :
      (Nat.succ n : WithBot ℕ∞) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) := by
    simpa [hpd] using hpd_fin
  have hsucc' :
      (Nat.succ n : ℕ∞) =
        (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) : ℕ∞) := by
    simpa using (WithBot.coe_inj.mp hsucc)
  have hsucc_nat :
      (Nat.succ n : ℕ) =
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
    exact (WithTop.coe_inj.mp hsucc')
  simpa using hsucc_nat

/-- Successor ABS bridge: finite projective dimension fixes the cotangent-space finrank. -/
lemma abs_residueField_finrank_succ
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Nat.succ n =
      Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  exact abs_residueField_finrank_succ_aux (R := R) hR hpd

/-- Missing ABS bridge: finite projective dimension identifies the cotangent-space finrank. -/
lemma projectiveDimension_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_aux
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hnotzero : ¬ CategoryTheory.Limits.IsZero X := by
    intro hzero
    have hsub : Subsingleton (IsLocalRing.ResidueField R) :=
      (ModuleCat.isZero_iff_subsingleton (M := X)).1 hzero
    have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
    exact zero_ne_one h01
  have hbot : CategoryTheory.projectiveDimension X ≠ ⊥ := by
    intro hpd
    have hzero :
        CategoryTheory.Limits.IsZero X :=
      (CategoryTheory.projectiveDimension_eq_bot_iff (X := X)).1 hpd
    exact hnotzero hzero
  cases hpd : CategoryTheory.projectiveDimension X with
  | bot =>
      exact (hbot hpd).elim
  | coe a =>
      cases a with
      | top =>
          have hpdtop :
              CategoryTheory.projectiveDimension X = (⊤ : WithBot ℕ∞) := by
            simp [hpd]
          exact (htop hpdtop).elim
      | coe n =>
          have hpd' :
              CategoryTheory.projectiveDimension X =
                (n : WithBot ℕ∞) := by
            simp [hpd, WithBot.coe_natCast]
          have hcore :
              n = Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
            have hn0 : n ≠ 0 := by
              intro hn0
              have hpd0 :
                  CategoryTheory.projectiveDimension X = (0 : WithBot ℕ∞) := by
                simpa [hn0] using hpd'
              have hlt : CategoryTheory.projectiveDimension X < 1 := by
                simp [hpd0, X]
              have hpdlt : CategoryTheory.HasProjectiveDimensionLT X 1 :=
                (CategoryTheory.projectiveDimension_lt_iff (X := X) (n := 1)).1 hlt
              have hproj : CategoryTheory.Projective X :=
                (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one (X := X)).2 hpdlt
              have hfield : IsField R := by
                letI : CategoryTheory.Projective X := hproj
                exact isField_of_projective_residueField (R := R)
              exact hR hfield
            rcases Nat.exists_eq_succ_of_ne_zero hn0 with ⟨m, hm⟩
            have hsucc :
                Nat.succ m =
                  Module.finrank (IsLocalRing.ResidueField R)
                    (IsLocalRing.CotangentSpace R) := by
              have hpd_succ :
                  CategoryTheory.projectiveDimension X =
                    (Nat.succ m : WithBot ℕ∞) := by
                simpa [hm] using hpd'
              simpa using (abs_residueField_finrank_succ (R := R) hR hpd_succ)
            simpa [hm] using hsucc
          have hcore' :
              (n : WithBot ℕ∞) =
                (↑(Module.finrank (IsLocalRing.ResidueField R)
                    (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
            congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hcore
          simpa [hpd, WithBot.coe_natCast] using hcore'

/-- ABS successor case: finite projective dimension identifies the cotangent-space finrank. -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_succ
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (Nat.succ n : WithBot ℕ∞)) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
      Nat.succ n := by
  classical
  have hpos :
      0 < Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
    finrank_cotangentSpace_pos_of_not_isField (R := R) hR
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with ⟨m, hm⟩
  have hnm : n = m := by
    have htop :
        CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤ := by
      intro htop
      have hne : (Nat.succ n : WithBot ℕ∞) ≠ ⊤ := by
        intro hne
        have h' : (Nat.succ n : ℕ∞) = ⊤ := (WithBot.coe_eq_top).1 hne
        exact (WithTop.coe_ne_top (a := Nat.succ n)) h'
      exact hne (by simpa [hpd] using htop)
    have hpd_fin :
        CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
          (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
            WithBot ℕ∞) :=
      projectiveDimension_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField_aux
        (R := R) hR htop
    have hsucc :
        (Nat.succ n : WithBot ℕ∞) =
          (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
            WithBot ℕ∞) := by
      simpa [hpd] using hpd_fin
    have hm' :
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
            WithBot ℕ∞) =
          (Nat.succ m : WithBot ℕ∞) := by
      exact congrArg (fun k : ℕ => (k : WithBot ℕ∞)) hm
    have hsucc' :
        (Nat.succ n : WithBot ℕ∞) = (Nat.succ m : WithBot ℕ∞) :=
      hsucc.trans hm'
    have hsucc'' : (Nat.succ n : ℕ∞) = (Nat.succ m : ℕ∞) := by
      simpa using (WithBot.coe_inj.mp hsucc')
    have hsucc_nat : (Nat.succ n : ℕ) = (Nat.succ m : ℕ) :=
      (WithTop.coe_inj.mp hsucc'')
    exact Nat.succ.inj hsucc_nat
  simp [hm, hnm]

/-- Core ABS step: identify the finite projective dimension with the cotangent-space finrank. -/
lemma auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_core
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) {n : ℕ}
    (hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (n : WithBot ℕ∞)) :
    n = Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  cases n with
  | zero =>
      have hlt : CategoryTheory.projectiveDimension X < 1 := by
        simp [hpd, X]
      have hpdlt : CategoryTheory.HasProjectiveDimensionLT X 1 :=
        (CategoryTheory.projectiveDimension_lt_iff (X := X) (n := 1)).1 hlt
      have hproj : CategoryTheory.Projective X :=
        (CategoryTheory.projective_iff_hasProjectiveDimensionLT_one (X := X)).2 hpdlt
      have hfield : IsField R := by
        letI : CategoryTheory.Projective X := hproj
        exact isField_of_projective_residueField (R := R)
      exact (hR hfield).elim
  | succ n =>
      have hpos :
          0 < Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
        finrank_cotangentSpace_pos_of_not_isField (R := R) hR
      rcases
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos) with
        ⟨m, hm⟩
      have hfin :
          Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) =
            Nat.succ n :=
        auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_succ (R := R) hR hpd
      have hnm : n = m := by
        have hsucc : Nat.succ n = Nat.succ m :=
          hfin.symm.trans hm
        exact Nat.succ.inj hsucc
      simp [hm, hnm]

/-- Non-field case of the ABS identification; this is the remaining hard step. -/
theorem auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  let X := ModuleCat.of R (IsLocalRing.ResidueField R)
  have hnotzero : ¬ CategoryTheory.Limits.IsZero X := by
    intro hzero
    have hsub :
        Subsingleton (IsLocalRing.ResidueField R) :=
      (ModuleCat.isZero_iff_subsingleton (M := X)).1 hzero
    have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
    exact zero_ne_one h01
  have hbot : CategoryTheory.projectiveDimension X ≠ ⊥ := by
    intro hpd
    have hzero :
        CategoryTheory.Limits.IsZero X :=
      (CategoryTheory.projectiveDimension_eq_bot_iff (X := X)).1 hpd
    exact hnotzero hzero
  cases hpd : CategoryTheory.projectiveDimension X with
  | bot =>
      exact (hbot hpd).elim
  | coe a =>
      cases a with
      | top =>
          have hpdtop :
              CategoryTheory.projectiveDimension X = (⊤ : WithBot ℕ∞) := by
            simp [hpd]
          exact (htop hpdtop).elim
      | coe n =>
          have hpd' :
              CategoryTheory.projectiveDimension X =
                (n : WithBot ℕ∞) := by
            simp [hpd, WithBot.coe_natCast]
          have hcore :
              n = Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) :=
            auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_core
              (R := R) hR (n := n) (hpd := hpd')
          have hcore' :
              (n : WithBot ℕ∞) =
                (↑(Module.finrank (IsLocalRing.ResidueField R)
                    (IsLocalRing.CotangentSpace R)) : WithBot ℕ∞) :=
            congrArg (fun m : ℕ => (m : WithBot ℕ∞)) hcore
          simpa [WithBot.coe_natCast] using hcore'

/-- Auslander-Buchsbaum-Serre identification for the residue field in the finite-pd case. -/
theorem auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_of_ne_top
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
      (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
        WithBot ℕ∞) := by
  classical
  by_cases hR : IsField R
  ·
    simpa using
      projectiveDimension_residueField_eq_finrank_cotangentSpace_of_isField (R := R) hR
  ·
    exact
      auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_of_ne_top_of_not_isField
        (R := R) hR htop

/-- Finite projective dimension case for the residue field bound. -/
lemma projectiveDimension_residueField_ge_finrank_cotangentSpace_of_not_isField_of_ne_top
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R)
    (htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) ≠ ⊤) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  have _ := hR
  have hpd :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) =
        (↑(Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) :
          WithBot ℕ∞) :=
    auslander_buchsbaum_serre_pd_residueField_eq_finrank_cotangentSpace_of_ne_top
      (R := R) htop
  simp [hpd]

/-- Non-field case: bound the cotangent-space finrank by the residue field projective dimension. -/
lemma projectiveDimension_residueField_ge_finrank_cotangentSpace_of_not_isField {R : Type}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (hR : ¬ IsField R) :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  classical
  by_cases htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) = ⊤
  ·
    simp [htop]
  ·
    exact
      projectiveDimension_residueField_ge_finrank_cotangentSpace_of_not_isField_of_ne_top
        (R := R) hR htop

/-- Reduce the cotangent-space bound to the finite projective dimension case. -/
lemma projectiveDimension_residueField_ge_finrank_cotangentSpace {R : Type} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] :
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
  classical
  by_cases htop :
      CategoryTheory.projectiveDimension (ModuleCat.of R (IsLocalRing.ResidueField R)) = ⊤
  ·
    simp [htop]
  ·
    by_cases hR : IsField R
    ·
      have hfin :
          Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = 0 :=
        (IsLocalRing.finrank_cotangentSpace_eq_zero_iff (R := R)).2 hR
      have hpd0 :
          (0 : ℕ) ≤ CategoryTheory.projectiveDimension
            (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
        refine
          (CategoryTheory.projectiveDimension_ge_iff
              (X := ModuleCat.of R (IsLocalRing.ResidueField R)) (n := 0)).2 ?_
        intro hpdlt
        have hzero :
            CategoryTheory.Limits.IsZero (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
          (CategoryTheory.hasProjectiveDimensionLT_zero_iff_isZero
            (X := ModuleCat.of R (IsLocalRing.ResidueField R))).1 hpdlt
        have hsub :
            Subsingleton (IsLocalRing.ResidueField R) :=
          (ModuleCat.isZero_iff_subsingleton
            (M := ModuleCat.of R (IsLocalRing.ResidueField R))).1 hzero
        have h01 : (0 : IsLocalRing.ResidueField R) = 1 := Subsingleton.elim _ _
        exact zero_ne_one h01
      simpa [hfin] using hpd0
    ·
      exact
        projectiveDimension_residueField_ge_finrank_cotangentSpace_of_not_isField (R := R) hR

/--
Suppose that \( R \) is a Noetherian local ring with maximal ideal \( \mathfrak{m} \) and residue field \( \kappa \).
In this case the projective dimension of \( \kappa \) is \( \geq \dim_{\kappa} \mathfrak{m} / \mathfrak{m}^{2} \). -/
theorem not_hasProjectiveDimensionLT_finrank_cotangentSpace {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
      ¬ CategoryTheory.HasProjectiveDimensionLT
        (ModuleCat.of R (IsLocalRing.ResidueField R))
          (Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R)) := by
  classical
  by_cases hR : IsField R
  ·
    simpa using
      not_hasProjectiveDimensionLT_finrank_cotangentSpace_of_isField (R := R) hR
  ·
    have hpd1 :
        (1 : ℕ) ≤
          CategoryTheory.projectiveDimension
            (ModuleCat.of R (IsLocalRing.ResidueField R)) :=
      one_le_projectiveDimension_residueField_of_not_isField (R := R) hR
    have hpd :
        Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) ≤
          CategoryTheory.projectiveDimension
            (ModuleCat.of R (IsLocalRing.ResidueField R)) := by
      exact projectiveDimension_residueField_ge_finrank_cotangentSpace (R := R)
    exact
      (CategoryTheory.projectiveDimension_ge_iff
          (X := ModuleCat.of R (IsLocalRing.ResidueField R))
          (n := Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R))).1 hpd

import Mathlib

open MvPolynomial

-- If `P` lies over `p` and the algebra has going-down, prime height is monotone.
lemma primeHeight_le_of_liesOver_of_hasGoingDown {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S] {p : Ideal R} [p.IsPrime]
    {P : Ideal S} [P.IsPrime] [P.LiesOver p] :
    p.primeHeight ≤ P.primeHeight := by
  classical
  refine Order.height_le ?_
  intro l hl
  haveI : P.LiesOver l.last.asIdeal := by
    simpa [hl] using (inferInstance : P.LiesOver p)
  obtain ⟨L, hlen, hlast, _⟩ :=
    Ideal.exists_ltSeries_of_hasGoingDown (R := R) (S := S) l P
  have hle : (l.length : ℕ∞) ≤ Order.height L.last := by
    simpa [hlen] using (Order.length_le_height_last (p := L))
  simpa [Ideal.primeHeight, hlast] using hle
/--Let \( K \) be a field and \( L \) an extension field of \( K \). If \( P \) is a prime ideal of
\( L[X_1, \dots, X_n] \) and \( \mathfrak{p} = P \cap K[X_1, \dots, X_n] \), then \(
\operatorname{ht}(P) \geq \operatorname{ht}(\mathfrak{p}) \).-/
theorem primeHeight_le_of_comap_eq {K L : Type} (n : ℕ) [Field K] [Field L] [Algebra K L]
    (P : Ideal (MvPolynomial (Fin n) L)) (p : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime]
    [p.IsPrime] (h : P.comap (MvPolynomial.map (algebraMap K L)) = p) :
    p.primeHeight ≤ P.primeHeight := by
  classical
  letI : Algebra (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
    MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := K) (S := L)
  have h' : p = P.under (MvPolynomial (Fin n) K) := by
    simpa [Ideal.under_def, MvPolynomial.algebraMap_def] using h.symm
  haveI : P.LiesOver p := ⟨h'⟩
  -- TODO: supply a going-down instance for the coefficient extension.
  -- A plausible route is to prove `Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L)`
  -- using base change/tensor-product equivalences, then use `Algebra.HasGoingDown.of_flat`.
  haveI : Algebra.HasGoingDown (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) := by
    have hbase :
        IsBaseChange (MvPolynomial (Fin n) K)
          (IsScalarTower.toAlgHom K L (MvPolynomial (Fin n) L)).toLinearMap := by
      simpa using (Algebra.IsPushout.out :
        IsBaseChange (MvPolynomial (Fin n) K)
          (IsScalarTower.toAlgHom K L (MvPolynomial (Fin n) L)).toLinearMap)
    haveI : Module.Flat K L := inferInstance
    haveI : Module.Flat (MvPolynomial (Fin n) K) (MvPolynomial (Fin n) L) :=
      Module.Flat.isBaseChange (R := K) (S := MvPolynomial (Fin n) K) (M := L)
        (N := MvPolynomial (Fin n) L)
        (f := (IsScalarTower.toAlgHom K L (MvPolynomial (Fin n) L)).toLinearMap)
        hbase
    infer_instance
  exact primeHeight_le_of_liesOver_of_hasGoingDown (p := p) (P := P)

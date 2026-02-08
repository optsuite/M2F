import Mathlib

/-- Suppose that a ring $S$ is integral over the image of a ring homomorphism $R \to S$. Show that
the Krull dimension of $M$ as an $S$-module is the same as the Krull dimension of $M$ as an
$R$-module. -/
-- `PrimeSpectrum.comap` is strictly monotone for integral extensions.
lemma PrimeSpectrum.strictMono_comap_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro P Q hPQ
  have hPQ' : (P.asIdeal : Ideal S) < Q.asIdeal := by
    simpa using hPQ
  rcases SetLike.lt_iff_le_and_exists.mp hPQ' with ⟨hPQle, x, hxQ, hxP⟩
  have hx : x ∈ ((Q.asIdeal : Ideal S) : Set S) \ P.asIdeal := ⟨hxQ, hxP⟩
  have hcomap_lt :
      P.asIdeal.comap (algebraMap R S) < Q.asIdeal.comap (algebraMap R S) :=
    Ideal.comap_lt_comap_of_integral_mem_sdiff (I := P.asIdeal) (J := Q.asIdeal)
      hPQle hx (Algebra.IsIntegral.isIntegral x)
  simpa using hcomap_lt

/-- Going-up step on prime spectra for an integral extension. -/
lemma PrimeSpectrum.exists_ge_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] {p q : PrimeSpectrum R} (hpq : p ≤ q)
    {P : PrimeSpectrum S} (hP : PrimeSpectrum.comap (algebraMap R S) P = p) :
    ∃ Q : PrimeSpectrum S, P ≤ Q ∧ PrimeSpectrum.comap (algebraMap R S) Q = q := by
  have hpq' : p.asIdeal ≤ q.asIdeal := by
    simpa using hpq
  have hP' : P.asIdeal.comap (algebraMap R S) = p.asIdeal := by
    simpa [PrimeSpectrum.comap_asIdeal] using congrArg PrimeSpectrum.asIdeal hP
  have hIP : P.asIdeal.comap (algebraMap R S) ≤ q.asIdeal := by
    simpa [hP'] using hpq'
  obtain ⟨Q, hQge, hQprime, hQcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := S) (P := q.asIdeal)
      (I := P.asIdeal) hIP
  refine ⟨⟨Q, hQprime⟩, ?_, ?_⟩
  · simpa using hQge
  · apply PrimeSpectrum.ext
    simpa [PrimeSpectrum.comap_asIdeal] using hQcomap

/-- Lift a strict chain of primes along an integral extension. -/
lemma PrimeSpectrum.exists_ltSeries_of_isIntegral {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hinj : Function.Injective (algebraMap R S)) (l : LTSeries (PrimeSpectrum R)) :
    ∃ L : LTSeries (PrimeSpectrum S),
      L.length = l.length ∧
      PrimeSpectrum.comap (algebraMap R S) L.last = l.last := by
  classical
  refine RelSeries.inductionOn' (motive := fun l =>
      ∃ L : LTSeries (PrimeSpectrum S),
        L.length = l.length ∧
        PrimeSpectrum.comap (algebraMap R S) L.last = l.last) ?_ ?_ l
  · intro p
    have hIP : Ideal.comap (algebraMap R S) ⊥ ≤ p.asIdeal :=
      Ideal.comap_bot_le_of_injective (f := algebraMap R S) (I := p.asIdeal) hinj
    obtain ⟨Q, _, hQprime, hQcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral (R := R) (S := S) (P := p.asIdeal)
        (I := ⊥) hIP
    refine ⟨RelSeries.singleton _ ⟨Q, hQprime⟩, ?_, ?_⟩
    · simp
    · have : PrimeSpectrum.comap (algebraMap R S) ⟨Q, hQprime⟩ = p := by
        apply PrimeSpectrum.ext
        simpa [PrimeSpectrum.comap_asIdeal] using hQcomap
      simpa using this
  · intro l x hx ih
    rcases ih with ⟨L, hlen, hlast⟩
    obtain ⟨Q, hLQle, hQcomap⟩ :=
      PrimeSpectrum.exists_ge_of_isIntegral (R := R) (S := S)
        (p := l.last) (q := x) (P := L.last) hx.le hlast
    have hLQlt : L.last < Q := by
      refine lt_of_le_of_ne hLQle ?_
      intro hEQ
      have : l.last = x := by
        calc
          l.last = PrimeSpectrum.comap (algebraMap R S) L.last := hlast.symm
          _ = PrimeSpectrum.comap (algebraMap R S) Q := by simp [hEQ]
          _ = x := hQcomap
      exact (ne_of_lt hx) this
    refine ⟨L.snoc Q hLQlt, ?_, ?_⟩
    · simp [hlen]
    · simpa using hQcomap

theorem ringKrullDim_quot_annihilator_eq {R S M : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [Algebra R S] [Module S M] [Module R M] [IsScalarTower R S M]
    [Algebra.IsIntegral R S] :
    ringKrullDim (S ⧸ (Module.annihilator S M)) = ringKrullDim (R ⧸ (Module.annihilator R M)) := by
  classical
  let I : Ideal S := Module.annihilator S M
  let J : Ideal R := I.comap (algebraMap R S)
  have hcomap : J = Module.annihilator R M := by
    simpa [I, J] using (Module.comap_annihilator (R := S) (R₀ := R) (M := M))
  have hle :
      ringKrullDim (S ⧸ I) ≤ ringKrullDim (R ⧸ J) := by
    simpa [ringKrullDim] using
      (Order.krullDim_le_of_strictMono
        (PrimeSpectrum.comap (algebraMap (R ⧸ J) (S ⧸ I)))
        (PrimeSpectrum.strictMono_comap_of_isIntegral
          (R := R ⧸ J) (S := S ⧸ I)))
  have hge :
      ringKrullDim (R ⧸ J) ≤ ringKrullDim (S ⧸ I) := by
    simp [ringKrullDim, Order.krullDim]
    intro l
    have hinj : Function.Injective (algebraMap (R ⧸ J) (S ⧸ I)) := by
      simpa [J] using (Ideal.algebraMap_quotient_injective (R := R) (A := S) (I := I))
    obtain ⟨L, hlen, -⟩ :=
      PrimeSpectrum.exists_ltSeries_of_isIntegral (R := R ⧸ J) (S := S ⧸ I) hinj l
    have hL : (L.length : ℕ∞) ≤ ringKrullDim (S ⧸ I) := by
      simpa [ringKrullDim] using (Order.LTSeries.length_le_krullDim (p := L))
    simpa [hlen] using hL
  have hEq : ringKrullDim (S ⧸ I) = ringKrullDim (R ⧸ J) := le_antisymm hle hge
  rw [hcomap] at hEq
  simpa [I] using hEq

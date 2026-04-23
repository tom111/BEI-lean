import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Quotient dimension lemmas

## Main results

- `ringKrullDim_quotient_anti`: `I ≤ J → dim(R/J) ≤ dim(R/I)`
- `ringKrullDim_quotient_radical`: `dim(R/I) = sup dim(R/P)` over minimal primes P of
  radical ideal I.
-/

variable {R : Type*} [CommRing R]

/-! ## Monotonicity of quotient dimension -/

/-- Quotient dimension is antitone: if `I ≤ J` then `dim(R/J) ≤ dim(R/I)`.
This gives: for any prime P containing I, `dim(R/I) ≥ dim(R/P)`. -/
theorem ringKrullDim_quotient_anti {I J : Ideal R} (h : I ≤ J) :
    ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ I) :=
  ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective h)

/-! ## Dimension of quotient by radical ideal -/

/-- The Krull dimension of a `zeroLocus I` subposet equals the supremum over
minimal primes P of I of the Krull dimension of the `zeroLocus P` subposet.

The key argument: any `LTSeries` in `zeroLocus I` has its minimum element above
some minimal prime P (by `Ideal.exists_minimalPrimes_le`), so the entire series
lies in `zeroLocus P`. -/
private lemma krullDim_zeroLocus_eq_iSup_minimalPrimes (I : Ideal R) :
    Order.krullDim (PrimeSpectrum.zeroLocus (I : Set R)) =
    ⨆ (P : Ideal R) (_ : P ∈ I.minimalPrimes),
      Order.krullDim (PrimeSpectrum.zeroLocus (P : Set R)) := by
  apply le_antisymm
  · -- Upper bound: every LTSeries in zeroLocus(I) lies in some zeroLocus(P)
    simp only [Order.krullDim, iSup_le_iff]
    intro l
    -- l(0) is a prime ideal containing I
    have h0_mem := (l 0).prop  -- (I : Set R) ⊆ (l 0).val.asIdeal
    -- Some minimal prime P sits below l(0)
    obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le (I := I)
      (J := (l 0).val.asIdeal) h0_mem
    -- Build the same series in zeroLocus(P)
    have hl_in_P : ∀ k, (l k).val ∈ PrimeSpectrum.zeroLocus (P : Set R) := by
      intro k
      change (P : Set R) ⊆ (l k).val.asIdeal
      rcases eq_or_lt_of_le (Fin.zero_le k) with h0k | h0k
      · rw [← h0k]; exact hPle
      · exact hPle.trans (show (l 0).val.asIdeal ≤ (l k).val.asIdeal from
          le_of_lt (l.rel_of_lt h0k))
    let l' : LTSeries (PrimeSpectrum.zeroLocus (P : Set R)) :=
      { length := l.length
        toFun := fun k => ⟨(l k).val, hl_in_P k⟩
        step := fun k => l.step k }
    apply le_iSup₂_of_le P hPmin
    exact le_iSup (fun (s : LTSeries _) => (s.length : WithBot ℕ∞)) l'
  · -- Lower bound: zeroLocus(P) ⊆ zeroLocus(I) for each minimal prime
    apply iSup₂_le
    intro P hP
    apply Order.krullDim_le_of_strictMono
      (fun ⟨q, hq⟩ => ⟨q, show (I : Set R) ⊆ q.asIdeal from hP.1.2.trans hq⟩)
      (fun _ _ h => h)

/-- For a radical ideal `I`, `dim(R/I) = sup dim(R/P)` over minimal primes P of I.

**Lower bound**: each P ∈ minimalPrimes(I) satisfies I ≤ P, so
`dim(R/I) ≥ dim(R/P)` by `ringKrullDim_quotient_anti`.

**Upper bound**: any `LTSeries` in `zeroLocus(I)` starts above some minimal
prime P (by `Ideal.exists_minimalPrimes_le`), so the entire chain lies in
`zeroLocus(P)`, giving `krullDim(zeroLocus I) ≤ sup_P krullDim(zeroLocus P)`.
-/
theorem ringKrullDim_quotient_radical (I : Ideal R) (_hrad : I.IsRadical) :
    ringKrullDim (R ⧸ I) =
    ⨆ (P : Ideal R) (_ : P ∈ I.minimalPrimes), ringKrullDim (R ⧸ P) := by
  simp only [ringKrullDim_quotient]
  exact krullDim_zeroLocus_eq_iSup_minimalPrimes I

/-! ## Dimension of quotient by equidimensional radical ideal -/

/-- If `I` is a radical ideal whose minimal primes all have the same Krull
codimension `d`, then `dim(R/I) = d`. Uses `ringKrullDim_quotient_radical`
(the sup formula) together with equidimensionality to compute the sup as a
constant. -/
theorem ringKrullDim_quotient_radical_equidim [IsNoetherianRing R]
    {I : Ideal R} (hne : I ≠ ⊤) (hrad : I.IsRadical)
    {d : WithBot ℕ∞}
    (hequidim : ∀ P ∈ I.minimalPrimes, ringKrullDim (R ⧸ P) = d) :
    ringKrullDim (R ⧸ I) = d := by
  -- minimalPrimes is nonempty since I ≠ ⊤
  have hne_mp : I.minimalPrimes.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact (Ideal.minimalPrimes_eq_empty_iff I).not.mpr hne
  obtain ⟨P₀, hP₀⟩ := hne_mp
  rw [ringKrullDim_quotient_radical I hrad]
  apply le_antisymm
  · exact iSup₂_le fun P hP => (hequidim P hP).le
  · exact le_iSup₂_of_le P₀ hP₀ (hequidim P₀ hP₀).ge

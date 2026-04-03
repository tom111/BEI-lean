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

/-- For a radical ideal `I`, `dim(R/I) = sup dim(R/P)` over minimal primes P of I.

**Lower bound** (proved): each P ∈ minimalPrimes(I) satisfies I ≤ P, so
`dim(R/I) ≥ dim(R/P)` by `ringKrullDim_quotient_anti`.

**Upper bound** (sorry): any `LTSeries` in `zeroLocus(I)` starts above some minimal
prime P (by `Ideal.exists_minimalPrimes_le`), so the entire chain lies in
`zeroLocus(P)`, giving `krullDim(zeroLocus I) ≤ sup_P krullDim(zeroLocus P)`.
-/
theorem ringKrullDim_quotient_radical (I : Ideal R) (hrad : I.IsRadical) :
    ringKrullDim (R ⧸ I) =
    ⨆ (P : Ideal R) (_ : P ∈ I.minimalPrimes), ringKrullDim (R ⧸ P) := by
  apply le_antisymm
  · -- Upper bound: dim(R/I) ≤ sup dim(R/P) over minimal primes
    -- Proof sketch: use ringKrullDim_quotient to convert to zeroLocus,
    -- then show every LTSeries in zeroLocus(I) lies in some zeroLocus(P).
    sorry
  · -- Lower bound: sup dim(R/P) ≤ dim(R/I)
    apply iSup₂_le
    intro P hP
    exact ringKrullDim_quotient_anti hP.1.2

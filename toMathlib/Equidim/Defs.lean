/-
This file contains definitions adapted from mathlib PR #26218 (by Nailin Guan, Yongle Hu),
backported to the v4.28.0 environment used by BEI-lean.

The long-term goal is to delete this local copy once the relevant CM infrastructure
is available upstream in Mathlib.

For the BEI project, we only need the consequence that CM quotient rings are
equidimensional: all minimal primes of J_G have the same quotient dimension.
We axiomatize this consequence directly.
-/

import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# Equidimensional rings (working definition for BEI)

The full Cohen-Macaulay definition (depth = dim for local rings) is not yet available in
Mathlib v4.28.0. We define the local BEI surrogate via the equidimensionality
consequence: all minimal primes have the same quotient dimension.

## Main definitions

- `IsEquidimRing`: a ring `R` is equidimensional if all minimal primes of `R` have the
  same `ringKrullDim` in the quotient. Equivalently, `R` is equidimensional
  in the sense that `ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ Q)` for all
  minimal primes P, Q of the zero ideal.
-/

variable (R : Type*) [CommRing R]

/-- A commutative ring is **equidimensional** if all minimal
primes have the same quotient dimension `ringKrullDim (R ⧸ P)`.

Note: This is the local surrogate currently used in the BEI project. It is a
consequence of the full Cohen-Macaulay definition (depth = dim for local rings),
not the definition itself.

Adapted from mathlib PR #26218. -/
class IsEquidimRing : Prop where
  /-- All minimal primes have the same quotient dimension. -/
  equidimensional : ∀ P Q : Ideal R, P ∈ minimalPrimes R →
    Q ∈ minimalPrimes R → ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ Q)

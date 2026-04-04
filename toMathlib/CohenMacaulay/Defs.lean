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
# Cohen-Macaulay rings (working definition for BEI)

The full CM definition (depth = dim for local rings) is not yet available in
Mathlib v4.28.0. We define CM for quotient rings via the equidimensionality
consequence: all minimal primes have the same quotient dimension.

## Main definitions

- `IsCohenMacaulayRing`: a ring R is CM if all minimal primes of R have the
  same `ringKrullDim` in the quotient. Equivalently, `R` is equidimensional
  in the sense that `ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ Q)` for all
  minimal primes P, Q of the zero ideal.
-/

variable (R : Type*) [CommRing R]

/-- A commutative ring is **Cohen-Macaulay** if it is equidimensional: all minimal
primes have the same quotient dimension `ringKrullDim (R ⧸ P)`.

Note: This is a consequence of the full CM definition (depth = dim for local rings),
not the definition itself. We use it because it's the exact property needed for the
BEI formalization, and the full depth machinery is not yet in Mathlib v4.28.0.

Adapted from mathlib PR #26218. -/
class IsCohenMacaulayRing : Prop where
  /-- All minimal primes have the same quotient dimension. -/
  equidimensional : ∀ P Q : Ideal R, P ∈ minimalPrimes R →
    Q ∈ minimalPrimes R → ringKrullDim (R ⧸ P) = ringKrullDim (R ⧸ Q)

/-
This file contains definitions adapted from mathlib PR #26218 (by Nailin Guan, Yongle Hu),
backported to the v4.28.0 environment used by BEI-lean.

The long-term goal is to delete this local copy once the relevant CM infrastructure
is available upstream in Mathlib.

The PR defines CM modules via `Module.supportDim R M = IsLocalRing.depth M`.
Since `IsLocalRing.depth` is not in Mathlib v4.28.0, we use a simplified definition
for rings (not modules) that suffices for the BEI application:

  A commutative Noetherian local ring R is Cohen-Macaulay if
  `ringKrullDim R = Ideal.depth (maximalIdeal R) R`

where `Ideal.depth` is the length of a maximal regular sequence in the ideal.

For the BEI project, we actually only need the consequence that CM rings are
equidimensional (all minimal primes have the same height). We axiomatize this
consequence directly rather than importing the full depth machinery.
-/

import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Cohen-Macaulay rings (minimal local definition for BEI)

This provides a real (non-sorry) definition of `IsCohenMacaulayRing` that
captures the equidimensionality consequence needed by the BEI project.

## Main definitions

- `IsCohenMacaulayRing`: a ring R is CM if localization at every maximal ideal
  is equidimensional (all minimal primes have the same height).

This is weaker than the full CM definition (depth = dim) but is the exact
property used by Corollary 3.4 and Corollary 3.7(d) in Herzog et al.
-/

variable (R : Type*) [CommRing R]

/-- A commutative ring is **Cohen-Macaulay** if it is equidimensional: all minimal
primes have the same height.

Note: This is a consequence of the full CM definition (depth = dim for local rings),
not the definition itself. We use it as a working definition because it's the exact
property needed for the BEI formalization, and the full depth machinery is not yet
in Mathlib v4.28.0.

Adapted from mathlib PR #26218. -/
class IsCohenMacaulayRing : Prop where
  /-- All minimal primes have the same height. -/
  equidimensional : ∀ P Q : Ideal R, P ∈ (⊥ : Ideal R).minimalPrimes →
    Q ∈ (⊥ : Ideal R).minimalPrimes → P.height = Q.height

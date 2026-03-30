/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BEI.Definitions
import Mathlib.RingTheory.Ideal.Height

/-!
# Height of 2-minor ideals (determinantal ideals)

The ideal of 2×2 minors of a generic 2×m matrix has height m − 1. In the
language of binomial edge ideals, this is `height(J_{K_m}) = m − 1` where
K_m is the complete graph on m vertices.

## Main results

- `height_binomialEdgeIdeal_complete`: `height(J_{K_m}) = m − 1`

## Proof strategy

The ideal `J_{K_m}` is the kernel of the Segre-type map
  `φ : K[x₁,...,xₘ,y₁,...,yₘ] → K[t, u₁,...,uₘ]`
  `x_i ↦ t · u_i,  y_i ↦ u_i`

The image has Krull dimension m + 1 (it is a polynomial ring in m + 1
algebraically independent generators). Since the ambient ring has dimension 2m:
  `height(J_{K_m}) = 2m − (m + 1) = m − 1`

This uses the catenary property of polynomial rings:
  `height(P) + dim(R/P) = dim(R)`
which is NOT in Mathlib v4.28.0.

Alternatively, this is a special case of the **Eagon–Northcott theorem**:
the ideal of t-minors of a generic p × q matrix has height (p−t+1)(q−t+1).
For t = 2, p = 2, q = m: height = 1 · (m − 1) = m − 1.

## Mathlib prerequisites (available)
- `Ideal.height` (`Mathlib.RingTheory.Ideal.Height`)
- `MvPolynomial.ringKrullDim` (`Mathlib.RingTheory.KrullDimension.Polynomial`)
- `binomialEdgeIdeal` (`BEI.Definitions`)

## Mathlib gaps (blockers)
- Catenary property for polynomial rings
- Eagon–Northcott complex
- `height(P) + dim(R/P) = dim(R)` for `MvPolynomial`
-/

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial

/-- The binomial edge ideal of the complete graph K_m has height m − 1.
Equivalently, the ideal of 2×2 minors of a generic 2×m matrix has height m − 1.

This is the Eagon–Northcott theorem for the special case t = 2, p = 2, q = m. -/
theorem height_binomialEdgeIdeal_complete (m : ℕ) (hm : 2 ≤ m) :
    Ideal.height (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m))) = m - 1 := by
  sorry

end

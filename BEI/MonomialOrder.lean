import BEI.Groebner
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Data.Fintype.Card

variable {V : Type*} [LinearOrder V] [Finite V]

/-!
# Monomial order for binomial edge ideals

This file connects the `LinearOrder` on `BinomialEdgeVars V` to Mathlib's
`MonomialOrder` infrastructure, and identifies the leading term of the generator
`f_{ij} = x_i y_j - x_j y_i`.

## Key results
- `binomialEdgeMonomialOrder`: the lex monomial order on `BinomialEdgeVars V →₀ ℕ`
- The leading monomial of `f_{ij}` (with `i < j`) is `x_i · y_j`

## Reference: Herzog et al. (2010), Section 1
-/

noncomputable section

open MvPolynomial MonomialOrder

/-!
## The monomial order

We use Mathlib's `MonomialOrder.lex`, which requires `WellFoundedGT` on the variable
type. We establish well-foundedness of the strict order on `BinomialEdgeVars V` by
noting the order is (anti-isomorphic to) a well-order: all y-variables are below all
x-variables, and within each block the order on V is well-founded.
-/

/--
The lex monomial order on `BinomialEdgeVars V →₀ ℕ`, inducing the variable order
`x_n > ... > x_1 > y_n > ... > y_1` (i.e., all x above all y, indices descending).

We construct this directly as a `MonomialOrder` structure (rather than via `MonomialOrder.lex`)
to avoid a LT-instance diamond that prevents Lean from synthesizing `WellFoundedGT` in the
context of `MonomialOrder.lex`. The `wf` field provides `WellFoundedGT` inline where the
LT context is already fixed by the surrounding structure fields.
-/
noncomputable def binomialEdgeMonomialOrder : MonomialOrder (BinomialEdgeVars V) where
  syn := Lex (BinomialEdgeVars V →₀ ℕ)
  toSyn := { toEquiv := toLex
             map_add' := toLex_add }
  toSyn_monotone := Finsupp.toLex_monotone
  wf := by
    haveI : Finite (BinomialEdgeVars V) := Sum.instFinite
    exact Finsupp.Lex.wellFoundedLT_of_finite

/-! ## Leading terms of the generators -/

variable {K : Type*} [Field K]

/-- The generator `f_{ij} = x_i * y_j - x_j * y_i` for `i < j`. -/
noncomputable def fij (i j : V) : MvPolynomial (BinomialEdgeVars V) K :=
  x i * y j - x j * y i

/--
Under `binomialEdgeMonomialOrder`, the leading monomial of `f_{ij}` (with `i < j`)
is `x_i · y_j`. This follows from `i < j` implies `Sum.inl i > Sum.inl j` in
our variable order, and x-variables dominate y-variables.
-/
theorem fij_degree (i j : V) (hij : i < j) :
    binomialEdgeMonomialOrder.degree (fij (K := K) i j) =
      Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1 := by
  sorry

/-- The leading coefficient of `f_{ij}` is 1. -/
theorem fij_leadingCoeff (i j : V) (hij : i < j) :
    binomialEdgeMonomialOrder.leadingCoeff (fij (K := K) i j) = 1 := by
  sorry

/-- The leading coefficient of each generator is a unit. -/
theorem fij_leadingCoeff_isUnit (i j : V) (hij : i < j) :
    IsUnit (binomialEdgeMonomialOrder.leadingCoeff (fij (K := K) i j)) := by
  sorry

end

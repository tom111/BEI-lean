import BEI.Groebner
import Mathlib.Data.Finite.Sum
import Mathlib.Data.Finsupp.Lex
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

/-! ## Well-foundedness -/

/-- The reversed lex order on `BinomialEdgeVars V` is well-founded
(descending chains must terminate, since the type is finite). -/
noncomputable instance : WellFoundedGT (BinomialEdgeVars V) := Finite.to_wellFoundedGT

/-!
## The monomial order

We use Mathlib's `MonomialOrder.lex`, which requires `WellFoundedGT` on the variable type.
With the opaque `BinomialEdgeVars` type, there is no instance diamond: the `LT` instance
from our `LinearOrder` is the unique `LT` on `BinomialEdgeVars V`, and both `Finsupp.instLTLex`
and the LT derived from `Finsupp.Lex.linearOrder` resolve to the same instance.
-/

/--
The lex monomial order on `BinomialEdgeVars V →₀ ℕ`, inducing the variable order
`x_n > ... > x_1 > y_n > ... > y_1` (i.e., all x above all y, indices descending).
-/
noncomputable def binomialEdgeMonomialOrder : MonomialOrder (BinomialEdgeVars V) :=
  MonomialOrder.lex

/-! ## Leading terms of the generators -/

variable {K : Type*} [Field K]

/-- The generator `f_{ij} = x_i * y_j - x_j * y_i` for `i < j`. -/
noncomputable def fij (i j : V) : MvPolynomial (BinomialEdgeVars V) K :=
  x i * y j - x j * y i

/-!
### Helper: the lex comparison for leading monomials

The key inequality: under the lex order on `BinomialEdgeVars V →₀ ℕ` (where
`x_i > x_j` when `i < j` and all x > all y), the monomial `x_i y_j` is
lexicographically greater than `x_j y_i` whenever `i < j`.

We state this directly in terms of `binomialEdgeMonomialOrder.toSyn` so that
the LT instance matches what `MonomialOrder.degree_sub_of_lt` expects.
-/
private lemma fij_lex_lt (i j : V) (hij : i < j) :
    binomialEdgeMonomialOrder.toSyn
      (Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
       Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ) <
    binomialEdgeMonomialOrder.toSyn
      (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
       Finsupp.single (Sum.inr j) 1 : BinomialEdgeVars V →₀ ℕ) := by
  rw [Finsupp.Lex.lt_iff]
  refine ⟨Sum.inr j, fun l hl => ?_, ?_⟩
  · -- For all l < Sum.inr j, both monomials agree.
    simp only [binomialEdgeMonomialOrder, MonomialOrder.lex, AddEquiv.coe_mk,
      ofLex_toLex, Finsupp.add_apply, Finsupp.single_apply]
    cases l with
    | inl v =>
      -- Sum.inl v < Sum.inr j means binomialEdgeLE (inl v) (inr j) = False
      exact absurd hl.1 (by simp [binomialEdgeLE])
    | inr v =>
      -- Sum.inr v < Sum.inr j means j < v (our reversed order)
      have hvj : j < v := by
        obtain ⟨h1, h2⟩ := hl; simp only [binomialEdgeLE] at h1 h2
        exact lt_of_le_not_ge h1 h2
      -- Neither Sum.inr i nor Sum.inr j equals Sum.inr v at this position
      have h1 : ¬(@Sum.inr V V i = @Sum.inr V V v) :=
        fun h => absurd (Sum.inr.inj h) (ne_of_lt (lt_trans hij hvj))
      have h2 : ¬(@Sum.inr V V j = @Sum.inr V V v) :=
        fun h => absurd (Sum.inr.inj h) (ne_of_lt hvj)
      simp [h1, h2]
  · -- At position Sum.inr j: LHS = 0 < 1 = RHS.
    simp only [binomialEdgeMonomialOrder, MonomialOrder.lex, AddEquiv.coe_mk,
      ofLex_toLex, Finsupp.add_apply, Finsupp.single_apply]
    have h1 : ¬(@Sum.inr V V i = @Sum.inr V V j) :=
      fun h => absurd (Sum.inr.inj h) (ne_of_lt hij)
    simp [h1]

/--
Under `binomialEdgeMonomialOrder`, the leading monomial of `f_{ij}` (with `i < j`)
is `x_i · y_j`. The key: in the lex order `x_i > x_j` (since `i < j` reverses),
so `x_i y_j > x_j y_i`, and `degree_sub_of_lt` applies.
-/
theorem fij_degree (i j : V) (hij : i < j) :
    binomialEdgeMonomialOrder.degree (fij (K := K) i j) =
      Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1 := by
  unfold fij x y
  have hxi : (X (Sum.inl i) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hyj : (X (Sum.inr j) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hxj : (X (Sum.inl j) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hyi : (X (Sum.inr i) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hdeg1 : binomialEdgeMonomialOrder.degree
      (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial (BinomialEdgeVars V) K) =
      Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1 := by
    rw [degree_mul hxi hyj, degree_X, degree_X]
  have hdeg2 : binomialEdgeMonomialOrder.degree
      (X (Sum.inl j) * X (Sum.inr i) : MvPolynomial (BinomialEdgeVars V) K) =
      Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr i) 1 := by
    rw [degree_mul hxj hyi, degree_X, degree_X]
  have hlt : binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree
        (X (Sum.inl j) * X (Sum.inr i) : MvPolynomial (BinomialEdgeVars V) K)) <
    binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree
        (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial (BinomialEdgeVars V) K)) := by
    rw [hdeg1, hdeg2]; exact fij_lex_lt i j hij
  rw [degree_sub_of_lt hlt, hdeg1]

/-- The leading coefficient of `f_{ij}` is 1. -/
theorem fij_leadingCoeff (i j : V) (hij : i < j) :
    binomialEdgeMonomialOrder.leadingCoeff (fij (K := K) i j) = 1 := by
  unfold fij x y
  have hxi : (X (Sum.inl i) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hyj : (X (Sum.inr j) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hxj : (X (Sum.inl j) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hyi : (X (Sum.inr i) : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := X_ne_zero _
  have hdeg1 : binomialEdgeMonomialOrder.degree
      (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial (BinomialEdgeVars V) K) =
      Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1 := by
    rw [degree_mul hxi hyj, degree_X, degree_X]
  have hdeg2 : binomialEdgeMonomialOrder.degree
      (X (Sum.inl j) * X (Sum.inr i) : MvPolynomial (BinomialEdgeVars V) K) =
      Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr i) 1 := by
    rw [degree_mul hxj hyi, degree_X, degree_X]
  have hlt : binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree
        (X (Sum.inl j) * X (Sum.inr i) : MvPolynomial (BinomialEdgeVars V) K)) <
    binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree
        (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial (BinomialEdgeVars V) K)) := by
    rw [hdeg1, hdeg2]; exact fij_lex_lt i j hij
  rw [leadingCoeff_sub_of_lt hlt, leadingCoeff_mul, leadingCoeff_X, leadingCoeff_X, mul_one]

/-- The leading coefficient of each generator is a unit. -/
theorem fij_leadingCoeff_isUnit (i j : V) (hij : i < j) :
    IsUnit (binomialEdgeMonomialOrder.leadingCoeff (fij (K := K) i j)) := by
  rw [fij_leadingCoeff i j hij]
  exact isUnit_one

end

---
title: Code map
---

# Code Map

A one-line gloss for every Lean file in `BEI/` and `toMathlib/`, grouped by
purpose. For the paper-to-Lean theorem table, see
[`FORMALIZATION_MAP.md`](https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md);
for an editorial overview, see
[`OVERVIEW.md`](https://github.com/tom111/BEI-lean/blob/master/OVERVIEW.md).

## `BEI/` — Main development

### Foundations and term order

| File | Contents |
|---|---|
| [`Definitions.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/Definitions.lean) | `BinomialEdgeVars V := V ⊕ V`, the polynomial ring, `binomialEdgeIdeal G`, `IsClosedGraph G`. |
| [`Groebner.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/Groebner.lean) | Custom `LinearOrder (BinomialEdgeVars V)` with `x_1 > … > x_n > y_1 > … > y_n`. |
| [`MonomialOrder.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/MonomialOrder.lean) | The lex `MonomialOrder` instance; leading-term lemmas for `f_{ij}`. |
| [`GroebnerAPI.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerAPI.lean) | `IsRemainder`, `IsGroebnerBasis`, Buchberger's criterion. |
| [`AdmissiblePaths.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/AdmissiblePaths.lean) | `pathMonomial`, admissible paths, `groebnerBasisSet`. |

### Section 1 — closed graphs and Theorem 1.1

| File | Contents |
|---|---|
| [`GraphProperties.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | `IsChordal`, `IsClawFree`, `graphClosure`; Propositions 1.2 / 1.4 / 1.5 and Corollary 1.3. |
| [`ClosedGraphs.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/ClosedGraphs.lean) | **Theorem 1.1** — closed graph ↔ quadratic Gröbner basis. |

### Section 2 — Theorem 2.1 and radicality

| File | Contents |
|---|---|
| [`HerzogLemmas.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/HerzogLemmas.lean) | `f_{ij}` algebraic identities and `IsRemainder` helpers used in Theorem 2.1. |
| [`CoveredWalks.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/CoveredWalks.lean) | Walk and path arithmetic, S-polynomial helpers, covered-walk lemmas. |
| [`GroebnerBasisSPolynomial.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasisSPolynomial.lean) | **Theorem 2.1** — Buchberger / S-polynomial proof. |
| [`GroebnerBasis.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasis.lean) | Reducedness half of Theorem 2.1 and the paper-facing wrapper. |
| [`Radical.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/Radical.lean) | **Corollary 2.2** — `J_G` is radical. |

### Section 3 — prime decomposition, dimension, minimal primes

| File | Contents |
|---|---|
| [`PrimeIdeals.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeIdeals.lean) | `primeComponent`, `componentCount`, `numConnectedComponents`. |
| [`PrimeDecomposition.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | **Theorem 3.2** and **Proposition 3.6**. |
| [`PrimeDecompositionDimension.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | **Corollary 3.3**, quotient-dimension and equidim support lemmas. |
| [`Corollary3_4.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/Corollary3_4.lean) | **Corollary 3.4**, the connected-case wrapper, **Corollary 3.7** CM branch. |
| [`MinimalPrimes.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | **Propositions 3.8 / 3.9**, minimal-prime classification. |
| [`CycleUnmixed.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/CycleUnmixed.lean) | Cycle component-count lemmas; unmixed branch of Corollary 3.7. |

### Section 4 — conditional independence ideals

| File | Contents |
|---|---|
| [`CIIdeals.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | `ciGraph`, `ciIdeal`, `CIStatement`; bridge theorems and transferred results. |

### Proposition 1.6 (Cohen–Macaulay criterion)

| File | Contents |
|---|---|
| [`Equidim.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/Equidim.lean) | Herzog–Hibi bipartite ring infrastructure and global CM theorem on the monomial side. |
| [`ReducedHH.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/ReducedHH.lean) | The reduced Herzog–Hibi ring used by the F2 route. |
| [`GroebnerDeformation.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerDeformation.lean) | One-parameter deformation `S[t] ⧸ Ĩ`; CM transfer from initial ideal to `J_G`. |
| [`Proposition1_6.lean`](https://github.com/tom111/BEI-lean/blob/master/BEI/Proposition1_6.lean) | **Proposition 1.6** assembled and the path-graph corollaries. |

## `toMathlib/` — Supporting library

Material intended for possible upstreaming to Mathlib, plus project-local
generic infrastructure.

### Cohen–Macaulay layer

| File | Contents |
|---|---|
| [`CohenMacaulay/Defs.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Defs.lean) | `ringDepth`, `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`. |
| [`CohenMacaulay/Basic.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Basic.lean) | Quotient-local-ring setup; regular-quotient CM transfer. |
| [`CohenMacaulay/Localization.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Localization.lean) | Localization, unmixedness, and local-to-global CM transfer. |
| [`CohenMacaulay/Polynomial.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Polynomial.lean) | CM lemmas for polynomial rings and finite-free extensions. |
| [`CohenMacaulay/TensorPolynomialAway.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/TensorPolynomialAway.lean) | Tensor-away isomorphism; localization preserves global CM. |

### Graded algebra

| File | Contents |
|---|---|
| [`GradedIrrelevant.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedIrrelevant.lean) | Irrelevant ideal of a connected graded algebra; maximality and homogeneous core. |
| [`GradedQuotient.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedQuotient.lean) | Graded structure on `A ⧸ I` for homogeneous `I`. |
| [`GradedAssociatedPrime.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedAssociatedPrime.lean) | Annihilators of homogeneous elements are homogeneous. |
| [`GradedPrimeAvoidance.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedPrimeAvoidance.lean) | Homogeneous prime avoidance and pairwise-incomparable reduction. |
| [`GradedRegularSop.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedRegularSop.lean) | Graded-algebra structure on `A ⧸ ⟨ℓ⟩` for a regular homogeneous element. |
| [`GradedFiniteFree.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedFiniteFree.lean) | Finite-free Case C route for connected graded CM algebras. |
| [`GradedCM.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedCM.lean) | Graded local-to-global Cohen–Macaulay theorem. |
| [`GradedEquidim.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/GradedEquidim.lean) | Equidimensionality for connected graded CM algebras via finite-free + flat. |
| [`MvPolynomialHomogeneous.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/MvPolynomialHomogeneous.lean) | Graded contraction in `MvPolynomial`; non-zero-divisor criterion. |

### Equidimensionality and dimension

| File | Contents |
|---|---|
| [`Equidim/Defs.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/Equidim/Defs.lean) | Local working definition `IsEquidimRing`. |
| [`IntegralDimension.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/IntegralDimension.lean) | `ringKrullDim` invariant under integral injective extensions. |
| [`FiniteFreeEquidim.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/FiniteFreeEquidim.lean) | Equidimensionality for module-finite, module-flat algebras over a Noetherian domain. |
| [`QuotientDimension.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/QuotientDimension.lean) | Monotonicity of quotient dimension; supremum over minimal primes. |
| [`HeightVariableIdeal.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/HeightVariableIdeal.lean) | Krull dimension of `MvPolynomial / span(X_i)`. |
| [`HeightDeterminantal.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/HeightDeterminantal.lean) | `height(J_{K_m}) = m − 1` for the complete graph. |

### Monomial and squarefree primes

| File | Contents |
|---|---|
| [`IsPrimeSpanX.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/IsPrimeSpanX.lean) | Variable-generated ideals in `MvPolynomial` are prime over a domain. |
| [`MonomialIdeal.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/MonomialIdeal.lean) | `Ideal.IsMonomial`; prime and primary classification. |
| [`SquarefreeMonomialPrimes.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/SquarefreeMonomialPrimes.lean) | Edge ideals, vertex covers, minimal-prime ↔ minimal-vertex-cover bijection. |

### Other helpers

| File | Contents |
|---|---|
| [`IdealQuotientHelpers.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/IdealQuotientHelpers.lean) | Double-quotient and `QuotSMulTop` ↔ `R ⧸ span {x}` bridges. |
| [`MinimalPrimesRegular.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/MinimalPrimesRegular.lean) | Non-zero-divisor criterion via minimal-prime avoidance in reduced rings. |
| [`PolynomialAwayTensor.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/PolynomialAwayTensor.lean) | `K[α] ⊗_K K[β][m^{-1}] ≃ K[α ⊔ β][m'^{-1}]`. |
| [`TensorLocalisation.lean`](https://github.com/tom111/BEI-lean/blob/master/toMathlib/TensorLocalisation.lean) | Localization of a tensor product at a prime contracting to `m`. |

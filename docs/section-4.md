---
title: Section 4
---

# Section 4: CI-Ideals and Robustness

## Status

The current Section 4 theorem layer is formalized in `BEI/CIIdeals.lean` for the
binary-output setting used in the paper. This includes both CI-ideal = BEI bridge
theorems and the transferred Section 2 / Section 3 consequences that have been carried
over so far.

Current landed declarations:

1. `ciGraph`
2. `ciIdeal`
3. `ciIdeal_single_eq_binomialEdgeIdeal`
4. `CIStatement`
5. `ciGraphSpec`
6. `ciIdealSpec`
7. `ciIdealSpec_eq_binomialEdgeIdeal`
8. `ciIdealSpec_isRadical`
9. `ciIdealSpec_primeDecomposition`
10. `ciIdealSpec_minimalPrimes`

## Intended formal content

The mathematical content to be formalized is narrower than the full statistical prose of
the paper. The central expected steps are:

1. define the relevant CI ideals in the binary-output setting;
2. identify them with binomial edge ideals of graphs on the input state space;
3. extend the single-statement bridge to robustness specifications;
4. transfer radicality, prime decomposition, and minimal-prime results from the
   earlier sections.

## Position in the project

Section 4 sits on top of the algebraic results from Sections 2 and 3 through the
single-statement and specification-level bridge theorems. The currently transferred
minimal-prime theorem keeps the connectedness hypothesis from Corollary 3.9, so that
restriction remains part of the present Lean endpoint.

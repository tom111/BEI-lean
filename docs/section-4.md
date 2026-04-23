---
title: Section 4
---

# Section 4: Conditional Independence Ideals and Robustness

Section 4 identifies the conditional-independence ideals from the paper with
binomial edge ideals, so the radicality, prime decomposition, and
minimal-prime results from earlier sections transfer to the algebraic
statistics setting.

## Theorem map

| Paper result | Lean declaration(s) | Lean file |
|---|---|---|
| CI graph (binary output) | `ciGraph` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| CI ideal (binary output) | `ciIdeal` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| Single-statement bridge | `ciIdeal_single_eq_binomialEdgeIdeal` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| Robustness specification | `CIStatement`, `ciGraphSpec`, `ciIdealSpec` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| Specification bridge | `ciIdealSpec_eq_binomialEdgeIdeal` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| CI radicality | `ciIdealSpec_isRadical` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| CI prime decomposition | `ciIdealSpec_primeDecomposition` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |
| CI minimal primes | `ciIdealSpec_minimalPrimes` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) |

The current minimal-prime theorem keeps the connectedness hypothesis from
Corollary 3.9, so that restriction remains part of the Lean statement here.

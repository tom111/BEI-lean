---
title: Section 4
---

# Section 4: Conditional Independence Ideals and Robustness

Section 4 identifies the conditional-independence ideals from the paper with
binomial edge ideals and then transfers the algebraic results from the earlier
sections.

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| CI graph (binary output) | `ciGraph` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| CI ideal (binary output) | `ciIdeal` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| Single-statement bridge | `ciIdeal_single_eq_binomialEdgeIdeal` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| Robustness specification | `CIStatement`, `ciGraphSpec`, `ciIdealSpec` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| Specification bridge | `ciIdealSpec_eq_binomialEdgeIdeal` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| CI radicality | `ciIdealSpec_isRadical` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| CI prime decomposition | `ciIdealSpec_primeDecomposition` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |
| CI minimal primes | `ciIdealSpec_minimalPrimes` | [CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean) | Exact |

## Notes

The formalization proves:

- CI ideals in the binary-output setting are defined directly;
- the single-statement and specification-level ideals are identified with binomial edge ideals;
- radicality, prime decomposition, and minimal-prime results are then transferred from Sections 2 and 3.

The current minimal-prime theorem keeps the connectedness hypothesis from Corollary 3.9,
so that restriction remains part of the present Lean statement.

---
title: Section 3
---

# Section 3: Prime Decomposition, Dimension, Minimal Primes

Section 3 contains the algebraic core of the paper: the prime ideals `P_S`,
the decomposition of `J_G`, the dimension formula, and the description of the
minimal primes.

For mathematicians, this is the page that explains how the graph controls the
prime ideals of the binomial edge ideal. The complete prime decomposition and
dimension formula are formalized. Proposition 1.6, Corollary 3.4, and
Corollary 3.7 are formalized as well.

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Lemma 3.1 | `lemma_3_1` | [PrimeIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeIdeals.lean) | Exact |
| Theorem 3.2 | `theorem_3_2` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | Exact |
| Corollary 3.3 | `corollary_3_3` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Exact |
| Corollary 3.3 lower bound | `corollary_3_3_lower_bound` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Exact |
| Corollary 3.4 | `corollary_3_4`, `corollary_3_4_connected` | [Corollary3_4.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Corollary3_4.lean) | Exact |
| Proposition 3.6 | `prop_3_6` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | Equivalent |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_cm_forward`, `corollary_3_7_cm_fin` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean), [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean), [Corollary3_4.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Corollary3_4.lean) | Exact |
| Proposition 3.8 | `prop_3_8` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Equivalent |
| Corollary 3.9 | `corollary_3_9` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Equivalent |

## Reading the table

- `Exact` means the Lean theorem follows the paper statement closely.
- `Equivalent` means the same mathematics is formalized, but the Lean theorem is
  packaged differently.
- `Partial` means a paper statement has only been reached through an
  equidimensional or otherwise incomplete substitute so far.

## Notes

Prime decomposition, minimal primes, and the dimension formula are formalized.
The Section 3 Cohen–Macaulay status is:

- the prime decomposition is formalized;
- the dimension consequences are formalized;
- the minimal-prime characterization is formalized;
- Proposition 1.6 is formalized in its paper-faithful CM form;
- Corollary 3.4 is formalized in its paper-faithful CM form;
- the prime, unmixed, and Cohen–Macaulay cycle-graph equivalences are formalized;
- and the equivalent-packaging items on this page are Proposition 3.6,
  Proposition 3.8, and Corollary 3.9.

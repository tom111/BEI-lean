---
title: Section 3
---

# Section 3: Prime Decomposition, Dimension, Minimal Primes

Section 3 is the algebraic core of the paper: the prime ideals $P_S$,
the decomposition of $J_G$, the dimension formula, and the description of the
minimal primes, all read off from the graph.

## Theorem map

| Paper result | Lean declaration(s) | Lean file |
|---|---|---|
| Lemma 3.1 | `lemma_3_1` | [PrimeIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeIdeals.lean) |
| Theorem 3.2 | `theorem_3_2` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) |
| Corollary 3.3 | `corollary_3_3` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) |
| Corollary 3.3 lower bound | `corollary_3_3_lower_bound` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) |
| Corollary 3.4 | `corollary_3_4`, `corollary_3_4_connected` | [Corollary3_4.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Corollary3_4.lean) |
| Proposition 3.6 | `prop_3_6` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_cm_forward`, `corollary_3_7_cm_fin` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean), [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean), [Corollary3_4.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Corollary3_4.lean) |
| Proposition 3.8 | `prop_3_8` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) |
| Corollary 3.9 | `corollary_3_9` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) |

Proposition 3.6, Proposition 3.8, and Corollary 3.9 are packaged a little
differently in Lean than in the paper (same mathematics, slightly different
phrasing); the remaining entries are close formal matches to the paper.

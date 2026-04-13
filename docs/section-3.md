---
title: Section 3
---

# Section 3: Prime Decomposition, Dimension, Minimal Primes

Section 3 contains the algebraic core of the paper: the prime ideals `P_S`,
the decomposition of `J_G`, the dimension formula, and the description of the
minimal primes.

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Lemma 3.1 | `lemma_3_1` | [PrimeIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeIdeals.lean) | Exact |
| Theorem 3.2 | `theorem_3_2` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | Exact |
| Corollary 3.3 | `corollary_3_3` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Exact |
| Corollary 3.3 lower bound | `corollary_3_3_lower_bound` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Exact |
| Corollary 3.4 | `corollary_3_4_equidim` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Partial |
| Proposition 3.6 | `prop_3_6` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | Equivalent |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_equidim` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean), [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean), [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Partial |
| Proposition 3.8 | `prop_3_8` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Equivalent |
| Corollary 3.9 | `corollary_3_9` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Equivalent |

## Notes

Prime decomposition, minimal primes, and the dimension formula are formalized.
The Cohen–Macaulay consequences are still partial:

- the prime decomposition is formalized;
- the dimension consequences are formalized;
- the minimal-prime characterization is formalized;
- the prime and unmixed cycle-graph equivalences are formalized exactly;
- and the remaining Cohen–Macaulay statements are currently represented by
  `corollary_3_4_equidim` and `corollary_3_7_equidim`.

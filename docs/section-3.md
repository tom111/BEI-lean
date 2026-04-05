---
title: Section 3
---

# Section 3: Prime Decomposition, Dimension, Minimal Primes

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Lemma 3.1 | `lemma_3_1` | [PrimeIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeIdeals.lean) | Exact |
| Theorem 3.2 | `theorem_3_2` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | Exact |
| Corollary 3.3 | `corollary_3_3` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Exact |
| Corollary 3.3 lower bound | `corollary_3_3_lower_bound` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Exact |
| Corollary 3.4 | `corollary_3_4` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean) | Sorry |
| Proposition 3.6 | `prop_3_6` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean) | Equivalent |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_CM` | [PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean), [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Partial |
| Proposition 3.8 | `prop_3_8` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Equivalent |
| Corollary 3.9 | `corollary_3_9` | [MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean) | Equivalent |

## Notes

Section 3 contains the algebraic core of the project:

- the prime components `P_S(G)`,
- the prime decomposition of `J_G`,
- the description of minimal primes;
- and the Krull-dimension formula from Corollary 3.3.

The major remaining statements in this section are now:

- Corollary 3.4 on the CM branch;
- the CM completion of Corollary 3.7.

The non-CM branch of Corollary 3.7 is formalized in `MinimalPrimes.lean`. The remaining
Section 3 work is concentrated in the unfinished CM proofs.

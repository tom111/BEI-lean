---
title: Section 3
---

# Section 3: Prime Decomposition, Dimension, Minimal Primes

## Theorem map

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Lemma 3.1 | `lemma_3_1` | `PrimeIdeals.lean` | Exact | Height formula proved |
| Theorem 3.2 | `theorem_3_2` | `PrimeDecomposition.lean` | Exact | Prime decomposition proved |
| Corollary 3.3 | `corollary_3_3` | `PrimeDecomposition.lean` | Blocked | Dimension formula |
| Corollary 3.3 lower bound | `corollary_3_3_lower_bound` | `PrimeDecomposition.lean` | Blocked | `dim ≥ n + c(G)` |
| Corollary 3.4 | `corollary_3_4` | `PrimeDecomposition.lean` | Blocked | Depends on CM foundation |
| Proposition 3.6 | `prop_3_6` | `PrimeDecomposition.lean` | Equivalent | Reachability formulation |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_CM` | `PrimeDecomposition.lean` / `MinimalPrimes.lean` | Partial | Prime branch largely in place; CM branch blocked |
| Proposition 3.8 | `prop_3_8` | `MinimalPrimes.lean` | Equivalent | Uses `SameComponent` packaging |
| Corollary 3.9 | `corollary_3_9` | `MinimalPrimes.lean` | Equivalent | Uses `IsCutVertexRelative` |

## Main remaining bottlenecks

### Corollary 3.3

This is the main non-CM open theorem.

Relevant guides:

- [`guides/COR_3_3_DIMENSION.md`](/home/tom/BEI-lean/guides/COR_3_3_DIMENSION.md)
- [`guides/ANSWER_01_DIMENSION_OF_QUOTIENT_BY_PRIME.md`](/home/tom/BEI-lean/guides/ANSWER_01_DIMENSION_OF_QUOTIENT_BY_PRIME.md)
- [`guides/ANSWER_02_RADICAL_IDEAL_DIMENSION_FORMULA.md`](/home/tom/BEI-lean/guides/ANSWER_02_RADICAL_IDEAL_DIMENSION_FORMULA.md)
- [`guides/ANSWER_03_PRIMALITY_OF_SUM_IN_DISJOINT_VARIABLES.md`](/home/tom/BEI-lean/guides/ANSWER_03_PRIMALITY_OF_SUM_IN_DISJOINT_VARIABLES.md)
- [`guides/ANSWER_08_CHAIN_ABOVE_PRIME_COMPONENT.md`](/home/tom/BEI-lean/guides/ANSWER_08_CHAIN_ABOVE_PRIME_COMPONENT.md)
- [`guides/ANSWER_11_LTSERIES_ASSEMBLY.md`](/home/tom/BEI-lean/guides/ANSWER_11_LTSERIES_ASSEMBLY.md)

### Corollary 3.7 unmixed branch

The unmixed branch is substantially more local than the full CM story and should be
treated as its own theorem target.

Relevant guides:

- [`guides/COR_3_7_FULL_EQUIVALENCE.md`](/home/tom/BEI-lean/guides/COR_3_7_FULL_EQUIVALENCE.md)
- [`guides/ANSWER_06_UNMIXED_FOR_COR_3_7.md`](/home/tom/BEI-lean/guides/ANSWER_06_UNMIXED_FOR_COR_3_7.md)
- [`guides/ANSWER_09_CYCLE_COMPONENTCOUNT_COMBINATORICS.md`](/home/tom/BEI-lean/guides/ANSWER_09_CYCLE_COMPONENTCOUNT_COMBINATORICS.md)
- [`guides/ANSWER_10_CYCLE_INDUCE_PRECONNECTED.md`](/home/tom/BEI-lean/guides/ANSWER_10_CYCLE_INDUCE_PRECONNECTED.md)


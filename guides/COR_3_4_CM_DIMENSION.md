# Guide: Corollary 3.4 and the CM Dimension Consequences

## Paper statement

The paper proves:

```text
If S / J_G is Cohen–Macaulay, then dim S / J_G = n + c(G).
```

This is currently stubbed in [PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean)
as `corollary_3_4`.


## Dependency picture

This corollary now sits on top of two ingredients:

1. a genuine notion of Cohen–Macaulayness and equidimensionality;
2. the Section 3 dimension/minimal-prime results.

So the right order is:

1. use the existing local CM API;
2. package the equidimensional consequence cleanly;
3. then prove `corollary_3_4`.


## Core mathematical structure of the paper proof

The paper uses:

1. `P_∅(G)` is a minimal prime of `J_G`;
2. `dim(R / P_∅(G)) = n + c(G)`;
3. if `R / J_G` is Cohen–Macaulay, then it is equidimensional;
4. hence all minimal primes have the same dimension, so the quotient dimension equals
   the dimension of `R / P_∅(G)`.

Only step 3 is genuinely CM-dependent, and the repo now already has the beginnings of
that API in `isCohenMacaulay_of_equidim_minimalPrimes`.


## What is already available

### Subgoal 1: isolate `P_∅` as a distinguished minimal prime

This is already available from:

- `minimalPrimes_characterization`
- `primeComponent_isPrime`
- `binomialEdgeIdeal_le_primeComponent`

Package a theorem like:

```text
primeComponent G ∅ ∈ minimalPrimes (binomialEdgeIdeal G)
```

if it is not already easy to obtain in one line.

### Subgoal 2: compute `dim(R / P_∅)`

This already falls out of the `Cor 3.3` infrastructure and the fixed-`S` quotient-dimension
theorems.

### Subgoal 3: define the exact CM consequence needed

Rather than attacking full CM theory, isolate the one theorem actually needed here:

```text
CohenMacaulay quotient -> all minimal primes have equal quotient dimension
```

or an equivalent equidimensionality theorem.

That is now the true blocker for Corollary 3.4.


## Suggested work split

## Phase A: finish the non-CM prerequisites

This phase is done.

## Phase B: decide where the CM equidimensionality theorem lives

The repo already has a real local definition. The work now is to make the proof use the
existing quotient-dimension lemmas instead of a one-off ad hoc argument.


## Possible helper theorem packaging

Recommended theorem names:

- `primeComponent_empty_mem_minimalPrimes`
- `ringKrullDim_quot_primeComponent_empty`
- `IsCohenMacaulay.equidimensional_quotient` or similar as a local convenience theorem


## Definition of done

This guide is complete when:

1. all non-CM prerequisites for `corollary_3_4` are already formalized;
2. the final theorem depends only on a precise CM equidimensionality lemma;
3. the repo no longer presents `corollary_3_4` as blocked by vague missing foundations.

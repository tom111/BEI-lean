# Guide: Corollary 3.4 and the CM Dimension Consequences

## Paper statement

The paper proves:

```text
If S / J_G is Cohen–Macaulay, then dim S / J_G = n + c(G).
```

This is currently stubbed in [PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
as `corollary_3_4`.


## Dependency picture

This corollary sits on top of two separate ingredients:

1. a genuine notion of Cohen–Macaulayness and equidimensionality;
2. the Section 3 dimension/minimal-prime results.

So the right order is:

1. finish `corollary_3_3`;
2. establish a real CM API;
3. prove the equidimensional consequence;
4. then prove `corollary_3_4`.


## Core mathematical structure of the paper proof

The paper uses:

1. `P_∅(G)` is a minimal prime of `J_G`;
2. `dim(R / P_∅(G)) = n + c(G)`;
3. if `R / J_G` is Cohen–Macaulay, then it is equidimensional;
4. hence all minimal primes have the same dimension, so the quotient dimension equals
   the dimension of `R / P_∅(G)`.

Only step 3 is genuinely CM-dependent.


## What can be formalized before the CM API exists

### Subgoal 1: isolate `P_∅` as a distinguished minimal prime

This is essentially already available from:

- `minimalPrimes_characterization`
- `primeComponent_isPrime`
- `binomialEdgeIdeal_le_primeComponent`

Package a theorem like:

```text
primeComponent G ∅ ∈ minimalPrimes (binomialEdgeIdeal G)
```

if it is not already easy to obtain in one line.

### Subgoal 2: compute `dim(R / P_∅)`

This should fall out of the `Cor 3.3` infrastructure or the fixed-`S` quotient-dimension
theorem from that guide.

### Subgoal 3: define the exact CM consequence needed

Rather than attacking full CM theory, isolate the one theorem needed here:

```text
CohenMacaulay quotient -> all minimal primes have equal quotient dimension
```

or an equivalent equidimensionality theorem.

That is the true blocker for Corollary 3.4.


## Suggested work split

## Phase A: finish the non-CM prerequisites

Depend on [COR_3_3_DIMENSION.md](/home/tom/BEI-lean/guides/COR_3_3_DIMENSION.md).

By the end of this phase, Corollary 3.4 should reduce to one CM lemma.

## Phase B: decide where the CM equidimensionality theorem lives

If a future Mathlib CM API arrives:

- use it directly.

If not:

- create a local theorem file for CM consequences only if there is a real definition.

Do not prove Corollary 3.4 from a fake placeholder.


## Possible helper theorem packaging

Recommended theorem names:

- `primeComponent_empty_mem_minimalPrimes`
- `ringKrullDim_quot_primeComponent_empty`
- `IsCohenMacaulay.equidimensional_quotient` or similar once a real CM API exists


## Definition of done

This guide is complete when:

1. all non-CM prerequisites for `corollary_3_4` are already formalized;
2. the final theorem depends only on a real CM equidimensionality theorem;
3. the repo no longer presents `corollary_3_4` as blocked by a vague "CM missing"
   comment, but by one precise missing theorem.

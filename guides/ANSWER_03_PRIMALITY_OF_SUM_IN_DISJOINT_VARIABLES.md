# Answer to Q3: Primality of the Intermediate Ideals `Q_k`

## Preserved question

For the Corollary 3.3 lower-bound chain, we need intermediate ideals `Q_k` built from:

- complete-graph BEI pieces on disjoint variable blocks; and
- variable ideals killing selected `x`-variables.

The original question asked how best to prove each `Q_k` is prime in Lean:

- via quotient-isomorphism machinery,
- via `MvPolynomial` domain instances,
- or via a direct kernel-of-a-map-to-a-domain construction.

## Short answer

For the BEI application, the cleanest proof is to construct a surjective ring map to a
domain and identify its kernel with `Q_k`.

Do not start by searching for a fully abstract theorem about disjoint-variable sums of
prime ideals.

## Recommended proof path

1. Build the quotient/domain coming from the surviving complete-graph blocks.
2. Extend it by free polynomial variables for the surviving `y`-variables in the killed
   region.
3. Define a map from the ambient polynomial ring using `MvPolynomial.eval₂`.
4. Show every generator of `Q_k` maps to zero.
5. Show the kernel is exactly `Q_k`.
6. Conclude `Q_k` is prime because the codomain is a domain.

## Sub-question answers

### Polynomial ring over a domain

Yes, this should be available as an instance in Mathlib, and it is the key reason the
direct kernel route is attractive.

### Quotient-isomorphism route

Possible, but heavier than needed. It requires more quotient bookkeeping than the kernel
argument.

### `eval₂` / `aeval`

This is the recommended implementation tool. The map is an "evaluation at zero on some
variables, canonical image on the others" construction.

### Existing abstract theorem

Even if something close exists, the explicit kernel theorem is still likely the cleanest
for the actual `Q_k` used in the lower-bound chain.

## Recommendation

Prove a concrete BEI-specific theorem:

```text
ker(phi_k) = Q_k
```

with codomain a polynomial ring over a domain. That is enough for the lower-bound proof.

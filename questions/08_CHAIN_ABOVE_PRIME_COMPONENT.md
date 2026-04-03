# Question 8: Constructing an explicit chain of primes above P_S(G)

## Context

We need `ringKrullDim (R ⧸ primeComponent G S) = |V| - |S| + c(S)` where
`R = MvPolynomial (V ⊕ V) K`.

By `ringKrullDim_quotient`: `dim(R/P_S) = Order.krullDim(zeroLocus P_S)`.
And `Order.le_krullDim_iff` says `n ≤ krullDim ↔ ∃ LTSeries of length n`.

So the lower bound requires an `LTSeries` of length `|V| - |S| + c(S)` in
`PrimeSpectrum.zeroLocus P_S`.

The upper bound requires `height(P_S) + coheight(P_S) ≤ dim(R) = 2|V|`
combined with `height(P_S) = |S| + |V| - c(S)` from `lemma_3_1`.

## Proposed chain for the lower bound

For G with components G_1,...,G_c of G[V\S] on vertex sets V_1,...,V_c:

```
P_S < Q_1 < Q_2 < ... < Q_{c-1} < (x_all, y_S) < ... < (x_all, y_all) = m
```

where `Q_k` replaces the BEI of component V_{c-k+1},...,V_c with x-variable
generators (killing x_v for those components).

Chain length: (c-1) + 1 + (|V| - |S|) = |V| - |S| + c.

Wait, let me recount:
- P_S to Q_1: 1 step
- Q_1 to Q_2: 1 step (c-1 steps total from P_S to Q_{c-1})
- Q_{c-1} to (x_all, y_S): 1 step (total c steps from P_S to (x_all, y_S))
- (x_all, y_S) to (x_all, y_S, y_{w_1}): 1 step
- ... adding y-variables for w ∉ S: |V| - |S| steps

Total: c + (|V| - |S|) = |V| - |S| + c(S). ✓

## Question

1. For the Q_k intermediate ideals: the quotient R/Q_k is a polynomial ring
   over `primeComponent G' ∅` where G' is the graph restricted to remaining
   components. `primeComponent_isPrime` gives primality of the base ring.
   Can we use `MvPolynomial.isDomain` (polynomial ring over domain is domain)
   to get primality? What is the cleanest Lean formalization of:
   "Q_k is prime because R/Q_k ≅ D[y-variables] for domain D"?

2. The `eval₂` approach (ANSWER_03): define a ring hom from R to a domain
   that kills x_v for v in the killed components and maps the rest canonically.
   The kernel is Q_k. How to construct this concretely in Lean?
   
   Sketch: `MvPolynomial.aeval` with a function `BinomialEdgeVars V → D` that
   sends `inl v ↦ 0` for v in killed components and `inl v ↦ x_v` otherwise,
   and `inr v ↦ y_v` always.

3. For the variable chain from (x_all, y_S) to (x_all, y_all): these are
   variable ideals, so `MvPolynomial.isPrime_span_X_image` from
   `toMathlib/HeightVariableIdeal.lean` applies. But we need each intermediate
   ideal `(x_all, y_S, y_{w_1}, ..., y_{w_k})` to be prime and strictly
   larger than the previous. This should be straightforward since we're just
   adding one variable generator at a time. Is there a clean induction?

4. For the upper bound: `coheight(P_S) ≤ 2|V| - height(P_S) = |V| - |S| + c(S)`.
   This should follow from `krullDim_eq_iSup_height_add_coheight_of_nonempty`
   plus `ringKrullDim_quotient` plus `MvPolynomial.ringKrullDim_of_isNoetherianRing`.
   Is there a clean lemma path?

5. Would it be simpler to avoid the chain construction entirely and instead
   prove the catenary property for the specific primes P_S using their explicit
   structure (variable ideal + determinantal ideal in disjoint blocks)?

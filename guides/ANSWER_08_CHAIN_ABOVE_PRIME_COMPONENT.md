# Answer to Q8: Explicit Prime Chains Above `primeComponent G S`

## Preserved question

We need:

```text
ringKrullDim (R ⧸ primeComponent G S) = |V| - |S| + c(S)
```

with `R = MvPolynomial (V ⊕ V) K`.

The proposed lower-bound route is to build an explicit chain of primes above `P_S` inside
`PrimeSpectrum.zeroLocus P_S`, of length `|V| - |S| + c(S)`.

The question asked:

1. how to prove the intermediate `Q_k` are prime;
2. whether the `eval₂` / kernel-to-domain approach is the cleanest Lean route;
3. how to handle the variable-ideal tail of the chain;
4. what the clean upper-bound path should be;
5. whether a direct catenary argument for these specific primes would be simpler.


## Short answer

Yes, the explicit-chain route is viable, and the cleanest proof of primality for the
intermediate `Q_k` is the **kernel of a map to a domain** approach from Answer 03.

This is a good route for the **lower bound**.

For the **upper bound**, use the order-theoretic inequality:

```text
height(P_S) + coheight(P_S) ≤ dim(R)
```

together with the already-proved height formula and the ambient polynomial-ring dimension.

So:

- lower bound = explicit chain;
- upper bound = height + coheight ≤ ambient dimension.


## Best decomposition

## Part A: the lower bound via an explicit chain

The proposed chain shape is good:

```text
P_S < Q_1 < ... < Q_{c-1} < (x_all, y_S) < ... < (x_all, y_all).
```

This cleanly separates the proof into:

1. a "component-collapse" segment;
2. a "variable-adjoining" segment.

That is the right way to structure it in Lean as well.


## Part B: proving `Q_k` is prime

### Recommended route

Use a concrete ring map:

```text
phi_k : R -> MvPolynomial freeYVars D_k
```

where:

- `D_k` is the quotient ring for the surviving complete-graph blocks;
- the killed `x`-variables go to `0`;
- the surviving variables go to their canonical images;
- the remaining free `y`-variables become polynomial variables.

Then show:

```text
ker(phi_k) = Q_k.
```

Since the codomain is a polynomial ring over a domain, it is a domain, hence `Q_k` is prime.

### Why this is better than quotient-isomorphism first

Because you only need primality, not a polished quotient equivalence.
Kernel equality is enough.

If a quotient equivalence later drops out cleanly, fine, but do not make it the first target.


## Part C: how to build `phi_k` concretely

Yes, the right tool is an evaluation/renaming map built from the multivariate polynomial
universal property.

The clean strategy is:

1. define the codomain variables as a sum type recording:
   - surviving `x/y` variables modulo the determinantal relations;
   - free `y` variables from the killed components;
2. define the variable assignment
   `BinomialEdgeVars V -> codomain`;
3. induce the ring hom via `MvPolynomial.eval₂Hom` or the equivalent API.

In practical terms:

- killed `x_v` go to `0`;
- `y_v` in the variable tail go to polynomial indeterminates;
- surviving variables go to the quotient-domain images.

The key proof burden is kernel equality, not map construction.


## Part D: the variable-ideal tail

This is the easy segment and should be handled separately.

Once you reach `(x_all, y_S)`, you can add the missing `y`-variables one at a time.
Each step is:

- prime variable ideal in a polynomial ring / quotient already known to be a domain;
- strict inclusion because the added variable was not already in the previous ideal.

Do this by a clean induction over an enumeration of `V \ S`.

Do not mix this segment with the `Q_k` construction.


## Part E: upper bound

This should **not** require any new chain construction.

Use:

```text
coheight(P_S) ≤ dim(R) - height(P_S)
```

with:

- `dim(R) = 2|V|`;
- `height(P_S) = |S| + |V| - c(S)`.

Then:

```text
coheight(P_S) ≤ |V| - |S| + c(S).
```

Since:

```text
ringKrullDim (R ⧸ P_S) = coheight(P_S)
```

via `ringKrullDim_quotient = krullDim(zeroLocus P_S)`, this gives the upper bound.

So the chain only needs to prove the lower bound.


## Answer to the meta-question

### Would a direct catenary argument for these specific primes be simpler?

No.

At that point you are essentially proving the quotient-dimension theorem anyway, but with
less explicit control. The chain-plus-upper-bound method is cleaner for these `P_S`.


## Final recommendation

For `ringKrullDim (R ⧸ P_S)`:

1. prove the lower bound by the explicit chain you proposed;
2. prove `Q_k` prime by `ker(phi_k)` into a polynomial ring over a domain;
3. prove the upper bound from `height + coheight ≤ dim(R)`;
4. do **not** pursue catenarity here.

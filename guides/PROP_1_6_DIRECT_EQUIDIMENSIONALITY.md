# Proposition 1.6 via Direct Equidimensionality

## Preserved context

Current live state in `BEI/CohenMacaulay.lean`:

- `prop_1_6` is stated and reduced to a single sorry:
  `cm_transfer_initialIdeal`
- the paper-faithful reduction through the monomial initial ideal and the
  Herzog–Hibi bipartite graph is already formalized
- the monomial-side CM statement
  `monomialInitialIdeal_isCohenMacaulay`
  is already proved

Current local CM definition:

- in `toMathlib/CohenMacaulay/Defs.lean`, `IsCohenMacaulayRing` means
  equidimensionality of minimal primes, not the full depth-based definition

This matters because the standard Gröbner theorem used in the paper transfers
genuine Cohen–Macaulayness under flat deformation. It does **not** automatically
transfer the weaker local surrogate “all minimal primes have equal quotient
dimension”.

So this guide is the direct fallback route:

- do **not** try to formalize the full Gröbner flat-deformation theorem
- instead, finish Proposition 1.6 directly under the repo’s current local CM
  definition


## Task

Prove Proposition 1.6 directly by showing that every minimal prime
`P_S(G)` of `J_G` has the same quotient dimension.

The exact target shape is:

```lean
private theorem prop_1_6_componentCount_eq
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hConn : G.Connected)
    (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G)
    {S : Finset (Fin n)}
    (hSmin : primeComponent (K := K) G S ∈
      (binomialEdgeIdeal (K := K) G).minimalPrimes) :
    componentCount G S = S.card + 1
```

Then use:

- `minimalPrimes_characterization`
- `ringKrullDim_quot_primeComponent`
- `isCohenMacaulay_of_equidim_minimalPrimes`

to prove `prop_1_6` directly.


## Why this route is legitimate

This is **not** the paper’s proof. It is a fallback route justified only because
the repo’s local `IsCohenMacaulayRing` is already defined as equidimensionality.

So the correct endpoint here is:

- an honest proof of the current local theorem `prop_1_6`

This route should **not** be described as a formalization of Eisenbud 15.17 or as
the paper’s actual Gröbner-degeneration proof.


## What is already available

From `BEI/PrimeDecompositionDimension.lean`:

- `ringKrullDim_quot_primeComponent`
- `isCohenMacaulay_of_equidim_minimalPrimes`

From `BEI/PrimeDecomposition.lean` / `BEI/MinimalPrimes.lean`:

- `minimalPrimes_characterization`
- `corollary_3_9`

From `BEI/CohenMacaulay.lean`:

- `prop_1_6_herzogHibi`
- `hhEdgeSet_diagonal`
- `minimalVertexCover_exactlyOne`
- `minimalVertexCover_subset_active`
- `minimalVertexCover_ncard_eq`
- `minimalPrime_bipartiteEdgeMonomialIdeal_iff`
- `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`

These already encode the hard combinatorics on the bipartite HH side.


## Recommended strategy

### Main idea

Do **not** push new commutative algebra.

Instead:

1. classify the minimal-prime data on the BEI side using the already-proved HH
   bipartite-graph combinatorics;
2. extract the numerical statement needed for `componentCount G S`;
3. plug that into the existing dimension formula for `P_S(G)`.


## Decomposition into subgoals

### Step 1. Find the right bridge from BEI minimal primes to HH data

The minimal-prime sets `S` for `J_G` and the minimal vertex covers for `hhEdgeSet G`
are not literally the same objects, but they should encode the same numerical
information under the Proposition 1.6 hypotheses.

Do not guess this numerology globally. Isolate one exact bridge theorem.

Good target shape:

```lean
private theorem prop_1_6_minimalPrime_to_cover_data
  ...
```

This theorem should connect:

- `hSmin : primeComponent G S ∈ J.minimalPrimes`

to a controlled combinatorial description of `S` in terms of the active indices
that appear in the HH graph.


### Step 2. Turn the HH “exactly one” theorem into a count on the BEI side

The theorem `minimalVertexCover_exactlyOne` is the important input:

- every minimal vertex cover of `hhEdgeSet G` picks exactly one of
  `Sum.inl i` or `Sum.inr i`
  for each active index `i`

This should force a fixed cardinality for the relevant cover data.

The next job is to translate that fixed cardinality into the BEI-side quantity
that appears in

`ringKrullDim_quot_primeComponent G S = |V| - |S| + componentCount G S`.


### Step 3. Prove the exact component-count equality

The theorem you actually want is:

```lean
componentCount G S = S.card + 1
```

for every minimal-prime set `S` under the Proposition 1.6 hypotheses.

This is the direct analogue of the path-graph argument already used in
`path_is_CM`, but now driven by the HH combinatorics already formalized in
`BEI/CohenMacaulay.lean`.


### Step 4. Convert to equal quotient dimensions

Once `componentCount G S = S.card + 1` is available, the dimension formula gives:

```lean
ringKrullDim (R ⧸ P_S(G)) = n + 1
```

for every minimal prime `P_S(G)`.

Then use `isCohenMacaulay_of_equidim_minimalPrimes`.


### Step 5. Replace the current sorry-based proof of `prop_1_6`

If the direct route lands, remove `cm_transfer_initialIdeal` from the critical path
of Proposition 1.6.

Possible outcomes:

- leave `cm_transfer_initialIdeal` in the file as a clearly deferred theorem, but do
  not use it in `prop_1_6`; or
- move it out of the way entirely if that produces a cleaner theorem layer

Do not silently leave a sorry-based lemma on the proof path once a direct proof exists.


## Warnings / false routes

### Do not claim this proves the paper’s actual Gröbner transfer theorem

It does not. It only closes Proposition 1.6 under the repo’s local working
definition of `IsCohenMacaulayRing`.


### Do not try to prove a huge new classification of all closed graphs

You only need the numerical equality for minimal-prime sets under the Proposition 1.6
hypotheses.


### Do not rebuild the HH graph API

Use the already-proved theorems in `BEI/CohenMacaulay.lean`.


### Do not start from scratch on path-style induction

The repo already has stronger HH-side combinatorics than the old path proof used.
Exploit those first.


## Definition of done

Best outcome:

- a direct proof of `prop_1_6` via `isCohenMacaulay_of_equidim_minimalPrimes`
- `cm_transfer_initialIdeal` removed from the proof path
- docs updated to say Proposition 1.6 is proved directly under the local CM definition

Minimum acceptable outcome:

- one exact BEI-side theorem reducing Proposition 1.6 to the numerical identity
  `componentCount G S = S.card + 1`
- or the numerical identity itself, even before final packaging


## Files likely involved

- `BEI/CohenMacaulay.lean`
- `BEI/PrimeDecompositionDimension.lean`
- `TODO.md`
- `FORMALIZATION_MAP.md`
- `guides/INDEX.md`

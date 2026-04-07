# Guide: Proposition 1.6 HH Equidimensionality Step

## Task

Take the next concrete step in Proposition 1.6 after the variable-pair bridge.

The bridge packet is done:

- `hhEdgeSet`
- `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`
- `minimalPrime_bipartiteEdgeMonomialIdeal_iff`

The next job is to use the Herzog–Hibi conditions already proved for `G` to show that
all minimal vertex covers of the associated bipartite graph have the same size, and
then package the resulting equidimensionality statement for the quotient by
`bipartiteEdgeMonomialIdeal`.


## Current live state

### In `BEI/CohenMacaulay.lean`

Already proved:

- `prop_1_6_herzogHibi`
- `hhEdgeSet`
- `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`
- `minimalPrime_bipartiteEdgeMonomialIdeal_iff`

So the reduction from `J_G` to the HH bipartite edge ideal is now packaged all the
way down to a minimal-prime / minimal-vertex-cover description.

### In `toMathlib/SquarefreeMonomialPrimes.lean`

Already proved:

- variable-pair ideals
- vertex covers / minimal vertex covers
- minimal prime ↔ minimal vertex cover classification

### In the local CM branch

`IsCohenMacaulay` is the local equidimensionality-style notion from
`toMathlib/CohenMacaulay/Defs.lean`, and the Section 3 CM consequences already use that
working definition.


## Exact next goal

Prove the equidimensionality step for the HH bipartite graph associated to
Proposition 1.6.

In practical terms:

1. use the HH conditions to show all minimal vertex covers of `hhEdgeSet G` have the
   same cardinality;
2. convert that to “all minimal primes of `bipartiteEdgeMonomialIdeal G` have the same
   quotient dimension”;
3. if that lands cleanly, package the quotient by `bipartiteEdgeMonomialIdeal G` as
   `IsCohenMacaulay` under the Prop 1.6 hypotheses.

Do not spend the round on the final transfer

- `S / in_<(J_G)` CM → `S / J_G` CM

unless the equidimensionality step lands easily and there is clearly time left.


## Why this is the right next packet

This is the remaining internal mathematical step before the final Gröbner-transfer
theorem.

The current chain is:

1. `J_G` → monomial initial ideal
2. y-shift to bipartite edge ideal
3. bridge to `variablePairIdeal`
4. minimal primes = minimal vertex covers
5. all minimal vertex covers have equal size
6. equidimensional quotient / local CM
7. transfer CM back from `in_<(J_G)` to `J_G`

Steps 1–4 are now done. Step 5 is the real next target.


## Recommended implementation plan

### Step 1: isolate the exact HH combinatorics on covers

Read `prop_1_6_herzogHibi` carefully and determine the clean combinatorial statement
you actually need about minimal vertex covers of `hhEdgeSet G`.

Do not start by proving a fully general theorem about arbitrary HH graphs if the
statement needed here is narrower and cleaner.

Good target shape:

- for `G` satisfying the Prop 1.6 hypotheses, any two minimal vertex covers of
  `hhEdgeSet G` have the same finite cardinality.

Since the variable set is finite, it is acceptable to formulate this with `Finite` /
`Fintype` machinery on the specific index type `BinomialEdgeVars (Fin n)`.

### Step 2: connect cover size to quotient dimension

For a variable ideal `span (X '' S)`, the quotient dimension should be the number of
variables outside `S`. Use the existing quotient-dimension / equidimensionality API
already present in the repo when possible.

Prefer a direct theorem tailored to this setting over a large new dimension API.

### Step 3: package the BEI-side consequence

Once equal-cardinality of minimal covers is proved and the dimension conversion is in
place, prove the corresponding equidimensionality / local CM statement for
`bipartiteEdgeMonomialIdeal G`.

This should be the theorem that leaves only the final initial-ideal transfer step.


## Good theorem shapes

Names are suggestions only:

```lean
theorem hhEdgeSet_minimalVertexCover_card_eq
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G)
    {S T : Set (BinomialEdgeVars (Fin n))} :
    MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S →
    MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) T →
    S.encard = T.encard := by
  ...

theorem bipartiteEdgeMonomialIdeal_isCM
    {n : ℕ} (G : SimpleGraph (Fin n))
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsCohenMacaulay
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) := by
  ...
```

If `encard` is awkward, a finite-cardinality formulation with `Finset` or `Nat.card`
is fine. Choose the smallest clean packaging that works with the existing quotient
dimension lemmas.


## False routes / cautions

- Do not reopen the variable-pair bridge packet. It is done.
- Do not spend the round on the final CM transfer back to `J_G` unless the
  equidimensionality theorem is already secured.
- Do not build a huge abstract HH-graph framework unless the proof genuinely needs it.
- Do not abandon the paper-faithful route in favor of a totally unrelated direct proof
  of Proposition 1.6.
- Do not overclaim full Proposition 1.6 until the final transfer theorem is handled.


## Definition of done

Best outcome:

- equal-size theorem for minimal vertex covers of `hhEdgeSet G`;
- equidimensionality / local-CM theorem for `bipartiteEdgeMonomialIdeal G`;
- `prop_1_6` reduced to only the final CM transfer from the initial ideal.

Minimum acceptable outcome:

- one substantial theorem showing the HH conditions force equal cardinality of minimal
  vertex covers, or
- the exact BEI-specific combinatorial blocker isolated in Lean terms.


## Status docs

If the equidimensionality / local-CM step lands, update:

- `TODO.md`
- `FORMALIZATION_MAP.md`

Only update `CLAUDE.md` if file structure or standing workflow guidance changes.

# Guide: Proposition 1.6 Dimension Step

## Task

Take the next concrete step in Proposition 1.6 after the HH minimal-vertex-cover
combinatorics.

The following are now proved in `BEI/CohenMacaulay.lean`:

- `hhEdgeSet`
- `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`
- `minimalPrime_bipartiteEdgeMonomialIdeal_iff`
- `hhEdgeSet_diagonal`
- `minimalVertexCover_exactlyOne`
- `minimalVertexCover_subset_active`
- `minimalVertexCover_ncard_eq`

So the remaining internal gap is no longer about graph combinatorics. It is the
dimension/equidimensionality step.


## Current live state

### In `BEI/CohenMacaulay.lean`

The reduction chain now reaches:

1. `J_G` → monomial initial ideal
2. y-shift to a bipartite edge ideal
3. bridge to `MvPolynomial.variablePairIdeal`
4. minimal primes = minimal vertex covers
5. all minimal vertex covers have equal size under the HH conditions

What remains internally is:

6. convert equal cover size into equal quotient dimensions for all minimal primes
7. package the quotient by `bipartiteEdgeMonomialIdeal G` as locally
   Cohen–Macaulay / equidimensional

The final transfer

- `S / in_<(J_G)` CM → `S / J_G` CM

is still a separate last step and should not be the focus of this round.


## Exact next goal

Use the new theorem

- `minimalVertexCover_ncard_eq`

together with the minimal-prime description

- `minimalPrime_bipartiteEdgeMonomialIdeal_iff`

to prove that all minimal primes of `bipartiteEdgeMonomialIdeal G` have the same
quotient dimension.

In other words: land the actual equidimensionality theorem for the HH bipartite edge
ideal.


## Recommended route

### Step 1: isolate the dimension formula for variable ideals

The main missing bridge is probably a dimension formula of the form:

```lean
ringKrullDim (MvPolynomial σ K ⧸ Ideal.span (MvPolynomial.X '' S)) = ...
```

for finite `σ`.

You do not need the most general theorem possible unless it comes cheaply. The
BEI-specific target is enough:

- `σ = BinomialEdgeVars (Fin n)`
- compare dimensions for two sets `S` and `T` with equal cardinality

Good target shapes:

```lean
theorem ringKrullDim_quot_span_X_image_eq
    {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ringKrullDim (MvPolynomial σ K ⧸ Ideal.span (MvPolynomial.X '' S)) =
      Nat.card σ - S.ncard := by
  ...
```

or the weaker comparison-only form:

```lean
theorem ringKrullDim_quot_span_X_image_eq_of_ncard_eq
    (hST : S.ncard = T.ncard) :
    ringKrullDim (MvPolynomial σ K ⧸ Ideal.span (MvPolynomial.X '' S)) =
    ringKrullDim (MvPolynomial σ K ⧸ Ideal.span (MvPolynomial.X '' T)) := by
  ...
```

If the exact formula is easy, prefer it. If the exact formula is awkward but the
comparison theorem is easy and sufficient for Proposition 1.6, take the comparison
theorem first.

### Step 2: transport from covers to minimal primes

After the variable-ideal dimension theorem exists, combine:

- `minimalPrime_bipartiteEdgeMonomialIdeal_iff`
- `minimalVertexCover_ncard_eq`

to show that any two minimal primes of `bipartiteEdgeMonomialIdeal G` have equal
quotient dimension.

### Step 3: package the equidimensionality / local CM consequence

Use the local CM definition from `toMathlib/CohenMacaulay/Defs.lean` to prove the
BEI-side consequence for the quotient by `bipartiteEdgeMonomialIdeal G`.

That theorem should leave only the final initial-ideal transfer gap in `prop_1_6`.


## Important cautions

- Do not reopen the already-finished HH cover-combinatorics packet.
- Do not spend the round on the final CM transfer back from `in_<(J_G)` to `J_G`
  unless the dimension step is already secured.
- Do not build a huge abstract commutative-algebra tower if a direct theorem about
  quotients by variable ideals is enough.
- Stay close to what Proposition 1.6 actually needs.


## Definition of done

Best outcome:

- a usable dimension theorem for quotients by variable ideals;
- an equidimensionality theorem for `bipartiteEdgeMonomialIdeal G` under HH conditions;
- `prop_1_6` reduced to only the final CM-transfer step.

Minimum acceptable outcome:

- the dimension comparison theorem for variable ideals, or
- the exact Lean blocker isolated for that step.


## Status docs

If the equidimensionality theorem lands, update:

- `TODO.md`
- `FORMALIZATION_MAP.md`

Only update `CLAUDE.md` if file structure or standing workflow guidance changes.

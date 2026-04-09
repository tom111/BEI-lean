# Guide: Proposition 1.6 CM Transfer Step

## Status

This is the secondary paper-faithful track.

It is not the active next packet now that the direct equidimensional surrogate route is
finished.

Only work on this guide if explicitly assigned to the transfer/backport route.

## Task

This is the remaining paper-faithful algebra packet for Proposition 1.6.

Everything internal to the BEI reduction is now proved:

- the initial ideal description for closed graphs;
- the y-shift to the bipartite edge ideal;
- the bridge to `variablePairIdeal`;
- minimal primes = minimal vertex covers;
- equal cardinality of minimal vertex covers under the Herzog–Hibi conditions;
- the dimension step;
- the local equidimensional surrogate statement for the bipartite edge ideal.

The remaining gap on the paper-style code path is the standard
Gröbner-basis transfer theorem

- `S / in_<(I)` Cohen–Macaulay → `S / I` Cohen–Macaulay.


## Current live state

### In `BEI/Equidim.lean`

The theorems

- `bipartiteEdgeMonomialIdeal_isEquidim`
- `monomialInitialIdeal_isEquidim`

are proved.

However, the direct equidimensional route now exists separately in
`BEI/PrimeDecompositionDimension.lean`, and already closes the local surrogate theorem.
So this file is now strictly about the remaining paper-faithful CM track.

### In `toMathlib/HeightVariableIdeal.lean`

The variable-ideal quotient equivalence and dimension formulas are proved:

- `ker_killS_eq_span_X_image`
- `killS_surjective`
- `quotientSpanXEquiv`
- `MvPolynomial.ringKrullDim_quotient_span_X_image`
- `MvPolynomial.ringKrullDim_quotient_span_X_eq_of_card_eq`

### In `toMathlib/Equidim/Defs.lean`

The local working notion used in the current repo is equidimensionality. That is not the
full depth-based Cohen–Macaulay theory from the paper.


## Exact next goal

Formalize a transfer theorem strong enough to justify the final step of the paper:

```text
if the quotient by the initial ideal is Cohen–Macaulay,
then the quotient by the original ideal is Cohen–Macaulay.
```

For the current project, it is acceptable if the theorem is stated only in the scope
actually needed for the paper-faithful Proposition 1.6 route, rather than as the most
general possible upstream result, provided the statement is mathematically honest.

Important scope note:

- proving this theorem would restore the paper-style reduction in code;
- but the repo would still need real depth-based CM foundations, not just the local
  equidimensional surrogate names, before claiming the paper’s full CM statement.


## Recommended strategy

### Step 1: separate the paper theorem from the local surrogate

Do not try to prove a transfer theorem for the local equidimensional surrogate and then
present it as the paper's theorem. The actual target here is the paper's depth-based
Cohen–Macaulay transfer statement.

Read:

- `/home/tom/BEI-lean/toMathlib/Equidim/Defs.lean`

only so you stay clear on what the repo currently has and what it still lacks.

### Step 2: look for the smallest truthful transfer theorem

The ideal theorem may need to be narrower than the classical statement. Good outcomes:

- a theorem directly for polynomial quotients under the monomial order already used in
  this project;
- or, if necessary, a theorem reducing the transfer to a more standard known algebraic
  result that can be isolated clearly.

Do not overstate what has been formalized if the theorem only covers the current BEI
setting.

### Step 3: reconnect to the paper-style route

Once a truthful transfer theorem is available, use the already-proved

- `initialIdeal_closed_eq`
- `rename_yPredVar_monomialInitialIdeal`
- `bipartiteEdgeMonomialIdeal_isEquidim`
- `monomialInitialIdeal_isEquidim`

as the already-formalized surrogate side data, while keeping clear that the missing
piece is now genuine CM infrastructure.


## Important cautions

- This is the one place where it may be necessary to formalize a genuinely external
  commutative-algebra theorem. Do not pretend it is already in Mathlib if it is not.
- Prefer the smallest theorem that honestly closes the current project.
- Do not reopen the graph-combinatorial or dimension packets; they are done.
- If the transfer theorem turns out to require more serious infrastructure than fits in
  one round, isolate that precisely instead of masking it with broad status prose.


## Definition of done

Best outcome:

- a usable CM transfer theorem from `in_<(I)` to `I`;
- the paper-style Proposition 1.6 route reduced to whatever real CM foundation still
  remains missing.

Minimum acceptable outcome:

- the exact correct statement for the transfer theorem is pinned down in Lean terms;
- one substantial supporting lemma or reduction is proved;
- the remaining blocker is isolated precisely.


## Status docs

If this route lands, update:

- `TODO.md`
- `FORMALIZATION_MAP.md`
- `CLAUDE.md`
- public `docs/` pages to distinguish clearly between:
  - finishing Proposition 1.6 under the local surrogate, and
  - fully formalizing the paper’s depth-based CM statement

# Guide: Proposition 1.6 CM Transfer Step

## Task

This is the final remaining packet for Proposition 1.6.

Everything internal to the BEI reduction is now proved:

- the initial ideal description for closed graphs;
- the y-shift to the bipartite edge ideal;
- the bridge to `variablePairIdeal`;
- minimal primes = minimal vertex covers;
- equal cardinality of minimal vertex covers under the Herzog–Hibi conditions;
- the dimension step;
- the local Cohen–Macaulay / equidimensionality statement for the bipartite edge ideal.

The only remaining gap is the standard Gröbner-basis transfer theorem

- `S / in_<(I)` Cohen–Macaulay → `S / I` Cohen–Macaulay.


## Current live state

### In `BEI/CohenMacaulay.lean`

The theorem

- `bipartiteEdgeMonomialIdeal_isCohenMacaulay`

is proved, and `prop_1_6` is now reduced to the final transfer step.

### In `toMathlib/HeightVariableIdeal.lean`

The variable-ideal quotient equivalence and dimension formulas are proved:

- `ker_killS_eq_span_X_image`
- `killS_surjective`
- `quotientSpanXEquiv`
- `MvPolynomial.ringKrullDim_quotient_span_X_image`
- `MvPolynomial.ringKrullDim_quotient_span_X_eq_of_card_eq`

### In `toMathlib/CohenMacaulay/Defs.lean`

The local working notion of Cohen–Macaulayness is the equidimensionality-style one used
throughout the current CM branch.


## Exact next goal

Formalize a transfer theorem strong enough to justify the final step of the paper:

```text
if the quotient by the initial ideal is Cohen–Macaulay,
then the quotient by the original ideal is Cohen–Macaulay.
```

For the current project, it is acceptable if the theorem is stated only in the scope
actually needed for `prop_1_6`, rather than as the most general possible upstream
result, provided the statement is mathematically honest.


## Recommended strategy

### Step 1: inspect what the local CM definition really needs

Because local `IsCohenMacaulay` is an equidimensionality-style condition, the transfer
theorem may not need the full classical depth machinery as stated in textbooks.

Read:

- `/home/tom/BEI-lean/toMathlib/CohenMacaulay/Defs.lean`

and determine what exact property must be transferred from `in_<(I)` to `I`.

### Step 2: look for the smallest truthful transfer theorem

The ideal theorem may need to be narrower than the classical statement. Good outcomes:

- a theorem directly for polynomial quotients under the monomial order already used in
  this project;
- a theorem formulated for the local equidimensionality-style CM notion;
- or, if necessary, a theorem reducing the transfer to a more standard known algebraic
  result that can be isolated clearly.

Do not overstate what has been formalized if the theorem only covers the current BEI
setting.

### Step 3: close `prop_1_6`

Once the transfer theorem is available, use the already-proved

- `initialIdeal_closed_eq`
- `rename_yPredVar_monomialInitialIdeal`
- `bipartiteEdgeMonomialIdeal_isCohenMacaulay`

to finish `prop_1_6`.


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
- `prop_1_6` fully proved.

Minimum acceptable outcome:

- the exact correct statement for the transfer theorem is pinned down in Lean terms;
- one substantial supporting lemma or reduction is proved;
- the remaining blocker is isolated precisely.


## Status docs

If `prop_1_6` lands, update:

- `TODO.md`
- `FORMALIZATION_MAP.md`
- `CLAUDE.md`
- public `docs/` pages that still say one theorem remains open

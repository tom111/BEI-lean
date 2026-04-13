# Guide: Real Cohen-Macaulay Track for Proposition 1.6

## Task

This is the remaining paper-faithful algebra track for Proposition 1.6.

Everything internal to the BEI reduction is now proved:

- the initial ideal description for closed graphs;
- the y-shift to the bipartite edge ideal;
- the bridge to `variablePairIdeal`;
- minimal primes = minimal vertex covers;
- equal cardinality of minimal vertex covers under the Herzog–Hibi conditions;
- the dimension step;
- the local equidimensional surrogate statement for the bipartite edge ideal.

The remaining paper-level gaps are:

1. package the finished HH regularity infrastructure into a genuine
   Herzog–Hibi bipartite Cohen–Macaulay theorem for the graph `Γ`;
2. formalize a Gröbner-basis transfer theorem strong enough for Proposition 1.6.


## Current live state

### In `BEI/Equidim.lean`

The theorems

- `bipartiteEdgeMonomialIdeal_isEquidim`
- `monomialInitialIdeal_isEquidim`
- `sum_XY_isSMulRegular_mod_diagonalSum`
- `bipartiteEdgeMonomialIdeal_isWeaklyRegular`
- `ringKrullDim_bipartiteEdgeMonomialIdeal`

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

### In the current repo

The local working notion used in the current repo is equidimensionality. That is not the
full depth-based Cohen–Macaulay theory from the paper. The surrogate theorem
`prop_1_6_equidim` is already done and is not the target of this guide.


## Exact next goal

Bring in real Cohen–Macaulay foundations far enough to support the final step of the paper:

```text
if the quotient by the initial ideal is Cohen–Macaulay,
then the quotient by the original ideal is Cohen–Macaulay.
```

This should be approached in two layers:

1. real CM foundations in a dedicated `toMathlib/CohenMacaulay/` area;
2. an HH-side theorem that turns the completed regularity infrastructure into a
   genuine CM conclusion;
3. then the smallest truthful transfer theorem actually needed for Proposition 1.6.

Important scope note:

- do not prove a theorem only for the local equidimensional surrogate and present it as
  the paper's CM statement;
- the goal here is genuine CM infrastructure, not further work on the surrogate branch.


## Recommended strategy

### Step 1: keep the CM backport track separate

The real CM foundation work in

- `toMathlib/CohenMacaulay/Defs.lean`
- `toMathlib/CohenMacaulay/Basic.lean`

is useful and should continue as a separate supporting track.

However, the missing forward depth inequality for regular quotients is only one
possible support theorem for this route; it should not be confused with the
whole remaining Proposition 1.6 gap by itself.

That packet now lives as supporting infrastructure in:

- [cm_pr_26218/BASIC_FORWARD_DEPTH.md](cm_pr_26218/BASIC_FORWARD_DEPTH.md)

### Step 2: target the two paper-critical theorems directly

The actual remaining paper route consists of two isolated gaps:

1. HH bipartite CM:
   use the completed weakly-regular-sequence theorem and the proved dimension
   formula to show that the quotient by the bipartite edge ideal is genuinely
   Cohen–Macaulay under the Herzog–Hibi conditions;
2. Gröbner transfer:
   prove that Cohen–Macaulayness transfers from the initial ideal quotient back
   to the original ideal quotient.

The HH-side packet now lives concretely in:

- [HH_CM_TO_GLOBAL.md](HH_CM_TO_GLOBAL.md)
- [GRADED_CM_LOCAL_TO_GLOBAL.md](GRADED_CM_LOCAL_TO_GLOBAL.md)

Most of the old internal HH blockers are now closed:

1. free-variable NZD for `x_{n-1}` and `y_{n-1}`: DONE;
2. extension of the regular sequence from length `n - 1` to `n + 1 = dim`: DONE;
3. local CM at the irrelevant / augmentation ideal: DONE;
4. CM-localization backport: DONE.

The remaining HH-side internal blocker is now:

5. a graded local-to-global CM step turning augmentation-ideal CM into a
   genuine global `IsCohenMacaulayRing` theorem for the HH quotient.

The Gröbner-transfer gap should be treated as its own theorem packet:

- [GROEBNER_CM_TRANSFER.md](GROEBNER_CM_TRANSFER.md)

### Step 3: look for the smallest truthful theorem in each gap

The ideal theorem may need to be narrower than the classical statement. Good outcomes:

- a theorem directly for polynomial quotients under the monomial order already used in
  this project;
- or, if necessary, a theorem reducing the transfer to a more standard known algebraic
  result that can be isolated clearly.

Do not overstate what has been formalized if the theorem only covers the current BEI
setting.

### Step 4: reconnect to the paper-style route

Once real CM foundations and a truthful transfer theorem are available, use the
already-proved

- `initialIdeal_closed_eq`
- `rename_yPredVar_monomialInitialIdeal`
- `bipartiteEdgeMonomialIdeal_isEquidim`
- `monomialInitialIdeal_isEquidim`

as algebraic setup while keeping clear that the paper theorem is now being proved with
genuine CM foundations.


## Important cautions

- This is the one place where it may be necessary to formalize genuinely external
  commutative-algebra infrastructure. Do not pretend it is already in Mathlib if it is not.
- Do not confuse the general CM backport track with the immediate Proposition 1.6
  critical path.
- Prefer the smallest theorem that honestly closes the current project.
- Do not reopen the graph-combinatorial or dimension packets; they are done.
- If the transfer theorem turns out to require more serious infrastructure than fits in
  one round, isolate that precisely instead of masking it with broad status prose.


## Definition of done

Best outcome:

- real CM foundations imported/backported into the repo;
- a usable CM transfer theorem from `in_<(I)` to `I`;
- the paper-style Proposition 1.6 route proved honestly.

Minimum acceptable outcome:

- the exact real-CM slice needed from PR `#26218` is identified;
- one substantial imported/backported foundation theorem is landed;
- the remaining blocker is isolated precisely.


## Status docs

If this route lands, update:

- `TODO.md`
- `FORMALIZATION_MAP.md`
- `CLAUDE.md`
- public `docs/` pages to distinguish clearly between:
  - the finished equidimensional surrogate track, and
  - the real Cohen–Macaulay track

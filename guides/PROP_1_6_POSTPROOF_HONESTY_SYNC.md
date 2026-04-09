# Guide: Post-Proof Honesty Sync for Proposition 1.6

## Purpose

This guide is **not** the active next packet while `BEI/PrimeDecompositionDimension.lean`
is still under live theorem work.

Use it only **after** the direct equidimensional Prop. 1.6 proof has either:

- landed cleanly, or
- been explicitly abandoned for the current round.

Its job is to keep the repository honest once the proof state is stable.


## Scope

This guide has two phases.

### Phase 1. Status sync

Correct the status files so they match the live Lean code exactly.

### Phase 2. Naming / wording refactor

Rename or reword the local CM-surrogate layer so the repo stops overclaiming
depth-based Cohen-Macaulay formalization.

Do **not** run Phase 2 in the middle of live theorem work.


## Why this guide exists

The repository currently has stale status claims because earlier reports said the direct
equidimensional Prop. 1.6 route was finished, but the live code later reintroduced
`sorry`s in `BEI/PrimeDecompositionDimension.lean`.

So the theorem layer, status files, and public explanation are temporarily out of sync.


## Phase 1: status sync checklist

Once the proof state is stable, check these first:

- `/home/tom/BEI-lean/FORMALIZATION_MAP.md`
- `/home/tom/BEI-lean/TODO.md`
- `/home/tom/BEI-lean/CLAUDE.md`
- `/home/tom/BEI-lean/OVERVIEW.md`

### Known stale claims from the last audit

These were wrong at the time of writing this guide and should be rechecked against the
code before editing:

1. `FORMALIZATION_MAP.md`
   - Proposition 1.6 marked `Proved`
   - notes claiming direct proof with `0 sorries`
   - note claiming `SatisfiesProp1_6Condition` is unused

2. `TODO.md`
   - Prop. 1.6 marked `[x] proved via direct equidimensionality (0 sorries)`
   - `prop_1_6` described as already proved directly
   - active-sorry table listing only `cm_transfer_initialIdeal`
   - stale references to deleted or demoted Prop. 1.6 guides

3. `CLAUDE.md`
   - still describing the Proposition 1.6 branch as reduced to the final
     `cm_transfer_initialIdeal` transfer step

4. `OVERVIEW.md`
   - still describing the only active paper endpoint as Proposition 1.6 without
     reflecting the direct-route `sorry` location accurately

### Editing rule

Do not guess. Before editing, inspect:

- `/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean`
- `/home/tom/BEI-lean/BEI/CohenMacaulay.lean`
- current `sorry` locations

Then label Proposition 1.6 honestly as one of:

- `Proved`
- `Partial`
- `Sorry`
- `Blocked`

according to the actual live state.


## Phase 2: naming / wording refactor

This phase is about honesty, not new mathematics.

The repo currently uses names like `IsCohenMacaulayRing` for a local equidimensional
surrogate. That is useful internally, but it overpromises if presented as the paper’s
full depth-based Cohen-Macaulay theory.

### Recommended order

1. fix status files first
2. decide the target naming scheme
3. rename the code/API layer
4. then sync docs/guides/public pages

### Likely rename targets

Core definitions and theorems:

- `IsCohenMacaulayRing`
- `IsCohenMacaulay`
- `isCohenMacaulay_of_equidim_minimalPrimes`
- `isCohenMacaulay_of_ringEquiv`

Examples and consequences:

- `complete_is_CM`
- `path_is_CM`
- `corollary_3_7_CM`
- `bipartiteEdgeMonomialIdeal_isCohenMacaulay`
- `monomialInitialIdeal_isCohenMacaulay`

Files and module wording:

- `BEI/CohenMacaulay.lean`
- `toMathlib/CohenMacaulay/Defs.lean`

Status/docs wording:

- `TODO.md`
- `FORMALIZATION_MAP.md`
- `CLAUDE.md`
- `README.md`
- `OVERVIEW.md`
- `docs/`
- `guides/`

### Caution

This is a cross-repo rename and wording pass. It should have one owner and should not be
done in parallel with live theorem work.


## Public wording target

The public-facing description should say:

- Proposition 1.6 is not fully formalized until the remaining proof gap is closed.
- The current repo also studies an equidimensional variant.
- Full depth-based Cohen-Macaulay formalization still depends on newer Mathlib or a
  backport, with Mathlib PR `#26218` as the main current reference.

Do not describe the equidimensional surrogate as if it were already the paper’s CM
theorem.


## Integration note

Even if the direct Prop. 1.6 proof lands in
`BEI/PrimeDecompositionDimension.lean`, the main library entry file

- `/home/tom/BEI-lean/BEI.lean`

currently imports `BEI/CohenMacaulay.lean` but not `BEI/PrimeDecompositionDimension.lean`.

So after the proof stabilizes, also decide whether the direct route should become part of
the main import path.


## Definition of done

Best outcome:

- all stale status claims corrected
- naming/writing no longer overclaims CM
- public docs and internal guides clearly distinguish:
  - the equidimensional surrogate route
  - the future full CM route

Minimum acceptable outcome:

- status files corrected
- rename plan pinned down precisely, even if the actual refactor is deferred

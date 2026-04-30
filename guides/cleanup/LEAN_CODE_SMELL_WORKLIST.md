# Lean Code Smell Worklist

## Preserved task

The current task is to convert the repo scan for expensive or brittle Lean code into a
short concrete worklist.

This file is the execution-oriented companion to `LEAN_CODE_SMELL_AUDIT.md`.

## Scope

This is a **cleanup queue**, not theorem development.

The goal is to reduce build cost and proof brittleness by:

- shrinking large declarations;
- extracting repeated helper lemmas;
- reducing avoidable instance-search and unfolding pressure; and
- making the remaining heartbeat raises measured and explainable.

## Immediate queue

### 1. `BEI/Equidim/IteratedRegularity.lean` and the residual hub — DONE 2026-04-30

The two giant declarations have been carved:

- `nilradical_nzd_map_diagSubstHom` (was 589 LOC) → thin dispatcher
  (~66 LOC) plus three private case helpers
  (`caseB`/`caseC`/`caseD_nilradical_nzd_map_diagSubstHom_helper`).
- `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
  (was 290 LOC) → thin dispatcher (~52 LOC) plus `cm_F2_route` (~250 LOC).

All seven flagship axiom checks remain
`[propext, Classical.choice, Quot.sound]`. Full record in
[archive/EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/archive/EQUIDIM_GIANT_CARVING.md).

The remaining residual structural item is the ~354-LOC Case D helper.
It can be sub-decomposed along the natural seams (Finsupp coefficient
bookkeeping, generator analysis, HH transitivity contradiction) but
the signature-plumbing cost was judged not worth the marginal clarity
gain at carving time. Tracked as a stand-alone bullet in
[`TODO.md`](/home/tom/BEI-lean/TODO.md).

### 2. `BEI/PrimeIdeals.lean`

Why second:

- explicit expensive-unfolding note already in the source;
- overlaps with existing evaluation-map cleanup work;
- the heartbeat raises are gone after the 2026-04-27 audit, but the
  structural cost remains.

Concrete tasks:

1. Profile the declarations near the `aeval_X unfolding is expensive` comment.
2. Extract reusable evaluation-map and kernel-containment helpers.
3. Extract witness-computation lemmas so the contradiction pattern is not rebuilt inline.

Done when:

- the repeated `aeval` pattern appears as named lemmas;
- the file's elaboration cost is meaningfully reduced (measure with
  `#count_heartbeats`).

### 3. `BEI/CoveredWalks.lean` and `BEI/PrimeDecompositionDimension.lean`

Why together:

- both are large;
- both look dominated by repeated path/counting arithmetic;
- helper extraction in one should likely pay off in the other.

Concrete tasks:

1. Search for repeated endpoint, support-membership, and path-length subproofs.
2. Move shared path/counting lemmas into the smallest reasonable helper layer.
3. Replace repeated `omega` tails with named lemmas where the same shape occurs multiple
   times.
4. Re-evaluate whether either file should split after the helper layer is present.

Done when:

- the repeated arithmetic patterns have names;
- the long theorem bodies mostly assemble named facts instead of rebuilding them.

### 4. `BEI/GroebnerBasisSPolynomial.lean`

Why now:

- large file;
- high automation count;
- likely repeated `split_ifs` plus arithmetic closure patterns.

Concrete tasks:

1. Identify the most repeated `split_ifs`/arithmetic endings.
2. Extract normalization lemmas for those endings.
3. Re-measure the one heartbeat-raised declaration after the helper cleanup.

Done when:

- the file has fewer repeated local arithmetic scripts;
- the remaining raised declaration is justified by measurement rather than inertia.

### 5. `toMathlib/CohenMacaulay/Polynomial.lean`

Why before secondary BEI files:

- shared support file;
- downstream files pay for its cost.

Concrete tasks:

1. Profile the single remaining raised declaration (was 5 raises before
   the 2026-04-27 audit).
2. Separate stable support lemmas from large theorem bodies when imports allow it.
3. Keep the public support API stable while reducing the rebuild radius.

Done when:

- the remaining raised declaration is simplified or moved to a thinner dependency layer.

## Secondary queue

- `BEI/ClosedGraphs.lean`
  Heartbeat raises gone after the 2026-04-27 audit; revisit only if a new
  pressure point appears.
- `BEI/GroebnerDeformation.lean`
  Heartbeat raises gone after the 2026-04-27 audit; large file but no
  immediate pressure point.
- `BEI/CycleUnmixed.lean`
  The dedicated `MINIMALPRIMES_CYCLE_PERFORMANCE.md` packet is complete and archived;
  route any new performance work through `LEAN_PERFORMANCE_TRIAGE.md` unless a fresh packet is needed.
- `BEI/Corollary3_4.lean`
  One local raise survives (around `beQuotientGrading_isGradedRing`); was
  tested at the default 200k and proved necessary, so leave in place.

## Working rules

1. Measure first. Use profiler output and `#count_heartbeats`.
2. Prefer helper extraction over tactic golfing.
3. Prefer mathematical seams over arbitrary file splitting.
4. Keep theorem statements and public names stable unless explicitly asked otherwise.
5. When a smell already has a dedicated packet, work there instead of duplicating notes.

## Deliverable format

Each completed item in this worklist should leave behind:

1. the declarations that were measured;
2. the main cost that was identified;
3. the helper or file-structure refactor that was made; and
4. the resulting heartbeat or build improvement.

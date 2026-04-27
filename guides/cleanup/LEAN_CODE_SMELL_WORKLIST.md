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

### 1. `BEI/Equidim/IteratedRegularity.lean` and the residual hub

Why first:

- the equidim file split landed 2026-04-27, and the next pass is the
  Phase 4 carving of the two remaining giant declarations;
- the audit-driven heartbeat reductions have already taken every easy
  win — the next perf gain has to come from proof-shape changes inside
  these two giants.

Concrete tasks:

1. Carve `BEI/Equidim/IteratedRegularity.lean::nilradical_nzd_map_diagSubstHom`
   (589 LOC) along its 4-case structure (A/B/C/D) into named private helpers
   ≤ 150 LOC each. Cases B and C are near-mirror; consider a single
   parameterised helper.
2. Carve
   `BEI/Equidim.lean::isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
   (290 LOC) by extracting the F2-route branch into a private helper; the
   in-`augIdeal` branch is short enough to leave inline.
3. After each carving, run the axiom check on the paper-facing theorems to
   confirm `[propext, Classical.choice, Quot.sound]` is unchanged.

The full plan and the natural sub-helper boundaries are in
[EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_GIANT_CARVING.md).

Done when:

- no single declaration in the equidim subtree exceeds ~200 LOC;
- axiom checks on `proposition_1_6`, `monomialInitialIdeal_isCohenMacaulay`,
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`,
  `prop_1_6_herzogHibi`, `corollary_3_4`, `corollary_3_4_connected`,
  `corollary_3_7_cm_fin` are all unchanged.

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

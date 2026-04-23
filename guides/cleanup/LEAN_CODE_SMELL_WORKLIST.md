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

### 1. `BEI/Equidim.lean`

Why first:

- largest file in the repo;
- highest number of heartbeat raises;
- only hotspot with repeated `synthInstance.maxHeartbeats`.

Concrete tasks:

1. Profile the declarations around lines `3712`, `3828`, `6539`, `6580`, `8152`, and
   `8154`.
2. Identify repeated inferred structures and bind them explicitly with `letI` or named
   local terms.
3. Extract any stable helper layer that is reused across the high-heartbeat declarations.
4. Propose one mathematically coherent file split and validate it with `#min_imports`.

Done when:

- the file has a documented split seam or a documented reason not to split yet;
- the instance-search hotspots have measured profiler evidence;
- at least one raise is removed or reduced for measured reasons.

### 2. `BEI/PrimeIdeals.lean`

Why second:

- largest single heartbeat caps in the repo;
- explicit expensive-unfolding note already in the source;
- overlaps with existing evaluation-map cleanup work.

Concrete tasks:

1. Profile the declarations at lines `140`, `786`, `882`, and `1075`.
2. Extract reusable evaluation-map and kernel-containment helpers.
3. Extract witness-computation lemmas so the contradiction pattern is not rebuilt inline.
4. Recheck the declarations at lines `1465`, `1553`, `1590`, and `1626` after the helper
   layer exists.

Done when:

- the repeated `aeval` pattern appears as named lemmas;
- the three `2000000` caps have either dropped or have profiler-backed justification.

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

1. Profile the raised declarations at lines `251`, `635`, `1282`, `1392`, and `1563`.
2. Separate stable support lemmas from large theorem bodies when imports allow it.
3. Keep the public support API stable while reducing the rebuild radius.

Done when:

- at least one raised declaration is simplified or moved to a thinner dependency layer.

## Secondary queue

- `BEI/ClosedGraphs.lean`
  Treat as a local decomposition pass after the top five items.
- `BEI/GroebnerDeformation.lean`
  Profile the three raised declarations before any larger cleanup plan.
- `BEI/CycleUnmixed.lean`
  Continue under `MINIMALPRIMES_CYCLE_PERFORMANCE.md`, not in a separate packet.
- `BEI/Corollary3_4.lean`
  Low priority unless the single local raise survives broader support cleanup.

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

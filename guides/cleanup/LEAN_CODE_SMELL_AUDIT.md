# Lean Code Smell Audit

## Preserved task

The current task is to search the repo for hallmarks of expensive or brittle Lean code
and turn the results into a concrete cleanup guide.

This packet records the current repo scan and converts it into a prioritized cleanup map.

## Scope

This is a **cleanup and proof-engineering packet**, not theorem development.

It focuses on four concrete smell classes:

- oversized files with too many unrelated responsibilities;
- declarations that require raised `maxHeartbeats` or `synthInstance.maxHeartbeats`;
- automation-heavy files where arithmetic or case-splitting is repeated many times;
- brittle proof shapers such as repeated `convert`.

It does **not** authorize:

- theorem statement changes;
- new mathematical claims;
- broad rewrites without measurement.

## Repo snapshot (2026-04-23)

The following scans were taken across `BEI/`, `toMathlib/`, and `Supplement/`.

### Heartbeat snapshot

- total heartbeat overrides: `37`
- affected files: `8`
- worst file by count: `BEI/Equidim.lean` with `12`
- next: `BEI/PrimeIdeals.lean` with `8`
- next: `BEI/ClosedGraphs.lean` and `toMathlib/CohenMacaulay/Polynomial.lean` with `5`
- largest current single raises: `BEI/PrimeIdeals.lean` at `2000000`
- current cycle hotspot after the split: `BEI/CycleUnmixed.lean` at `800000`

### Largest Lean files

- `BEI/Equidim.lean` — `8489` lines
- `BEI/CoveredWalks.lean` — `2671` lines
- `BEI/GroebnerDeformation.lean` — `2232` lines
- `BEI/PrimeDecompositionDimension.lean` — `2093` lines
- `BEI/PrimeIdeals.lean` — `2007` lines
- `BEI/GroebnerBasisSPolynomial.lean` — `1963` lines
- `toMathlib/GradedFiniteFree.lean` — `1775` lines
- `toMathlib/CohenMacaulay/Polynomial.lean` — `1652` lines

### Automation-heavy files

The following counts come from searching for
`omega|linarith|ring_nf|aesop|grind`. These counts are not bugs by themselves,
but they are a useful signal when combined with file size or heartbeat raises.

- `BEI/Equidim.lean` — `212`
- `BEI/GroebnerBasisSPolynomial.lean` — `99`
- `BEI/CoveredWalks.lean` — `79`
- `BEI/PrimeDecompositionDimension.lean` — `73`
- `BEI/GraphProperties.lean` — `62`
- `BEI/PrimeIdeals.lean` — `40`
- `toMathlib/HeightDeterminantal.lean` — `40`

### `convert`-heavy files

- `BEI/Equidim.lean` — `7`
- `BEI/PrimeIdeals.lean` — `4`
- `BEI/PrimeDecomposition.lean` — `2`
- `toMathlib/CohenMacaulay/Localization.lean` — `2`
- `toMathlib/GradedFiniteFree.lean` — `2`

## What the scan says

The repo does **not** have one single performance problem.

Instead it has three different cleanup classes:

1. **Structural hotspots**
   Large files that combine public theorems, support lemmas, and expensive local proof
   machinery. These should be split or decomposed first.
2. **Automation hotspots**
   Files where many similar arithmetic or case-splitting steps are rebuilt over and over.
   These need helper lemmas and small proof APIs, not just higher heartbeat caps.
3. **Shared support hotspots**
   Imported support files whose raised heartbeats affect many downstream rebuilds.
   These need especially careful profiling because their cost propagates widely.

## Priority files

### Tier 1: Structural and heartbeat hotspots

#### `BEI/Equidim.lean`

Evidence:

- `8489` lines
- `12` heartbeat overrides
- `3` `synthInstance.maxHeartbeats` sites
- `212` heavy-automation hits
- `7` `convert` hits

Diagnosis:

- This is the strongest sign of a file-boundary problem in the repo.
- The file is large enough that even correct local proofs are likely paying a rebuild tax.
- The instance-search raises mean this is not only a tactic-automation issue.

Concrete next move:

- profile the declarations around lines `3712`, `3828`, `6539`, `6580`, `8152`, and
  `8154`;
- bind repeated inferred instances explicitly with `letI` or named local terms;
- split the file at a mathematically stable seam before doing micro-optimizations.

#### `BEI/PrimeIdeals.lean`

Evidence:

- `2007` lines
- `8` heartbeat overrides
- three `2000000` caps at lines `786`, `882`, and `1075`
- `40` heavy-automation hits
- `4` `convert` hits
- explicit comment at line `140`:
  `aeval_X unfolding is expensive`

Diagnosis:

- This is the clearest evaluation-map and unfolding hotspot in the repo.
- The large caps suggest expensive declarations, not just mild local friction.

Concrete next move:

- profile the declarations at lines `140`, `786`, `882`, and `1075` first;
- extract evaluation and kernel-containment helpers so the expensive `aeval` pattern is
  not rebuilt repeatedly;
- normalize witness-computation lemmas before touching theorem statements.

#### `toMathlib/CohenMacaulay/Polynomial.lean`

Evidence:

- `1652` lines
- `5` heartbeat overrides
- shared support file imported by multiple downstream results

Diagnosis:

- A heavy support file is more expensive than a heavy endpoint file because many rebuilds
  pay for it.

Concrete next move:

- profile the raised declarations at lines `251`, `635`, `1282`, `1392`, and `1563`;
- separate stable support lemmas from large theorem bodies if imports allow it;
- keep shared API declarations in the thinnest file that works.

### Tier 2: Large automation hotspots without major heartbeat evidence yet

#### `BEI/CoveredWalks.lean`

Evidence:

- `2671` lines
- `79` heavy-automation hits
- one of the largest files in the repo

Diagnosis:

- This is likely a repeated arithmetic and path-manipulation file rather than a single
  declaration hotspot.
- It is a likely source of slow elaboration even without many explicit heartbeat raises.

Concrete next move:

- search for repeated path-length and support-membership arguments;
- extract small reusable lemmas for walk arithmetic and endpoint bookkeeping;
- reduce duplicated `omega` tails before any broad file move.

#### `BEI/PrimeDecompositionDimension.lean`

Evidence:

- `2093` lines
- `73` heavy-automation hits
- `1` `convert` hit

Diagnosis:

- This looks like a mixed structural and arithmetic-cleanup target.
- It likely shares helper needs with `CoveredWalks` and the graph API files.

Concrete next move:

- extract interval, path, and counting helper lemmas used more than once;
- move stable helper material out of long theorem bodies;
- keep the public theorem layer close to the paper while thinning the proof layer.

#### `BEI/GroebnerBasisSPolynomial.lean`

Evidence:

- `1963` lines
- `99` heavy-automation hits
- `1` heartbeat override

Diagnosis:

- This looks less like instance-search trouble and more like repeated local proof shapes,
  especially `split_ifs` and arithmetic closure.

Concrete next move:

- identify the most repeated `split_ifs` plus arithmetic endings;
- replace them with named normalization lemmas;
- remeasure the single raised declaration after helper extraction.

### Tier 3: Secondary measured cleanup targets

#### `BEI/ClosedGraphs.lean`

Evidence:

- `988` lines
- `5` heartbeat overrides

Concrete next move:

- treat this as a local theorem-decomposition pass after Tier 1 and Tier 2 work settle.

#### `BEI/GroebnerDeformation.lean`

Evidence:

- `2232` lines
- `3` heartbeat overrides
- `13` heavy-automation hits

Concrete next move:

- keep this below `Equidim` and `PrimeIdeals` in the queue;
- prefer targeted declaration profiling over premature file splitting.

#### `BEI/CycleUnmixed.lean`

Evidence:

- `507` lines
- `0` local heartbeat overrides after the completed cycle packet
- the old giant `MinimalPrimes` cycle theorem is already isolated here and now split into helper lemmas

Concrete next move:

- the dedicated cycle packet is complete and archived;
- if new pressure appears here, continue under `LEAN_PERFORMANCE_TRIAGE.md` or write a fresh packet.

## Cross-links to existing packets

The following existing guides should be reused rather than duplicated:

- `archive/MINIMALPRIMES_CYCLE_PERFORMANCE.md` for the completed `BEI/CycleUnmixed.lean` pass
- `LEAN_PERFORMANCE_TRIAGE.md` for repo-wide heartbeat measurement workflow
- `EVALUATION_MAP_API.md` for `BEI/PrimeIdeals.lean`
- `PATH_AND_INTERNAL_VERTEX_API.md` for graph/path helper extraction
- `FILE_SPLITTING_PLAN.md` and `EQUIDIM_DECOMPOSITION.md` for large-file restructuring

## Concrete acceptance criteria

This audit has been acted on successfully when:

1. the top-tier files have per-declaration profiling notes, not just guesses;
2. at least one Tier 1 file and one Tier 2 file have extracted helper APIs;
3. the remaining heartbeat raises are attached to measured declarations;
4. large-file cleanup is driven by mathematical seams, not arbitrary chopping; and
5. repeated automation patterns appear once as named lemmas instead of many times inline.

## Warnings

- Do not treat raw `omega` or `convert` counts as proof that a file is bad.
- Do not start by deleting heartbeat caps to see what breaks.
- Do not refactor public theorem statements for performance alone.
- Do not duplicate cleanup work already captured in a more specific packet.

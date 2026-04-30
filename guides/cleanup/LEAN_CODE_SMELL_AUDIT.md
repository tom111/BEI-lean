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

## Repo snapshot (2026-04-27)

The following scans were taken across `BEI/`, `toMathlib/`, and `Supplement/`.

### Heartbeat snapshot

- total heartbeat overrides: `9`
- affected files: `5`
- worst file by count: `BEI/Equidim.lean` with `4`
- next: `BEI/Equidim/L1Iso.lean` with `2`
- next: `BEI/Equidim/AugmentationLocalCM.lean`,
  `BEI/Corollary3_4.lean`, `toMathlib/CohenMacaulay/Polynomial.lean` with `1` each
- largest current single raises: `BEI/Equidim/L1Iso.lean` at `1300000` and
  `1100000` (heavy tensor-product extensionality on the L1 iso)

A repo-wide heartbeat audit landed on `master` 2026-04-27 alongside the
equidim file split. `BEI/PrimeIdeals.lean` (was 8 raises, including three at
2M) and `BEI/ClosedGraphs.lean` (was 5 raises) now use the default 200k.

### Largest Lean files

- `BEI/CoveredWalks.lean` — `2671` lines
- `BEI/Equidim/IteratedRegularity.lean` — `2404` lines
- `BEI/GroebnerDeformation.lean` — `2221` lines
- `BEI/PrimeDecompositionDimension.lean` — `2094` lines
- `BEI/PrimeIdeals.lean` — `2052` lines
- `BEI/GroebnerBasisSPolynomial.lean` — `1984` lines
- `toMathlib/GradedFiniteFree.lean` — `1773` lines
- `toMathlib/CohenMacaulay/Polynomial.lean` — `1639` lines
- `BEI/Equidim/ReducedHHLocalCM.lean` — `1236` lines
- `BEI/GroebnerAPI.lean` — `1193` lines
- `BEI/Equidim/L1Iso.lean` — `1050` lines

The 8489-line monolith `BEI/Equidim.lean` from the earlier snapshot is gone:
the equidim file split (2026-04-27) trimmed the residual hub to 713 lines and
moved the rest into 11 sibling files in `BEI/Equidim/`.

### Automation-heavy files

The following counts come from searching for
`omega|linarith|ring_nf|aesop|grind`. These counts are not bugs by themselves,
but they are a useful signal when combined with file size or heartbeat raises.
The pre-split `BEI/Equidim.lean` count (212) is now distributed across the
files in `BEI/Equidim/`; counts below should be re-scanned at the start of
the next cleanup pass.

- `BEI/GroebnerBasisSPolynomial.lean` — `99`
- `BEI/CoveredWalks.lean` — `79`
- `BEI/PrimeDecompositionDimension.lean` — `73`
- `BEI/GraphProperties.lean` — `62`
- `BEI/PrimeIdeals.lean` — `40`
- `toMathlib/HeightDeterminantal.lean` — `40`

### `convert`-heavy files

- `BEI/PrimeIdeals.lean` — `4`
- `BEI/PrimeDecomposition.lean` — `2`
- `toMathlib/CohenMacaulay/Localization.lean` — `2`
- `toMathlib/GradedFiniteFree.lean` — `2`

The pre-split `BEI/Equidim.lean` count (7) is also now distributed across
the files in `BEI/Equidim/`; rescan when starting a `convert` cleanup pass.

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

#### `BEI/Equidim/IteratedRegularity.lean`

Evidence:

- `2456` lines (post-2026-04-30 carving)
- inherits the heaviest block from the pre-split `BEI/Equidim.lean`
- the 589-LOC giant `nilradical_nzd_map_diagSubstHom` was carved on
  2026-04-30 into a thin dispatcher plus three private case helpers
  (`caseB`/`caseC`/`caseD_nilradical_nzd_map_diagSubstHom_helper`); the
  Case D helper at ~354 LOC is the largest residual block.

Diagnosis:

- File is large because the iterated-regularity infrastructure is big, not because of
  unrelated material — the equidim split already did the structural cleanup at the
  top-level seam.
- The Case D helper could still be sub-decomposed; deferred at carving
  time because the signature-plumbing cost outweighed the marginal
  clarity gain.

Concrete next move:

- if a future change exposes Case D as a real bottleneck, sub-decompose
  it along the natural seams (Finsupp coefficient bookkeeping, generator
  analysis, HH transitivity contradiction) noted in the archived
  carving guide.

#### `BEI/Equidim.lean` (residual hub) and the F2-route main theorem

Evidence:

- `731` lines after the file split and the 2026-04-30 F2-route carving.
- the 290-LOC giant
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` was
  carved into a thin dispatcher (~52 LOC) plus the private helper
  `cm_F2_route` (~250 LOC).
- the previously listed heartbeat raises moved with the heavy work onto
  `cm_F2_route`; the `E_U_algebraMap_mkI_X_pairedSurvivor_*` traces
  remain at 400k each and were tested at the default 200k and proved
  necessary.

Diagnosis:

- File is now the right size for a public theorem hub; the remaining cost is
  concentrated in the F2-route assembly.
- All raises were bisected to the smallest stable values; further
  reduction needs proof-shape changes, not heartbeat tweaks.

Concrete next move:

- nothing pressing here; revisit only if a future change reintroduces
  pressure.

#### `BEI/PrimeIdeals.lean`

Evidence:

- `2052` lines
- 0 heartbeat overrides after the 2026-04-27 audit (was 8, including three at 2M)
- `40` heavy-automation hits
- `4` `convert` hits
- explicit comment at line `140`:
  `aeval_X unfolding is expensive`

Diagnosis:

- The previous evaluation-map / unfolding hotspot has been substantially
  addressed at the heartbeat-raise level. The file is still large and a
  natural target for helper extraction.

Concrete next move:

- extract reusable evaluation-map and kernel-containment helpers so the
  expensive `aeval` pattern is not rebuilt repeatedly;
- normalize witness-computation lemmas before touching theorem statements.

#### `toMathlib/CohenMacaulay/Polynomial.lean`

Evidence:

- `1639` lines
- `1` heartbeat override (was 5; four were dropped in earlier passes)
- shared support file imported by multiple downstream results

Diagnosis:

- A heavy support file is more expensive than a heavy endpoint file because many rebuilds
  pay for it; the file is no longer a heartbeat hotspot but is still big.

Concrete next move:

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

- 0 heartbeat overrides after the 2026-04-27 audit (was 5; all dropped, the
  proofs build at the default 200k)

Concrete next move:

- nothing pressing; revisit only if a future change reintroduces a raise.

#### `BEI/GroebnerDeformation.lean`

Evidence:

- `2221` lines
- 0 heartbeat overrides after the 2026-04-27 audit (was 3)
- `13` heavy-automation hits

Concrete next move:

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
- `archive/EQUIDIM_FILE_SPLIT.md` and `archive/EQUIDIM_DECOMPOSITION.md` for the completed equidim split
- `archive/EQUIDIM_GIANT_CARVING.md` for the (now-completed) carving of the two giants
- `LEAN_PERFORMANCE_TRIAGE.md` for repo-wide heartbeat measurement workflow
- `archive/EVALUATION_MAP_API.md` for the (now-completed) eval-map contradiction API
- `PATH_AND_INTERNAL_VERTEX_API.md` for graph/path helper extraction
- `FILE_SPLITTING_PLAN.md` for the remaining non-equidim large-file restructuring

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

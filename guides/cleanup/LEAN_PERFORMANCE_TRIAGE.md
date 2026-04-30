# Lean Performance Triage Packet

## Preserved task

The current task is to convert the repo-level Lean performance research and the
file-specific `MinimalPrimes` diagnosis into concrete work packages.

This packet is the repo-level triage plan that should be used after, or alongside,
the dedicated `MinimalPrimes` cycle packet.

Status note:

- the dedicated `MINIMALPRIMES_CYCLE_PERFORMANCE.md` packet is now complete and archived;
- use this triage packet for the next repo-level performance targets.

## Scope

This is a **cleanup and performance packet**, not theorem development.

It covers:

- heartbeat reduction;
- faster local elaboration and kernel checking;
- faster rebuilds through better file boundaries and imports.

It does **not** authorize statement changes or broad theorem repackaging.

## Current repo-level snapshot (2026-04-30)

From the current heartbeat scan, after the 2026-04-27 audit and the
2026-04-30 giant carving:

- total heartbeat overrides: `8` (was `37`, then `9`).
- distribution by file:
  - `BEI/Equidim.lean` (now hosts `cm_F2_route`) — count unchanged after
    carving; the heavy `E_U_algebraMap_mkI_X_pairedSurvivor_*` traces
    moved with the proof onto the helper.
  - `BEI/Equidim/L1Iso.lean` — `2` (1300000 + 1100000, the
    tensor-product extensionality blocks).
  - `BEI/Equidim/AugmentationLocalCM.lean`, `BEI/Corollary3_4.lean`,
    `toMathlib/CohenMacaulay/Polynomial.lean` — `1` each.

Large hotspot files (post equidim split + 2026-04-30 carving):

- `BEI/CoveredWalks.lean` — `2671` lines
- `BEI/Equidim/IteratedRegularity.lean` — `2456` lines (post-carving)
- `BEI/GroebnerDeformation.lean` — `2221` lines
- `BEI/PrimeIdeals.lean` — `2052` lines
- `toMathlib/CohenMacaulay/Polynomial.lean` — `1639` lines
- `BEI/Equidim.lean` (residual hub) — `731` lines (post-carving)

## Priority order

The earlier priority list (`BEI/Equidim.lean`, `BEI/PrimeIdeals.lean`,
`BEI/ClosedGraphs.lean`, `toMathlib/CohenMacaulay/Polynomial.lean`,
`BEI/GroebnerDeformation.lean`) has been substantially addressed by the
2026-04-27 audit, the equidim file split, and the 2026-04-30 carving
of the two giants
(`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`,
`nilradical_nzd_map_diagSubstHom`). Remaining work, in order:

1. `BEI/Equidim/L1Iso.lean` — drive the two remaining
   `maxHeartbeats 1300000 / 1100000` raises lower by simplifying the
   tensor-product extensionality blocks (proof-shape change, not just
   a cap adjustment).
2. `BEI/PrimeIdeals.lean` — heartbeats already gone; the structural
   `aeval_X` evaluation-map work is now substantially done — see the
   archived `archive/EVALUATION_MAP_API.md`. Remaining: API extraction
   for the `lbMap` / `killStep` / `segreStep` family if appetite is
   there.
3. `BEI/CoveredWalks.lean` and `BEI/PrimeDecompositionDimension.lean` —
   helper extraction for the path/counting arithmetic; see
   [`PATH_AND_INTERNAL_VERTEX_API.md`](/home/tom/BEI-lean/guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md).
4. Re-profile the remaining 8 heartbeat overrides; some may be droppable
   after recent refactors. Tracked in `TODO.md`.

The two giants are now tracked as a completed packet in
[archive/EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/archive/EQUIDIM_GIANT_CARVING.md).

## Standard measurement workflow

For each hotspot declaration:

1. add temporary profiling;
2. identify the actual dominant cost;
3. refactor for that cost specifically;
4. remeasure with `#count_heartbeats`;
5. only then decide whether a heartbeat raise still belongs.

Recommended temporary instrumentation:

```lean
set_option profiler true in
set_option profiler.threshold 50 in
set_option trace.profiler.useHeartbeats true in
set_option diagnostics true in
...
```

Additional targeted tools:

- if profiling says `simp`: try `simp?` / `simpa?`, then prune to `simp only`
- if profiling says typeclass inference:
  `set_option trace.Meta.synthInstance true in`
- if profiling points at one declaration repeatedly: use `#count_heartbeats in`
- if a file split is under consideration: use `#min_imports`

## Diagnosis-to-fix map

If the measured hotspot is:

- broad `simp`:
  prune simp lemmas and replace global simp search with curated local rewrites.
- instance search:
  materialize the expensive instance with `letI` or an explicit local term.
- elaboration:
  replace `_`, add type annotations, and factor long proof terms into typed helpers.
- bad unfolding:
  first isolate the definition boundary; only then consider `seal`, `unseal`, or
  local transparency control.
- giant theorem body:
  split it into separate private lemmas before doing tactic micro-optimization.
- large rebuild radius:
  split files at stable mathematical seams and rerun `#min_imports`.

## File-specific hints

### `BEI/Equidim/IteratedRegularity.lean` and the residual hub

Primary target:

- the two giant declarations
  (`nilradical_nzd_map_diagSubstHom`, 589 LOC, and
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`, 290 LOC).

First moves:

- carve along the natural case-split boundaries described in
  [EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_GIANT_CARVING.md);
- after each helper extraction, run an axiom check on the paper-facing
  theorems to confirm `[propext, Classical.choice, Quot.sound]` is unchanged.

### `BEI/Equidim/L1Iso.lean`

Primary suspicion:

- heavy tensor-product extensionality on the L1 monomial-localisation iso

First moves:

- the `maxHeartbeats 1300000 / 1100000` raises were bisected to the smallest
  stable values; reducing further requires a proof-shape change, not a
  heartbeat tweak;
- the natural target is the algHom extensionality on pure tensors
  in `L1Forward_Backward_left` / `L1Forward_Backward_right`.

### `BEI/PrimeIdeals.lean`

Primary suspicion:

- expensive unfolding and large algebraic proof blocks (heartbeat raises
  are gone, but the structural cost remains)

First moves:

- profile declarations near the `aeval_X unfolding is expensive` comment;
- isolate the evaluation/algebra helpers into their own declarations;
- see `EVALUATION_MAP_API.md` for the helper API plan.

### `toMathlib/CohenMacaulay/Polynomial.lean`

Primary suspicion:

- imported algebraic machinery plus long support proofs in a shared file
  (heartbeat raises mostly gone; one remains)

First moves:

- profile the single remaining raised declaration;
- separate stable support lemmas from the most expensive theorem bodies if the imports
  allow it;
- keep shared API declarations in thinner files where possible.

## Deliverables

For each hotspot file, the deliverable is:

1. a short note recording which declarations were measured;
2. profiler or heartbeat evidence for the chosen refactor;
3. the refactor itself;
4. updated heartbeat counts or justification for any remaining raises.

## Acceptance criteria

This packet has made real progress when:

- the repo has fewer heartbeat raises, or materially lower ones;
- the largest hotspot files are split at mathematically stable seams;
- the remaining raises are attached to measured declarations rather than guesses;
- the work is documented file by file rather than as vague “performance cleanup”.

## Warnings

- Do not lower heartbeat caps aggressively just to make the numbers look better.
- Do not optimize based on taste alone; use profiler output.
- Do not start with global cleanup campaigns across the entire repo.
- Do not conflate build-speed cleanup with theorem-status changes.

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

## Current repo-level snapshot

From the current heartbeat scan:

- total heartbeat overrides: `37`
- worst file by count: `BEI/Equidim.lean` with `12`
- next: `BEI/PrimeIdeals.lean` with `8`
- next: `BEI/ClosedGraphs.lean` with `5`
- next: `toMathlib/CohenMacaulay/Polynomial.lean` with `5`
- next: `BEI/GroebnerDeformation.lean` with `3`
- worst single raise: `BEI/MinimalPrimes.lean` with `maxHeartbeats 4000000`

Large hotspot files:

- `BEI/Equidim.lean` — `8489` lines
- `BEI/GroebnerDeformation.lean` — `2232` lines
- `BEI/PrimeIdeals.lean` — `2007` lines
- `toMathlib/CohenMacaulay/Polynomial.lean` — `1652` lines

## Priority order

Work in this order:

1. `BEI/Equidim.lean`
   Reason: worst file by count and the only hotspot visibly using
   `synthInstance.maxHeartbeats`.
2. `BEI/PrimeIdeals.lean`
   Reason: eight overrides, explicit note that `aeval_X` unfolding is expensive,
   and likely reusable support lemmas.
3. `BEI/ClosedGraphs.lean`
   Reason: multiple local raises in a moderate-size file.
4. `toMathlib/CohenMacaulay/Polynomial.lean`
   Reason: repeated raises in a support file that is widely imported.
5. `BEI/GroebnerDeformation.lean`
   Reason: fewer raises, but still large and potentially import-heavy.

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

### `BEI/Equidim.lean`

Primary suspicion:

- repeated instance synthesis and heavy imported infrastructure

First moves:

- profile only declarations with `synthInstance.maxHeartbeats`;
- run `trace.Meta.synthInstance`;
- identify repeated local-ring / quotient / localization instances;
- bind them explicitly;
- then look for natural file-splitting seams.

### `BEI/PrimeIdeals.lean`

Primary suspicion:

- expensive unfolding and large algebraic proof blocks

First moves:

- profile declarations near the `aeval_X unfolding is expensive` comment;
- isolate the evaluation/algebra helpers into their own declarations;
- reduce repeated unfolding pressure before raising more heartbeats.

### `BEI/ClosedGraphs.lean`

Primary suspicion:

- local proof blocks that are large enough to defeat incremental reuse

First moves:

- identify the exact declarations carrying the five local raises;
- split long closure/graph-walk arguments into reusable private lemmas;
- only then test whether further simp pruning is needed.

### `toMathlib/CohenMacaulay/Polynomial.lean`

Primary suspicion:

- imported algebraic machinery plus long support proofs in a shared file

First moves:

- profile the five raised declarations individually;
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

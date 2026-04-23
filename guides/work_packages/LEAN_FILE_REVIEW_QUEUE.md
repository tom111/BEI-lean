# Work Package: File-by-File Lean Review Queue

## Origin

The TODO list under `### Lean File Review Queue` has every Lean file in
the repo flagged for a cleanup pass. As of 2026-04-23 the completed
items are:

- `BEI.lean`, `BEI/AdmissiblePaths.lean`, `BEI/CIIdeals.lean`,
  `BEI/ClosedGraphs.lean`, `BEI/Corollary3_4.lean`,
  `BEI/CoveredWalks.lean`, `BEI/Definitions.lean`, `BEI/Equidim.lean`
  (cleanup pass complete; structural split tracked in
  [`EQUIDIM_FILE_SPLIT.md`](EQUIDIM_FILE_SPLIT.md)),
  `BEI/GraphProperties.lean`, `BEI/Groebner.lean`,
  `BEI/GroebnerAPI.lean`, `BEI/GroebnerBasis.lean`,
  `BEI/GroebnerBasisSPolynomial.lean`, `BEI/GroebnerDeformation.lean`.

Everything else under `BEI/`, `Supplement/`, and `toMathlib/` in
`TODO.md` is still pending.

This work package is the recipe each agent should follow when picking
the next file off the queue. It must be re-read every session — do not
skip steps because "this file looks small".

## Goal

For each remaining queue file, perform a cleanup pass that:

- removes or justifies every `set_option maxHeartbeats N` raise;
- removes or justifies every `set_option synthInstance.maxHeartbeats N`
  raise;
- fixes every linter warning attributable to the file
  (`linter.flexible`, `linter.style.maxHeartbeats`, etc.);
- shortens proofs only via the lean4 skill workflow (`/lean4:refactor`,
  then `/lean4:golf`) — no ad-hoc rewrites;
- preserves all theorem statements and produces no new axioms.

After the pass, update `TODO.md` to mark the file done.

## Standing rules

These rules apply at every step of every file. Violations are commit blockers.

1. **Use the Lean MCP for proof state, not repeated `lake build` cycles.**
   Specifically: `mcp__lean-lsp__lean_diagnostic_messages`,
   `mcp__lean-lsp__lean_goal`, `mcp__lean-lsp__lean_multi_attempt`,
   `mcp__lean-lsp__lean_hover_info`, `mcp__lean-lsp__lean_local_search`.
2. **Never change a theorem, lemma, or definition statement** unless the
   user has explicitly approved the specific change. The skills enforce
   this.
3. **Never introduce a new axiom.** Run
   `mcp__lean-lsp__lean_verify <fully.qualified.name>` after substantive
   changes if you suspect any.
4. **Do not silence linters with `set_option linter.X false`** to make
   warnings disappear. Fix the cause.
5. **Whole-project `lake build` must pass before each commit.** Single-
   file builds are useful for iteration, but the commit gate is
   `lake build`.

## The per-file recipe

Pick the next unchecked file in `TODO.md` under `### Lean File Review
Queue`. Then run these phases in order. Each phase ends with a Lean MCP
diagnostics check, not a guess.

### Phase A — Baseline and audit (read-only)

1. Capture the baseline:
   ```
   lake build <Module.Name>
   ```
   Record compile time, warning count, and the list of
   `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` raises
   (and their current values).
2. Run the read-only quality audit:
   ```
   /lean4:review <path/to/File.lean>
   ```
   Read the report. Note opportunities the skill flags. Do not
   apply anything yet.
3. If the file has any `set_option maxHeartbeats N in` blocks, also
   run targeted profiling per
   [`cleanup/LEAN_PERFORMANCE_TRIAGE.md`](../cleanup/LEAN_PERFORMANCE_TRIAGE.md):
   ```
   mcp__lean-lsp__lean_profile_proof <path/to/File.lean> <line>
   ```
   on each raised declaration. Record the dominant cost (`simp`,
   instance synthesis, elaboration, kernel, …).

### Phase B — Strategy-level refactor

```
/lean4:refactor <path/to/File.lean>
```

This is the **first mutating step**. The skill will:

- find repeated patterns and propose helper extraction;
- search mathlib for shorter proofs;
- present a plan and ask before each batch.

Approve only batches whose proposed change matches the audit findings
in Phase A. Reject any batch that:

- changes a theorem statement;
- introduces a new axiom;
- moves a declaration to a different file (file moves are tracked by
  the dedicated `EQUIDIM_FILE_SPLIT.md` package — do not duplicate the
  work here).

If the file is the `LEAN_PERFORMANCE_TRIAGE.md` bullet "primary
suspicion: instance synthesis", insist on `letI` / explicit-instance
batches before approving anything else.

After applying batches, the skill runs `lake build` automatically. If
that fails, the skill reverts. Re-run with a smaller scope if needed.

### Phase C — Tactic-level golf

```
/lean4:golf <path/to/File.lean>
```

The skill will:

- detect golfable patterns in policy order
  (directness → structural → conditional);
- collapse `apply f; exact h`, narrow non-terminal `simp` to `simp only`,
  and similar instant wins;
- offer a lemma-replacement pass when invoked with
  `--search=quick` (default) or `--search=full`.

If the file is small (< 500 LOC) and the audit found low-hanging
opportunities, prefer `--search=full`:

```
/lean4:golf <path/to/File.lean> --search=full
```

After the pass, the skill runs `lake build` automatically. The skill
*must* report 0 new warnings vs. the Phase A baseline.

### Phase D — Heartbeat tightening

For every `set_option maxHeartbeats N in` block in the file:

1. Try removing the override entirely. If `lake build <Module.Name>`
   still passes, leave it removed.
2. If removal fails, halve `N`. If that also fails, restore the original
   value and add a one-line comment after the `set_option` explaining
   *why* (e.g. `-- heavy tensor extensionality, see
   L1Forward_Backward_left for the analogous proof`).
3. The Mathlib `linter.style.maxHeartbeats` warning requires the comment
   to be *after* `set_option ... in`, not before. The skills do not
   manage this — verify manually.

For every `set_option synthInstance.maxHeartbeats N in` block, do not
just halve. Per the triage guide:

1. Profile (Phase A already did this).
2. If the dominant cost is repeated instance synthesis, refactor in
   Phase B with `letI` bindings.
3. Re-measure heartbeats with `#count_heartbeats in` (run via
   `lean_run_code` to test without editing).
4. Reduce only when the new measurement supports it.

### Phase E — Verify and commit

1. Whole-project gate:
   ```
   lake build
   ```
   The build must succeed with **zero** new warnings on the touched
   file.
2. Axiom hygiene:
   ```
   bash "$LEAN4_SCRIPTS/check_axioms_inline.sh" <path/to/File.lean>
   ```
   No new axioms relative to baseline.
3. Update `TODO.md`: flip `[ ]` to `[x]` for the file.
4. Commit with `/lean4:checkpoint`:
   ```
   /lean4:checkpoint "review queue: <File.lean>"
   ```
   This runs the build, axiom check, and commit in one step.

## Skill cheatsheet (per file)

| Phase | Command |
|---|---|
| A — read-only audit | `/lean4:review <path/to/File.lean>` |
| A — profiling (only if heartbeats raised) | `mcp__lean-lsp__lean_profile_proof <path/to/File.lean> <line>` |
| B — strategy refactor | `/lean4:refactor <path/to/File.lean>` |
| C — tactic golf | `/lean4:golf <path/to/File.lean>` (or `--search=full` for small files) |
| D — heartbeat experiment | `mcp__lean-lsp__lean_multi_attempt` to test without committing |
| E — commit | `/lean4:checkpoint "review queue: <File.lean>"` |

## When to stop and ask

Ask the user (do not push through) if any of these occur:

- A skill proposes a change that requires touching a different file.
  File-spanning refactors are tracked separately
  ([`EQUIDIM_FILE_SPLIT.md`](EQUIDIM_FILE_SPLIT.md), or by paper
  formalization scope changes the user has authorized).
- A `set_option synthInstance.maxHeartbeats` block resists Phase D
  removal even after Phase B refactoring. The right next step is a
  written profile-driven question, not a guess.
- A theorem statement looks like it should change. Always ask first.
- The lean4 skill aborts repeatedly with "build failed" after applying
  its plan. Do not bypass — read the diagnostics, write a focused
  question to `questions/`, and wait for user direction.

## When the queue is empty

When every file under `### Lean File Review Queue` is `[x]`, archive
this work package to `guides/archive/`, update
`TODO.md` to remove the queue section, and update `guides/INDEX.md`.

## Out of scope

- Splitting any file into multiple files. That is the job of the
  dedicated split work packages
  ([`EQUIDIM_FILE_SPLIT.md`](EQUIDIM_FILE_SPLIT.md) and
  [`cleanup/FILE_SPLITTING_PLAN.md`](../cleanup/FILE_SPLITTING_PLAN.md)).
- Moving lemmas to `toMathlib/`. The Equidim extraction commit
  `d53e84d` is the model — when a similar opportunity appears in another
  file, write a focused question to `questions/` rather than acting
  unilaterally inside the cleanup pass.
- Any change to paper-facing theorem statements.
- Speculative rewrites that the lean4 skill workflow does not propose.
  This guide deliberately limits the agent to the skill workflow.

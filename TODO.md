# BEI Lean Formalization — TODO

## Status Legend

- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Current Tasks

### Homepage And Public Docs

- `[ ]` Expose the main definitions and setup more clearly on the homepage so
  readers can inspect the codebase structure more effectively.

### Cleanup And Maintenance Backlog

- `[ ]` Review archived and dormant support material and decide what still
  deserves explicit status tracking.
- `[ ]` Keep non-critical infrastructure issues separate from the completed
  paper-result status.
- `[ ]` Public theorem layer cleanup where the exported declarations can be
  presented more cleanly.
- `[ ]` File-splitting cleanup if current theorem locations are still awkward
  for readers or maintainers.
- `[ ]` Proof cleanup and linter cleanup from `guides/cleanup/`.

### Lean File Review Queue

- `[x]` Run a file-by-file Lean cleanup pass for simplification, shortening,
  proof golf, and presentation improvements where appropriate. Queue
  completed 2026-04-24; the per-file recipe packet is archived at
  [`guides/archive/LEAN_FILE_REVIEW_QUEUE.md`](guides/archive/LEAN_FILE_REVIEW_QUEUE.md).

---

## Standing Workflow Rules

- Keep `TODO.md`, `FORMALIZATION_MAP.md`, `docs/`, and `guides/INDEX.md` in
  sync after status or website edits.
- Archive finished work packages promptly so `guides/work_packages/` contains
  only genuinely active packets.
- Remove stale references to old blockers, old proof routes, or old milestone
  language when the corresponding work is already complete.
- Use the Lean MCP tools and the `/lean4:golf` workflow intentionally during
  file-review cleanup rather than making ad hoc edits.
- `guides/work_packages/` should stay empty until a genuinely new
  theorem-critical task appears.

---

## Current Status Snapshot

### Repository Status

- `[x]` Sections 1--4 are represented in Lean.
- `[x]` The named paper results are all covered.
- `[x]` The public status pages describe the paper-to-Lean map as complete.
- `[x]` The reader-facing website copy has had an initial editorial cleanup
  pass.

### Paper Map Snapshot

- Section 1: complete.
  Equivalent packaging remains for Proposition 1.4.
- Section 2: complete.
  Theorem 2.1 remains split across the Buchberger proof, reducedness proof, and
  the wrapper theorem.
- Section 3: complete.
  Equivalent packaging remains for Proposition 3.6, Proposition 3.8, and
  Corollary 3.9.
- Section 4: complete.

This means the remaining work is cleanup, presentation, and maintenance rather
than theorem-critical formalization.

### Guide State

- Active theorem-critical work packages: none.
- Recently retired packets:
  - `guides/archive/NEXT_SESSION_PROMPT.md`
  - `guides/archive/COROLLARY_3_4_IMPLEMENTATION.md`

---

## Notes

- `FORMALIZATION_MAP.md` is the detailed paper-vs-Lean statement map.
- `guides/cleanup/` contains the current non-critical cleanup backlog.
- `guides/website/HOMEPAGE_MATH_CONTEXT_PLAN.md` is the current website-side
  planning note.

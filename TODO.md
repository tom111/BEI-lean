# BEI Lean Formalization — TODO

## Status Legend

- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Current Tasks

### Homepage And Public Docs

- `[x]` Inline a compact "Definitions in Lean" block on the homepage (after the
  $P_4$ plate, before the Sections grid). Shows the four core declarations —
  `BinomialEdgeVars`, `binomialEdgeIdeal`, `IsClosedGraph`, and
  `binomialEdgeMonomialOrder` — in actual Lean, with file links.
- `[x]` Add a small file map (one-line gloss per Lean file under `BEI/` and
  `toMathlib/`). Lives at [`docs/code-map.md`](docs/code-map.md), linked from
  the homepage `Project Links` and the site nav.

### Cleanup And Maintenance Backlog

- `[x]` Review archived and dormant support material and decide what still
  deserves explicit status tracking. Done 2026-05-01: the previously-tracked
  dormant sorries in `toMathlib/HeightAdditivity.lean` and
  `toMathlib/GradedCM.lean` are gone (the file no longer exists or is
  sorry-free after the finite-free Case C route landed); `BEI/` and
  `toMathlib/` are sorry-free. The bloated archive enumeration in
  `guides/INDEX.md` was collapsed to a one-paragraph pointer.
- `[x]` Keep non-critical infrastructure issues separate from the completed
  paper-result status. Done 2026-05-01: TODO.md already separates the
  "Cleanup And Maintenance Backlog" / "Speed And Clarity Backlog" / "Lean
  File Review Queue" sections from the "Current Status Snapshot" /
  "Paper Map Snapshot" sections, and FORMALIZATION_MAP.md is paper-vs-Lean
  only. Treated as an evergreen organizational rule, not a discrete task.
- `[ ]` Public theorem layer cleanup where the exported declarations can be
  presented more cleanly. Dedicated guide:
  [`guides/cleanup/PUBLIC_THEOREM_LAYER.md`](guides/cleanup/PUBLIC_THEOREM_LAYER.md).
- `[ ]` File-splitting cleanup if current theorem locations are still awkward
  for readers or maintainers. Dedicated guide:
  [`guides/cleanup/FILE_SPLITTING_PLAN.md`](guides/cleanup/FILE_SPLITTING_PLAN.md).
- `[ ]` Proof cleanup and linter cleanup from `guides/cleanup/`.

### Speed And Clarity Backlog (added 2026-04-30)

- `[ ]` **Profile and drop the remaining heartbeat overrides.** 8 overrides
  remain across 4 files after the 2026-04-27 audit. Re-profile each with
  `lean_profile_proof` after recent refactors and remove any that are no
  longer load-bearing. Pairs with
  [`guides/cleanup/LEAN_PERFORMANCE_TRIAGE.md`](guides/cleanup/LEAN_PERFORMANCE_TRIAGE.md).
- `[ ]` **Sub-decompose the 354-LOC `caseD_nilradical_nzd_map_diagSubstHom_helper`.**
  Phase 1 of the giant-carving deferred this; natural sub-splits documented
  in the archived guide. Targets clarity plus a smaller per-helper rebuild
  cost.
- `[~]` **Drop unused `[Fintype V]` hypotheses.** The two helpers added on
  2026-04-30 in `BEI/PrimeDecomposition.lean` were cleared. The remaining
  ~17 warnings (across `Radical`, `PrimeDecomposition`, `MinimalPrimes`,
  `Corollary3_4`, `PrimeDecompositionDimension`, `CycleUnmixed`,
  `toMathlib/HeightVariableIdeal`) are not "pure cleanup" — the proof
  bodies need `[Fintype V]` for `IsNoetherianRing` /
  `Algebra.FiniteType` / similar instance synthesis even when the type
  signature does not. The proper fix is to change the file-level
  `variable {V : Type*} … [Fintype V]` to `[Finite V]` and recover
  `Fintype V` locally via `Fintype.ofFinite` only where actually
  needed; that's a broader refactor than this bullet implied.
- `[ ]` **Extract walk and path arithmetic helpers from `BEI/CoveredWalks.lean`.**
  Largest file in the repo (2671 LOC, 79 automation hits). Pairs with
  [`guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md`](guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md).
- `[ ]` **Add `BEI/AxiomCheck.lean`.** Permanent file with `#print axioms` on
  the seven flagship paper-facing theorems so axiom regressions are caught
  at build time instead of via ad-hoc scratch files.
- `[ ]` **CI heartbeat ratchet.** Fail CI when a new `set_option maxHeartbeats`
  raise is introduced without justification. Tracked in
  [`guides/cleanup/STATUS_AND_CI_HYGIENE.md`](guides/cleanup/STATUS_AND_CI_HYGIENE.md).

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

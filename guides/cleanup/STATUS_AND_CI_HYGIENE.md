# Guide: Status Docs and CI Hygiene

## Goal

Keep the repo's maintenance surface honest:

- status docs match the live Lean code;
- guide indexes match the actual guide set;
- CI checks at least the default build;
- warning noise is visible instead of being silently reintroduced.


## Why this matters

The repo has moved quickly.

That creates two predictable failure modes:

1. status drift, where docs still describe an older theorem layout or older
   blocker count;
2. invisible quality regressions, because the repo currently has a Pages
   workflow but no build workflow.

This is now large enough to deserve its own work package.


## Work package 1: synchronize theorem-status docs — DONE 2026-04-30

`TODO.md`, `FORMALIZATION_MAP.md`, `README.md`, and `OVERVIEW.md` now
reflect the post-2026-04-22 reality: the active paper path is sorry-free
with `proposition_1_6`, `corollary_3_4`, `corollary_3_4_connected`, and
`corollary_3_7_cm_fin` all axiom-clean. The only remaining sorries live
in `Supplement/RauhApproach.lean`, which is not built by the default Lake
target. Maintain this state on each landed pass.


## Work package 2: synchronize guide indexes and archives

Primary files:

- [guides/INDEX.md](/home/tom/BEI-lean/guides/INDEX.md)
- [guides/cleanup/PROOF_CLEANUP_INDEX.md](/home/tom/BEI-lean/guides/cleanup/PROOF_CLEANUP_INDEX.md)

Tasks:

- make sure new cleanup packets are indexed;
- move superseded guides to `archive/` rather than leaving them half-live;
- retire or rewrite stale planning files instead of letting them linger as if
  current policy.


## Work package 3: add a real Lean CI workflow

Current situation:

- the repo has [pages.yml](/home/tom/BEI-lean/.github/workflows/pages.yml);
- it does not have a GitHub Actions workflow for `lake build`.

Minimum acceptable CI:

- checkout;
- install Lean toolchain / mathlib cache as appropriate;
- run `lake build`.

The goal is not fancy automation. The goal is to stop regressions from landing
without a build signal.


## Work package 4: add warning visibility

Optional but high-value follow-up:

- have CI print or count warnings;
- keep a warning budget or at least surface the count in logs;
- make style regressions visible before they become normal.

Do not turn this into a giant lint policy before the basic build workflow exists.


## Work package 5: maintain honesty about the CM branch

Status as of 2026-04-22: `proposition_1_6`, `corollary_3_4`,
`corollary_3_4_connected`, and `corollary_3_7_cm_fin` are all
axiom-clean. The historical distinction between the equidimensional
surrogate branch and the paper's real Cohen-Macaulay branch is no longer
load-bearing for the active paper path.

What public-facing maintenance passes should still preserve:

- the surrogate-vs-paper distinction in any documentation that
  pre-dates 2026-04-22 or covers the historical development;
- the fact that the equidimensional surrogates (e.g. `IsEquidim`,
  `corollary_3_4_equidim`) are still present in the codebase as
  intermediate building blocks below the paper-facing CM theorems;
- the fact that `Supplement/RauhApproach.lean` is the only file that
  still contains `sorry`, and is intentionally outside the default
  build target.

This is not optional wording polish. It is part of mathematical correctness for
the repo metadata.


## Definition of done

This guide is complete when:

1. status docs and guide indexes match the live repo state;
2. stale planning files have been rewritten or archived;
3. GitHub Actions runs at least `lake build`;
4. warning growth is visible enough that cleanup progress can be preserved.

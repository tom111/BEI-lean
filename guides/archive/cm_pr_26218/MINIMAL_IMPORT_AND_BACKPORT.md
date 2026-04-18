# Guide: Minimal Import and Backport from mathlib PR #26218

## Preserved task

There is a mathlib pull request for Cohen–Macaulay infrastructure, referenced in
[TODO.md](/home/tom/BEI-lean/TODO.md) as PR `#26218`.

The task is:

- use that PR as a source of CM code if useful;
- import the **minimum** amount of code needed for this project;
- and, if necessary, backport that code to this repo's pinned mathlib version
  `v4.28.0` instead of upgrading the whole project.


## Current local constraints

This repo is pinned to:

- Lean `v4.28.0`
- mathlib `v4.28.0`

via:

- [lean-toolchain](/home/tom/BEI-lean/lean-toolchain)
- [lakefile.toml](/home/tom/BEI-lean/lakefile.toml)

The equidimensional surrogate track is now complete, but the paper's actual
Cohen–Macaulay track is still open. The goal here is to add real CM foundations
without needlessly destabilizing the rest of the project.

Status update:

- the first `#26218`-based CM slice is already landed locally in
  `toMathlib/CohenMacaulay/Defs.lean` and `toMathlib/CohenMacaulay/Basic.lean`;
- the current preferred next import target is no longer “some CM code in
  general”, but specifically the localization/globalization slice visible in
  upstream PR `#28599`, which depends on `#26218`.


## Core policy

Do **not** import the entire PR wholesale unless you are willing to:

- upgrade mathlib for the whole project;
- repair downstream breakage;
- and track upstream PR churn.

Instead:

1. inspect the PR;
2. identify the smallest useful CM core;
3. vendor or backport only that core;
4. keep the imported code clearly separated from BEI-specific theorems.


## What "minimal import" means

For this repo, the likely useful layers are:

### Layer 1: real CM definitions

Potentially useful:

- the actual `IsCohenMacaulay` definition;
- any prerequisite definitions it depends on, if the dependency footprint is small.

This is the most valuable slice because it gives the repo a real CM layer rather than
only the equidimensional surrogate.

### Layer 2: immediate consequences actually needed here

Potentially useful:

- CM implies equidimensionality / unmixedness consequences;
- any theorem directly needed for [Corollary 3.4](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
  or the CM half of [Corollary 3.7](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean).

This is useful only if the dependency chain remains small.

### Layer 3: deep CM machinery

Examples:

- transfer from initial ideals;
- Eagon–Northcott / determinantal CM results;
- shellability or Stanley–Reisner CM infrastructure.

Do **not** import this layer early. It is likely too large and too unstable for a pinned
`v4.28.0` project.


## Recommended workflow

## Phase 1: inspect the PR before importing anything

Before copying code, record:

1. PR number and branch/author information.
2. Exact files changed.
3. Whether the PR targets current `master` only or has been partially merged elsewhere.
4. Whether the files depend on post-`v4.28.0` APIs.

Make a temporary note file if needed, for example:

- `guides/work_packages/cm_pr_26218/PR_NOTES.md`

The goal is to know whether the useful CM code is:

- self-contained;
- easy to backport;
- or entangled with newer mathlib changes.


## Phase 2: classify files by importability

For each file or theorem in the PR, classify it as:

### Class A: direct backport candidate

Good examples:

- definitions;
- short lemmas with low dependency footprint;
- statements whose imports already exist in `v4.28.0`.

These can often be copied nearly verbatim.

### Class B: backportable with local patching

Examples:

- uses APIs renamed after `v4.28.0`;
- depends on a few newer support lemmas that can also be copied.

These are acceptable if the dependency cone is still small.

### Class C: too entangled

Examples:

- depends on large new algebraic-geometry infrastructure;
- uses broad import chains not available in `v4.28.0`;
- requires a repo-wide mathlib upgrade.

Do not backport these unless the project has explicitly decided to migrate.


## Phase 3: vendor the minimal CM core into a dedicated local area

Do **not** paste imported mathlib PR code directly into BEI theorem files.

Instead, create a clearly marked local foundation area:

- `toMathlib/CohenMacaulay/`

Recommended file split:

- `toMathlib/CohenMacaulay/Defs.lean`
- `toMathlib/CohenMacaulay/Basic.lean`
- `toMathlib/CohenMacaulay/Equidimensional.lean`

Only create the files you actually need.

Current status:

- `toMathlib/CohenMacaulay/Defs.lean` is now landed
- `toMathlib/CohenMacaulay/Basic.lean` is now landed
- `toMathlib/CohenMacaulay/Localization.lean` is now landed as the
  localization/globalization slice mined from PR `#28599`
- the `CM localizes` execution packet is now complete:
  - [../cm_pr_28599/BACKPORT_CM_LOCALIZES.md](../cm_pr_28599/BACKPORT_CM_LOCALIZES.md)
- the remaining paper-facing blocker is now downstream of the backport:
  the HH graded local-to-global CM step


## Phase 4: preserve provenance

At the top of every imported/backported file, include:

1. that the code was adapted from mathlib PR `#26218`;
2. that it was backported for compatibility with `v4.28.0`;
3. what was modified locally.

This matters for:

- future cleanup;
- eventual upstreaming or deletion;
- and avoiding confusion about which layer is project-local.

Suggested header note:

```text
This file contains code adapted from mathlib PR #26218, backported to the
v4.28.0 environment used by BEI-lean. The long-term goal is to delete this
local copy once the relevant CM infrastructure is available upstream.
```


## Phase 5: wire the CM files into the project slowly

Do not replace the placeholder branch all at once.

Recommended order:

1. import the real CM definition;
2. get the project building again;
3. only then import one needed theorem at a time;
4. only after that reconnect the paper-faithful Proposition 1.6 route.

This ensures you know which imported theorem causes breakage.


## What to try importing first

If the PR actually contains these, import in this order:

1. definition of `IsCohenMacaulay`;
2. theorem: CM implies equidimensionality / unmixedness;
3. only then any stronger corollaries.

Why:

- this is the minimum needed to make [Corollary 3.4](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
  honest once Corollary 3.3 is finished;
- it avoids dragging in deep CM applications too early.


## What not to import yet

Avoid importing first:

- determinantal CM theorems;
- initial-ideal-to-original-ideal CM transfer;
- shellability / Stanley–Reisner consequences;
- large AG dependencies.

Those are not the right first slice for BEI.


## Backport mechanics

## Step 1: copy the smallest dependency cone

When a theorem from the PR depends on helper lemmas, copy only the helpers it directly
uses, not the whole directory.

## Step 2: patch imports to `v4.28.0`

Expect issues like:

- renamed declarations;
- changed namespace paths;
- changed theorem argument order;
- newer notation or elaboration conveniences.

Backport by:

- keeping the theorem statements as close to upstream as possible;
- changing only the implementation details needed for compatibility.

## Step 3: keep local names stable

If possible, preserve the upstream names.
That will make it easier to delete the local backport later when upstream mathlib catches up.


## Testing protocol

For each imported slice:

1. build only the new CM foundation file;
2. build the file that consumes it, e.g. [CohenMacaulay.lean](/home/tom/BEI-lean/BEI/CohenMacaulay.lean);
3. then run full `lake build`.

Do not import multiple major files before testing.


## Decision rules

## Rule 1: stop if the dependency cone explodes

If importing one "small" theorem forces:

- many unrelated files;
- many new imports;
- or substantial API mismatch with `v4.28.0`,

stop and reassess. That probably means the project should either:

- remain blocked on CM for now; or
- plan a full mathlib upgrade.

## Rule 2: prefer weaker honest substitutes if they solve the immediate theorem

If Corollary 3.4 only needs equidimensionality, and the PR has a theorem giving that
from CM, import only that layer.

Do not import a full CM tower just because it exists upstream.

## Rule 3: keep the paper alignment in view

The purpose of this import is to make the paper's CM-dependent results honest.
Do not let the repo drift into a general CM experiment unrelated to BEI.


## Concrete recommended plan for BEI

### Stage A

Inspect PR `#26218` and identify:

- the definition file;
- the smallest theorem file proving a consequence like equidimensionality.

### Stage B

Backport only those files into a local CM foundation area.

### Stage C

Use them to:

1. replace the placeholder `IsCohenMacaulay`;
2. unblock the exact theorem needed for [Corollary 3.4](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean),
   if possible.

### Stage D

Only later revisit:

- Proposition 1.6;
- the CM half of Corollary 3.7;
- deeper CM transfer theorems.


## Deliverables

If Claude follows this guide, the expected outputs should be:

1. a short note recording what PR `#26218` contains and what was selected;
2. a local backported CM foundation directory;
3. provenance comments in each imported file;
4. replacement of the fake placeholder with real code;
5. no unnecessary mathlib upgrade unless explicitly chosen.


## Final recommendation

Use PR `#26218` as a **mine**, not as a **dependency**.

That is:

- extract the smallest honest CM core;
- backport it locally to `v4.28.0`;
- keep provenance clear;
- and import only what is needed for the paper-facing BEI goals.

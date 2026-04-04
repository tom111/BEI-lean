# Status Files Sync Guide

## Task

Keep `TODO.md` and `FORMALIZATION_MAP.md` synchronized with the actual Lean code.
These are human-facing documents, so stale status here is worse than having less detail.

## Why this matters

This repo now has several split theorem files:
- `BEI/GroebnerBasisSPolynomial.lean` vs `BEI/GroebnerBasis.lean`
- `BEI/PrimeDecomposition.lean` vs `BEI/PrimeDecompositionDimension.lean`

When a theorem moves or gets split, the status docs drift quickly unless they are updated
in the same round. Worker agents should not leave those files behind after a substantial
proof or organization change.

## Source of truth

Use this order:

1. `BEI.tex` for the paper statement.
2. The live Lean declaration and its current file location.
3. `lake build` / warning output for whether the declaration still depends on `sorry`.
4. Only then update `TODO.md` and `FORMALIZATION_MAP.md`.

Do not let an older guide or comment override the code.

## What to update after a theorem change

When a theorem is newly proved, moved, split, or rephrased:

1. Update `TODO.md`.
   - current status
   - current file location
   - active priorities if this changes what is blocking the project
   - sorry counts if the theorem removed or added one

2. Update `FORMALIZATION_MAP.md`.
   - exact Lean declaration name
   - correct file
   - fidelity label: Exact / Equivalent / Weaker / Partial / Sorry / Blocked
   - a short honest note if the Lean statement differs from the paper

3. If the structure changed, update `CLAUDE.md`.
   - only the project-structure bullets and standing workflow notes

4. If a public GitHub-facing link changed, update `README.md` or `docs/`.

## How to classify status honestly

- Use **Exact** only when the Lean theorem really matches the paper statement.
- Use **Equivalent** when the statement is the same mathematically but phrased differently.
- Use **Partial** when one direction or one branch is still incomplete.
- Use **Sorry** when the declaration exists but still depends on `sorry`.
- Use **Blocked** when the endpoint depends on missing foundations, for example the current CM branch.

Do not collapse `Partial`, `Sorry`, and `Blocked` into one bucket.

## Cohen–Macaulay caution

Do not advertise CM results as proved while `BEI/CohenMacaulay.lean` still defines
`IsCohenMacaulay` by placeholder. In particular:
- Proposition 1.6
- Corollary 3.4
- the CM branch of Corollary 3.7

should remain clearly marked as blocked or sorry until the foundations are real.

## Current hotspots

As of the current repo state, the status files most need to track:
- the Corollary 3.3 move to `BEI/PrimeDecompositionDimension.lean`
- the Theorem 2.1 split between `BEI/GroebnerBasisSPolynomial.lean` and `BEI/GroebnerBasis.lean`
- the fact that Corollary 3.7 is still only partial
- the honest CM-blocked state of Proposition 1.6 and Corollary 3.4

## Minimum acceptable practice

If you finish a theorem or complete a file split, do not leave the repo with stale
`TODO.md` and `FORMALIZATION_MAP.md`. Update them before moving on.

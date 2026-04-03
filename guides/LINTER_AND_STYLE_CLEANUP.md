# Guide: Linter and Style Cleanup

## Goal

Reduce noise so that warnings no longer drown out meaningful proof problems.


## Why this matters

`lake build` currently succeeds, but the warning stream is large.
That has two bad effects:

1. real regressions are harder to spot;
2. Claude gets less signal about what actually needs attention.


## Highest-value cleanup items

## 1. Remove unused section variables and typeclass assumptions

This is especially noisy in:

- [GraphProperties.lean](/home/tom/BEI-lean/BEI/GraphProperties.lean)
- `toMathlib/*`

Recommended pattern:

- narrow the `variable` blocks;
- use `classical` locally instead of carrying `[DecidableEq _]` or `[Fintype _]`
  throughout an entire section when only a few proofs need them.


## 2. Replace `show` with `change` where the linter complains

This is minor but easy and keeps style consistent.


## 3. Replace deprecated constants

Example:

- use the nondeprecated quotient nontriviality theorem in `HeightAdditivity`.


## 4. Tighten theorem statements

If a theorem only needs `Finite`, do not require `Fintype`.
If a proof only needs decidability locally, do not put it in the theorem statement.

This improves both readability and reuse.


## 5. Keep notes precise

The current inline notes are often helpful. Keep them, but make sure they describe:

- a real mismatch;
- a subtlety in the mathematics;
- or a proof-engineering reason.

Avoid notes that only narrate implementation trivia unless the trivia prevents future
misproofs.


## Order of work

Recommended order:

1. fix unused assumptions in `GraphProperties.lean`;
2. fix style warnings in `toMathlib/*`;
3. then revisit other files opportunistically during real refactors.

Do not spend a whole session only on linter cleanup if larger structural cleanup is
already in progress.


## Definition of done

This guide is complete when:

1. the warning count is substantially lower;
2. the remaining warnings correspond to genuinely deferred issues, not routine cleanup;
3. theorem statements carry only the assumptions they actually use.

# Guide: Linter and Style Cleanup

## Goal

Reduce noise so that warnings no longer drown out meaningful proof problems.


## Why this matters

`lake build` currently succeeds, but the warning stream is large.
That has two bad effects:

1. real regressions are harder to spot;
2. Claude gets less signal about what actually needs attention.

At the 2026-04-30 repo state, the default build emits roughly **46
warnings total** (down from 399 on 2026-04-20). The remaining
warning classes are dominated by:

- "hypothesis not used in the remainder of the type"
  (linter.unusedFintypeInType) — most of the remaining warnings;
- long-line warnings in `BEI/GroebnerBasis.lean`;
- a handful of flexible-tactic and missing-`maxHeartbeats`-comment
  hits in `toMathlib/CohenMacaulay/`.

Re-scan with `lake build 2>&1 | grep -c '^warning:'` before starting
a new pass — the absolute counts shift quickly under cleanup.

The biggest warning hotspots are:

- [BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean)
- [BEI/GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
- [BEI/MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)
- [toMathlib/CohenMacaulay/Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean)
- [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean)


## Highest-value cleanup items

## 1. Remove unused assumptions from theorem statements

This is the largest recurring warning class.

Especially noisy files:

- [BEI/GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
- [BEI/MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)
- [BEI/PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)

Recommended pattern:

- narrow the `variable` blocks;
- replace `[Fintype _]` with `Finite` when that is all the statement needs;
- use `classical` locally instead of carrying `[DecidableEq _]` or `[Fintype _]`
  through an entire theorem statement.


## 2. Replace `show` with `change` in style-only conversions

This is now concentrated in:

- the files in [BEI/Equidim/](/home/tom/BEI-lean/BEI/Equidim/) (the pre-split
  `BEI/Equidim.lean` was the original noisy file; the warnings now live in
  the split files, especially `IteratedRegularity.lean` and `L1Iso.lean`)
- [toMathlib/CohenMacaulay/Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean)
- [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean)

Do not do this blindly where `show` is genuinely being used for readability and
not to change the goal. The point is to delete linter noise, not to churn proofs.


## 3. Delete unused `simp` arguments

This is the easiest high-volume cleanup after unused assumptions.

Especially noisy files:

- the files in [BEI/Equidim/](/home/tom/BEI-lean/BEI/Equidim/) (post-split)
- [BEI/GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
- [BEI/MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)
- [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean)

Prefer:

- `simp only` with the exact surviving lemmas;
- or delete the redundant arguments and keep the existing `simp`.


## 4. Scope every `maxHeartbeats` and justify it

Current problems:

- missing inline comments explaining the need for the heartbeat increase;
- one unscoped `set_option maxHeartbeats` warning in
  [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean).

Cleanup rule:

- every heartbeat bump should be declaration-scoped;
- every bump should carry a one-line reason tied to proof search or elaboration cost.


## 5. Tighten theorem statements and variable blocks

If a theorem only needs `Finite`, do not require `Fintype`.
If a proof only needs decidability locally, do not put it in the theorem statement.

This improves both readability and reuse.


## 6. Remove long lines, flexible `simp`, and dead locals

This is lower mathematical value than the items above, but still worth doing in
the high-noise files.

In particular:

- wrap long type signatures and `simp only` lists;
- replace flexible `simp at h` calls when the linter gives a stable suggestion;
- delete unused local hypotheses like `hConn`, `hn`, `ha`.


## 7. Keep notes precise

The current inline notes are often helpful. Keep them, but make sure they describe:

- a real mismatch;
- a subtlety in the mathematics;
- or a proof-engineering reason.

Avoid notes that only narrate implementation trivia unless the trivia prevents future
misproofs.


## Order of work

Recommended order:

1. clean active theorem-path files with localized changes:
   [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean),
   [BEI/Proposition1_6.lean](/home/tom/BEI-lean/BEI/Proposition1_6.lean),
   nearby status docs;
2. remove unused assumptions and dead locals in
   [BEI/GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean),
   [BEI/MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean),
   and [BEI/PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean);
3. clean [toMathlib/CohenMacaulay/Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean)
   after its API boundary is clearer;
4. tackle the files in [BEI/Equidim/](/home/tom/BEI-lean/BEI/Equidim/) one
   at a time. The pre-split monolith is gone; each split file is now a
   reasonable batch on its own.

Do not spend a whole session only on linter cleanup if larger structural cleanup is
already in progress.


## Definition of done

This guide is complete when:

1. routine style noise is gone from the active theorem-path files;
2. the warning count is substantially lower and concentrated in a small set of
   genuinely deferred hotspots;
3. theorem statements carry only the assumptions they actually use;
4. no file uses unscoped `set_option maxHeartbeats`.

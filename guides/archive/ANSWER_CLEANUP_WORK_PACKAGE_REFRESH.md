# Answer: Refresh Cleanup Work Packages

## Original task

> Update the cleanup work packages and add new ones if necessary. No need for a
> schedule. Just lay out what needs to be done in appropriate size work packages.


## Context used

This answer is based on the live repo state as of 2026-04-20:

- Section 4 is complete.
- The paper-critical path has been reduced to one remaining sorry in
  [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean).
- The default `lake build` succeeds, but the warning stream is still large.
- The main current maintenance hotspots are:
  [BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean),
  [BEI/CoveredWalks.lean](/home/tom/BEI-lean/BEI/CoveredWalks.lean),
  [BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean),
  [BEI/PrimeIdeals.lean](/home/tom/BEI-lean/BEI/PrimeIdeals.lean),
  [BEI/GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean),
  [BEI/GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean),
  and
  [toMathlib/CohenMacaulay/Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean).


## What was changed

Updated cleanup packets:

- [cleanup/PROOF_CLEANUP_INDEX.md](/home/tom/BEI-lean/guides/cleanup/PROOF_CLEANUP_INDEX.md)
- [cleanup/PUBLIC_THEOREM_LAYER.md](/home/tom/BEI-lean/guides/cleanup/PUBLIC_THEOREM_LAYER.md)
- [cleanup/PATH_AND_INTERNAL_VERTEX_API.md](/home/tom/BEI-lean/guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
- [cleanup/MONOMIAL_AND_FINSUPP_API.md](/home/tom/BEI-lean/guides/cleanup/MONOMIAL_AND_FINSUPP_API.md)
- [cleanup/FILE_SPLITTING_PLAN.md](/home/tom/BEI-lean/guides/cleanup/FILE_SPLITTING_PLAN.md)
- [cleanup/LINTER_AND_STYLE_CLEANUP.md](/home/tom/BEI-lean/guides/cleanup/LINTER_AND_STYLE_CLEANUP.md)

New cleanup packets:

- [cleanup/EQUIDIM_DECOMPOSITION.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_DECOMPOSITION.md)
- [cleanup/CM_SUPPORT_REFACTOR.md](/home/tom/BEI-lean/guides/cleanup/CM_SUPPORT_REFACTOR.md)
- [cleanup/STATUS_AND_CI_HYGIENE.md](/home/tom/BEI-lean/guides/cleanup/STATUS_AND_CI_HYGIENE.md)

Index sync:

- [guides/INDEX.md](/home/tom/BEI-lean/guides/INDEX.md)


## New work package boundaries

The main changes in scope are:

1. `Equidim` now has its own decomposition packet, because it is no longer just
   a small surrogate file. It mixes initial-ideal setup, HH regularity, HH CM,
   tensor-localization transport, and public wrappers.
2. The CM support layer now has its own refactor packet, because
   `toMathlib/CohenMacaulay/Polynomial.lean` has grown into a real maintenance
   target with mixed theorem roles.
3. Status-doc and CI hygiene now have their own packet, because the repo is
   large enough that stale status prose and missing build CI are now genuine
   quality risks rather than incidental cleanup.


## Intended use

These packets are not a schedule.

They are meant to give Claude or a future maintenance pass a set of
self-contained, correctly-sized cleanup units:

- theorem-layer cleanup;
- shared API extraction;
- large-file decomposition;
- warning burn-down;
- repo-honesty and CI hygiene.

That is the right granularity for the current repository state.

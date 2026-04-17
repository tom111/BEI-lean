# Guide Index

`guides/` is now an umbrella directory with four subdirectories:

- `work_packages/` for active Claude-facing coding packets;
- `answers/` for preserved answers and decision memos;
- `cleanup/` for optional refactor and proof-cleanup packets;
- `process/` for workflow / maintenance notes.

## Active Work Packages

1. [work_packages/PROP_1_6_CM_TRANSFER.md](work_packages/PROP_1_6_CM_TRANSFER.md)
   Bring real Cohen–Macaulay theory into the repo far enough to finish the
   paper-faithful Proposition 1.6 track.

2. [work_packages/HH_GLOBAL_CM_FROM_AUGIDEAL.md](work_packages/HH_GLOBAL_CM_FROM_AUGIDEAL.md)
   Smallest active HH-side packet: turn augmentation-ideal CM into a genuine
   global `IsCohenMacaulayRing` theorem for the HH quotient.

3. [work_packages/POLYNOMIAL_RING_CM_BASE_CASE.md](work_packages/POLYNOMIAL_RING_CM_BASE_CASE.md)
   **Active support packet**: the polynomial CM infrastructure is now landed in
   `toMathlib/CohenMacaulay/Polynomial.lean`; finish the final remaining sorry
   in the polynomial-extension theorem, then use it in the HH base case.

4. [work_packages/GROEBNER_CM_TRANSFER.md](work_packages/GROEBNER_CM_TRANSFER.md)
   Dormant paper-critical packet: after the HH-side global CM theorem lands,
   transfer Cohen–Macaulayness from the initial ideal quotient back to the
   original quotient.

## Proposition 1.6 Context

- [work_packages/GRADED_CM_LOCAL_TO_GLOBAL.md](work_packages/GRADED_CM_LOCAL_TO_GLOBAL.md)
  Broader theorem-context memo for the remaining HH-side global CM step.

- [work_packages/GRADED_CM_INDUCTION.md](work_packages/GRADED_CM_INDUCTION.md)
  Superseded route memo; kept as a record of the graded-induction branch that
  narrowed the problem before the current graded-contraction route.

- [work_packages/GRADED_CONTRACTION_NZD.md](work_packages/GRADED_CONTRACTION_NZD.md)
  Completed support packet; the contraction theorem is proved and the
  remaining HH-side blocker is now the polynomial-ring base case.

- [work_packages/CM_PARAMETER_PREFIX_UNMIXED.md](work_packages/CM_PARAMETER_PREFIX_UNMIXED.md)
  Superseded route memo; the broad parameter-prefix strategy was narrowed and
  then replaced by the polynomial-CM base-case route.

- [work_packages/DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md](work_packages/DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md)
  Superseded route memo; kept only as a record of the dehomogenization branch
  that was investigated and then rejected as the active path.

- [work_packages/CM_LOCALIZES.md](work_packages/CM_LOCALIZES.md)
  Completed theorem-context memo for the now-landed CM-localization packet.

Consumed packet:
- [work_packages/HH_CM_TO_GLOBAL.md](work_packages/HH_CM_TO_GLOBAL.md)
  The HH regular-sequence and local-CM work is done there; the remaining global
  CM step is tracked separately in `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.

Completed (bridge lemmas + IsWeaklyRegular now landed):
- [work_packages/HH_CM_BRIDGE_LEMMAS.md](work_packages/HH_CM_BRIDGE_LEMMAS.md)
  Steps A+B done; Step C (localization) documented in HH_CM_TO_GLOBAL.md.

Superseded:
- [work_packages/HH_BIPARTITE_CM_PACKAGING.md](work_packages/HH_BIPARTITE_CM_PACKAGING.md)
  Resolved by the bridge lemmas and IsWeaklyRegular theorem.

Supporting CM backport packet:
- [work_packages/cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md](work_packages/cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md)
  Historical/supporting backport-planning packet; no longer the immediate
  Proposition 1.6 coding target.

- [work_packages/cm_pr_26218/BASIC_FORWARD_DEPTH.md](work_packages/cm_pr_26218/BASIC_FORWARD_DEPTH.md)
  Useful general CM infrastructure, but not the immediate paper-critical task.

Completed backport packet:
- [work_packages/cm_pr_28599/BACKPORT_CM_LOCALIZES.md](work_packages/cm_pr_28599/BACKPORT_CM_LOCALIZES.md)
  Completed CM-localization backport, now landed in
  `toMathlib/CohenMacaulay/Localization.lean`.

## Answers And Decision Notes

- [answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md](answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md)
  Decision note: the paper-critical gaps are the HH bipartite CM theorem and
  the Gröbner transfer theorem; the forward depth inequality is supporting
  infrastructure, not the immediate Prop. 1.6 blocker.

- [answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md)
  Dormant infrastructure repair; useful reference, not on the critical path.

## Cleanup And Refactor Packets

- [cleanup/PROOF_CLEANUP_INDEX.md](cleanup/PROOF_CLEANUP_INDEX.md)
  Index of optional proof-cleanup packets.

- [cleanup/PUBLIC_THEOREM_LAYER.md](cleanup/PUBLIC_THEOREM_LAYER.md)
- [cleanup/EVALUATION_MAP_API.md](cleanup/EVALUATION_MAP_API.md)
- [cleanup/PATH_AND_INTERNAL_VERTEX_API.md](cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
- [cleanup/MONOMIAL_AND_FINSUPP_API.md](cleanup/MONOMIAL_AND_FINSUPP_API.md)
- [cleanup/FILE_SPLITTING_PLAN.md](cleanup/FILE_SPLITTING_PLAN.md)
- [cleanup/LINTER_AND_STYLE_CLEANUP.md](cleanup/LINTER_AND_STYLE_CLEANUP.md)

## Website Plans

- [website/HOMEPAGE_MATH_CONTEXT_PLAN.md](website/HOMEPAGE_MATH_CONTEXT_PLAN.md)
  Plan for a richer public-facing site with theorem-driven section pages and
  side-by-side paper/Lean comparison cards.

## Process

- [process/STATUS_FILES_SYNC.md](process/STATUS_FILES_SYNC.md)
  Workflow note for keeping status files aligned with the live Lean code.

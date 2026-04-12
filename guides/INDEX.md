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

2. [work_packages/cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md](work_packages/cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md)
   Supporting general-CM subtrack: inspect PR `#26218`, identify the smallest
   usable real CM slice, and backport/import it cleanly.

Current next concrete target:
- [work_packages/CM_LOCALIZES.md](work_packages/CM_LOCALIZES.md)
  Current recommended packet for the remaining HH-side global CM step:
  isolate or prove a theorem strong enough to pass from the proved
  `IsCohenMacaulayLocalRing` at the augmentation ideal to a global
  `IsCohenMacaulayRing` theorem for the HH quotient.  Right now this is framed
  as "CM localizes".

Consumed packet:
- [work_packages/HH_CM_TO_GLOBAL.md](work_packages/HH_CM_TO_GLOBAL.md)
  The HH regular-sequence and local-CM work is done there; the remaining global
  CM step is tracked separately in CM_LOCALIZES.md.

Completed (bridge lemmas + IsWeaklyRegular now landed):
- [work_packages/HH_CM_BRIDGE_LEMMAS.md](work_packages/HH_CM_BRIDGE_LEMMAS.md)
  Steps A+B done; Step C (localization) documented in HH_CM_TO_GLOBAL.md.

Superseded:
- [work_packages/HH_BIPARTITE_CM_PACKAGING.md](work_packages/HH_BIPARTITE_CM_PACKAGING.md)
  Resolved by the bridge lemmas and IsWeaklyRegular theorem.

Supporting CM backport packet:
- [work_packages/cm_pr_26218/BASIC_FORWARD_DEPTH.md](work_packages/cm_pr_26218/BASIC_FORWARD_DEPTH.md)
  Useful general CM infrastructure, but not the immediate paper-critical task.

Dormant paper-critical packet:
- [work_packages/GROEBNER_CM_TRANSFER.md](work_packages/GROEBNER_CM_TRANSFER.md)
  The second remaining Proposition 1.6 gap after the HH-side CM theorem:
  transfer Cohen–Macaulayness from the initial ideal quotient back to the
  original quotient.

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

## Process

- [process/STATUS_FILES_SYNC.md](process/STATUS_FILES_SYNC.md)
  Workflow note for keeping status files aligned with the live Lean code.

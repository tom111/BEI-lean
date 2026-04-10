# Guide Queue

This directory is the current todo list.

## Active Theorem Track

1. [PROP_1_6_CM_TRANSFER.md](PROP_1_6_CM_TRANSFER.md)
   Bring real Cohen–Macaulay theory into the repo far enough to finish the
   paper-faithful Proposition 1.6 track.

2. [cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md](cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md)
   Supporting general-CM subtrack: inspect PR `#26218`, identify the smallest
   usable real CM slice, and backport/import it cleanly.

Current next concrete target:
- [ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md](ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md)
  Decision note: the paper-critical gaps are the HH bipartite CM theorem and
  the Gröbner transfer theorem; the forward depth inequality is supporting
  infrastructure, not the immediate Prop. 1.6 blocker.

Current next concrete theorem packet to write/use:
- a new guide for the HH bipartite Cohen–Macaulay theorem

Supporting CM backport packet:
- [cm_pr_26218/BASIC_FORWARD_DEPTH.md](cm_pr_26218/BASIC_FORWARD_DEPTH.md)
  Useful general CM infrastructure, but not the immediate paper-critical task.

## Dormant / Optional

- [ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md)
  Dormant infrastructure repair; not on the critical path.

- [FILE_SPLITTING_PLAN.md](FILE_SPLITTING_PLAN.md)
  Structural cleanup notes for later refactors.

- [PROOF_CLEANUP_INDEX.md](PROOF_CLEANUP_INDEX.md)
  Index of optional proof-cleanup packets.

- [PUBLIC_THEOREM_LAYER.md](PUBLIC_THEOREM_LAYER.md)
- [EVALUATION_MAP_API.md](EVALUATION_MAP_API.md)
- [PATH_AND_INTERNAL_VERTEX_API.md](PATH_AND_INTERNAL_VERTEX_API.md)
- [MONOMIAL_AND_FINSUPP_API.md](MONOMIAL_AND_FINSUPP_API.md)
- [LINTER_AND_STYLE_CLEANUP.md](LINTER_AND_STYLE_CLEANUP.md)

# Guide Index

`guides/` is an umbrella directory with the following subdirectories:

- `work_packages/` — active Claude-facing coding packets.
- `answers/` — preserved answers and decision memos.
- `cleanup/` — optional refactor and proof-cleanup packets.
- `process/` — workflow / maintenance notes.
- `website/` — plans for the public-facing site.
- `archive/` — completed / superseded guides, kept for historical context.

When a guide is completed or superseded, move it into `archive/`. Do not delete — rename and leave a trail.

## Active Work Packages

1. [work_packages/NEXT_SESSION_PROMPT.md](work_packages/NEXT_SESSION_PROMPT.md)
   **Proposition 1.6 is now AXIOM-CLEAN (2026-04-22).** This file records the full proof chain and lists possible follow-up targets: Corollary 3.4 full paper statement, proof cleanup, dormant-sorry retirement, and Mathlib upstreaming candidates.

## Answers And Decision Notes

- [answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md)
  Dormant infrastructure repair; useful reference, not on the critical path.

## Cleanup And Refactor Packets

Optional proof-engineering work, not on the theorem-proving critical path.

- [cleanup/PROOF_CLEANUP_INDEX.md](cleanup/PROOF_CLEANUP_INDEX.md) — index of the other cleanup packets.
- [cleanup/PUBLIC_THEOREM_LAYER.md](cleanup/PUBLIC_THEOREM_LAYER.md)
- [cleanup/EVALUATION_MAP_API.md](cleanup/EVALUATION_MAP_API.md)
- [cleanup/PATH_AND_INTERNAL_VERTEX_API.md](cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
- [cleanup/MONOMIAL_AND_FINSUPP_API.md](cleanup/MONOMIAL_AND_FINSUPP_API.md)
- [cleanup/EQUIDIM_DECOMPOSITION.md](cleanup/EQUIDIM_DECOMPOSITION.md)
- [cleanup/CM_SUPPORT_REFACTOR.md](cleanup/CM_SUPPORT_REFACTOR.md)
- [cleanup/FILE_SPLITTING_PLAN.md](cleanup/FILE_SPLITTING_PLAN.md)
- [cleanup/LINTER_AND_STYLE_CLEANUP.md](cleanup/LINTER_AND_STYLE_CLEANUP.md)
- [cleanup/STATUS_AND_CI_HYGIENE.md](cleanup/STATUS_AND_CI_HYGIENE.md)

## Website Plans

- [website/HOMEPAGE_MATH_CONTEXT_PLAN.md](website/HOMEPAGE_MATH_CONTEXT_PLAN.md)

## Process

- [process/STATUS_FILES_SYNC.md](process/STATUS_FILES_SYNC.md)

## Archive

Completed / superseded packets, retained for historical context only. Do not treat as current policy.

### Prop 1.6 work packages (all fully consumed, 2026-04-22)

- `archive/FULL_PROP_1_6_PLAN.md` — 3-step plan for paper-exact Proposition 1.6; all steps landed.
- `archive/PROP_1_6_CM_TRANSFER.md` — higher-level strategic context; consumed.
- `archive/GROEBNER_CM_TRANSFER.md` — Gröbner deformation CM transfer (Eisenbud 15.17); R1 closed.
- `archive/GRADED_CM_CASE_C_PLAN.md` — plan for closing `caseC_CM_transfer`; closed via finite-free route.
- `archive/ROUTE_B_OBSTACLE_PLAN.md` — abandoned Route B (generic-linear-form induction); Case C closed via finite-free route instead.
- `archive/CASE_C_MATH_QUESTION.md` — math question for deep-thinking model; answered in `ANSWER_CASE_C_FINITE_FREE_ROUTE.md`.
- `archive/ANSWER_CASE_C_FINITE_FREE_ROUTE.md` — strategic answer adopting the finite-free parameter-subring route; strategy fully realized.
- `archive/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md` — decision note identifying the HH and Gröbner gaps; both gaps now closed.
- `archive/ANSWER_CLEANUP_WORK_PACKAGE_REFRESH.md` — cleanup packet refresh; consumed.

### Earlier completed packets

- `archive/CM_LOCALIZES.md` — CM-localizes theorem packet (landed).
- `archive/CM_PARAMETER_PREFIX_UNMIXED.md` — superseded route.
- `archive/DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md` — superseded route.
- `archive/GRADED_CM_INDUCTION.md` — superseded graded-induction branch.
- `archive/GRADED_CM_LOCAL_TO_GLOBAL.md` — broader theorem-context memo, now consumed.
- `archive/GRADED_CONTRACTION_NZD.md` — completed support packet.
- `archive/HH_BIPARTITE_CM_PACKAGING.md` — superseded by `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.
- `archive/HH_CM_BRIDGE_LEMMAS.md` — bridge lemmas landed; step C tracked in `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.
- `archive/HH_CM_TO_GLOBAL.md` — consumed; remaining work moved to `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.
- `archive/POLYNOMIAL_RING_CM_BASE_CASE.md` — polynomial CM extension landed.
- `archive/cm_pr_26218/` — Cohen–Macaulay backport from Mathlib PR #26218, landed.
- `archive/cm_pr_28599/` — CM-localization backport from Mathlib PR #28599, landed.
- `archive/SESSION_A2_HANDOFF.md` — Session A′.2 handoff brief, consumed.
- `archive/SESSION_C3_HANDOFF.md` — Session C3 handoff; consumed 2026-04-20.
- `archive/FINAL_CHAIN_PLAN.md` — F2-chain sequencing plan; fully consumed.
- `archive/HH_GLOBAL_CM_FROM_AUGIDEAL.md` — F2-route narrative; consumed 2026-04-20.
- `archive/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md` — validated F2 strategy; consumed.

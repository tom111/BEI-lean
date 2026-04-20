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

1. [work_packages/FULL_PROP_1_6_PLAN.md](work_packages/FULL_PROP_1_6_PLAN.md)
   Overall 3-phase plan for paper-exact Proposition 1.6. **Phase 1 (HH global CM) done 2026-04-20**; Phases 2 (Gröbner degeneration) and 3 (assembly) remain.

2. [work_packages/PROP_1_6_CM_TRANSFER.md](work_packages/PROP_1_6_CM_TRANSFER.md)
   Remaining paper-faithful algebra track for Prop 1.6: part (1) packaging the HH regularity infrastructure is **done** (`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`); part (2) Gröbner transfer remains (see `GROEBNER_CM_TRANSFER.md`).

3. [work_packages/GROEBNER_CM_TRANSFER.md](work_packages/GROEBNER_CM_TRANSFER.md)
   Phase 2 packet: transfer Cohen–Macaulayness from the initial ideal quotient back to the original quotient (upper semicontinuity of depth).

## Answers And Decision Notes

- [answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md](answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md)
  Decision note: the paper-critical gaps are the HH bipartite CM theorem (now done) and the Gröbner transfer theorem.

- [answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md)
  Dormant infrastructure repair; useful reference, not on the critical path.

## Cleanup And Refactor Packets

Optional proof-engineering work, not on the theorem-proving critical path.

- [cleanup/PROOF_CLEANUP_INDEX.md](cleanup/PROOF_CLEANUP_INDEX.md) — index of the other cleanup packets.
- [cleanup/PUBLIC_THEOREM_LAYER.md](cleanup/PUBLIC_THEOREM_LAYER.md)
- [cleanup/EVALUATION_MAP_API.md](cleanup/EVALUATION_MAP_API.md)
- [cleanup/PATH_AND_INTERNAL_VERTEX_API.md](cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
- [cleanup/MONOMIAL_AND_FINSUPP_API.md](cleanup/MONOMIAL_AND_FINSUPP_API.md)
- [cleanup/FILE_SPLITTING_PLAN.md](cleanup/FILE_SPLITTING_PLAN.md)
- [cleanup/LINTER_AND_STYLE_CLEANUP.md](cleanup/LINTER_AND_STYLE_CLEANUP.md)

## Website Plans

- [website/HOMEPAGE_MATH_CONTEXT_PLAN.md](website/HOMEPAGE_MATH_CONTEXT_PLAN.md)

## Process

- [process/STATUS_FILES_SYNC.md](process/STATUS_FILES_SYNC.md)

## Archive

Completed / superseded packets, retained for historical context only. Do not treat as current policy.

- `archive/CM_LOCALIZES.md` — CM-localizes theorem packet (landed).
- `archive/CM_PARAMETER_PREFIX_UNMIXED.md` — superseded route.
- `archive/DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md` — superseded route.
- `archive/GRADED_CM_INDUCTION.md` — superseded graded-induction branch.
- `archive/GRADED_CM_LOCAL_TO_GLOBAL.md` — broader theorem-context memo, now consumed.
- `archive/GRADED_CONTRACTION_NZD.md` — completed support packet.
- `archive/HH_BIPARTITE_CM_PACKAGING.md` — superseded by `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.
- `archive/HH_CM_BRIDGE_LEMMAS.md` — bridge lemmas landed; step C tracked in `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.
- `archive/HH_CM_TO_GLOBAL.md` — consumed; remaining work moved to `HH_GLOBAL_CM_FROM_AUGIDEAL.md`.
- `archive/POLYNOMIAL_RING_CM_BASE_CASE.md` — polynomial CM extension landed (domain + non-domain versions both in `toMathlib/CohenMacaulay/Polynomial.lean`).
- `archive/cm_pr_26218/` — Cohen–Macaulay backport from Mathlib PR #26218, landed.
- `archive/cm_pr_28599/` — CM-localization backport from Mathlib PR #28599, landed (companion to the polynomial PR #28599 slice now directly in `toMathlib/CohenMacaulay/Polynomial.lean`).
- `archive/SESSION_A2_HANDOFF.md` — Session A′.2 handoff brief, consumed by commit `9067040`.
- `archive/SESSION_C3_HANDOFF.md` — Session C3 handoff (C3a-inr + C3b assembly); consumed 2026-04-20, sorry closed in `BEI/Equidim.lean`.
- `archive/FINAL_CHAIN_PLAN.md` — F2-chain sequencing plan; fully consumed (Sessions A′, B, C1, C2, C3 all landed 2026-04-20).
- `archive/HH_GLOBAL_CM_FROM_AUGIDEAL.md` — F2-route narrative; consumed by `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` (2026-04-20).
- `archive/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md` — validated F2 strategy for `p ⊄ m⁺` branch; strategy fully consumed 2026-04-20.

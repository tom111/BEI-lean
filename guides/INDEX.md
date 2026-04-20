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
   Overall 3-step plan for paper-exact Proposition 1.6. **Step 1 (monomial-side CM) done 2026-04-20**: `monomialInitialIdeal_isCohenMacaulay` in `BEI/Equidim.lean`. Steps 2 (Gröbner degeneration) and 3 (final assembly) remain.

2. [work_packages/PROP_1_6_CM_TRANSFER.md](work_packages/PROP_1_6_CM_TRANSFER.md)
   Higher-level strategic context for the remaining paper-faithful algebra track. Most internal HH blockers are resolved; remaining paper-critical gap is the Gröbner transfer (see `GROEBNER_CM_TRANSFER.md`).

3. [work_packages/GROEBNER_CM_TRANSFER.md](work_packages/GROEBNER_CM_TRANSFER.md)
   Step 2 packet: transfer CM from `S ⧸ in_<(J_G)` to `S ⧸ J_G`. Contains detailed plans for R1 (Eisenbud 15.17 / depth semicontinuity), R2 (Conca–Varbaro), R3 (direct regular sequence), and R4 (immediate axiomatized transfer to unblock the Step 3 assembly). Recommended sequencing: R4 first, then R1 as the long-term target.

## Answers And Decision Notes

- [answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md](answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md)
  Decision note: the paper-critical gaps are the HH bipartite CM theorem (now done) and the Gröbner transfer theorem.

- [answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](answers/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md)
  Dormant infrastructure repair; useful reference, not on the critical path.

- [answers/ANSWER_CLEANUP_WORK_PACKAGE_REFRESH.md](answers/ANSWER_CLEANUP_WORK_PACKAGE_REFRESH.md)
  Decision note: refreshes the cleanup packet set to match the live 2026-04-20
  repo state and adds new packets for `Equidim`, the CM support layer, and
  status/CI hygiene.

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

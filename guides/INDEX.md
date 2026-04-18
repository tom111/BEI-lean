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
   Overall 3-phase plan for paper-exact Proposition 1.6 (HH global CM → Gröbner degeneration → assembly).

2. [work_packages/HH_GLOBAL_CM_FROM_AUGIDEAL.md](work_packages/HH_GLOBAL_CM_FROM_AUGIDEAL.md)
   **Active sorry (`BEI/Equidim.lean:4648`)**: turn augmentation-ideal CM into a global `IsCohenMacaulayRing` theorem for the HH quotient. Tracks the F2 route and the Strategy I alternative.

3. [work_packages/PROP_1_6_CM_TRANSFER.md](work_packages/PROP_1_6_CM_TRANSFER.md)
   Remaining paper-faithful algebra track for Prop 1.6: packaging the HH regularity infrastructure, invoking the Gröbner transfer, and writing the final statement.

4. [work_packages/GROEBNER_CM_TRANSFER.md](work_packages/GROEBNER_CM_TRANSFER.md)
   Phase 2 packet: transfer Cohen–Macaulayness from the initial ideal quotient back to the original quotient (upper semicontinuity of depth).

## Answers And Decision Notes

- [answers/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md](answers/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md)
  Validated F2 strategy for the `p ⊄ m⁺` branch: reject Strategy I
  (induction on n); keep F2 decomposition but replace L7 with a small
  tensor-polynomial-localisation CM lemma using the backported
  polynomial-over-CM. Includes a corrected decomposition
  `R_p ≅ (A^red_{G', m} ⊗_K K[Λ ⊔ U][s_U⁻¹])_𝔓` with explicit generator
  formulas and a counterexample check (n=4, K_4).

- [answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md](answers/ANSWER_PROP_1_6_CM_WHAT_IS_NEEDED.md)
  Decision note: the paper-critical gaps are the HH bipartite CM theorem and the Gröbner transfer theorem.

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

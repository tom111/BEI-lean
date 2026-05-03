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

No active work package is currently queued for fresh-Claude dispatch.

The Graded* family refactor — `toMathlib/GradedFiniteFree.lean` and
`toMathlib/GradedRegularSop.lean` — shipped on 2026-05-03 across five
stage commits. The guide is archived at
[archive/GRADED_FINITE_FREE_REFACTOR.md](archive/GRADED_FINITE_FREE_REFACTOR.md).
Stage 0 Mathlib hunt found `LinearEquiv.isWeaklyRegular_congr` and
`Module.Basis.mapCoeffs` already in Mathlib; Stage 1 extracted the
duplicated localization-bridge helper
`localizationAtIrrelevantOfQuotientSpan_ringEquiv` (77 LOC saved);
Stage 2 added `QuotSMulTop.linearEquivQuotSpanSingleton` (6 LOC); Stage
3 pulled `aeval_finCons_eq_polynomial_aeval` and
`quotientMk_aeval_finCons_eq_aeval_coeff_zero` out of
`linearIndependent_aeval_cons_step` (3 LOC); Stage 4's high-gain swing
replaced an 85-LOC hand-built `repr_LE` in the
`finiteFree_over_mvPolynomial_of_homogeneous_regular_sop` zero branch
with a one-line `Module.Basis.mapCoeffs` call (76 LOC); Stage 5
trimmed three dead `have` blocks (10 LOC). Net: 172 LOC across both
files; `BEI.AxiomCheck` clean after every stage commit.

The largest standing LOC target — `theorem_2_1` (1848 LOC, the
biggest declaration in the repo) — shipped on 2026-05-03 across five
stage commits. The guide is
archived at
[archive/THEOREM_2_1_REFACTOR.md](archive/THEOREM_2_1_REFACTOR.md).
Five private helpers were extracted
(`cov_inr_or_inl_of_admissible_path`, `degree_monomial_mul_fij`,
`case4_remainder` / `case5_remainder`, `fij_degree_inr_eq_zero` /
`fij_degree_inl_eq_zero`); `BEI/GroebnerBasisSPolynomial.lean` shrank
from 1991 to 1455 LOC (−536, 27%). The originally proposed
"`case2_3_lt_branch` mega-helper" was deliberately skipped per the
"negative-value extraction" rule — its signature would have grown
beyond the body savings.

The next-largest LOC target — `isRemainder_fij_of_mixed_walk`
(837 LOC) — shipped on 2026-05-03 across five stage commits. The
guide is archived at
[archive/MIXED_WALK_REMAINDER_REFACTOR.md](archive/MIXED_WALK_REMAINDER_REFACTOR.md).
Eight private helpers landed across the three flagship walk theorems
(`isRemainder_fij_of_covered_walk{,_y}` and `_mixed_walk`): the
bad-vertex pickers `exists_min_bad_vertex` / `exists_max_bad_vertex`,
the algebraic identities `x_telescope_monomial_eq` /
`y_telescope_monomial_eq`, the bad-case packagers
`telescope_step_x_bad` / `telescope_step_y_bad`, the head?/getLast?
distinctness wrappers `ne_head?_of_internal` /
`ne_getLast?_of_internal`, and four `sub_add_single_*_eval_*`
Finsupp evaluators. `isRemainder_fij_of_mixed_walk` itself shrank
837 → 402 LOC; `BEI/CoveredWalks.lean` shrank 2390 → 1960 LOC
(−430, ~18%) with no axiom or statement change.

The `groebnerElement_reduced_same_endpoints` deduplication finished on
2026-05-02; the guide is archived at
[archive/GROEBNER_REDUCED_SAME_ENDPOINTS_REFACTOR.md](archive/GROEBNER_REDUCED_SAME_ENDPOINTS_REFACTOR.md).
Stages 1–2 dropped inline reinventions of `mem_internalVertices_of_ne`
and `internal_ne_getLast` from `BEI/CoveredWalks.lean`; Stage 3
extracted `endpoints_notMem_internalVertices` and used it in both the
primary target and the sister `groebnerElement_leadingMonomial_squarefree`.
`BEI/GroebnerBasis.lean` shrank from 766 → 652 LOC (the primary itself
274 → ~210) with no axiom or statement change.

The `groebner_implies_closed` deduplication finished on 2026-05-02; the
guide is archived at
[archive/GROEBNER_IMPLIES_CLOSED_REFACTOR.md](archive/GROEBNER_IMPLIES_CLOSED_REFACTOR.md).
Stages 0–2 dropped the unused `extract_b` helper, extracted
`cubic_degree` (one private lemma replacing 8 inline 9-line `degree_mul`
blocks) and `extract_cond1` / `extract_cond2` (private Finsupp lemmas
replacing the four 30-LOC `(a, b)`-extraction epilogues). Stage 3
(`cubic_witness`) was deliberately skipped: the parameterisation would
have grown rather than shrunk the proof. The four-branch proof body
shrank from 513 LOC to ~281 LOC (file 978 → 862) with no axiom or
statement change.

The Buchberger decomposition refactor finished on 2026-05-02; the guide
is archived at
[archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md](archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md).
Stage 0 split the iff into two private helpers and Stage 1 replaced the
manual k-induction with `MonomialOrder.sPolynomial_decomposition'`,
dropping `BEI/GroebnerAPI.lean` from 1209 → 850 LOC with no axiom or
statement change.

The earlier giant-decl carves (`EQUIDIM_FILE_SPLIT.md`,
`EQUIDIM_GIANT_CARVING.md`) are complete and archived. The two giant
declarations
(`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` in
`BEI/Equidim.lean` and `nilradical_nzd_map_diagSubstHom` in
`BEI/Equidim/IteratedRegularity.lean`) have been carved into thin
dispatchers plus private case helpers; statements are byte-identical
and axiom checks remain clean.

Otherwise, use `cleanup/`, `process/`, and `website/` for ongoing
maintenance work until a new formalization task appears.

## Answers And Decision Notes

There are currently no live answer memos in `guides/answers/`.

## Cleanup And Refactor Packets

Optional proof-engineering work, not on the theorem-proving critical path.

- [cleanup/PROOF_CLEANUP_INDEX.md](cleanup/PROOF_CLEANUP_INDEX.md) — index of the other cleanup packets.
- [cleanup/PATH_AND_INTERNAL_VERTEX_API.md](cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
- [cleanup/MONOMIAL_AND_FINSUPP_API.md](cleanup/MONOMIAL_AND_FINSUPP_API.md)
- [cleanup/CM_SUPPORT_REFACTOR.md](cleanup/CM_SUPPORT_REFACTOR.md)
- [cleanup/FILE_SPLITTING_PLAN.md](cleanup/FILE_SPLITTING_PLAN.md)
- [cleanup/LEAN_PERFORMANCE_TRIAGE.md](cleanup/LEAN_PERFORMANCE_TRIAGE.md)
- [cleanup/LEAN_CODE_SMELL_AUDIT.md](cleanup/LEAN_CODE_SMELL_AUDIT.md)
- [cleanup/LEAN_CODE_SMELL_WORKLIST.md](cleanup/LEAN_CODE_SMELL_WORKLIST.md)
- [cleanup/LINTER_AND_STYLE_CLEANUP.md](cleanup/LINTER_AND_STYLE_CLEANUP.md)
- [cleanup/STATUS_AND_CI_HYGIENE.md](cleanup/STATUS_AND_CI_HYGIENE.md)

## Website Plans

- [website/HOMEPAGE_MATH_CONTEXT_PLAN.md](website/HOMEPAGE_MATH_CONTEXT_PLAN.md)

## Process

- [process/STATUS_FILES_SYNC.md](process/STATUS_FILES_SYNC.md)

## Archive

Completed / superseded packets, retained for historical context only. Do not
treat any archived guide as current policy. See `guides/archive/` for the
full historical packet list — Proposition 1.6 (FULL_PROP_1_6_PLAN,
PROP_1_6_CM_TRANSFER, GROEBNER_CM_TRANSFER, GRADED_CM_*, CASE_C_*,
ROUTE_B_*, ANSWER_*); the `BEI/Equidim.lean` file split and giant
carving (EQUIDIM_FILE_SPLIT, EQUIDIM_GIANT_CARVING,
EQUIDIM_DECOMPOSITION); the F2 / HH bipartite chain (HH_*,
FINAL_CHAIN_PLAN, SESSION_*); the per-file Lean cleanup queue
(LEAN_FILE_REVIEW_QUEUE); the Cohen–Macaulay backports
(`cm_pr_26218/`, `cm_pr_28599/`, POLYNOMIAL_RING_CM_BASE_CASE,
CM_LOCALIZES, CM_PARAMETER_PREFIX_UNMIXED, DEHOMOGENIZATION_*); and
miscellaneous landed packets (EVALUATION_MAP_API,
MINIMALPRIMES_CYCLE_PERFORMANCE, COROLLARY_3_4_IMPLEMENTATION,
ANSWER_05_LEAN_PERFORMANCE_RESEARCH, NEXT_SESSION_PROMPT).

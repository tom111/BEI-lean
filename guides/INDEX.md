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

There are currently no active work packages. Recently-completed packets
live in `guides/archive/`.

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

# Guide Queue

Completed guides (deleted):
- Cor 1.3 — paper-faithful, fully proved
- Cor 3.3 — dimension formula fully proved
- PrimeDecomposition organization split — done
- GroebnerBasis organization split — done
- Cycle componentCount combinatorics (Q9, Q13, Q14, Q15) — all resolved
- Unmixed for Cor 3.7 (Q6) — `corollary_3_7_unmixed` fully proved
- Section 4 minimal primes — `ciIdealSpec_minimalPrimes` fully proved
- Corollary 3.4 — `corollary_3_4` fully proved
- Corollary 3.7 CM — `corollary_3_7_CM` fully proved
- Primary converse (ANSWER_18) — `isPrimary_of_criterion` and `isPrimary_iff` fully proved
- Monomial ideal primary decomp guide — primary iff fully proved
- Support-monomial cleanup — `Ideal.not_mem_exists_monomial_notMem` relocated as a general lemma before monomial-ideal specializations
- Squarefree monomial minimal primes — `minimalPrime_variablePairIdeal_iff` fully proved
- Variable-pair bridge — `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal` and minimal-prime transport proved
- HH equidimensionality — `minimalVertexCover_exactlyOne` and `minimalVertexCover_ncard_eq` proved
- Dimension step — `bipartiteEdgeMonomialIdeal_equidimensional` and `bipartiteEdgeMonomialIdeal_isCohenMacaulay` proved; `ringKrullDim_quotient_span_X_image` and `ringKrullDim_quotient_span_X_eq_of_card_eq` added to `toMathlib/HeightVariableIdeal.lean`

## Immediate Work Packets

- [ANSWER_CUTVERTEX_PRESERVED_SORRY.md](ANSWER_CUTVERTEX_PRESERVED_SORRY.md) — current active packet: helper-first plan for the `closedGraph_cutVertex_preserved_of_erase` sorry
- [PROP_1_6_EQUIDIM_BLOCKER.md](PROP_1_6_EQUIDIM_BLOCKER.md) — broader blocker context for the direct equidimensionality route
- [PROP_1_6_CM_TRANSFER.md](PROP_1_6_CM_TRANSFER.md) — secondary paper-faithful algebra track; not the active next packet unless explicitly chosen

## Current Proposition 1.6 State

There are now two distinct unfinished tracks:

- direct equidimensional surrogate route:
  `closedGraph_cutVertex_preserved_of_erase` in `BEI/PrimeDecompositionDimension.lean`
- paper-faithful CM-transfer route:
  `cm_transfer_initialIdeal` in `BEI/CohenMacaulay.lean`

The current plan is:

- first finish Proposition 1.6 under the repo’s local equidimensional surrogate;
- then refactor names/docs so the repo stops overclaiming depth-based
  Cohen-Macaulayness;
- separately keep the paper-faithful CM track visible as future work.

Do not blur those two endpoints.

## CM Reference Notes

These are not first-line work packets.

- [ANSWER_05_COHEN_MACAULAY_FOUNDATION.md](ANSWER_05_COHEN_MACAULAY_FOUNDATION.md) — CM foundations and honest scope
- [PROP_1_6_DIRECT_EQUIDIMENSIONALITY.md](PROP_1_6_DIRECT_EQUIDIMENSIONALITY.md) — track overview for the direct surrogate route
- [CM_CODEBASE_RESEARCH_MONOMIAL_IDEAL.md](CM_CODEBASE_RESEARCH_MONOMIAL_IDEAL.md) — what the local CM/PR codebase does and does not provide for the monomial-ideal step
- ~~SQUAREFREE_MONOMIAL_MINIMAL_PRIMES~~ — done: `minimalPrime_variablePairIdeal_iff` fully proved in `toMathlib/SquarefreeMonomialPrimes.lean`
- [cm_pr_26218/](cm_pr_26218/) — Mathlib CM PR backport / import plan

## Dormant / Background

- [ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md) — not on the active critical path

## Cleanup / Refactor References

- [ADMISSIBLE_PATHS_REFACTOR.md](ADMISSIBLE_PATHS_REFACTOR.md) — reduce duplicated split-path machinery in `BEI/AdmissiblePaths.lean` without changing the mathematics
- [INFRA_LINTER_PACKET_01.md](INFRA_LINTER_PACKET_01.md) — concrete cleanup packet for `PrimeIdeals`, `GraphProperties`, and `CoveredWalks` after the code-review sweep
- [PROOF_CLEANUP_INDEX.md](PROOF_CLEANUP_INDEX.md) — index of proof-cleanup guides
- [PUBLIC_THEOREM_LAYER.md](PUBLIC_THEOREM_LAYER.md)
- [EVALUATION_MAP_API.md](EVALUATION_MAP_API.md)
- [PATH_AND_INTERNAL_VERTEX_API.md](PATH_AND_INTERNAL_VERTEX_API.md)
- [MONOMIAL_AND_FINSUPP_API.md](MONOMIAL_AND_FINSUPP_API.md)
- [FILE_SPLITTING_PLAN.md](FILE_SPLITTING_PLAN.md)
- [LINTER_AND_STYLE_CLEANUP.md](LINTER_AND_STYLE_CLEANUP.md)
- [STATUS_FILES_SYNC.md](STATUS_FILES_SYNC.md)

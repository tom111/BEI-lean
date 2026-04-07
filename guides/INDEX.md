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

## Immediate Work Packets

- [PROP_1_6_DIMENSION_STEP.md](PROP_1_6_DIMENSION_STEP.md) — next Proposition 1.6 packet: convert equal-cardinality of HH minimal vertex covers into equal quotient dimensions for the corresponding minimal primes
- [PROP_1_6_COHEN_MACAULAY.md](PROP_1_6_COHEN_MACAULAY.md) — primary remaining paper endpoint: Proposition 1.6 CM branch and its remaining external algebraic inputs

## Longer-Horizon CM Packet

The Proposition 1.6 branch is still larger than a one-lemma task. The reference notes below record the main strategic splits inside that program.

## CM Reference Notes

These are not first-line work packets, but they contain important strategic context.

- [ANSWER_05_COHEN_MACAULAY_FOUNDATION.md](ANSWER_05_COHEN_MACAULAY_FOUNDATION.md) — CM foundations and honest scope
- [ANSWER_16_PROP_1_6_EQUIDIMENSIONALITY.md](ANSWER_16_PROP_1_6_EQUIDIMENSIONALITY.md) — backup direct route for Proposition 1.6
- [ANSWER_17_PROP_1_6_STRATEGY.md](ANSWER_17_PROP_1_6_STRATEGY.md) — why the paper route should still be preferred
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

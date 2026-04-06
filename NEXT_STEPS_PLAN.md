# Next Steps Plan for the BEI Formalization

## Purpose

This is a current continuation plan for the repository, written for humans and worker
agents who need to know what the next mathematically meaningful tasks are.

The goal is not just to remove `sorry`s. The goal is to finish the remaining paper
endpoints while keeping the theorem statements, status files, and public blueprint in
sync with the actual code.


## Current Situation

The project already has the main Gröbner-basis and prime-decomposition backbone of the
paper:

- Theorem 1.1
- Theorem 2.1
- Corollary 2.2
- Lemma 3.1
- Theorem 3.2
- Corollary 3.3
- Proposition 3.8
- Corollary 3.9

The remaining work is now concentrated in two branches:

1. the Cohen–Macaulay branch;
2. Section 4.


## Priority 1: Finish the Cohen–Macaulay Branch Honestly

The CM branch no longer lacks a definition. It now uses the local working definition in:

- `toMathlib/CohenMacaulay/Defs.lean`

But the main CM-dependent theorems are still open:

- `BEI/CohenMacaulay.lean`
  - `prop_1_6`
- `BEI/PrimeDecompositionDimension.lean`
  - `corollary_3_4`
- `BEI/PrimeDecomposition.lean`
  - `corollary_3_7_CM`

The branch has nevertheless moved materially:

- `complete_is_CM` is proved in `BEI/CohenMacaulay.lean`
- `path_is_CM` is proved in `BEI/PrimeDecompositionDimension.lean`
- `prop_1_6_herzogHibi` isolates the graph-combinatorial reduction from the paper
- the initial ideal, variable shift, and bipartite edge monomial ideal are now packaged in `BEI/CohenMacaulay.lean`
- `rename_yPredVar_monomialInitialIdeal` proves the ideal-level transport to the shifted bipartite edge ideal
- quotient-dimension and equidimensionality lemmas now exist for the local CM route

### Working discipline

- treat the current local CM notion as a BEI-specific working foundation, not as full
  upstream CM theory;
- do not overclaim the CM branch in public docs;
- keep the proofs tied to the exact paper statements when possible.

### Supporting guides

- `guides/PROP_1_6_COHEN_MACAULAY.md`
- `guides/COR_3_4_CM_DIMENSION.md`
- `guides/ANSWER_05_COHEN_MACAULAY_FOUNDATION.md`
- `guides/ANSWER_16_PROP_1_6_EQUIDIMENSIONALITY.md`
- `guides/ANSWER_17_PROP_1_6_STRATEGY.md`
- `guides/cm_pr_26218/`


## Priority 2: Keep the Meta Files Honest

Once the remaining theorems move again, the first failure mode will be status drift.

The main files that must stay synchronized are:

- `TODO.md`
- `FORMALIZATION_MAP.md`
- `CLAUDE.md`
- `docs/`

Use:

- `guides/STATUS_FILES_SYNC.md`

as the standing maintenance rule.


## Priority 3: Proof-Engineering Cleanup

The repository is mathematically stronger than its current proof presentation.

The main cleanup targets remain:

- `BEI/GroebnerBasisSPolynomial.lean`
- `BEI/GroebnerBasis.lean`
- Section 3 file boundaries and theorem packaging
- lint / style cleanup

These are secondary to finishing the remaining paper endpoints, but they should continue
whenever a proof becomes stable enough to refactor safely.


## Priority 4: Section 4

Section 4 should wait until:

- the Section 3 endpoints are stable;
- the CM branch is at least honestly scoped;
- the project has a clear theorem map for the earlier sections.

Once that is true, the natural next stage is:

1. define the CI-ideal side cleanly;
2. identify it with the BEI constructions;
3. transfer the already formalized algebraic results.


## Summary

If choosing the next task today:

1. continue the CM branch from the new local CM definition;
2. focus first on the two remaining external algebraic inputs for `prop_1_6`, since Corollary 3.4 and Corollary 3.7 CM both sit downstream of the same story;
3. keep the status files and blueprint aligned as the code changes;
4. start Section 4 only once the CM branch is honestly scoped.

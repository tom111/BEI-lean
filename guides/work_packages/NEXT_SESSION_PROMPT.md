# PROPOSITION 1.6 IS FULLY AXIOM-CLEAN (2026-04-22)

Status as of today: `proposition_1_6` in `BEI/Proposition1_6.lean`
depends only on `{propext, Classical.choice, Quot.sound}` — **no
`sorryAx`**.

This was the primary goal of the finite-free Case C route. The route
is now fully closed through all four steps:

| Step | Theorem | File |
|------|---------|------|
| Phase 1 / BH 1.5.6 | `GradedAssociatedPrime.isAssociatedPrime_isHomogeneous` | `toMathlib/GradedAssociatedPrime.lean` |
| A (single-step) | `GradedRegularSop.exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos` | `toMathlib/GradedRegularSop.lean` |
| A (full iter) | `GradedRegularSop.exists_homogeneous_regular_sop_of_cm_at_irrelevant` | same |
| B1 | `GradedFiniteFree.mul_left_injective_of_notMem_irrelevant` | `toMathlib/GradedFiniteFree.lean` |
| B2a | `irrelevant_isNilpotent_of_isArtinianRing_atIrrelevant` | same |
| B2b | `finite_over_K_of_isArtinianRing_atIrrelevant` | same |
| C.b | `exists_homogeneous_basis_of_finite_graded` | same |
| C helper | `exists_homogeneous_decomposition_mem_span_range` | same |
| C surj | `span_aeval_eq_top_of_homogeneous_basis_lift` | same |
| C inj base | `linearIndependent_aeval_fin_zero` | same |
| C inj step | `linearIndependent_aeval_cons_step` | same |
| C inj full | `linearIndependent_aeval_of_basis_lift` | same |
| C main | `finiteFree_over_mvPolynomial_of_homogeneous_regular_sop` | same |
| D | `isCohenMacaulayRing_of_module_free_of_mvPolynomial` | same |
| D (Flat) | `isCohenMacaulayRing_of_module_flat_of_mvPolynomial` | same |
| Assembly | `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree` | `toMathlib/GradedRegularSop.lean` |
| Graded L-to-G CM | `GradedCM.isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant` | `toMathlib/GradedCM.lean` |
| BEI R1 framework | `BEI.GroebnerDeformation.groebnerDeformation_cm_transfer` | `BEI/GroebnerDeformation.lean` |
| Paper Prop 1.6 | `proposition_1_6`, `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` | `BEI/Proposition1_6.lean` |

All axiom-clean.

## Verification

```
$ lake build        # succeeds
$ lake env lean <<< '#print axioms proposition_1_6'
  propext, Classical.choice, Quot.sound
$ lake env lean <<< '#print axioms binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm'
  propext, Classical.choice, Quot.sound
```

## Residual sorries

Non-critical, dormant:
- `toMathlib/HeightAdditivity.lean` — 2 sorries, dormant infrastructure, not on paper path.
- `Supplement/RauhApproach.lean` — 2 sorries, archived.

These have been tolerated through the entire project and remain
irrelevant to paper-faithful Proposition 1.6.

## Possible next-session targets

1. **Corollary 3.4 (full paper statement)**. Currently only the
   equidimensional surrogate `corollary_3_4_equidim` is proved;
   the full "CM implies dim = n + c" statement can now be closed via
   the axiom-clean `proposition_1_6_dim_formula`. Expected LOC: ~50.

2. **Clean up**. The Step C proof in `toMathlib/GradedFiniteFree.lean`
   added ~1200 LOC. Review for simplifications, dedupe against
   Mathlib. Run `simplify` and `proof-golfer` subagents over the
   file. Expected reduction: 20–30%.

3. **Retire dormant sorries**. `toMathlib/HeightAdditivity.lean`
   contains 2 dormant sorries; these are not critical but landing
   them is a natural follow-up.

4. **Upstream to Mathlib**. Several of the new theorems are genuinely
   general (graded local-to-global CM, finite-free over polynomial
   parameter subring, etc.) and would fit as Mathlib contributions.
   Investigate.

## Memory anchors

- `project_step_a_full.md` — progress summary up to 2026-04-22.
- `project_bh156_done.md` — BH 1.5.6 and early Step C scoping.
- `guides/answers/ANSWER_CASE_C_FINITE_FREE_ROUTE.md` — original math strategy.

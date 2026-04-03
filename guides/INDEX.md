# Remaining Statement Guides

These guides break the remaining paper statements into isolated Lean tasks.

Use them in this order:

1. [COR_1_3_EXACT_STATEMENT.md](/home/tom/BEI-lean/guides/COR_1_3_EXACT_STATEMENT.md)
2. [COR_3_3_DIMENSION.md](/home/tom/BEI-lean/guides/COR_3_3_DIMENSION.md)
3. [COR_3_7_FULL_EQUIVALENCE.md](/home/tom/BEI-lean/guides/COR_3_7_FULL_EQUIVALENCE.md)
4. [PROP_1_6_COHEN_MACAULAY.md](/home/tom/BEI-lean/guides/PROP_1_6_COHEN_MACAULAY.md)
5. [COR_3_4_CM_DIMENSION.md](/home/tom/BEI-lean/guides/COR_3_4_CM_DIMENSION.md)
6. [SECTION_4_CI_IDEALS.md](/home/tom/BEI-lean/guides/SECTION_4_CI_IDEALS.md)

Question-response guides:

- [ANSWER_01_DIMENSION_OF_QUOTIENT_BY_PRIME.md](/home/tom/BEI-lean/guides/ANSWER_01_DIMENSION_OF_QUOTIENT_BY_PRIME.md)
- [ANSWER_02_RADICAL_IDEAL_DIMENSION_FORMULA.md](/home/tom/BEI-lean/guides/ANSWER_02_RADICAL_IDEAL_DIMENSION_FORMULA.md)
- [ANSWER_03_PRIMALITY_OF_SUM_IN_DISJOINT_VARIABLES.md](/home/tom/BEI-lean/guides/ANSWER_03_PRIMALITY_OF_SUM_IN_DISJOINT_VARIABLES.md)
- [ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md](/home/tom/BEI-lean/guides/ANSWER_04_HEIGHT_ADDITIVITY_REPAIR.md)
- [ANSWER_05_COHEN_MACAULAY_FOUNDATION.md](/home/tom/BEI-lean/guides/ANSWER_05_COHEN_MACAULAY_FOUNDATION.md)
- [ANSWER_06_UNMIXED_FOR_COR_3_7.md](/home/tom/BEI-lean/guides/ANSWER_06_UNMIXED_FOR_COR_3_7.md)
- [ANSWER_07_CATENARY_FOR_MVPOLYNOMIAL.md](/home/tom/BEI-lean/guides/ANSWER_07_CATENARY_FOR_MVPOLYNOMIAL.md)
- [ANSWER_08_CHAIN_ABOVE_PRIME_COMPONENT.md](/home/tom/BEI-lean/guides/ANSWER_08_CHAIN_ABOVE_PRIME_COMPONENT.md)
- [ANSWER_09_CYCLE_COMPONENTCOUNT_COMBINATORICS.md](/home/tom/BEI-lean/guides/ANSWER_09_CYCLE_COMPONENTCOUNT_COMBINATORICS.md)

Why this order:

- `Cor 1.3` is a statement-fidelity cleanup and should be cheap compared to the algebra.
- `Cor 3.3` is the main remaining Section 3 theorem and the best non-CM target.
- `Cor 3.7` depends partly on `Cor 3.3` and exposes the missing "unmixed" branch.
- `Prop 1.6`, `Cor 3.4`, and the CM half of `Cor 3.7` all depend on a real
  Cohen–Macaulay foundation, not the current placeholder.
- Section 4 should wait until the algebraic backbone and paper-faithful status are stable.

General rule:

- If a guide says "first isolate the missing abstract theorem", do that before trying
  to brute-force the final paper statement inside the BEI file.
- If a guide touches Cohen–Macaulayness, do not build on the current placeholder
  `IsCohenMacaulay := sorry` as if it were a finished formalization.

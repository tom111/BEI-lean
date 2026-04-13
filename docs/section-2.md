---
title: Section 2
---

# Section 2: Reduced Gröbner Basis and Radicality

Section 2 proves that the quadratic generators give a reduced Gröbner basis and
then deduces that the binomial edge ideal is radical.

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Theorem 2.1 | `theorem_2_1`, `theorem_2_1_reduced`, `theorem_2_1_isReducedGroebnerBasis` | [GroebnerBasisSPolynomial.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasisSPolynomial.lean), [GroebnerBasis.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasis.lean) | Equivalent, split |
| Corollary 2.2 | `corollary_2_2` | [Radical.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Radical.lean) | Exact |

## Notes

The main theorem is split across two files:

- `theorem_2_1` for the Gröbner-basis property;
- `theorem_2_1_reduced` for reducedness;
- and `theorem_2_1_isReducedGroebnerBasis` as the paper-facing wrapper.

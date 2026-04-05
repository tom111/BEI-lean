---
title: Section 2
---

# Section 2: Reduced Gröbner Basis and Radicality

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Theorem 2.1 | `theorem_2_1`, `theorem_2_1_reduced`, `theorem_2_1_isReducedGroebnerBasis` | [GroebnerBasisSPolynomial.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasisSPolynomial.lean), [GroebnerBasis.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasis.lean) | Equivalent, split |
| Corollary 2.2 | `corollary_2_2` | [Radical.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Radical.lean) | Exact |

## Notes

The mathematics of Section 2 is substantially in place.

The main paper theorem is represented in Lean by a split proof architecture:

- `theorem_2_1` for the Gröbner-basis property;
- `theorem_2_1_reduced` for reducedness;
- and `theorem_2_1_isReducedGroebnerBasis` as the paper-facing wrapper.

The code organization is still being cleaned up, but the theorem-level story is already
in place.

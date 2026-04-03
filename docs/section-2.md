---
title: Section 2
---

# Section 2: Reduced Gröbner Basis and Radicality

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Theorem 2.1 | `theorem_2_1`, `theorem_2_1_reduced` | [GroebnerBasis.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasis.lean) | Equivalent, split |
| Corollary 2.2 | `corollary_2_2` | [Radical.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Radical.lean) | Exact |

## Notes

The mathematics of Section 2 is substantially in place.

The main paper theorem is represented in Lean by a split packaging:

- one theorem for the Gröbner-basis property;
- and one theorem for reducedness.

This is mathematically faithful, but not yet packaged as a single paper-style endpoint.

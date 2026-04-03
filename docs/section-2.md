---
title: Section 2
---

# Section 2: Reduced Gröbner Basis and Radicality

## Theorem map

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Theorem 2.1 | `theorem_2_1`, `theorem_2_1_reduced` | `GroebnerBasis.lean` | Equivalent, split | Gröbner-basis-ness and reducedness are proved separately |
| Corollary 2.2 | `corollary_2_2` | `Radical.lean` | Exact | `J_G` is radical |

## Notes

The mathematics of Section 2 is largely in place, but the main file
[`BEI/GroebnerBasis.lean`](/home/tom/BEI-lean/BEI/GroebnerBasis.lean) is still carrying
too much low-level proof detail in one place.

Relevant cleanup guides:

- [`guides/PUBLIC_THEOREM_LAYER.md`](/home/tom/BEI-lean/guides/PUBLIC_THEOREM_LAYER.md)
- [`guides/PATH_AND_INTERNAL_VERTEX_API.md`](/home/tom/BEI-lean/guides/PATH_AND_INTERNAL_VERTEX_API.md)
- [`guides/MONOMIAL_AND_FINSUPP_API.md`](/home/tom/BEI-lean/guides/MONOMIAL_AND_FINSUPP_API.md)
- [`guides/FILE_SPLITTING_PLAN.md`](/home/tom/BEI-lean/guides/FILE_SPLITTING_PLAN.md)


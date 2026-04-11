---
title: Section 1
---

# Section 1: Closed Graphs and Quadratic Gröbner Bases

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Theorem 1.1 | `theorem_1_1` | [ClosedGraphs.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/ClosedGraphs.lean) | Exact |
| Proposition 1.2 | `prop_1_2` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Corollary 1.3 | `cor_1_3` and related wrappers | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Proposition 1.4 | `prop_1_4` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Equivalent |
| Proposition 1.5 | `prop_1_5` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Proposition 1.6 | `prop_1_6_equidim`, `prop_1_6_herzogHibi`, `sum_XY_isSMulRegular_mod_diagonalSum` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean), [Equidim.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Equidim.lean) | Partial |

## Notes

### Theorem 1.1

This is the central theorem of Section 1: the quadratic generators form a Gröbner basis
if and only if the graph is closed.

### Corollary 1.3

This is the main Section 1 packaging subtlety.

The paper states, informally:

> A bipartite graph is closed if and only if it is a line.

The Lean development now packages the result in a paper-faithful connected-graph form,
while making the connectedness and labeling subtleties explicit.

### Examples 1.7

The supporting Section 1 examples are formalized at the local equidimensional surrogate level:

- Example 1.7(a): `complete_isEquidim` in `BEI/Equidim.lean`
- Example 1.7(b): `path_isEquidim` in `BEI/PrimeDecompositionDimension.lean`

### Proposition 1.6

The Proposition 1.6 branch is only partially formalized.

The current state is as follows.

The theorem from the paper is not yet fully formalized.

The full depth-based Cohen-Macaulay theory used in the paper is not available in the
pinned Mathlib version for this project. Relevant upstream work exists, and the main
reference for this repository is Mathlib PR
[`#26218`](https://github.com/leanprover-community/mathlib4/pull/26218).

As a partial substitute, the current code also studies an equidimensional variant,
implemented via the temporary local definition in
`toMathlib/Equidim/Defs.lean`.

What is already in place:

- the graph-combinatorial reduction from the paper;
- the monomial initial ideal and variable-shift reduction;
- the Herzog-Hibi bipartite-graph side;
- the iterated HH regularity theorem `sum_XY_isSMulRegular_mod_diagonalSum`;
- the local equidimensional stand-in;
- and a direct proof of the resulting equidimensional surrogate theorem.

What is still missing:

- the actual depth-based Cohen-Macaulay statement from the paper;
- the final HH-side real-CM packaging theorem built on the finished regularity infrastructure;
- the separate paper-faithful Gröbner CM transfer theorem;
- and the full Cohen-Macaulay theory needed to count the paper as fully formalized.

So there are currently two distinct goals:

- keep the proved equidimensional surrogate in place;
- later replace that stand-in with a real Cohen-Macaulay formalization, likely via
  newer Mathlib or a backport from Mathlib PR `#26218`.

This page therefore does not claim that either Proposition 1.6 itself or the paper's
full Cohen-Macaulay statement has been completed yet.

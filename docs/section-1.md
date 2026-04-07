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
| Proposition 1.6 | `prop_1_6`, `cm_transfer_initialIdeal` | [CohenMacaulay.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CohenMacaulay.lean) | Partial |

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

The supporting Cohen–Macaulay examples from Section 1 are now partly formalized:

- Example 1.7(a): `complete_is_CM` in `BEI/CohenMacaulay.lean`
- Example 1.7(b): `path_is_CM` in `BEI/PrimeDecompositionDimension.lean`

### Proposition 1.6

The Proposition 1.6 branch is now formalized up to the limit of the current local
definition of Cohen-Macaulayness.
The reduction chain is in place, but the theorem is still not finished.

What is already in place:

- the graph-combinatorial reduction from the paper;
- the monomial initial ideal and variable-shift reduction;
- the Herzog-Hibi bipartite-graph side;
- and a local equidimensional surrogate for Cohen-Macaulayness.

What is still missing:

- the last unfinished step in the current Proposition 1.6 branch;
- the full depth-based Cohen-Macaulay theory needed to count the paper as fully
  formalized;
- in the current code, this missing step is isolated in
  `cm_transfer_initialIdeal`.

So the Lean theorem layer is very close to complete, but this page does not claim that
either the current Proposition 1.6 branch or the paper's full Cohen-Macaulay statement
has been finished yet.

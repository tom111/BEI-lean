---
title: Section 1
---

# Section 1: Closed Graphs and Quadratic Gröbner Bases

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Theorem 1.1 | `theorem_1_1` | [ClosedGraphs.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/ClosedGraphs.lean) | Exact |
| Proposition 1.2 | `prop_1_2` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Corollary 1.3 | `cor_1_3` and related wrappers | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Mixed |
| Proposition 1.4 | `prop_1_4` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Equivalent |
| Proposition 1.5 | `prop_1_5` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Proposition 1.6 | `prop_1_6` | [CohenMacaulay.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CohenMacaulay.lean) | Blocked |

## Notes

### Theorem 1.1

This is the central theorem of Section 1: the quadratic generators form a Gröbner basis
if and only if the graph is closed.

### Corollary 1.3

This is the main Section 1 packaging subtlety.

The paper states, informally:

> A bipartite graph is closed if and only if it is a line.

The Lean development formalizes the structural content and tracks the connectedness and
labeling subtleties explicitly.

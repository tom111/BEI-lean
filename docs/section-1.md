---
title: Section 1
---

# Section 1: Closed Graphs and Quadratic Gröbner Bases

## Theorem map

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Theorem 1.1 | `theorem_1_1` | `ClosedGraphs.lean` | Exact | Generators form a Gröbner basis iff the graph is closed |
| Proposition 1.2 | `prop_1_2` | `GraphProperties.lean` | Exact | Closed implies chordal and claw-free |
| Corollary 1.3 | `cor_1_3` and related wrappers | `GraphProperties.lean` | Mixed | Structural content is formalized; packaging still needs review |
| Proposition 1.4 | `prop_1_4` | `GraphProperties.lean` | Equivalent | Uses shortest walks / directedness packaging |
| Proposition 1.5 | `prop_1_5` | `GraphProperties.lean` | Exact | Unique minimal closed supergraph |
| Proposition 1.6 | `prop_1_6` | `CohenMacaulay.lean` | Blocked | Depends on real CM infrastructure |

## Notes

### Corollary 1.3

This is the most important Section 1 fidelity issue.

The paper says, informally:

> A bipartite graph is closed iff it is a line.

The Lean development currently formalizes the structural consequence and documents the
connectedness / labeling subtlety. This is mathematically honest, but it should continue
to be tracked explicitly as a packaging issue.

Relevant guide:

- [`guides/COR_1_3_EXACT_STATEMENT.md`](/home/tom/BEI-lean/guides/COR_1_3_EXACT_STATEMENT.md)


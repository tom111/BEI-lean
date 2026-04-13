---
title: Section 1
---

# Section 1: Closed Graphs and Quadratic Gröbner Bases

Section 1 proves that closed graphs are exactly the graphs whose quadratic
binomials form a Gröbner basis. It also records the main graph-theoretic
consequences and the closure construction.

## Theorem map

| Paper result | Lean declaration(s) | Lean file | Fidelity |
|---|---|---|---|
| Theorem 1.1 | `theorem_1_1` | [ClosedGraphs.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/ClosedGraphs.lean) | Exact |
| Proposition 1.2 | `prop_1_2` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Corollary 1.3 | `cor_1_3` and related wrappers | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Proposition 1.4 | `prop_1_4` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Equivalent |
| Proposition 1.5 | `prop_1_5` | [GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean) | Exact |
| Proposition 1.6 | `prop_1_6_equidim`, `prop_1_6_herzogHibi`, `sum_XY_isSMulRegular_mod_diagonalSum` | [PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean), [Equidim.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Equidim.lean) | Partial |

## Paper vs Lean

Each card below places the paper statement next to the current Lean theorem.

<div class="theorem-stack">
  {% assign section1_cards = "theorem_1_1,prop_1_2,cor_1_3,prop_1_4,prop_1_5,prop_1_6" | split: "," %}
  {% for key in section1_cards %}
    {% assign thm = site.data.section1[key] %}
    {% include theorem_compare.html item=thm %}
  {% endfor %}
</div>

## Notes

### Theorem 1.1

Closed graphs are characterized by the quadratic generators of the binomial
edge ideal forming a Gröbner basis.

### Corollary 1.3

The Lean statement keeps the connected-graph hypothesis explicit and spells out
the path-graph conclusion directly.

### Examples 1.7

The supporting examples are formalized at the equidimensional level:

- Example 1.7(a): `complete_isEquidim` in `BEI/Equidim.lean`
- Example 1.7(b): `path_isEquidim` in `BEI/PrimeDecompositionDimension.lean`

### Proposition 1.6

This branch is still partial.

Already proved:

- the graph-combinatorial reduction from the paper;
- the monomial initial ideal and variable-shift reduction;
- the Herzog-Hibi bipartite-graph side;
- the iterated HH regularity theorem `sum_XY_isSMulRegular_mod_diagonalSum`;
- a direct equidimensional substitute in `PrimeDecompositionDimension.lean`;
- and most of the real Cohen–Macaulay infrastructure behind the HH side.

Still open:

- the actual depth-based Cohen-Macaulay statement from the paper;
- the last HH-side global Cohen–Macaulay step in `Equidim.lean`;
- the separate paper-faithful Gröbner CM transfer theorem;
- and therefore the full paper statement of Proposition 1.6.

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
| Proposition 1.6 | `proposition_1_6`, `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm`, `prop_1_6_herzogHibi`, `monomialInitialIdeal_isCohenMacaulay` | [Proposition1_6.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Proposition1_6.lean), [GroebnerDeformation.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerDeformation.lean), [Equidim.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Equidim.lean) | Exact |

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

The supporting examples now split by strength:

- Example 1.7(a): `complete_isEquidim` in `BEI/Equidim.lean`
- Example 1.7(b): `pathGraph_binomialEdgeIdeal_isCohenMacaulay` and `pathGraph_binomialEdgeIdeal_ringKrullDim` in `BEI/Proposition1_6.lean`
- The direct surrogate route is also still available as `path_isEquidim` in `BEI/PrimeDecompositionDimension.lean`

### Proposition 1.6

The main declaration is `proposition_1_6` in `BEI/Proposition1_6.lean`.
Its proof is assembled in the same order as the paper's strategy:

- `prop_1_6_herzogHibi` packages the graph hypotheses into the HH bipartite conditions;
- `monomialInitialIdeal_isCohenMacaulay` proves the monomial-side CM theorem;
- `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` and `groebnerDeformation_cm_transfer` carry CM back from the initial ideal to `J_G`;
- and the direct equidimensional route in `PrimeDecompositionDimension.lean`
  remains available as a separate surrogate argument, not as the main theorem
  recorded on this page.

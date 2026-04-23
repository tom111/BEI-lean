---
title: Section 2
---

# Section 2: Reduced Gröbner Basis and Radicality

Section 2 upgrades the Section 1 result: the quadratic generators form a
*reduced* Gröbner basis. Since the leading monomials are then squarefree,
$J_G$ is a radical ideal.

## Theorem map

| Paper result | Lean declaration(s) | Lean file |
|---|---|---|
| Theorem 2.1 | `theorem_2_1`, `theorem_2_1_reduced`, `theorem_2_1_isReducedGroebnerBasis` | [GroebnerBasisSPolynomial.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasisSPolynomial.lean), [GroebnerBasis.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasis.lean) |
| Corollary 2.2 | `corollary_2_2` | [Radical.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Radical.lean) |

Theorem 2.1 is packaged as three Lean declarations: `theorem_2_1` for the
Gröbner-basis property, `theorem_2_1_reduced` for reducedness, and
`theorem_2_1_isReducedGroebnerBasis` as the paper-facing wrapper.

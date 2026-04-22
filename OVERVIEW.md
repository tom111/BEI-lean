# BEI Formalization: Executive Summary

## What This Repository Covers

This is a Lean 4 / Mathlib formalization of Herzog, Hibi, Hreinsdóttir, Kahle, and
Rauh, "Binomial edge ideals and conditional independence statements" (2010).

The project already formalizes the main algebraic backbone of the paper:

- Theorem 1.1 on closed graphs and quadratic Gröbner bases
- Theorem 2.1 on the admissible-path Gröbner basis
- Corollary 2.2 on radicality
- Lemma 3.1 and Theorem 3.2 on the prime components `P_S(G)`
- Corollary 3.3 on the Krull-dimension formula
- Corollary 3.4 on the equidimensional surrogate dimension consequence
- Proposition 1.6 on the paper-faithful Cohen–Macaulay criterion
- Proposition 3.8 and Corollary 3.9 on minimal primes
- Corollary 3.7, including the equidimensional surrogate branch for cycle graphs
- the Section 4 binary-output CI ideal = BEI bridges and transferred radicality / prime decomposition / minimal-prime results

It also now contains the basic equidimensional surrogate examples corresponding to the paper's Cohen–Macaulay discussion:

- the complete graph case
- the path graph case, including the paper-faithful CM theorem and dimension formula

The remaining paper endpoints are concentrated in:

- the full Corollary 3.4 Cohen–Macaulay statement (beyond the equidimensional surrogate)
- the full Corollary 3.7 Cohen–Macaulay branch for cycle graphs


## Mathematical Setup

The polynomial ring is modeled as `MvPolynomial (V ⊕ V) K`, where `Sum.inl i` and
`Sum.inr i` represent the variables `x_i` and `y_i`.

For a graph `G`, the binomial edge ideal is:

`J_G = ⟨x_i y_j - x_j y_i : {i,j} ∈ E(G), i < j⟩`.

The formalization follows the paper closely, but where Lean packages a theorem
differently, the status files record whether the result is exact, equivalent, partial,
or still open.


## Current Structure

The main mathematical files are now split roughly as follows:

- `BEI/ClosedGraphs.lean` — Theorem 1.1
- `BEI/GroebnerBasisSPolynomial.lean` — Buchberger / S-polynomial proof of Theorem 2.1
- `BEI/GroebnerBasis.lean` — reducedness and paper-facing Theorem 2.1 wrapper
- `BEI/Radical.lean` — Corollary 2.2
- `BEI/PrimeIdeals.lean` — prime components and the height formula
- `BEI/PrimeDecomposition.lean` — Theorem 3.2 and Proposition 3.6
- `BEI/PrimeDecompositionDimension.lean` — Corollaries 3.3, the equidimensional surrogate version of Corollary 3.4, the equidimensional surrogate branch of Corollary 3.7, and the direct equidimensional Proposition 1.6 route
- `BEI/MinimalPrimes.lean` — Proposition 3.8, Corollary 3.9, and Corollary 3.7 unmixed branch
- `BEI/Proposition1_6.lean` — the paper-faithful Proposition 1.6 theorem, its specialized dimension formula, and the path-graph CM example
- `BEI/CIIdeals.lean` — Section 4 binary-output CI ideals, both bridge theorems, and transferred radicality / prime decomposition / minimal-prime theorems
- `BEI/Equidim.lean` — the local equidimensional surrogate API, HH bipartite-graph infrastructure, the monomial-side CM theorem used in Proposition 1.6, and the complete-graph equidimensional example
- `BEI/GroebnerDeformation.lean` — the paper-faithful Gröbner deformation CM transfer used to pass from the initial ideal back to `J_G`

Generic or backported infrastructure lives in `toMathlib/`, including
`toMathlib/Equidim/Defs.lean`.

Supplementary archived code that is outside the main paper formalization lives in
`Supplement/`, currently including an alternative Rauh-style route to Theorem 2.1.


## Current Status

The project is no longer in the “infrastructure only” stage. The main question is now
how to finish the remaining paper endpoints cleanly and document them accurately.

At the time of this summary:

- the non-CM Section 3 backbone is in place, including the unmixed branch of Corollary 3.7;
- the Section 3 equidimensional surrogate consequences `corollary_3_4_equidim` and `corollary_3_7_equidim` are proved over the local equidimensional definition;
- Section 4 now has the binary-output single-statement bridge, specification bridge, and transferred radicality / prime decomposition / minimal-prime theorems in `BEI/CIIdeals.lean`;
- the paper-faithful Proposition 1.6 theorem `proposition_1_6` is now fully proved and axiom-clean;
- the direct equidimensional Proposition 1.6 route is still available as a separate BEI-specific surrogate argument;
- the HH regularity infrastructure in `BEI/Equidim.lean` now reaches the iterated theorem `sum_XY_isSMulRegular_mod_diagonalSum`;
- the remaining paper-level gaps are the full Corollary 3.4 and Corollary 3.7 Cohen–Macaulay statements, which are still represented by equidimensional surrogates.


## Where To Look Next

For theorem-by-theorem status:

- see `FORMALIZATION_MAP.md`
- see `TODO.md`

For the public blueprint:

- see `docs/`
- or the published site at `https://tom111.github.io/BEI-lean/`

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
- Proposition 3.8 and Corollary 3.9 on minimal primes

The remaining paper endpoints are concentrated in:

- the Cohen–Macaulay branch (Proposition 1.6, Corollary 3.4, Corollary 3.7 CM)
- Section 4 on CI-ideals


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
- `BEI/PrimeDecomposition.lean` — Theorem 3.2, Proposition 3.6, Corollary 3.7 prime / CM branch
- `BEI/PrimeDecompositionDimension.lean` — Corollaries 3.3 and 3.4
- `BEI/MinimalPrimes.lean` — Proposition 3.8, Corollary 3.9, and Corollary 3.7 unmixed branch
- `BEI/CohenMacaulay.lean` — Proposition 1.6 and the CM examples

Generic or backported infrastructure lives in `toMathlib/`, including
`toMathlib/CohenMacaulay/Defs.lean`.


## Current Status

The project is no longer in the “infrastructure only” stage. The main question is now
how to finish the remaining paper endpoints cleanly and document them accurately.

At the time of this summary:

- the non-CM Section 3 backbone is in place, including the unmixed branch of Corollary 3.7;
- the CM branch uses a real local working definition, but several CM-dependent theorems
  still contain `sorry`;
- Section 4 has not yet been formalized as a theorem layer.


## Where To Look Next

For theorem-by-theorem status:

- see `FORMALIZATION_MAP.md`
- see `TODO.md`

For the public blueprint:

- see `docs/`
- or the published site at `https://tom111.github.io/BEI-lean/`

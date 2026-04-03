# Guide: Extract a Monomial and Finsupp API

## Goal

Hide the low-level `Finsupp` and monomial-order arithmetic behind domain-specific helper
lemmas so the public algebraic proofs are shorter and easier to read.


## Why this matters

The current proofs repeatedly unfold:

- `Finsupp.single`
- `sup`
- `tsub`
- support arithmetic
- monomial degree calculations
- endpoint exponents for path monomials

This is unavoidable at the bottom layer, but it should not remain visible everywhere.

Files most affected:

- [ClosedGraphs.lean](/home/tom/BEI-lean/BEI/ClosedGraphs.lean)
- [GroebnerBasis.lean](/home/tom/BEI-lean/BEI/GroebnerBasis.lean)
- [PrimeIdeals.lean](/home/tom/BEI-lean/BEI/PrimeIdeals.lean)
- [Radical.lean](/home/tom/BEI-lean/BEI/Radical.lean)


## Main refactor idea

Introduce lemma families that speak in the mathematics of the project:

- "the degree at the left endpoint is 1";
- "the degree at irrelevant variables is 0";
- "the S-polynomial lcm shape in the shared-first-endpoint case is ...";
- "path monomials are squarefree";
- "a squarefree degree below an `n`-multiple is below the original degree".

The low-level Finsupp calculation should appear once.


## Immediate extraction targets

## 1. `ClosedGraphs.lean`

The lemmas

- `finsupp_ext_shared_inl`
- `finsupp_ext_shared_inr`
- `finsupp_ext_coprime`

are useful, but they are still too close to raw `Finsupp`.

Try introducing a higher-level S-polynomial helper layer:

- `sPolynomial_shape_shared_first`
- `sPolynomial_shape_shared_last`
- `sPolynomial_shape_coprime`

Then the case analysis in the theorem can refer to these shapes directly.


## 2. `GroebnerBasis.lean`

The cluster around:

- `groebnerElement_degree_inl`
- `groebnerElement_degree_inr`
- `groebnerElement_degree_at_inl_i`
- `groebnerElement_degree_at_inr_j`

is exactly the right direction.

The next cleanup step is to collect them into a dedicated section with a comment saying:

- this is the degree API for admissible-path binomials;
- reducedness proofs should use only these lemmas, not unfold definitions.


## 3. `PrimeIdeals.lean`

This file has the heaviest monomial manipulation.

Try to isolate:

- normalization/fiber-equivalence API;
- support-on-`S` vs support-off-`S` API;
- kernel-membership criteria;
- chain-extension lemmas.

The goal is to make the height proof read in phases rather than in raw exponent algebra.


## Suggested local file organization

Inside each major file, create explicit sections such as:

- `## Degree API`
- `## Squarefree API`
- `## Shared-endpoint S-polynomial shapes`
- `## Kernel chain API`

Even before splitting files, this improves readability.


## Anti-patterns to avoid

- unfolding `Finsupp` directly in every major theorem;
- mixing monomial arithmetic with graph-case reasoning in the same paragraph;
- exposing raw `tsub` manipulations in paper-facing proofs.


## Definition of done

This guide is complete when the main Gröbner and height theorems depend on a compact
monomial/Finsupp API rather than raw pointwise arithmetic.

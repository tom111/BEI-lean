---
title: Overview
---

# Overview

<div class="intro-card">
The project is organized around the four main sections of the paper. The pages in this
blueprint are meant to help a human reader move back and forth between the published
mathematics and the Lean development.
</div>

## Aim

The formalization aims to stay as close as possible to the original paper in
[BEI.tex](https://github.com/tom111/BEI-lean/blob/master/BEI.tex), while still making
good use of Lean and Mathlib.

One important qualification: the current project uses a local equidimensional stand-in
for Cohen-Macaulayness in the Proposition 1.6 branch. That stand-in is not the full
depth-based theory from commutative algebra. The direct proof of the resulting
equidimensional surrogate is now complete, but the project still does not count the
paper as completely formalized until the full Cohen-Macaulay theory is in place.

For the full theory, the likely next source is newer Mathlib or a backport from
Mathlib PR `#26218`.

This means the blueprint should be read on two levels:

1. the **paper level**: what theorem is being formalized;
2. the **Lean level**: how the theorem is represented in the code.

## Main source files

The core development lives in:

- [BEI/Definitions.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Definitions.lean)
- [BEI/GraphProperties.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GraphProperties.lean)
- [BEI/ClosedGraphs.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/ClosedGraphs.lean)
- [BEI/GroebnerBasisSPolynomial.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasisSPolynomial.lean)
- [BEI/GroebnerBasis.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/GroebnerBasis.lean)
- [BEI/Radical.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Radical.lean)
- [BEI/PrimeIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeIdeals.lean)
- [BEI/PrimeDecomposition.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecomposition.lean)
- [BEI/PrimeDecompositionDimension.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/PrimeDecompositionDimension.lean)
- [BEI/MinimalPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/MinimalPrimes.lean)
- [BEI/CIIdeals.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/CIIdeals.lean)
- [BEI/Equidim.lean](https://github.com/tom111/BEI-lean/blob/master/BEI/Equidim.lean)

Supporting generic lemmas intended for possible upstreaming live in:

- [toMathlib/](https://github.com/tom111/BEI-lean/tree/master/toMathlib)
- including [toMathlib/Equidim/Defs.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/Equidim/Defs.lean)
- and are summarized in the dedicated [toMathlib support page](./toMathlib.html)

## Organization by paper section

- Section 1 covers closed graphs and the quadratic Gröbner basis criterion.
- Section 2 covers the reduced Gröbner basis and radicality.
- Section 3 covers prime components, minimal primes, and dimension statements.
- The Section 3 CM consequences now live in `PrimeDecompositionDimension.lean`.
- Section 4 concerns the conditional-independence interpretation; `CIIdeals.lean`
  now contains the binary-output single-statement bridge, specification bridge, and
  transferred radicality / prime decomposition / minimal-prime theorems.

## How to use this site

The section pages are theorem maps. Each one tells you:

- the paper result;
- the Lean declaration(s);
- the code file;
- and the fidelity of the formalization.

The blueprint is therefore primarily a navigational aid for mathematicians and Lean users
who want to know what is already in place.

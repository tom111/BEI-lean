---
title: Overview
---

# Overview

<div class="intro-card">
The project follows the four main sections of the paper and records, for each
result, where the Lean theorem lives and how closely it matches the published
statement.
</div>

## Aim

The formalization stays close to the statements in
[BEI.tex](https://github.com/tom111/BEI-lean/blob/master/BEI.tex).

One part is still unfinished: the paper proves Proposition 1.6 and some later
corollaries with Cohen–Macaulay arguments. The current Lean development already
has a direct equidimensional substitute and a substantial Cohen–Macaulay
infrastructure layer, but the full depth-based route from the paper is not
finished yet.

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

## By paper section

- Section 1 covers closed graphs and the quadratic Gröbner basis criterion.
- Section 2 covers the reduced Gröbner basis and radicality.
- Section 3 covers prime components, minimal primes, and dimension statements.
- The Section 3 Cohen–Macaulay consequences currently split between the direct
  equidimensional route in `PrimeDecompositionDimension.lean` and the unfinished
  paper-faithful route in `Equidim.lean`.
- Section 4 concerns the conditional-independence interpretation; `CIIdeals.lean`
  now contains the binary-output single-statement bridge, specification bridge, and
  transferred radicality / prime decomposition / minimal-prime theorems.

## Reading the pages

Each section page records:

- the paper result;
- the Lean declaration(s);
- the code file;
- and the fidelity of the formalization.

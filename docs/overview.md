---
title: Overview
---

# Overview

<div class="intro-card">
The site follows the four main sections of the paper. The goal is not only to
record where each Lean theorem lives, but to show which mathematical results
have already been formalized and which ones are still open.
</div>

## Aim

The formalization stays close to the statements in
[BEI.tex](https://github.com/tom111/BEI-lean/blob/master/BEI.tex).

The paper-faithful Cohen–Macaulay theorem of Proposition 1.6 is now fully
formalized. The remaining gaps are the full Cohen–Macaulay branches of
Corollaries 3.4 and 3.7, which are still represented in Lean by
equidimensional surrogates.

## Mathematical roadmap

- Section 1 characterizes closed graphs by a quadratic Gröbner basis criterion.
- Section 2 proves that the quadratic generators form a reduced Gröbner basis
  and deduces radicality.
- Section 3 describes the prime decomposition, dimension formula, and minimal
  primes of binomial edge ideals.
- Section 4 connects these ideals to conditional independence statements.

For a reader coming from the paper, the section pages are the main entry point.
The code-file list below is mainly for navigation once you know which theorem or
construction you want to inspect.

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

- Section 1: closed graphs, path-like consequences, the closure operation, and the paper-faithful Proposition 1.6 theorem.
- Section 2: reduced Gröbner bases and radicality.
- Section 3: prime ideals `P_S`, prime decomposition, dimension, and minimal
  primes, together with the Cohen–Macaulay dimension and cycle criteria.
- Section 4: the translation to conditional independence ideals and the transfer
  of the results from Sections 2 and 3.

## Reading the section pages

Each section page records:

- the paper result;
- the corresponding Lean declaration(s);
- the file where the proof lives;
- whether the Lean statement is exact, equivalent, or only partial.

Here:

- `Exact` means the Lean theorem matches the paper statement closely.
- `Equivalent` means the mathematics is the same, but the formal statement is
  packaged differently.
- `Partial` means only part of the paper statement is formalized so far.

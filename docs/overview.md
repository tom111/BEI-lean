---
title: Overview
---

# Overview

## What the formalization covers

- **Section 1** characterizes closed graphs by a quadratic Gröbner basis
  criterion and derives the Cohen–Macaulay condition.
- **Section 2** shows that the edge binomials give a reduced Gröbner basis,
  and deduces that $J_G$ is radical.
- **Section 3** describes the prime decomposition, the dimension formula, and
  the minimal primes of $J_G$ in graph-theoretic terms.
- **Section 4** identifies conditional independence ideals in algebraic
  statistics with binomial edge ideals, and transfers the earlier results to
  that setting.

The Lean statements stay close to the paper; in a handful of places a formal
statement is reformulated (same mathematics, different packaging) and each
section page flags those cases in prose.

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


---
title: Overview
---

# Overview

## Aim

The formalization aims to stay as close as possible to the original paper in
[`BEI.tex`](/home/tom/BEI-lean/BEI.tex), while still respecting the realities of Lean and
Mathlib.

The project should therefore be read on two levels:

1. the **paper level**: what theorem is being formalized;
2. the **Lean level**: how the theorem is packaged, split, or blocked.

## Current structure

The core code lives in:

- [`BEI/Definitions.lean`](/home/tom/BEI-lean/BEI/Definitions.lean)
- [`BEI/GraphProperties.lean`](/home/tom/BEI-lean/BEI/GraphProperties.lean)
- [`BEI/ClosedGraphs.lean`](/home/tom/BEI-lean/BEI/ClosedGraphs.lean)
- [`BEI/GroebnerBasis.lean`](/home/tom/BEI-lean/BEI/GroebnerBasis.lean)
- [`BEI/Radical.lean`](/home/tom/BEI-lean/BEI/Radical.lean)
- [`BEI/PrimeIdeals.lean`](/home/tom/BEI-lean/BEI/PrimeIdeals.lean)
- [`BEI/PrimeDecomposition.lean`](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
- [`BEI/MinimalPrimes.lean`](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)

## Main bottlenecks

### Section 3 dimension formulas

The core issue is not "the theorem is hard" in the abstract. The real issue is that the
project still needs a clean route to:

- `ringKrullDim (R ⧸ primeComponent G S)`;
- and then `ringKrullDim (R ⧸ J_G)` as a supremum over minimal primes.

### Cohen–Macaulay branch

The CM-dependent results are not yet honest formalizations, because the current project
still uses a placeholder notion in
[`BEI/CohenMacaulay.lean`](/home/tom/BEI-lean/BEI/CohenMacaulay.lean).

## Supporting material

The repo also contains theorem and workflow guides in [`guides/`](/home/tom/BEI-lean/guides),
which act as worker-facing proof blueprints for hard remaining steps.


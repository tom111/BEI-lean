# Guide: Split the Largest Files by Proof Role

## Goal

Reduce file-level cognitive load by splitting the largest files according to proof role,
not arbitrary line count.


## Why this matters

The current large files are:

- [CoveredWalks.lean](/home/tom/BEI-lean/BEI/CoveredWalks.lean) (~2600 lines)
- [GroebnerBasis.lean](/home/tom/BEI-lean/BEI/GroebnerBasis.lean) (~2800 lines)
- [PrimeIdeals.lean](/home/tom/BEI-lean/BEI/PrimeIdeals.lean) (~1900 lines)

These files are doing multiple jobs at once.

Large files are not automatically bad, but in Lean they become hard to navigate and hard
for Claude to continue safely because:

- theorem search context becomes noisy;
- imports and local helper lemmas get tangled;
- proof-role boundaries disappear.


## Splitting principle

Split by conceptual layer.

Do not split only to shrink line counts.


## Target 1: `CoveredWalks.lean`

Current roles mixed together:

- list/monomial helper lemmas;
- path surgery lemmas;
- walk construction for the hard Gröbner cases;
- remainder/reduction infrastructure.

Recommended split:

- `CoveredWalksCore.lean` for generic walk/path combinatorics;
- `CoveredWalksReduction.lean` for Gröbner-remainder constructions;
- keep `CoveredWalks.lean` as a thin re-export if desired.


## Target 2: `GroebnerBasis.lean`

Current roles mixed together:

- theorem statement and Buchberger application;
- large shared-endpoint case construction;
- reducedness proof;
- degree computations for admissible-path binomials;
- squarefree leading-monomial API.

Recommended split:

- `GroebnerBasisMain.lean` for the theorem statement and high-level proof;
- `GroebnerBasisCases.lean` for the long S-polynomial case analysis;
- `GroebnerBasisReduced.lean` for reducedness and degree API.

If a three-way split is too disruptive, at least isolate the reducedness section first.


## Target 3: `PrimeIdeals.lean`

Current roles mixed together:

- definition of `primeComponent`;
- primality proof via kernel map;
- generic support and swap lemmas;
- generating-set upper bound;
- lower bound via prime chains;
- component-count combinatorics.

Recommended split:

- `PrimeComponentDefs.lean`
- `PrimeComponentPrime.lean`
- `PrimeComponentHeight.lean`

This is the most mathematically meaningful split in the project.


## Migration strategy

Do not perform a giant split in one step.

Recommended sequence:

1. add section headers and comments inside the existing file;
2. move one coherent block to a new file;
3. rebuild and adjust imports;
4. repeat.

This avoids breaking the project while refactoring.


## What not to split yet

- small, stable files like `Definitions.lean`, `Groebner.lean`, `MonomialOrder.lean`,
  `Radical.lean`.
- the CM placeholder file should stay small until the CM branch is real.


## Archived material

- [RauhApproach.lean](/home/tom/BEI-lean/Supplement/RauhApproach.lean) should remain clearly
  separated from the main development.
- It should not influence the structure of the live files.


## Definition of done

This guide is complete when the largest theorem files each serve one main mathematical
role and can be navigated without scrolling through unrelated infrastructure.

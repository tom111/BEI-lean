# Guide: Split the Largest Files by Proof Role

## Goal

Reduce file-level cognitive load by splitting the largest files according to proof role,
not arbitrary line count.


## Why this matters

The current large files are:

- [Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean) (~8500 lines)
- [CoveredWalks.lean](/home/tom/BEI-lean/BEI/CoveredWalks.lean) (~2600 lines)
- [PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean)
  (~2100 lines)
- [PrimeIdeals.lean](/home/tom/BEI-lean/BEI/PrimeIdeals.lean) (~1900 lines)
- [GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
  (~2000 lines)
- [GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean)
  (~1700 lines)
- [Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean)
  (~1600 lines)

These files are doing multiple jobs at once.

Large files are not automatically bad, but in Lean they become hard to navigate and hard
for Claude to continue safely because:

- theorem search context becomes noisy;
- imports and local helper lemmas get tangled;
- proof-role boundaries disappear.


## Splitting principle

Split by conceptual layer.

Do not split only to shrink line counts.


## Target 1: `Equidim.lean`

Current roles mixed together:

- the local surrogate API;
- initial-ideal and `y`-shift setup for Proposition 1.6;
- HH graph conditions;
- regular-sequence and NZD infrastructure;
- local and global CM theorems at the augmentation ideal;
- localization-away / tensor transport;
- examples and public wrappers.

Recommended split:

- `InitialIdeal.lean`
- `HHRegularity.lean`
- `HHCohenMacaulay.lean`
- `HHLocalisation.lean`
- keep `Equidim.lean` as a thin public wrapper or re-export layer

This is now the highest-value structural split in the repository.


## Target 2: `CoveredWalks.lean`

Current roles mixed together:

- list/monomial helper lemmas;
- path surgery lemmas;
- walk construction for the hard Gröbner cases;
- remainder/reduction infrastructure.

Recommended split:

- `CoveredWalksCore.lean` for generic walk/path combinatorics;
- `CoveredWalksReduction.lean` for Gröbner-remainder constructions;
- keep `CoveredWalks.lean` as a thin re-export if desired.


## Target 3: `PrimeDecompositionDimension.lean`

Current roles mixed together:

- Corollary 3.3 and related quotient-dimension lemmas;
- equidimensional surrogate consequences for Corollaries 3.4 and 3.7;
- the direct equidimensional route to Proposition 1.6;
- supporting equidimensionality lemmas and examples.

Recommended split:

- `PrimeDecompositionDimensionCore.lean` for Corollary 3.3 and dimension lemmas;
- `PrimeDecompositionEquidim.lean` for `corollary_3_4_equidim`,
  `corollary_3_7_equidim`, and related equidimensional consequences;
- `Prop1_6Equidim.lean` for the direct surrogate route if the support layer is
  still too large after the first split.

This split matters because the file currently mixes paper Section 3 dimension
results with the Proposition 1.6 surrogate branch.


## Target 4: `PrimeIdeals.lean`

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


## Target 5: `GroebnerBasisSPolynomial.lean`

Current roles mixed together:

- long S-polynomial case analysis;
- endpoint-sharing case infrastructure;
- telescope and remainder patterns;
- generic path or monomial lemmas that should live elsewhere.

Recommended split:

- `GroebnerBasisCases.lean` for the long S-polynomial case analysis;
- keep [GroebnerBasis.lean](/home/tom/BEI-lean/BEI/GroebnerBasis.lean)
  as the reducedness and public theorem wrapper file.

The older plan that targeted `GroebnerBasis.lean` is now stale. The hard case
analysis moved, so the split target moved with it.


## Target 6: `toMathlib/CohenMacaulay/Polynomial.lean`

Current roles mixed together:

- generic ring-equivalence CM transport;
- field base cases;
- polynomial extension theorems;
- quotient-localization identifications;
- regular-quotient descent and consumer-facing wrappers.

Recommended split:

- `PolynomialBase.lean`
- `PolynomialQuotient.lean`
- leave truly generic support in `Basic.lean` or `Localization.lean`

This is the main `toMathlib/` structural target now.


## Target 7: `GroebnerDeformation.lean`

Current roles mixed together:

- deformation ring and specialization maps;
- monomial-order setup;
- Gröbner-basis and colon-ideal machinery;
- flatness and regularity transfer;
- the final CM-transfer assembly.

Recommended split:

- none yet while the active Prop 1.6 branch is still moving;
- after the branch stabilizes, split into:
  - `GroebnerDeformationCore.lean`
  - `GroebnerDeformationGB.lean`
  - `GroebnerDeformationCM.lean`

For now, prefer theorem-layer cleanup and style cleanup over structural moves.


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
  `Radical.lean`;
- [Proposition1_6.lean](/home/tom/BEI-lean/BEI/Proposition1_6.lean), which is already a
  small public wrapper;
- dormant archived support files unless they return to the critical path.


## Archived material

- [RauhApproach.lean](/home/tom/BEI-lean/Supplement/RauhApproach.lean) should remain clearly
  separated from the main development.
- It should not influence the structure of the live files.


## Definition of done

This guide is complete when the largest theorem files each serve one main mathematical
role and can be navigated without scrolling through unrelated infrastructure.

# Guide: Split the Largest Files by Proof Role

## Goal

Reduce file-level cognitive load by splitting the largest files according to proof role,
not arbitrary line count.


## Why this matters

The current large files are (post 2026-05-02 PrimeDecompositionDimension split):

- [CoveredWalks.lean](/home/tom/BEI-lean/BEI/CoveredWalks.lean) (~2700 lines)
- [Equidim/IteratedRegularity.lean](/home/tom/BEI-lean/BEI/Equidim/IteratedRegularity.lean)
  (~2400 lines, residual heavy block from the equidim split)
- [GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean)
  (~2200 lines)
- [PrimeIdeals.lean](/home/tom/BEI-lean/BEI/PrimeIdeals.lean) (~2000 lines)
- [GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
  (~2000 lines)
- [Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean)
  (~1600 lines)
- [Prop1_6Equidim.lean](/home/tom/BEI-lean/BEI/Prop1_6Equidim.lean)
  (~1430 lines, residual block from the PrimeDecompositionDimension split)

These files are doing multiple jobs at once.

Large files are not automatically bad, but in Lean they become hard to navigate and hard
for Claude to continue safely because:

- theorem search context becomes noisy;
- imports and local helper lemmas get tangled;
- proof-role boundaries disappear.


## Splitting principle

Split by conceptual layer.

Do not split only to shrink line counts.


## Target 1: `Equidim.lean` — DONE 2026-04-27

The equidim file split landed via the `refactor/equidim` branch and was
merged to `master` on 2026-04-27. The resulting layout is:

- `BEI/Equidim/MonomialInitial.lean` (~200 LOC)
- `BEI/Equidim/Bipartite.lean` (~360 LOC)
- `BEI/Equidim/Transport.lean` (~310 LOC)
- `BEI/Equidim/ClosedGraphIntervals.lean` (~160 LOC)
- `BEI/Equidim/IteratedRegularity.lean` (~2456 LOC, post-2026-04-30 carving of `nilradical_nzd_map_diagSubstHom`)
- `BEI/Equidim/AugmentationLocalCM.lean` (~325 LOC)
- `BEI/Equidim/GlobalCMSetup.lean` (~460 LOC)
- `BEI/Equidim/F2Scaffolding.lean` (~450 LOC)
- `BEI/Equidim/L4Iso.lean` (~940 LOC)
- `BEI/Equidim/L1Iso.lean` (~1050 LOC)
- `BEI/Equidim/ReducedHHLocalCM.lean` (~1240 LOC)
- `BEI/Equidim.lean` (residual hub, ~713 LOC) — Session B + Session C1 +
  the F2-route main theorem + paper-facing wrappers

Phase 4 of the plan — carving the two giant declarations
(`nilradical_nzd_map_diagSubstHom` and the F2-route main theorem) —
landed on `master` 2026-04-30 and is recorded in
[archive/EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/archive/EQUIDIM_GIANT_CARVING.md).
The original work package is in
[archive/EQUIDIM_FILE_SPLIT.md](/home/tom/BEI-lean/guides/archive/EQUIDIM_FILE_SPLIT.md).


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


## Target 3: `PrimeDecompositionDimension.lean` — DONE 2026-05-02

Three-way split landed on `master` 2026-05-02. The resulting layout is:

- `BEI/PrimeDecompositionDimensionCore.lean` (~570 LOC) — Corollary 3.3
  family (`ringKrullDim_quot_primeComponent`, `corollary_3_3`,
  `corollary_3_3_lower_bound`), the `dimChainMap` chain machinery, and the
  generic third-isomorphism dimension helper `ringKrullDim_quotQuot_eq`.
- `BEI/PrimeDecompositionDimension.lean` (~160 LOC, residual) — equidimensional
  surrogate variants `corollary_3_4_equidim` and `corollary_3_7_equidim` (with
  the cycle-pair minimal-prime helper).
- `BEI/Prop1_6Equidim.lean` (~1430 LOC) — Example 1.7(b) path-graph
  surrogate (`path_isEquidim`), Proposition 1.6 surrogate
  (`prop_1_6_equidim`), and the shared `isEquidim_of_equidim_minimalPrimes`
  helper.

`Proposition1_6.lean` now imports `BEI.Prop1_6Equidim` directly;
`Corollary3_4.lean` keeps its single import of `BEI.PrimeDecompositionDimension`.


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

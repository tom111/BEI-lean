# Proof Cleanup Guides

These guides are for refactoring the existing formalization so that proofs become:

- shorter;
- more human-readable;
- easier for Claude to extend without regressions.

Current live hotspots from the 2026-04-20 repo state:

- `BEI/Equidim.lean` is now the largest and noisiest active file.
- `BEI/CoveredWalks.lean`, `BEI/PrimeDecompositionDimension.lean`,
  `BEI/PrimeIdeals.lean`, and `BEI/GroebnerBasisSPolynomial.lean`
  remain the main BEI proof-engineering bottlenecks.
- `toMathlib/CohenMacaulay/Polynomial.lean` is now a real maintenance target,
  not just background support code.
- `BEI/GroebnerDeformation.lean` is large and active, but should receive
  presentation cleanup more readily than structural splitting until the current
  Prop 1.6 branch settles.

Recommended order:

1. [PUBLIC_THEOREM_LAYER.md](/home/tom/BEI-lean/guides/cleanup/PUBLIC_THEOREM_LAYER.md)
2. [PATH_AND_INTERNAL_VERTEX_API.md](/home/tom/BEI-lean/guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
3. [MONOMIAL_AND_FINSUPP_API.md](/home/tom/BEI-lean/guides/cleanup/MONOMIAL_AND_FINSUPP_API.md)
4. [EVALUATION_MAP_API.md](/home/tom/BEI-lean/guides/cleanup/EVALUATION_MAP_API.md)
5. [EQUIDIM_DECOMPOSITION.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_DECOMPOSITION.md)
6. [CM_SUPPORT_REFACTOR.md](/home/tom/BEI-lean/guides/cleanup/CM_SUPPORT_REFACTOR.md)
7. [FILE_SPLITTING_PLAN.md](/home/tom/BEI-lean/guides/cleanup/FILE_SPLITTING_PLAN.md)
8. [LINTER_AND_STYLE_CLEANUP.md](/home/tom/BEI-lean/guides/cleanup/LINTER_AND_STYLE_CLEANUP.md)
9. [STATUS_AND_CI_HYGIENE.md](/home/tom/BEI-lean/guides/cleanup/STATUS_AND_CI_HYGIENE.md)

General rule:

- do not try to shorten proofs by golfing tactics;
- first extract the right helper lemmas and abstractions;
- only then simplify the top-level proof scripts.

Secondary rule:

- if a file is on the active paper-critical path, prefer presentation cleanup,
  theorem-layer cleanup, and helper extraction before ambitious file moves.

The target is not "fewer lines at any cost". The target is:

- the public theorem layer reads like the paper;
- the private helper layer absorbs the low-level Lean plumbing;
- recurring proof patterns appear once, not five times;
- the warning stream is small enough that real theorem regressions stand out.

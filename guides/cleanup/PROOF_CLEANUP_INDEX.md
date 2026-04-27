# Proof Cleanup Guides

These guides are for refactoring the existing formalization so that proofs become:

- shorter;
- more human-readable;
- easier for Claude to extend without regressions.

Current live hotspots from the 2026-04-27 repo state:

- `BEI/CoveredWalks.lean` (2671 LOC) is now the largest single file in the repo.
- `BEI/Equidim/IteratedRegularity.lean` (2404 LOC) inherits the heavy iterated-regularity
  block from the equidim split and still hosts the 589-LOC giant
  `nilradical_nzd_map_diagSubstHom`.
- `BEI/GroebnerDeformation.lean` (2221 LOC) and
  `BEI/PrimeDecompositionDimension.lean` (2094 LOC) remain large active files.
- `BEI/PrimeIdeals.lean` (2052 LOC) and
  `BEI/GroebnerBasisSPolynomial.lean` (1984 LOC) are the main BEI
  proof-engineering bottlenecks outside the equidim subtree.
- `BEI/CycleUnmixed.lean` now isolates the old cycle hotspot; its dedicated
  performance packet is complete and archived.
- `toMathlib/CohenMacaulay/Polynomial.lean` (1639 LOC) is a real maintenance target,
  not just background support code.

The equidim split (8106 → 713 LOC residual + 11 split files in `BEI/Equidim/`)
has landed; the follow-up Phase 4 carving of the two giant declarations is
tracked separately in
[EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_GIANT_CARVING.md).

Recommended order:

1. [LEAN_CODE_SMELL_AUDIT.md](/home/tom/BEI-lean/guides/cleanup/LEAN_CODE_SMELL_AUDIT.md)
2. [LEAN_CODE_SMELL_WORKLIST.md](/home/tom/BEI-lean/guides/cleanup/LEAN_CODE_SMELL_WORKLIST.md)
3. [LEAN_PERFORMANCE_TRIAGE.md](/home/tom/BEI-lean/guides/cleanup/LEAN_PERFORMANCE_TRIAGE.md)
4. [PUBLIC_THEOREM_LAYER.md](/home/tom/BEI-lean/guides/cleanup/PUBLIC_THEOREM_LAYER.md)
5. [PATH_AND_INTERNAL_VERTEX_API.md](/home/tom/BEI-lean/guides/cleanup/PATH_AND_INTERNAL_VERTEX_API.md)
6. [MONOMIAL_AND_FINSUPP_API.md](/home/tom/BEI-lean/guides/cleanup/MONOMIAL_AND_FINSUPP_API.md)
7. [EVALUATION_MAP_API.md](/home/tom/BEI-lean/guides/cleanup/EVALUATION_MAP_API.md)
8. [EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_GIANT_CARVING.md)
9. [CM_SUPPORT_REFACTOR.md](/home/tom/BEI-lean/guides/cleanup/CM_SUPPORT_REFACTOR.md)
10. [FILE_SPLITTING_PLAN.md](/home/tom/BEI-lean/guides/cleanup/FILE_SPLITTING_PLAN.md)
11. [LINTER_AND_STYLE_CLEANUP.md](/home/tom/BEI-lean/guides/cleanup/LINTER_AND_STYLE_CLEANUP.md)
12. [STATUS_AND_CI_HYGIENE.md](/home/tom/BEI-lean/guides/cleanup/STATUS_AND_CI_HYGIENE.md)

Completed:

- [archive/MINIMALPRIMES_CYCLE_PERFORMANCE.md](/home/tom/BEI-lean/guides/archive/MINIMALPRIMES_CYCLE_PERFORMANCE.md)
  Split `CycleUnmixed`, decomposed the cycle component-count proof, removed the heartbeat overrides, and trimmed `MinimalPrimes` imports.
- [archive/EQUIDIM_FILE_SPLIT.md](/home/tom/BEI-lean/guides/archive/EQUIDIM_FILE_SPLIT.md)
  Split `BEI/Equidim.lean` (8106 lines) into `BEI/Equidim/` directory with 11
  files; landed 2026-04-27. Phase 4 follow-up tracked in
  [EQUIDIM_GIANT_CARVING.md](/home/tom/BEI-lean/guides/cleanup/EQUIDIM_GIANT_CARVING.md).
- [archive/EQUIDIM_DECOMPOSITION.md](/home/tom/BEI-lean/guides/archive/EQUIDIM_DECOMPOSITION.md)
  Earlier high-level note for the same split.

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

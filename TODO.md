# BEI Lean Formalization — TODO

## Status Legend

- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Current Tasks

### Homepage And Public Docs

- `[ ]` Expose the main definitions and setup more clearly on the homepage so
  readers can inspect the codebase structure more effectively.

### Cleanup And Maintenance Backlog

- `[ ]` Review archived and dormant support material and decide what still
  deserves explicit status tracking.
- `[ ]` Keep non-critical infrastructure issues separate from the completed
  paper-result status.
- `[ ]` Public theorem layer cleanup where the exported declarations can be
  presented more cleanly.
- `[ ]` File-splitting cleanup if current theorem locations are still awkward
  for readers or maintainers.
- `[ ]` Proof cleanup and linter cleanup from `guides/cleanup/`.

### Lean File Review Queue

- `[ ]` Run a file-by-file Lean cleanup pass for simplification, shortening,
  proof golf, and presentation improvements where appropriate.
  **Follow the per-file recipe in
  [`guides/work_packages/LEAN_FILE_REVIEW_QUEUE.md`](guides/work_packages/LEAN_FILE_REVIEW_QUEUE.md)**
  — every file uses `/lean4:refactor` then `/lean4:golf` and the Lean MCP
  tools, never ad-hoc rewrites.

#### Root

- `[x]` `BEI.lean`

#### `BEI/`

- `[x]` `BEI/AdmissiblePaths.lean`
- `[x]` `BEI/CIIdeals.lean`
- `[x]` `BEI/ClosedGraphs.lean`
- `[x]` `BEI/Corollary3_4.lean`
- `[x]` `BEI/CoveredWalks.lean`
- `[x]` `BEI/Definitions.lean`
- `[x]` `BEI/Equidim.lean`
- `[x]` `BEI/GraphProperties.lean`
- `[x]` `BEI/Groebner.lean`
- `[x]` `BEI/GroebnerAPI.lean`
- `[x]` `BEI/GroebnerBasis.lean`
- `[x]` `BEI/GroebnerBasisSPolynomial.lean`
- `[x]` `BEI/GroebnerDeformation.lean`
- `[x]` `BEI/HerzogLemmas.lean`
- `[x]` `BEI/MinimalPrimes.lean`
- `[x]` `BEI/MonomialOrder.lean`
- `[x]` `BEI/PrimeDecomposition.lean`
- `[x]` `BEI/PrimeDecompositionDimension.lean`
- `[x]` `BEI/PrimeIdeals.lean`
- `[x]` `BEI/Proposition1_6.lean`
- `[x]` `BEI/Radical.lean`
- `[x]` `BEI/ReducedHH.lean`
- `[x]` `BEI/Scratch.lean`

#### `Supplement/`

- `[x]` `Supplement/RauhApproach.lean`

#### `toMathlib/`

- `[x]` `toMathlib/CohenMacaulay/Basic.lean`
- `[ ]` `toMathlib/CohenMacaulay/Defs.lean`
- `[ ]` `toMathlib/CohenMacaulay/Localization.lean`
- `[ ]` `toMathlib/CohenMacaulay/Polynomial.lean`
- `[ ]` `toMathlib/CohenMacaulay/TensorPolynomialAway.lean`
- `[ ]` `toMathlib/Equidim/Defs.lean`
- `[ ]` `toMathlib/FiniteFreeEquidim.lean`
- `[ ]` `toMathlib/GradedAssociatedPrime.lean`
- `[ ]` `toMathlib/GradedCM.lean`
- `[ ]` `toMathlib/GradedEquidim.lean`
- `[ ]` `toMathlib/GradedFiniteFree.lean`
- `[ ]` `toMathlib/GradedIrrelevant.lean`
- `[ ]` `toMathlib/GradedPrimeAvoidance.lean`
- `[ ]` `toMathlib/GradedQuotient.lean`
- `[ ]` `toMathlib/GradedRegularSop.lean`
- `[ ]` `toMathlib/HeightDeterminantal.lean`
- `[ ]` `toMathlib/HeightVariableIdeal.lean`
- `[ ]` `toMathlib/IntegralDimension.lean`
- `[ ]` `toMathlib/IsPrimeSpanX.lean`
- `[ ]` `toMathlib/MonomialIdeal.lean`
- `[ ]` `toMathlib/PolynomialAwayTensor.lean`
- `[ ]` `toMathlib/QuotientDimension.lean`
- `[ ]` `toMathlib/SquarefreeMonomialPrimes.lean`
- `[ ]` `toMathlib/TensorLocalisation.lean`

---

## Standing Workflow Rules

- Keep `TODO.md`, `FORMALIZATION_MAP.md`, `docs/`, and `guides/INDEX.md` in
  sync after status or website edits.
- Archive finished work packages promptly so `guides/work_packages/` contains
  only genuinely active packets.
- Remove stale references to old blockers, old proof routes, or old milestone
  language when the corresponding work is already complete.
- Use the Lean MCP tools and the `/lean4:golf` workflow intentionally during
  file-review cleanup rather than making ad hoc edits.
- `guides/work_packages/` should stay empty until a genuinely new
  theorem-critical task appears.

---

## Current Status Snapshot

### Repository Status

- `[x]` Sections 1--4 are represented in Lean.
- `[x]` The named paper results are all covered.
- `[x]` The public status pages describe the paper-to-Lean map as complete.
- `[x]` The reader-facing website copy has had an initial editorial cleanup
  pass.

### Paper Map Snapshot

- Section 1: complete.
  Equivalent packaging remains for Proposition 1.4.
- Section 2: complete.
  Theorem 2.1 remains split across the Buchberger proof, reducedness proof, and
  the wrapper theorem.
- Section 3: complete.
  Equivalent packaging remains for Proposition 3.6, Proposition 3.8, and
  Corollary 3.9.
- Section 4: complete.

This means the remaining work is cleanup, presentation, and maintenance rather
than theorem-critical formalization.

### Guide State

- Active theorem-critical work packages: none.
- Recently retired packets:
  - `guides/archive/NEXT_SESSION_PROMPT.md`
  - `guides/archive/COROLLARY_3_4_IMPLEMENTATION.md`

---

## Notes

- `FORMALIZATION_MAP.md` is the detailed paper-vs-Lean statement map.
- `guides/cleanup/` contains the current non-critical cleanup backlog.
- `guides/website/HOMEPAGE_MATH_CONTEXT_PLAN.md` is the current website-side
  planning note.

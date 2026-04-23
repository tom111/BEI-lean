# BEI Lean Formalization — TODO

## Status Legend
- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Repository Status

- `[x]` Sections 1--4 are represented in Lean.
- `[x]` The named paper results are all covered.
- `[x]` The public status pages describe the theorem map as complete.
- `[x]` The reader-facing website copy has had an initial editorial cleanup pass.

## Paper Map Snapshot

- Section 1: complete.
  Equivalent packaging remains for Proposition 1.4.
- Section 2: complete.
  Theorem 2.1 remains split across the Buchberger proof, reducedness proof,
  and the wrapper theorem.
- Section 3: complete.
  Equivalent packaging remains for Proposition 3.6, Proposition 3.8, and
  Corollary 3.9.
- Section 4: complete.

This means the remaining work is cleanup, presentation, and maintenance rather
than theorem-critical formalization.

---

## Current Priorities

### Priority 1: Homepage Editorial Cleanup

- `[x]` Rewrite the homepage copy so it reads like a public project overview,
  not a theorem-by-theorem completion log.
- `[x]` Remove theorem-local comments of the form
  "Proposition 1.6 is formalized in its paper-faithful CM form" and
  "Corollary 3.4 is formalized in its paper-faithful CM form".
  Everything listed there is already supposed to be paper-faithful unless
  explicitly marked as an equivalent reformulation.
- `[x]` Prefer section-level and project-level descriptions over milestone
  language such as "now formalized", "finally complete", or other historical
  framing that does not help a homepage reader.
- `[x]` Review homepage cards, section blurbs, and theorem highlights for the
  same issue.
- `[ ]` Expose the main definitions and setup more clearly on the homepage so
  readers can inspect the codebase structure more effectively.

### Priority 2: Status File Hygiene

- `[ ]` Keep `TODO.md`, `FORMALIZATION_MAP.md`, `docs/`, and `guides/INDEX.md`
  in sync after status or website edits.
- `[ ]` Archive finished work packages promptly so `guides/work_packages/`
  contains only genuinely active packets.
- `[ ]` Remove stale references to old blockers, old proof routes, or old
  milestone language when the corresponding work is already complete.

### Priority 3: Optional Cleanup / Refactor

- `[ ]` Proof cleanup and linter cleanup from `guides/cleanup/`.
- `[ ]` Public theorem layer cleanup where the exported declarations can be
  presented more cleanly.
- `[ ]` File-splitting cleanup if current theorem locations are still awkward
  for readers or maintainers.

### Priority 4: Dormant / Non-Critical Review

- `[ ]` Review archived and dormant support material and decide what still
  deserves explicit status tracking.
- `[ ]` Keep non-critical infrastructure issues separate from the completed
  paper-result status.

### Priority 5: Lean File Review Queue

- `[ ]` Run a file-by-file Lean cleanup pass for simplification, shortening,
  proof golf, and presentation improvements where appropriate.
  Use the Lean MCP tools and the `/lean4:golf` workflow intentionally rather
  than making ad hoc edits.

#### Root

- `[x]` `BEI.lean`

#### `BEI/`

- `[x]` `BEI/AdmissiblePaths.lean`
- `[x]` `BEI/CIIdeals.lean`
- `[x]` `BEI/ClosedGraphs.lean`
- `[x]` `BEI/Corollary3_4.lean`
- `[ ]` `BEI/CoveredWalks.lean`
- `[ ]` `BEI/Definitions.lean`
- `[ ]` `BEI/Equidim.lean`
- `[ ]` `BEI/GraphProperties.lean`
- `[ ]` `BEI/Groebner.lean`
- `[ ]` `BEI/GroebnerAPI.lean`
- `[ ]` `BEI/GroebnerBasis.lean`
- `[ ]` `BEI/GroebnerBasisSPolynomial.lean`
- `[ ]` `BEI/GroebnerDeformation.lean`
- `[ ]` `BEI/HerzogLemmas.lean`
- `[ ]` `BEI/MinimalPrimes.lean`
- `[ ]` `BEI/MonomialOrder.lean`
- `[ ]` `BEI/PrimeDecomposition.lean`
- `[ ]` `BEI/PrimeDecompositionDimension.lean`
- `[ ]` `BEI/PrimeIdeals.lean`
- `[ ]` `BEI/Proposition1_6.lean`
- `[ ]` `BEI/Radical.lean`
- `[ ]` `BEI/ReducedHH.lean`
- `[ ]` `BEI/Scratch.lean`

#### `Supplement/`

- `[ ]` `Supplement/RauhApproach.lean`

#### `toMathlib/`

- `[ ]` `toMathlib/CohenMacaulay/Basic.lean`
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

## Guide State

- Active theorem-critical work packages: none.
- `guides/work_packages/` should stay empty until a genuinely new task appears.
- Recently retired packets:
  - `guides/archive/NEXT_SESSION_PROMPT.md`
  - `guides/archive/COROLLARY_3_4_IMPLEMENTATION.md`

---

## Notes

- `FORMALIZATION_MAP.md` is the detailed paper-vs-Lean statement map.
- `guides/cleanup/` contains the current non-critical cleanup backlog.
- `guides/website/HOMEPAGE_MATH_CONTEXT_PLAN.md` is the current website-side
  planning note.

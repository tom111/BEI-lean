# `GroebnerDeformation` grading section: ride Mathlib's `IsWeightedHomogeneous` + `GradedAlgebra`

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review. Has not yet been confirmed by a read-only
investigator. Stage 0 of the refactor plan below MUST start with
such an investigation.

## TL;DR

`BEI/GroebnerDeformation.lean` lines 927–1117 (~245 LOC) build the
weighted-homogeneity + graded-algebra + connected-graded
infrastructure for the deformation ring `DefRing n K`:

- `defWeight` — weight function for the grading
- `isWeightedHomogeneous_fijTilde` — the deformed generator is
  weighted-homogeneous
- `defGrading` + `GradedAlgebra` instance
- `tildeJ_isHomogeneous`
- `tildeJQuotGrading` + `GradedRing` instance
- `tildeJQuotGrading_connectedGraded`

Mathlib has substantial graded-algebra infrastructure:
`MvPolynomial.IsWeightedHomogeneous`,
`MvPolynomial.weightedHomogeneousSubmodule`,
`MvPolynomial.weightedHomogeneousAlgebra`, `Algebra.GradedAlgebra`,
`HomogeneousIdeal`, `ConnectedGradedRing`, etc.

**Estimated reduction: ~100 LOC** if Mathlib's API covers the cases.
**Risk: medium** — universe and instance plumbing.

This is a "Mathlib hunt" refactor, like Stage 4 of the
GradedFiniteFree carve (which found `LinearEquiv.isWeaklyRegular_congr`
and `Module.Basis.mapCoeffs` already upstream).

## Math content

`DefRing n K` is `S[t] = K[t][x_1, …, x_n, y_1, …, y_n]`. The
deformation grading places `x_i, y_i` in degree 1 and `t` in
degree 0 (or some similar weighting). The deformed generators
`f̃_{i,j} = x_i y_j − t · x_j y_i` are weighted-homogeneous of
degree 2. `tildeJ G` is homogeneous; the quotient is a graded ring;
the grading is connected (degree-0 part is a field).

These are all standard graded-algebra constructions for which
Mathlib has a generic API.

## Goal

1. Statements of `defGrading`, `tildeJ_isHomogeneous`,
   `tildeJQuotGrading`, etc. **byte-identical** (or replaced by
   thin wrappers around Mathlib named constructs).
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
3. The grading section materially shorter.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read the grading section end-to-end (lines 927–1117).
- Search Mathlib for:
  - `MvPolynomial.IsWeightedHomogeneous`
  - `MvPolynomial.weightedHomogeneousSubmodule`
  - `MvPolynomial.weightedHomogeneousAlgebra` — does it provide a
    `GradedAlgebra` instance for any weight function?
  - `HomogeneousIdeal.toIdeal_quotient_isGradedRing` — does it
    discharge the `GradedRing` instance on a quotient?
  - `ConnectedGradedRing` / `Algebra.IsConnectedGraded`
- Decide which of the 6 local declarations have direct Mathlib
  replacements vs which need bespoke proofs.

### Stage 1: replace `isWeightedHomogeneous_fijTilde`

If Mathlib has a clean way to assert that `monomial d c` (or a
linear combination of two monomials) is `IsWeightedHomogeneous` of
some degree, use it. Otherwise this stays bespoke.

### Stage 2: replace `defGrading` / `GradedAlgebra` instance

If `MvPolynomial.weightedHomogeneousAlgebra` provides this directly,
the local construction collapses to a thin wrapper.

### Stage 3: replace `tildeJ_isHomogeneous` / `tildeJQuotGrading`

If `HomogeneousIdeal` API gives the quotient `GradedRing` instance
for free, the local hand-rolled version collapses.

### Stage 4: replace `tildeJQuotGrading_connectedGraded`

`ConnectedGradedRing` requires "degree-0 part is a field". Mathlib
may have helpers; if not, this stays bespoke.

### Stage 5: tighten

Each stage commits independently. Final pass tightens scaffolding.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `proposition_1_6` and the
`groebnerDeformation_cm_transfer` consumer via `lean_verify`.

## Risks

1. **Mathlib hunt may come up empty.** If
   `MvPolynomial.weightedHomogeneousAlgebra` doesn't exist or doesn't
   discharge what's needed, fall back to local helpers (still
   probably some saving via deduplication).
2. **Universe / instance plumbing.** `GradedAlgebra` instances often
   need explicit type annotations on `K`, `n`, etc.
3. **`tildeJ` is a non-trivially-graded ideal.** Some Mathlib API may
   assume the standard ℕ-grading; this uses a custom weight. May
   require `OneIndependent` or similar.
4. **Heartbeat regressions** — extract sub-helpers if needed.

## Methodology reminders

See `feedback_fat_proof_carving.md`. This is the "Mathlib helper
hiding in plain sight" pattern that paid off in Buchberger and
GradedFiniteFree. **Stage 0 MUST do the Mathlib hunt before
committing to extraction**, because the saving estimates above are
contingent on Mathlib providing the right pieces.

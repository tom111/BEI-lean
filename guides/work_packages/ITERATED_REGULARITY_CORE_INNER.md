# `IteratedRegularity` core (308–1619): intra-step NZD-on-quotient generalisation

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review. Has not yet been confirmed by a read-only
investigator. Stage 0 of the refactor plan below MUST start with
such an investigation.

## TL;DR

The 1311-LOC core of `BEI/Equidim/IteratedRegularity.lean`
(lines 308–1619) implements iterated regularity via diagonal
substitution: at each step, prove that the next diagonal sum
`x_i + y_i` is a non-zero-divisor on the quotient by the current
modulus. Inside, `nilradical_nzd_map_diagSubstHom` plus its case
helpers (`caseB_*`, `caseC_*`, `caseD_*`) drive the argument.

The case helpers were already factored in the 2026-05-02 carve
(item #2 of the original fat-proof list). What was *not* done is to
look across iterations for **a unified "stepwise NZD on quotient"
lemma** that could live in `toMathlib/CohenMacaulay/Basic.lean` and
be called once per step, replacing several ad-hoc intermediate
witnesses.

**Estimated reduction: ~150 LOC.** **Risk: medium–high** — getting
the right level of abstraction is delicate; previous case-helper
extractions stopped here for a reason. Worth attempting only after
(1A) and/or (1B) above have shipped, since both reduce the local
scaffolding this lemma would lift.

## Math content

The claim being iterated: given a CM ring `R` and an element
`r ∈ R` such that (a) `r` lifts to a regular element on `R / I` and
(b) `R / (I + ⟨r⟩)` is again CM (with appropriate hypotheses), then
the iterative chain extending the regular sequence by `r` preserves
the CM property at the irrelevant ideal.

In `IteratedRegularity`, this is applied step-by-step for each
diagonal sum, with `R` becoming the cumulative quotient.

## Goal

1. Statements of `nilradical_nzd_map_diagSubstHom` and the case
   helpers **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
3. The iterated NZD chain becomes a thin wrapper over a single
   `toMathlib/CohenMacaulay/Basic.lean` "stepwise NZD" lemma.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read `nilradical_nzd_map_diagSubstHom` and its case helpers.
- Identify the *uniform* claim across iterations. Is it really
  "given CM at step k, conclude CM at step k+1 via NZD argument"?
  Or do successive steps differ in non-trivial ways (e.g., the
  modulus structure)?
- Audit `toMathlib/CohenMacaulay/Basic.lean` and
  `toMathlib/CohenMacaulay/Localization.lean` for existing helpers
  that almost cover this. Look for `IsSMulRegular`,
  `isCohenMacaulayLocalRing_quotient`, etc.
- Decide: extract a new helper, or generalise an existing one.

### Stage 1 (if Stage 0 confirms): write the unified helper

Add a private/public lemma in `toMathlib/CohenMacaulay/Basic.lean`
(or wherever it best fits) covering the uniform "stepwise NZD on
quotient" claim. Test on one iteration first.

### Stage 2: rewire one iteration to use it

Replace one inline case helper invocation with a call to the new
lemma. Build + AxiomCheck + commit.

### Stage 3: rewire the rest

Once the pattern works, repeat for the remaining iterations. Each
should be a one-line change.

### Stage 4: tighten

Look for now-redundant intermediate witnesses.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `proposition_1_6` and `monomialInitialIdeal_isCohenMacaulay`
via `lean_verify`.

## Risks

1. **Wrong level of abstraction.** The previous fat-proof pass
   stopped at extracting case helpers — there's a real risk that
   the "uniform claim" is too narrow to compress meaningfully across
   iterations, or too wide to apply with reasonable hypotheses.
2. **Mathlib churn.** `IsSMulRegular` and Cohen–Macaulay theory in
   Mathlib evolves; pin to the project's mathlib v4.28.0 conventions.
3. **Heartbeat regressions** — extract sub-helpers if needed.

## Methodology reminders

See `feedback_fat_proof_carving.md`. **Negative-value rule applies
strongly here**: if the unified helper signature would grow beyond
the body savings, *abort* and document. This refactor is the most
speculative of the three IteratedRegularity proposals.

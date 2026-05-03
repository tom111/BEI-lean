# `GroebnerDeformation` S-poly identities tail (1569–end): transplant the `theorem_2_1` helpers

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review. Has not yet been confirmed by a read-only
investigator. Stage 0 of the refactor plan below MUST start with
such an investigation.

## TL;DR

`BEI/GroebnerDeformation.lean` lines 1569–end (~665 LOC) is the file's
largest unstudied block. It implements **Buchberger's criterion for
the deformation ring** — i.e., proves S-polynomials of `f̃_{i,j}`
generators reduce to 0 modulo `groebnerBasisSet G` lifted to `S[t]`.

This is *the same case structure as `theorem_2_1`* (over `S[t]`
instead of `S`, with extra `t` factors at each step). The
`theorem_2_1` carve (2026-05-03, item #11 of the original fat-proof
list) shrank that proof from 1991 → 1455 LOC via 5 helpers:

- `cov_inr_or_inl_of_admissible_path`
- `degree_monomial_mul_fij`
- `case4_remainder` / `case5_remainder`
- `fij_degree_inr_eq_zero` / `fij_degree_inl_eq_zero`

**The same 5 helpers may transplant** to the deformed setting with
mild adjustments to handle the `t` factor.

**Estimated reduction: ~200–250 LOC.** **Risk: medium–high** — the
deformation introduces extra `t` factors at every step; the helpers
may need parameterising on whether the underlying ring is `S` or
`S[t]`, or new "deformed" sister helpers may need extracting.

## Math content

The deformed Buchberger argument: prove the deformed Gröbner basis
`{f̃_{i,j}^π}` (where `π` ranges over admissible paths) is a
Gröbner basis of `tildeJ G` in `DefRing n K = S[t]`, by reducing
S-polynomials of pairs of generators to 0. Same case split as in the
original theorem (shared first endpoint, shared last endpoint,
disjoint, etc.); same telescope identities; same coverage arguments.

## Goal

1. Statements of the deformed Buchberger lemmas
   (e.g., `tildeJ_isGroebnerBasis`) **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
3. The 665-LOC tail materially shorter via either (a) direct reuse
   of the `theorem_2_1` helpers, or (b) deformed sister helpers
   following the same shape.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read the S-poly tail end-to-end. Identify the case-split
  structure (same 4 cases as `theorem_2_1`?).
- Compare the case bodies side-by-side with the post-carve
  `theorem_2_1` helpers in `BEI/GroebnerBasisSPolynomial.lean`.
  Are the bodies textually parallel modulo `t` factors?
- Decide: (a) generalise the existing helpers to take an extra
  `t : K[t]` parameter and reuse, OR (b) extract new "deformed
  sister" helpers following the same pattern.
- If the deformed bodies diverge materially from the original
  (more case work, different telescope identity, etc.), document
  and re-plan.

### Stage 1: extract or reuse the coverage-lambda helper

Either (a) call `cov_inr_or_inl_of_admissible_path` directly if
applicable, or (b) extract a `cov_inr_or_inl_of_admissible_path_def`
sister.

### Stage 2: extract or reuse `degree_monomial_mul_fij`

Same pattern. The deformed `f̃_{i,j}` has degree under
`deformationMonomialOrder`; check if the original `degree_monomial_mul_fij`
generalises.

### Stage 3: extract or reuse `case4_remainder` / `case5_remainder`

The most direct transplant. May require sister helpers
`case4_remainder_def` / `case5_remainder_def`.

### Stage 4: extract or reuse `fij_degree_inr_eq_zero` / `fij_degree_inl_eq_zero`

The cross-cutting "32 occurrence" helper from the `theorem_2_1`
carve. The deformed analogue might cut similar volume.

### Stage 5: tighten

Final pass.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `proposition_1_6` and `groebnerDeformation_cm_transfer`
via `lean_verify`. The deformation route is one of the two paths to
`proposition_1_6`; if it breaks, `proposition_1_6` will fail in the
AxiomCheck.

## Risks

1. **`t` factor parameterisation pain.** Every degree calculation,
   every monomial product, has an extra `t` factor in the deformed
   setting. The original helpers may not generalise cleanly; sister
   helpers may be needed instead.
2. **`deformationMonomialOrder` vs `binomialEdgeMonomialOrder`.**
   Two different monomial orders on two different variable types.
   Helpers parameterised on monomial order are needed.
3. **Universe / instance plumbing.** `S[t]` has different typeclass
   resolution paths than `S`.
4. **Heartbeat regressions** — extract sub-helpers if needed.

## Methodology reminders

See `feedback_fat_proof_carving.md`. The `theorem_2_1` carve is the
direct precedent; replicate the staged-commit cadence and the
"negative-value rule" stop condition.

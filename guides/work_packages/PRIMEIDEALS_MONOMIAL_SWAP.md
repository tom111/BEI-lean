# `PrimeIdeals` monomial-swap lemma (296–786): the 490-LOC elephant

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review. Has not yet been confirmed by a read-only
investigator. Stage 0 of the refactor plan below MUST start with
such an investigation — this proposal's saving estimate is the
most speculative of the 10.

## TL;DR

`BEI/PrimeIdeals.lean` lines 296–786 (~490 LOC) implement the
"monomial swap lemma by induction on deviation": any monomial in the
ambient polynomial ring can be reduced step-by-step to a canonical
form via repeated local swaps that preserve membership in (or out of)
`P_S(G)`. This is the single biggest unstudied block in
`PrimeIdeals.lean`.

**Estimated reduction: ~150–200 LOC.** **Risk: high** — this is
deep mathematical machinery; the saving estimate is a guess until
a read-only investigation confirms structure.

## Math content

To prove `ker(φ) ≤ P_S(G)`, the proof reduces an arbitrary monomial
to a "canonical form" via a sequence of local swaps. Each swap
exchanges, e.g., `x_v y_w` for `x_w y_v` modulo `J_{K_C}` for the
appropriate component `C`. "Deviation" measures how far the current
monomial is from canonical form; "induction on deviation" proves the
swap-chain terminates.

This is a normal-form argument. Mathlib's symmetric-function /
permutation-group infrastructure may apply, or a recursive
`Equiv.Perm`-based normalisation may work.

## Goal

1. The eventual conclusion of the section (the monomial swap lemma)
   **byte-identical** in statement.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
3. The 490-LOC body materially shorter via either (a) a more direct
   normal-form proof, (b) Mathlib's symmetric-function infrastructure,
   or (c) sister-fold of the 4-way `(inl, inl) / (inl, inr) / …` case
   analysis on swap pairs.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

This stage is critical and may take significant time.

- Read the entire 490-LOC section end-to-end. Understand what
  "deviation" measures and how the inductive step proceeds.
- Identify the case-split structure inside the inductive step.
  Almost certainly there's a 4-way split on swap pair type:
  `(inl, inl)`, `(inl, inr)`, `(inr, inl)`, `(inr, inr)`. Are all
  4 cases inhabited and non-trivial?
- Search Mathlib for symmetric-function / canonical-form
  infrastructure: `MvPolynomial.symmetric*`, `Equiv.Perm`-based
  reductions, `MonoidAlgebra.symmetricPolynomials`, etc.
- Decide: (a) sister-fold the 4-way case analysis (smaller win,
  lower risk), (b) replace with Mathlib normal-form API (bigger
  win, higher risk), (c) abort and document as INTRINSIC.

### Stage 1 (if Stage 0 says "sister-fold"): extract a `swap_step` helper

Parameterise the 4-way swap-pair case analysis on a `(Side, Side)`
pair. Helper covers all 4 cases with the right per-case witnesses.

### Stage 1 (if Stage 0 says "Mathlib"): rewrite via Mathlib API

Replace the hand-rolled normal-form argument with calls to
Mathlib's symmetric/permutation infrastructure. Higher risk, likely
needs significant universe / instance plumbing.

### Stage 2: tighten

Final pass.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `theorem_3_2` (the chief consumer of `P_S(G)` primality)
and `corollary_3_3` via `lean_verify`.

## Risks

1. **The math may be intrinsically hand-rolled.** If "deviation" is a
   custom metric specific to the bipartite x/y duality, no Mathlib
   API will cover it cleanly. Stage 0 must be honest about this.
2. **The 4-way case analysis may not factor cleanly.** Some of the
   4 cases may be vacuous, others may share machinery; the natural
   parameterisation may not collapse the lemma as much as hoped.
3. **Universe / instance plumbing** if Mathlib's symmetric-function
   API has a different universe convention.
4. **Heartbeat regressions** — extract sub-helpers if needed.

## Methodology reminders

See `feedback_fat_proof_carving.md`. **Negative-value rule applies
strongly**: if the helper signature would grow beyond body savings,
abort. The previous fat-proof pass classified comparable proofs in
the 200–280 LOC range as INTRINSIC for similar reasons; honest
classification here is more valuable than a forced extraction.

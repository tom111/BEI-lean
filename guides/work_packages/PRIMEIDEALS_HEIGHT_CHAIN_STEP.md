# `PrimeIdeals` Lemma 3.1 + lower-bound chain: extract `primeHeight_chain_step` to toMathlib

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review. Has not yet been confirmed by a read-only
investigator. The previous fat-proof pass classified this region as
INTRINSIC; this proposal re-frames the opportunity.

## TL;DR

`BEI/PrimeIdeals.lean` lines 1330–end (~730 LOC) prove Lemma 3.1
(`height(P_S) = |S| + |V| − c(S)`) via a 3-phase chain (Segre /
x-kill / y-kill) constructing strict prime inclusions of length
|S| + |V| − c(S).

The previous pass classified this INTRINSIC because each phase has
its own witness construction. **This proposal pivots**: instead of
shrinking `lemma_3_1`, **extract a `primeHeight_chain_step` helper to
toMathlib/** and let the 3 phases share the chain-arithmetic
boilerplate.

The pattern repeated 9× total (3 phases × 3 steps each):

```
have hlt : ker_small < ker_big :=
  lt_of_le_of_ne hle (fun heq => hwitness_nmem (heq ▸ hwitness_mem))
…
calc (n + 1 : ℕ∞)
    ≤ ker_small.primeHeight + 1 := by gcongr
  _ ≤ ker_big.primeHeight :=
      Ideal.primeHeight_add_one_le_of_lt hlt
```

A tight `chain_step` helper packaging this would collapse ~10 LOC
per iteration × 9 iterations.

**Estimated reduction: ~80–100 LOC.** **Risk: medium** — needs the
right level of abstraction; previously skipped because of awkward
signature.

## Math content

`primeHeight P + 1 ≤ primeHeight Q` when `P < Q` are both prime is
the chain step. The lemma `Ideal.primeHeight_add_one_le_of_lt`
already exists in Mathlib; the boilerplate is the surrounding
`lt_of_le_of_ne` + `calc` ritual that builds the strict inclusion
from witness membership / non-membership.

## Goal

1. `lemma_3_1` statement **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
3. The 3-phase chain becomes a thin wrapper over a single
   `toMathlib/Ideal/PrimeHeight.lean` "chain step" lemma.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read all 3 phases (`phase1`, `phase2`, `phase3` inside `lemma_3_1`).
  Confirm the chain-step pattern is identical across all 9
  invocations.
- Check Mathlib for an existing `chain_step`-like helper. Look for:
  - `Ideal.primeHeight_add_one_le_of_lt` (exists; needs the strict
    inclusion as an argument)
  - `Ideal.primeHeight_add_one_le_of_subset_of_mem_diff` (may not
    exist — this would be the candidate name)
- Document the helper signature decision *before* extraction:
  - Inputs: `P Q : Ideal R`, `[P.IsPrime]`, `[Q.IsPrime]`,
    `hle : P ≤ Q`, `witness : R`, `hmem : witness ∈ Q`,
    `hnmem : witness ∉ P`.
  - Output: `P.primeHeight + 1 ≤ Q.primeHeight`.
- If the signature has more than ~6 parameters or requires fiddly
  typeclass inference, **abort and document as INTRINSIC**.

### Stage 1: write the toMathlib helper

Add to `toMathlib/Ideal/PrimeHeight.lean` (create the file if it
doesn't exist):

```
theorem Ideal.primeHeight_add_one_le_of_lt_witness
    {R : Type*} [CommRing R] {P Q : Ideal R}
    [P.IsPrime] [Q.IsPrime] (hle : P ≤ Q)
    (witness : R) (hmem : witness ∈ Q) (hnmem : witness ∉ P) :
    P.primeHeight + 1 ≤ Q.primeHeight := by
  apply Ideal.primeHeight_add_one_le_of_lt
  exact lt_of_le_of_ne hle (fun heq => hnmem (heq ▸ hmem))
```

### Stage 2: rewire `phase1`

Replace the chain-step boilerplate with helper calls. ~30 LOC saved
in `phase1` alone.

### Stage 3: rewire `phase2` and `phase3`

Same pattern. Total 6 more invocations.

### Stage 4: tighten

Final pass.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `corollary_3_3` (the chief consumer of `lemma_3_1`) via
`lean_verify`.

## Risks

1. **Helper signature may grow.** The 3 phases have different
   typeclass resolution paths; a "uniform" helper signature may
   require explicit instance arguments at each call site. Stage 0
   must validate this isn't a deal-breaker.
2. **Heartbeat regressions** — extract sub-helpers if needed.

## Coupling

If this `toMathlib/Ideal/PrimeHeight.lean` helper lands, it will
also be consumable by `ringKrullDim_quot_primeComponent_ge` in
`BEI/PrimeDecompositionDimensionCore.lean` (216 LOC, similar
3-phase structure per the broader scan). Bonus consumer.

## Methodology reminders

See `feedback_fat_proof_carving.md`. **Negative-value rule applies**.
The previous pass skipped this because the helper signature looked
awkward; this proposal reframes by lifting to toMathlib (rather
than file-local) where the API can be cleaner.

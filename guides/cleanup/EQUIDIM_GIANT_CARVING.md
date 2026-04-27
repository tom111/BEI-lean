# Cleanup: carve the two remaining giant declarations in the equidim development

## Status

Optional proof-engineering follow-up. Statements must remain byte-identical
and no new axioms may appear. The equidim file split (the
`EQUIDIM_FILE_SPLIT.md` work package) deliberately deferred this carving
to keep that pass to pure file moves.

## Targets

Two declarations significantly exceed the ~200-LOC ceiling that the file
split work package set as the long-term acceptance criterion:

| Declaration | File | LOC | Structure |
|---|---|---|---|
| `nilradical_nzd_map_diagSubstHom` | `BEI/Equidim/IteratedRegularity.lean` (line ≈ 859) | 589 | Four-case proof on whether `d₀(inl i)` and `d₀(inr i)` are positive: A both ≥ 1 (~20 LOC), B inl≥1/inr=0 (~104 LOC), C symmetric to B (~80 LOC), D both = 0 (~342 LOC). Cases B and C are near-duplicates. Case D dominates and uses HH transitivity. Shared prelude (`Iφ`, `hIsM`, `hd₀_supp`, `hd₀_not`, `hcoeff_ne`, `hdiv`, diagonal-membership) sits at lines 869–901. |
| `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` | `BEI/Equidim.lean` (line ≈ 380) | 290 | Two-case main theorem on whether the ambient prime sits inside the augmentation ideal: in-augIdeal case uses localization transitivity; non-augIdeal case is the F2 route through `E_U`, `pairedSurvivors_*_mem`, the C3a forward traces, and the `augIdealReduced` maximality argument. |

## Recommended approach

1. **`nilradical_nzd_map_diagSubstHom` (Case D first).**
   Extract Case D into a private helper of its own (~342 LOC → ≤ 150 LOC
   after further sub-decomposition). The natural sub-helpers inside Case D:
   - "monomial dx and dy lie in `Iφ`" (the Finsupp coefficient bookkeeping
     at lines ≈ 1115–1156 is nearly mechanical; would shrink ~80 LOC).
   - "generator analysis on dx, dy via `support_divisible_by_generator`"
     (the parallel calls at lines ≈ 1158–1230; ~70 LOC).
   - "HH transitivity gives the contradiction" (the closing combinatorial
     argument; ~50 LOC).
   After Case D is its own helper, do Cases B and C: they are near-mirrors
   of each other, so a single helper parameterised on a `Bool` (or two
   tiny helpers + a private `case_BC_helper`) collapses ~180 LOC.

2. **`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`.**
   Already split into two large `by_cases` branches inside the `by` block.
   Extract the F2-route branch (the larger one) into a private lemma
   `cm_F2_route` taking the prime, the not-in-augIdeal hypothesis, the
   `E_U` bundle, and the C3a forward traces as arguments. The
   "in-augIdeal" branch is short enough to leave inline.

## Constraints

- **No statement changes** for any pre-existing public declaration.
- **No new axioms.** Run an axiom check after each commit on
  `proposition_1_6`, `monomialInitialIdeal_isCohenMacaulay`,
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`,
  `prop_1_6_herzogHibi`, `corollary_3_4`, `corollary_3_4_connected`,
  `corollary_3_7_cm_fin` — all currently `[propext, Classical.choice, Quot.sound]`.
- New helper lemmas should be `private` unless a downstream file already
  uses them.
- Preserve any `set_option maxHeartbeats` raise that the original block
  uses (the giants currently do not raise heartbeats; carving may free up
  budget but should not introduce new raises without a measurement).

## Other tracked cleanup opportunities

The following files are still candidates for `/lean4:refactor` and
`/lean4:golf` passes after the carving lands. They are not on the paper
critical path so any cleanup is purely engineering.

- `BEI/Equidim/L4Iso.lean` (940 LOC, no single declaration > 200 LOC,
  but several ~100-LOC helpers and lots of repetitive case work).
- `BEI/Equidim/L1Iso.lean` (1050 LOC; includes the two
  `set_option maxHeartbeats` blocks already bisected to 1.3M / 1.1M).
- `BEI/Equidim/ReducedHHLocalCM.lean` (1237 LOC).

## Verification recipe

After each commit on this work, run:

```
lake build
```

Then on a scratch Lean file:

```
import BEI.Proposition1_6
import BEI.Equidim
import BEI.Corollary3_4
import BEI.GroebnerBasis

#print axioms proposition_1_6
#print axioms isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal
#print axioms monomialInitialIdeal_isCohenMacaulay
#print axioms prop_1_6_herzogHibi
#print axioms corollary_3_4
#print axioms corollary_3_4_connected
#print axioms corollary_3_7_cm_fin
```

Each must report `[propext, Classical.choice, Quot.sound]`.

## Status of the related performance audit (April 2026)

A `set_option ...maxHeartbeats` audit was completed alongside the file
split. Results landed in master:

| File | Before | After |
|---|---|---|
| `BEI/Equidim/L1Iso.lean` | two 1.6M blocks | 1.3M + 1.1M |
| `BEI/Equidim.lean` (main theorem) | 800k + 400k synth | 500k + 250k synth |
| `BEI/ClosedGraphs.lean` | 5 raises (3×800k + 2×400k) | none (default 200k) |
| `BEI/Equidim/ReducedHHLocalCM.lean` | one 400k | none |
| `BEI/Equidim/GlobalCMSetup.lean` | one synth 400k | none |
| `BEI/Equidim/AugmentationLocalCM.lean` | synth 400k | synth 250k |

The remaining 400k raises in `BEI/Equidim.lean` (around the C3a
`E_U_algebraMap_mkI_X_pairedSurvivor_inl` / `_inr` traces) and in
`BEI/Corollary3_4.lean` (around `beQuotientGrading_isGradedRing`) were
tested at 200k and proved necessary; leave them in place.

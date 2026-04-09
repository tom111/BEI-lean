# Guide: Infrastructure Linter Cleanup Packet 01

## Origin

This guide comes from a manual code-review sweep over the current live repo state.
The goal is not new mathematics. The goal is to reduce warning noise and remove stale
proof-engineering artifacts in the core infrastructure files that theorem work depends on.

This is a cleanup packet, not a theorem packet.

## Current state

The repo builds, but the warning stream is still noisy. The most relevant review findings
after direct small fixes are:

1. `BEI/PrimeIdeals.lean`
   - many theorem statements still carry unused `[DecidableEq V]` / `[Fintype V]`
     assumptions;
   - several declarations still trigger the `set_option maxHeartbeats` style warning;
   - there are still a few style-only warnings after the latest direct cleanup.

2. `BEI/GraphProperties.lean`
   - deprecated `List.Chain'` usage remains;
   - several `simp at ...` flexible-tactic warnings remain.

3. `BEI/CoveredWalks.lean`
   - many deprecated `List.Chain'` uses remain;
   - many flexible `simp` warnings remain;
   - several theorem statements still carry unused assumptions.

4. `BEI/ClosedGraphs.lean`
   - several declarations use scoped `maxHeartbeats`, but still trigger style warnings;
   - many theorem statements carry unused assumptions;
   - there are many long-line warnings.

This packet should focus on the first three items. Do not sprawl into unrelated theorem
refactors.

## What was already fixed directly

Before this guide:

- stale dead-code blocks in `BEI/GroebnerBasisSPolynomial.lean` were removed;
- a stale “sorry” comment in `BEI/PrimeIdeals.lean` was corrected;
- some local unused-simp-arg warnings in `BEI/PrimeIdeals.lean` were cleaned up;
- a few `GroebnerAPI` style issues were cleaned up;
- `toMathlib/MonomialIdeal.lean` was simplified so
  `Ideal.not_mem_exists_monomial_notMem` no longer carries fake extra assumptions.

So do not reopen those already-fixed points unless the current code genuinely regressed.

## Target files for this packet

Priority order:

1. `BEI/PrimeIdeals.lean`
2. `BEI/GraphProperties.lean`
3. `BEI/CoveredWalks.lean`
4. `BEI/ClosedGraphs.lean` only if the first three finish cleanly

## Concrete work items

### 1. `BEI/PrimeIdeals.lean`

Main tasks:

- remove unused simp arguments still flagged by the linter;
- shrink theorem assumptions where they are obviously unused;
- deal honestly with the `set_option maxHeartbeats` warnings.

For the `maxHeartbeats` warnings:

- check whether the current command form can be replaced by a more local scoped form that
  the style linter accepts;
- if not, add a precise inline comment and leave the smallest truthful local form;
- do not disable the linter globally.

Do not rewrite the large proofs unless the cleanup forces it.

### 2. `BEI/GraphProperties.lean`

Main tasks:

- replace deprecated `List.Chain'` with `List.IsChain`;
- convert flexible `simp at h` uses into explicit `simp only [...]` or a `suffices` step;
- remove obviously unused assumptions from theorem statements when that is local and safe.

This should be largely mechanical.

### 3. `BEI/CoveredWalks.lean`

Main tasks:

- same `List.Chain'` migration as above;
- same flexible-`simp` cleanup pattern as above;
- shrink theorem assumptions where clearly unused.

This file is large. Do not attempt a whole-file aesthetic rewrite. Work warning-by-warning
on the declarations the linter already points to.

## What not to do

- do not change theorem statements in ways that move the formalization away from the paper;
- do not touch `BEI/Equidim.lean` or Section 4 in this packet;
- do not mix cleanup with new theorem development;
- do not start broad “replace all classical assumptions everywhere” work if the local
  warning can be fixed by a smaller change.

## Verification

Build each touched file directly after editing it.

Recommended commands:

```text
lake build BEI.PrimeIdeals
lake build BEI.GraphProperties
lake build BEI.CoveredWalks
lake build BEI.ClosedGraphs
```

## Definition of done

This packet is successful if:

1. the touched files still build;
2. the warning count for those files is materially lower;
3. no theorem statements were weakened or distorted just to silence lint;
4. the cleanup stays local to the named files.

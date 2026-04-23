# MinimalPrimes Cycle Performance Packet

## Preserved task

The current task is to turn the Lean-performance research note and the follow-up
analysis into a concrete work package for performance improvements.

This packet is the first and highest-priority cleanup target.

## Scope

This is a **performance and file-structure cleanup packet**, not new theorem work.

Target file:

- `BEI/MinimalPrimes.lean`

Target block:

- everything from `/-! ## Corollary 3.7 unmixed branch -/` onward

Main hotspot declarations:

- `cycle_induce_preconnected` at line ~569
- `cycle_componentCount_pair_nonadj` at line ~654

Why this packet comes first:

- `BEI/MinimalPrimes.lean` contains the repo's largest single heartbeat raise:
  `set_option maxHeartbeats 4000000`
- the large proof is concentrated in one declaration, so the likely payoff is high
- the cycle branch is mathematically coherent and can be split from the rest of the file

## Current diagnosis

The main issue here is **not** broad automation.

In this file:

- `simp only` is already used heavily;
- there is no meaningful `convert` problem in the hotspot block;
- there are only a few `omega` calls compared to the size of the proof term.

The real problem is the giant theorem
`cycle_componentCount_pair_nonadj`, which currently mixes:

- cycle-walk construction;
- edge classification;
- arc decomposition;
- induced-subgraph reachability;
- no-cross-edge reasoning;
- component separation; and
- final `Nat.card_eq_two_iff` assembly.

That should be decomposed into smaller declarations before doing any second-line
performance tuning.

## Main objective

Replace one giant heartbeat-heavy theorem by:

1. a dedicated cycle/unmixed file;
2. one short assembly theorem; and
3. `6–8` private helper lemmas with local, measurable heartbeat costs.

## Recommended file split

Move everything from

- `/-! ## Corollary 3.7 unmixed branch -/`

into a new file, with one of these names:

- `BEI/CycleUnmixed.lean`
- `BEI/CycleComponentCounts.lean`

Preferred default:

- `BEI/CycleUnmixed.lean`

Reason:

- this block is mathematically self-contained;
- the Matching/IsCycles/cycle-support API is only used here;
- the non-cycle Proposition 3.8 material should no longer pay that import cost;
- smaller files should improve rebuild scope and readability.

After the split:

- run `#min_imports` on the new file;
- run `#min_imports` on the reduced `BEI/MinimalPrimes.lean`;
- keep the public theorem names unchanged unless explicitly requested.

## Required decomposition

### A. Hoist repeated bridge lemmas

First extract the repeated

- `IsCycleGraph -> IsCycles`

bridge into one private lemma, e.g.

```lean
private lemma isCycles_of_isCycleGraph
    (G : SimpleGraph V) (hCyc : IsCycleGraph G) : G.IsCycles := ...
```

This bridge currently appears twice and should not be duplicated.

Also extract membership helpers for the survivor set:

```lean
private def survivors (u w : V) : Set V := {x : V | x ∉ ({u, w} : Finset V)}

private lemma mem_survivors_pair_iff {u w x : V} :
    x ∈ survivors u w ↔ x ≠ u ∧ x ≠ w := by
  ...
```

and, if helpful, the singleton version used by `cycle_induce_preconnected`.

Replace `set S ... with hS_def` by `let S := ...` if `hS_def` is unused.

### B. Split `cycle_induce_preconnected`

This is the smaller rehearsal target. It should be reduced to:

- one bridge lemma call;
- one cycle-walk extraction step;
- one reachability assembly step.

Likely helpers:

- a helper that every vertex lies on the Hamiltonian cycle support;
- a helper that vertices other than the basepoint lie on the tail support;
- a helper packaging the `takeUntil` induced-reachability argument.

### C. Split `cycle_componentCount_pair_nonadj`

This theorem should become an assembly theorem over private lemmas. Candidate
helper structure:

- `edge_on_arc`
- `arc1_reachable`
- `arc2_reachable`
- `no_cross_edge`
- `separated_components`
- `every_component_hits_arc`

The final theorem should ideally only:

1. set up `S`, `G'`, `arc1`, `arc2`;
2. invoke the helper lemmas;
3. conclude with `Nat.card_eq_two_iff`.

### D. Refactor the Proposition 3.8 evaluation-map block

Still in `BEI/MinimalPrimes.lean`, extract reusable helpers for:

- the evaluation map used in `prop_3_8_var_not_mem`;
- the prime-component-to-kernel containment proof;
- the witness evaluation computation.

Main target declarations:

- `prop_3_8_var_not_mem`
- `prop_3_8_sameComponent_preserved`

The goal is not to change the mathematics. The goal is to stop rebuilding the
same long evaluation/simp pattern in multiple proofs.

## Measurement plan

Do **not** profile the entire file first.

Profile the two heartbeat-raised lemmas first:

- `cycle_induce_preconnected`
- `cycle_componentCount_pair_nonadj`

Use temporary instrumentation like:

```lean
set_option profiler true in
set_option profiler.threshold 50 in
set_option trace.profiler.useHeartbeats true in
set_option diagnostics true in
...
```

After each structural refactor:

- run `#count_heartbeats in` on the helper or final theorem;
- if noise matters, use `#count_heartbeats!`;
- only keep a heartbeat raise if the theorem is still genuinely expensive;
- if a raise remains, keep a generous margin rather than a knife-edge cap.

## Acceptance criteria

This packet is complete when:

1. the cycle/unmixed branch lives in its own file;
2. `cycle_componentCount_pair_nonadj` is reduced to a short assembly theorem;
3. the duplicated `IsCycles` bridge has been hoisted;
4. repeated survivor-set simp boilerplate has been replaced by helper lemmas;
5. the Proposition 3.8 evaluation-map pattern has been factored;
6. the new file(s) build cleanly;
7. heartbeat measurement has been rerun on the refactored declarations; and
8. the remaining heartbeat raises, if any, are lower or better justified.

## Explicit non-goals

Do not start this packet by:

- globally replacing `simp` by `simp?`;
- chasing instance-search tuning first;
- trying `seal`, `unseal`, or transparency hacks first;
- changing theorem statements;
- rewriting unrelated Section 3 files.

Those may become relevant later, but not before the structural split.

## Warnings

- Keep all public theorem names stable unless explicitly asked otherwise.
- Do not claim success based only on moving code into a new file; the large theorem must
  actually be decomposed.
- Do not replace one giant theorem by a giant local `where` block. The helpers should be
  separate declarations so Lean and the editor can reuse them incrementally.
- If profiling shows kernel checking rather than tactic search is dominant, still prefer
  theorem decomposition first.

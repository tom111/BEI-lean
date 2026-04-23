# Work Package: Split `BEI/Equidim.lean` into a `BEI/Equidim/` directory

## Origin

Discussion in the cleanup session of 2026-04-23: the file is too large
(8106 lines after the toMathlib extraction in commit `d53e84d`,
8489 lines before it) to navigate, profile, or edit safely. Compile time is
~210 s for this single file. It mixes ten distinct mathematical sections.

This guide supersedes the high-level
[`cleanup/EQUIDIM_DECOMPOSITION.md`](../cleanup/EQUIDIM_DECOMPOSITION.md),
adding concrete file-by-file targets, declaration assignments, dependency
ordering, and acceptance criteria. The cleanup version should be archived
once this work package is consumed.

## What `BEI/Equidim.lean` currently contains

All line numbers are post-extraction (commit `d53e84d` or later).

| Block | Lines | Topic |
|---|---|---|
| 1 | 1–134 | `IsEquidim`, complete-graph example, paper-facing public hooks |
| 2 | 135–213 | `monomialInitialIdeal` and the `y`-predecessor shift |
| 3 | 214–548 | `bipartiteEdgeMonomialIdeal`, `hhEdgeSet`, vertex covers, equidim of monomial side |
| 4 | 549–824 | Regular elements, transports, `y`-pred equivalence, equidim of monomial initial ideal quotient |
| 5 | 825–961 | Closed-graph component-count lemmas (small, weakly tied to the rest) |
| 6 | 962–3441 | Iterated regularity via diagonal substitution, NZD proofs, weakly regular sequences, dimension formula. **2480 lines — by far the largest single block.** |
| 7 | 3442–3704 | Augmentation ideal, last-pair permutation, local CM at `augIdeal` (carries both `synthInstance.maxHeartbeats` blocks) |
| 8 | 3705–4001 | Global-CM scaffolding: structural lemmas, flat base change, regular elements outside `augIdeal`, graded contraction wiring, homogeneity |
| 9 | 4002–4400 | F2 route scaffolding (survivors, λ-set), restricted ring setup |
| 10 | 4401–5285 | L4 iso (smaller HH ring): forward, backward, bijectivity |
| 11 | 5286–6275 | L1 iso (monomial localization): forward, backward, **the two `set_option maxHeartbeats 1600000` blocks live here** |
| 12 | 6276–7456 | Session A′: reduced HH at `augIdeal` is CM local — the "kill last pair" bridge |
| 13 | 7457–7765 | Session B + Session C1 (`E_U` bundled equiv) |
| 14 | 7766–end | Main theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` and paper-facing wrapping |

## Public surface that must stay accessible

Three files outside `BEI/Equidim.lean` import from it:

| Importer | Symbols used |
|---|---|
| `BEI/Proposition1_6.lean` | `IsEquidim`, `SatisfiesProp1_6Condition`, `HerzogHibiConditions`, `monomialInitialIdeal`, `monomialInitialIdeal_isCohenMacaulay`, `prop_1_6_herzogHibi` |
| `BEI/GroebnerDeformation.lean` | `monomialInitialIdeal` |
| `BEI/PrimeDecomposition.lean` | (uses `primeComponent` from `BEI/PrimeIdeals.lean`, not Equidim) |

So `BEI/Equidim.lean` (the post-split residual file) must continue to expose
those six identifiers — either directly or via re-export.

## Target directory layout

| New file | Source range | Approx LOC | Topic |
|---|---|---|---|
| `BEI/Equidim/MonomialInitial.lean` | 1–213 | 210 | `IsEquidim`, complete-graph example, `monomialInitialIdeal`, `yPredVar` |
| `BEI/Equidim/Bipartite.lean` | 214–548 | 335 | Bipartite edge ideal, vertex covers, equidim of monomial side |
| `BEI/Equidim/Transport.lean` | 549–824 | 275 | Regular elements, ideal-level transport, `y`-pred equivalence, equidim transfer |
| `BEI/Equidim/ClosedGraphIntervals.lean` | 825–961 | 140 | Closed-graph component counts (candidate to fold into `BEI/ClosedGraphs.lean` instead) |
| `BEI/Equidim/IteratedRegularity.lean` | 962–3441 | 2480 | Diagonal substitution, NZD proofs, weakly regular sequences. **Will need internal subdivision before being moved — see "Block 6 caveat" below.** |
| `BEI/Equidim/AugmentationLocalCM.lean` | 3442–3704 | 265 | Augmentation ideal, last-pair permutation, local CM at `augIdeal`. Hosts both `synthInstance.maxHeartbeats 400000` blocks. |
| `BEI/Equidim/GlobalCM_Setup.lean` | 3705–4001 | 295 | Structural lemmas, flat base change, regular elements in non-`augIdeal` primes, graded contraction wiring |
| `BEI/Equidim/F2Scaffolding.lean` | 4002–4400 | 400 | F2 route, survivors, λ-set, restricted ring setup |
| `BEI/Equidim/L4Iso.lean` | 4401–5285 | 885 | L4 iso (smaller HH ring) |
| `BEI/Equidim/L1Iso.lean` | 5286–6275 | 990 | L1 iso (monomial-localization). Hosts both `maxHeartbeats 1600000` blocks. |
| `BEI/Equidim/ReducedHHLocalCM.lean` | 6276–7456 | 1180 | Session A′: kill-last-pair bridge to `augIdealReduced` |
| `BEI/Equidim.lean` (residual) | (re-export hub) | ≤ 300 | Imports the above. Hosts Session B, Session C1 (`E_U`), the main theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`, and the paper-facing public wrapping. |

## Dependency direction

The current code is written top-down so the natural dependency order matches
the file order above:

```
MonomialInitial
    └─ Bipartite
        └─ Transport
            ├─ ClosedGraphIntervals
            └─ IteratedRegularity
                └─ AugmentationLocalCM
                    └─ GlobalCM_Setup
                        ├─ F2Scaffolding
                        │   └─ L4Iso
                        │       └─ L1Iso
                        │           └─ ReducedHHLocalCM
                        │               └─ Equidim   (residual: Session B + C1 + main theorem)
                        └─ Equidim                  (residual)
```

There are no expected back-edges. Confirm with `lake build` after each move.

## Block 6 caveat (`IteratedRegularity`, 2480 lines)

This is the only block too large to move atomically. It contains one
cohesive 589-line proof (`isSMulRegular_map_diagSubstHom`) plus several
261- and 240-line companions. Two-phase plan:

1. **In-place refactor first.** Inside the current `BEI/Equidim.lean`,
   carve `isSMulRegular_map_diagSubstHom` into 4–5 named private helpers,
   each ≤ 150 lines. Same for `isMonomial_span_of_support_singleton`
   (now in toMathlib but it had a 261-line companion that did similar work).
   Build must stay green after this in-place refactor.
2. **Move second.** Once the block is no longer dominated by one giant
   declaration, move it to `BEI/Equidim/IteratedRegularity.lean`.

Do not skip phase 1. A 2480-line file with one 589-line `theorem` is just
as hard to maintain as the 8000-line parent file.

## Migration order — concrete steps

Each phase is **one commit** and requires a clean `lake build` of the whole
project before commit. The order below is the only safe order — do not
reorder.

Every phase uses the same five-step rhythm:

1. **Pre-flight** — `lake build BEI.Equidim` baseline; record compile time
   and warning count.
2. **Move** — copy the listed declarations into the new file, add imports,
   delete from `BEI/Equidim.lean`, promote `private` → public where the
   declaration is now used cross-file (see `private` → public discipline).
3. **Verify** — `lake build` whole project; resolve every error before
   moving on. Use `lean_diagnostic_messages` from the Lean MCP, not
   repeated `lake build` cycles.
4. **Polish** — run `/lean4:refactor BEI/Equidim/<NewFile>.lean` first
   (strategy-level: extract helpers, find shorter mathlib paths,
   simplify proof shape), then `/lean4:golf BEI/Equidim/<NewFile>.lean`
   (tactic-level: collapse `apply f; exact h` and similar, narrow
   non-terminal `simp` to `simp only`). Both skills must end with a clean
   `lake build`.
5. **Commit** — single commit per phase. Body must list the moved
   declarations and any promotions. Use `/lean4:checkpoint "split N: <name>"`
   if you want it to run the build + axiom check + commit in one step.

### Phase 1 — `BEI/Equidim/MonomialInitial.lean`

- Source range: lines 1–213. Approx 210 LOC.
- Move: `IsEquidim`, `IsDomain.isEquidimRing`, `SatisfiesProp1_6Condition`,
  `prop_1_6_herzogHibi`, `complete_isEquidim`, `monomial_pair_eq_X_mul_X`,
  `monomialInitialIdeal`, `initialIdeal_closed_eq`, `yPredVar`,
  `mod_pred`, `rename_yPredVar_generator`.
- Skills: `/lean4:refactor BEI/Equidim/MonomialInitial.lean` then
  `/lean4:golf BEI/Equidim/MonomialInitial.lean`. This is the
  validation phase — the lowest-risk file. If `/lean4:refactor` proposes
  any helper extraction here, accept only if the helper is reused twice in
  the new file.
- Re-export from `BEI/Equidim.lean`: yes (downstream files import
  `IsEquidim`, `SatisfiesProp1_6Condition`, `monomialInitialIdeal`,
  `prop_1_6_herzogHibi`).

### Phase 2 — `BEI/Equidim/Bipartite.lean`

- Source range: lines 214–548. Approx 335 LOC.
- Move: `bipartiteEdgeMonomialIdeal`, `hhEdgeSet`,
  `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`,
  `minimalPrime_bipartiteEdgeMonomialIdeal_iff`, `hhEdgeSet_diagonal`,
  the `remove_inl_uncovers` / `remove_inr_uncovers` /
  `minimalVertexCover_*` cluster (lines 270–497), plus
  `bipartiteEdgeMonomialIdeal_equidimensional`,
  `bipartiteEdgeMonomialIdeal_isEquidim`.
- Skills: `/lean4:refactor BEI/Equidim/Bipartite.lean` then
  `/lean4:golf BEI/Equidim/Bipartite.lean`. The vertex-cover cluster is
  a strong candidate for helper extraction — three near-duplicate
  `remove_*_uncovers` lemmas, ~200 lines combined.

### Phase 3 — `BEI/Equidim/Transport.lean` (+ optional `ClosedGraphIntervals.lean`)

- Source range: lines 549–961.
- Move: regular elements (`sum_X_not_mem_minimalPrime`,
  `sum_XY_isSMulRegular`), ideal-level transport
  (`rename_yPredVar_monomialInitialIdeal`), `isEquidim_of_ringEquiv`,
  `yPredEquiv` and helpers, `monomialInitialIdeal_isEquidim`.
- **Decision point before starting:** is
  `closedGraph_componentCount_le_card_add_one` and the surrounding closed-
  graph component-count cluster (lines 825–961, ~140 LOC) better folded
  into `BEI/ClosedGraphs.lean`? Read both files, decide, then either:
    - put it in `BEI/Equidim/ClosedGraphIntervals.lean`, **or**
    - move it to `BEI/ClosedGraphs.lean` and skip the new file.
- Skills: `/lean4:refactor` then `/lean4:golf` on each of the new files
  produced by this phase.

### Phase 4 — Block 6 in-place refactor (no file move)

- Stay inside `BEI/Equidim.lean`. **No new file** in this phase.
- Targets:
    - `isSMulRegular_map_diagSubstHom` (line ≈1836, 589 lines).
      Carve into 4–5 named private helpers, each ≤ 150 lines.
    - `monomialInitialIdeal_isCohenMacaulay` (line ≈8160, 291 lines).
      Carve into ≤ 3 named private helpers.
- Skills: `/lean4:refactor BEI/Equidim.lean:1836` first, then
  `/lean4:refactor BEI/Equidim.lean:8160`. **Do not** run `/lean4:golf`
  on the whole file in this phase — too large to be safe in one pass.
  After both refactors land, run a focused golf pass per new helper:
  `/lean4:golf BEI/Equidim.lean:<helper-line>`.
- Acceptance: no single declaration in `BEI/Equidim.lean` exceeds 200
  lines after this phase. Build must stay green throughout.

### Phase 5 — `BEI/Equidim/IteratedRegularity.lean`

- Source range: lines 962–3441. **Largest file in the split** (~2480 LOC
  even after phase 4).
- Move: everything from `/-! ## Regular sequence infrastructure` through
  the end of `/-! ### Full regular sequence of length n + 1`.
- Skills: `/lean4:refactor BEI/Equidim/IteratedRegularity.lean` first
  with `--scope=file` to find more helper extraction opportunities now
  that the file is isolated, then `/lean4:golf
  BEI/Equidim/IteratedRegularity.lean`. Both runs may take noticeable
  time on a file this size — accept the wait.
- This file may legitimately need to stay > 1000 LOC. The acceptance
  criterion is "no declaration > 200 LOC", not "file < N LOC".

### Phase 6 — `BEI/Equidim/AugmentationLocalCM.lean`

- Source range: lines 3442–3704. ~265 LOC.
- Move: `augIdeal`-level CM machinery, the last-pair-permutation lemmas,
  and **both** `set_option synthInstance.maxHeartbeats 400000` blocks
  (`isSMulRegular_mk_y_last`, `isCohenMacaulayLocalRing_reducedHH_at_augIdeal`).
- Skills:
    - First, **profile** before any change:
      `mcp__lean-lsp__lean_profile_proof BEI/Equidim/AugmentationLocalCM.lean <line>`
      on each `synthInstance.maxHeartbeats` block. Per
      `cleanup/LEAN_PERFORMANCE_TRIAGE.md`, the suspected cause is
      repeated instance synthesis.
    - Then `/lean4:refactor BEI/Equidim/AugmentationLocalCM.lean`. The
      `letI` / explicit instance binding mentioned in the triage guide is
      a refactor-shape change.
    - Finally `/lean4:golf BEI/Equidim/AugmentationLocalCM.lean`.
- After this phase, attempt to remove the `synthInstance.maxHeartbeats`
  raises one at a time. Do not remove if the build fails — restore and
  document which one needed it.

### Phase 7 — `BEI/Equidim/GlobalCM_Setup.lean`, then `F2Scaffolding.lean`

- Two sub-files moved sequentially in two commits.
- Source ranges: 3705–4001 (`GlobalCM_Setup`) and 4002–4400 (`F2Scaffolding`).
- Move from `GlobalCM_Setup`: `augIdeal_le_of_forall_mkI_X_mem`,
  flat-base-change material, `minimalPrime_le_augIdeal`,
  `exists_smulRegular_in_augIdeal`, `bipartiteEdgeMonomialIdeal_isMonomial`,
  `isMonomial_homogeneousComponent_mem`.
- Move from `F2Scaffolding`: `hhNbhd`, `hhIndep`, `hhSurvivors`,
  `pairedSurvivors*` infrastructure, `smallerHHGraph`,
  `restrictedHHRing` and helpers.
- Skills: `/lean4:refactor` then `/lean4:golf` on each new file.

### Phase 8 — `BEI/Equidim/L4Iso.lean`, then `BEI/Equidim/L1Iso.lean`

- Two sub-files in two separate commits.
- `L4Iso`: lines 4401–5285, ~885 LOC.
- `L1Iso`: lines 5286–6275, ~990 LOC. Hosts both
  `set_option maxHeartbeats 1600000` blocks (`L1Forward_Backward_left`,
  `L1Forward_Backward_right`).
- Skills: `/lean4:refactor` then `/lean4:golf` on each. After moving
  `L1Iso`, also try the heartbeat reduction again:
    1. Halve both 1.6M raises to 800k.
    2. `lake build BEI.Equidim.L1Iso` — file-local rebuild is much
       faster than the 212 s parent build.
    3. If both fail, restore. If one succeeds, commit that one.
    4. Per `cleanup/LEAN_PERFORMANCE_TRIAGE.md`, do not lower past where
       the proof actually fails.

### Phase 9 — `BEI/Equidim/ReducedHHLocalCM.lean`

- Source range: 6276–7456. ~1180 LOC.
- Move: Session A′ (the kill-last-pair bridge), the
  `isCohenMacaulayLocalRing_at_augIdealReduced_step` /
  `isCohenMacaulayRing_at_augIdealReduced` cluster.
- Skills: `/lean4:refactor` then `/lean4:golf`. Watch carefully for
  cross-references back into the moved files — Session A′ uses material
  from `AugmentationLocalCM`, `L4Iso`, `L1Iso`.

### Phase 10 — Trim `BEI/Equidim.lean` to the residual hub

- Source range: what remains (Session B, Session C1 / `E_U`, the main
  theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`,
  paper-facing wrappers, re-exports of the public surface).
- Target file size: ≤ 300 LOC.
- Skills: `/lean4:refactor BEI/Equidim.lean` followed by
  `/lean4:golf BEI/Equidim.lean`. With the file finally short, both
  passes will be tractable.
- Update `TODO.md`, `FORMALIZATION_MAP.md`, `CLAUDE.md`. Archive this
  work package and `cleanup/EQUIDIM_DECOMPOSITION.md` to
  `guides/archive/`. Update `guides/INDEX.md`.

## Skill cheatsheet

Use these exact invocations. Always work from the project root
`/home/tom/BEI-lean`.

| Phase task | Command |
|---|---|
| Read-only audit before moving | `/lean4:review BEI/Equidim/<File>.lean` |
| After move — strategy refactor | `/lean4:refactor BEI/Equidim/<File>.lean` |
| After refactor — tactic golf | `/lean4:golf BEI/Equidim/<File>.lean` |
| Profile a heartbeat-heavy proof | `mcp__lean-lsp__lean_profile_proof` (Lean MCP) |
| Goal inspection during repair | `mcp__lean-lsp__lean_goal` (Lean MCP) |
| Test a tactic without editing | `mcp__lean-lsp__lean_multi_attempt` (Lean MCP) |
| Build + axiom check + commit | `/lean4:checkpoint "split N: <file>"` |

**Never** run `/lean4:golf` on `BEI/Equidim.lean` itself before phase 4.
The file is too large for the golf pass to terminate safely.

**Never** introduce new axioms or change theorem statements during any
phase — both refactor and golf skills enforce this and will refuse, but
manual edits must respect the same rule.

## `private` → public discipline

Many lemmas in `BEI/Equidim.lean` are `private`. Once they cross a file
boundary they need to be visible from the new home. Rules:

- If a `private` lemma is only used by the file it is moving with, keep it
  `private` in the new file.
- If it is used by a *different* file in the split (e.g. a `Bipartite`
  lemma needed by `Transport`), promote it. Do **not** change its name on
  promotion unless the name is misleading. Add a 1-line docstring if it
  does not already have one.
- Track every promotion in the commit message ("promoted N lemmas" plus a
  list).

## Variable bindings

The current file declares `variable {K : Type*} [Field K]` and similar at
the top. Each new file must re-establish the variable bindings it uses.
Do not rely on the residual `BEI/Equidim.lean` variables to leak into
imports — they will not.

## Things that must **not** change

- Statements of `monomialInitialIdeal_isCohenMacaulay`,
  `prop_1_6_herzogHibi`, `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`,
  `monomialInitialIdeal`, `bipartiteEdgeMonomialIdeal`, `IsEquidim`,
  `SatisfiesProp1_6Condition`, `HerzogHibiConditions`.
- The `synthInstance.maxHeartbeats 400000` and
  `maxHeartbeats 1600000` raises must be preserved verbatim during the
  move. Profiling and reduction is a *separate* step (see
  `cleanup/LEAN_PERFORMANCE_TRIAGE.md`).
- No new axioms.
- No new `sorry`.

## Verification at every step

After each commit:

1. `lake build` must succeed for the whole project.
2. `lean_verify` on the public theorems
   (`monomialInitialIdeal_isCohenMacaulay`, `prop_1_6_herzogHibi`,
   `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`)
   must report the same axiom set as before the split.
3. Compile time of the largest remaining file should never grow above the
   pre-split parent's 212 s baseline.

## Definition of done

The work package is complete when:

1. `BEI/Equidim.lean` is ≤ 300 lines and reads as a public theorem hub.
2. No file under `BEI/Equidim/` exceeds ~1200 lines.
3. No single declaration exceeds ~200 lines.
4. The `lake build` time for any single file in `BEI/Equidim/` is ≤ 60 s
   (down from 212 s for the monolith).
5. The full project still builds clean with no new warnings.
6. The toMathlib extraction commit `d53e84d` and this work package are both
   referenced from the final commit's message.
7. `TODO.md`, `FORMALIZATION_MAP.md`, `CLAUDE.md`, and
   `cleanup/EQUIDIM_DECOMPOSITION.md` are updated; the latter is archived.
8. This work package is archived to `guides/archive/`.

## Out of scope

- Moving more material to `toMathlib/`. The first round (commit `d53e84d`)
  already extracted the obvious general-algebra lemmas. Further extraction
  is a follow-up only if a downstream BEI consumer needs a still-private
  helper.
- Any change to the proofs of `L1Forward_Backward_left/right`, the
  `synthInstance.maxHeartbeats` blocks, or the main CM theorem.
- File-splitting any of `BEI/PrimeIdeals.lean`,
  `BEI/GroebnerDeformation.lean`, etc. Those are tracked in
  `cleanup/FILE_SPLITTING_PLAN.md`.

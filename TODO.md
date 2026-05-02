# BEI Lean Formalization — TODO

## Status Legend

- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Current Tasks

### Homepage And Public Docs

- `[x]` Inline a compact "Definitions in Lean" block on the homepage (after the
  $P_4$ plate, before the Sections grid). Shows the four core declarations —
  `BinomialEdgeVars`, `binomialEdgeIdeal`, `IsClosedGraph`, and
  `binomialEdgeMonomialOrder` — in actual Lean, with file links.
- `[x]` Add a small file map (one-line gloss per Lean file under `BEI/` and
  `toMathlib/`). Lives at [`docs/code-map.md`](docs/code-map.md), linked from
  the homepage `Project Links` and the site nav.

### Cleanup And Maintenance Backlog

- `[x]` Review archived and dormant support material and decide what still
  deserves explicit status tracking. Done 2026-05-01: the previously-tracked
  dormant sorries in `toMathlib/HeightAdditivity.lean` and
  `toMathlib/GradedCM.lean` are gone (the file no longer exists or is
  sorry-free after the finite-free Case C route landed); `BEI/` and
  `toMathlib/` are sorry-free. The bloated archive enumeration in
  `guides/INDEX.md` was collapsed to a one-paragraph pointer.
- `[x]` Keep non-critical infrastructure issues separate from the completed
  paper-result status. Done 2026-05-01: TODO.md already separates the
  "Cleanup And Maintenance Backlog" / "Speed And Clarity Backlog" / "Lean
  File Review Queue" sections from the "Current Status Snapshot" /
  "Paper Map Snapshot" sections, and FORMALIZATION_MAP.md is paper-vs-Lean
  only. Treated as an evergreen organizational rule, not a discrete task.
- `[x]` Public theorem layer cleanup where the exported declarations can be
  presented more cleanly. Done 2026-05-02: all 6 targets of
  [`guides/archive/PUBLIC_THEOREM_LAYER.md`](guides/archive/PUBLIC_THEOREM_LAYER.md)
  consumed (Theorem 2.1 packaging, Section 3 dimension/surrogate, Theorem 3.2
  narrative, Prop 3.8 / Cor 3.9 packaging, Prop 1.6 transfer surface, Cor 1.3
  + paper-statement fidelity notes). Module headers now list paper-facing
  endpoints; ~46 internal scaffolding declarations privatized after
  reference audits; fidelity-vs-paper notes added where the Lean statement
  differs from Herzog et al. 2010.
- `[x]` File-splitting cleanup. Target 3
  (`PrimeDecompositionDimension.lean`) split into Core / residual /
  `Prop1_6Equidim.lean` on 2026-05-02. Targets 2, 4, 5, 6 of
  [`guides/cleanup/FILE_SPLITTING_PLAN.md`](guides/cleanup/FILE_SPLITTING_PLAN.md)
  were dropped on 2026-05-02 as cosmetic — the LOC live inside a few
  monolithic proofs, so renaming files without carving those proofs first
  just relabels the bulk. Target 7 (`GroebnerDeformation.lean`) remains
  deferred per the guide.

### Fat Single-Proof Refactor (added 2026-05-02)

The real navigation pain in the largest files comes from a small number of
monolithic proofs. Carve each into named private sub-lemmas, verify
`lake build` is clean, and check `#print axioms` for any flagship theorem
on the consumer side after each carve. Order is rough — easiest / lowest
risk first, the load-bearing Section 2 monolith last.

| # | LOC | File:line | Declaration |
|---|---|---|---|
| `[x]` 1 | 188 → 27 | `BEI/Prop1_6Equidim.lean:434` | `path_cutVertex_of_erase` (warmup, done 2026-05-02). Reused the existing `componentCount_lt_of_merged` (moved up in file) instead of reproving the pigeonhole inline; extracted the path-graph opposite-sides argument as `path_witnesses_opposite_sides`. Net file shrinkage: ~98 LOC. `path_isEquidim` and `prop_1_6_equidim` remain axiom-clean. |
| `[x]` 2 | 357 → 231 | `BEI/Equidim/IteratedRegularity.lean` | `caseD_nilradical_nzd_map_diagSubstHom_helper` (done 2026-05-02). Mathematical content is intrinsic (no shorter proof exists), but the proof had heavy sx/sy duplication. Extracted four private helpers: `caseD_both_monomials_in_image` (~50 LOC, both `dx` and `dy` lie in `Iφ`), `caseD_typeA_exponent_zero` (~45 LOC, type-A image at `Sum.inl i` / `Sum.inr i` is zero — replaces 28-LOC duplicate twice), `caseD_typeB_exponent_eq` (~10 LOC, type-B singleton support extraction — replaces 7-LOC duplicate twice), and `caseD_HH_contradiction` (~50 LOC, HH transitivity tail). `proposition_1_6` axiom-clean. |
| `[!]` 3 | 612 | `BEI/Prop1_6Equidim.lean:642` | `closedGraph_cutVertex_preserved_of_erase`. Investigated 2026-05-02 with the carving methodology: math content is intrinsic (closed-graph + Prop-1.6 rigidity argument via 4-way case split on bridge orientations × inner sub-splits on vertex orderings). Already uses every available helper (`componentCount_lt_of_merged`, `exists_adj_bridge_of_sameComponent_erase`, `adj_of_gap`, `closedGraph_adj_between`, `reflTransGen_convex_closed`, `SameComponent_mono`). The 4 inline `have`s (`mk_sc`, `convex_a`, `convex_b`, `edge_contra`) capture local context (`a`, `b`, `hnotsc_S`); extracting them as top-level helpers requires ~12-15-arg signatures and increases total LOC. Each of the 4 case bodies (60–195 LOC) could be a private helper but signature overhead negates the gain. **No productive simplification found.** A real reduction would require a brand-new "closed-graph components are convex intervals" structural lemma (200+ LOC of new proof). Skipped — spending further effort here is negative-value. |
| `[x]` 4 | 384 → 314 | `BEI/CoveredWalks.lean` | `isRemainder_fij_of_covered_walk` (done 2026-05-02). The methodology found that the y-sibling at line 872 shares ~135 LOC of *textually identical* sub-walk surgery (`τ.drop k` and `τ.take (k+1)` extractions). Pulled out two reusable helpers `subWalk_drop` and `subWalk_take` that abstract the "extract sub-walk at internal vertex" pattern. Used 4× across the x and y variants. `theorem_2_1` axiom-clean. Same helpers also applicable to the 6 sub-walk extractions inside #10 (`isRemainder_fij_of_mixed_walk`) — folded as part of that carve. |
| `[x]` 5 | 362 → 298 | `BEI/CoveredWalks.lean` | `isRemainder_fij_of_covered_walk_y` (done 2026-05-02 as part of #4 — the new `subWalk_drop` / `subWalk_take` helpers are used here too). |
| `[ ]` 6 | 263 | `BEI/Equidim.lean:391` | `cm_F2_route` |
| `[ ]` 7 | 263 | `BEI/Equidim/IteratedRegularity.lean:447` | `ell_not_mem_minimalPrime_map_diagSubstHom` |
| `[ ]` 8 | 281 | `BEI/PrimeIdeals.lean:1753` | `lemma_3_1` |
| `[ ]` 9 | 532 | `toMathlib/CohenMacaulay/Polynomial.lean:637` | `cm_localize_polynomial_of_cm_aux` (toMathlib-side; isolated from BEI fixes) |
| `[x]` 10 | 1087 → 835 | `BEI/CoveredWalks.lean` | `isRemainder_fij_of_mixed_walk` (done 2026-05-02). Capitalized on the `subWalk_drop` / `subWalk_take` helpers extracted in #4/#5. The mixed-walk proof has **6** sub-walk extractions (3 pairs in 3 different code branches), all textually identical to the patterns in the x/y siblings. Generalized the helpers' preconditions from `a < v₀` / `v₀ < b` to `v₀ ≠ a` / `v₀ ≠ b` so the third branch (which has `v₀ < a` and `v₀ < b`) could reuse them. `theorem_2_1` axiom-clean. File-level: `BEI/CoveredWalks.lean` shrunk from 2671 → 2390 LOC across #4/#5/#10. |
| `[ ]` 11 | 1848 | `BEI/GroebnerBasisSPolynomial.lean:143` | `theorem_2_1` (load-bearing public Buchberger proof; refactor last, with extra care) |

Smaller fat proofs to fold into adjacent carves only when they sit inside
the same file: `walk_from_shared_first_aux` (203, `CoveredWalks:2453`),
`killLastPairEquiv_map_augIdealQuot` (205,
`Equidim/ReducedHHLocalCM.lean:576`), `no_s_ker_mem` (191,
`PrimeIdeals.lean:949`), `swapExp_fiberEquiv` (185, `PrimeIdeals.lean:470`),
`localization_at_comap_maximal_isCM_isCM_local` (165,
`toMathlib/CohenMacaulay/Polynomial.lean:1392`).

### Defensive Infrastructure

- `[ ]` **Profile and drop the remaining heartbeat overrides.** 8 overrides
  remain across 4 files after the 2026-04-27 audit. Re-profile each with
  `lean_profile_proof` after recent refactors and remove any that are no
  longer load-bearing. Pairs with
  [`guides/cleanup/LEAN_PERFORMANCE_TRIAGE.md`](guides/cleanup/LEAN_PERFORMANCE_TRIAGE.md).
- `[ ]` **Add `BEI/AxiomCheck.lean`.** Permanent file with `#print axioms` on
  the seven flagship paper-facing theorems so axiom regressions are caught
  at build time instead of via ad-hoc scratch files.
- `[ ]` **CI heartbeat ratchet.** Fail CI when a new `set_option maxHeartbeats`
  raise is introduced without justification. Tracked in
  [`guides/cleanup/STATUS_AND_CI_HYGIENE.md`](guides/cleanup/STATUS_AND_CI_HYGIENE.md).

---

## Standing Workflow Rules

- Keep `TODO.md`, `FORMALIZATION_MAP.md`, `docs/`, and `guides/INDEX.md` in
  sync after status or website edits.
- Archive finished work packages promptly so `guides/work_packages/` contains
  only genuinely active packets.
- Remove stale references to old blockers, old proof routes, or old milestone
  language when the corresponding work is already complete.
- Use the Lean MCP tools and the `/lean4:golf` workflow intentionally during
  file-review cleanup rather than making ad hoc edits.
- `guides/work_packages/` should stay empty until a genuinely new
  theorem-critical task appears.

---

## Current Status Snapshot

### Repository Status

- `[x]` Sections 1--4 are represented in Lean.
- `[x]` The named paper results are all covered.
- `[x]` The public status pages describe the paper-to-Lean map as complete.
- `[x]` The reader-facing website copy has had an initial editorial cleanup
  pass.

### Paper Map Snapshot

- Section 1: complete.
  Equivalent packaging remains for Proposition 1.4.
- Section 2: complete.
  Theorem 2.1 remains split across the Buchberger proof, reducedness proof, and
  the wrapper theorem.
- Section 3: complete.
  Equivalent packaging remains for Proposition 3.6, Proposition 3.8, and
  Corollary 3.9.
- Section 4: complete.

This means the remaining work is cleanup, presentation, and maintenance rather
than theorem-critical formalization.

### Guide State

- Active theorem-critical work packages: none.
- Recently retired packets:
  - `guides/archive/NEXT_SESSION_PROMPT.md`
  - `guides/archive/COROLLARY_3_4_IMPLEMENTATION.md`

---

## Notes

- `FORMALIZATION_MAP.md` is the detailed paper-vs-Lean statement map.
- `guides/cleanup/` contains the current non-critical cleanup backlog.
- `guides/website/HOMEPAGE_MATH_CONTEXT_PLAN.md` is the current website-side
  planning note.

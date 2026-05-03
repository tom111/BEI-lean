# `theorem_2_1`: collapse the i<k / k<i and 4-leaf sister symmetries

## TL;DR

`theorem_2_1` (`BEI/GroebnerBasisSPolynomial.lean:143`) is **1848 LOC**,
the **largest declaration in the repo**. Investigated 2026-05-03 by a
read-only subagent and classified `[CARVE-CANDIDATE-HIGH-VALUE]`.

The proof is Buchberger's criterion for the binomial edge ideal: every
S-polynomial of two admissible-path generators reduces to 0 modulo
`groebnerBasisSet G`. The case split has 4 main branches; the bulk
(~1400 LOC) sits in Cases 2 & 3, which contain a 4-way leaf
explosion. **The leaves are textually parameterizable** — the `k<i`
branch literally opens with `fij_antisymm` reductions to the `i<k`
shape, then duplicates the logic with names swapped. Same for `j<l`
vs `l<j`. The ~50-line `(fun w hw => by ...)` coverage proof fed to
`isRemainder_fij_of_mixed_walk` appears **8× with only label
permutations**.

Estimated **1848 → ~900–1000 LOC** (~−850 LOC, **largest single LOC win
still available in the repo**). **Risk: medium** — the proof is long
but structurally repetitive, no exotic tactics, and the upstream
helpers it relies on (`isRemainder_fij_of_mixed_walk`,
`sPolynomial_decomposition'`,
`isGroebnerBasis_iff_sPolynomial_isRemainder`) are already in their
post-carve states.

This refactor has been previously deferred. With the recent Buchberger
and `groebner_implies_closed` carves shipped axiom-clean and the new
`BEI/AxiomCheck.lean` regression check in place, the helper budget for
splitting `theorem_2_1` is now genuinely healthier than at the time of
the original deferral.

## Status

**ARCHIVED 2026-05-03** — all five stages landed.

- File `BEI/GroebnerBasisSPolynomial.lean`: **1991 → 1455 LOC (−536 LOC,
  27% reduction)** across Stages 1–5.
- `theorem_2_1` axioms unchanged: `[propext, Classical.choice, Quot.sound]`.
  Locked in by `BEI/AxiomCheck.lean`.
- Stage commits on master: `d7b5350` (cycle fix), `ed7c8ad` (Stages 1+2),
  `5269295` (guide progress note), `43de6a1` (Stage 3), `6526e8a` (Stage 4),
  `368eacf` (Stage 5).

Per-stage savings:

| Stage | Helper | LOC before | LOC after | Δ |
|---|---|---|---|---|
| 1 | `cov_inr_or_inl_of_admissible_path` (24× reuse) | 1991 | ~1758 | −233 |
| 2 | `degree_monomial_mul_fij` (5× reuse) | ~1758 | 1718 | −40 |
| 3 | `case4_remainder` + `case5_remainder` (each 2× reuse) | 1718 | 1658 | −60 |
| 4 | `fij_degree_inr_eq_zero` + `fij_degree_inl_eq_zero` (32× reuse) | 1658 | 1550 | −108 |
| 5 | tighten leftovers (drop now-redundant haves/sets, hoist) | 1550 | 1455 | −95 |

The original guide forecast ~1848 → 900–1000 LOC (~−850). The actual
−536 was less aggressive because Stage 4's full leaf-fold helper
described in the guide was **not** attempted: the helper signature
would have grown beyond what its body savings justified (~14
parameters, including path-inclusion direction and per-Q "skip"
witness terms). A smaller cross-cutting `fij_degree_*_eq_zero`
extraction was substituted, hitting 32 occurrences with a 4-LOC
helper instead.

Originally marked `[!]` in the "Fat Single-Proof Refactor" table of
`TODO.md` (item #11). This guide superseded that skip note.

## Goal

1. The statement is **byte-identical** (signature, name, namespace,
   declaration kind — `theorem`, not `private`).
2. **No new axioms**: the existing `BEI/AxiomCheck.lean` block for
   `theorem_2_1` must continue to pass *unchanged*. If you need to
   modify any other AxiomCheck block (e.g. because a refactored
   declaration appears with a slightly different name), that is itself
   a regression — stop and re-plan.
3. The body is materially shorter, structured around 2–4 new private
   helpers (see "The proposed helpers" below).
4. `lake build` is clean, with no new heartbeat overrides.
5. **All eleven flagship theorems** in `BEI/AxiomCheck.lean` continue
   to pass after every stage commit.

## Where the proof lives

The case dispatch in the proof body is `by_cases heq_i : i = k <;>
by_cases heq_j : j = l`. Bracketing line numbers from the 2026-05-03
state of `BEI/GroebnerBasisSPolynomial.lean`:

| Block | Lines | Body | LOC |
|---|---|---|---|
| Header (`hUnit`, `not_head_of_internal'`, `not_last_of_internal'`) | ~143–161 | Setup. | ~18 |
| Case 1 | 162–173 | `i = k`, `j = l` (same endpoints). Trivial. | 12 |
| Case 4 | 174–373 | `i = k`, `j ≠ l` (shared first endpoint). Splits on `j < l` vs `l < j`. | 200 |
| Case 5 | 374–589 | `j = l`, `i ≠ k` (shared last endpoint). Sister of Case 4 with swap; splits on `i < k` vs `k < i`. | 216 |
| Cases 2 & 3 (combined) | 590–end | "Disjoint or cross-matched". Has nested sub-cases. | ~1400 |
| ... Same-component branch | 630–1842 | Has 4-way leaf explosion. | ~1200 |
| ... ... `i < k` branch | 694–1245 | Splits on `j < l` / `l < j`. | ~552 |
| ... ... `k < i` branch | 1246–1842 | **Sister of `i < k`** — opens with `fij_antisymm` reductions then duplicates. | ~597 |
| ... Different-components branch | 1843–end | Coprime leading terms; short. | ~150 |

**Eight leaf bodies share the same coverage-lambda skeleton:**

- Cases 4: lines 258–311, 312–373 (`j < l`, `l < j` — but Case 4 is shorter)
- Case 5: lines 452–520, 521–589
- Cases 2 & 3, `i < k`: lines 804–969, 970–1245
- Cases 2 & 3, `k < i`: lines 1375–1547, 1548–1842

Each of these is built around an `isRemainder_fij_of_mixed_walk` call
whose final argument is a ~50-line `(fun w hw => by ...)` lambda
proving the coverage hypotheses with `by_cases hw_eq_X / hw_eq_Y` +
`sPolyD_ge_of_zero`.

## The proposed helpers

### Helper 1: `mixed_walk_coverage_lambda` (low-risk, biggest win)

Extract the ~50-line `(fun w hw => by ...)` lambda body fed to
`isRemainder_fij_of_mixed_walk` into a top-level private helper
parameterised by:

- the four endpoints `(a b X Y : V)` and their order witnesses,
- the path data `(τ : List V)` and its head/last/nodup/walk hypotheses,
- the four "fij_*0" skolems (`hfij_inr0`, `hfkl_inr0`, `hfij_inl0`,
  `hfkl_inl0`).

Used **8×** with only label permutations. Estimated savings: ~280 LOC.
Land this first — it's the biggest mechanical win and validates the
parameterisation before the riskier helpers.

### Helper 2: `case2_3_branch_combine` (low-risk)

The post-`h₁ h₂` ring/`degree_ne`/`isRemainder_add_of_degree_ne`
finisher (~25 LOC) is repeated 8×. Extract once, parameterise on the
two reduced polynomials and the discriminator hypothesis. Estimated
savings: ~150 LOC.

### Helper 3: `case4_case5_branch` (medium-risk)

Fold Case 4's two sub-cases (`j < l`, `l < j`) into a single helper
parameterised by which endpoint is shared. Reuse for Case 5 by a
symmetric application. Collapses ~416 LOC of body into one ~150 LOC
helper called twice. Risk: parameterising "which endpoint is shared"
(first vs last) requires careful handling of `fij` argument order.

### Helper 4: `case2_3_lt_branch` (medium–high risk)

Single helper for the `i < k` / `j < l` leaf, applied **4×** across
the four leaf bodies (`i<k j<l`, `i<k l<j`, `k<i j<l`, `k<i l<j`)
with permuted arguments. The `k<i` leaves apply via `fij_antisymm`
reductions; the `l<j` leaves apply by reflecting. Collapses ~2200 LOC
of leaves into ~600 LOC. Risk: this is the most delicate
parameterisation — at least 8–10 hypothesis arguments. **Stop here if
helpers 1–3 already produce a satisfying total reduction.**

## Concrete refactor plan

Work in **stages**, with `lake build` clean and the full
`BEI/AxiomCheck.lean` suite passing after each stage. Commit each
stage separately.

### Stage 0: orientation pass (cheap)

- Read all eight leaf bodies end-to-end. Confirm the textual symmetry
  claim by diffing pairs (e.g., `i<k j<l` vs `i<k l<j`, then `i<k j<l`
  vs `k<i j<l`).
- Note any leaf that diverges materially. If you find one, **stop and
  re-plan**: the helper signatures derived from the "uniform" leaves
  won't fit a divergent one.
- Confirm `subWalk_drop` / `subWalk_take` (in `BEI/CoveredWalks.lean`)
  are *already* used inside `theorem_2_1` — the broader CoveredWalks
  carve folded these in. If not, that's a separate easy win.

### Stage 1: extract Helper 1 (`mixed_walk_coverage_lambda`)

- Add the new private helper near the top of
  `BEI/GroebnerBasisSPolynomial.lean` (before `theorem_2_1`).
- Replace the 8 inline lambda bodies with helper calls.
- Build, run `lake build BEI.AxiomCheck` to verify all 11 axiom
  assertions still pass, commit.

### Stage 2: extract Helper 2 (`case2_3_branch_combine`)

- Same pattern. Smaller helper, smaller per-call savings.
- Build + AxiomCheck + commit.

### Stage 3: extract Helper 3 (`case4_case5_branch`)

- Higher-risk helper: parameterise on the "which endpoint" choice
  carefully.
- Build + AxiomCheck + commit.

### Stage 4: extract Helper 4 (`case2_3_lt_branch`)

- Highest-risk helper. **Optional** — only attempt if Stages 1–3
  shipped without difficulty and the projected total LOC win still
  justifies the helper's signature complexity.
- Build + AxiomCheck + commit.

### Stage 5: tighten

- After Stages 1–4, look for now-redundant `have`s and `set`s in the
  surrounding scaffolding.
- Final build + AxiomCheck + commit.

## Verification recipe

After every commit on this work, run:

```
lake build
lake build BEI.AxiomCheck
```

Then via the Lean MCP:

```
lean_verify file=BEI/GroebnerBasisSPolynomial.lean theorem=theorem_2_1
```

Must report `axioms = [propext, Classical.choice, Quot.sound]`,
no warnings.

The full flagship-theorem cross-check is now mechanised by
`BEI/AxiomCheck.lean` — if any of the 11 `#guard_msgs` blocks fires,
the build itself fails. So `lake build BEI.AxiomCheck` is the
canonical regression check.

## Risks

1. **Sister-symmetry break.** If one of the 8 leaves has a subtle
   variation the agent missed, the Stage 1 lambda extraction won't
   typecheck. Mitigation: read all 8 leaves in Stage 0 and abort on
   divergence.
2. **`fij_antisymm` parameterisation pain.** The `k<i` and `l<j`
   variants use `fij_antisymm` to reduce to the `<`-direction; folding
   this into Helper 4 requires careful sign tracking. Mitigation: stop
   at Stage 3 if Stage 4 won't pay for itself.
3. **Heartbeat regressions.** `theorem_2_1` is already a long proof.
   Any new `set_option maxHeartbeats` raise is a smell — extract
   sub-helpers instead.
4. **Statement drift.** It is *very easy* to accidentally change the
   `theorem_2_1` statement when refactoring. The
   `BEI/AxiomCheck.lean` regression check catches axiom drift but
   *not* signature drift. Diff the theorem header byte-for-byte at
   each commit.

## Rollback

Revert with `git revert` of the specific stage commits. Each stage
should be its own commit so individual stages can be rolled back
independently. Do **not** force-push.

## Remaining work (2026-05-03)

Stages 1 and 2 are done. Two private helpers were added near the top of
`BEI/GroebnerBasisSPolynomial.lean`:

- `degree_monomial_mul_fij` — eliminates the 6-line
  `degree (monomial Q 1 * fij a b) = ...` calculation that appeared
  5×.
- `cov_inr_or_inl_of_admissible_path` — eliminates the ~12-line
  per-vertex coverage proof that appeared 24× across the eight
  `isRemainder_fij_of_mixed_walk` lambda bodies in the Cases 2 & 3
  same-component branch.

The bonus side-fix: removing the redundant `import BEI.AxiomCheck` from
`BEI.lean` broke the `BEI ↔ BEI.AxiomCheck` import cycle introduced in
commit `0362f5e`. The lib glob still picks up `BEI.AxiomCheck`, so the
`#guard_msgs` regression block still runs.

Stage 3 (Cases 4 & 5 fold) is **not** yet attempted. The local
`cov_inr_of_lt_i_π` / `cov_inl_of_gt_j` helpers in those cases would
need lifting to module scope before a fold is feasible; that's a
larger refactor than the per-leaf path-classification work that Stage
1 covered. Stage 4 (single helper for the four `isRemainder_fij_of_mixed_walk`
leaves) remains "highest-risk" per the original plan and was
deliberately skipped.

## Methodology reminders (from `feedback_fat_proof_carving.md`)

- Before touching the proof, **state in your own words** what
  `theorem_2_1` is mathematically trying to prove (Buchberger
  criterion forward direction: every S-polynomial of admissible-path
  generators reduces to 0 modulo `groebnerBasisSet G`).
- **Sketch the simpler proof** ignoring the existing one. The natural
  approach is exactly the existing one — case-split on shared
  endpoints, build a covering walk for each S-polynomial, apply
  `isRemainder_fij_of_mixed_walk`. The wins here are *plumbing
  through symmetry*, not reformulation.
- The two recent successful work packages
  (`guides/archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md` and
  `guides/archive/GROEBNER_IMPLIES_CLOSED_REFACTOR.md`) are good
  templates for the stage / verify / commit cadence.
- The `BEI/AxiomCheck.lean` regression file is the canonical
  cross-check — `lake build BEI.AxiomCheck` after every stage commit
  should be a one-line ritual.
- **Do not extract sub-`have`s into named lemmas as a first resort.**
  The win here is the four parameterized helpers above. Other inline
  `have`s deserve names only if they cleanly factor across multiple
  call sites.

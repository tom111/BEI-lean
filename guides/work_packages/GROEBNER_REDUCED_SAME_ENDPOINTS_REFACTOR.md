# `groebnerElement_reduced_same_endpoints`: reuse existing CoveredWalks helpers

## TL;DR

`groebnerElement_reduced_same_endpoints` (`BEI/GroebnerBasis.lean:229`) is
**274 LOC**. About **~85 LOC of its body reinvents helpers that already
exist in `BEI/CoveredWalks.lean`** — `mem_internalVertices_of_ne`,
`internal_ne_getLast`, `head_of_head?`, `getLast_of_getLast?`. Plus a
sister lemma in the *same* file (`groebnerElement_leadingMonomial_squarefree`
at line 615) repeats the same ~27 LOC of "endpoint is not internal"
reasoning, so a single new helper benefits both.

Estimated **274 → ~190 LOC** (~30% reduction), with bonus savings
(~27 LOC) at the sister call site. **Risk: low** — the extractions
replace inline reinventions with calls to already-tested utilities, no
clever parameterisation required.

## Status

- Discovered: 2026-05-02 broader fat-proof scan.
- Investigated by a read-only subagent 2026-05-02; classified as
  `[CARVE-CANDIDATE]` low risk.
- Proof is **stable and axiom-clean**
  (`{propext, Classical.choice, Quot.sound}`); do not touch unless
  committed to the full refactor.
- Marked `[ ]` in the "Newly-discovered fat proofs" table of `TODO.md`.

## Goal

Refactor `groebnerElement_reduced_same_endpoints` so that:

1. The statement is **byte-identical** (signature, name, namespace,
   declaration kind).
2. **No new axioms** are introduced. After the refactor, `lean_verify`
   on `groebnerElement_reduced_same_endpoints`, `theorem_2_1`, and the
   five flagship theorems (see Verification recipe) must still report
   `[propext, Classical.choice, Quot.sound]`.
3. The body is materially shorter, structured around already-existing
   `CoveredWalks` helpers plus one new helper that benefits both the
   primary target and its same-file sister.
4. `lake build` is clean, with no new heartbeat overrides.

The same-file sister `groebnerElement_leadingMonomial_squarefree`
(line 615) gets ~27 LOC removed for free as part of this work — record
that bonus reduction in the commit message but do not change its
statement.

## Where the proof lives

| Block | Lines | Role |
|---|---|---|
| Statement + setup | 229–239 | Theorem header, basic destructuring. |
| **Step 1: `mem_int`** | 240–~290 | Inline ~50-LOC argument that reinvents `mem_internalVertices_of_ne` from CoveredWalks. |
| **Step 1: `j_not_int`** | ~290–347 | Inline ~50-LOC argument that reinvents `internal_ne_getLast` (and supporting `head_of_head?` / `getLast_of_getLast?` patterns). |
| Step 1: degree bound | (within above) | A 50-LOC degree-bound argument showing `internalVertices π₁ ⊆ internalVertices π₂`. **Genuinely intrinsic** — leave it. |
| Step 2: vertex containment | 349–359 | `π₁ ⊆ π₂`. Short. |
| Step 3: path-surgery `π'` | 360–500 | Find first-difference index k via `Nat.find`; build `π' = π₂.take k ++ π₂.drop n`; verify shorter admissible path; invoke `hπ₂_min` to close. **Genuinely intrinsic** — leave it. |
| Sister: `groebnerElement_leadingMonomial_squarefree` | 615–641 | Same file. Duplicates `hi_not_int` / `hj_not_int` (~27 LOC) of the "endpoint is not internal" reasoning. |

## The existing helpers to reuse

All in `BEI/CoveredWalks.lean`:

| Helper | Line | What it does |
|---|---|---|
| `mem_internalVertices_of_ne` | 1315 | Membership in `internalVertices τ` from non-headness + non-lastness. |
| `internal_ne_getLast` | 1284 | An internal vertex is not the last element. |
| `internal_ne_head` | 1272 | Mirror: an internal vertex is not the head element. |
| `head_of_head?` | 1301 | Convert `head? = some a` to a concrete head equality. |
| `getLast_of_getLast?` | 1308 | Mirror: `getLast? = some b` to last equality. |

If `BEI/GroebnerBasis.lean` does not already import `BEI.CoveredWalks`,
check the import graph — these helpers must be visible at the call site.

## The proposed new helper

Both `groebnerElement_reduced_same_endpoints` and
`groebnerElement_leadingMonomial_squarefree` derive "the endpoints
`i, j` of an admissible path `π` are not in `internalVertices π`".
The two derivations are textually parallel.

Proposed:

```
private lemma endpoint_notMem_internalVertices_admissible
    (G : SimpleGraph V) {i j : V} (π : List V)
    (hπ : IsAdmissiblePath G i j π) :
    i ∉ internalVertices π ∧ j ∉ internalVertices π := by
  ...
```

Drop it next to or just before `groebnerElement_reduced_same_endpoints`
in `BEI/GroebnerBasis.lean`. Use it twice — once in the primary
target, once in the sister.

(If a more direct framing suits the call sites — e.g., separate
`endpoint_left` / `endpoint_right` lemmas — prefer that.)

## Concrete refactor plan

Work in **stages**, with `lake build` clean and `lean_verify` on
`groebnerElement_reduced_same_endpoints` axiom-clean after each
checkpoint. Commit each stage separately.

### Stage 0: confirm imports + sister duplication (cheap)

- Verify `BEI/GroebnerBasis.lean` imports (transitively or directly)
  `BEI/CoveredWalks.lean`, so the helpers above are in scope.
- Read both `groebnerElement_reduced_same_endpoints` and
  `groebnerElement_leadingMonomial_squarefree` end-to-end to confirm
  the agent's claim that the endpoint-non-internal reasoning is
  textually duplicated.
- If a divergence appears, **stop and re-plan** before extracting the
  shared helper.

### Stage 1: replace inline `mem_int` with `mem_internalVertices_of_ne` (low risk)

- Excise the inline ~50-LOC `mem_int` block from
  `groebnerElement_reduced_same_endpoints`.
- Replace each call site with `mem_internalVertices_of_ne` from
  CoveredWalks.
- May need to use `head_of_head?` / `getLast_of_getLast?` to convert
  the `head? = some i` / `getLast? = some j` hypotheses already in
  scope.
- Build, axiom-check.

### Stage 2: replace inline `j_not_int` with `internal_ne_getLast` (low risk)

- Excise the inline ~50-LOC `j_not_int` block.
- Replace each call site with `internal_ne_getLast`.
- Build, axiom-check.

### Stage 3: extract `endpoint_notMem_internalVertices_admissible` (low–medium risk)

- Add the new helper next to `groebnerElement_reduced_same_endpoints`.
- Use it in `groebnerElement_reduced_same_endpoints`.
- Use it in `groebnerElement_leadingMonomial_squarefree` (the sister
  at line 615) to remove the parallel ~27-LOC duplication.
- Build, axiom-check both targets.

### Stage 4 (optional bonus): extract `firstDiffIdx`

- The agent flagged: a tiny private lemma packaging `k`, `hk_ne`,
  `hk_min`, `hk_pos`, `hk_lt` for two non-equal lists sharing a first
  element would clean up the entry to Step 3.
- Only do this if it actually shortens the surrounding code; the
  parameter list may eat the savings.

## Verification recipe

After every commit on this work, run:

```
lake build
```

Then via the Lean MCP:

```
lean_verify file=BEI/GroebnerBasis.lean
            theorem=groebnerElement_reduced_same_endpoints
lean_verify file=BEI/GroebnerBasis.lean
            theorem=groebnerElement_leadingMonomial_squarefree
```

Both must report `axioms = [propext, Classical.choice, Quot.sound]`,
no warnings.

Plus the standard flagship-theorem cross-check:

```
lean_verify file=BEI/GroebnerBasisSPolynomial.lean theorem=theorem_2_1
lean_verify file=BEI/Proposition1_6.lean           theorem=proposition_1_6
lean_verify file=BEI/Corollary3_4.lean             theorem=corollary_3_4
lean_verify file=BEI/Corollary3_4.lean             theorem=corollary_3_7_cm_fin
lean_verify file=BEI/Equidim.lean                  theorem=monomialInitialIdeal_isCohenMacaulay
```

All five must remain axiom-clean.

## Risks

1. **Hypothesis-shape mismatch.** The CoveredWalks helpers (especially
   `mem_internalVertices_of_ne`) take `head? = some a` / `getLast? =
   some b` style hypotheses; the local proof may have those in slightly
   different forms. Use `head_of_head?` / `getLast_of_getLast?` (already
   in CoveredWalks) to bridge.
2. **Sister divergence.** The sister at line 615 may differ from the
   primary in ways not yet noted; if so, drop Stage 3 and ship Stages
   1–2 only.
3. **Heartbeat regressions.** Watch for `set_option maxHeartbeats`
   raises after each stage.
4. **Step 3 path surgery.** Do not touch Step 3 — it is genuinely
   intrinsic and the existing implementation is sound.

## Rollback

Revert with `git revert` of the specific stage commits. The original
proof is preserved in the git history.

## Methodology reminders (from `feedback_fat_proof_carving.md`)

- Before touching the proof, **state in your own words** what
  `groebnerElement_reduced_same_endpoints` is mathematically trying to
  prove (reducedness for the same-endpoint case of Theorem 2.1: if two
  distinct admissible (i,j)-paths π₁ ≠ π₂ have leading-monomial
  divisibility, derive False by building a strictly shorter admissible
  path inside π₂).
- **Sketch the simpler proof** ignoring the existing one. The natural
  proof is exactly what the existing one does in Step 3 — find first
  difference, splice. The wins here are *plumbing*, not reformulation.
- The **Buchberger guide** (`guides/archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md`)
  and the **`groebner_implies_closed` guide**
  (`guides/archive/GROEBNER_IMPLIES_CLOSED_REFACTOR.md`) are good
  templates for the stage / verify / commit cadence.
- After each stage, **run the verification recipe above**. If
  `lean_verify` reports a new axiom, stop and investigate.
- **Do not extract sub-`have`s into named lemmas as a first resort.**
  The win here is to *delete* inline reinventions and call the
  CoveredWalks helpers — not to rename the surviving Step 3.

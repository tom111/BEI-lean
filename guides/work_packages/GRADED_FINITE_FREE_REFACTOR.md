# Graded* family refactor: deduplicate the localization bridge, sister-collapse the `aeval` proofs, and Mathlib-hunt the basis transport

## TL;DR

Four big proofs in `toMathlib/GradedFiniteFree.lean` and one duplicated
~70-LOC block across two proofs in `toMathlib/GradedRegularSop.lean`
together account for **~975 LOC** of declarations ≥150 LOC in the
graded-algebra infrastructure that landed Proposition 1.6.

Investigated 2026-05-03 by a read-only subagent. Findings:

| Target | LOC | Verdict | Lever | Saving |
|---|---|---|---|---|
| `linearIndependent_aeval_cons_step` | 247 | CARVE-CANDIDATE | extract `hfactor`/`hmod` aeval/finSuccEquiv identities | ~60–80 |
| `linearIndependent_aeval_of_basis_lift` | 245 | CARVE-CANDIDATE | sister of #1; transfer "weak regularity through `QuotSMulTop ↔ A/⟨x⟩`" | ~40–60 |
| `finiteFree_over_mvPolynomial_of_homogeneous_regular_sop` | 243 | CARVE-CANDIDATE | hunt for Mathlib `Module.Free.of_equiv` / `Basis.mapCoeffs` API | ~60–90 *if API exists* |
| `exists_homogeneous_regular_sop_aux` | 240 | INTRINSIC | bookkeeping mirrors paper proof step-by-step | ≤30 |
| `exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos` + `ringKrullDim_irrelevant_quotient_eq` | 179 + 167 | CARVE-CANDIDATE | **70 LOC of `heq_ring + hPC + hequiv_bridge` is duplicated verbatim across the two proofs** | **~60, low-risk** |

**Estimated total reduction**: ~230–280 LOC across `GradedFiniteFree.lean`
and `GradedRegularSop.lean`.

Risk pattern matches the "high risk / high gain" framing requested:
cheap Stage 0 warmup buys confidence, then escalating risk in
Stages 1–3, with Stage 3 being the genuine "Mathlib hunt or new
infra" swing. **All toMathlib-side, so paper-facing theorems
(Section 1–4) are insulated**.

## Status

- Discovered: 2026-05-03 broader fat-proof scan; investigated the
  same day.
- Proofs are **stable and axiom-clean**; the downstream paper-facing
  flagship theorems (`proposition_1_6` chiefly) all hit
  `[propext, Classical.choice, Quot.sound]`, locked in by
  `BEI/AxiomCheck.lean`.
- Marked `[ ]` in the relevant TODO row (this guide is the dedicated
  packet).

## Goal

1. Statements **byte-identical** for all five targets.
2. **No new axioms** for any flagship: `BEI/AxiomCheck.lean` must
   pass after every stage commit. `lake build BEI.AxiomCheck` is
   the canonical regression check.
3. Body of each target materially shorter via 4 new private/public
   helpers (see "Proposed helpers" below).
4. `lake build` clean, no new heartbeat overrides.

## Where the proofs live

### `toMathlib/GradedFiniteFree.lean`

| Block | Lines | Role | LOC |
|---|---|---|---|
| `span_aeval_eq_top_of_homogeneous_basis_lift` | 759 | Surjectivity of `aeval θ`-span. INTRINSIC. | 193 |
| `linearIndependent_aeval_cons_step` | 1003 | Lifts LI through `Fin n → Fin (n+1)` cons step. **#1 target.** | 247 |
| `linearIndependent_aeval_of_basis_lift` | 1285 | Inductive version of #1. **#2 target, sister of #1.** | 245 |
| `finiteFree_over_mvPolynomial_of_homogeneous_regular_sop` | 1530 | Connected graded `A` + homogeneous regular sop ⟹ `A` finite-free over `MvPolynomial(Fin d) K`. **#3 target.** | 243 |

### `toMathlib/GradedRegularSop.lean`

| Block | Lines | Role | LOC |
|---|---|---|---|
| `exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos` | 197 | Produce homogeneous NZD with quotient still CM. | 179 |
| `ringKrullDim_irrelevant_quotient_eq` | 451 | Quotient drops dim by 1. Already uses Mathlib's `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`. | 167 |
| `exists_homogeneous_regular_sop_aux` | 618 | Inductive existence of homogeneous regular sop of length `d`. INTRINSIC. | 240 |

The **duplicated localization-bridge block** sits at lines ~287–358 of
`exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos` and
~498–578 of `ringKrullDim_irrelevant_quotient_eq` — ~70 LOC of
`heq_ring + hPC + hequiv_bridge` reasoning, textually parallel.

### `toMathlib/GradedPrimeAvoidance.lean`

| Block | Lines | Role | LOC |
|---|---|---|---|
| `exists_homogeneous_notMem_of_forall_not_le` | 211 | Graded prime avoidance. INTRINSIC (the homogeneous version genuinely needs the `wu^dℓ` power trick; ungraded `Ideal.subset_union_prime` exists but does not cover this). | 172 |

## Proposed helpers

### Helper 0: `localizationAtIrrelevantOfQuotientSpan_ringEquiv` (cheapest)

Extract the ~70-LOC `heq_ring + hPC + hequiv_bridge` block duplicated
across `exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos`
(GradedRegularSop.lean:197, lines ~287–358) and
`ringKrullDim_irrelevant_quotient_eq` (line 451, lines ~498–578).

Both consumers are in the same file. Both call sites are the same
shape. The helper is purely a `RingEquiv` between
`Localization.AtPrime (irrelevant ⧸ span{x})` and the corresponding
quotient-then-localise object.

Estimated saving: ~60 LOC. **Zero risk**: no exported statement
changes, two consumers in one file.

### Helper 1: `weaklyRegular_quotient_span_iff_quotSMulTop` (sister-collapse)

Both `linearIndependent_aeval_cons_step` (#1) and
`linearIndependent_aeval_of_basis_lift` (#2) need to transfer "weak
regularity of θ" through the bridge `A ⧸ ⟨x⟩` ↔ `QuotSMulTop x A`.
The investigator notes a near-identical chunk at line 800 of
GradedRegularSop.lean and line 1408 of GradedFiniteFree.lean.

**Pre-flight Mathlib hunt**: this *might* already exist as
`LinearEquiv.isWeaklyRegular_congr` or
`RingEquiv.isWeaklyRegular_congr` or similar. If so, no extraction
needed — just call the Mathlib lemma directly. Use
`lean_leansearch` and `lean_loogle` aggressively before deciding.

If not in Mathlib, extract a single local helper used in both #1 and
#2 (and possibly the line-800 GradedRegularSop site). Estimated
saving: ~50 LOC.

### Helper 2: `hfactor` / `hmod` extraction in `linearIndependent_aeval_cons_step`

Inside #1 (`cons_step`), the surrounding scalar-tower bookkeeping
that sets up the strong induction on `natDegree(finSuccEquiv b)`
contains pure aeval/finSuccEquiv identities (`hfactor` and `hmod`)
that are reusable elsewhere in the file. Extract them as private
lemmas above #1.

Estimated saving: ~60–80 LOC inside #1.

### Helper 3: `Basis.ofRingEquiv` (the Mathlib hunt)

The zero branch (~120 LOC) of #3
(`finiteFree_over_mvPolynomial_of_homogeneous_regular_sop`)
hand-builds a `LinearEquiv A ≃ₗ[P] (ι →₀ P)` to transport a
`K`-basis through `MvPolynomial.isEmptyRingEquiv K`.

**Pre-flight Mathlib hunt**: try
- `Module.Free.of_equiv`
- `Module.Free.of_ringEquiv`
- `Basis.mapCoeffs`
- `Basis.smul_of_isScalarTower`

If any of these covers the case, use it directly. Estimated saving:
~60–90 LOC.

If no Mathlib API covers the case, extract `Basis.ofRingEquiv` as a
new top-level public helper in `toMathlib/` — this might be PR-worthy
upstream to Mathlib too, but for now just live in `toMathlib/`.

## Concrete refactor plan

Work in **stages**, with `lake build` clean and `lake build
BEI.AxiomCheck` clean after each stage. Commit each stage separately.

### Stage 0: orientation pass (cheap)

- Read all 5 targets end-to-end. Confirm the duplication and
  parameterisation claims.
- Run the Mathlib hunt for Helpers 1 and 3 (`lean_leansearch`,
  `lean_loogle`). Document what you find or don't find.
- If Helper 1's Mathlib API exists, the Stage 1 plan changes from
  "extract" to "replace inline call with Mathlib name". Note
  accordingly.
- If Helper 3's Mathlib API exists, you have a path to a much bigger
  win for #3.

### Stage 1: extract `localizationAtIrrelevantOfQuotientSpan_ringEquiv` (zero-risk warmup)

- Add the helper at the top of `toMathlib/GradedRegularSop.lean`.
- Replace both inline ~70-LOC blocks with one-line calls.
- Build, AxiomCheck, commit.

### Stage 2: handle the weak-regularity transfer (low-medium risk)

- If Stage 0 found a Mathlib name: replace the inline derivations in
  #1 and #2 with calls.
- Otherwise: extract `weaklyRegular_quotient_span_iff_quotSMulTop` as
  a private/public helper and call it from #1 and #2.
- Build, AxiomCheck, commit.

### Stage 3: extract `hfactor` / `hmod` for #1 (low-medium risk)

- Extract the two aeval/finSuccEquiv identities as private lemmas
  above #1.
- Replace the inline blocks.
- Build, AxiomCheck, commit.

### Stage 4: tackle #3's zero branch (medium-high risk — the swing)

- If Stage 0 found a Mathlib API for basis transport along
  `RingEquiv`: rewrite the zero branch using the Mathlib name.
- Otherwise: extract `Basis.ofRingEquiv` as a new top-level helper in
  `toMathlib/` (or under a more specific name like
  `Basis.ofMvPolynomialEmptyEquiv`).
- Build, AxiomCheck, commit.

### Stage 5: tighten

- After Stages 0–4, look for now-redundant `set`s and `have`s in the
  surrounding scaffolding.
- Final build + AxiomCheck + commit.

## Verification recipe

After every commit on this work:

```
lake build
lake build BEI.AxiomCheck
```

Then via the Lean MCP, spot-check the two most directly-affected
flagship downstreams:

```
lean_verify file=BEI/Proposition1_6.lean theorem=proposition_1_6
lean_verify file=BEI/Equidim.lean        theorem=monomialInitialIdeal_isCohenMacaulay
```

Both must report `axioms = [propext, Classical.choice, Quot.sound]`.
The `BEI/AxiomCheck.lean` regression file covers all 11 flagship
assertions automatically; if any fires, the build fails at the
offending block with a clear docstring/message diff.

## Risks

1. **Mathlib hunt comes up empty.** If neither
   `weaklyRegular_quotient_span_iff_quotSMulTop` nor a basis-transport
   API exists in Mathlib, Stages 2 and 4 fall back to extracting new
   helpers. The savings are smaller (signature overhead eats some of
   the body savings) but still positive.
2. **Universe / instance plumbing.** `toMathlib/GradedFiniteFree.lean`
   uses universes carefully. New helpers may need explicit
   `(K := K)` / `(σ := σ)` annotations at call sites. Watch
   diagnostics.
3. **Heartbeat regressions.** The Graded files already have a few
   heartbeat raises. Any new `set_option maxHeartbeats` is a smell —
   extract a sub-helper instead.
4. **Down-cascade through Proposition 1.6.** This file family is the
   "finite-free Case C route" that landed `proposition_1_6`. If a
   refactor accidentally weakens a claim, the cascade through
   `BEI/Equidim.lean` → `BEI/Proposition1_6.lean` will surface as an
   AxiomCheck failure or a build break upstream. Mitigation: stage
   commits + per-stage AxiomCheck.

## Rollback

`git revert` the offending stage commit. Each stage should be its own
commit so individual stages can be rolled back independently.

## Methodology reminders (from `feedback_fat_proof_carving.md`)

- Before touching any of the five targets, **state in your own words**
  what each one proves. Don't paraphrase the docstring — describe the
  math.
- The two recent toMathlib-adjacent work packages
  (`guides/archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md` and
  `guides/archive/THEOREM_2_1_REFACTOR.md`) are good templates for
  the stage / verify / commit cadence.
- The `BEI/AxiomCheck.lean` regression file is the canonical
  cross-check — `lake build BEI.AxiomCheck` after every stage commit
  should be a one-line ritual.
- **Do not extract sub-`have`s into named lemmas as a first resort.**
  The wins here are: one duplicated 70-LOC block (Helper 0), one
  sister-symmetric `weakly regular transfer` (Helper 1), two pure
  algebraic identities (`hfactor`/`hmod` for Helper 2), and one
  Mathlib hunt that may or may not pay off (Helper 3). If a Mathlib
  hunt comes up empty, fall back to extracting a small new helper —
  do not invent a parameterised mega-helper.
- **Negative-value rule**: per the rule applied in the `theorem_2_1`
  Stage 4 substitution, if a helper signature would clearly grow
  beyond the body savings, *do not extract*. Substitute a smaller,
  cross-cutting extraction or skip.

# `isRemainder_fij_of_mixed_walk`: collapse the 4 telescope branches and unify with the `_x`/`_y` siblings

## TL;DR

`isRemainder_fij_of_mixed_walk` (`BEI/CoveredWalks.lean:1335`) is
**837 LOC** — the largest declaration left in the repo after the
`theorem_2_1` carve, and now the **biggest single LOC win still
available**.

Investigated 2026-05-03 by a read-only subagent. Findings:

- **4 telescope blocks** (bad-x, bad-y, processable-y, processable-x)
  differ only in (a) which `Sum` side, (b) which telescope identity
  (`fij_x_telescope` vs `fij_telescope`), (c) whether one sub-walk is
  reversed, (d) which discriminator coordinate. Each block is ~110
  LOC of nearly identical scaffolding.
- **The `halg / hne_deg / isRemainder_add` end-block is textually
  identical** between `_mixed_walk` and the smaller siblings
  `isRemainder_fij_of_covered_walk` (line ~552) and
  `isRemainder_fij_of_covered_walk_y` (line ~874), modulo
  `inl ↔ inr`. ~120 LOC × **6 instances** total across the three
  callers.
- Existing infrastructure in place: `subWalk_drop` / `subWalk_take`,
  `internal_ne_head`, `internal_ne_getLast`,
  `mem_internalVertices_of_ne`, `head_of_head?`,
  `getLast_of_getLast?`, `chain'_reverse'`, `degree_bounds_of_ne`,
  `isRemainder_add`, `isRemainder_neg'`, `fij_x_telescope`,
  `fij_telescope`.

**Estimated reduction**: 837 → **~280–350 LOC** (~−500 LOC, **~60%**).
`BEI/CoveredWalks.lean` (currently 2390 LOC, the largest file in the
repo) drops to ~1900 LOC — a comparable win to the Buchberger refactor.

**Risk: medium.** The `Sum.inl` / `Sum.inr` simp-lemma sets do not
unify trivially; parameterising on a side requires a `Sum`-direction
lemma (or two thin wrappers). The reverse-sub-walk paths add one
more axis.

## Status

- Discovered: 2026-05-02 broader scan; the 6 sub-walk extractions
  inside this proof were folded into the `subWalk_drop` /
  `subWalk_take` helpers as part of the earlier `isRemainder_fij_of_*`
  carves (file 2671 → 2390 LOC across #4/#5/#10).
- Re-investigated 2026-05-03 by a read-only subagent; classified
  `[CARVE-CANDIDATE-HIGH-VALUE]`.
- Proof is **stable and axiom-clean**; downstream consumer
  `theorem_2_1` is locked in by `BEI/AxiomCheck.lean`.
- **Completed 2026-05-03** in five committed stages (Stage 1 through
  Stage 4, see the `mixed_walk_remainder Stage *` commits on master):
  - File: `BEI/CoveredWalks.lean` 2390 → 1960 LOC (**−430 LOC, ~18%**).
  - Theorem `isRemainder_fij_of_mixed_walk`: 837 → 402 LOC
    (**~52% body reduction**).
  - All four planned helpers landed:
    `exists_min_bad_vertex` / `exists_max_bad_vertex` (Stage 1),
    `x_telescope_monomial_eq` / `y_telescope_monomial_eq` plus the
    bad-vertex packagers `telescope_step_x_bad` / `telescope_step_y_bad`
    (Stage 2), `ne_head?_of_internal` / `ne_getLast?_of_internal`
    (Stage 3), and four `sub_add_single_*_eval_*` Finsupp evaluators
    plus reflowed proc-y/proc-x sub-branches (Stage 4).
  - `lake build` and `lake build BEI.AxiomCheck` both clean after
    every stage commit.
  - Archived 2026-05-03.

## Goal

1. Statement **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` must pass after every
   stage commit. `lake build BEI.AxiomCheck` is the canonical
   regression check.
3. Body shorter via 2–3 new private helpers (see "Proposed
   helpers" below).
4. `lake build` clean, no new heartbeat overrides.
5. `theorem_2_1` and the four `_x` / `_y` / `_mixed_walk` cousins
   must continue to build and remain axiom-clean.

## What the lemma proves

Same conclusion as the `_x` and `_y` variants — the polynomial
`monomial d_q · f_{a,b}` reduces to 0 mod the Gröbner basis set —
but under a **weakened, disjunctive coverage hypothesis**: every
internal vertex `v` of the walk has `d_q(inl v) ≥ 1` *or*
`d_q(inr v) ≥ 1`. The `_x`/`_y` siblings demand a deterministic
split:

- `_x`: `v < a → d_q(inr v) ≥ 1`, `b < v → d_q(inl v) ≥ 1`,
  bad (`a < v < b`) → `d_q(inl v) ≥ 1`.
- `_y`: same but bad → `d_q(inr v) ≥ 1`.
- `_mixed`: bad → either side; processable internal vertex chooses
  side based on coverage.

## Internal structure

Top split on `hBad` (does a bad internal vertex exist):

- **Bad case**: pick `v₀ = min` bad. Split on
  `hcov_v₀ : d_q(inl v₀) ≥ 1 ∨ d_q(inr v₀) ≥ 1`:
  - `inl` side → x-telescope via `fij_x_telescope` (~110 LOC).
  - `inr` side → y-telescope via `fij_telescope` (~110 LOC).
- **No-bad case**: split on existence of a processable
  internal vertex (`b < v` or `v < a` with the right side covered):
  - `b < v` → y-telescope, sub-walk `τ₂` reversed (~110 LOC).
  - `v < a` → x-telescope, sub-walk `τ₁` reversed (~110 LOC).
  - Else → `isRemainder_fij_via_groebnerElement` directly.

The 4 telescope blocks share the same skeleton:

```
pick v₀
set e_v₀, e_a, e_b singleton Finsupps
set d₁ := d_q - e_v₀ + e_a
set d₂ := d_q - e_v₀ + e_b
derive hCov₁, hCov₂ (the two sub-walks' coverage hypotheses)
apply IH twice → h₁, h₂
prove halg : monomial d_q · f_{a,b} = ... + ... via fij_*_telescope
prove hne_deg : the two terms have different degrees
finish with isRemainder_add (... h₁ h₂ degree_bounds_of_ne)
```

The 4 blocks differ only in the four parameters listed in the TL;DR.

## Proposed helpers

### Helper 1: `telescope_remainder_step` (largest win, lowest-risk)

The end-block `halg → hne_deg → isRemainder_add` is textually
identical across all 4 `_mixed_walk` telescope blocks **and** the 2
sibling proofs `_covered_walk` / `_covered_walk_y` — **6 call sites
total**, each ~80 LOC core.

Helper signature (sketch):

```
private lemma telescope_remainder_step
    (G : SimpleGraph V) (a b v₀ : V) (hav₀ : a < v₀) (hv₀b : v₀ < b)
    (side : Bool)  -- false = x-telescope, true = y-telescope
    (d_q : BinomialEdgeVars V →₀ ℕ)
    (h_cov_side : if side then d_q (Sum.inr v₀) ≥ 1 else d_q (Sum.inl v₀) ≥ 1)
    (h₁ : IsRemainder (monomial d₁ · fij a v₀) (groebnerBasisSet G) 0)
    (h₂ : IsRemainder (monomial d₂ · fij v₀ b) (groebnerBasisSet G) 0) :
    IsRemainder (monomial d_q · fij a b) (groebnerBasisSet G) 0
```

The `Bool` parameterisation may end up cleaner as an inductive `Side`
type. Decide based on which produces the cleanest call sites.

Estimated saving: **~250 LOC** across `_mixed_walk` and the two
siblings.

### Helper 2: `coverage_transfer_through_subwalk` (medium-risk)

The disjunctive `hCov₁` / `hCov₂` derivations appear in 8
near-duplicate blocks of ~30 LOC, parameterised on side and on
whether the sub-walk is reversed.

Helper takes the sub-walk membership (`u ∈ internalVertices τ₁` or
`τ₂`), the coverage of the *full* walk, and produces the
disjunctive coverage of the sub-walk.

Estimated saving: ~150 LOC.

### Helper 3: `min_bad_vertex` / `max_bad_vertex` (small but cross-cutting)

Both `_x` and `_y` and `_mixed_walk` use `Finset.min'` / `Finset.max'`
on the filtered set of bad vertices, with the same setup and the same
`hBadSet` non-emptiness witness. Currently inlined identically in
3 files.

Helper:

```
private lemma min_bad_vertex {τ : List V} (a b : V)
    (hBad : ∃ v ∈ internalVertices τ, a < v ∧ v < b) :
    ∃ v₀ ∈ internalVertices τ, a < v₀ ∧ v₀ < b ∧
      ∀ w ∈ internalVertices τ, a < w → w < b → v₀ ≤ w
```

Estimated saving: ~30 LOC across 3 call sites.

## Concrete refactor plan

Work in **stages**, with `lake build` clean and `lake build
BEI.AxiomCheck` clean after each stage. Commit each stage separately.

### Stage 0: orientation pass

- Read all 4 telescope blocks of `_mixed_walk` end-to-end.
- Read the corresponding telescope blocks in `_covered_walk`
  (line ~575–760) and `_covered_walk_y` (line ~897–1080).
- Confirm the textual symmetry claim by diffing pairs.
- If a block diverges materially, **stop and re-plan**: the helper
  signatures derived from the "uniform" blocks won't fit a divergent
  one.

### Stage 1: extract `min_bad_vertex` / `max_bad_vertex` (small warmup)

- Add the helpers near the top of `BEI/CoveredWalks.lean`.
- Replace the 3 inline call sites in `_mixed_walk`, `_covered_walk`,
  `_covered_walk_y`.
- Build, AxiomCheck, commit.
- Validates the cross-file refactor mechanism on a small target.

### Stage 2: extract `telescope_remainder_step` (the biggest win)

- Add the helper above `_covered_walk` (so all three callers can use
  it).
- Replace all 6 inline end-blocks with helper calls.
- This is the structural-symmetry sanity check: if the four
  `_mixed_walk` blocks really do collapse into one helper call each,
  the parameterisation is correct.
- Build, AxiomCheck, commit.

### Stage 3: extract `coverage_transfer_through_subwalk` (medium risk)

- Add the helper.
- Replace the 8 inline `hCov₁` / `hCov₂` derivations.
- Build, AxiomCheck, commit.

### Stage 4: tighten

- After Stages 1–3, look for now-redundant `set`s and `have`s in the
  surrounding scaffolding.
- Final build + AxiomCheck + commit.

## Verification recipe

After every commit on this work:

```
lake build
lake build BEI.AxiomCheck
```

Then via the Lean MCP, spot-check the most directly affected flagship
downstream:

```
lean_verify file=BEI/GroebnerBasisSPolynomial.lean theorem=theorem_2_1
```

Must report `axioms = [propext, Classical.choice, Quot.sound]`,
no warnings.

The `BEI/AxiomCheck.lean` regression file covers all 11 flagship
assertions automatically; if any fires, the build fails at the
offending block with a clear docstring/message diff.

## Risks

1. **`Sum.inl` / `Sum.inr` simp-lemma sets don't unify trivially.**
   Parameterising on a side (`Bool` or inductive `Side`) requires a
   `Sum`-direction lemma or two thin wrappers
   (`d_q.coverage_at_inl`, `d_q.coverage_at_inr`). Mitigation: write
   the wrapper helpers first, prove they collapse via simp, then
   parameterise the main helper.
2. **Reverse-sub-walk paths.** The processable-y and processable-x
   blocks reverse one of the two sub-walks (`τ₂.reverse` or
   `τ₁.reverse`). The helper signature must allow this; consider
   making the "which sub-walk is reversed" a parameter (or make
   it implicit by always passing the data in the unreversed form
   and letting the helper handle reversal internally).
3. **`fij_x_telescope` vs `fij_telescope`.** These are two distinct
   identities, not one parameterised lemma. The helper picks the
   right one based on the `side` parameter.
4. **Heartbeat regressions.** This is already a long proof. Any new
   `set_option maxHeartbeats` raise is a smell — extract a
   sub-helper instead.

## Rollback

`git revert` the offending stage commit. Each stage should be its own
commit so individual stages can be rolled back independently.

## Methodology reminders (from `feedback_fat_proof_carving.md`)

- Before touching the proof, **state in your own words** what
  `isRemainder_fij_of_mixed_walk` proves (the disjunctive-coverage
  variant: every internal vertex has `inl` *or* `inr` coverage, vs
  the deterministic `_x` and `_y` variants).
- The successful `theorem_2_1` work package
  (`guides/archive/THEOREM_2_1_REFACTOR.md`) and Buchberger work
  package (`guides/archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md`) are
  good templates for the stage / verify / commit cadence.
- The `BEI/AxiomCheck.lean` regression file is the canonical
  cross-check — `lake build BEI.AxiomCheck` after every stage commit
  should be a one-line ritual.
- **Negative-value rule** (per `theorem_2_1` Stage 4 substitution):
  if a helper signature would clearly grow beyond the body savings,
  *do not extract*. The Stage 2 `telescope_remainder_step` is the
  critical helper; the others are nice-to-have. If Stage 2 lands
  cleanly with a tractable signature, the refactor is a success
  even without Stages 3–4.
- **Do not extract sub-`have`s into named lemmas as a first resort.**
  The wins here are: one cross-cutting end-block parameterised on
  `side` (Helper 1), one coverage transfer (Helper 2), and one tiny
  `min'/max'` packaging (Helper 3). Other inline `have`s deserve
  names only if they cleanly factor across multiple call sites.

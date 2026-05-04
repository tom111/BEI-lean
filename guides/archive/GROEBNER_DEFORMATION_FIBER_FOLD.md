# `GroebnerDeformation` t=1 / t=0 fibre identification: sister-fold

## Status

**Done 2026-05-04.** Sister-fold landed in two commits:

- `acad325` — Stage 1 + 2: extracted `defRing_specialize_quotient`
  helper, rewired both `baseQuotEquiv` (t=1) and `specZeroQuotEquiv`
  (t=0) as one-line specialisations. The shared helper takes
  `(G, c, J, specC)` plus four hypotheses (specC's action on inl/inr
  variables, image of `Ĩ` under specC, and the comap inclusion
  `J ⊆ baseInclude⁻¹(Ĩ ⊔ span{t-Cc})`). The asymmetric
  `binomialEdgeIdeal_le_baseInclude_comap_sup` (geom_sum identity) and
  `monomialInitialIdeal_le_baseInclude_comap_zeroSum` (simpler `t^d`
  divisibility) supply the per-fibre `hJ_comap` witnesses.
  LOC: 2234 → 2131 (−103).
- `b331b4e` — Stage 3: collapsed `(C 1 : DefRing) = 1` /
  `(C 0 : DefRing) = 0` boilerplate into `map_one`/`map_zero`
  one-liners and folded `hcomap`/`h_inr` haves into `refine` goal
  slots. LOC: 2131 → 2116 (−15).

**Total**: 2234 → 2116 (−118 LOC). All 11 `BEI.AxiomCheck`
`#guard_msgs` blocks pass; full `lake build` clean.

The asymmetric "init-extraction" hazard from §Risks turned out to be
parameterisable cleanly: only the `hJ_comap` input differs between the
two fibres (each is one private lemma), the rest of the construction
shares the new helper.

## TL;DR

`BEI/GroebnerDeformation.lean` Sections 5 and 6 are sister branches
identifying the deformation's two distinguished fibres:

| Lines | Section | LOC |
|---|---|---|
| 217–422 | `t = 1` quotient ≅ `S / J_G` | **205** |
| 423–619 | `t = 0` quotient ≅ `S / init(J_G)` | **196** |

Mathematically, both are specialisations of `S[t] / Ĩ` at a particular
value of `t ∈ K[t]` (`t = 1` and `t = 0` respectively). They reuse
the same machinery: the `K[t]`-algebra structure, the deformation
ideal `Ĩ`, the specialisation maps. They differ in (a) which value
of `t` is plugged in, (b) what the resulting quotient is identified
with, (c) some bridging that's required for `t = 0` because
`init(J_G)` involves stripping the `t · x_j y_i` term.

**Estimated reduction: ~100 LOC.** **Risk: medium** — the
asymmetric bridge for `t = 0` (initial-ideal extraction) is the
main parameterisation hazard.

## Math content

The Gröbner deformation: build `S[t] / Ĩ` over `K[t]`, where the
deformed generators are `f̃_{i,j} = x_i y_j − t · x_j y_i`. By
flatness of `K[t] → S[t] / Ĩ`, the closed fibres at all values of
`t ∈ K[t]` are isomorphic up to nilpotents. Two fibres matter:
`t = 1` recovers the actual binomial edge ideal `J_G`; `t = 0`
recovers the monomial initial ideal `init(J_G)`. CM transfers from
`t = 0` (handled by Route A) to `t = 1` via flatness.

## Goal

1. Statements of `tildeJ_oneQuotEquiv` (or whatever it's called) and
   `tildeJ_zeroQuotEquiv` **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
   `proposition_1_6` (the chief consumer) remains
   `[propext, Classical.choice, Quot.sound]`.
3. The two section bodies materially shorter via a parameterised
   "specialise at any K-element" helper.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read both sections end-to-end. Confirm the textual symmetry claim
  by diffing 5 vs 6.
- Identify *exactly* what's shared and what's specific to each
  fibre. The `t = 0` section's `init(J_G)` bridge is the main
  asymmetry; document its scope.
- Decide if a `defRing_specialize_quotient (c : K) : ...` helper is
  the right form, or if it should be split into a "specialise to
  any value" helper + per-fibre downstream identification.

### Stage 1: extract `defRing_specialize_quotient`

A single helper covering the shared specialisation machinery.
Returns `S[t] / Ĩ` quotiented by `t = c` for a specified `c : K`.

### Stage 2: rewire `t = 1` and `t = 0` sections

Each becomes: invoke the helper with the right `c`, then compose with
the per-fibre identification (trivial for `t = 1`, the
`init(J_G)`-extraction bridge for `t = 0`).

### Stage 3: tighten

Look for now-redundant `set`s and `have`s in the surrounding
scaffolding.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `proposition_1_6` via `lean_verify`.

## Risks

1. **Asymmetric `init(J_G)` bridge for t=0.** The two fibres are
   not perfectly parallel because `t = 0` requires extracting
   `init(J_G)`, which involves identifying which monomial wins in
   each generator. The helper signature must allow this asymmetry
   without forcing the caller to re-derive shared scaffolding.
2. **`MvPolynomial`-over-`K[t]` universe plumbing.** Specialisation
   at `c ∈ K` involves the `K[t] → K` quotient by `(t − c)`. Universe
   bookkeeping may need explicit annotations.
3. **Heartbeat regressions** — extract sub-helpers if needed.

## Methodology reminders

See `feedback_fat_proof_carving.md`. The mixed_walk and
groebner_implies_closed carves both succeeded with sister-fold
of two textually parallel branches; this refactor follows the same
pattern.

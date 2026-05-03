# Cross-file `Side` abstraction with `Sum.swap` lemmas

## Status

**Pre-investigation proposal — large architectural play.** Identified
during the 2026-05-03 bird's-eye review. Has not yet been confirmed by
a read-only investigator. **Highest blast radius of any proposal in
the active queue.**

This is the speculative one. Read the entire guide before deciding
whether to dispatch.

## TL;DR

The bipartite x/y duality (`Sum.inl` for x-variables, `Sum.inr` for
y-variables) pervades the BEI proofs. Almost every theorem has an
x-side and a y-side, often as textual twins. The carving pass has
exploited this *locally*:

- `subWalk_drop` / `subWalk_take` (CoveredWalks, 10× reuse)
- `caseD_*` helpers (IteratedRegularity)
- `case4_remainder` / `case5_remainder` (`theorem_2_1`)
- `cubic_degree`, `extract_cond1` / `extract_cond2`
  (`groebner_implies_closed`)

What we *haven't* done is introduce a **cross-file `Side`
abstraction** that lets us prove half the bipartite lemmas once and
derive the other half via swap.

**Estimated reduction: ~400–600 LOC across the repo** *if* the
abstraction lands cleanly. **Risk: VERY HIGH** — the entire
bipartite proof would need re-plumbing; many call sites would
require changes; universe / instance hazards are real. This is a
multi-week refactor with broad blast radius and uncertain pay-off.

**Do NOT dispatch this without first scoping a minimum-viable
prototype on a small file** to validate the abstraction's
ergonomics.

## Math content

The BEI ring `K[x_1, …, x_n, y_1, …, y_n]` is naturally indexed by
`Fin n ⊕ Fin n` (the `BinomialEdgeVars` type). The two halves are
exchanged by `Sum.swap`. Most BEI proofs respect this symmetry:
swapping the two halves yields a "y-version" of any "x-version"
lemma, and the proofs are textually parallel modulo `inl ↔ inr`.

A `Side` abstraction would make this symmetry first-class:

```
inductive BinomialSide
  | x  -- aka inl
  | y  -- aka inr

def BinomialSide.var (s : BinomialSide) : Fin n → BinomialEdgeVars (Fin n) := …
def BinomialSide.swap : BinomialSide → BinomialSide := …
```

Helpers like `cov_inr_or_inl_of_admissible_path` could be
parameterised on `Side` and proved once, with the y-version derived
from the x-version via `Sum.swap` symmetry.

## Goal

1. All paper-facing flagship theorems **byte-identical** in
   statement and axiom set.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes.
3. The `Side` abstraction in place in `BEI/Definitions.lean` (or a
   new file like `BEI/BipartiteSide.lean`).
4. At least one major file (e.g., `BEI/CoveredWalks.lean` or
   `BEI/Equidim/IteratedRegularity.lean`) materially shorter via
   `Side`-parameterised helpers.
5. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: minimum viable prototype

**This stage is critical** and may take multiple days. Do *not*
proceed past Stage 0 without a working prototype.

- Add `BinomialSide` (or whatever name) plus `swap`, `var`, basic
  lemmas (`swap_swap`, `var_swap`, etc.) to `BEI/Definitions.lean`
  (or a new file).
- Pick **one small, well-understood pair of sister lemmas** in the
  repo. Candidates:
  - `caseD_typeA_exponent_zero` (already extracted) — does it
    cleanly become `Side`-parameterised?
  - `cubic_degree` (already extracted) — likewise.
- Re-prove the pair via the `Side` abstraction. Confirm that the
  resulting code is materially shorter, builds cleanly, and is
  axiom-clean.
- If the prototype is awkward, **abort the entire refactor** and
  document the failure mode.

### Stage 1: rewire one file

Pick one big file (suggest `BEI/CoveredWalks.lean` — already heavily
carved, well-understood). Apply the `Side` abstraction throughout.
Estimate the saving honestly.

### Stage 2: evaluate

Look at the Stage 1 result. Did it save ≥100 LOC in that file?
Did the API surface get cleaner or messier? Did downstream
consumers break?

If positive: continue to Stage 3.
If neutral or negative: stop, document, leave the prototype as a
toMathlib offering.

### Stage 3: extend to other files

Roll the abstraction out to `IteratedRegularity`, `GroebnerDeformation`,
`PrimeIdeals`, etc. Each in its own staged commit.

### Stage 4: tighten

Final pass.

## Verification recipe

```
lake build
lake build BEI.AxiomCheck
```

After every commit. Cross-check ALL 11 flagship theorems via
`lean_verify` (this refactor's blast radius is the whole repo).

## Risks

1. **Universe / instance plumbing.** The `Side` type interacting
   with `MvPolynomial.aeval`, `Sum.swap` infrastructure, and
   typeclass resolution is the highest-risk surface. Stage 0
   must include realistic typeclass interactions.
2. **API churn for consumers.** Even if BEI flagship statements
   don't change, the *helper* statements may. If downstream
   guides / consumers reference helpers by name, those references
   break.
3. **Diminishing returns.** Many BEI proofs are no longer x/y
   duplicates after the carving pass. The estimated 400–600 LOC
   saving is generous; a more honest estimate post-pass might be
   200–400 LOC.
4. **Heartbeat regressions** — pervasive change; many files may
   need careful tuning.
5. **Reviewer / collaborator overhead** — a cross-file refactor of
   this scope is hard to review piecemeal; expect non-trivial
   communication cost.

## When to NOT dispatch this

- If the previous narrower carves (especially the per-file ones in
  this batch) saturate the available LOC reduction with much lower
  risk.
- If the project is preparing for paper submission / external
  review and stability matters more than aesthetic.
- If the active maintainer doesn't have multi-week capacity to
  see it through.

## When to dispatch this

- After all the smaller per-file proposals in this batch are
  resolved (carved or formally skipped).
- When the active maintainer wants to pursue a longer-horizon
  architectural improvement.
- Specifically when the existing BEI codebase is *stable* (no other
  active refactors in flight that might conflict).

## Methodology reminders

See `feedback_fat_proof_carving.md`. **The negative-value rule
applies aggressively here**: this is the largest blast-radius
refactor in the queue. If Stage 0's prototype isn't *clearly*
better than the existing per-helper extraction approach, abort.

The right Stage 0 outcome to proceed past is: "the prototype on
a single sister-pair shows ≥30% reduction with no awkward
parameterisation, and the resulting helper is more readable than
two separate sisters." Anything less and the abstraction's
machinery cost will eat the savings.

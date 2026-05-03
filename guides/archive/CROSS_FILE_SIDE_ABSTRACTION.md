# Cross-file `Side` abstraction with `Sum.swap` lemmas

## Status

**Stage 0 prototype completed 2026-05-03 — INVESTIGATED, ABORTED.**
Result: the abstraction's machinery cost exceeds its savings on the
prototype sister-pair. No further stages attempted; no code changes
landed.

See "Stage 0 outcome (2026-05-03)" below for the failure mode.

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

## Stage 0 outcome (2026-05-03) — ABORTED

### What was prototyped

1. **Infrastructure (≈50 LOC) added to `BEI/Definitions.lean`**:
   ```
   inductive BinomialSide := | x | y  deriving DecidableEq
   namespace BinomialSide
     def swap : BinomialSide → BinomialSide
     theorem swap_swap (s) : s.swap.swap = s
     def var {V} : BinomialSide → V → BinomialEdgeVars V    -- @[reducible]
     theorem var_x / var_y                                   -- @[simp]
     theorem var_injective
     def endpoint {V} : BinomialSide → V → V → V
     theorem endpoint_x / endpoint_y                         -- @[simp]
   end BinomialSide
   ```

2. **Sister pair chosen**: `fij_degree_inl_eq_zero` and
   `fij_degree_inr_eq_zero` (both at `BEI/GroebnerBasisSPolynomial.lean`
   ≈line 159–173). Each is 4 lines of body, 2 lines of signature, plus
   `omit` and a docstring; together about 19 source lines. They have
   ≈48 call sites in the same file.

3. **Unified lemma**:
   ```lean
   private lemma fij_degree_var_eq_zero {a b : V} (hab : a < b)
       (s : BinomialSide) (v : V) (hne : v ≠ s.endpoint a b) :
       binomialEdgeMonomialOrder.degree (fij (K := K) a b) (s.var v) = 0 := by
     rw [fij_degree _ _ hab, Finsupp.add_apply,
         Finsupp.single_apply, Finsupp.single_apply]
     cases s
     · simp [show (Sum.inl a : BinomialEdgeVars V) ≠ Sum.inl v from
         fun h => hne.symm (Sum.inl_injective h)]
     · simp [show (Sum.inr b : BinomialEdgeVars V) ≠ Sum.inr v from
         fun h => hne.symm (Sum.inr_injective h)]
   ```
   ≈11 lines. On its own, **about 42% shorter** than the sum of the two
   sister lemma bodies — meeting the 30 % bar in isolation.

### Why it was aborted

Call sites of the original sister lemmas occur inside chains like

```
exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
  (fij_degree_inr_eq_zero (K := K) hij v (ne_of_lt …))
  (fij_degree_inr_eq_zero (K := K) hil v (ne_of_lt …))).1 (hE_ge_D _))
```

Migrating these to the unified `fij_degree_var_eq_zero (s := .y)` makes
the position become `(BinomialSide.y).var v` instead of `Sum.inr v`.
**`omega` does not unfold `BinomialSide.var` even when it is marked
`@[reducible]`**, regardless of whether the body uses `match` or `s.rec`.

Verified directly (via `mcp lean_run_code`):
```lean
@[reducible] def BS.var {V} (s : BS) (v : V) : V ⊕ V :=
  s.rec (Sum.inl v) (Sum.inr v)
example (v : ℕ) (f : ℕ ⊕ ℕ → ℕ) (h : f (Sum.inr v) = 1) :
    1 ≤ f ((BS.y).var v) := by omega
-- ❌ omega: "No usable constraints found."
```
The same goal closes with `simp only [BS.var]; omega`. So every chained
`omega` call in the original code (8 such sites in the prototype file
and >30 across the codebase) would need either a `simp only
[BinomialSide.var]` or a `show … (Sum.inl/inr v) …` pre-step
inserted before omega — each insertion costing ≥1 line.

### LOC accounting

| | Lines |
|---|---|
| Infrastructure added to `Definitions.lean` | +50 |
| Unified lemma replacing the two sisters    | −19 → +11 = −8 |
| `simp only [BinomialSide.var]` before each `omega` (8 sites local; ≥30 across repo) | +8 (file) / +30 (repo) |
| Net change for the prototype file alone | **+0** |
| Net change including infrastructure       | **+50** |

The 30 % win on the unified lemma vanishes once the omega-unfolding tax
is paid at every call site, and the 50 LOC of new infrastructure is
pure overhead. With wrappers preserved (which avoids touching call
sites), the total is +6 inside the file plus +50 in `Definitions.lean`
= +56 LOC.

### Could the omega tax be amortised across many sister pairs?

In principle: each subsequent sister-pair fold gives ~5 lines back in
its body, while the omega tax is paid once per `omega`-using call site
(not per pair). If there are ≥10 sister pairs that fold cleanly *and*
their call sites do not chain through `omega`, the infrastructure could
break even. But:
- The other natural candidates (`pathMonomial_exponent_*_zero`/`_one`,
  `subWalk_drop`/`_take`, `caseD_*`) have **dual** parameters (e.g.
  `j < v` vs `v < i`, `prefix` vs `suffix`) that `BinomialSide` alone
  does not capture. Each would need its own additional parameterisation
  on top of `Side`.
- Many sister pairs are already short enough (3–6 line bodies) that
  even a 50 % reduction is a 1–3 line save per pair, easily eroded by
  call-site overhead.
- `omega`-blindness through reducible definitions is a **structural**
  obstacle, not a per-pair quirk; every call site that ends in `omega`
  pays the same tax.

### Decision

Abort the refactor. Bank the empirical lesson:
**`omega`-style tactics do not unfold custom indexing definitions**, so
any abstraction whose value depends on transparent unfolding inside
chained-arithmetic call sites pays a per-site tax that swamps the
local savings.

The infrastructure (`BinomialSide`) was **not** committed to the
repository; the prototype was reverted via `git checkout`. The codebase
remains exactly as before the investigation, and this guide is moved to
`guides/archive/` as an investigated-and-aborted record.

If a future investigator wants to revisit this, the new entry point
should be: pick a sister pair whose call sites do **not** chain through
`omega`/`linarith`/`positivity`. Until such a pair is identified, the
abstraction does not pay for itself.

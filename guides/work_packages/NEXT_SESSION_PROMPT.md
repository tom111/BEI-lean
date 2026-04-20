# Next-Session Prompt: Prop 1.6 R1 — close one of the two remaining sub-sorries

## Where we are

Paper-faithful `proposition_1_6` is assembled in `BEI/Proposition1_6.lean`,
modulo exactly **two** sub-sorries in `BEI/GroebnerDeformation.lean`:

1. `tildeJ_quotient_isCohenMacaulay` — global Cohen–Macaulayness of
   `S[t] ⧸ Ĩ` (the deformation ring quotient).
2. `tildeJ_tMinusOne_isSMulRegular` — `(t − 1)` is a non-zero-divisor on
   `S[t] ⧸ Ĩ` (equivalent to `K[t]`-flatness, the Eisenbud 15.17 technical heart).

Build is green. `proposition_1_6` axiom check is
`{propext, sorryAx, Classical.choice, Quot.sound}`.

## Required reading before starting

1. `BEI/GroebnerDeformation.lean` — the R1 framework. Contains the
   deformation ring, deformed generators
   `f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i`, fiber identifications,
   `baseQuotEquiv`, the four-arrow assembly, and the two named sub-sorries
   with status comments.
2. `guides/work_packages/GROEBNER_CM_TRANSFER.md` — the full route plan,
   including the audit findings and the R1.a–R1.g breakdown.
3. `toMathlib/GradedCM.lean:280–356` — the documented Case-C obstacle and the
   four candidate strategies (this matters for sub-sorry 1).
4. `BEI/Equidim.lean` — has the bipartite HH CM theorem
   `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` and Step 1
   (`monomialInitialIdeal_isCohenMacaulay`); look here for examples of
   regular-quotient-lift patterns that could be adapted.

## Pick one of the two sub-sorries

### Option A — `tildeJ_tMinusOne_isSMulRegular` (the flatness/Gröbner heart)

This is R1.d. The classical proof:

- `K[t]` is a PID, so flatness of `S[t] ⧸ Ĩ` over `K[t]` is equivalent to
  `t`-torsion-freeness, equivalently `(t − 1)`-torsion-freeness for any other
  prime element.
- `{f̃_{i,j} : edges, i < j}` is a Gröbner basis of `Ĩ` whose leading terms
  `x_i y_j` contain no `t`. The standard normal form in `S[t] ⧸ Ĩ` is then
  `K[t]`-free on the standard monomials of `J_G`.

Concrete plan:

1. State `tildeJ_t_isSMulRegular` (sibling lemma — `t` is NZD on `S[t] ⧸ Ĩ`)
   alongside the existing `tildeJ_tMinusOne_isSMulRegular`. They will share
   most of the proof infrastructure (both reduce to flatness over `K[t]`).
2. Lift the BEI Gröbner basis from `S` to `S[t]`. The leading terms of `f̃_{i,j}`
   in the appropriate weighted order are `x_i y_j` — same as the
   `binomialEdgeMonomialOrder` leading terms of `f_{i,j}`. Existing
   infrastructure: `BEI/MonomialOrder.lean`, `BEI/Groebner.lean`,
   `BEI/GroebnerAPI.lean`, `BEI/GroebnerBasis.lean`.
3. Use the standard monomial basis to argue `K[t]`-freeness of `S[t] ⧸ Ĩ`,
   hence flatness, hence `t` and `(t − 1)` are NZD.

This does not depend on closing the GradedCM Case-C sorry. Independent of
Option B.

### Option B — `tildeJ_quotient_isCohenMacaulay` (graded LTG step)

This requires the graded local-to-global CM theorem from
`toMathlib/GradedCM.lean`, which has a dormant Case-C sorry. Three sub-options:

- **B.1** Close `caseC_CM_transfer` in `toMathlib/GradedCM.lean` directly.
  This is ~400–800 LOC of new graded-depth / `*-CM` infrastructure (per the
  strategy comments at lines 286–334 of that file).
- **B.2** Pivot to the graded Noether-normalisation route (Strategy 3 in the
  GradedCM comments). Also several hundred LOC of new infrastructure.
- **B.3** A BEI-specific bypass — none was found in the 2026-04-20 audit
  (Stanley–Reisner doesn't apply because `S[t] ⧸ Ĩ` is not squarefree, and
  the "homogeneous-core localization" trick fails for the documented reason).

Recommend Option A if you only have one session — it's self-contained and
doesn't require touching the GradedCM blocker.

## Workflow rules — IMPORTANT

**Use the lean-lsp MCP tools, not `lake build`.** The previous session burned
many full-build cycles on issues that one-shot MCP queries would have caught.

- `lean_diagnostic_messages BEI/GroebnerDeformation.lean` — read just this
  file's errors after an edit. Do NOT run `lake build` until the file is
  diagnostic-clean.
- `lean_goal BEI/GroebnerDeformation.lean <line> [column]` — inspect the proof
  state before committing to a tactic. Use this BEFORE writing `rfl` or `simp`.
- `lean_multi_attempt BEI/GroebnerDeformation.lean <line> ["tac1", "tac2", ...]`
  — test several tactic candidates without editing. Cheap and fast.
- `lean_local_search <name>` and `lean_hover_info <file> <line> <col>` —
  confirm a lemma's name and signature before writing it. Catches typos like
  `geom_series_def` (not a real name, the right one is `geom_sum_mul`).
- `lean_leansearch` / `lean_loogle` — find Mathlib lemmas by description or
  type pattern. Faster than grep.
- Reserve `lake build` for the final sanity check before committing, after
  diagnostics are clean.

The rationale memory: `feedback_lean_mcp_over_lake.md`.

## Other workflow rules

- If a `set_option maxHeartbeats X` block is needed, add it with a comment
  explaining why (the linter complains otherwise).
- The deformation ring `DefRing n K = MvPolynomial (BinomialEdgeVars (Fin n) ⊕ Unit) K`
  has a deeply nested type. Explicit `(K := K)` annotations on `tildeJ`,
  `tDef`, `specOne` etc. help elaboration.
- `BinomialEdgeVars V` is a `def`, not `abbrev` (intentionally opaque).
  Simp lemmas about it can fail to fire if the term has the unfolded form.
  Prefer rewriting over `simp` for these targets.
- The `K : Type` (universe 0) restriction is inherited from the F2-route
  HH theorem; do not generalize unless you also generalize
  `toMathlib/PolynomialAwayTensor.lean`.

## Commit discipline

When the chosen sub-sorry is closed:

1. Update `TODO.md` (active sorry count, status block).
2. Update `FORMALIZATION_MAP.md` (Prop 1.6 row).
3. Update `guides/work_packages/GROEBNER_CM_TRANSFER.md` (R1 sub-sorry status).
4. Update `MEMORY.md` (Sorry Summary section).
5. Run `lake build` once for final sanity, then commit with a focused message
   that names the closed sorry. Do NOT push (per `feedback_no_auto_commit.md` /
   `feedback_push_all_remotes.md` semantics — wait for explicit user request).

## Definition of done for this session

Best outcome: one of the two sub-sorries closed, build green, status docs
updated, committed.

Minimum acceptable outcome: substantial concrete progress on one sub-sorry,
with the remaining gap isolated as one or more clearly-named smaller lemmas
with documented status. Not a regression of the framework (must still build
modulo the same sub-sorries).

Do not chase the universe generalization, the corollary restatements
(`corollary_3_4` real-CM branch, `corollary_3_7` real-CM branch), or the
`toMathlib/HeightAdditivity.lean` dormant sorries this session — they are
orthogonal and can wait.

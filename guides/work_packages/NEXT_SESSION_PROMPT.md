# Next-Session Prompt: Prop 1.6 R1 — two remaining sub-sorries

## Where we are

Paper-faithful `proposition_1_6` is assembled in `BEI/Proposition1_6.lean`,
modulo exactly **two** sub-sorries in `BEI/GroebnerDeformation.lean`:

1. `tildeJ_quotient_isCohenMacaulay` — global Cohen–Macaulayness of
   `S[t] ⧸ Ĩ` (the deformation ring quotient). Graded local-to-global CM;
   depends on the dormant Case-C sorry in `toMathlib/GradedCM.lean`.
2. `tildeJ_flat_over_polyT` — flatness of `S[t] ⧸ Ĩ` over `K[t] = PolyT K`.
   The classical Eisenbud 15.17 standard-monomial argument over `K[t]`.

**Update (after R1.d refactor):** the `IsSMulRegular` step is **closed
conditional on flatness**. Specifically, `tildeJ_tMinusOne_isSMulRegular`
and its sibling `tildeJ_t_isSMulRegular` are both fully proved once
`tildeJ_flat_over_polyT` is available, via
`Module.Flat.isSMulRegular_of_isRegular` + `isSMulRegular_map`. The
`K[t]`-algebra structure on `DefRing n K` is registered globally via
`polyTInclude = rename Sum.inr`, with scalar tower
`K → PolyT K → DefRing n K`.

Build is green. `proposition_1_6` axiom check is
`{propext, sorryAx, Classical.choice, Quot.sound}`.

## Required reading before starting

1. `BEI/GroebnerDeformation.lean` — the R1 framework. Contains the
   deformation ring, deformed generators, fiber identifications,
   `baseQuotEquiv`, the `K[t]`-algebra registration, the
   `tildeJ_flat_over_polyT` sub-sorry, and the now-proved
   `tildeJ_tMinusOne_isSMulRegular` / `tildeJ_t_isSMulRegular` lemmas.
2. `guides/work_packages/GROEBNER_CM_TRANSFER.md` — the full route plan
   and audit.
3. `toMathlib/GradedCM.lean:280–356` — the documented Case-C obstacle
   (relevant for sub-sorry 1).
4. `BEI/Equidim.lean` — bipartite HH CM theorem + Step 1
   (`monomialInitialIdeal_isCohenMacaulay`); examples of regular-quotient
   lift patterns.

## Pick one of the two sub-sorries

### Option A — `tildeJ_flat_over_polyT` (the isolated technical heart)

This is the reformulated R1.d. The classical proof: the standard monomials
of `J_G` (monomials not divisible by any leading term `x_i y_j` with
`{i, j}` an edge, `i < j`) form a free `K[t]`-basis of `S[t] ⧸ Ĩ`. Free ⟹
flat, done.

Concrete plan:

1. Identify the standard monomials of `J_G` in Lean. Existing infrastructure:
   `BEI/GroebnerBasis.lean`, `BEI/GroebnerAPI.lean`,
   `BEI/GroebnerBasisSPolynomial.lean`, `BEI/MonomialOrder.lean`.
2. Show: every element of `DefRing n K` reduces uniquely modulo `Ĩ` to a
   `K[t]`-linear combination of standard monomials of `J_G` (the
   "division algorithm" over `K[t][x, y]`).
3. Build a `LinearEquiv (PolyT K)` between `DefRing n K ⧸ tildeJ G` and
   `(PolyT K) ⊗[K] (standard monomials as K-vector space)`, or more
   directly construct a `Basis` via `Module.Free.of_basis`.
4. `Module.Free (PolyT K) (DefRing n K ⧸ tildeJ G)` ⟹ `Module.Flat`.

**Alternative (avoiding a full basis):** use
`Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` — since `PolyT K` is a
PID (Bezout + domain), flatness is equivalent to torsion-free. Torsion-free
means: if `q ∈ PolyT K` is nonzero and `c ∈ DefRing n K` with
`polyTInclude n q · c ∈ tildeJ G`, then `c ∈ tildeJ G`. This still needs
the Gröbner-basis argument but lets you focus on a single test.

Substantial effort: ~300–700 LOC of Gröbner-basis-over-`K[t]` infrastructure
(per the guide's original estimate; possibly less if you reuse
`BEI/GroebnerAPI.lean`'s division-algorithm scaffolding).

### Option B — `tildeJ_quotient_isCohenMacaulay` (graded LTG step)

This requires the graded local-to-global CM theorem from
`toMathlib/GradedCM.lean`, which has a dormant Case-C sorry. Three
sub-options (unchanged from the prior session):

- **B.1** Close `caseC_CM_transfer` in `toMathlib/GradedCM.lean` directly.
  ~400–800 LOC of new graded-depth / `*-CM` infrastructure.
- **B.2** Pivot to the graded Noether-normalisation route.
- **B.3** A BEI-specific bypass — none was found in the 2026-04-20 audit.

Recommend Option A if starting fresh — the infrastructure it needs is
adjacent to existing BEI Gröbner code, whereas Option B requires new
graded commutative algebra machinery.

## Workflow rules — IMPORTANT

**Use the lean-lsp MCP tools, not `lake build`.**

- `lean_diagnostic_messages BEI/GroebnerDeformation.lean` — file errors
  after an edit. Do NOT run `lake build` until the file is diagnostic-clean.
- `lean_goal BEI/GroebnerDeformation.lean <line> [column]` — inspect the
  proof state before committing to a tactic.
- `lean_multi_attempt BEI/GroebnerDeformation.lean <line> ["tac1", …]`
  — test tactic candidates without editing.
- `lean_local_search <name>` / `lean_hover_info <file> <line> <col>` —
  verify a lemma's name and signature.
- `lean_leansearch` / `lean_loogle` — find Mathlib lemmas.
- Reserve `lake build` for the final sanity check before committing.

Rationale memory: `feedback_lean_mcp_over_lake.md`.

## Other workflow notes

- The `PolyT K := MvPolynomial Unit K` abbreviation is set up in
  `BEI/GroebnerDeformation.lean`, with `Algebra (PolyT K) (DefRing n K)`
  registered globally. Helpful lemmas: `algebraMap_polyT_tMinusOne`,
  `algebraMap_polyT_t`.
- `BinomialEdgeVars V` is a `def` (opaque). Prefer `show`/`change` to
  unfold it rather than hoping `simp` fires.
- The `K : Type` (universe 0) restriction is inherited from the F2 route.
- For a `set_option maxHeartbeats X` bump, scope it to a single
  declaration and annotate with a short `--` comment (linter requires this).

## Commit discipline

When the chosen sub-sorry is closed:

1. Update `TODO.md` (active sorry count, status block).
2. Update `FORMALIZATION_MAP.md` (Prop 1.6 row).
3. Update `guides/work_packages/GROEBNER_CM_TRANSFER.md` (R1 sub-sorry status).
4. Update `MEMORY.md` (Sorry Summary section).
5. Run `lake build` once for final sanity.
6. Report changes to the user. Do NOT commit or push unless explicitly
   asked (per `feedback_no_auto_commit.md`).

## Definition of done for this session

Best outcome: one of the two sub-sorries closed, build green, status docs
updated.

Minimum acceptable outcome: substantial concrete progress on one sub-sorry,
with the remaining gap isolated as one or more clearly-named smaller lemmas
with documented status. Not a regression of the framework (must still build
modulo the same sub-sorries).

Do not chase the universe generalization, the corollary restatements
(`corollary_3_4` real-CM branch, `corollary_3_7` real-CM branch), or the
`toMathlib/HeightAdditivity.lean` dormant sorries this session.

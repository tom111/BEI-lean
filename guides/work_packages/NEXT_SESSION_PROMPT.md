# Next-Session Prompt: Prop 1.6 R1 — close the colon-ideal sub-sorry

## Where we are

Paper-faithful `proposition_1_6` is assembled in `BEI/Proposition1_6.lean`,
modulo exactly **two** sub-sorries in `BEI/GroebnerDeformation.lean`:

1. `tildeJ_quotient_isCohenMacaulay` — global CM of `S[t] ⧸ Ĩ` (graded
   local-to-global step; depends on dormant Case-C of `toMathlib/GradedCM.lean`).
2. `tildeJ_polyT_colon_eq` — **the active leaf of the R1.d branch**: for
   every nonzero `q ∈ K[t]` and `c ∈ DefRing n K`,
   `polyTInclude q · c ∈ Ĩ ⟹ c ∈ Ĩ`.

The R1.d branch is now fully reduced to the single colon-ideal statement:

- `tildeJ_flat_over_polyT` (flatness) — PROVED conditional on
  `tildeJ_polyT_colon_eq`, via torsion-free ⇒ flat over the PID `K[t]`.
- `tildeJ_tMinusOne_isSMulRegular` + `tildeJ_t_isSMulRegular` — PROVED
  conditional on flatness.

Monomial-order scaffolding for the Gröbner-basis proof of the colon
sub-sorry is in place:

- `defLE` — paper's `x_1 > x_2 > ... > y_1 > ... > y_n` order extended
  with `t = Sum.inr ()` at the bottom.
- `defVars_Finite`, `defVars_LinearOrder`, `defVars_WellFoundedGT`.
- `deformationMonomialOrder n : MonomialOrder (BinomialEdgeVars (Fin n) ⊕ Unit)`.

Build is green. `proposition_1_6` axiom check unchanged:
`{propext, sorryAx, Classical.choice, Quot.sound}`.

## Required reading before starting

1. `BEI/GroebnerDeformation.lean` — R1 framework, `K[t]`-algebra,
   monomial order, the `tildeJ_polyT_colon_eq` sub-sorry at lines ~498–528.
2. Mathlib `Mathlib/RingTheory/MvPolynomial/Groebner.lean` — has
   `MonomialOrder.div`, `MonomialOrder.div_set`, `MonomialOrder.div_single`:
   the division algorithm for polynomials with unit leading coefficients.
3. `BEI/GroebnerBasis.lean` + `BEI/GroebnerBasisSPolynomial.lean` — for
   closed graphs, `{fij}` is a reduced Gröbner basis of `J_G`. The
   corresponding deformed statement for `{f̃_{i,j}}` as a GB of `Ĩ` has not
   been formalized yet, but would follow a similar Buchberger structure.

## Pick one of the two sub-sorries

### Option A (recommended) — close `tildeJ_polyT_colon_eq` for closed graphs

Classical proof:

1. **Leading term of `f̃_{i,j}` is `x_i y_j`** (for `i < j`) under
   `deformationMonomialOrder n`. Leading coefficient is `1` — a unit in
   `DefRing n K` (or in `PolyT K` if we transport via `sumAlgEquiv`).
2. **Division algorithm**: Mathlib's `MonomialOrder.div_set` gives a
   normal form for any `c ∈ DefRing n K` modulo `{f̃_{i,j}}`, with remainder
   `r` having no monomial divisible by any `x_i y_j` (an edge).
3. **Multiplying by `polyTInclude q`** (a pure-`t` polynomial) preserves
   the "no `x_i y_j` factor" property of the remainder's support.
4. **Gröbner basis property** (the genuinely new BEI fact): for closed
   graphs, if `p ∈ Ĩ` has support with no `x_i y_j` factor, then `p = 0`.
   Equivalently, `{f̃_{i,j}}` is a Gröbner basis of `Ĩ` (closed graphs).
5. From 2–4: if `polyTInclude q · c ∈ Ĩ`, then `polyTInclude q · r = 0`
   in `DefRing n K`. Since `DefRing n K` is a domain and `polyTInclude q ≠ 0`
   (from `q ≠ 0`), `r = 0`, so `c = Σ g_b · f̃_b ∈ Ĩ`.

Concrete session plan:

- Start with `leadingCoeff_fijTilde`: show
  `(deformationMonomialOrder n).leadingCoeff (fijTilde i j) = 1` when
  `i < j`. Unfolds: `fijTilde i j = x_i y_j - t^(j-i) x_j y_i`. Argue
  the `x_i y_j` term dominates under `deformationMonomialOrder` (lex
  with `x_i > x_j > y_i > y_j > t`). ~50–100 LOC.
- Then `degree_fijTilde`: the leading multi-index. Needed for
  `div_set`'s "remainder support" predicate.
- Apply `MonomialOrder.div_set` to get the normal form.
- The **Gröbner basis property** (step 4) is the genuinely new BEI fact.
  Either close it as a separate lemma (heavy: Buchberger for
  deformed generators, ~200–400 LOC), or add `IsClosedGraph G` to
  `tildeJ_polyT_colon_eq` and reduce to the closed-graph GB of `J_G`
  via deformation lifting. The latter likely needs `BEI/GroebnerBasis.lean`
  machinery re-expressed in the deformation setting.

If adding `IsClosedGraph G`, propagate through `tildeJ_flat_over_polyT`,
`tildeJ_tMinusOne_isSMulRegular`, `tildeJ_t_isSMulRegular`,
`tildeJ_quotient_isCohenMacaulay`, and `groebnerDeformation_cm_transfer`.
`binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` already has it.

### Option B — close `tildeJ_quotient_isCohenMacaulay`

Still blocked by GradedCM Case C (the dormant sorry in
`toMathlib/GradedCM.lean`). Three sub-options (unchanged from prior rounds):
B.1 close Case C directly (~400–800 LOC); B.2 graded Noether normalization;
B.3 no BEI-specific bypass was found in the 2026-04-20 audit.

Recommend Option A — the infrastructure is already started and the
remaining work is BEI-specific Gröbner combinatorics rather than new
graded commutative algebra.

## Workflow rules — IMPORTANT

Use the lean-lsp MCP tools, not `lake build`:

- `lean_diagnostic_messages BEI/GroebnerDeformation.lean` for file errors.
- `lean_goal`, `lean_multi_attempt`, `lean_local_search`, `lean_hover_info`.
- `lean_leansearch` / `lean_loogle` for Mathlib lemmas.
- Reserve `lake build` for the final sanity check.

## Other workflow notes

- `PolyT K` is registered as `IsPrincipalIdealRing` (hence Bezout, Dedekind).
- `Algebra (PolyT K) (DefRing n K)` instance + scalar tower already in place.
- `BinomialEdgeVars V` is a `def`; use `show` or `change` rather than hoping
  `simp` unfolds it.
- `WellFoundedGT` for `BinomialEdgeVars (Fin n) ⊕ Unit` required explicit
  diamond-avoidance with `Sum`'s default `LT` — see `defVars_WellFoundedGT`.
- The `K : Type` (universe 0) restriction is inherited from the F2 route.

## Commit discipline

When the sub-sorry is closed:

1. Update `TODO.md` (active sorry count, status block).
2. Update `FORMALIZATION_MAP.md` (Prop 1.6 row).
3. Update `guides/work_packages/GROEBNER_CM_TRANSFER.md` (R1 sub-sorry status).
4. Update `MEMORY.md` (Sorry Summary section).
5. Run `lake build` once for final sanity.
6. Commit with a focused message.
7. Push to both `origin` and `github` (per `feedback_push_all_remotes.md`).

## Definition of done for this session

Best outcome: `tildeJ_polyT_colon_eq` closed (conditional on `IsClosedGraph G`
if needed), build green, status docs updated.

Minimum acceptable outcome: substantial concrete progress on
`tildeJ_polyT_colon_eq` — e.g. `leadingCoeff_fijTilde` proved, `div_set`
application set up, with remaining gap isolated in a smaller named lemma.

Do not chase the universe generalization, the corollary restatements, or
the dormant sorries in `toMathlib/HeightAdditivity.lean` or
`toMathlib/GradedCM.lean` unless directly closing a blocker.

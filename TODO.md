# BEI Lean Formalization — Task List

## Status Legend
- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Paper ↔ Lean Status

| Paper result | Lean location | Status |
|---|---|---|
| **§1 Thm 1.1** (closed iff quadratic GB) | `BEI/ClosedGraphs.lean` | `[x]` proved |
| **§1 Prop 1.2** (closed implies chordal and claw-free) | `BEI/GraphProperties.lean` | `[x]` proved |
| **§1 Cor 1.3** (bipartite closed graphs / line graphs) | `BEI/GraphProperties.lean` | `[x]` paper-faithful version proved |
| **§1 Prop 1.4** (shortest paths directed) | `BEI/GraphProperties.lean` | `[x]` proved |
| **§1 Prop 1.5** (closure exists) | `BEI/GraphProperties.lean` | `[x]` proved |
| **§1 Prop 1.6** (CM sufficient condition) | `BEI/Proposition1_6.lean`, `BEI/PrimeDecompositionDimension.lean` | `[x]` **AXIOM-CLEAN 2026-04-22**: paper-faithful `proposition_1_6` fully proved via finite-free Case C route (Steps A+B+C+D). `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` closed via `groebnerDeformation_cm_transfer` + graded local-to-global CM. Equidimensional surrogate also proved. |
| **§2 Thm 2.1** (reduced Gröbner basis) | `BEI/GroebnerBasisSPolynomial.lean`, `BEI/GroebnerBasis.lean` | `[x]` proved |
| **§2 Cor 2.2** (`J_G` radical) | `BEI/Radical.lean` | `[x]` proved |
| **§3 Lem 3.1** (height formula for `P_S`) | `BEI/PrimeIdeals.lean` | `[x]` proved |
| **§3 Thm 3.2** (`J_G = ⋂ P_S`) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.3** (dimension formula) | `BEI/PrimeDecompositionDimension.lean` | `[x]` proved |
| **§3 Cor 3.4** (CM implies `dim = n + c`) | `BEI/PrimeDecompositionDimension.lean` | `[~]` equidimensional surrogate proved; full paper CM statement now achievable via `proposition_1_6_dim_formula` (2026-04-22, axiom-clean) |
| **§3 Prop 3.6** (prime iff components complete) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.7** (cycle equivalences) | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean`, `BEI/PrimeDecompositionDimension.lean` | `[~]` prime/unmixed/equidimensional branches proved; paper CM branch still surrogate-only |
| **§3 Prop 3.8** (`P_T ⊆ P_S` characterization) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§3 Cor 3.9** (minimal primes via cut-point sets) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§4 Bridge** (CI ideal = BEI, single statement) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Spec bridge** (robustness specification) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Radical** (CI ideal is radical) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Primes** (CI prime decomposition) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Minimal primes** (CI minimal prime characterization) | `BEI/CIIdeals.lean` | `[x]` proved (connected graphs) |

---

## Current Priorities

### Priority 1: Real Cohen-Macaulay track

**HH-side global CM theorem is now fully proved (2026-04-20).**
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` closes with
axioms `{propext, Classical.choice, Quot.sound}`. No `sorry` remains on
the critical path inside `BEI/`.

**Monomial-side CM for `J_G` packaged (2026-04-20).**
`monomialInitialIdeal_isCohenMacaulay` in `BEI/Equidim.lean` transports
the HH CM theorem along the y-predecessor ring isomorphism, giving that
`S ⧸ monomialInitialIdeal G` is globally CM under HH conditions
(restricted to `K : Type`). This closes Step 1 of the Prop 1.6 plan.

**Paper-faithful `proposition_1_6` assembled modulo two sub-sorries (2026-04-20; updated).**
`BEI/GroebnerDeformation.lean` lays down the full R1 framework: the
deformation ring `S[t]`, the deformation parameter, the deformed generators
`f̃_{i,j} = x_i y_j - t^(j-i) x_j y_i`, the deformation ideal `Ĩ`, the
specialization maps at `t = 0` and `t = 1`, the fiber identifications
`tildeJ_specZero_eq` (gives `monomialInitialIdeal G`) and `tildeJ_specOne_eq`
(gives `binomialEdgeIdeal G`), and the iso
`baseQuotEquiv : S ⧸ J_G ≃+* S[t] ⧸ (Ĩ ⊔ {t-1})`.

**Monomial-order infrastructure for R1.d closed (2026-04-20).** Opaque
type wrapper `DefVars n := BinomialEdgeVars (Fin n) ⊕ Unit` blocks the
`Sum.instLTSum` diamond on the deformation variable type. The order
`defLE` is arranged so `t = inr ()` is LARGEST (hence LEAST significant
in `MonomialOrder.lex`'s smallest-most-significant convention). The two
structural lemmas `degree_fijTilde` (leading monomial = `x_i y_j`) and
`leadingCoeff_fijTilde = 1` are proved (axioms
`{propext, Classical.choice, Quot.sound}`), with helper
`fijTilde_lex_lt`.

**R1.d colon chain fully closed (2026-04-20).**
The division-algorithm wrapper `tildeJ_div`, the support-transfer
lemma `polyTInclude_mul_support_avoids`, the colon-ideal theorem
`tildeJ_polyT_colon_eq`, `tildeJ_gbProperty` (via existing
`exists_degree_le_of_mem` in `BEI/Radical.lean`), and
**`tildeJ_isGroebnerBasis`** (the Buchberger proof that `{f̃_{i,j}}`
is a Gröbner basis of `Ĩ` under `deformationMonomialOrder`, for closed `G`)
are all proved with clean axioms
`{propext, Classical.choice, Quot.sound}`.
Consequently `tildeJ_flat_over_polyT`, `tildeJ_tMinusOne_isSMulRegular`,
and `tildeJ_t_isSMulRegular` are all sorry-free.

`hClosed : IsClosedGraph G` is threaded through the R1 chain
(`tildeJ_polyT_colon_eq`, `tildeJ_flat_over_polyT`,
`tildeJ_tMinusOne_isSMulRegular`, `tildeJ_t_isSMulRegular`,
`tildeJ_quotient_isCohenMacaulay`, `groebnerDeformation_cm_transfer`),
because the Gröbner-basis property only holds for closed graphs.

The four-arrow assembly `groebnerDeformation_cm_transfer` now has **zero
local sorries**: the BEI-side graded plumbing is complete, including the
local CM at the irrelevant ideal. Axiom check:
- `tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant`:
  `{propext, Classical.choice, Quot.sound}` — **clean**.
- `tildeJ_quotient_isCohenMacaulay`, `groebnerDeformation_cm_transfer`,
  `proposition_1_6`: `sorryAx` present transitively via the dormant
  Case-C sorry of `toMathlib/GradedCM.lean` (graded local-to-global
  theorem for non-homogeneous primes). Closing that single upstream
  gap would make Proposition 1.6 fully axiom-clean.

`BEI/Proposition1_6.lean` now reduces to one line —
`binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm := groebnerDeformation_cm_transfer hCM`.
The high-level `proposition_1_6` axiom check is
`{propext, sorryAx, Classical.choice, Quot.sound}`.

Active follow-up work now lives in:
- `guides/work_packages/FULL_PROP_1_6_PLAN.md` — overall 3-phase plan (Phase 1 done)
- `guides/work_packages/PROP_1_6_CM_TRANSFER.md` — overall CM transfer strategy
- `guides/work_packages/GROEBNER_CM_TRANSFER.md` — the Gröbner deformation transfer (Phase 2, still open)

Completed / superseded packets are now under `guides/archive/` (see
`guides/INDEX.md`).

Supporting files on this branch:
- `BEI/PrimeDecompositionDimension.lean`
- `BEI/Equidim.lean`
- `toMathlib/CohenMacaulay/Defs.lean` — first real CM foundation layer: `ringDepth`, `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`, and the basic inequality `ringDepth ≤ ringKrullDim`
- `toMathlib/CohenMacaulay/Basic.lean` — quotient-local-ring setup, the easy depth inequality `depth(R/xR) + 1 ≤ depth(R)`, and the converse regular-quotient CM transfer
- `toMathlib/CohenMacaulay/Localization.lean` — forward CM transfer, unmixedness, `CM localizes`, and the local-ring global-CM wrapper
- `toMathlib/MonomialIdeal.lean` — `Ideal.IsMonomial`, prime classification, radical-is-monomial, full primary iff characterization
- `toMathlib/SquarefreeMonomialPrimes.lean` — variable-pair ideals, vertex covers, and minimal prime ↔ minimal vertex cover
- `toMathlib/HeightVariableIdeal.lean` — quotients by variable ideals, quotient equivalences, and dimension formulas

`IsEquidim` now has a real local working definition (equidimensionality, adapted
from mathlib PR #26218) in `toMathlib/Equidim/Defs.lean`.

`prop_1_6_equidim` is now proved directly via equidimensionality (0 sorries).
The proof is in `BEI/PrimeDecompositionDimension.lean`, not the paper's Gröbner
degeneration route. It uses:
1. `closedGraph_componentCount_le_card_add_one` — convex components in closed graphs give
   `c(S) ≤ |S| + 1` (in `BEI/Equidim.lean`)
2. `corollary_3_9` — cut vertex property for minimal-prime sets
3. `closedGraph_minimalPrime_componentCount_eq` — combines 1+2 to get `c(S) = |S| + 1`
4. `isEquidim_of_equidim_minimalPrimes` + `ringKrullDim_quot_primeComponent`

The old paper-faithful route (HH bipartite graph → monomial ideal CM → transfer) is
still present as infrastructure in `BEI/Equidim.lean`. The iterated HH regularity theorem
`sum_XY_isSMulRegular_mod_diagonalSum` is now proved there, and the key CM bridge lemmas
are also done:
- `isSMulRegular_of_doubleQuot` — transfers NZD from `R ⧸ (I ⊔ J)` to `(R ⧸ I) ⧸ J.map mk_I`
- `ideal_smul_top_self` — `I • ⊤ = I` for the self-module
- `mem_map_mk_iff_mem_sup` — `mk_I(x) ∈ J.map mk_I ↔ x ∈ I ⊔ J`

The `IsWeaklyRegular` theorem `bipartiteEdgeMonomialIdeal_isWeaklyRegular` is now fully
proved (0 sorries): the diagonal elements form a weakly regular sequence on the bipartite
quotient under HH conditions.

The quotient dimension formula is now proved:
- `ringKrullDim_bipartiteEdgeMonomialIdeal`: `dim(S ⧸ I) = n + 1` under HH conditions
- Uses `ringKrullDim_quotient_radical_equidim` (radical + equidim → dim = common value)
- Supporting lemmas: `bipartiteEdgeMonomialIdeal_ne_top`, `minimalVertexCover_ncard_val`

The free variable NZD steps are now proved:
- `X_inl_last_isSMulRegular_mod_diagonalSum`: `x_{n-1}` is NZD on `S ⧸ (I ⊔ diag_{n-1})`
- `X_inr_last_isSMulRegular_mod_diagonalSum_sup`: `y_{n-1}` is NZD on `S ⧸ (I ⊔ diag_{n-1} ⊔ ⟨x_{n-1}⟩)`

The full regular sequence and local CM at the augmentation ideal are now proved:
- `bipartiteEdgeMonomialIdeal_isWeaklyRegular_full`: full weakly regular sequence of
  length `n + 1 = dim` on `S ⧸ I` (diagonal sums + two free variables)
- `isCohenMacaulayLocalRing_at_augIdeal`: `IsCohenMacaulayLocalRing` at the
  augmentation ideal (kernel of constant-coefficient map) under HH conditions

The CM-localization backport route is now complete in
`toMathlib/CohenMacaulay/Localization.lean`:

- forward CM transfer is proved;
- unmixedness for CM local rings is proved;
- localization of CM local rings at primes is proved;
- and the wrapper `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` is proved.

Together with the F2 route (L1, L4, L5, L7 replacement, Session A′, Session B,
Session C1 bundled equiv, Session C2 tensor-left-localisation bridge, and
Session C3 assembly), this now closes the HH-side global CM theorem
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` (restricted to
`K : Type` because of the universe-monomorphic polynomial-away tensor API).

Both branches of the two-case split are proved:
1. the branch `p ≤ augIdeal`: closed via `isCohenMacaulayLocalRing_at_augIdeal` + CM localizes;
2. the branch `p ⊄ augIdeal`: closed via pick-U + E_U + C2 bridge + L7 tensor-away CM.

Earlier dehomogenization / graded-local-to-global route memos are preserved in
`guides/archive/`.

The Gröbner CM transfer theorem (Eisenbud 15.17) also remains unformalized, so the full
paper Cohen–Macaulay statement is still open even after the HH-side CM theorem lands.
That second paper-critical gap is now tracked separately in
`guides/work_packages/GROEBNER_CM_TRANSFER.md`.

The real CM foundation files:

1. `toMathlib/CohenMacaulay/Defs.lean` — definitions and the basic inequality
   `ringDepth ≤ ringKrullDim`
2. `toMathlib/CohenMacaulay/Basic.lean` — quotient-local-ring instances,
   `ringDepth_quotSMulTop_succ_le`,
   `isCohenMacaulayLocalRing_of_regular_quotient`,
   `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim` (new),
   `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero` (new)
3. `toMathlib/CohenMacaulay/Localization.lean` — Ext/Rees machinery, the hard
   depth inequality, forward CM transfer, unmixedness, localization of CM local
   rings, and the local-ring global-CM wrapper

Note: the direct proof uses the repo's local equidimensional surrogate for
Cohen–Macaulayness. This does not yet count as a full formalization of the paper's
depth-based CM statement.

### Priority 2: Section 4

Section 4 is complete in `BEI/CIIdeals.lean`. All transfers proved:
- Single-statement and specification-level bridge theorems
- Radicality (Cor 2.2), prime decomposition (Thm 3.2), minimal primes (Cor 3.9)

The minimal-prime transfer assumes a connected union graph, mirroring `corollary_3_9`.

### Background / dormant

- `toMathlib/HeightAdditivity.lean` is still incomplete, but it is not currently on the
  critical path.
- `Supplement/RauhApproach.lean` remains archived and off the main import path.
- `lake build` succeeds for the whole project; the only remaining `sorry`s are the two
  dormant ones in `toMathlib/HeightAdditivity.lean` and the two archived ones in
  `Supplement/RauhApproach.lean`.

---

## Current File Split

- `BEI/GroebnerBasisSPolynomial.lean` carries the Buchberger / S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2 and Proposition 3.6.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3, the equidimensional surrogate version `corollary_3_4_equidim`, `corollary_3_7_equidim`, the path equidimensional example, `prop_1_6_equidim`, and supporting quotient-dimension / equidimensionality lemmas.
- `BEI/CIIdeals.lean` carries the Section 4 binary-output setup, the single-statement and specification-level CI ideal = BEI bridges, and the transferred radicality / prime-decomposition / minimal-prime theorems.
- `BEI/Equidim.lean` carries the local equidimensional surrogate API, the HH bipartite-graph infrastructure, the closed-graph component-count upper bound, and the complete-graph equidimensional example.
- `toMathlib/Equidim/Defs.lean` carries the local working equidimensional definition used by the current surrogate branch.
- `toMathlib/CohenMacaulay/Defs.lean` carries the first real Cohen–Macaulay foundation layer: local/global CM definitions via regular-sequence depth and the basic inequality `ringDepth ≤ ringKrullDim`.
- `toMathlib/CohenMacaulay/Localization.lean` carries the Ext/Rees bridge, the hard depth inequality, forward CM transfer, unmixedness, and the localization/globalization theorems for CM local rings.
- `toMathlib/MonomialIdeal.lean` carries `Ideal.IsMonomial`, the `Set σ` version of `isPrime_span_X_image`, the prime classification theorem for monomial ideals, `Ideal.IsMonomial.span_X_image`, `coeff_pow_lexMax`, `Ideal.IsMonomial.radical_isMonomial`, `Ideal.isPrimary_monomial_criterion`, `Ideal.IsMonomial.isPrimary_radical_eq_span_X`, the structural lemmas `Ideal.monomial_mem_iff_add_outside` / `Ideal.monomial_mem_iff_filter`, the general support-extraction lemma `Ideal.not_mem_exists_monomial_notMem`, the converse helper `Ideal.mem_of_mul_mem_of_lexMax_outside`, and the full primary iff `Ideal.IsMonomial.isPrimary_iff`.
- `toMathlib/SquarefreeMonomialPrimes.lean` carries `MvPolynomial.variablePairIdeal`, `MvPolynomial.IsVertexCover`, `MvPolynomial.IsMinimalVertexCover`, the containment-iff-vertex-cover theorem, and the complete minimal prime ↔ minimal vertex cover characterization.
- `toMathlib/HeightVariableIdeal.lean` carries the variable-killing quotient map, the quotient-by-variable-ideal equivalence, and the quotient-dimension formulas for variable ideals.

Some of these splits still need cleanup, but these are the current live locations.

---

## Active Sorry Count

| File | Sorries | Notes |
|---|---:|---|
| `BEI/Equidim.lean` | 0 | HH global CM theorem closed 2026-04-20 |
| `BEI/PrimeDecompositionDimension.lean` | 0 | direct equidimensional Prop. 1.6 route complete |
| `BEI/PrimeDecomposition.lean` | 0 | |
| `toMathlib/CohenMacaulay/Localization.lean` | 0 | completed CM-localization backport |
| `toMathlib/HeightAdditivity.lean` | 2 | dormant infrastructure |
| `toMathlib/GradedCM.lean` | 0 | **Case C CLOSED 2026-04-22**: `caseC_CM_transfer` deleted; `isCohenMacaulayLocalRing_atPrime_of_not_isHomogeneous` now routes through the new finite-free Case C assembly + `CM_localize`. `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant` now requires `[Algebra.FiniteType K A]`, auto-inferred downstream. Axiom-clean. |
| `toMathlib/GradedAssociatedPrime.lean` | 0 | BH 1.5.6 complete (associated primes homogeneous), axioms `{propext, Classical.choice, Quot.sound}` (2026-04-21) |
| `toMathlib/GradedFiniteFree.lean` | 0 | **Step C fully PROVED 2026-04-22.** All pieces axiom-clean: B1/B2a/B2b/D, `exists_homogeneous_basis_of_finite_graded`, `exists_homogeneous_decomposition_mem_span_range`, `span_aeval_eq_top_of_homogeneous_basis_lift` (surjectivity), `linearIndependent_aeval_fin_zero` + `linearIndependent_aeval_cons_step` + `linearIndependent_aeval_of_basis_lift` (injectivity via d-induction + finSuccEquiv + regularity), main `finiteFree_over_mvPolynomial_of_homogeneous_regular_sop`. |
| `toMathlib/GradedRegularSop.lean` | 0 | Full Step A iteration 2026-04-21 + Case C combined assembly `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree` added 2026-04-22. Both axiom-clean. |
| `Supplement/RauhApproach.lean` | 2 | archived, not on main path |
| `BEI/GroebnerDeformation.lean` | 0 | R1 framework **fully closed BEI-side**. `groebnerDeformation_cm_transfer`, `tildeJ_quotient_isCohenMacaulay`: axiom-clean `{propext, Classical.choice, Quot.sound}` as of 2026-04-22 (GradedCM Case C closure removed the last transitive sorryAx). |
| `BEI/Proposition1_6.lean` | 0 | **AXIOM-CLEAN 2026-04-22.** `proposition_1_6`, `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm`, `pathGraph_binomialEdgeIdeal_isCohenMacaulay` all depend only on `{propext, Classical.choice, Quot.sound}`. |
| **Active total** | **0** | **Zero active sorries on the paper-critical path. Proposition 1.6 is fully formalized axiom-clean.** Only dormant sorries remain: `toMathlib/HeightAdditivity.lean` (2, dormant infrastructure) and `Supplement/RauhApproach.lean` (2, archived). |

---

## Maintenance Rule

Whenever a theorem is finished, moved, or split across files, update this file and
`FORMALIZATION_MAP.md` in the same round. The code is the source of truth; the docs
should follow immediately.

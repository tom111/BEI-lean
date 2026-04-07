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
| **§1 Prop 1.6** (CM sufficient condition) | `BEI/CohenMacaulay.lean` | `[~]` graph-combinatorial reduction done; final algebraic CM step still open |
| **§2 Thm 2.1** (reduced Gröbner basis) | `BEI/GroebnerBasisSPolynomial.lean`, `BEI/GroebnerBasis.lean` | `[x]` proved |
| **§2 Cor 2.2** (`J_G` radical) | `BEI/Radical.lean` | `[x]` proved |
| **§3 Lem 3.1** (height formula for `P_S`) | `BEI/PrimeIdeals.lean` | `[x]` proved |
| **§3 Thm 3.2** (`J_G = ⋂ P_S`) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.3** (dimension formula) | `BEI/PrimeDecompositionDimension.lean` | `[x]` proved |
| **§3 Cor 3.4** (CM implies `dim = n + c`) | `BEI/PrimeDecompositionDimension.lean` | `[x]` proved |
| **§3 Prop 3.6** (prime iff components complete) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.7** (cycle equivalences) | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean`, `BEI/PrimeDecompositionDimension.lean` | `[x]` proved (all four branches) |
| **§3 Prop 3.8** (`P_T ⊆ P_S` characterization) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§3 Cor 3.9** (minimal primes via cut-point sets) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§4 Bridge** (CI ideal = BEI, single statement) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Spec bridge** (robustness specification) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Radical** (CI ideal is radical) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Primes** (CI prime decomposition) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Minimal primes** (CI minimal prime characterization) | `BEI/CIIdeals.lean` | `[x]` proved (connected graphs) |

---

## Current Priorities

### Priority 1: Cohen–Macaulay branch

Active CM work lives in:
- `BEI/CohenMacaulay.lean`
- `toMathlib/MonomialIdeal.lean` — `Ideal.IsMonomial`, prime classification, radical-is-monomial, full primary iff characterization
- `toMathlib/SquarefreeMonomialPrimes.lean` — variable-pair ideals, vertex covers, and minimal prime ↔ minimal vertex cover
- `guides/PROP_1_6_COHEN_MACAULAY.md`
- `guides/PROP_1_6_HH_EQUIDIMENSIONALITY.md`
- `guides/ANSWER_05_COHEN_MACAULAY_FOUNDATION.md`
- `guides/ANSWER_16_PROP_1_6_EQUIDIMENSIONALITY.md`
- `guides/CM_CODEBASE_RESEARCH_MONOMIAL_IDEAL.md`
- `guides/cm_pr_26218/`

`IsCohenMacaulay` now has a real local working definition (equidimensionality, adapted
from mathlib PR #26218) in `toMathlib/CohenMacaulay/Defs.lean`.

The remaining CM paper endpoint is:
- `BEI/CohenMacaulay.lean`: `prop_1_6`

Recently completed CM groundwork includes:
- `BEI/CohenMacaulay.lean`: `complete_is_CM`
- `BEI/CohenMacaulay.lean`: `prop_1_6_herzogHibi`
- `BEI/CohenMacaulay.lean`: `initialIdeal_closed_eq`, `yPredVar`, `rename_yPredVar_generator`, `bipartiteEdgeMonomialIdeal`
- `BEI/CohenMacaulay.lean`: `rename_yPredVar_monomialInitialIdeal`
- `BEI/PrimeDecompositionDimension.lean`: `path_is_CM`
- `BEI/PrimeDecompositionDimension.lean`: quotient-dimension and equidimensionality helpers
- `toMathlib/MonomialIdeal.lean`: `coeff_pow_lexMax`, prime classification,
  `Ideal.IsMonomial.radical_isMonomial`,
  `Ideal.IsMonomial.isPrimary_radical_eq_span_X`,
  `Ideal.IsMonomial.isPrimary_of_criterion`,
  `Ideal.IsMonomial.isPrimary_iff`

The primary monomial ideal characterization is now complete (both directions).

For Proposition 1.6 specifically, the remaining gap is now algebraic rather than graph-theoretic:
- Herzog–Hibi CM theorem for the associated bipartite graph
- transfer from `S / in_<(J_G)` to `S / J_G`

The minimal-primes-via-vertex-covers correspondence is now proved in
`toMathlib/SquarefreeMonomialPrimes.lean`:
- `MvPolynomial.variablePairIdeal_le_span_X_iff` (containment ↔ vertex cover)
- `MvPolynomial.minimalPrime_variablePairIdeal_iff` (minimal primes = minimal vertex covers)

The variable-pair bridge and minimal-prime transport are now proved in
`BEI/CohenMacaulay.lean`:
- `bipartiteEdgeMonomialIdeal_eq_variablePairIdeal` (ideal equality)
- `minimalPrime_bipartiteEdgeMonomialIdeal_iff` (minimal primes = minimal vertex covers)

The remaining algebraic gap for Proposition 1.6 is:
- use the Herzog–Hibi conditions to show all minimal vertex covers of `hhEdgeSet G`
  have equal size (equidimensionality)
- finish the CM transfer from `S / in_<(J_G)` back to `S / J_G`

### Priority 2: Section 4

Section 4 is complete in `BEI/CIIdeals.lean`. All transfers proved:
- Single-statement and specification-level bridge theorems
- Radicality (Cor 2.2), prime decomposition (Thm 3.2), minimal primes (Cor 3.9)

The minimal-prime transfer assumes a connected union graph, mirroring `corollary_3_9`.

### Background / dormant

- `toMathlib/HeightAdditivity.lean` is still incomplete, but it is not currently on the
  critical path.
- `BEI/RauhApproach.lean` remains archived and off the main import path.

---

## Current File Split

- `BEI/GroebnerBasisSPolynomial.lean` carries the Buchberger / S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2 and Proposition 3.6.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3, Corollary 3.4, `corollary_3_7_CM`, the path CM example, and supporting quotient-dimension / equidimensionality lemmas.
- `BEI/CIIdeals.lean` carries the Section 4 binary-output setup, the single-statement and specification-level CI ideal = BEI bridges, and the transferred radicality / prime-decomposition / minimal-prime theorems.
- `BEI/CohenMacaulay.lean` carries Proposition 1.6 and the complete-graph CM example.
- `toMathlib/CohenMacaulay/Defs.lean` carries the local working CM definition used by the current CM branch.
- `toMathlib/MonomialIdeal.lean` carries `Ideal.IsMonomial`, the `Set σ` version of `isPrime_span_X_image`, the prime classification theorem for monomial ideals, `Ideal.IsMonomial.span_X_image`, `coeff_pow_lexMax`, `Ideal.IsMonomial.radical_isMonomial`, `Ideal.isPrimary_monomial_criterion`, `Ideal.IsMonomial.isPrimary_radical_eq_span_X`, the structural lemmas `Ideal.monomial_mem_iff_add_outside` / `Ideal.monomial_mem_iff_filter`, the general support-extraction lemma `Ideal.not_mem_exists_monomial_notMem`, the converse helper `Ideal.mem_of_mul_mem_of_lexMax_outside`, and the full primary iff `Ideal.IsMonomial.isPrimary_iff`.
- `toMathlib/SquarefreeMonomialPrimes.lean` carries `MvPolynomial.variablePairIdeal`, `MvPolynomial.IsVertexCover`, `MvPolynomial.IsMinimalVertexCover`, the containment-iff-vertex-cover theorem, and the complete minimal prime ↔ minimal vertex cover characterization.

Some of these splits still need cleanup, but these are the current live locations.

---

## Active Sorry Count

| File | Sorries | Notes |
|---|---:|---|
| `BEI/CohenMacaulay.lean` | 1 | `prop_1_6` |
| `BEI/PrimeDecomposition.lean` | 0 | |
| `toMathlib/HeightAdditivity.lean` | 2 | dormant infrastructure |
| `BEI/RauhApproach.lean` | 2 | archived, not on main path |
| **Active total** | **3** | excluding archived `RauhApproach` |

---

## Maintenance Rule

Whenever a theorem is finished, moved, or split across files, update this file and
`FORMALIZATION_MAP.md` in the same round. The code is the source of truth; the docs
should follow immediately.

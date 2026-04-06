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
| **§3 Cor 3.4** (CM implies `dim = n + c`) | `BEI/PrimeDecompositionDimension.lean` | `[~]` statement present, proof still open |
| **§3 Prop 3.6** (prime iff components complete) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.7** (cycle equivalences) | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean` | `[~]` partial: prime and unmixed branches done, CM branch still open |
| **§3 Prop 3.8** (`P_T ⊆ P_S` characterization) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§3 Cor 3.9** (minimal primes via cut-point sets) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§4 Bridge** (CI ideal = BEI, single statement) | `BEI/CIIdeals.lean` | `[x]` proved |
| **§4 Multi** (robustness specification, corollaries) | not yet started | `[ ]` pending |

---

## Current Priorities

### Priority 1: Cohen–Macaulay branch

Active CM work lives in:
- `BEI/CohenMacaulay.lean`
- `guides/PROP_1_6_COHEN_MACAULAY.md`
- `guides/COR_3_4_CM_DIMENSION.md`
- `guides/ANSWER_05_COHEN_MACAULAY_FOUNDATION.md`
- `guides/ANSWER_16_PROP_1_6_EQUIDIMENSIONALITY.md`
- `guides/cm_pr_26218/`

`IsCohenMacaulay` now has a real local working definition (equidimensionality, adapted
from mathlib PR #26218) in `toMathlib/CohenMacaulay/Defs.lean`.

The remaining CM endpoints are:
- `BEI/CohenMacaulay.lean`: `prop_1_6`
- `BEI/PrimeDecompositionDimension.lean`: `corollary_3_4`
- `BEI/PrimeDecomposition.lean`: `corollary_3_7_CM`

Recently completed CM groundwork includes:
- `BEI/CohenMacaulay.lean`: `complete_is_CM`
- `BEI/CohenMacaulay.lean`: `prop_1_6_herzogHibi`
- `BEI/CohenMacaulay.lean`: `initialIdeal_closed_eq`, `yPredVar`, `rename_yPredVar_generator`, `bipartiteEdgeMonomialIdeal`
- `BEI/CohenMacaulay.lean`: `rename_yPredVar_monomialInitialIdeal`
- `BEI/PrimeDecompositionDimension.lean`: `path_is_CM`
- `BEI/PrimeDecompositionDimension.lean`: quotient-dimension and equidimensionality helpers

For Proposition 1.6 specifically, the remaining gap is now algebraic rather than graph-theoretic:
- Herzog–Hibi CM theorem for the associated bipartite graph
- transfer from `S / in_<(J_G)` to `S / J_G`

This branch is no longer blocked on a missing definition, but it still needs honest
proofs and should not be overclaimed.

### Priority 2: Section 4

Section 4 has begun in `BEI/CIIdeals.lean`. The single-statement bridge theorem
(`ciIdeal_single_eq_binomialEdgeIdeal`) is proved. Remaining work:
- Multi-statement robustness specifications (union of CI graphs)
- Corollaries transferring radicality (Cor 2.2) and minimal prime characterization
  (Section 3) to CI ideals via the bridge

### Background / dormant

- `toMathlib/HeightAdditivity.lean` is still incomplete, but it is not currently on the
  critical path.
- `BEI/RauhApproach.lean` remains archived and off the main import path.

---

## Current File Split

- `BEI/GroebnerBasisSPolynomial.lean` carries the Buchberger / S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2, Proposition 3.6, and the CM/cycle endpoints.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3, Corollary 3.4, the path CM example, and supporting quotient-dimension / equidimensionality lemmas.
- `BEI/CohenMacaulay.lean` carries Proposition 1.6 and the complete-graph CM example.
- `toMathlib/CohenMacaulay/Defs.lean` carries the local working CM definition used by the current CM branch.

Some of these splits still need cleanup, but these are the current live locations.

---

## Active Sorry Count

| File | Sorries | Notes |
|---|---:|---|
| `BEI/CohenMacaulay.lean` | 1 | `prop_1_6` |
| `BEI/PrimeDecomposition.lean` | 1 | `corollary_3_7_CM` |
| `BEI/PrimeDecompositionDimension.lean` | 1 | `corollary_3_4` |
| `toMathlib/HeightAdditivity.lean` | 2 | dormant infrastructure |
| `BEI/RauhApproach.lean` | 2 | archived, not on main path |
| **Active total** | **5** | excluding archived `RauhApproach` |

---

## Maintenance Rule

Whenever a theorem is finished, moved, or split across files, update this file and
`FORMALIZATION_MAP.md` in the same round. The code is the source of truth; the docs
should follow immediately.

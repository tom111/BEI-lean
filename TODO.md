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
| **§1 Prop 1.6** (CM sufficient condition) | `BEI/CohenMacaulay.lean` | `[!]` blocked on real CM foundations |
| **§2 Thm 2.1** (reduced Gröbner basis) | `BEI/GroebnerBasisSPolynomial.lean`, `BEI/GroebnerBasis.lean` | `[x]` proved |
| **§2 Cor 2.2** (`J_G` radical) | `BEI/Radical.lean` | `[x]` proved |
| **§3 Lem 3.1** (height formula for `P_S`) | `BEI/PrimeIdeals.lean` | `[x]` proved |
| **§3 Thm 3.2** (`J_G = ⋂ P_S`) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.3** (dimension formula) | `BEI/PrimeDecompositionDimension.lean` | `[x]` proved |
| **§3 Cor 3.4** (CM implies `dim = n + c`) | `BEI/PrimeDecomposition.lean` | `[!]` statement present, proof blocked on CM |
| **§3 Prop 3.6** (prime iff components complete) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.7** (cycle equivalences) | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean` | `[~]` partial: prime branch done, unmixed branch nearly done, CM branch blocked |
| **§3 Prop 3.8** (`P_T ⊆ P_S` characterization) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§3 Cor 3.9** (minimal primes via cut-point sets) | `BEI/MinimalPrimes.lean` | `[x]` proved |
| **§4** (CI-ideal applications) | not yet started | `[ ]` pending |

---

## Current Priorities

### Priority 1: Cohen–Macaulay foundations

Active CM work lives in:
- `BEI/CohenMacaulay.lean`
- `guides/PROP_1_6_COHEN_MACAULAY.md`
- `guides/COR_3_4_CM_DIMENSION.md`
- `guides/ANSWER_05_COHEN_MACAULAY_FOUNDATION.md`
- `guides/cm_pr_26218/`

The honest blocker is still the same: `IsCohenMacaulay` is currently a placeholder,
so Proposition 1.6, Corollary 3.4, and the CM branch of Corollary 3.7 are not yet
genuinely formalized.

### Priority 2: Finish Corollary 3.7 outside the CM branch

The remaining non-CM work is in `BEI/MinimalPrimes.lean`:
- `cycle_induce_preconnected`
- one downstream cycle combinatorics lemma
- `corollary_3_7_unmixed`

These are much smaller than the CM foundations and should stay separated from them.

### Priority 3: Section 4

Section 4 has not started. It should wait until the Section 3 backbone and CM story
are stable enough that the final statements can be phrased cleanly.

### Background / dormant

- `toMathlib/HeightAdditivity.lean` is still incomplete, but it is not currently on the
  critical path.
- `BEI/RauhApproach.lean` remains archived and off the main import path.

---

## Current File Split

- `BEI/GroebnerBasisSPolynomial.lean` carries the Buchberger / S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2, Proposition 3.6, and the CM/cycle endpoints.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3.

Some of these splits still need cleanup, but these are the current live locations.

---

## Active Sorry Count

| File | Sorries | Notes |
|---|---:|---|
| `BEI/CohenMacaulay.lean` | 4 | placeholder CM definition and CM branch theorems |
| `BEI/PrimeDecomposition.lean` | 2 | `corollary_3_4`, `corollary_3_7_CM` |
| `BEI/MinimalPrimes.lean` | 2 | cycle / unmixed combinatorics |
| `toMathlib/HeightAdditivity.lean` | 2 | dormant infrastructure |
| `BEI/RauhApproach.lean` | 2 | archived, not on main path |
| **Active total** | **10** | excluding archived `RauhApproach` |

---

## Maintenance Rule

Whenever a theorem is finished, moved, or split across files, update this file and
`FORMALIZATION_MAP.md` in the same round. The code is the source of truth; the docs
should follow immediately.

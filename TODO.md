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
| **§1 Prop 1.6** (CM sufficient condition) | `BEI/CohenMacaulay.lean` | `[~]` `prop_1_6` is fully assembled; the only remaining sorry is the isolated transfer theorem `cm_transfer_initialIdeal` |
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
- `toMathlib/HeightVariableIdeal.lean` — quotients by variable ideals, quotient equivalences, and dimension formulas
- `guides/PROP_1_6_COHEN_MACAULAY.md`
- `guides/PROP_1_6_CM_TRANSFER.md`
- `guides/ANSWER_05_COHEN_MACAULAY_FOUNDATION.md`
- `guides/ANSWER_16_PROP_1_6_EQUIDIMENSIONALITY.md`
- `guides/CM_CODEBASE_RESEARCH_MONOMIAL_IDEAL.md`
- `guides/cm_pr_26218/`

`IsCohenMacaulay` now has a real local working definition (equidimensionality, adapted
from mathlib PR #26218) in `toMathlib/CohenMacaulay/Defs.lean`.

`prop_1_6` is now a clean wrapper theorem. The only remaining sorry in this branch is
the isolated transfer lemma `cm_transfer_initialIdeal`. The proof chain is:
1. `bipartiteEdgeMonomialIdeal_isCohenMacaulay` — bipartite edge ideal quotient is CM
2. `monomialInitialIdeal_isCohenMacaulay` — monomial initial ideal quotient is CM (via `yPredEquiv` ring isomorphism)
3. `cm_transfer_initialIdeal` — Gröbner CM transfer from `in_<(J_G)` to `J_G` (**1 sorry**)

New theorems in this round:
- `isCohenMacaulay_of_ringEquiv` — CM transfers through ring isomorphisms (fully proved)
- `yPredEquiv` — y-predecessor variable equivalence (fully proved)
- `monomialInitialIdeal_isCohenMacaulay` — CM of the monomial initial ideal quotient (fully proved)
- `cm_transfer_initialIdeal` — Gröbner CM transfer (sorry; standard result not in Mathlib v4.28.0)

The **only remaining gap** is:
- `cm_transfer_initialIdeal`: `S / in_<(J_G)` CM → `S / J_G` CM
  (standard Gröbner degeneration theorem; Eisenbud, Thm 15.17)

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
- `toMathlib/HeightVariableIdeal.lean` carries the variable-killing quotient map, the quotient-by-variable-ideal equivalence, and the quotient-dimension formulas for variable ideals.

Some of these splits still need cleanup, but these are the current live locations.

---

## Active Sorry Count

| File | Sorries | Notes |
|---|---:|---|
| `BEI/CohenMacaulay.lean` | 1 | `cm_transfer_initialIdeal` (Gröbner CM transfer) |
| `BEI/PrimeDecomposition.lean` | 0 | |
| `toMathlib/HeightAdditivity.lean` | 2 | dormant infrastructure |
| `BEI/RauhApproach.lean` | 2 | archived, not on main path |
| **Active total** | **1** | excluding dormant `HeightAdditivity` and archived `RauhApproach` |

---

## Maintenance Rule

Whenever a theorem is finished, moved, or split across files, update this file and
`FORMALIZATION_MAP.md` in the same round. The code is the source of truth; the docs
should follow immediately.

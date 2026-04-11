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
| **§1 Prop 1.6** (CM sufficient condition) | `BEI/PrimeDecompositionDimension.lean` | `[~]` equidimensional surrogate proved directly; full paper CM statement still open |
| **§2 Thm 2.1** (reduced Gröbner basis) | `BEI/GroebnerBasisSPolynomial.lean`, `BEI/GroebnerBasis.lean` | `[x]` proved |
| **§2 Cor 2.2** (`J_G` radical) | `BEI/Radical.lean` | `[x]` proved |
| **§3 Lem 3.1** (height formula for `P_S`) | `BEI/PrimeIdeals.lean` | `[x]` proved |
| **§3 Thm 3.2** (`J_G = ⋂ P_S`) | `BEI/PrimeDecomposition.lean` | `[x]` proved |
| **§3 Cor 3.3** (dimension formula) | `BEI/PrimeDecompositionDimension.lean` | `[x]` proved |
| **§3 Cor 3.4** (CM implies `dim = n + c`) | `BEI/PrimeDecompositionDimension.lean` | `[~]` equidimensional surrogate proved; full paper CM statement still open |
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

Active follow-up work now lives in:
- `guides/work_packages/PROP_1_6_CM_TRANSFER.md`
- `guides/work_packages/cm_pr_26218/`

Supporting files on this branch:
- `BEI/PrimeDecompositionDimension.lean`
- `BEI/Equidim.lean`
- `toMathlib/CohenMacaulay/Defs.lean` — first real CM foundation layer: `ringDepth`, `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`, and the basic inequality `ringDepth ≤ ringKrullDim`
- `toMathlib/CohenMacaulay/Basic.lean` — quotient-local-ring setup, the easy depth inequality `depth(R/xR) + 1 ≤ depth(R)`, and the converse regular-quotient CM transfer
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

The next step toward a genuine `IsCohenMacaulayRing` conclusion requires:
1. localizing the weakly regular sequence at primes (Mathlib has
   `IsWeaklyRegular.isRegular_of_isLocalization_of_mem`)
2. showing the localized dimension matches the sequence length
3. applying `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim`

The Gröbner CM transfer theorem (Eisenbud 15.17) also remains unformalized, so the full
paper Cohen–Macaulay statement is still open.

The real CM foundation files:

1. `toMathlib/CohenMacaulay/Defs.lean` — definitions and the basic inequality
   `ringDepth ≤ ringKrullDim`
2. `toMathlib/CohenMacaulay/Basic.lean` — quotient-local-ring instances,
   `ringDepth_quotSMulTop_succ_le`,
   `isCohenMacaulayLocalRing_of_regular_quotient`,
   `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim` (new),
   `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero` (new)

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
- `toMathlib/MonomialIdeal.lean` carries `Ideal.IsMonomial`, the `Set σ` version of `isPrime_span_X_image`, the prime classification theorem for monomial ideals, `Ideal.IsMonomial.span_X_image`, `coeff_pow_lexMax`, `Ideal.IsMonomial.radical_isMonomial`, `Ideal.isPrimary_monomial_criterion`, `Ideal.IsMonomial.isPrimary_radical_eq_span_X`, the structural lemmas `Ideal.monomial_mem_iff_add_outside` / `Ideal.monomial_mem_iff_filter`, the general support-extraction lemma `Ideal.not_mem_exists_monomial_notMem`, the converse helper `Ideal.mem_of_mul_mem_of_lexMax_outside`, and the full primary iff `Ideal.IsMonomial.isPrimary_iff`.
- `toMathlib/SquarefreeMonomialPrimes.lean` carries `MvPolynomial.variablePairIdeal`, `MvPolynomial.IsVertexCover`, `MvPolynomial.IsMinimalVertexCover`, the containment-iff-vertex-cover theorem, and the complete minimal prime ↔ minimal vertex cover characterization.
- `toMathlib/HeightVariableIdeal.lean` carries the variable-killing quotient map, the quotient-by-variable-ideal equivalence, and the quotient-dimension formulas for variable ideals.

Some of these splits still need cleanup, but these are the current live locations.

---

## Active Sorry Count

| File | Sorries | Notes |
|---|---:|---|
| `BEI/Equidim.lean` | 0 | paper-faithful CM-transfer route kept as future infrastructure |
| `BEI/PrimeDecompositionDimension.lean` | 0 | direct equidimensional Prop. 1.6 route complete |
| `BEI/PrimeDecomposition.lean` | 0 | |
| `toMathlib/HeightAdditivity.lean` | 2 | dormant infrastructure |
| `Supplement/RauhApproach.lean` | 2 | archived, not on main path |
| **Active total** | **0** | excluding dormant `HeightAdditivity` and archived `RauhApproach` |

---

## Maintenance Rule

Whenever a theorem is finished, moved, or split across files, update this file and
`FORMALIZATION_MAP.md` in the same round. The code is the source of truth; the docs
should follow immediately.

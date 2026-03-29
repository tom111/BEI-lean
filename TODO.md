# BEI Lean Formalization — Task List

## Status Legend
- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Paper ↔ Formalization Map

| Paper result | File | Status |
|---|---|---|
| **§1 Thm 1.1** (closed ↔ quadratic GB) | ClosedGraphs.lean | ✅ proved |
| **§1 Prop 1.2** (closed → chordal + claw-free) | GraphProperties.lean | ✅ proved |
| **§1 Cor 1.3** (closed + bipartite → line) | GraphProperties.lean | ✅ proved |
| **§1 Prop 1.4** (closed ↔ shortest paths directed) | GraphProperties.lean | ✅ proved |
| **§1 Prop 1.5** (closure existence) | GraphProperties.lean | ✅ proved |
| **§1 Prop 1.6** (CM sufficient condition for closed graphs) | CohenMacaulay.lean | ❌ blocked on `IsCohenMacaulay` |
| **§2 Thm 2.1** (reduced GB = admissible paths) | GroebnerBasis.lean | ✅ proved |
| **§2 Cor 2.2** (J_G radical) | Radical.lean | ✅ proved |
| **§3 Lem 3.1** (height P_S = \|S\| + n − c(S)) | PrimeIdeals.lean | ❌ sorry |
| **§3 Thm 3.2** (J_G = ⋂ P_S) | PrimeDecomposition.lean | ✅ proved |
| **§3 Cor 3.3** (dim S/J_G formula) | PrimeDecomposition.lean | ❌ sorry (needs 3.2) |
| **§3 Cor 3.4** (CM → dim = n+c) | PrimeDecomposition.lean | ❌ sorry (needs 3.2) |
| **§3 Prop 3.6** (J_G prime ↔ components complete) | PrimeIdeals.lean | ❌ sorry |
| **§3 Cor 3.7** (cycle: n=3 ↔ prime ↔ CM) | PrimeDecomposition.lean | ❌ sorry (needs 3.2) |
| **§3 Prop 3.8** (P_T ⊆ P_S characterization) | MinimalPrimes.lean | ✅ proved |
| **§3 Cor 3.9** (minimal primes = cut-points) | MinimalPrimes.lean | → proved, ← sorry |
| **§4** (CI-ideal connection to robustness) | — | ❌ not yet started |

---

## Mathlib Availability (checked v4.28.0)

| Concept | Status | Location |
|---|---|---|
| `Ideal.IsRadical` | **available** | `Mathlib.RingTheory.Ideal.Operations` |
| `Ideal.height` / `primeHeight` | **available** | `Mathlib.RingTheory.Ideal.Height` |
| `krullDim` | **available** | `Mathlib.Order.KrullDimension` |
| `MonomialOrder` + division | **available** | `Mathlib.RingTheory.MvPolynomial.Groebner` |
| `Squarefree` | **available** | `Mathlib.Algebra.Squarefree.Basic` |
| Initial ideal (`in_<(I)`) | **not available** | no `MonomialOrder.initialIdeal` |
| Squarefree initial → radical | **not available** | needs Gröbner deformation |
| `IsCohenMacaulay` | **not available** | no CM definition at all |
| Flat deformation / Gröbner family | **not available** | only flat morphisms in AG |
| Conditional independence ideals | **not available** | no CI-ideal theory |
| Bipartite CM (Herzog-Hibi) | **not available** | needs CM + graph theory |

---

## Remaining Work (prioritized)

### ~~Priority 1: Theorem 3.2 ⊇~~ ✅ DONE
### ~~Priority 2: Corollary 2.2~~ ✅ DONE

### Priority 3: Corollary 3.9 ← — minimal primes = cut-points (reverse)
**NOW UNBLOCKED** by theorem_3_2 + minimalPrimes_characterization.
**Paper argument:** Contradiction via Prop 3.8 and component counting.
If c(S\{i}) < c(S) for all i ∈ S, then P_S is minimal. If P_T ⊆ P_S for
proper T ⊂ S, choose i ∈ S\T. By c(S\{i}) < c(S), vertex i connects ≥2
components. The components of G[V\T] merging through i violate Prop 3.8.
**File:** MinimalPrimes.lean (~80-120 lines)

### Priority 4: Proposition 3.6 — J_G prime ↔ components complete
**Uses:** theorem_3_2. Forward: all complete → J_G = P_∅ is prime.
Backward: J_G prime → unique minimal prime → P_∅ = J_G → all components complete.
**File:** PrimeIdeals.lean (~60-100 lines)

### Priority 5: Corollary 3.7 — cycle: n=3 ↔ prime
**Uses:** Prop 3.6. Cycle prime ↔ complete ↔ n ≤ 3. Since n ≥ 3: n = 3.
**File:** PrimeDecomposition.lean (~40-60 lines)

### Priority 6: Lemma 3.1 — height(P_S) = |S| + (n − c(S))
**Paper argument:** height = 2|S| + Σ(n_j − 1) = |S| + n − c(S).
**Mathlib:** `Ideal.height` exists. Need to compute:
(a) height({x_i, y_i}) = 2|S| (chain of primes)
(b) height(J_{K_n}) = n−1 (2-minors of 2×n matrix — main obstacle)
(c) Heights add for ideals in disjoint variable sets
**File:** PrimeIdeals.lean (~200-300 lines, HARD)

### Priority 7: Corollaries 3.3, 3.3 lower bound
dim S/J_G = max{(n−|S|) + c(S)}, and dim ≥ n + c(G).
**Dependencies:** Lem 3.1 + Thm 3.2.
**File:** PrimeDecomposition.lean (~100 lines)

### Priority 8: Cohen-Macaulay results (DEFERRED)
All 6 CM-related sorries (Cor 3.4, Cor 3.7 CM, IsCohenMacaulay def,
Prop 1.6, complete_is_CM, path_is_CM) are blocked on `IsCohenMacaulay`
not existing in Mathlib v4.28.0. Deferred until Mathlib adds CM support.
**Files:** CohenMacaulay.lean, PrimeDecomposition.lean

### Priority 9: Section 4 — CI-ideal applications (NOT STARTED)
Define probability ring, CI-ideal construction, show correspondence with BEI.
Apply Thm 3.2 + Cor 2.2. New file `BEI/CIIdeals.lean` (~300-500 lines).

---

## Sorry Count by File (2026-03-29)
| File | Sorries | Notes |
|------|---------|-------|
| GroebnerBasis.lean | 0 | Cor 2.2 moved to Radical.lean, PROVED |
| Radical.lean | 0 | Cor 2.2 fully proved (squarefree GB → radical) |
| PrimeIdeals.lean | 2 | Lem 3.1, Prop 3.6 |
| MinimalPrimes.lean | 1 | Cor 3.9 ← only |
| PrimeDecomposition.lean | 5 | corollaries only (Thm 3.2 + minimalPrimes PROVED) |
| CohenMacaulay.lean | 4 | Prop 1.6 + CM definition |
| RauhApproach.lean | 2 | archived alternative approach |
| **Total** | **14** | |

---

## Notes
- `groebnerBasisSet_span`: PROVED — Ideal.span groebnerBasisSet = J_G
- `theorem_1_1`: PROVED — closed ↔ quadratic GB
- `theorem_2_1`: PROVED — reduced GB for admissible paths
- `theorem_2_1_reduced`: PROVED — GB is reduced
- `groebnerElement_leadingMonomial_squarefree`: PROVED
- `isGroebnerBasis_iff_sPolynomial_isRemainder`: PROVED (Buchberger criterion)
- `primeComponent_isPrime`: PROVED
- `prop_3_8`: PROVED (P_T ⊆ P_S characterization)
- `theorem_3_2`: PROVED — J_G = ⋂ P_S (fully sorry-free)
- `minimalPrimes_characterization`: PROVED — minimal primes = minimal P_S's
- `iInf_primeComponent_eq_radical`: PROVED — ⋂ P_S = radical(J_G) (no sorry dependency)
- `corollary_2_2`: PROVED — J_G is radical (squarefree Gröbner basis → radical)
- `isRadical_of_squarefree_isGroebnerBasis`: PROVED — general radicality theorem
- `Ideal.height` IS in Mathlib v4.28.0 (previously assumed missing)
- `IsCohenMacaulay` is NOT in Mathlib v4.28.0 (confirmed)
- Initial ideal construction is NOT in Mathlib v4.28.0

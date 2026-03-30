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
| **§3 Prop 3.6** (J_G prime ↔ components complete) | PrimeDecomposition.lean | ✅ proved |
| **§3 Cor 3.7** (cycle: n=3 ↔ prime) | PrimeDecomposition.lean | ✅ proved |
| **§3 Cor 3.7 CM** (cycle: prime ↔ CM) | PrimeDecomposition.lean | ❌ sorry (needs CM) |
| **§3 Prop 3.8** (P_T ⊆ P_S characterization) | MinimalPrimes.lean | ✅ proved |
| **§3 Cor 3.9** (minimal primes = cut-points) | MinimalPrimes.lean | ✅ proved |
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

### ~~Priority 3: Corollary 3.9~~ ✅ DONE
### ~~Priority 4: Proposition 3.6~~ ✅ DONE
### ~~Priority 5: Corollary 3.7~~ ✅ DONE

### Priority 6: Lemma 3.1 — height(P_S) = |S| + (n − c(S))  ⚠️ BLOCKED
**Paper argument:** height = 2|S| + Σ(n_j − 1) = |S| + n − c(S).
**Approach:** P_S = ker(primeComponentMap G S), so height(P_S) = dim(R) − dim(R/P_S)
= 2n − (n − |S| + c(S)) = |S| + n − c(S). The image ring has transcendence
degree n − |S| + c(S) (n − |S| independent x-variables + c(S) component parameters).

**Mathlib infrastructure available:**
- `Ideal.height` definition (`Mathlib.RingTheory.Ideal.Height`)
- `MvPolynomial.ringKrullDim_of_isNoetherianRing`: dim(K[X₁,...,Xₙ]) = n
- Krull's height theorem: height(P) ≤ |generators| (`KrullsHeightTheorem.lean`)
- `height_le_ringKrullDim_quotient_add_spanFinrank`: ht(p) ≤ dim(R/I) + spanFinrank(I)
- `IsLocalization.AtPrime.ringKrullDim_eq_height`: dim(R_p) = ht(p)

**Mathlib gaps (blockers):**
- **No catenary property**: `IsCatenary` not defined in Mathlib v4.28.0
- **No height+dim formula**: `height(P) + dim(R/P) = dim(R)` for polynomial rings
  over fields is NOT in Mathlib. Only the inequality `height(P) ≤ dim(R)` exists.
- **No transcendence degree = Krull dim**: For f.g. algebras over fields, the equality
  `trdeg = krullDim` is not formalized.
- Krull's height theorem gives only the WEAK upper bound ht ≤ |generators|, not
  the exact value, since the 2-minor ideal of a 2×n matrix has height n−1 but
  needs n(n−1)/2 generators (not a complete intersection for n ≥ 3).

**File:** PrimeIdeals.lean (~200-300 lines, HARD — blocked on Mathlib gaps)

### Priority 7: Corollaries 3.3, 3.3 lower bound  ⚠️ BLOCKED on Lem 3.1
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
| PrimeIdeals.lean | 1 | Lem 3.1 only (Prop 3.6 moved to PrimeDecomposition) |
| MinimalPrimes.lean | 0 | Cor 3.9 FULLY PROVED |
| PrimeDecomposition.lean | 4 | Prop 3.6 PROVED, Cor 3.7 PROVED; 4 corollary sorries remain |
| CohenMacaulay.lean | 4 | Prop 1.6 + CM definition |
| RauhApproach.lean | 2 | archived alternative approach |
| **Total** | **11** | |

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
- `prop_3_6`: PROVED — J_G prime ↔ every connected component is complete (evaluation map argument)
- `corollary_3_7`: PROVED — cycle: n=3 ↔ J_G prime (degree constraint from cycle graph)
- `Ideal.height` IS in Mathlib v4.28.0 (previously assumed missing)
- `IsCohenMacaulay` is NOT in Mathlib v4.28.0 (confirmed)
- Initial ideal construction is NOT in Mathlib v4.28.0

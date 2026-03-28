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
| **§2 Cor 2.2** (J_G radical) | GroebnerBasis.lean | ❌ sorry (see Priority 1) |
| **§3 Lem 3.1** (height P_S = \|S\| + n − c(S)) | PrimeIdeals.lean | ❌ sorry |
| **§3 Thm 3.2** (J_G = ⋂ P_S) | PrimeDecomposition.lean | ⊆ proved, ⊇ sorry |
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

### Priority 1: Theorem 3.2 ⊇ — ⋂ P_S(G) ⊆ J_G
**The key unlocking result.** Almost everything else depends on this.
**Paper argument (induction on n):**
1. Show every minimal prime P of J_G has P = P_S(G) for some S.
2. Key step: x_i ∈ P ⟺ y_i ∈ P (uses connected graph + prime argument).
3. Then: P contains no variables → show f_{ij} ∈ P for all edges of complete
   components (x-telescope: x_{i₁} f_{ij} = x_j f_{i,i₁} + x_i f_{i₁,j}, prime argument).
4. Since J_G radical and every minimal prime is P_S, we get J_G = ⋂ P_S.
**Note:** Step 4 needs J_G radical (Cor 2.2). BUT the paper's proof of Thm 3.2 actually
establishes the minimal prime structure FIRST, from which radicality follows. So the
correct order is: Thm 3.2 (characterize minimal primes) → J_G = ⋂ primes → J_G radical.
This breaks the apparent circularity.
**File:** PrimeDecomposition.lean
**Dependencies:** `primeComponent_isPrime` (done), `binomialEdgeIdeal_le_primeComponent` (done)

### Priority 2: Corollary 2.2 — J_G is radical
**Paper argument:** Squarefree initial ideal ⇒ radical (Gröbner deformation).
**Alternative:** Derive as consequence of Thm 3.2 (J_G = ⋂ primes ⇒ radical).
**Mathlib:** `Ideal.IsRadical` exists. If using Thm 3.2 route, need: intersection of
primes is radical (should be in Mathlib or easy to prove).
**File:** GroebnerBasis.lean

### Priority 3: Corollary 3.9 ← — minimal primes = cut-points (reverse)
**Paper argument:** Contradiction via Prop 3.8 and component counting.
**Dependencies:** Prop 3.8 (done). Thm 3.2 (to know minimal primes are all P_S).
**File:** MinimalPrimes.lean

### Priority 4: Lemma 3.1 — height(P_S) = |S| + (n − c(S))
**Paper argument:** height = 2|S| + Σ(n_j − 1) = |S| + n − c(S).
**Mathlib:** `Ideal.height` exists. Need to compute height of (variables) + (2-minors of
generic matrices) ideals. Height of 2-minors of 2×n matrix = n−1 (standard, may need proof).
**File:** PrimeIdeals.lean

### Priority 5: Corollaries 3.3, 3.4, 3.7, Prop 3.6
All follow from Thm 3.2 + Lem 3.1 by straightforward arguments.
- **Cor 3.3:** dim S/J_G = max{(n−|S|) + c(S)}
- **Cor 3.4:** CM ⇒ dim = n + c
- **Cor 3.7:** Cycle: n=3 ↔ prime ↔ unmixed ↔ CM
- **Prop 3.6:** J_G prime ↔ each component complete
**Files:** PrimeDecomposition.lean, PrimeIdeals.lean

### Priority 6: Proposition 1.6 — CM sufficient condition for closed graphs
**Paper argument:** Show S/in_<(J_G) is CM via bipartite edge ideal characterization
(Herzog-Hibi). Then CM lifts from initial ideal to original.
**Blockers:** (a) `IsCohenMacaulay` not in Mathlib (b) bipartite CM characterization
(c) CM lifts through flat deformation.
**Approach:** Define `IsCohenMacaulay` locally (as `depth = dim` or via regular sequences),
prove the bipartite characterization, then the lifting. This is substantial standalone work.
**File:** CohenMacaulay.lean

### Priority 7: Section 4 — CI-ideal applications
**Paper content:** Connect binomial edge ideals to conditional independence statements.
Show CI-ideals of "robustness specifications" with binary output are radical, and
their primary decomposition has statistical interpretation.
**Approach:** Define the polynomial ring for probability distributions, the CI-ideal
construction, and show the correspondence with binomial edge ideals. Then apply
Thm 3.2 and Cor 2.2.
**File:** new `BEI/CIIdeals.lean`

---

## Sorry Count by File (2026-03-29)
| File | Sorries | Notes |
|------|---------|-------|
| GroebnerBasis.lean | 1 | Cor 2.2 |
| PrimeIdeals.lean | 2 | Lem 3.1, Prop 3.6 |
| MinimalPrimes.lean | 1 | Cor 3.9 ← only |
| PrimeDecomposition.lean | 7 | Thm 3.2 ⊇ + corollaries |
| CohenMacaulay.lean | 4 | Prop 1.6 + CM definition |
| RauhApproach.lean | 2 | archived alternative approach |
| **Total** | **17** | |

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
- `theorem_3_2` (⊆): proved via `binomialEdgeIdeal_le_primeComponent`
- `Ideal.height` IS in Mathlib v4.28.0 (previously assumed missing)
- `IsCohenMacaulay` is NOT in Mathlib v4.28.0 (confirmed)
- Initial ideal construction is NOT in Mathlib v4.28.0

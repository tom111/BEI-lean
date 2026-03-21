# BEI Lean Formalization — Task List

## Status Legend
- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Phase 1 — Fix Compilation Blocker
- [x] `MonomialOrder.lean:50` — Replace `Sum.instFinite` with `inferInstance`

## Phase 2 — MonomialOrder Leading Term Proofs
- [x] `BinomialEdgeVars` changed to opaque `def` to eliminate instance diamond
- [x] `binomialEdgeMonomialOrder` — defined via `MonomialOrder.lex`
- [x] `fij_degree`, `fij_leadingCoeff`, `fij_leadingCoeff_isUnit`

## Phase 3 — Graph Theory Properties
- [x] `prop_1_4` — closed ↔ all shortest walks directed
- [x] `cor_1_3` — closed + bipartite → path graph (noTriangle + degree bound + acyclicity)

---

## Phase 4 — Admissible Paths Membership
- [x] All compilation errors fixed (Groups 1-5, type mismatch, chain'_reverse)
- [x] `groebnerElement_mem` — proved

---

## Phase 5 — Prime Ideal Properties

### 5A. `primeComponent_isPrime` — **PROVED** ✅
Actual strategy used: construct φ : K[x,y] → K[x,y] directly (not a quotient target).
φ sends x_i,y_i ↦ 0 for i∈S; x_j ↦ X(inl j), y_j ↦ X(inl j)*X(inr(rep j)) for j∉S.
ker(φ) = P_S(G) via primeComponent_le_ker + ker_primeComponentMap_le (strong induction on
support size using normExp/FiberEquiv/monomial_swap_mem). P_S(G) prime by RingHom.ker_isPrime.

- [x] **5A-i** `primeComponentMap G S` defined via `MvPolynomial.aeval`
- [x] **5A-ii** `primeComponent_le_ker`: generators map to 0
- [x] **5A-iii** Target K[x,y] is integral domain (no need for product ring)
- [x] **5A-iv** `primeComponent_isPrime`: PROVED

- [ ] `lemma_3_1` — height formula (very hard; needs chain of prime ideals)
- [ ] `prop_3_6` — J_G prime ↔ each component complete

---

## Phase 6 — Minimal Primes

- [x] `prop_3_8_var_not_mem` — proved via eval argument
- [x] `prop_3_8` (→): T ⊆ S via `prop_3_8_var_not_mem`
- [x] `prop_3_8_sameComponent_preserved` — proved via eval
- [x] `prop_3_8` (←): T⊆S + component preservation → P_T ≤ P_S
- [~] `corollary_3_9` — → proved; ← still sorry (needs theorem_3_2 ⊇)

---

## Phase 7 — Prime Decomposition

- [x] `theorem_3_2` (⊆): proved inline via `binomialEdgeIdeal_le_primeComponent`
- [ ] `theorem_3_2` (⊇): ⋂ P_S(G) ⊆ J_G — hard; needs J_G is radical + Nullstellensatz
- [ ] `corollary_3_3_lower_bound` — dim ≥ |V| + c(G) via S = ∅ chain (relatively accessible)
- [ ] `corollary_3_7` — cycle: n=3 ↔ J_G prime
- [ ] `minimalPrimes_characterization`, `corollary_3_3`, `corollary_3_4` — depend on thm_3_2

---

## Phase 8 — Gröbner Basis

### 8A. Squarefreeness
- [x] `groebnerElement_leadingMonomial_squarefree`

### 8B. Gröbner basis API (BEI/GroebnerAPI.lean)
- [x] `MonomialOrder.IsRemainder`
- [x] `MonomialOrder.IsGroebnerBasis`
- [x] `MonomialOrder.exists_isRemainder`
- [x] `isGroebnerBasis_iff_sPolynomial_isRemainder` — **Buchberger criterion FULLY PROVED**
  (WFI + sPolynomial_decomposition' + IsRemainder representation update; ~400 lines)

### 8C. Leading coefficient lemma
- [x] `groebnerElement_leadingCoeff`

### 8D. S-polynomial reductions (Buchberger case analysis for Theorem 1.1)
Target: `closed_implies_groebner` in `ClosedGraphs.lean` (NOT in GroebnerBasis.lean)
**ALL CASES PROVED.** All helper lemmas in ClosedGraphs.lean.

### 8E. `theorem_2_1` — Gröbner basis for admissible paths (GroebnerBasis.lean)

**Approach: Herzog et al. (2010) direct S-polynomial proof (Second Step).**

For any f_π1, f_π2 in G, show S(f_π1, f_π2) reduces to 0 mod G via Buchberger.
- Coprime initial terms: trivial (regular sequence argument)
- Shared endpoint i=k: S-poly = y_i · f_{jl} (or similar), decompose along τ-path
- Shared endpoint j=l: symmetric

The τ-path construction: concatenate π1 and π2 at their common vertex, extract
subsequence of "jump points" j_{t(0)} < j_{t(1)} < ... < j_{t(q)}, each sub-path
τ_c is admissible, and the telescoping sum gives a standard expression with remainder 0.

Previous Rauh approach archived in `RauhApproach.lean`.

- [ ] `theorem_2_1` — 1 sorry remaining

### 8F. Radical
- [!] `corollary_2_2` — blocked on Thm 3.2 (radical = intersection of primes) or squarefree initial
  ideal → radical (not in Mathlib v4.28.0); deferred

---

## Phase 9 — Theorem 1.1 ✅ COMPLETE
- [x] `closed_implies_groebner` — PROVED (Buchberger criterion + 4-case S-polynomial analysis)
- [x] `theorem_1_1` — PROVED (⟨groebner_implies_closed, closed_implies_groebner⟩)
- [x] `groebner_implies_closed` — PROVED

---

## Phase 10 — Cohen-Macaulay (deferred; not in Mathlib)
- [!] All deferred until `IsCohenMacaulay` is in Mathlib

---

## Priority Order (what to work on next)

1. **Phase 8E: `theorem_2_1`** — Herzog direct S-polynomial proof (interactive with user)
2. **Phase 6: `corollary_3_9`** — cut-vertex characterization of minimal primes
3. **Phase 7: `theorem_3_2` ⊇** — radical ideal argument
4. **Phase 7: corollaries** — once Thm 3.2 proved

---

## Sorry Count by File (2026-03-21)
| File | Sorries |
|------|---------|
| GroebnerBasis.lean | 2 (theorem_2_1, corollary_2_2) |
| PrimeIdeals.lean | 2 (lemma_3_1, prop_3_6) |
| MinimalPrimes.lean | 1 (corollary_3_9 <- only) |
| PrimeDecomposition.lean | 7 |
| CohenMacaulay.lean | 4 (all deferred) |
| **Total** | **16** |

---

## Notes
- `groebnerBasisSet_span`: PROVED (GroebnerBasis.lean) — Ideal.span groebnerBasisSet = J_G
- `theorem_1_1`: PROVED (ClosedGraphs.lean) — closed <-> quadratic GB
- `isGroebnerBasis_iff_sPolynomial_isRemainder`: PROVED (GroebnerAPI.lean)
- `primeComponent_isPrime`: PROVED (PrimeIdeals.lean)
- `theorem_3_2` (⊆): proved inline via `binomialEdgeIdeal_le_primeComponent`
- `RauhApproach.lean`: archived alternative approach (bihomogeneity, crossing, killVars)
- `corollary_2_2`: deferred (squarefree initial -> radical not in Mathlib v4.28.0)
- Cohen-Macaulay: deferred (IsCohenMacaulay not in Mathlib)

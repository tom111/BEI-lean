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

### 5A. `primeComponent_isPrime` — broken into sub-steps
The paper strategy: K[x,y]/P_S(G) injects into `⊗_{component C} K[t_v : v ∈ C, s]` via xᵢ ↦ tᵢ, yᵢ ↦ s·tᵢ.

- [ ] **5A-i** Define the ring map `φ : MvPolynomial (BinomialEdgeVars V) K → Target` where
  `Target` is a product of polynomial rings (one per connected component of G[V\S])
- [ ] **5A-ii** Show φ kills each generator of P_S(G)
- [ ] **5A-iii** Show Target is an integral domain
- [ ] **5A-iv** Conclude P_S(G) is prime

- [ ] `lemma_3_1` — height formula (very hard; needs chain of prime ideals)
- [ ] `prop_3_6` — J_G prime ↔ each component complete

---

## Phase 6 — Minimal Primes

- [x] `prop_3_8_var_not_mem` — proved via eval argument
- [x] `prop_3_8` (→): T ⊆ S via `prop_3_8_var_not_mem`
- [x] `prop_3_8_sameComponent_preserved` — proved via eval
- [x] `prop_3_8` (←): T⊆S + component preservation → P_T ≤ P_S
- [ ] `corollary_3_9` — depends on `primeComponent_isPrime` (Phase 5A, hard)

---

## Phase 7 — Prime Decomposition

- [ ] `theorem_3_2` (⊆): **already follows** from `binomialEdgeIdeal_le_primeComponent`
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

Strategy: Apply `isGroebnerBasis_iff_sPolynomial_isRemainder` then case analysis:

**Case 1 — Same pair** (g₁ = g₂): S = 0 → trivial (sPolynomial_self + isRemainder_zero)

**Case 2 — Shared first endpoint** (i₁ = i₂ = i, j₁ ≠ j₂):
- [x] `sPolynomial_fij_shared_first`: S(fij i j₁, fij i j₂) = -(y i) * fij j₁ j₂  (ring identity)
- [x] `isRemainder_single_mul`: IsRemainder (q * f) G 0 when f ∈ G
- Use closedness h.1 to get G.Adj j₁ j₂; sub-cases on j₁ < j₂ vs j₁ > j₂

**Case 3 — Shared last endpoint** (j₁ = j₂ = j):
- [x] `sPolynomial_fij_shared_last`: S(fij i₁ j, fij i₂ j) = x j * fij i₁ i₂  (ring identity)
- Use closedness h.2 to get G.Adj i₁ i₂; sub-cases on i₁ < i₂ vs i₁ > i₂

**Case 4 — Coprime** (i₁ ≠ i₂ and j₁ ≠ j₂):
- Key identity: S = x j₂ * y i₂ * fij i₁ j₁ - x j₁ * y i₁ * fij i₂ j₂
  (same polynomial as from sPolynomial_def, by ring since fij₁ * fij₂ = fij₂ * fij₁)
- Degree bounds:
  - Let M2 = deg(fij i₁ j₁) + deg(x j₂ * y i₂), M1 = deg(fij i₂ j₂) + deg(x j₁ * y i₁)
  - M1 ≠ M2 (proved: at position inl i₁, M2 has 1 but M1 has 0 since i₁ ≠ i₂ and i₁ < j₁)
  - Case M2 > M1: deg(S) = M2 by degree_sub_of_lt; M2 ≼ M2 = deg(S) ✓; M1 ≺ M2 so ≼ ✓
  - Case M1 > M2: symmetric
- No closedness needed for this case (pure algebra)
- [~] `isRemainder_coprime_fij` — needs to be written and committed

**Overall status**: helper lemmas for Cases 1-3 are proved but not yet written into ClosedGraphs.lean.
Case 4 coprime lemma still needs to be written.

### 8E. Radical
- [!] `corollary_2_2` — blocked on Thm 3.2 (radical = intersection of primes) or squarefree initial
  ideal → radical (not in Mathlib v4.28.0); deferred

---

## Phase 9 — Theorem 1.1 (blocked on 8D)
- [~] `closed_implies_groebner` — in progress (helper lemmas proved, coprime case needed)
- [ ] `theorem_1_1` — follows from `closed_implies_groebner` ∧ `groebner_implies_closed`
- [x] `groebner_implies_closed` — PROVED

---

## Phase 10 — Cohen-Macaulay (deferred; not in Mathlib)
- [!] All deferred until `IsCohenMacaulay` is in Mathlib

---

## Priority Order (what to work on next)

1. **Phase 9: `closed_implies_groebner`** — write helper lemmas into file, prove coprime case
   - Add `zero_le_syn`, `isRemainder_single_mul`, `sPolynomial_fij_shared_first/last` to ClosedGraphs.lean
   - Write `isRemainder_coprime_fij` (coprime degree bound via case-split on M1 vs M2)
   - Assemble `closed_implies_groebner` proof
2. **Phase 9: `theorem_1_1`** — trivial once `closed_implies_groebner` is done
3. **Phase 5A: `primeComponent_isPrime`** — key unblocking lemma for rest
4. **Phase 7: `theorem_3_2` ⊇** — radical ideal argument
5. **Phase 7: corollaries** — once Thm 3.2 proved

---

## Why These Sorries Are Hard

### "Medium" (genuine Lean work, unblocked)
- `closed_implies_groebner` (9): Coprime case degree bound + finsupp witness construction
- `corollary_3_3_lower_bound` (7): Follows from chain of primes

### "Hard" (genuine mathematical content)
- `primeComponent_isPrime` (5A): Needs explicit ring map construction in Lean
- `theorem_3_2` ⊇ (7): Radical ideal theory
- `theorem_2_1_groebner/_leading/_reduced` (8D for GroebnerBasis.lean): Full Buchberger for admissible paths

### "Very Hard / Deferred" (depends on missing Mathlib)
- `lemma_3_1`: Height formula (needs Gröbner basis + dimension theory)
- `corollary_2_2`: Squarefree initial ideal → radical (not in Mathlib v4.28.0)
- Cohen-Macaulay: Deferred until `IsCohenMacaulay` in Mathlib

---

## Sorry Count by File (current)
| File | Sorries |
|------|---------|
| GraphProperties.lean | 0 |
| AdmissiblePaths.lean | 0 |
| MonomialOrder.lean | 0 |
| GroebnerAPI.lean | 0 (Buchberger criterion PROVED) |
| GroebnerBasis.lean | 4 (theorem_2_1_groebner, _leading, _reduced; cor2_2) |
| PrimeIdeals.lean | 3 (isPrime, lemma_3_1, prop_3_6) |
| MinimalPrimes.lean | 1 (corollary_3_9, blocked on primeComponent_isPrime) |
| PrimeDecomposition.lean | 7 (thm3_2 ⊇, minPrimesChar, cor3_3 ×2, cor3_4, cor3_7 ×2) |
| ClosedGraphs.lean | 2 (thm1_1, closed→GB) |
| CohenMacaulay.lean | 4 (def + 3 thms, all deferred) |
| **Total** | **21** |

---

## Notes
- `groebner_implies_closed`: PROVED (ClosedGraphs.lean)
- `isGroebnerBasis_iff_sPolynomial_isRemainder`: FULLY PROVED (GroebnerAPI.lean)
- `theorem_3_2` (⊆): already proved by `binomialEdgeIdeal_le_primeComponent`
- `theorem_2_1_leading` needs `f ≠ 0` hypothesis; currently incorrectly stated
- `idealHeight` uses `Ideal.primeHeight` from Mathlib

## Helper lemmas proved but not yet in file (for closed_implies_groebner)
```lean
-- BEI/ClosedGraphs.lean — needs to be written:
private lemma zero_le_syn (d : BinomialEdgeVars V →₀ ℕ) :
    binomialEdgeMonomialOrder.toSyn 0 ≤ binomialEdgeMonomialOrder.toSyn d := bot_le (after simp)

lemma isRemainder_single_mul (f q : MvPolynomial (BinomialEdgeVars V) K)
    (G : Set ...) (h_mem : f ∈ G) : IsRemainder (q * f) G 0
  -- via Finsupp.single b₀ q, linearCombination_single, degree trivially ≼ itself

lemma sPolynomial_fij_shared_first (i j₁ j₂ : V) (hij₁ : i < j₁) (hij₂ : i < j₂) (hj : j₁ ≠ j₂) :
    sPolynomial (fij i j₁) (fij i j₂) = -(y i) * fij j₁ j₂
  -- by sPolynomial_def + Finsupp sup/tsub computation + ring

lemma sPolynomial_fij_shared_last (i₁ i₂ j : V) (hi₁j : i₁ < j) (hi₂j : i₂ < j) (hi : i₁ ≠ i₂) :
    sPolynomial (fij i₁ j) (fij i₂ j) = x j * fij i₁ i₂
  -- symmetric to above
```

## Coprime case: key degree bound argument
Given fij i₁ j₁ and fij i₂ j₂ with i₁ ≠ i₂, j₁ ≠ j₂:
- S = x j₂ * y i₂ * fij i₁ j₁ - x j₁ * y i₁ * fij i₂ j₂  (ring identity, same as from sPolynomial_def)
- M2 := deg(fij i₁ j₁) + e_{inl j₂} + e_{inr i₂}, M1 := deg(fij i₂ j₂) + e_{inl j₁} + e_{inr i₁}
- M1 ≠ M2: at position inl i₁, M2 = 1 but M1 = 0 (since i₁ ≠ i₂ and i₁ ≠ j₁)
- Case split on toSyn M1 < toSyn M2 vs toSyn M2 < toSyn M1 (via lt_or_gt_of_ne)
- In each case, use degree_sub_of_lt to compute deg(S) = max(M1, M2)
- Degree bounds then follow from eq or lt
- IsRemainder witness: two-element Finsupp (single b₁ (x j₂ * y i₂) + single b₂ (-(x j₁ * y i₁)))

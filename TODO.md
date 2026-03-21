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

### 8E. `theorem_2_1_groebner` — Gröbner basis for admissible paths (GroebnerBasis.lean)

⭐ **RESTRUCTURED (2nd time): Single sorry `exists_edge_crossing_aux`.**

**Key insight (discovered during formalization)**: `walk_from_crossing` as previously stated
is **FALSE**: for f = x₁x₂y₃² - x₁x₃y₂y₃ ∈ J_{P₃}, LM has crossing at (1,3) but any
walk from 1 to 3 in P₃ goes through vertex 2 ∈ (1,3), violating the hVtx condition.

**Current approach**: Prove `exists_edge_crossing_aux`:
for any nonzero f ∈ J_G, ∃ ADJACENT i < j with d(inl i) ≥ 1 and d(inr j) ≥ 1.
Then use trivial admissible path [i,j] → groebnerElement degree = inl(i)+inr(j) ≤ LM(f).
`exists_groebnerElement_degree_le` follows trivially; Buchberger+`isRemainder_of_mem_ideal`
give `theorem_2_1_groebner`.

**Mathematical proof of `exists_edge_crossing_aux`**:
Write f = Σ q_e * g_e. coeff(f, LM(f)) ≠ 0. Each edge e={i,j} (i<j) contributes:
  A_e = coeff(q_e, d-inl(i)-inr(j))  [from x_i*y_j term → EDGE CROSSING if nonzero]
  B_e = coeff(q_e, d-inl(j)-inr(i))  [from -x_j*y_i term]
If all A_e=0: coeff(f,d) = -ΣB_e ≠ 0. But B_e≠0 for edge e={i,j} forces
LM(q_e*g_e) = LM(q_e)+inl(i)+inr(j) >_lex d (since inl(i)>inl(j), inr(j)>inr(i) in lex).
For LM(f)=d, these >d terms must cancel between edges, recurse... Eventually find A_e ≠ 0.

**Sub-tasks:**
- [x] **R1. No-monomial lemma**: `binomialEdgeIdeal_no_monomial` — PROVED
- [x] **Assembly**: `exists_groebnerElement_degree_le` — compiled, uses `exists_edge_crossing_aux`
- [ ] **R2-R3. Edge crossing**: `exists_edge_crossing_aux` — one sorry remaining

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

1. **Phase 8E: `theorem_2_1_groebner`** — Follow Rauh's approach (see §8E R0–R4 above).
   Start by reading Rauh arxiv:1210.7960 §2, mapping out steps, then implementing.
   Do NOT delete existing sorry'd code; set it aside and build fresh alongside it.
2. **Phase 6: `corollary_3_9`** — cut-vertex characterization of minimal primes
3. **Phase 7: `theorem_3_2` ⊇** — radical ideal argument
4. **Phase 7: corollaries** — once Thm 3.2 proved

---

## Why These Sorries Are Hard

### "Medium" (genuine Lean work, unblocked)
- `theorem_2_1_groebner` (8E): Via Rauh's approach — unknown difficulty until mapped out
- `corollary_3_9` (6): Cut-vertex characterization of minimal primes
- `corollary_3_3_lower_bound` (7): Follows from chain of primes

### "Hard" (genuine mathematical content + significant Lean plumbing)
- `theorem_2_1_groebner` (8E): Via Herzog et al. S-pair approach — τ-path construction is very hard;
  ABANDONED in favor of Rauh. Previous attempts left in file for reference (do not delete yet).
- `theorem_3_2` ⊇ (7): Radical ideal theory
- `prop_3_6` (5): J_G prime ↔ each component complete

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
| GroebnerBasis.lean | 2 (exists_edge_crossing_aux, corollary_2_2) |
| PrimeIdeals.lean | 2 (lemma_3_1, prop_3_6) — **isPrime PROVED** |
| MinimalPrimes.lean | 1 (corollary_3_9 ← only; → proved) |
| PrimeDecomposition.lean | 7 (thm3_2 ⊇, minPrimesChar, cor3_3 ×2, cor3_4, cor3_7 ×2) |
| ClosedGraphs.lean | 0 (**Theorem 1.1 FULLY PROVED**) |
| CohenMacaulay.lean | 4 (def + 3 thms, all deferred) |
| **Total** | **17** (walk_from_crossing false → replaced by exists_edge_crossing_aux) |

---

## Notes
- `groebner_implies_closed`: PROVED (ClosedGraphs.lean)
- `closed_implies_groebner`: PROVED (ClosedGraphs.lean) — 4-case Buchberger analysis
- `isGroebnerBasis_iff_sPolynomial_isRemainder`: FULLY PROVED (GroebnerAPI.lean)
- `primeComponent_isPrime`: PROVED (PrimeIdeals.lean) — ring map φ with ker(φ)=P_S(G)
- `theorem_3_2` (⊆): proved inline via `binomialEdgeIdeal_le_primeComponent`
- `theorem_2_1_leading`: NOW PROVED (follows from theorem_2_1_groebner)
- `idealHeight` uses `Ideal.primeHeight` from Mathlib
- ⚠ Herzog et al. S-pair proof of Thm 2.1 is INCOMPLETE in BEI.tex; coprime "regular sequence" claim is WRONG
- ⭐ Prefer Rauh's approach (arxiv:1210.7960) for Theorem 2.1 — inductive, cleaner
- Previous S-pair attempt code in GroebnerBasis.lean (~lines 300–650): do NOT delete, but set aside

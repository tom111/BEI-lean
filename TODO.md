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

### 8E. `theorem_2_1_groebner` — Buchberger for admissible paths (GroebnerBasis.lean)

**Overall structure**: Apply `isGroebnerBasis_iff_sPolynomial_isRemainder`, then for each pair
of basis elements `eₖ = pathMonomialₖ * fij(iₖ,jₖ)`, show S(e₁,e₂) reduces to 0.

**Key factorization** (all cases): By `sPolynomial_monomial_mul` + `pathMonomial_eq_monomial'`:
`S(e₁, e₂) = monomial D 1 * S(fij₁, fij₂)` where
`D = (d₁ + deg fij₁) ⊔ (d₂ + deg fij₂) - deg fij₁ ⊔ deg fij₂`

⚠ **WARNING**: Paper's "regular sequence" claim for coprime case is WRONG.
The general statement "if in<(f),in<(g) form regular sequence then S(uf,vg) reduces to 0"
is FALSE. Handle all cases via direct case-by-case analysis instead.

**Case 0 — Same edge** (i₁=i₂, j₁=j₂): S = 0 by `sPolynomial_self`
- [x] PROVED (commit ba8d7a0)

**Case A — Coprime** (i₁ ≠ i₂ AND j₁ ≠ j₂):
Leading monomials of fij₁, fij₂ have disjoint variable supports.
This includes disjoint endpoints, cross-match i₁=j₂, and cross-match j₁=i₂.

Strategy: Express S(e₁,e₂) = Q₁*e₁ - Q₂*e₂ via factored form, then `isRemainder_sub_mul`.

- [ ] **A1. Make `coprime_degrees_ne` and `degree_bounds_of_sub` accessible**
  Currently `private` in ClosedGraphs.lean. Either make `protected`/public, or re-prove locally.

- [ ] **A2. Prove `d_le_D_coprime`**: When fij degrees have disjoint supports,
  `d₁ ≤ D` and `d₂ ≤ D` (pointwise). Key Finsupp calculation using disjointness.

- [ ] **A3. Factor S-polynomial into groebnerElement combination**:
  `S(e₁,e₂) = monomial(D-d₁) 1 * x_{j₂} * y_{i₂} * e₁ - monomial(D-d₂) 1 * x_{j₁} * y_{i₁} * e₂`
  Uses `sPolynomial_monomial_mul` + `sPolynomial_fij_coprime` + A2.

- [ ] **A4. Verify degree bounds**:
  `deg(Q₁*e₁) = D + deg(x_{j₂}*y_{i₂}*fij₁) ≤ D + deg(S(fij₁,fij₂)) = deg(S(e₁,e₂))`
  Uses `coprime_degrees_ne` + `degree_bounds_of_sub` from A1.

- [ ] **A5. Conclude**: Apply `isRemainder_sub_mul` with the decomposition from A3 and bounds from A4.

**Case B — Shared first endpoint** (i₁ = i₂, j₁ ≠ j₂):
`S(fij(i,j₁), fij(i,j₂)) = -y_i * fij(j₁,j₂)` by `sPolynomial_fij_shared_first`.
So `S(e₁,e₂) = -monomial D 1 * y_i * fij(j₁,j₂)`.
Need to express `fij(j₁,j₂)` as combination of groebnerBasisSet elements.
WITHOUT closedness, there's no direct edge j₁-j₂ in general.

Strategy: τ-path construction from the paper (Section 2.1, lines 578–695).

- [ ] **B1. τ-path construction**: Given admissible paths π₁: i→j₁ and π₂: i→j₂,
  construct path τ: j₁→j₂ by reversing tail of π₁ and concatenating with tail of π₂.
  Find the last shared vertex i_a = i'_b where the paths diverge.
  τ = [j₁=i_r, i_{r-1}, ..., i_{a+1}, i_a=i'_b, i'_{b+1}, ..., i'_{s-1}, j₂=i'_s]

- [ ] **B2. Turning points t(c)**: Define the sequence 0 = t(0) < t(1) < ... < t(q) = t
  where j_{t(c)} are the successive minima of τ-vertices that exceed j₁.
  Prove: j₁ = j_{t(0)} < j_{t(1)} < ... < j_{t(q)} = j₂.

- [ ] **B3. Admissibility of sub-paths**: Show each τ_c (from j_{t(c-1)} to j_{t(c)})
  is an admissible path in G. Requires checking all 7 conditions of `IsAdmissiblePath`:
  ordering, head/last, nodup, interior vertex condition, chain adjacency, minimality.

- [ ] **B4. Telescoping identity**: Prove the ring identity
  `w * fij(j₁,j₂) = Σ_{c=1}^{q} v_{τ_c} * u_{τ_c} * fij(j_{t(c-1)}, j_{t(c)})`
  where w = y_i * lcm(pathMonomial₁, pathMonomial₂) and v_{τ_c} are explicit monomials.
  This is a telescoping sum: (x_j * y_ℓ)/(x_{j_c}) terms that cancel pairwise.

- [ ] **B5. Degree chain ordering**: Prove the chain of inequalities
  `deg(v₁*u_{τ₁}*fij₁) > deg(v₂*u_{τ₂}*fij₂) > ... > deg(v_q*u_{τ_q}*fij_q)`
  showing each term's degree is strictly decreasing (so the sum is a standard expression).

- [ ] **B6. Conclude IsRemainder**: Combine B4 identity + B5 degree bounds + B3 membership
  to construct the `IsRemainder` witness. The remainder is 0 since all terms are accounted for.

**Case C — Shared last endpoint** (j₁ = j₂, i₁ ≠ i₂):
Symmetric to Case B. `S(fij(i₁,j), fij(i₂,j)) = x_j * fij(i₁,i₂)`.

- [ ] **C1–C6**: Mirror of B1–B6 with reversed roles of x and y, first and last endpoints.
  Can potentially share infrastructure with Case B via a symmetry argument.

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

1. **Phase 8E Case A: coprime** — most tractable; infrastructure exists from Thm 1.1
2. **Phase 8E Cases B+C: shared endpoint** — hardest; τ-path construction
3. **Phase 6: `corollary_3_9`** — cut-vertex characterization of minimal primes
4. **Phase 7: `theorem_3_2` ⊇** — radical ideal argument
5. **Phase 7: corollaries** — once Thm 3.2 proved

---

## Why These Sorries Are Hard

### "Medium" (genuine Lean work, unblocked)
- `theorem_2_1_groebner` Case A — coprime (8E): Pure algebra; infrastructure exists from Thm 1.1
- `corollary_3_9` (6): Cut-vertex characterization of minimal primes
- `corollary_3_3_lower_bound` (7): Follows from chain of primes

### "Hard" (genuine mathematical content + significant Lean plumbing)
- `theorem_2_1_groebner` Cases B+C — shared endpoint (8E): τ-path construction, admissibility
  proofs, telescoping identity, degree chains. ~500-800 lines estimated.
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
| GroebnerBasis.lean | 2 (theorem_2_1_groebner 1 sorry — Cases A/B/C; corollary_2_2 deferred) |
| PrimeIdeals.lean | 2 (lemma_3_1, prop_3_6) — **isPrime PROVED** |
| MinimalPrimes.lean | 1 (corollary_3_9 ← only; → proved) |
| PrimeDecomposition.lean | 7 (thm3_2 ⊇, minPrimesChar, cor3_3 ×2, cor3_4, cor3_7 ×2) |
| ClosedGraphs.lean | 0 (**Theorem 1.1 FULLY PROVED**) |
| CohenMacaulay.lean | 4 (def + 3 thms, all deferred) |
| **Total** | **16** (same-edge case of theorem_2_1_groebner now proved in else branch) |

---

## Notes
- `groebner_implies_closed`: PROVED (ClosedGraphs.lean)
- `closed_implies_groebner`: PROVED (ClosedGraphs.lean) — 4-case Buchberger analysis
- `isGroebnerBasis_iff_sPolynomial_isRemainder`: FULLY PROVED (GroebnerAPI.lean)
- `primeComponent_isPrime`: PROVED (PrimeIdeals.lean) — ring map φ with ker(φ)=P_S(G)
- `theorem_3_2` (⊆): proved inline via `binomialEdgeIdeal_le_primeComponent`
- `theorem_2_1_leading`: NOW PROVED (follows from theorem_2_1_groebner)
- `idealHeight` uses `Ideal.primeHeight` from Mathlib
- ⚠ Paper's regular sequence claim (coprime case of Thm 2.1) is WRONG — use case-by-case instead
- `coprime_degrees_ne` and `degree_bounds_of_sub` are `private` in ClosedGraphs.lean — need to
  make accessible for reuse in GroebnerBasis.lean (Case A of theorem_2_1_groebner)

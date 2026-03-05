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

### 4A. Fix errors in `subwalk_props` (known fixes, mechanical)
These are compilation errors in existing proof code, grouped by root cause:

**Group 1 — nil-case simp failures** (lines 174, 176, 248, 250, 285, 287):
- Root cause: after `cases hπ_form : π`, `hπHead` still mentions abstract `π`
- Fix: change `simp at hπHead` → `simp [hπ_form] at hπHead` (add `hπ_form` to simp set)

**Group 2 — opaque let-variables β/α'** (lines 219, 221, 270):
- Root cause: after `intro k β α'`, `β = π.drop k` is a local def; simp can't unfold it
- Fix: prepend `change (π.drop k).xxx = ...` or `change (π.take (k+1)).reverse.xxx = ...`

**Group 3 — `β.length` opaque in omega** (line 233):
- Root cause: omega can't see `β.length = π.length - k`
- Fix: introduce `have hβlen : β.length = π.length - k := List.length_drop k π`

**Group 4 — `getElem_inj_iff` used as function** (line 241):
- Root cause: `hπND.getElem_inj_iff` returns an `Iff`, not a function; can't apply `(by omega)`
- Fix: provide `i j : Fin π.length` explicitly, or restructure using `List.Nodup.getElem_inj`

**Group 5 — invalid `▸` notation** (lines 256, 293):
- Root cause: `hπtail_last ▸ hv_ne_j` rewrites in wrong direction
- Fix: `hπtail_last.symm ▸ hv_ne_j` or `fun heq => hv_ne_j (heq.trans hπtail_last)`

### 4B. Fix type mismatch in `subwalk_props_above` (line 312 + 349 + call site 630)
- Root cause: parameter `hi_lt_v₀ : i < v₀` should be `hj_lt_v₀ : j < v₀`; we're in Case B
  where j < v₀ is the invariant, not i < v₀
- Fix:
  1. Change signature line 312: `hi_lt_v₀ : i < v₀` → `hj_lt_v₀ : j < v₀`
  2. Remove line 349 (`have hj_lt_v₀ := ...`; now a hypothesis)
  3. Line 346: replace `ne_of_gt hi_lt_v₀` with `ne_of_gt (hij.trans hj_lt_v₀)`
  4. Call site line 630: replace `ha_lt_v₀` with `hv₀_gt_j`

Note: `subwalk_props_above` has the SAME Group 1-5 errors; apply same fixes to lines 386-387, 397
(β/α' opacity), and any nil-case pattern matches.

### 4C. `chain'_reverse` — done (only deprecation warnings remain)

### 4D. `internalVertices` partition lemmas (needed for pathMonomial_split)
These are sub-lemmas to break up the monomial factorization proof:
- [ ] `internalVertices_drop` — for k ∈ (0, π.length-1):
  `internalVertices (π.drop k) = [π[k]] ++ internalVertices π from position k+1 to end, minus last`
  More precisely: `internalVertices (π.drop k) ⊆ {π[k]} ∪ { v ∈ internalVertices π | ... }`
- [ ] `internalVertices_take_reverse` — `internalVertices ((π.take (k+1)).reverse) = ...`
- [ ] `internalVertices_partition` — if k = idxOf v₀, then the internal vertices of π split as:
  `(internalVertices π).toFinset = {v₀} ∪ (internalVertices β).toFinset ∪ (internalVertices α').toFinset`
  (disjoint union, where β = π.drop k, α' = (π.take k+1).reverse)

### 4E. `pathMonomial_split_below` — monomial factorization (Case A: v₀ < i)
Strategy: once 4D is proved, this reduces to:
- Partition of x-products: `{v ∈ ints(π) | v > j} = {v ∈ ints(β) | v > j}` (since ints(α')
  only has vertices with v < i < j or v > i but v ∈ π, and v₀ < i < j so v₀ ∉ x-part)
- Partition of y-products: `{v ∈ ints(π) | v < i} = {v₀} ∪ {v ∈ ints(α') | v < v₀} ∪ {v ∈ ints(β) | v < v₀}`
Approach: Use `Finset.prod_union` + `internalVertices_partition` to split the product

### 4F. `pathMonomial_split_above` — monomial factorization (Case B: v₀ > j)
Symmetric to 4E with x/y roles swapped.

---

## Phase 5 — Prime Ideal Properties

### 5A. `primeComponent_isPrime` — broken into sub-steps
The paper strategy: K[x,y]/P_S(G) injects into `⊗_{component C} K[t_v : v ∈ C, s]` via xᵢ ↦ tᵢ, yᵢ ↦ s·tᵢ.

- [ ] **5A-i** Define the ring map `φ : MvPolynomial (BinomialEdgeVars V) K → Target` where
  `Target` is a product of polynomial rings (one per connected component of G[V\S])
- [ ] **5A-ii** Show φ kills each generator of P_S(G):
  - xᵢ ↦ 0 for i ∈ S (direct)
  - yᵢ ↦ 0 for i ∈ S (direct)
  - xⱼ·yₖ - xₖ·yⱼ ↦ tⱼ·s·tₖ - tₖ·s·tⱼ = 0 for j, k same component (direct)
- [ ] **5A-iii** Show Target is an integral domain (product of domains via connectedness)
- [ ] **5A-iv** Conclude: P_S(G) = ker φ contains P_S(G) and maps to domain → P_S(G) is prime

Note: This approach requires choosing the "Target" ring carefully. A simpler choice:
map to `MvPolynomial V K × MvPolynomial Unit K` by xᵢ ↦ (Xᵢ, 0), yᵢ ↦ (0, 1)... but this
doesn't quite work. The paper's actual approach uses a "normalization" map to a specific ring.
Alternatively, show P_S(G) is prime by induction on |S| + number of components.

- [ ] `lemma_3_1` — height formula (very hard; needs chain of prime ideals of known length;
  likely requires Phase 8 Gröbner basis for upper bound)
- [ ] `prop_3_6` — J_G prime ↔ each component complete (needs theorem_3_2 or direct argument)

---

## Phase 6 — Minimal Primes

- [x] `prop_3_8_var_not_mem` — **key sub-lemma**: if i ∉ S, then X(inl i) ∉ primeComponent G S
  Proved: eval at σ: x_i ↦ 1, everything else ↦ 0; generators map to 0; contradiction.
- [x] `prop_3_8` (→ direction): use `prop_3_8_var_not_mem` to show T ⊆ S
  Proved: X(inl a) ∈ P_T ≤ P_S but X(inl a) ∉ P_S — contradiction.
- [ ] `prop_3_8` (→ direction): component preservation from containment
- [ ] `corollary_3_9` — depends on both directions of prop_3_8

---

## Phase 7 — Prime Decomposition

- [ ] `theorem_3_2` (⊆): J_G ⊆ ⋂ P_S(G) — **already follows** from `binomialEdgeIdeal_le_primeComponent`
- [ ] `theorem_3_2` (⊇): ⋂ P_S(G) ⊆ J_G — hard; needs J_G is radical + Nullstellensatz-type arg
- [ ] `corollary_3_3_lower_bound` — dim ≥ |V| + c(G) via S = ∅ chain (relatively accessible)
- [ ] `corollary_3_7` — cycle: n=3 ↔ J_G prime (computational; small graph case)
- [ ] `minimalPrimes_characterization`, `corollary_3_3`, `corollary_3_4` — depend on thm_3_2

---

## Phase 8 — Gröbner Basis

### 8A. Squarefreeness
- [x] `groebnerElement_leadingMonomial_squarefree` — each variable appears ≤ 1 time
  (DONE: proved via `prod_X_image_squarefree` helpers)

### 8B. Gröbner basis API (new: BEI/GroebnerAPI.lean)
Source: WuProver/groebner_proj (Apache 2.0), adapted for Mathlib v4.28.0.
The `sPolynomial` is already in Mathlib; we ported the missing pieces.
- [x] `MonomialOrder.IsRemainder` — polynomial division remainder predicate
  (defined using Mathlib's `div_set` output structure)
- [x] `MonomialOrder.IsGroebnerBasis` — standard algebraic definition:
  `G ⊆ I ∧ span(lt(I)) = span(lt(G))`
- [x] `MonomialOrder.exists_isRemainder` — existence from Mathlib's `div_set`
- [ ] `MonomialOrder.isGroebnerBasis_iff_sPolynomial_isRemainder` — **Buchberger criterion**
  Statement: `IsGroebnerBasis G (span G) ↔ ∀ g₁ g₂ ∈ G, IsRemainder S(g₁,g₂) G 0`
  Proof: port from WuProver/groebner_proj `Groebner.lean`
  (needs `IsRemainder` existence + uniqueness-type arguments)

### 8C. Leading coefficient lemma
- [ ] `groebnerElement_leadingCoeff` — `leadingCoeff (u_π · f_{ij}) = 1`
  Proof: `leadingCoeff(pathMonomial) = 1` (product of monic variables) and
  `leadingCoeff(fij) = 1` (proved as `fij_leadingCoeff`); use `leadingCoeff_mul`.

### 8D. S-polynomial reductions (Buchberger case analysis)
- [ ] `theorem_2_1_groebner` — groebnerBasisSet is a Gröbner basis via Buchberger
  Strategy: rw Buchberger criterion, then case analysis on pairs of basis elements.
  Cases for `S(u_{π₁} f_{i₁j₁}, u_{π₂} f_{i₂j₂})`:
  1. **Coprime** — leading monomials of `e₁` and `e₂` have disjoint variable sets:
     S-polynomial reduces trivially to 0 (general Buchberger property)
  2. **Shared first endpoint** `i₁ = i₂`: use admissible path concatenation
  3. **Shared last endpoint** `j₁ = j₂`: symmetric
  4. **Cross cases** (`i₁ = j₂` or `j₁ = i₂`): use path reversal + closedness

### 8E. Radical (standalone after 8A)
- [ ] `corollary_2_2` — J_G is radical; squarefree initial ideal → radical
  (search Mathlib for `MvPolynomial.radical_of_squarefreeInitial` or similar)

---

## Phase 9 — Theorem 1.1 (blocked on Phase 8B+8D)
- [ ] `theorem_1_1`, `closed_implies_groebner`, `groebner_implies_closed`
  All now use the real `MonomialOrder.IsGroebnerBasis` definition (not a stub).

## Phase 10 — Cohen-Macaulay (deferred; not in Mathlib)
- [!] All deferred until `IsCohenMacaulay` is in Mathlib

---

## Priority Order (what to work on next)

1. ~~Phase 4A+4B~~ DONE — compilation errors fixed
2. ~~Phase 6 `prop_3_8_var_not_mem`~~ DONE — proved via eval argument
3. ~~Phase 8A~~ DONE — `groebnerElement_leadingMonomial_squarefree`
4. ~~Phase 8B API~~ DONE — `IsRemainder`, `IsGroebnerBasis`, `exists_isRemainder`
5. **Phase 8B Buchberger** — `isGroebnerBasis_iff_sPolynomial_isRemainder` (port from groebner_proj)
6. **Phase 8C** — `groebnerElement_leadingCoeff` (mechanical, uses `fij_leadingCoeff`)
7. **Phase 8D** — S-polynomial case analysis (long but each case manageable)
8. **Phase 9** — `theorem_1_1` (once 8B+8D done)
9. **Phase 5A** — `primeComponent_isPrime` (needed for prime decomposition)
10. **Phase 7** — `theorem_3_2` ⊇ direction + corollaries

---

## Why These Sorries Are Hard

### "Easy/Medium" (now unblocked)
- `groebnerElement_leadingCoeff` (8C): Mechanical, use `leadingCoeff_mul` + `fij_leadingCoeff`
- `corollary_3_3_lower_bound` (7): Follows from chain of primes

### "Medium" (genuine Lean work)
- Buchberger criterion proof (8B): Port from WuProver/groebner_proj
- S-polynomial coprime case (8D): General Buchberger property, Lean API work
- S-polynomial endpoint cases (8D): Algebraic path manipulation

### "Hard" (genuine mathematical content)
- `primeComponent_isPrime` (5A): Needs explicit ring map construction in Lean
- `theorem_3_2` ⊇ (7): Radical ideal theory
- `theorem_1_1` backward direction (9): Non-reduction argument

### "Very Hard / Deferred" (depends on missing Mathlib)
- `lemma_3_1`: Height formula (needs Gröbner basis + dimension theory)
- `theorem_1_1` full proof: Requires complete Buchberger
- Cohen-Macaulay: Deferred until `IsCohenMacaulay` in Mathlib

---

## Sorry Count by File (current)
| File | Sorries |
|------|---------|
| GraphProperties.lean | 0 |
| AdmissiblePaths.lean | 0 |
| MonomialOrder.lean | 0 |
| GroebnerAPI.lean | 1 (Buchberger criterion) |
| GroebnerBasis.lean | 4 (groebnerElement_leadingCoeff, theorem_2_1_groebner, _leading, _reduced; cor2_2) |
| PrimeIdeals.lean | 3 (isPrime, lemma_3_1, prop_3_6) |
| MinimalPrimes.lean | 2 (prop_3_8 component preservation, corollary_3_9) |
| PrimeDecomposition.lean | 7 (thm3_2 ⊇, minPrimesChar, cor3_3 ×2, cor3_4, cor3_7 ×2) |
| ClosedGraphs.lean | 3 (thm1_1, closed→GB, GB→closed) |
| CohenMacaulay.lean | 4 (def + 3 thms, all deferred) |
| **Total** | **24** |

---

## Notes
- `chain'_reverse`: done (only deprecation warnings remain; `[x]` above was premature in old list)
- `prop_3_8` → direction: `prop_3_8_var_not_mem` via eval is the cleanest unblocking step
- `theorem_3_2` (⊆): already proved by `binomialEdgeIdeal_le_primeComponent`!
- `IsGroebnerBasis'` uses `True` for S-polynomial condition; not mathematically valid
- `idealHeight` uses `Ideal.height` from `Mathlib.RingTheory.Ideal.Height`

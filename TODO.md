# BEI Lean Formalization — Task List

## Status Legend
- `[ ]` pending
- `[~]` in progress
- `[x]` done
- `[!]` blocked / deferred

---

## Phase 1 — Fix Compilation Blocker
- [x] `MonomialOrder.lean:50` — Add `import Mathlib.Data.Finite.Sum` and replace `Sum.instFinite` with `inferInstance`

## Phase 2 — MonomialOrder Leading Term Proofs
- [x] Root cause fixed: changed `abbrev BinomialEdgeVars` → opaque `def BinomialEdgeVars` to eliminate `Sum.instLESum`/`Sum.instLTSum` instance diamond with `Finsupp.Lex`
- [x] `Groebner.lean` rewritten: `LinearOrder (BinomialEdgeVars V)` now has explicit `lt` field so instances are unambiguous
- [x] `binomialEdgeMonomialOrder` — defined via `MonomialOrder.lex` (correct term order: x_1 > x_2 > ... > x_n > y_1 > ... > y_n, matching paper)
- [x] `fij_degree` — leading monomial of `f_{ij}` is `x_i · y_j`
- [x] `fij_leadingCoeff` — leading coefficient is 1
- [x] `fij_leadingCoeff_isUnit` — 1 is a unit

## Phase 3 — Graph Theory Properties
- [x] `prop_1_4` — both directions proved: (←) length-2 walk gives contradiction; (→) strong induction on walk length, using closedness to shortcut non-directed first steps
- [~] `cor_1_3` — closed + bipartite → path graph:
  - [x] `noTriangle_of_bipartite` helper lemma (bipartite coloring + triangle → False)
  - [x] degree bound: `∀ v, G.degree v ≤ 2` proved via pigeonhole + IsClosedGraph + noTriangle
  - [ ] acyclicity `G.IsAcyclic` — strategy: bipartite → all cycles even → even cycle ≥ 4 → IsChordal gives chord → same-color chord violates bipartite (base n=4) or sub-cycles contradict IH (n>4 by strong induction); formalizing chord-splitting in Walk API is complex

## Phase 4 — Admissible Paths Membership
- [~] `groebnerElement_mem` — `u_π · f_{ij} ∈ binomialEdgeIdeal G`
  - [x] Base cases: [] (trivial), [a] (contradicts i < j), [a, b] (edge case, proven)
  - [ ] Inductive step (`a :: b :: c :: rest`): strategy is MAX-split — find v₀ = max{internal v < i}, split walk at v₀ into prefix [i,…,v₀] and suffix [v₀,…,j]; show suffix satisfies conditions (max ensures other below-verts are < v₀); use identity y_{v₀}·f_{ij} = y_i·f_{v₀j} − y_j·f_{v₀i}; apply IH to suffix (v₀<j) and rev-prefix (v₀<i); symmetric case for min-above-split

## Phase 5 — Prime Ideal Properties
- [x] `primeComponent_empty_connected` — P_∅(G) = J_{K_V} when G connected
- [x] `binomialEdgeIdeal_le_primeComponent` — J_G ⊆ P_S(G) for all S (proved by case split on edge endpoint membership in S)
- [ ] `primeComponent_isPrime` — P_S(G) is prime; strategy: show quotient is domain via injecting into K[tᵢ:i∉S, s] by xⱼ↦tⱼ, yⱼ↦s·tⱼ
- [ ] `lemma_3_1` — height formula: height(P_S(G)) = |S| + (|V| − c(S))
- [ ] `prop_3_6` — J_G prime ↔ each connected component is complete

## Phase 6 — Minimal Primes
- [x] `minimalPrimes_finite` — J_G has finitely many minimal primes (Noetherian ring argument)
- [x] `prop_3_8` (← direction) — T ⊆ S and component-preservation → P_T ≤ P_S; proved by generators case split
- [ ] `prop_3_8` (→ direction) — P_T ≤ P_S implies T ≤ S and component-preservation; blocked: needs X(inl i) ∉ P_S when i ∉ S (requires Gröbner basis or primeness argument)
- [ ] `corollary_3_9` — P_S(G) minimal prime ↔ S = ∅ or every i ∈ S is a cut-vertex relative to S

## Phase 7 — Prime Decomposition
- [ ] `theorem_3_2` — J_G = ⋂ P_S(G); easy direction (⊆) follows from `binomialEdgeIdeal_le_primeComponent`; hard direction needs radical argument
- [ ] `minimalPrimes_characterization` — minimal primes of J_G are minimal P_S(G)
- [ ] `corollary_3_3` — dim formula: max_S(|V|−|S|+c(S))
- [ ] `corollary_3_3_lower_bound` — dim ≥ |V| + c(G) (S = ∅ case)
- [ ] `corollary_3_4` — CM implies dim = |V| + c(G)
- [ ] `corollary_3_7` — cycle: n=3 ↔ J_G prime
- [ ] `corollary_3_7_CM` — cycle: CM ↔ J_G prime

## Phase 8 — Gröbner Basis (hardest)
- [ ] `theorem_2_1` — Gröbner basis equality (requires Phase 4 + Buchberger criterion)
- [ ] `theorem_2_1_leading` — leading term divisibility
- [ ] `theorem_2_1_reduced` — reducedness
- [ ] `corollary_2_2` — J_G is radical (follows from squarefree initial ideal)
- [ ] `groebnerElement_leadingMonomial_squarefree` — squarefreeness of leading monomials

## Phase 9 — Theorem 1.1
- [ ] `theorem_1_1` — Gröbner basis ↔ closed graph (IsGroebnerBasis' currently has True placeholder for S-poly condition; needs proper formulation)
- [ ] `closed_implies_groebner` — G closed → generators form Gröbner basis
- [ ] `groebner_implies_closed` — Gröbner basis → G closed

## Phase 10 — Cohen-Macaulay (deferred)
- [!] `IsCohenMacaulay` — placeholder `sorry`-def; not yet in Mathlib
- [!] `prop_1_6`, `complete_is_CM`, `path_is_CM` — all blocked on `IsCohenMacaulay`

---

## Sorry Count by File (as of this session)
| File | Sorries |
|------|---------|
| GraphProperties.lean | 1 (cor_1_3 acyclicity) |
| AdmissiblePaths.lean | 1 (groebnerElem_mem_aux inductive step) |
| PrimeIdeals.lean | 3 (isPrime, lemma_3_1, prop_3_6) |
| MinimalPrimes.lean | 3 (prop_3_8 → ×2, corollary_3_9) |
| GroebnerBasis.lean | 5 (thm2_1 ×3, cor2_2, squarefree) |
| PrimeDecomposition.lean | 7 (thm3_2, minPrimesChar, cor3_3 ×2, cor3_4, cor3_7 ×2) |
| ClosedGraphs.lean | 3 (thm1_1, closed→GB, GB→closed) |
| CohenMacaulay.lean | 4 (def + 3 thms, all deferred) |
| **Total** | **27** |

---

## Notes
- `IsGroebnerBasis'` uses `True` as S-polynomial placeholder; `closed_implies_groebner` is trivially provable from it but not mathematically meaningful
- `prop_3_8` → direction needs that X(inl i) ∉ P_S when i ∉ S; this is hard without the Gröbner basis (linear independence argument)
- `idealHeight` uses `Ideal.height` from Mathlib (`Mathlib.RingTheory.Ideal.Height`)
- Gröbner basis machinery: `Mathlib.RingTheory.MvPolynomial.Groebner` imported but S-polynomial API not yet used

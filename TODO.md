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
- [~] `prop_1_4` — statement fixed (removed G.Adj precondition per paper); (←) proved: not-directed walk of length 2 via shared neighbor gives contradiction; (→) still sorry
- [~] `cor_1_3` — statement fixed (was wrong); now: bipartite ↔ `G.IsAcyclic ∧ ∀ v, G.degree v ≤ 2` (forest with max degree 2 = disjoint union of paths); proof still sorry

## Phase 4 — Admissible Paths Membership
- [ ] `groebnerElement_mem` — `u_π · f_{ij} ∈ binomialEdgeIdeal G`

## Phase 5 — Prime Ideal Properties
- [ ] `primeComponent_isPrime` — `P_S(G)` is a prime ideal
- [ ] `idealHeight` — replace sorry-def with actual Mathlib `Ideal.primeHeight`
- [ ] `lemma_3_1` — height formula `|S| + (|V| - c(S))`
- [ ] `prop_3_6` — `J_G` prime ↔ each component is complete

## Phase 6 — Minimal Primes
- [ ] `prop_3_8` (→ direction) — `P_T ≤ P_S` implies T ≤ S and component refinement
- [ ] `corollary_3_9` — minimal prime characterization

## Phase 7 — Prime Decomposition
- [ ] `theorem_3_2` — `J_G = ⋂ P_S(G)`
- [ ] Corollaries 3.3–3.7

## Phase 8 — Gröbner Basis (hardest)
- [ ] `theorem_2_1` — Gröbner basis equality
- [ ] `theorem_2_1_leading` — leading term divisibility
- [ ] `theorem_2_1_reduced` — reducedness
- [ ] `corollary_2_2` — `J_G` is radical
- [ ] `groebnerElement_leadingMonomial_squarefree`

## Phase 9 — Theorem 1.1
- [ ] `theorem_1_1` — Gröbner basis ↔ closed graph
- [ ] `closed_implies_groebner`
- [ ] `groebner_implies_closed`

## Phase 10 — Cohen-Macaulay (deferred)
- [!] `IsCohenMacaulay` placeholder — check if Mathlib has CM definitions

---

## Notes
- `prop_1_4` is currently stated as a tautology (`True`); needs proper statement from paper
- `cor_1_3` statement does not match paper (degree ≤ 2 condition is wrong); needs revision
- `idealHeight` is a sorry-def; Mathlib uses `Ideal.primeHeight`
- Gröbner basis machinery: check `Mathlib.RingTheory.MvPolynomial.Groebner` for S-polynomial API

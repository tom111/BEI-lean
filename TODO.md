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
| **§1 Prop 1.6** (CM sufficient condition) | CohenMacaulay.lean | ❌ deferred (needs `IsCohenMacaulay`) |
| **§2 Thm 2.1** (reduced GB = admissible paths) | GroebnerBasis.lean | ✅ proved |
| **§2 Cor 2.2** (J_G radical) | GroebnerBasis.lean | ❌ blocked (see below) |
| **§3 Lem 3.1** (height P_S = \|S\| + n − c(S)) | PrimeIdeals.lean | ❌ sorry |
| **§3 Thm 3.2** (J_G = ⋂ P_S) | PrimeDecomposition.lean | ⊆ proved, ⊇ sorry |
| **§3 Cor 3.3** (dim S/J_G formula) | PrimeDecomposition.lean | ❌ sorry (needs Thm 3.2) |
| **§3 Cor 3.4** (CM → dim = n+c) | PrimeDecomposition.lean | ❌ sorry (needs Thm 3.2) |
| **§3 Prop 3.6** (J_G prime ↔ components complete) | PrimeIdeals.lean | ❌ sorry |
| **§3 Cor 3.7** (cycle: n=3 ↔ prime ↔ CM) | PrimeDecomposition.lean | ❌ sorry (needs Thm 3.2) |
| **§3 Prop 3.8** (P_T ⊆ P_S characterization) | MinimalPrimes.lean | ✅ proved |
| **§3 Cor 3.9** (minimal primes = cut-points) | MinimalPrimes.lean | → proved, ← sorry |
| **§4** (CI-ideal applications) | — | ❌ not formalized (not planned) |

---

## Completed Phases

### Phase 1–4: Foundations ✅
- MonomialOrder, GraphProperties, AdmissiblePaths, GroebnerAPI all proved.

### Phase 8: Gröbner Basis ✅ (except Cor 2.2)
- Theorem 1.1 (closed ↔ quadratic GB): **proved**
- Theorem 2.1 (reduced GB): **proved** (Buchberger criterion, 4-case S-polynomial analysis, mixed-walk lemma)
- Theorem 2.1 reduced: **proved**
- Squarefree leading monomials: **proved**

### Phase 5A: Prime Component ✅
- `primeComponent_isPrime`: **proved**

### Phase 6: Minimal Primes (partial)
- Prop 3.8 (P_T ⊆ P_S characterization): **proved**
- Cor 3.9 (→): **proved**

---

## Remaining Work (prioritized)

### Priority 1: Corollary 2.2 — J_G is radical
**Paper argument:** Thm 2.1 gives a reduced squarefree GB ⇒ in_<(J_G) is squarefree ⇒ J_G radical.
**Blocker:** The implication "squarefree initial ideal ⇒ radical" requires either:
  (a) The Gröbner deformation argument (Lemma 4.4.9 of Bruns-Herzog) — needs graded Noetherian lifting not in Mathlib
  (b) Use Thm 3.2 (J_G = ⋂ primes) to get radical directly — but Thm 3.2 ⊇ uses Cor 2.2 (circular!)
**Possible approach:** Prove the squarefree-initial-implies-radical lemma directly as a standalone result. The key ingredient is: if in_<(I) is squarefree, then S/I has a flat deformation to S/in_<(I) which is reduced. This is standard but nontrivial commutative algebra.
**File:** GroebnerBasis.lean, line ~5286

### Priority 2: Theorem 3.2 ⊇ — ⋂ P_S(G) ⊆ J_G
**Paper argument:** Uses induction on n. Key step: show each minimal prime of J_G is of the form P_S(G).
  - Show x_i ∈ P iff y_i ∈ P (for minimal prime P)
  - Reduce to components, then show P = (variables) + (complete graph ideals)
  - The "f_{ij} ∈ P" step uses x-telescope: x_{i₁} f_{ij} = x_j f_{i,i₁} + x_i f_{i₁,j}, then since x_{i₁} ∉ P and P prime, f_{ij} ∈ P.
**Dependency:** Cor 2.2 (J_G radical) — but can be broken by proving radical independently.
**File:** PrimeDecomposition.lean

### Priority 3: Corollary 3.9 ← — minimal primes characterization (reverse)
**Paper argument:** If c(S\{i}) < c(S) for all i ∈ S, and P_T ⊆ P_S for some proper T ⊂ S, then choosing i ∈ S\T and analyzing connected components of G_{[n]\(S\{i})} gives a contradiction via Prop 3.8.
**Dependency:** Prop 3.8 (done). Thm 3.2 indirectly (to know all minimal primes are P_S).
**File:** MinimalPrimes.lean

### Priority 4: Lemma 3.1 — height(P_S) = |S| + (n − c(S))
**Paper argument:** Direct computation: height = 2|S| + Σ(n_j − 1) = |S| + n − c(S).
**Blocker:** Needs `Ideal.height` or Krull dimension in Mathlib. `krullDim` exists but computing height of specific ideals requires showing chains of primes.
**File:** PrimeIdeals.lean

### Priority 5: Prop 3.6 — J_G prime ↔ components complete
**Paper argument:** If J_G prime, then P_∅ = (J_{G̃₁}, ..., J_{G̃ᵣ}) is the unique minimal prime, so J_G = P_∅, giving G_i = G̃_i.
**Dependency:** Thm 3.2.
**File:** PrimeIdeals.lean

### Priority 6: Remaining corollaries (3.3, 3.4, 3.7)
All depend on Thm 3.2. Straightforward once 3.2 is done.

---

## Deferred (not in scope)

- **§1 Prop 1.6** (CM sufficient condition) — needs `IsCohenMacaulay` in Mathlib
- **§4** (CI-ideal applications) — statistical interpretation, not planned for formalization
- **CohenMacaulay.lean** — 4 sorries, all deferred

---

## Sorry Count by File (2026-03-29)
| File | Sorries | Notes |
|------|---------|-------|
| GroebnerBasis.lean | 1 | Cor 2.2 (blocked) |
| PrimeIdeals.lean | 2 | Lem 3.1, Prop 3.6 |
| MinimalPrimes.lean | 1 | Cor 3.9 ← only |
| PrimeDecomposition.lean | 7 | Thm 3.2 ⊇ + corollaries |
| CohenMacaulay.lean | 4 | all deferred |
| RauhApproach.lean | 2 | archived |
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
- `corollary_2_2`: blocked on squarefree-initial → radical (not in Mathlib)
- Cohen-Macaulay: deferred (IsCohenMacaulay not in Mathlib)
- Section 4 (CI-ideals): not planned for formalization

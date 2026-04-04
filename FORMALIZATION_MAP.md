# Formalization Map: Herzog et al. (2010) vs Lean

This file maps each paper result to its Lean formalization, noting fidelity.

## Fidelity key

- **Exact**: Lean statement matches the paper statement.
- **Equivalent**: Lean statement is logically equivalent but phrased differently.
- **Weaker**: Lean statement is strictly weaker than the paper statement.
- **Partial**: Some implications proved, others sorry or missing.
- **Sorry**: Statement present, proof incomplete.

## Section 1: Closed graphs and Groebner bases

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Theorem 1.1 | `theorem_1_1` | ClosedGraphs.lean | Exact | Generators form GB iff closed |
| Proposition 1.2 | `prop_1_2` | GraphProperties.lean | Exact | Closed implies chordal and claw-free |
| Corollary 1.3 | `cor_1_3`, `cor_1_3_connected_forward`, `pathGraph_isClosedGraph` | GraphProperties.lean | **Exact** | Forward: connected bipartite closed → `IsPathGraph`. Converse: `pathGraph n` on `Fin n` is closed. |
| Proposition 1.4 | `prop_1_4` | GraphProperties.lean | Equivalent | Checks `i < j` only (equivalent by symmetry of undirected adjacency) |
| Proposition 1.5 | `prop_1_5` | GraphProperties.lean | Exact | Unique minimal closed supergraph |

## Section 2: Reduced Groebner basis and radicality

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Theorem 2.1 | `theorem_2_1` + `theorem_2_1_reduced` | GroebnerBasis.lean | **Equivalent, split** | GB property and reducedness proved separately; no combined wrapper |
| Corollary 2.2 | `corollary_2_2` | Radical.lean | Exact | `J_G` is radical |

## Section 3: Prime decomposition and dimension

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Lemma 3.1 | `lemma_3_1` | PrimeIdeals.lean | Exact | `height(P_S) = |S| + |V| - c(S)` |
| Theorem 3.2 | `theorem_3_2` | PrimeDecomposition.lean | Exact | `J_G = inf P_S` |
| Corollary 3.3 | `corollary_3_3` | PrimeDecomposition.lean | **Sorry** | Correct statement, blocked by catenary/dimension infrastructure |
| Corollary 3.3 (lower bound) | `corollary_3_3_lower_bound` | PrimeDecomposition.lean | **Sorry** | `dim ≥ |V| + c(G)` |
| Corollary 3.4 | `corollary_3_4` | PrimeDecomposition.lean | **Sorry** | Depends on `IsCohenMacaulay` placeholder |
| Proposition 3.6 | `prop_3_6` | PrimeDecomposition.lean | Equivalent | "Components complete" rephrased as `Reachable → Adj ∨ eq` |
| Corollary 3.7 (a↔b) | `corollary_3_7` | PrimeDecomposition.lean | Partial | `|V|=3 ↔ prime` proved; `prime ↔ unmixed` structured (2 graph sorries in MinimalPrimes); (d) CM sorry |
| Proposition 3.8 | `prop_3_8` | MinimalPrimes.lean | Equivalent | Component containment rephrased via `SameComponent` predicate |
| Corollary 3.9 | `corollary_3_9` | MinimalPrimes.lean | Equivalent | Cut-point condition via `IsCutVertexRelative` |

## Not yet formalized

| Paper result | Status | Blocker |
|---|---|---|
| Proposition 1.6 (CM for special closed graphs) | Not started | `IsCohenMacaulay` not in Mathlib |
| Corollary 3.3 (dimension formula) | **Proved** | `corollary_3_3` in PrimeDecompositionDimension.lean |
| Corollary 3.3 (lower bound) | **Proved** | `corollary_3_3_lower_bound` in PrimeDecompositionDimension.lean |
| Corollary 3.4 (CM implies dim = n+c) | Statement present | `IsCohenMacaulay` placeholder |
| Corollary 3.5 (unmixed iff connected components) | Not started | Unmixed definition needed |

## Detailed blocker: Corollary 3.3

The missing abstract theorem is the **catenary property for polynomial rings**:
for a prime P in `MvPolynomial σ K` (K a field, σ finite),
`Ideal.primeHeight P + ringKrullDim (MvPolynomial σ K ⧸ P) = Nat.card σ`.

This is not in Mathlib v4.28.0 (no `IsCatenaryRing` class exists).

**Available Mathlib infrastructure (v4.28.0):**
- `ringKrullDim_quotient I`: `dim(R/I) = Order.krullDim(zeroLocus I)` (exact!)
- `MvPolynomial.ringKrullDim_of_isNoetherianRing`: `dim(K[σ]) = |σ|`
- `Ideal.primeSpectrumQuotientOrderIsoZeroLocus`: `Spec(R/I) ≃o zeroLocus(I)`
- `krullDim_eq_iSup_height_add_coheight_of_nonempty`: gives upper bound only
- `le_krullDim_iff`: chain of length n implies dim ≥ n

**BEI-specific proof strategy (avoids catenary):**

Upper bound: `dim(R/J_G) ≤ max_S (n - |S| + c(S))` follows from
`height + coheight ≤ dim(R)` (order theory, available).

Lower bound: Construct explicit chain of `n + c` primes containing `J_G`:
```
P_∅ < Q₁ < ... < Q_{c-1} < (x₁,...,xₙ) < (x₁,...,xₙ,y₁) < ... < m
```
Each `Q_k` replaces one component's complete-graph BEI with x-variable generators.
Primality of `Q_k`: quotient ≅ `D[y_v₁,...,y_{vₘ}]` (polynomial ring over domain D,
hence domain). The key fact "polynomial ring over domain is domain" IS in Mathlib.

**Sub-lemma proved:** `binomialEdgeIdeal_le_span_inl` — J_G ≤ (x₁,...,xₙ).

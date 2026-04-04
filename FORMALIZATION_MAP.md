# Formalization Map: Herzog et al. (2010) vs Lean

This file records how the statements in `BEI.tex` are represented in Lean, and how
faithfully the current Lean statements match the paper.

## Fidelity Key

- **Exact**: the Lean statement matches the paper statement.
- **Equivalent**: the Lean statement is mathematically equivalent but phrased differently.
- **Weaker**: the Lean statement proves only part of the paper statement.
- **Partial**: some parts are proved, but the full paper endpoint is not yet complete.
- **Sorry**: the statement is present, but its proof still depends on `sorry`.
- **Blocked**: the paper endpoint is deferred because the underlying foundations are missing.

## Section 1: Closed Graphs and Gröbner Bases

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Theorem 1.1 | `theorem_1_1` | `BEI/ClosedGraphs.lean` | Exact | Closed iff the quadratic generators form a Gröbner basis |
| Proposition 1.2 | `prop_1_2` | `BEI/GraphProperties.lean` | Exact | Closed implies chordal and claw-free |
| Corollary 1.3 | `cor_1_3`, `cor_1_3_connected_forward`, `pathGraph_isClosedGraph` | `BEI/GraphProperties.lean` | Exact | Formalized in the connected-graph form implicit in the paper |
| Proposition 1.4 | `prop_1_4` | `BEI/GraphProperties.lean` | Equivalent | Directed shortest-path formulation |
| Proposition 1.5 | `prop_1_5` | `BEI/GraphProperties.lean` | Exact | Unique minimal closed supergraph |
| Proposition 1.6 | `prop_1_6` | `BEI/CohenMacaulay.lean` | Blocked | Depends on a real `IsCohenMacaulay` foundation |

## Section 2: Reduced Gröbner Basis and Radicality

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Theorem 2.1 | `theorem_2_1`, `theorem_2_1_reduced`, `theorem_2_1_isReducedGroebnerBasis` | `BEI/GroebnerBasisSPolynomial.lean`, `BEI/GroebnerBasis.lean` | Equivalent, split | Buchberger proof and reducedness are formalized separately, with a wrapper theorem |
| Corollary 2.2 | `corollary_2_2` | `BEI/Radical.lean` | Exact | `J_G` is radical |

## Section 3: Prime Decomposition and Dimension

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| Lemma 3.1 | `lemma_3_1` | `BEI/PrimeIdeals.lean` | Exact | `height(P_S) = |S| + |V| - c(S)` |
| Theorem 3.2 | `theorem_3_2` | `BEI/PrimeDecomposition.lean` | Exact | `J_G = ⨅ S, P_S(G)` |
| Corollary 3.3 | `corollary_3_3` | `BEI/PrimeDecompositionDimension.lean` | Exact | Dimension formula proved directly in the quotient |
| Corollary 3.3 (lower bound) | `corollary_3_3_lower_bound` | `BEI/PrimeDecompositionDimension.lean` | Exact | `dim ≥ |V| + c(G)` |
| Corollary 3.4 | `corollary_3_4` | `BEI/PrimeDecomposition.lean` | Sorry | Statement present, but blocked by CM placeholder foundations |
| Proposition 3.6 | `prop_3_6` | `BEI/PrimeDecomposition.lean` | Equivalent | Completeness of components phrased via reachability |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_CM` | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean` | Partial | Prime branch done; unmixed branch has two remaining graph-theory sorries; CM branch is blocked |
| Proposition 3.8 | `prop_3_8` | `BEI/MinimalPrimes.lean` | Equivalent | Rephrased using `SameComponent` |
| Corollary 3.9 | `corollary_3_9` | `BEI/MinimalPrimes.lean` | Equivalent | Rephrased via `IsCutVertexRelative` |

## Section 4: Conditional Independence Ideals

| Paper result | Status | Notes |
|---|---|---|
| Section 4 applications | Not started | The algebraic backbone is largely in place, but the CI-ideal layer has not been formalized yet |

## Current Open Endpoints

| Paper endpoint | Current state |
|---|---|
| Proposition 1.6 | blocked on a real CM foundation |
| Corollary 3.4 | statement present, proof still `sorry` |
| Corollary 3.7 (unmixed branch) | close, but still depends on two graph combinatorics sorries |
| Corollary 3.7 (CM branch) | blocked on CM foundations |
| Section 4 | not started |

## Current File Split Notes

- `BEI/GroebnerBasisSPolynomial.lean` now carries the long S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2, Proposition 3.6, and the remaining CM / cycle endpoints.

These split points should be reflected in status docs whenever the structure changes again.

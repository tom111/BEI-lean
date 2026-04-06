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
| Proposition 1.6 | `prop_1_6`, `prop_1_6_herzogHibi`, `initialIdeal_closed_eq`, `rename_yPredVar_monomialInitialIdeal` | `BEI/CohenMacaulay.lean` | Sorry | The BEI-side reduction chain is now fully packaged; the remaining gap is exactly the external Herzog–Hibi theorem and CM transfer from the initial ideal |

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
| Corollary 3.4 | `corollary_3_4` | `BEI/PrimeDecompositionDimension.lean` | Sorry | CM definition exists; proof needs the quotient-dimension assembly from equidimensionality |
| Proposition 3.6 | `prop_3_6` | `BEI/PrimeDecomposition.lean` | Equivalent | Completeness of components phrased via reachability |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_CM` | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean` | Partial | Prime branch and unmixed branch are proved; the remaining CM branch is still open |
| Proposition 3.8 | `prop_3_8` | `BEI/MinimalPrimes.lean` | Equivalent | Rephrased using `SameComponent` |
| Corollary 3.9 | `corollary_3_9` | `BEI/MinimalPrimes.lean` | Equivalent | Rephrased via `IsCutVertexRelative` |

## Section 4: Conditional Independence Ideals

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| CI graph (binary output) | `ciGraph` | `BEI/CIIdeals.lean` | Exact | Graph on Omega with edges = same T-projection |
| CI ideal (binary output) | `ciIdeal` | `BEI/CIIdeals.lean` | Exact | 2x2 minors of the probability matrix |
| Single-statement bridge | `ciIdeal_single_eq_binomialEdgeIdeal` | `BEI/CIIdeals.lean` | Exact | CI ideal = BEI of the associated graph |
| Robustness specification | | | Not started | Multi-statement union of CI graphs |
| Corollaries (radical, minimal primes for CI) | | | Not started | Follow from Sections 2-3 via the bridge |

## Current Open Endpoints

| Paper endpoint | Current state |
|---|---|
| Proposition 1.6 | BEI-side reduction packaged end-to-end; remaining gap is the external Herzog–Hibi theorem plus CM transfer from the initial ideal |
| Corollary 3.4 | statement present, proof still `sorry` |
| Corollary 3.7 | prime and unmixed branches are proved; the CM branch is still `sorry` |
| Section 4 | single-statement bridge proved; multi-statement and corollaries not started |

## Current File Split Notes

- `BEI/GroebnerBasisSPolynomial.lean` now carries the long S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3, Corollary 3.4, the path CM example, and supporting equidimensionality lemmas.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2, Proposition 3.6, and the remaining CM endpoint for Corollary 3.7.
- `BEI/CohenMacaulay.lean` carries Proposition 1.6 and the complete-graph CM example.
- `toMathlib/CohenMacaulay/Defs.lean` carries the local working CM definition currently used in the project.

These split points should be reflected in status docs whenever the structure changes again.

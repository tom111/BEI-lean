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
| Proposition 1.6 | `prop_1_6`, `closedGraph_minimalPrime_componentCount_eq`, `closedGraph_componentCount_le_card_add_one` | `BEI/PrimeDecompositionDimension.lean`, `BEI/CohenMacaulay.lean` | Partial | Direct equidimensional surrogate proved; full depth-based CM statement from the paper still open |

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
| Corollary 3.4 | `corollary_3_4` | `BEI/PrimeDecompositionDimension.lean` | Exact | CM + `P_∅` minimal prime + equidimensionality |
| Proposition 3.6 | `prop_3_6` | `BEI/PrimeDecomposition.lean` | Equivalent | Completeness of components phrased via reachability |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_CM` | `BEI/PrimeDecomposition.lean`, `BEI/MinimalPrimes.lean`, `BEI/PrimeDecompositionDimension.lean` | Exact | All four equivalences proved (prime, unmixed, CM, |V|=3) |
| Proposition 3.8 | `prop_3_8` | `BEI/MinimalPrimes.lean` | Equivalent | Rephrased using `SameComponent` |
| Corollary 3.9 | `corollary_3_9` | `BEI/MinimalPrimes.lean` | Equivalent | Rephrased via `IsCutVertexRelative` |

## Section 4: Conditional Independence Ideals

| Paper result | Lean name | File | Fidelity | Notes |
|---|---|---|---|---|
| CI graph (binary output) | `ciGraph` | `BEI/CIIdeals.lean` | Exact | Graph on Omega with edges = same T-projection |
| CI ideal (binary output) | `ciIdeal` | `BEI/CIIdeals.lean` | Exact | 2x2 minors of the probability matrix |
| Single-statement bridge | `ciIdeal_single_eq_binomialEdgeIdeal` | `BEI/CIIdeals.lean` | Exact | CI ideal = BEI of the associated graph |
| Robustness specification | `CIStatement`, `ciGraphSpec`, `ciIdealSpec` | `BEI/CIIdeals.lean` | Exact | Family of CI statements, union graph, combined ideal |
| Specification bridge | `ciIdealSpec_eq_binomialEdgeIdeal` | `BEI/CIIdeals.lean` | Exact | CI ideal of specification = BEI of union graph |
| CI radicality | `ciIdealSpec_isRadical` | `BEI/CIIdeals.lean` | Exact | Transferred from Corollary 2.2 |
| CI prime decomposition | `ciIdealSpec_primeDecomposition` | `BEI/CIIdeals.lean` | Exact | Transferred from Theorem 3.2 |
| CI minimal primes | `ciIdealSpec_minimalPrimes` | `BEI/CIIdeals.lean` | Exact | Transferred from Corollary 3.9; requires connected union graph |

## Current Open Endpoints

| Paper endpoint | Current state |
|---|---|
| Proposition 1.6 | equidimensional surrogate proved directly; full paper CM statement still open |
| Corollary 3.4 | **proved** |
| Corollary 3.7 | **proved** (all branches) |
| Section 4 | complete: bridges, radicality, prime decomposition, and minimal-prime transfer all proved |

## Supporting `toMathlib` Progress

| Supporting result | Lean name | File | Status | Notes |
|---|---|---|---|---|
| Monomial ideal predicate | `Ideal.IsMonomial` | `toMathlib/MonomialIdeal.lean` | proved | Monomial ideals in `MvPolynomial` |
| Variable ideal prime, set version | `MvPolynomial.isPrime_span_X_image_set` | `toMathlib/MonomialIdeal.lean` | proved | Generalizes the local `Finset` version to `Set σ` |
| Variable factor in prime monomial membership | `Ideal.exists_variable_mem_of_monomial_mem_prime` | `toMathlib/MonomialIdeal.lean` | proved | Extracts a variable from a monomial lying in a prime ideal |
| Prime monomial ideals classification | `Ideal.IsMonomial.isPrime_iff_eq_span_X_image` | `toMathlib/MonomialIdeal.lean` | proved | Prime monomial ideals are exactly variable-generated ideals |
| Variable-generated ideals are monomial | `Ideal.IsMonomial.span_X_image` | `toMathlib/MonomialIdeal.lean` | proved | Basic API for the primary case |
| Forward primary monomial criterion | `Ideal.isPrimary_monomial_criterion` | `toMathlib/MonomialIdeal.lean` | proved | From `IsPrimary` plus `radical = span (X '' s)` to the outside-the-radical nonmembership criterion |
| Leading coefficient in powers | `coeff_pow_lexMax` | `toMathlib/MonomialIdeal.lean` | proved | Isolates the lex-maximal support contribution in `p ^ n` |
| Radical is monomial | `Ideal.IsMonomial.radical_isMonomial` | `toMathlib/MonomialIdeal.lean` | proved | Uses lex-max leading-term extraction; requires `[LinearOrder σ]` |
| Outside-`s` structural invariance | `Ideal.monomial_mem_iff_add_outside`, `Ideal.monomial_mem_iff_filter` | `toMathlib/MonomialIdeal.lean` | proved | Adding exponents outside the radical-variable set does not change monomial membership |
| Support extraction | `Ideal.not_mem_exists_monomial_notMem` | `toMathlib/MonomialIdeal.lean` | proved | General: if `p ∉ I`, some support monomial is not in `I` (only needs `CommRing`) |
| Converse helpers | `Ideal.mem_of_mul_mem_of_lexMax_outside` | `toMathlib/MonomialIdeal.lean` | proved | Leading-term peeling for the primary converse |
| Forward primary characterization | `Ideal.IsMonomial.isPrimary_radical_eq_span_X` | `toMathlib/MonomialIdeal.lean` | proved | Primary monomial → radical is variable-generated ∧ criterion |
| Converse primary characterization | `Ideal.IsMonomial.isPrimary_of_criterion` | `toMathlib/MonomialIdeal.lean` | proved | Criterion + radical = span(X '' s) → primary; minimal bad s-exponent + primality of span(X '' s) |
| Full primary iff | `Ideal.IsMonomial.isPrimary_iff` | `toMathlib/MonomialIdeal.lean` | proved | Complete characterization of primary monomial ideals |

### Variable ideal dimension (`toMathlib/HeightVariableIdeal.lean`)

| Result | Lean name(s) | File | Status | Notes |
|--------|-------------|------|--------|-------|
| Kernel = variable ideal | `ker_killS_eq_span_X_image` | `toMathlib/HeightVariableIdeal.lean` | proved | The kernel of the variable-killing map is exactly the variable ideal |
| Surjectivity | `killS_surjective` | `toMathlib/HeightVariableIdeal.lean` | proved | The variable-killing map hits every polynomial in the remaining variables |
| Quotient equivalence | `quotientSpanXEquiv` | `toMathlib/HeightVariableIdeal.lean` | proved | `MvPolynomial σ K ⧸ ⟨X_i : i ∈ s⟩ ≃+* MvPolynomial {j // j ∉ s} K` |
| Quotient dimension formula | `MvPolynomial.ringKrullDim_quotient_span_X_image` | `toMathlib/HeightVariableIdeal.lean` | proved | `dim(K[x₁,…,xₙ]/⟨xᵢ : i ∈ s⟩) = |{j ∉ s}|` |
| Dimension comparison | `MvPolynomial.ringKrullDim_quotient_span_X_eq_of_card_eq` | `toMathlib/HeightVariableIdeal.lean` | proved | Equal generator counts → equal quotient dims |

### Squarefree monomial primes (`toMathlib/SquarefreeMonomialPrimes.lean`)

| Result | Lean name(s) | File | Status | Notes |
|--------|-------------|------|--------|-------|
| Variable membership | `MvPolynomial.X_mem_span_X_image_iff` | `toMathlib/SquarefreeMonomialPrimes.lean` | proved | `X i ∈ span(X '' S) ↔ i ∈ S`; only needs `Nontrivial R` |
| Containment ↔ vertex cover | `MvPolynomial.variablePairIdeal_le_span_X_iff` | `toMathlib/SquarefreeMonomialPrimes.lean` | proved | Edge ideal ≤ variable ideal iff vertex cover |
| Minimal prime → minimal cover | `MvPolynomial.minimalPrime_variablePairIdeal_eq_span` | `toMathlib/SquarefreeMonomialPrimes.lean` | proved | Forward direction |
| Minimal cover → minimal prime | `MvPolynomial.span_minimalVertexCover_minimalPrime` | `toMathlib/SquarefreeMonomialPrimes.lean` | proved | Backward direction |
| Full iff | `MvPolynomial.minimalPrime_variablePairIdeal_iff` | `toMathlib/SquarefreeMonomialPrimes.lean` | proved | Complete characterization |

## Current File Split Notes

- `BEI/GroebnerBasisSPolynomial.lean` now carries the long S-polynomial proof of Theorem 2.1.
- `BEI/GroebnerBasis.lean` carries reducedness and the paper-facing wrapper.
- `BEI/PrimeDecompositionDimension.lean` carries Corollary 3.3, Corollary 3.4, `corollary_3_7_CM`, the path CM example, Proposition 1.6, and supporting equidimensionality lemmas.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2 and Proposition 3.6.
- `BEI/CIIdeals.lean` carries the Section 4 binary-output setup, both bridge theorems, and the transferred radicality / prime-decomposition / minimal-prime theorems.
- `BEI/CohenMacaulay.lean` carries the local CM-surrogate definition wrapper, HH bipartite graph infrastructure, the closed-graph component-count upper bound, and the complete-graph example.
- `toMathlib/CohenMacaulay/Defs.lean` carries the local working CM definition currently used in the project.
- `toMathlib/MonomialIdeal.lean` carries `Ideal.IsMonomial`, `MvPolynomial.isPrime_span_X_image_set` (Set version), `Ideal.exists_variable_mem_of_monomial_mem_prime`, `Ideal.IsMonomial.isPrime_iff_eq_span_X_image` (prime monomial ideals = variable ideals), `Ideal.IsMonomial.span_X_image`, `coeff_pow_lexMax`, `Ideal.IsMonomial.radical_isMonomial`, `Ideal.isPrimary_monomial_criterion`, `Ideal.IsMonomial.isPrimary_radical_eq_span_X`, the structural outside-`s` membership lemmas, the general support-extraction lemma `Ideal.not_mem_exists_monomial_notMem`, the converse helper `Ideal.mem_of_mul_mem_of_lexMax_outside`, and the full primary iff `Ideal.IsMonomial.isPrimary_iff`.
- `toMathlib/SquarefreeMonomialPrimes.lean` carries `variablePairIdeal`, `IsVertexCover`, `IsMinimalVertexCover`, and the complete minimal prime ↔ minimal vertex cover characterization for edge ideals.
- `toMathlib/HeightVariableIdeal.lean` carries the variable-killing map, the quotient equivalence for variable ideals, and the resulting quotient-dimension formulas.

These split points should be reflected in status docs whenever the structure changes again.

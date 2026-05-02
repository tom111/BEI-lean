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
| Proposition 1.6 | `proposition_1_6`, `proposition_1_6_dim_formula`, `pathGraph_binomialEdgeIdeal_isCohenMacaulay`, `pathGraph_binomialEdgeIdeal_ringKrullDim`, `groebnerDeformation_cm_transfer`, `monomialInitialIdeal_isCohenMacaulay`, `prop_1_6_equidim` | `BEI/Proposition1_6.lean`, `BEI/GroebnerDeformation.lean`, `BEI/Equidim.lean`, `BEI/Prop1_6Equidim.lean` | **Exact (axiom-clean 2026-04-22)** | Paper-faithful `proposition_1_6` fully proved. `#print axioms` reports `{propext, Classical.choice, Quot.sound}` — no `sorryAx`. Route: (Step 1) HH-side monomial CM `monomialInitialIdeal_isCohenMacaulay`, (Step 2) Gröbner deformation transfer `groebnerDeformation_cm_transfer` using weighted grading, flat family over `K[t]`, and graded local-to-global CM. The graded LTG theorem's Case C closure is via the **finite-free parameter-subring route** (Steps A + B + C + D in `toMathlib/GradedFiniteFree.lean` and `toMathlib/GradedRegularSop.lean`), completed 2026-04-22. Path-graph examples `pathGraph_satisfiesProp1_6Condition`, `pathGraph_binomialEdgeIdeal_isCohenMacaulay`, `pathGraph_binomialEdgeIdeal_ringKrullDim` are all axiom-clean. |

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
| Corollary 3.3 | `corollary_3_3` | `BEI/PrimeDecompositionDimensionCore.lean` | Exact | Dimension formula proved directly in the quotient |
| Corollary 3.3 (lower bound) | `corollary_3_3_lower_bound` | `BEI/PrimeDecompositionDimensionCore.lean` | Exact | `dim ≥ |V| + c(G)` |
| Corollary 3.4 | `corollary_3_4`, `corollary_3_4_connected`, `corollary_3_4_equidim` | `BEI/Corollary3_4.lean`, `BEI/PrimeDecompositionDimension.lean` | **Exact (axiom-clean 2026-04-22)** | Paper-faithful `corollary_3_4`: `IsCohenMacaulayRing (K[x,y] ⧸ J_G) → dim = Fintype.card V + numConnectedComponents G`. Route: standard ℕ-grading on `MvPolynomial (BinomialEdgeVars V) K` descends to `R ⧸ J_G`, which is connected graded and f.g. Noetherian; CM at the irrelevant ideal via `CM_localize` gives Step A + Step C finite-free over `K[z]`, and `IsEquidimRing.of_flat_finite` (`toMathlib/FiniteFreeEquidim.lean`) + `corollary_3_4_equidim` closes the dimension formula. `#print axioms` reports `{propext, Classical.choice, Quot.sound}`. |
| Proposition 3.6 | `prop_3_6` | `BEI/PrimeDecomposition.lean` | Equivalent | Completeness of components phrased via reachability |
| Corollary 3.7 | `corollary_3_7`, `corollary_3_7_unmixed`, `corollary_3_7_equidim`, `corollary_3_7_cm_forward`, `corollary_3_7_cm_fin` | `BEI/PrimeDecomposition.lean`, `BEI/CycleUnmixed.lean`, `BEI/PrimeDecompositionDimension.lean`, `BEI/Corollary3_4.lean` | **Exact (axiom-clean 2026-04-23)** | All four branches proved: prime (a↔b), unmixed (a↔c), equidim surrogate, and paper-faithful Cohen–Macaulay (a↔d). Forward `CM → n = 3` is general-V (`corollary_3_7_cm_forward`) via the `CM → IsEquidim` bridge. Backward `n = 3 → CM` is stated for `SimpleGraph (Fin n)` (`corollary_3_7_cm_backward_fin`, `corollary_3_7_cm_fin`) via `proposition_1_6` applied to `K_3`, whose closedness + Prop 1.6 transitivity condition hold (the latter vacuously: `k.val + 1 < 3` is incompatible with `i < j < k` in `Fin 3`). |
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

## Paper Endpoint Status

| Scope | Current state |
|---|---|
| Sections 1--4 | All paper endpoints listed above are represented in Lean. The section tables record which statements are exact matches and which are equivalent reformulations. |

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

### Real Cohen-Macaulay foundations (`toMathlib/CohenMacaulay/Defs.lean`)

| Result | Lean name(s) | File | Status | Notes |
|--------|-------------|------|--------|-------|
| Depth of a local ring | `ringDepth` | `toMathlib/CohenMacaulay/Defs.lean` | proved | Defined via lengths of weakly regular sequences in the maximal ideal |
| Local CM definition | `IsCohenMacaulayLocalRing` | `toMathlib/CohenMacaulay/Defs.lean` | proved | Real CM definition for local rings via `ringKrullDim = ringDepth` |
| Global CM definition | `IsCohenMacaulayRing` | `toMathlib/CohenMacaulay/Defs.lean` | proved | Defined by localization at every prime |
| Depth ≤ dimension | `weaklyRegular_length_le_ringKrullDim`, `ringDepth_le_ringKrullDim` | `toMathlib/CohenMacaulay/Defs.lean` | proved | First basic CM inequalities for the real-CM track |

### Real Cohen-Macaulay basics (`toMathlib/CohenMacaulay/Basic.lean`)

| Result | Lean name(s) | File | Status | Notes |
|--------|-------------|------|--------|-------|
| Quotient nontriviality/locality | `quotSMulTop_nontrivial`, `quotSMulTopLocalRing` | `toMathlib/CohenMacaulay/Basic.lean` | proved | If `x ∈ maximalIdeal R`, then `R ⧸ xR` is nontrivial and local |
| Easy depth inequality | `ringDepth_quotSMulTop_succ_le` | `toMathlib/CohenMacaulay/Basic.lean` | proved | `depth(R/xR) + 1 ≤ depth(R)` for regular `x ∈ maximalIdeal R` |
| Converse regular-quotient CM transfer | `isCohenMacaulayLocalRing_of_regular_quotient` | `toMathlib/CohenMacaulay/Basic.lean` | proved | CM quotient implies CM ring under regularity and Noetherianity |
| CM from regular sequence of max length | `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim` | `toMathlib/CohenMacaulay/Basic.lean` | proved | Weakly regular seq of length = dim implies CM |
| 0-dimensional CM | `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero` | `toMathlib/CohenMacaulay/Basic.lean` | proved | 0-dim Noetherian local ring is CM |
| Forward regular-quotient CM transfer | `isCohenMacaulayLocalRing_quotient` | `toMathlib/CohenMacaulay/Localization.lean` | proved | Uses Ext/Rees machinery and the hard depth inequality |
| CM localizes | `isCohenMacaulayLocalRing_localization_atPrime` | `toMathlib/CohenMacaulay/Localization.lean` | proved | Localization of a CM local ring at a prime is CM |
| Global CM from local ring CM | `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` | `toMathlib/CohenMacaulay/Localization.lean` | proved | Wrapper using `CM localizes` for already-local rings |
| Unmixedness of CM local rings | `associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing` | `toMathlib/CohenMacaulay/Localization.lean` | proved | Associated primes of a CM local ring are minimal |

### HH-side Proposition 1.6 infrastructure (`BEI/Equidim.lean`)

| Result | Lean name(s) | File | Status | Notes |
|--------|-------------|------|--------|-------|
| HH graph conditions | `prop_1_6_herzogHibi` | `BEI/Equidim.lean` | proved | Packages the graph-combinatorial Herzog–Hibi conditions from the Proposition 1.6 setup |
| Iterated diagonal regularity | `sum_XY_isSMulRegular_mod_diagonalSum` | `BEI/Equidim.lean` | proved | The successive diagonal sums are non-zero-divisors on the relevant HH quotients |
| NZD transfer through double quotient | `isSMulRegular_of_doubleQuot` | `BEI/Equidim.lean` | proved | Transfers NZD from `R ⧸ (I ⊔ J)` to `(R ⧸ I) ⧸ J.map mk_I` |
| Self-module ideal equality | `ideal_smul_top_self` | `BEI/Equidim.lean` | proved | `I • ⊤ = I` for self-module; bridges `IsWeaklyRegular` module quotients to ring quotients |
| `IsWeaklyRegular` packaging | `bipartiteEdgeMonomialIdeal_isWeaklyRegular` | `BEI/Equidim.lean` | proved | Diagonal forms are a weakly regular sequence of length `n-1` on the bipartite quotient |
| Dimension formula (`dim = n+1`) | `ringKrullDim_bipartiteEdgeMonomialIdeal` | `BEI/Equidim.lean` | proved | `dim(S ⧸ I) = n + 1` under HH conditions; uses radical equidim machinery |
| Radical equidim dim theorem | `ringKrullDim_quotient_radical_equidim` | `BEI/Equidim.lean` | proved | For radical equidimensional ideal: `dim(R/I) = d` when all minimal primes give dim `d` |
| NZD for `x_{n-1}` | `X_inl_last_isSMulRegular_mod_diagonalSum` | `BEI/Equidim.lean` | proved | `X(inl ⟨n-1⟩)` is NZD on `S ⧸ (I ⊔ diag_{n-1})`; uses monomial divisibility argument |
| NZD for `y_{n-1}` | `X_inr_last_isSMulRegular_mod_diagonalSum_sup` | `BEI/Equidim.lean` | proved | `X(inr ⟨n-1⟩)` is NZD on `S ⧸ (I ⊔ diag_{n-1} ⊔ ⟨x_{n-1}⟩)`; extended ideal handling |
| Extended `IsWeaklyRegular` (length `n+1`) | `bipartiteEdgeMonomialIdeal_isWeaklyRegular_full` | `BEI/Equidim.lean` | proved | Diagonal sums + two free variables; length = `n + 1 = dim` |
| Local CM at augmentation ideal | `isCohenMacaulayLocalRing_at_augIdeal` | `BEI/Equidim.lean` | proved | `IsCohenMacaulayLocalRing` at `ker(constantCoeff)` via regular-sequence localization + dimension sandwich |
| HH-side global CM step | `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` | `BEI/Equidim.lean` | proved | F2 route: `p ≤ augIdeal` via CM localizes; `p ⊄ augIdeal` via pick-U (Step 1), hhIndep (Step 2), localize-away-s_U (Step 4), E_U bundled equiv (Session C1), contraction equality via C3a-inl/inr (Step 6), C2 tensor-left-localisation bridge, L7 tensor-away CM replacement, loc-of-loc transport. `K : Type` (universe 0). |
| Reduced HH ring at aug is CM local | `isCohenMacaulayLocalRing_at_augIdealReduced` | `BEI/Equidim.lean` | proved | Session A′ inductive bridge from L5 output to reduced HH ring |
| Reduced HH ring at aug is globally CM | `isCohenMacaulayRing_at_augIdealReduced` | `BEI/Equidim.lean` | proved | Session B wrapper of the local version through `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` |
| Bundled monomial-localisation equiv | `E_U` | `BEI/Equidim.lean` | proved | Session C1: `R[s_U⁻¹] ≃ₐ[K] reducedHHRing G' ⊗[K] Localization.Away (rename Sum.inr s_U^U)` |
| Tensor-left-localisation bridge | `Algebra.tensorLeftLocalisationEquiv` | `toMathlib/TensorLocalisation.lean` | proved | Session C2: `(A⊗B)_𝔓 ≃+* (A_m ⊗ B)_𝔓'` where `m = 𝔓 ∩ A` |

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
- `BEI/PrimeDecompositionDimensionCore.lean` carries Corollary 3.3, the quotient-dimension chain machinery, the lower-bound theorem, and the third-isomorphism dimension helper used by every equidimensional surrogate.
- `BEI/PrimeDecompositionDimension.lean` carries the equidimensional surrogate variants of Corollaries 3.4 and 3.7.
- `BEI/Prop1_6Equidim.lean` carries Example 1.7(b) (the path graph equidimensional example), Proposition 1.6 via the direct equidimensional route, and the shared `isEquidim_of_equidim_minimalPrimes` helper.
- `BEI/PrimeDecomposition.lean` carries Theorem 3.2 and Proposition 3.6.
- `BEI/CIIdeals.lean` carries the Section 4 binary-output setup, both bridge theorems, and the transferred radicality / prime-decomposition / minimal-prime theorems.
- `BEI/Equidim.lean` carries the local equidimensional surrogate definition wrapper, HH bipartite graph infrastructure, the closed-graph component-count upper bound, and the complete-graph example.
- `toMathlib/Equidim/Defs.lean` carries the local working equidimensional definition currently used in the project.
- `toMathlib/CohenMacaulay/Defs.lean` carries the first real Cohen–Macaulay foundation layer, kept separate from the equidimensional surrogate.
- `toMathlib/CohenMacaulay/Basic.lean` carries the quotient-local-ring setup, the easy depth inequality for regular quotients, and the converse regular-quotient CM transfer.
- `toMathlib/CohenMacaulay/Localization.lean` carries the Ext/Rees bridge, the hard depth inequality, forward CM transfer, unmixedness, and the CM localization/globalization theorems for local rings.
- `toMathlib/MonomialIdeal.lean` carries `Ideal.IsMonomial`, `MvPolynomial.isPrime_span_X_image_set` (Set version), `Ideal.exists_variable_mem_of_monomial_mem_prime`, `Ideal.IsMonomial.isPrime_iff_eq_span_X_image` (prime monomial ideals = variable ideals), `Ideal.IsMonomial.span_X_image`, `coeff_pow_lexMax`, `Ideal.IsMonomial.radical_isMonomial`, `Ideal.isPrimary_monomial_criterion`, `Ideal.IsMonomial.isPrimary_radical_eq_span_X`, the structural outside-`s` membership lemmas, the general support-extraction lemma `Ideal.not_mem_exists_monomial_notMem`, the converse helper `Ideal.mem_of_mul_mem_of_lexMax_outside`, and the full primary iff `Ideal.IsMonomial.isPrimary_iff`.
- `toMathlib/SquarefreeMonomialPrimes.lean` carries `variablePairIdeal`, `IsVertexCover`, `IsMinimalVertexCover`, and the complete minimal prime ↔ minimal vertex cover characterization for edge ideals.
- `toMathlib/HeightVariableIdeal.lean` carries the variable-killing map, the quotient equivalence for variable ideals, and the resulting quotient-dimension formulas.

These split points should be reflected in status docs whenever the structure changes again.

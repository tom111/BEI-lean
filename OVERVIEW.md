# BEI Formalization: Executive Summary

## What This Is

A Lean 4 / Mathlib v4.28.0 formalization of Herzog, Hibi, Hreinsdóttir, Kahle, and Rauh (2010), "Binomial edge ideals and conditional independence statements." The central result is Theorem 1.1: the binomial edge ideal $J_G$ has a quadratic Gröbner basis if and only if $G$ is a closed graph.

## Mathematical Content

The polynomial ring $K[x_1,\ldots,x_n, y_1,\ldots,y_n]$ is modeled using `MvPolynomial (V ⊕ V) K`, where `Sum.inl i` represents $x_i$ and `Sum.inr i` represents $y_i$. The binomial edge ideal is $J_G = \langle x_i y_j - x_j y_i : \{i,j\} \in E(G),\, i < j \rangle$. A graph is *closed* if for any two edges sharing a vertex, a third edge must exist — the algebraic-combinatorial condition that forces all S-polynomials of the Gröbner basis generators to reduce to zero.

The project also formalizes the prime decomposition $J_G = \bigcap_S P_S(G)$ (Theorem 3.2), where each $P_S(G)$ is a prime ideal indexed by subsets $S \subseteq V$ satisfying a cut-vertex condition, and the Krull dimension formula $\dim K[x,y]/J_G = |V| + c(G)$ where $c(G)$ is the number of connected components of $G$.

## Project Structure

The source lives in `BEI/` with roughly one file per mathematical theme: `Definitions.lean` (core ring-theoretic setup), `Groebner.lean` (lex term order), `MonomialOrder.lean` (leading monomial computations), `GraphProperties.lean` (chordal/claw-free graphs, Proposition 1.4), `AdmissiblePaths.lean` (path monomials, Gröbner basis elements), `GroebnerAPI.lean` (abstract Buchberger theory), `ClosedGraphs.lean` (Theorem 1.1), `PrimeIdeals.lean`, `MinimalPrimes.lean`, `PrimeDecomposition.lean`, and `GroebnerBasis.lean` (Theorem 2.1).

## Current Progress

The foundational layers are complete. The lex monomial order, all leading monomial proofs for $f_{ij}$, graph-theoretic properties (Proposition 1.4 and Corollary 1.3), and admissible-path membership are all fully proved with zero sorries. The abstract Buchberger criterion — `isGroebnerBasis_iff_sPolynomial_isRemainder` — is fully proved in `GroebnerAPI.lean` via well-founded induction on the maximum degree appearing in any remainder representation. Most significantly, **Theorem 1.1 is fully proved**: `theorem_1_1` in `ClosedGraphs.lean` shows that the quadratic generators form a Gröbner basis if and only if the graph is closed. The forward direction (`closed_implies_groebner`) applies the Buchberger criterion with a four-case S-polynomial analysis covering same-pair, shared-first-endpoint, shared-last-endpoint, and coprime configurations.

The project currently has **17 sorries** across 5 files. The remaining sorries split into three difficulty bands. Accessible but requiring work: `corollary_3_9` (blocked on `primeComponent_isPrime`) and `corollary_3_3_lower_bound` (a chain-of-primes argument). Genuinely hard: `primeComponent_isPrime` (needs an explicit ring homomorphism into a product of polynomial rings), `theorem_3_2 ⊇` (radical ideal theory), and the Gröbner basis characterization for general admissible-path sets. Deferred indefinitely: Cohen–Macaulay results and `corollary_2_2` (squarefree initial ideal $\Rightarrow$ radical), both of which depend on Mathlib infrastructure not yet available in v4.28.0.

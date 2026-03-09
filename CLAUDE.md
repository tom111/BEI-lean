# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project Overview

This is a Lean 4 formalization project for **Binomial Edge Ideals (BEI)**, based on Herzog et al. (2010). The goal is to formally verify results about binomial edge ideals of simple graphs in commutative algebra.

- **Lean version**: `leanprover/lean4:v4.28.0`
- **Primary dependency**: Mathlib `v4.28.0`
- **Build system**: Lake (Lean's package manager)

## Build Commands

```bash
# Build the entire project
lake build

# Build a specific file (e.g., BEI.Definitions)
lake build BEI.Definitions

# Update/fetch dependencies
lake update

# Clean build artifacts
lake clean
```

There is no test suite — correctness is enforced by Lean's type checker. A successful `lake build` with no errors or `sorry`s is the goal.

## Project Structure

- `BEI/Definitions.lean` — Core mathematical definitions: `BinomialEdgeVars V` (= `V ⊕ V`), notation `x i` and `y i` for the two copies of variables, `binomialEdgeIdeal G`, and `IsClosedGraph G` (Condition (b) of Theorem 1.1 in Herzog et al.)
- `BEI/Groebner.lean` — Term order: defines `binomialEdgeLE` (lex with `x_1 > x_2 > ... > x_n > y_1 > ... > y_n`) and the corresponding `LinearOrder (BinomialEdgeVars V)` instance
- `BEI/MonomialOrder.lean` — Connects the linear order to Mathlib's `MonomialOrder` infrastructure; proves leading term of `f_{ij}` is `x_i · y_j`
- `BEI/GraphProperties.lean` — `IsChordal`, `IsClawFree`, `graphClosure`; Propositions 1.2, 1.4, 1.5, Corollary 1.3
- `BEI/AdmissiblePaths.lean` — `pathMonomial`, `groebnerElement`, `groebnerBasisSet`; admissible path membership
- `BEI/GroebnerAPI.lean` — `IsRemainder`, `IsGroebnerBasis`, Buchberger's criterion (fully proved)
- `BEI/ClosedGraphs.lean` — **Theorem 1.1**: closed graph ↔ quadratic Gröbner basis (fully proved)
- `BEI/GroebnerBasis.lean` — Theorem 2.1 (reduced Gröbner basis) and Corollary 2.2 (radical)
- `BEI/PrimeIdeals.lean` — `primeComponent`, `componentCount`; Section 3 prime ideal properties
- `BEI/MinimalPrimes.lean` — Proposition 3.8, Corollary 3.9; minimal prime characterization
- `BEI/PrimeDecomposition.lean` — Theorem 3.2 (prime decomposition), dimension corollaries
- `BEI/CohenMacaulay.lean` — Placeholder for Cohen-Macaulay results (deferred; not in Mathlib)
- `BEI.lean` — Root library entry point
- `BEI.tex` — Reference paper with the mathematical content being formalized

## Key Mathematical Concepts

- **Variables**: The polynomial ring uses `V ⊕ V` as the index type; `Sum.inl i` represents `x_i` and `Sum.inr i` represents `y_i`.
- **Binomial edge ideal**: `J_G = ⟨x_i y_j - x_j y_i : {i,j} ∈ E(G), i < j⟩` as a `Ideal (MvPolynomial (BinomialEdgeVars V) K)`.
- **Closed graph**: The `IsClosedGraph` property encodes that for any edges sharing a vertex, certain additional edges must exist (the condition that characterizes when `J_G` has a quadratic Gröbner basis).
- **Term order**: The Gröbner order is `x_1 > x_2 > … > x_n > y_1 > y_2 > … > y_n` (all `x`-variables above all `y`-variables, smaller index = larger variable), matching the paper.

## Lean/Mathlib Conventions

- The project uses `noncomputable section` throughout (polynomials over fields are noncomputable).
- `relaxedAutoImplicit = false` is set — all variables must be explicitly declared or introduced with `variable`.
- Linter `weak.linter.mathlibStandardSet` is enabled; follow Mathlib style for naming and formatting.
- Use `open MvPolynomial` when working with multivariate polynomials (already opened in `Definitions.lean`).
- Relevant Mathlib namespaces: `MvPolynomial`, `Ideal`, `SimpleGraph`, `LinearOrder`.

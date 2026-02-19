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
- `BEI/Groebner.lean` — Term order for Gröbner basis computations: defines `binomialEdgeLE` (lex with `x > y`, descending indices) and the corresponding `LinearOrder (BinomialEdgeVars V)` instance
- `BEI/Basic.lean` — Placeholder, currently unused
- `BEI.lean` — Root library entry point
- `BEI.tex` — Reference paper with the mathematical content being formalized

## Key Mathematical Concepts

- **Variables**: The polynomial ring uses `V ⊕ V` as the index type; `Sum.inl i` represents `x_i` and `Sum.inr i` represents `y_i`.
- **Binomial edge ideal**: `J_G = ⟨x_i y_j - x_j y_i : {i,j} ∈ E(G), i < j⟩` as a `Ideal (MvPolynomial (BinomialEdgeVars V) K)`.
- **Closed graph**: The `IsClosedGraph` property encodes that for any edges sharing a vertex, certain additional edges must exist (the condition that characterizes when `J_G` has a quadratic Gröbner basis).
- **Term order**: The Gröbner order has `y < x` (all `y`-variables precede all `x`-variables) and within each block indices are descending (i.e., `x_n > x_{n-1} > … > x_1`).

## Lean/Mathlib Conventions

- The project uses `noncomputable section` throughout (polynomials over fields are noncomputable).
- `relaxedAutoImplicit = false` is set — all variables must be explicitly declared or introduced with `variable`.
- Linter `weak.linter.mathlibStandardSet` is enabled; follow Mathlib style for naming and formatting.
- Use `open MvPolynomial` when working with multivariate polynomials (already opened in `Definitions.lean`).
- Relevant Mathlib namespaces: `MvPolynomial`, `Ideal`, `SimpleGraph`, `LinearOrder`.

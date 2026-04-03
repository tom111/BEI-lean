---
title: BEI Blueprint
---

# Blueprint: Binomial Edge Ideals

This is the initial blueprint for the Lean formalization of the paper
_Binomial edge ideals and conditional independence statements_
by Herzog, Hibi, Hreinsdóttir, Kahle, and Rauh.

Its purpose is to help humans understand:

- what the paper proves;
- where each result lives in Lean;
- whether the Lean statement is exact, equivalent, weaker, partial, or still blocked;
- and what the current proof bottlenecks are.

This blueprint is meant to evolve into a GitHub Pages site rooted in `docs/`.

## Paper and code

- Paper source: [`BEI.tex`](/home/tom/BEI-lean/BEI.tex)
- Existing formalization map: [`FORMALIZATION_MAP.md`](/home/tom/BEI-lean/FORMALIZATION_MAP.md)
- Main library entrypoint: [`BEI.lean`](/home/tom/BEI-lean/BEI.lean)

## Blueprint pages

- [Overview](overview.md)
- [Section 1: Closed Graphs and Quadratic Gröbner Bases](section-1.md)
- [Section 2: Reduced Gröbner Basis and Radicality](section-2.md)
- [Section 3: Prime Decomposition, Dimension, Minimal Primes](section-3.md)
- [Section 4: CI-Ideals and Robustness](section-4.md)
- [Workflow and Supporting Guides](workflow.md)

## Fidelity key

- **Exact**: Lean statement matches the paper statement.
- **Equivalent**: Lean statement is mathematically equivalent but phrased differently.
- **Weaker**: Lean proves a genuine weakening of the paper statement.
- **Partial**: some implications or subparts are proved, others are not.
- **Blocked**: the formal statement is known, but the required infrastructure is missing.

## Current headline status

- Section 1 is mostly formalized, with one important statement-packaging issue around
  Corollary 1.3.
- Section 2 is substantially formalized.
- Section 3 has the core prime decomposition in place, but the dimension corridor still
  needs careful infrastructure work.
- Section 4 is not yet formalized as a theorem layer, though there is now a plan for it.


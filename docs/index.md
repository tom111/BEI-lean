---
title: BEI Blueprint
---

# Blueprint: Binomial Edge Ideals

This site is a blueprint for the Lean formalization of the paper
_Binomial edge ideals and conditional independence statements_
by Jürgen Herzog, Takayuki Hibi, Freyja Hreinsdóttir, Thomas Kahle, and Johannes Rauh.

<div class="intro-card">
This blueprint is a reader-facing map of the project. It tells you which results from the
paper are formalized, where they live in the Lean codebase, and how closely the formal
statements match the originals.
</div>

It is intended as a reader-facing map of the project:

- which results from the paper are formalized;
- where they live in the Lean codebase;
- and with what fidelity they correspond to the original statements.

<div class="quick-links">
  <a href="overview.md">Overview</a>
  <a href="section-1.md">Section 1</a>
  <a href="section-2.md">Section 2</a>
  <a href="section-3.md">Section 3</a>
  <a href="section-4.md">Section 4</a>
</div>

## The paper

- Published version: [Advances in Applied Mathematics DOI](https://doi.org/10.1016/j.aam.2010.01.003)
- arXiv version: [arXiv:0909.4717](https://arxiv.org/abs/0909.4717)
- TeX source in this repository:
  [BEI.tex](https://github.com/tom111/BEI-lean/blob/master/BEI.tex)

## The code

- Main entrypoint:
  [BEI.lean](https://github.com/tom111/BEI-lean/blob/master/BEI.lean)
- Repository-side theorem map:
  [FORMALIZATION_MAP.md](https://github.com/tom111/BEI-lean/blob/master/FORMALIZATION_MAP.md)

## Fidelity labels

- **Exact**: the Lean theorem matches the paper statement.
- **Equivalent**: the Lean theorem is mathematically equivalent but phrased differently.
- **Weaker**: Lean proves a genuine weakening of the paper statement.
- **Partial**: part of the paper statement is formalized, part is still missing.
- **Blocked**: the intended statement is identified, but the needed foundation is not yet in place.

## Blueprint pages

- [Overview](overview.md)
- [Section 1: Closed Graphs and Quadratic Gröbner Bases](section-1.md)
- [Section 2: Reduced Gröbner Basis and Radicality](section-2.md)
- [Section 3: Prime Decomposition, Dimension, Minimal Primes](section-3.md)
- [Section 4: CI-Ideals and Robustness](section-4.md)

## Snapshot

- Section 1 is largely formalized.
- Section 2 is largely formalized.
- Section 3 contains the core algebraic heart of the project.
- Section 4 is not yet formalized as a theorem layer.

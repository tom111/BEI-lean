# Guide: Clean Up the Public Theorem Layer

## Goal

Make the top-level theorem statements and proofs read like the mathematical narrative of
the paper, while hiding low-level combinatorics and Finsupp plumbing behind private
helper lemmas.


## Why this matters

Right now the repo often has the right theorem, but the public file surface still
exposes too much of the implementation burden.

This hurts:

- readability for humans;
- reuse by Claude in later sessions;
- confidence that a theorem really matches the paper statement.


## Core rule

Every major paper theorem should have:

1. one paper-facing public statement;
2. a short proof skeleton visible near that statement;
3. heavy case analysis moved into named helper lemmas.


## Highest-priority targets

## 1. Theorem 2.1 packaging across the split files

Files:

- [GroebnerBasisSPolynomial.lean](/home/tom/BEI-lean/BEI/GroebnerBasisSPolynomial.lean)
- [GroebnerBasis.lean](/home/tom/BEI-lean/BEI/GroebnerBasis.lean)

Current state:

- `GroebnerBasisSPolynomial.lean` carries the long Buchberger proof;
- `GroebnerBasis.lean` carries reducedness and the wrapper theorem;
- `theorem_2_1_isReducedGroebnerBasis` exists as a good wrapper.

Cleanup goal:

- make `theorem_2_1_isReducedGroebnerBasis` the obvious public endpoint;
- make the wrapper proof read explicitly as:
  - span;
  - Buchberger;
  - reducedness;
- keep the case explosion inside named support lemmas, not in the public theorem.

Recommended refactor:

- give `GroebnerBasisSPolynomial.lean` explicit section names by case type;
- keep all endpoint/case-factorization lemmas private or clearly marked internal;
- add a short module comment saying exactly which theorem is the public paper-facing one.


## 2. Section 3 dimension and surrogate packaging

File:

- [PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean)

Current state:

- one file now mixes:
  - Corollary 3.3;
  - the equidimensional surrogate versions of Corollaries 3.4 and 3.7;
  - the direct equidimensional route to Proposition 1.6;
  - support lemmas for quotient dimensions and equidimensionality.

Cleanup goal:

- make the public theorem layer read as:
  - dimension formula first;
  - then surrogate corollaries;
  - then the direct surrogate Proposition 1.6 route;
- keep the low-level quotient and equidimensionality support out of the public path.


## 3. Theorem 3.2 narrative

File:

- [PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)

Current state:

- the mathematics is clean, but the file should read more explicitly as:
  - every `P_S` contains `J_G`;
  - every minimal prime is some `P_S`;
  - radicality identifies the intersection.

Cleanup goal:

- make `theorem_3_2` look like a short assembly theorem;
- keep `minimalPrime_eq_primeComponent` and the telescope lemmas as internal support.


## 4. Proposition 3.8 / Corollary 3.9 packaging

File:

- [MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)

Current state:

- the main logic is good;
- the proof reads more operationally than mathematically.

Cleanup goal:

- organize by conceptual steps:
  - containment of components;
  - cut-vertex criterion;
  - minimal-prime conclusion.


## 5. Proposition 1.6 presentation

Files:

- [GroebnerDeformation.lean](/home/tom/BEI-lean/BEI/GroebnerDeformation.lean)
- [Proposition1_6.lean](/home/tom/BEI-lean/BEI/Proposition1_6.lean)

Current state:

- `Proposition1_6.lean` is now the right small public wrapper;
- `GroebnerDeformation.lean` carries the active paper-faithful algebra track;
- the public status is: one remaining sorry in the graded local-to-global step.

Cleanup goal:

- keep `proposition_1_6` visibly paper-facing and short;
- keep `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` as the honest narrow transfer
  wrapper;
- make `GroebnerDeformation.lean` read as:
  - deformation setup;
  - fiber identifications;
  - Gröbner/flatness support;
  - final transfer assembly;
- keep every note exact about what is still open.


## 6. Corollary 1.3 and other paper-statement mismatches

File:

- [GraphProperties.lean](/home/tom/BEI-lean/BEI/GraphProperties.lean)

Cleanup goal:

- for every public theorem whose Lean statement is weaker or differently packaged than the
  paper, add one of:
  - a wrapper theorem;
  - or a short explanatory note.

The theorem should not silently claim more than it proves.


## Refactor checklist per theorem

For each major theorem:

1. Identify the exact paper statement.
2. Decide what the public Lean theorem should be.
3. Move long local argument blocks into helper lemmas named after proof steps.
4. Rewrite the theorem proof as a short assembly.
5. Add a brief comment if the Lean statement is weaker than the paper.


## Anti-patterns to avoid

- leaving the public theorem as a 500-line proof;
- exposing Finsupp arithmetic directly in the public proof;
- mixing statement-audit commentary with heavy algebraic case analysis;
- using long `have` chains where a named lemma would be clearer.


## Definition of done

This guide is complete when the public theorem layer in the main BEI files reads like a
mathematical outline rather than an implementation dump.

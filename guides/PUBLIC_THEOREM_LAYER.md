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

## 1. Theorem 2.1 packaging

File:

- [GroebnerBasis.lean](/home/tom/BEI-lean/BEI/GroebnerBasis.lean)

Current state:

- `theorem_2_1` proves Gröbner-basis-ness;
- `theorem_2_1_reduced` proves reducedness;
- `theorem_2_1_isReducedGroebnerBasis` exists as a good wrapper.

Cleanup goal:

- make `theorem_2_1_isReducedGroebnerBasis` the obvious public endpoint;
- ensure the theorem immediately above it reads as:
  - span;
  - Buchberger;
  - reducedness.

Recommended refactor:

- rename long internal sections by case type;
- keep all endpoint/case-factorization lemmas private;
- add a short module comment saying exactly which theorem is the public paper-facing one.


## 2. Theorem 3.2 narrative

File:

- [PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)

Current state:

- the mathematics is fairly clean;
- but the file should read more explicitly as:
  - every `P_S` contains `J_G`;
  - every minimal prime is some `P_S`;
  - radicality identifies the intersection.

Cleanup goal:

- make `theorem_3_2` look like a short assembly theorem;
- keep `minimalPrime_eq_primeComponent` and the telescope lemmas as internal support.


## 3. Proposition 3.8 / Corollary 3.9 packaging

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


## 4. Corollary 1.3 and other paper-statement mismatches

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

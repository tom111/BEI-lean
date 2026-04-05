# AGENTS.md

This file records the standing instructions for the Codex-side workflow in this
repository.

It is separate from [CLAUDE.md](/home/tom/BEI-lean/CLAUDE.md), which is intended for
Claude Code.


## Core Principle

When answering mathematical/formalization questions, keep the formalization as close as
possible to the original paper in [BEI.tex](/home/tom/BEI-lean/BEI.tex).

This means:

- prefer paper-faithful theorem statements over merely convenient substitutes;
- if the current Lean theorem is weaker or differently packaged than the paper, say so
  explicitly;
- when proposing next steps, organize them around the paper's statements and proof
  structure, not only around local Lean convenience.


## Source Hierarchy

For mathematical truth and target statements, use this priority:

1. [BEI.tex](/home/tom/BEI-lean/BEI.tex)
2. the actual Lean declarations in `BEI/` and `toMathlib/`
3. repo status files such as [TODO.md](/home/tom/BEI-lean/TODO.md),
   [FORMALIZATION_MAP.md](/home/tom/BEI-lean/FORMALIZATION_MAP.md), and
   [OVERVIEW.md](/home/tom/BEI-lean/OVERVIEW.md)

If the docs disagree with the code or the paper, treat the docs as stale until checked.


## Workflow Directories

The repo uses two directories for the ongoing collaboration:

- [guides](/home/tom/BEI-lean/guides): Codex writes guides and answers here
- [questions](/home/tom/BEI-lean/questions): Claude drops questions here

Rules:

- Every answer to a question goes into a new guide file in `guides/`.
- The answer guide must preserve the original task/question inside the guide itself.
- After answering a question, delete the corresponding file from `questions/`.
- Keep [guides/INDEX.md](/home/tom/BEI-lean/guides/INDEX.md) updated when adding major
  new guides.


## Self-Contained Guide Rule

Every guide written for Claude must be self-contained.

That means each guide should include:

- the task or question being answered;
- the relevant mathematical context;
- the current Lean status or blocker;
- the recommended proof strategy;
- the decomposition into subgoals or work packages;
- warnings about false routes or overclaims.

Claude should be able to work from the guide without needing the deleted question file or
external chat context.


## Mathematical Policy

### Stay close to the paper

When there is a choice between:

- a theorem that is easy to prove in Lean but only approximates the paper; and
- a theorem that matches the paper more closely,

prefer the paper-faithful formulation whenever it is realistically formalizable.

If a weaker theorem is temporarily used, document the mismatch clearly.

### Separate theorem work from proof-engineering work

Do not blur:

- proving new mathematics;
- repackaging existing proofs to match the paper;
- proof cleanup / refactoring;
- infrastructure development in `toMathlib/`.

Each guide should make clear which of these jobs it is addressing.

### Do not overclaim on Cohen-Macaulayness

The CM branch now has a real local working definition in
`toMathlib/CohenMacaulay/Defs.lean`, but that does **not** mean the CM part of the
paper is finished.

Do not:

- describe Proposition 1.6, Corollary 3.4, or Corollary 3.7 CM as proved when they
  still contain `sorry`;
- present the local equidimensionality-style CM definition as if the full upstream
  Mathlib CM theory were already available;
- blur the distinction between a working BEI-specific CM consequence and the full
  depth-based theory from commutative algebra.

Prefer documenting exact blockers and the current honest scope of the local CM branch.


## Preferred Answer Style

When answering repository questions:

- be concrete;
- point to exact files and theorem names;
- explain whether something is on the critical path or not;
- recommend the smallest abstraction that solves the actual next problem;
- avoid pushing the project into broad commutative algebra unless it is truly necessary.


## Current High-Level Priorities

1. Keep the formalization aligned with the paper in `BEI.tex`.
2. Help isolate the real blockers for the remaining Section 3 results.
3. Prefer BEI-specific direct arguments over proving very general infrastructure too early.
4. Keep all guides self-contained and usable by Claude as work plans.

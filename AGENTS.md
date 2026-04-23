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

## External Tooling

The repo contains a root-level git submodule:

- [lean4-skills](/home/tom/BEI-lean/lean4-skills): pinned third-party AI tooling / skill repo

It is part of the working environment, but not part of the BEI source tree.

Rules:

- initialize submodules after clone with `git submodule update --init --recursive`;
- do not edit `lean4-skills/` during normal BEI work unless explicitly asked;
- if the submodule is updated, treat that as a separate tooling change and commit it
  separately from theorem or docs work.


## Workflow Directories

The repo uses two collaboration roots:

- [guides](/home/tom/BEI-lean/guides): umbrella directory for Codex-written material
- [questions](/home/tom/BEI-lean/questions): Claude drops questions here

Within `guides/`, the current subdirectories are:

- [guides/work_packages](/home/tom/BEI-lean/guides/work_packages): active Claude work packets
- [guides/answers](/home/tom/BEI-lean/guides/answers): preserved answers to questions
- [guides/cleanup](/home/tom/BEI-lean/guides/cleanup): optional refactor / cleanup packets
- [guides/process](/home/tom/BEI-lean/guides/process): workflow notes
- [guides/website](/home/tom/BEI-lean/guides/website): public-site planning notes
- [guides/archive](/home/tom/BEI-lean/guides/archive): completed or superseded guides

Rules:

- Every answer to a question goes into a new guide file in `guides/answers/`.
- The answer guide must preserve the original task/question inside the guide itself.
- After answering a question, delete the corresponding file from `questions/`.
- Keep [guides/INDEX.md](/home/tom/BEI-lean/guides/INDEX.md) updated when adding,
  moving, or retiring major guides.


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

### Keep Cohen-Macaulay claims precise

The paper-facing Cohen--Macaulay results are now formalized, including
Proposition 1.6, Corollary 3.4, and Corollary 3.7.

Still, keep the layers separate:

- the equidimensional surrogate in `toMathlib/Equidim/Defs.lean` is support
  infrastructure, not a substitute for the paper-facing theorems;
- the local files in `toMathlib/CohenMacaulay/` and related support files are
  BEI-specific infrastructure and backports, not a claim that the full
  commutative-algebra theory has been upstreamed to Mathlib;
- if a Lean theorem is only an equivalent reformulation of the paper, say so
  explicitly rather than implying verbatim agreement.


## Lean Cleanup Guardrails

For any Lean simplification, shortening, refactor, or proof-golf pass:

- use the Lean skill workflow and Lean MCP tools as the default working method;
- require that the whole project still builds cleanly before considering the pass complete;
- require that the whole project still builds cleanly again before each commit;
- never change the statement of any paper-facing theorem under any circumstances unless
  explicitly instructed;
- do not change theorem, lemma, definition, or API statements unless explicitly asked;
- do not introduce new axioms;
- if it is unclear whether a cleanup strategy is correct, stable, or worth pursuing,
  write the questions into a markdown file under [questions](/home/tom/BEI-lean/questions)
  before proceeding.


## Preferred Answer Style

When answering repository questions:

- be concrete;
- point to exact files and theorem names;
- explain whether something is on the critical path or not;
- recommend the smallest abstraction that solves the actual next problem;
- avoid pushing the project into broad commutative algebra unless it is truly necessary.


## Current High-Level Priorities

1. Keep the formalization aligned with the paper in `BEI.tex`.
2. Keep status files, public docs, and instruction files truthful and readable.
3. Keep paper-facing theorems distinct from support infrastructure and cleanup work.
4. Keep all guides self-contained and usable by Claude as work plans.

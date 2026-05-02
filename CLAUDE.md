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

There is no test suite. Correctness is enforced by Lean's type checker, so a successful
`lake build` with no errors is required. Do not treat this file as a live project-status
snapshot; current theorem status belongs in `TODO.md`, `FORMALIZATION_MAP.md`, and the
Lean files themselves.

This repo also contains a root-level git submodule:

- `lean4-skills/` — pinned third-party AI tooling / skill repository used by the local
  agent workflow

After cloning, initialize it with:

```bash
git submodule update --init --recursive
```

Do not edit `lean4-skills/` as part of normal BEI work unless explicitly asked.

## Project Structure

- `BEI/Definitions.lean` — Core mathematical definitions: `BinomialEdgeVars V` (= `V ⊕ V`), notation `x i` and `y i` for the two copies of variables, `binomialEdgeIdeal G`, and `IsClosedGraph G` (Condition (b) of Theorem 1.1 in Herzog et al.)
- `BEI/Groebner.lean` — Term order: defines `binomialEdgeLE` (lex with `x_1 > x_2 > ... > x_n > y_1 > ... > y_n`) and the corresponding `LinearOrder (BinomialEdgeVars V)` instance
- `BEI/MonomialOrder.lean` — Connects the linear order to Mathlib's `MonomialOrder` infrastructure; proves leading term of `f_{ij}` is `x_i · y_j`
- `BEI/GraphProperties.lean` — `IsChordal`, `IsClawFree`, `graphClosure`; Propositions 1.2, 1.4, 1.5, Corollary 1.3
- `BEI/AdmissiblePaths.lean` — `pathMonomial`, `groebnerElement`, `groebnerBasisSet`; admissible path membership
- `BEI/GroebnerAPI.lean` — `IsRemainder`, `IsGroebnerBasis`, Buchberger's criterion (fully proved)
- `BEI/ClosedGraphs.lean` — **Theorem 1.1**: closed graph ↔ quadratic Gröbner basis (fully proved)
- `BEI/GroebnerBasisSPolynomial.lean` — Buchberger / S-polynomial proof of Theorem 2.1
- `BEI/GroebnerBasis.lean` — reducedness half of Theorem 2.1 and the paper-facing wrapper theorem
- `BEI/Radical.lean` — Corollary 2.2 (`J_G` is radical)
- `BEI/PrimeIdeals.lean` — `primeComponent`, `componentCount`; Section 3 prime ideal properties
- `BEI/MinimalPrimes.lean` — Proposition 3.8, Corollary 3.9; minimal prime characterization
- `BEI/PrimeDecomposition.lean` — Theorem 3.2 and Proposition 3.6
- `BEI/PrimeDecompositionDimensionCore.lean` — Corollary 3.3, quotient-dimension lemmas, and the third-isomorphism dimension helper used by every equidimensional surrogate downstream
- `BEI/PrimeDecompositionDimension.lean` — equidimensional surrogate variants of Corollaries 3.4 and 3.7
- `BEI/Prop1_6Equidim.lean` — Example 1.7(b) (path graph) and Proposition 1.6 equidimensional surrogate, plus the shared `isEquidim_of_equidim_minimalPrimes` helper
- `BEI/Corollary3_4.lean` — Corollary 3.4, the connected-case wrapper, and the paper-facing Cohen--Macaulay cycle criterion package for Corollary 3.7
- `BEI/CIIdeals.lean` — Section 4: `CIStatement`, `ciGraph`, `ciIdeal`, `ciGraphSpec`, `ciIdealSpec`, the single-statement and specification bridge theorems, and transferred radicality / prime decomposition / minimal-prime theorems
- `BEI/Equidim.lean` — HH bipartite graph infrastructure, direct-route helpers, and equidimensional support material used by the paper-facing Section 1 and Section 3 results
- `toMathlib/Equidim/Defs.lean` — local backport / working definition for the equidimensional surrogate branch
- `toMathlib/CohenMacaulay/Defs.lean` — local Cohen--Macaulay definitions such as `ringDepth`, `IsCohenMacaulayLocalRing`, and `IsCohenMacaulayRing`
- `toMathlib/CohenMacaulay/Basic.lean` — basic quotient and regular-sequence transfer lemmas for the local CM development
- `toMathlib/CohenMacaulay/Localization.lean` — localization, unmixedness, and local-to-global CM transfer lemmas used in the BEI proofs
- `toMathlib/CohenMacaulay/Polynomial.lean` — polynomial-ring Cohen--Macaulay lemmas and backported support used by the Section 1 and Section 3 arguments
- `toMathlib/IntegralDimension.lean` — integral and finite-extension dimension lemmas
- `toMathlib/FiniteFreeEquidim.lean` — flat / finite / finite-free equidimensional support lemmas
- `toMathlib/GradedEquidim.lean` — graded equidimensional and local-to-global support for the Section 3 CM dimension argument
- `toMathlib/MonomialIdeal.lean` — monomial ideals in `MvPolynomial`, variable-generated prime ideals, the prime classification for monomial ideals, `coeff_pow_lexMax`, `radical_isMonomial`, the full primary monomial ideal characterization (`isPrimary_iff`), and supporting structural lemmas
- `toMathlib/SquarefreeMonomialPrimes.lean` — variable-pair ideals (edge ideals), vertex covers, and minimal prime ↔ minimal vertex cover classification
- `toMathlib/HeightVariableIdeal.lean` — quotients by variable ideals, quotient equivalences, and Krull-dimension formulas used in the Proposition 1.6 CM branch
- `scripts/generate_repo_stats.py` — computes code-size and git-history statistics for `docs/_data/repo_stats.json`, which is used by the homepage
- `lean4-skills/` — root-level submodule pinning the external Lean AI skill/tooling repo used by the local workflow
- `BEI.lean` — Root library entry point
- `BEI.tex` — Reference paper with the mathematical content being formalized
- `TODO.md` / `FORMALIZATION_MAP.md` — human-facing status docs that must be updated whenever theorem status or file layout changes
- `guides/` — umbrella directory for self-contained agent guides and workflow notes
  - `guides/work_packages/` — active Claude-facing work packets; may be empty when no theorem-critical packet is active
  - `guides/answers/` — preserved answers / decision memos
  - `guides/cleanup/` — optional refactor and proof-cleanup packets
  - `guides/process/` — workflow notes
  - `guides/website/` — public-site planning notes
  - `guides/archive/` — completed or superseded guides
- `questions/` — incoming worker questions; preserve question context in any answer guide before deleting the question file

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

## Status-Tracking Rule

- Treat `BEI.tex` and the Lean files as the source of truth.
- If a theorem is finished, moved, split across files, or downgraded from an earlier claim, update `TODO.md` and `FORMALIZATION_MAP.md` in the same round.
- Do **not** put project state snapshots in this file — they go stale immediately. Current state belongs in `TODO.md`, `FORMALIZATION_MAP.md`, and the Lean code itself.
- Keep paper-facing theorems such as Proposition 1.6, Corollary 3.4, and Corollary 3.7 distinct from auxiliary equidimensional support lemmas and `toMathlib` infrastructure.
- `OVERVIEW.md`, `NEXT_STEPS_PLAN.md`, and the public `docs/` pages should stay reader-facing; avoid turning them into internal blocker logs.

## Worker Routine

When starting fresh on a task:

1. Read the relevant paper statement in `BEI.tex`.
2. Read the live Lean declaration and nearby helper lemmas.
3. Read the matching file in `guides/work_packages/` first, then in the other `guides/`
   subdirectories if the task is an answer, cleanup packet, or process note.
4. Restrict work to the requested theorem / file / branch before expanding scope.

Do not start by rewriting unrelated proofs, reorganizing files, or updating docs unless the
task actually requires that.

## Scope Discipline

- Prefer finishing one local mathematical objective over making partial edits across several branches.
- Keep theorem work, proof-engineering cleanup, and documentation cleanup separate unless they are tightly coupled.
- If a proof attempt becomes monolithic or brittle, factor it into private helper lemmas instead of continuing to patch one giant term.
- Treat scratch files and abandoned proof attempts as references, not as canonical code to preserve.

## Guides And Questions

- If a relevant guide exists in `guides/`, use it first.
- Guides should be self-contained and should preserve the original question context.
- If blocked, write a focused question in `questions/` about one exact sublemma or API issue, not a broad project-status note.
- After a question is answered in a new guide under `guides/answers/`, the corresponding question file should be deleted.
- If a guide has been fully carried out and is no longer needed, move it to `guides/archive/`.
- When archiving a completed guide, also update `guides/INDEX.md` so the guide list stays truthful.

## After Finishing A Guide

When a guide-driven task is genuinely finished, the worker should do the associated cleanup
in the same round when appropriate:

1. remove or mark complete the guide that has been fully consumed;
   Prefer moving it to `guides/archive/` rather than deleting it.
2. update `guides/INDEX.md`;
3. update `TODO.md` and `FORMALIZATION_MAP.md` if theorem status or file location changed;
4. update `CLAUDE.md` only if the standing workflow or file structure changed;
5. delete any answered question file from `questions/`;
6. if the resulting state is stable and truthful, commit that secured progress to git instead of leaving it only in the worktree.

Do not keep obsolete guides around if they now misrepresent the active work.

## Change Discipline

- Do not touch unrelated active branches just because they are nearby.
- Do not update status files or public docs in the middle of a proof attempt unless theorem status or file layout has actually changed.
- Before introducing a broad abstraction, check whether a smaller BEI-specific lemma is enough.
- Commit secured progress in small honest commits. Do not bundle broken proof attempts, speculative cleanup, or stale status updates into the same commit as finished work.

## Lean Cleanup Guardrails

- Use the Lean skill workflow and Lean MCP tools as the default method for cleanup and proof-golf work.
- For any simplification, shortening, refactor, or proof-golf pass, require that the whole project still builds cleanly before treating the pass as complete.
- Before each commit, require that the whole project still builds cleanly.
- Never change the statement of any paper-facing theorem unless explicitly instructed.
- Do not change theorem, lemma, definition, or exported API statements during cleanup work unless explicitly instructed.
- Do not introduce new axioms during cleanup work.
- If it is unclear whether a cleanup strategy is sound, stable, or worth pursuing, write the open questions into a markdown file under `questions/` before proceeding.

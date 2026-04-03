# Next Steps Plan for the BEI Formalization

## Purpose

This document is a concrete plan for how to continue the formalization of
Herzog–Hibi–Hreinsdóttir–Kahle–Rauh on binomial edge ideals in Lean 4.

The goal is not just to remove more `sorry`s. The goal is to:

1. make the existing claims line up more faithfully with the paper;
2. finish the mathematically accessible remaining results;
3. isolate genuine Mathlib gaps from local project gaps; and
4. keep the codebase in a form that an LLM can reliably extend.


## Current Situation

The project already has strong coverage of the core algebra-combinatorics:

- Theorem 1.1 is formalized.
- Theorem 2.1 is formalized, with reducedness split into a separate theorem.
- Corollary 2.2 is formalized.
- Theorem 3.2 is formalized.
- Lemma 3.1 is formalized.
- Proposition 3.6, Corollary 3.7 (prime part), Proposition 3.8, and Corollary 3.9 are formalized.

The remaining gaps fall into three different classes:

- faithful-statement gaps: the repo sometimes proves a nearby structural result rather
  than the exact paper statement;
- project-local proof gaps: the result should be finishable inside the current project;
- infrastructure gaps: the missing result depends on commutative algebra machinery that
  Mathlib does not yet provide.

The next work should be organized around those classes rather than by file alone.


## Guiding Principles

### 1. Separate mathematical progress from statement hygiene

Do not mix "prove a new theorem" with "fix the paper-to-Lean correspondence" in the
same session unless the fix is tiny. These are different jobs.

- Mathematical progress means adding new lemmas and proofs.
- Statement hygiene means checking whether the declaration actually matches the paper.

The corollary 1.3 mismatch is the model example: the current theorem is useful and
correct, but it is weaker than the paper's statement and should be documented as such.

### 2. Prefer exact paper statements once the infrastructure exists

If a result is already almost present, add a wrapper theorem matching the paper's
statement instead of continuing to advertise a nearby variant.

Examples:

- Corollary 1.3 should ideally exist in a paper-faithful form.
- Theorem 2.1 should ideally have a single wrapper theorem saying the admissible-path
  set is a reduced Gröbner basis, even if internally it still uses the split
  `theorem_2_1` plus `theorem_2_1_reduced`.

### 3. Keep the "LLM steering surface" small and current

The model does better when the repo has one canonical source of truth per topic.

That means:

- one canonical status file;
- one theorem map;
- one proof-plan file per genuinely difficult theorem;
- no stale progress counts;
- no contradictory claims across docs.

### 4. Push generic commutative algebra to `toMathlib/`

Any lemma whose statement does not mention binomial edge ideals should go to
`toMathlib/` or at least be written in that style. This has two advantages:

- the project files stay focused on the paper;
- the model can reason locally about whether a missing step is "BEI-specific" or "a
  generic infrastructure issue".


## Priority Order

## Priority 0: Statement audit and wrapper theorems

This should happen first, because it affects the reliability of every future status
claim.

### Goal

Bring the public-facing theorem layer into closer alignment with the paper, even if the
internal proof architecture stays the same.

### Tasks

1. Audit every theorem currently marked "done" against the exact paper statement.
2. Add short comments wherever the Lean theorem is intentionally weaker or differently
   packaged.
3. Add wrapper theorems when the exact paper statement is already derivable from current
   results.

### Immediate targets

#### Corollary 1.3

Current state:

- the code proves `bipartite ∧ closed → acyclic ∧ degree ≤ 2`;
- the paper states "bipartite graph is closed iff it is a line".

Plan:

1. Leave the current theorem in place.
2. Add a graph-level predicate representing "is a path graph" or "is a line", if the
   project does not already have an adequate notion.
3. Prove the forward direction under a connectedness assumption:
   `Connected G → bipartite G → IsClosedGraph G → IsLineGraph G`.
4. Decide whether to formalize the converse only for the natural labeling, or to leave
   it as documentation if it depends too much on representation choices.

This is valuable because it cleans up a known mismatch without touching heavy algebra.

#### Theorem 2.1 packaging

Current state:

- `theorem_2_1` proves Gröbner-basis-ness;
- `theorem_2_1_reduced` proves pairwise non-division of leading monomials.

Plan:

Add a wrapper theorem saying that the admissible-path family is a reduced Gröbner basis,
using the existing split proof. The wrapper should match the paper's phrasing as closely
as Mathlib's API allows.

### Deliverable

A short "paper-faithful status" section in the docs that distinguishes:

- exact match;
- equivalent reformulation;
- weaker formalized substitute.


## Priority 1: Finish the dimension corollaries if possible

The main open paper statements that still matter mathematically are the Section 3
dimension corollaries.

### Targets

- Corollary 3.3: `dim S / J_G = max_S ((n - |S|) + c(S))`
- the lower-bound statement `dim ≥ n + c(G)`
- Corollary 3.4 if possible, though it is probably blocked by Cohen–Macaulay
  infrastructure

### Why this is the best next mathematical target

- The prime decomposition is already done.
- Lemma 3.1 is already done.
- The missing statements are central to Section 3.
- This is the place where the current formalization stops feeling incomplete.

### Risk

The docs already note a likely catenary / dimension-theory gap. That may be real.
Before trying to prove Corollary 3.3 directly, first determine whether the missing link
is:

- a local lemma about Krull dimension and prime decomposition;
- a missing equality between quotient dimension and heights of minimal primes;
- or a genuinely unavailable general theorem in Mathlib.

### Recommended approach

#### Phase 1: isolate the exact missing commutative algebra lemma

Do not attack Corollary 3.3 in-line. First create a local note or `toMathlib/`
prototype identifying the exact abstract statement needed.

The likely shape is something like:

- for a Noetherian ring `R` and radical ideal `I`,
  `krullDim (R ⧸ I)` is the supremum of the dimensions of `R ⧸ P` over minimal primes
  `P` above `I`;
- in a polynomial ring over a field, this becomes a formula in terms of heights.

If such a theorem is already in Mathlib under a non-obvious name, use it.
If not, isolate a minimal substitute theorem that is sufficient for this project.

#### Phase 2: prove the quotient-dimension formula in the BEI setting

Exploit the very special structure of `P_S(G)`.

Potential route:

1. Express `primeComponent G S` as a sum of ideals in disjoint variable sets.
2. Use the already-proved height formulas for the variable ideal part and complete-graph
   determinantal part.
3. Relate quotient dimension to the explicit surviving-variable count instead of relying
   on the most general catenary theorem.

This is often better than trying to import full abstract commutative algebra.

#### Phase 3: derive Corollary 3.3_lower_bound as an easy corollary

Once the max formula exists, the lower bound should be immediate by evaluating at
`S = ∅`.

### Decision rule

Spend at most one focused session trying to locate an abstract Mathlib path.
If the blocker really is foundational, switch to proving a BEI-specific quotient
dimension lemma directly.


## Priority 2: Clean up the Cohen–Macaulay branch

The CM material is currently the least honest part of the repository, because it uses a
placeholder definition:

- `IsCohenMacaulay` is currently defined by `sorry`.

This is acceptable as a temporary marker, but not as a theorem-bearing foundation.

### Goal

Make the CM branch explicitly quarantined so that it does not contaminate the status of
the rest of the project.

### Plan

1. Keep all CM-dependent results grouped in `CohenMacaulay.lean` and explicit corollary
   stubs.
2. Mark every theorem depending on the placeholder definition clearly in docstrings.
3. Avoid proving further downstream statements from the fake definition unless the goal
   is purely organizational.
4. If Mathlib still lacks a usable CM notion, prefer one of these two options:
   - leave the CM results as documented future work;
   - or move them behind a clearly-named local axiom file so the dependency is explicit.

### Important discipline

Do not let the placeholder `IsCohenMacaulay` appear to be a completed formalization.
The rest of the project is strong enough that it should not be diluted by one fake
predicate.


## Priority 3: Simplify and stabilize the Section 3 infrastructure

Section 3 now has substantial proof mass, especially around heights, prime components,
and minimal primes. That makes it the area most likely to regress or become unreadable.

### Goal

Refactor the infrastructure so that a future model can continue from it reliably.

### Tasks

1. Identify long proof blocks in `PrimeIdeals.lean` that should be split into named
   helper lemmas.
2. Separate "height-chain construction" from "BEI application" more aggressively.
3. Move generic ring-theoretic lemmas out of `BEI/`.
4. Add module headers listing the exact paper results proved in each file.

### Specific opportunities

#### `PrimeIdeals.lean`

This file is doing too much:

- defining prime components;
- proving primality;
- proving height formulas;
- carrying kernel-chain constructions.

Recommended split:

- `PrimeComponentDefs.lean`
- `PrimeComponentPrime.lean`
- `PrimeComponentHeight.lean`

Only do this if it improves maintainability without breaking imports too badly.
If not, at least add section headers and a file-level roadmap.

#### `toMathlib/HeightAdditivity.lean`

This file still has open gaps and recent commits already discovered that at least one
candidate theorem statement was false. That is a signal to proceed carefully.

Plan:

1. Treat every remaining theorem there as suspect until checked against explicit
   counterexamples.
2. Narrow statements to what is actually needed by the BEI development.
3. Avoid building long chains of speculative infrastructure lemmas on top of unverified
   abstract statements.


## Priority 4: Bring the docs into a single consistent state

Right now the code is better than the docs. That is a good problem to have, but it still
hurts LLM performance.

### Problems to fix

- `OVERVIEW.md` and `TODO.md` disagree on counts and status details.
- some comments describe the exact paper theorem while the code proves a weaker form;
- old archived approaches remain in the tree and can confuse the model.

### Plan

1. Choose one canonical progress file. `TODO.md` is the natural candidate.
2. Make `OVERVIEW.md` a short executive summary only.
3. Add a "paper statement vs Lean statement" column for theorems whose packaging differs.
4. Move archival material like `RauhApproach.lean` behind a stronger warning banner, or
   out of the main narrative.

### Recommended doc structure

- `README.md`: one-paragraph project description and build instructions.
- `TODO.md`: canonical theorem status.
- `FORMALIZATION_MAP.md`: paper statement, Lean statement, file, status, fidelity notes.
- theorem-specific proof plans only for genuinely hard results.


## Priority 5: Prepare for small upstream contributions

The project is now mature enough that upstreaming some generic lemmas is worth doing.

### Best candidate

Variable-ideal results in `toMathlib/HeightVariableIdeal.lean` and the polished PR
candidate in `toMathlib/IsPrimeSpanX.lean`.

### Why upstream now

- these lemmas are generic;
- they have already stabilized;
- upstreaming reduces local technical debt;
- it clarifies which remaining gaps are truly project-specific.

### Strategy

1. Upstream only one small theorem family at a time.
2. Do not wait for the whole BEI project to finish.
3. Keep the BEI repo as the proving ground, then copy and polish into Mathlib style.


## Suggested Work Packages

The following work packages are designed to be manageable for an LLM-assisted workflow.

### Work Package A: Paper-faithful wrappers

Scope:

- audit done statements;
- add comments for mismatches;
- add wrapper theorems for exact paper phrasing when easy.

Definition of done:

- every theorem marked done is classified as exact/equivalent/weaker;
- corollary 1.3 mismatch is documented;
- theorem 2.1 has a paper-style wrapper.

### Work Package B: Dimension-corridor investigation

Scope:

- isolate the exact missing abstract lemma behind Corollary 3.3;
- either prove it locally or prove a BEI-specific substitute.

Definition of done:

- either Corollary 3.3 is proved, or there is a precise written blocker theorem
  explaining why not.

### Work Package C: Height-additivity triage

Scope:

- review the remaining `sorry`s in `toMathlib/HeightAdditivity.lean`;
- eliminate false conjectural statements;
- reduce the file to trustworthy infrastructure.

Definition of done:

- every remaining theorem is either proved, narrowed, or explicitly marked unnecessary.

### Work Package D: Documentation unification

Scope:

- reconcile `OVERVIEW.md`, `TODO.md`, and theorem comments;
- add a formalization map.

Definition of done:

- no contradictory status claims remain in the repo.


## Recommended Session Order for Claude

If Claude continues on this project, the highest-value order is:

1. finish the statement audit and add missing comments/wrappers;
2. investigate the exact blocker for Corollary 3.3;
3. either prove Corollary 3.3 or record the precise missing abstract theorem;
4. clean `toMathlib/HeightAdditivity.lean`;
5. unify documentation;
6. only then revisit Section 4 or the Cohen–Macaulay branch.

This ordering is important. Section 4 depends on the algebraic backbone being stable,
and the CM branch is currently downstream of missing infrastructure.


## Tactics for LLM-Guided Formalization

### For difficult theorems, write a theorem-specific proof plan first

Before asking the model to prove a hard theorem, create a short markdown note with:

- exact target statement;
- dependencies already proved;
- the expected high-level proof structure;
- known false approaches;
- the names of the helper lemmas likely needed.

This is especially important for:

- Corollary 3.3;
- any dimension / height comparison result;
- any future Section 4 algebra-statistics bridge.

### Keep counterexamples in the repo when a conjectured helper theorem fails

The recent `HeightAdditivity` correction is the right pattern. When an attempted general
lemma is false, preserve the failure as documentation rather than silently changing the
statement.

### Prefer proving small interface lemmas over growing giant proofs

When a proof exceeds what the model can stably carry in one pass, stop and extract a
named lemma with a narrow statement. This is especially important in Lean because:

- local context gets large quickly;
- long tactic proofs are fragile;
- smaller theorem names improve future retrieval.


## Concrete Next Milestone

The best next milestone is:

**Milestone: paper-faithful Section 1/2 statements plus a decisive Corollary 3.3
investigation**

This milestone is successful if all of the following are true:

- every done theorem in Sections 1 and 2 is labeled exact/equivalent/weaker;
- corollary 1.3 is clearly documented as weaker than the paper statement;
- theorem 2.1 has paper-style packaging;
- the exact blocker for Corollary 3.3 is identified in a theorem-sized statement;
- either Corollary 3.3 is proved, or the blocker is written down precisely enough to
  target in `toMathlib/`.


## What Not To Do Next

Avoid the following as the immediate next move:

- spending a long session on Section 4 before Section 3 is stable;
- building more CM results on top of the placeholder `IsCohenMacaulay`;
- adding broad new abstractions unless they are clearly needed by a current theorem;
- trusting old progress summaries without re-checking the declarations;
- trying to solve all remaining gaps in one pass.


## Final Recommendation

The project is already past the "toy formalization" stage. The best path forward is not
to chase the remaining `sorry`s blindly. The right strategy is:

1. make the public theorem layer faithful to the paper;
2. concentrate on Section 3 dimension results;
3. quarantine the CM placeholder branch;
4. upstream stable generic lemmas;
5. keep the documentation synchronized with the actual declarations.

If that discipline is maintained, Claude should be able to continue making real progress
without the repo drifting into a misleading state.

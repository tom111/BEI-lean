# Git History Timeline

## Task

Prepare a markdown file from the entire git history that records:

- what happened when;
- what the major obstacles were;
- when the main breakthroughs happened.

This guide is based on the full repository history from `2026-02-17` through
`2026-04-10` (`244` commits total).


## Scope And Reading Rule

This is a project-history guide, not a theorem-status file. It summarizes the
commit history by phase, with emphasis on mathematically meaningful milestones,
proof-engineering blockers, and changes in project direction.

It intentionally does **not** list every doc-sync or cleanup commit separately
unless that commit changed the project's scope, honesty policy, or critical
path.


## One-Paragraph Summary

The project started as a clean scaffold with paper-faithful theorem statements,
then spent most of March turning the Section 1 and Section 2 Gröbner story from
stubs into actual proofs. The dominant technical obstacle in the middle of the
history was Theorem 2.1, whose Buchberger/S-polynomial proof repeatedly forced
new covered-walk and admissible-path infrastructure. Once that barrier fell on
`2026-03-28`, the project moved quickly through Section 3: prime decomposition,
minimal primes, height formulas, and the dimension formula. Early April then
split into two parallel narratives for Proposition 1.6: a successful direct
equidimensional proof, and a more honest long-term restart of the genuinely
Cohen-Macaulay route, with the surrogate layer renamed and separated from the
new real-CM foundation files.


## Timeline

| Date(s) | What happened | Main obstacle | Breakthrough |
| --- | --- | --- | --- |
| `2026-02-17` to `2026-02-25` | Repository bootstrapped; paper scaffold added; early graph, prime-ideal, and minimal-prime lemmas proved. | The repo initially had theorem skeletons with many `sorry`s and some definitions/statements still needed correction. | The project established paper-faithful theorem files early instead of drifting into ad hoc local lemmas. |
| `2026-02-27` to `2026-03-09` | Section 1 was repaired and proved: monomial order fixed, `prop_1_4` corrected and proved, `cor_1_3` finished, real Gröbner API imported, and Theorem 1.1 proved. | A real monomial-order instance bug and the replacement of the fake Gröbner-basis stub with an actual Buchberger setup. | `2026-03-09`: `Theorem 1.1` (`closed graph ↔ Gröbner basis`) reached `0 sorries` in `BEI/ClosedGraphs.lean`. |
| `2026-03-10` to `2026-03-28` | The project attacked Theorem 2.1 in earnest: S-polynomial cases, covered-walk reductions, telescope arguments, and coprime cases. | This was the hardest proof-engineering bottleneck in the entire history: the proof kept exploding into walk decomposition, divisibility, and remainder lemmas. | `2026-03-28`: Theorem 2.1 was fully proved after the mixed-walk and coprime-case machinery finally landed. |
| `2026-03-29` to `2026-04-02` | With Section 2 complete, work pivoted to Section 3: `Cor 2.2`, `Thm 3.2`, `Cor 3.9`, `Prop 3.6`, variable-ideal heights, determinantal heights, and `Lemma 3.1`. | Section 3 needed missing commutative-algebra infrastructure, especially height computations and additivity. | `2026-04-02`: `Lemma 3.1` was fully proved, giving the key height formula `height(P_S) = |S| + n - c(S)`. |
| `2026-04-02` to `2026-04-04` | The dimension layer was built: quotient-dimension lemmas, upper/lower bounds for `dim(R/P_S)`, and full proof of `Cor 3.3`. | A false route was discovered in transferred primality, and the last residue in `Cor 3.3` became a Lean cast/sup compatibility issue after the real mathematics was already done. | `2026-04-02`: the bug `isPrime_transferred is FALSE` was documented instead of being patched over; `2026-04-04`: `Cor 3.3` was fully proved. |
| `2026-04-04` to `2026-04-06` | The repo completed most remaining Section 3 and all of Section 4: real `IsCohenMacaulay` definition replaced the placeholder, `Cor 3.4`, `Cor 3.7`, and the CI-ideal bridge theorems were proved, and monomial-ideal classification work accelerated. | The main difficulty was keeping the CM claims honest while still extracting usable consequences from local infrastructure. | `2026-04-06`: the repo had a working Section 3/4 theorem layer, including `Cor 3.4`, the CM branch of `Cor 3.7`, and the Section 4 CI transfer package. |
| `2026-04-07` to `2026-04-10` | Proposition 1.6 split into two tracks: a direct equidimensional proof succeeded, while the repo simultaneously separated that surrogate from a new real Cohen-Macaulay foundation layer. | The core obstacle became conceptual honesty: the direct proof was enough for a BEI-specific consequence, but not the same as the paper's CM route. | `2026-04-08` and `2026-04-09`: direct `Prop 1.6` was proved; `2026-04-09` to `2026-04-10`: the surrogate was renamed to `Equidim`, and the first genuine files `toMathlib/CohenMacaulay/Defs.lean` and `Basic.lean` were added. |


## Detailed Phase Narrative

### 1. Bootstrap And Paper Scaffold (`2026-02-17` to `2026-02-25`)

The repository began with a minimal Lean project on `2026-02-17`
(`Getting started`). Two days later, the project already had:

- `BEI/Definitions.lean`;
- `BEI/Groebner.lean`;
- `CLAUDE.md`;
- and then the full theorem scaffold in `BEI/AdmissiblePaths.lean`,
  `BEI/ClosedGraphs.lean`, `BEI/GroebnerBasis.lean`,
  `BEI/PrimeIdeals.lean`, `BEI/PrimeDecomposition.lean`,
  `BEI/MinimalPrimes.lean`, and the original `BEI/CohenMacaulay.lean`.

This early decision mattered: the project committed to paper-shaped theorem
statements immediately, instead of first building a disconnected API.

Early obstacles in this phase:

- `IsClosedGraph` needed correction on `2026-02-20`; the original condition was
  vacuously wrong on graphs with edges.
- `IsChordal` also needed repair on `2026-02-25`; the earlier walk-based
  definition was wrong for `K₄`.
- The minimal-prime side already exposed a mathematical false route:
  `componentCount_mono` and `componentCount_insert_le` were removed on
  `2026-02-25` because they were simply false.

First breakthroughs:

- `graphClosure` properties, `closedGraph_isClawFree`, and
  `binomialEdgeIdeal_le_primeComponent` were proved on `2026-02-20`.
- `primeComponent_empty_connected`, `minimalPrimes_finite`, and the backward
  direction of `prop_3_8` landed on `2026-02-25`.
- `BEI.tex` and the published paper PDF were added on `2026-02-26`, giving the
  project a stable mathematical reference point inside the repo.


### 2. Section 1 Repair And Theorem 1.1 (`2026-02-27` to `2026-03-09`)

This phase repaired the front end of the formalization and replaced fake
infrastructure with real Gröbner machinery.

Major obstacle 1: monomial order instance diamond.

On `2026-02-27`, the commit `Fix monomial order instance diamond; prove fij
leading term lemmas` identified a genuine typeclass/design bug:

- `BinomialEdgeVars V := V ⊕ V` had been an `abbrev`, hence transparent;
- Lean could see incompatible order instances through the sum type;
- this broke the intended lex order needed for leading terms.

The fix was structural, not cosmetic:

- change `BinomialEdgeVars` from `abbrev` to opaque `def`;
- add explicit instances;
- align the term order with the paper:
  `x_1 > x_2 > ... > x_n > y_1 > ... > y_n`.

Major obstacle 2: some early theorem statements were not yet paper-accurate.

On the same day, the project corrected:

- `prop_1_4`, replacing a tautological statement with the real shortest-walk
  characterization of closed graphs;
- `cor_1_3`, replacing a weak or mispackaged version with the exact
  bipartite+closed characterization.

From `2026-02-28` through `2026-03-04`, the project completed those repairs:

- `prop_1_4` fully proved on `2026-02-28`;
- `cor_1_3` acyclicity proved on `2026-03-04`;
- `GraphProperties.lean` reached `0 sorries`.

Major obstacle 3: the original Gröbner-basis layer was too fake to support the
paper.

On `2026-03-05`, the commit `Port Gröbner API from groebner_proj; replace stub
IsGroebnerBasis` was a clear turning point. Before this, the repo still had a
local stub notion of Gröbner basis. After this commit, the project switched to
an actual Buchberger framework in `BEI/GroebnerAPI.lean`.

Breakthrough of the phase:

- `2026-03-09`: `Prove Theorem 1.1: closed graph ↔ Gröbner basis
  (0 sorries in ClosedGraphs.lean)`.

This was the first major theorem-level closure point: Section 1 stopped being a
placeholder story and became a real formalized result.


### 3. Theorem 2.1 Bottleneck (`2026-03-10` to `2026-03-28`)

This was the central obstacle of the repository's first two months.

The proof of reduced Gröbner basis structure in `BEI/GroebnerBasis.lean` did
not yield to a short direct argument. Instead it forced the project to build a
large amount of specialized infrastructure:

- path-monomial splitting lemmas;
- squarefreeness and leading-monomial control;
- covered-walk construction;
- telescoping and walk-splitting arguments;
- coprime-case decomposition;
- mixed-walk remainder lemmas.

The history shows repeated restructurings rather than smooth linear progress:

- `2026-03-10` to `2026-03-16`: case structures, `D`-bounds, bihomogeneity, and
  crossing-existence machinery;
- `2026-03-21`: explicit pivot from the Rauh approach to a Herzog direct proof;
- `2026-03-24`: very heavy checkpoint day with eleven commits focused almost
  entirely on internal walk/remainder architecture;
- `2026-03-25` to `2026-03-26`: telescope cases and coprime cases decomposed
  into manageable packets;
- `2026-03-28`: `isRemainder_fij_of_mixed_walk` landed, then the remaining
  coprime sorries were filled.

Main obstacles in this phase:

- repeated proof explosion from each S-polynomial case into many local
  combinatorial subclaims;
- high dependency between walk combinatorics and monomial divisibility;
- instability of proof strategy, especially before the Herzog direct proof
  became the chosen route.

Main breakthroughs:

- `2026-03-21`: the project stopped trying to force the Rauh route and moved it
  into a separate file, reducing strategic ambiguity.
- `2026-03-25`: Cases 4 and 5 were completed, meaning the shared-endpoint
  telescope machinery finally stabilized.
- `2026-03-28`: `complete theorem 2.1 coprime case: all 5 sorries filled`.
- `2026-03-28`: `update TODO: theorem 2.1 fully proved`.

This is the single clearest "wall, then breakthrough" pattern in the history.


### 4. Section 3 Acceleration (`2026-03-29` to `2026-04-02`)

As soon as Theorem 2.1 was done, the history sped up.

On `2026-03-29`, the project immediately converted the Gröbner progress into:

- `Cor 2.2`;
- `Thm 3.2`;
- minimal-prime characterization work;
- and a full paper-to-formalization planning update.

Then the repository moved into the algebraic heart of Section 3:

- `2026-03-30`: `Prop 3.6`, the prime branch of `Cor 3.7`, and the first
  dedicated `toMathlib/` support files for Lemma 3.1;
- `2026-03-30` to `2026-03-31`: variable-ideal height bounds and determinantal
  ideal heights;
- `2026-03-31` to `2026-04-02`: the height-additivity proof and the full proof
  of `Lemma 3.1`.

Major obstacle:

- the theorem statements themselves were clear from the paper, but the repo did
  not yet have the commutative-algebra infrastructure to express or prove the
  height formulas cleanly.

Breakthrough:

- `2026-04-02`: `prove lemma_3_1: 0 sorries (height(P_S) = |S| + n - c(S))`.

This was a critical mathematical unlock. Once the height formula existed, the
dimension formulas and unmixed/CM consequences became realistic.


### 5. Dimension Formula And Honest Bug Discovery (`2026-04-02` to `2026-04-04`)

This short phase produced one of the healthiest moments in the history: an
important false statement was identified and documented instead of hidden.

On `2026-04-02`, the commit `document bug: isPrime_transferred is FALSE
(counterexample added)` recorded that a tempting transfer lemma for primality
was actually wrong. That mattered for two reasons:

- it prevented the repo from quietly building on a false infrastructure lemma;
- it forced the later dimension work to stay mathematically honest.

At the same time, the project pushed hard on quotient dimension:

- `ringKrullDim_quotient_radical`;
- upper and lower bounds for `ringKrullDim_quot_primeComponent`;
- dimension-chain infrastructure;
- graph lemmas needed for cycle cases;
- and then `Cor 3.3`.

Main obstacle:

- after the mathematical lower/upper-bound argument was mostly solved, the last
  blocker in `Cor 3.3` was a Lean packaging issue about casts and `iSup`
  compatibility rather than a missing idea.

Breakthrough:

- `2026-04-04`: `PROVE corollary_3_3: dimension formula FULLY PROVED
  (0 sorries)`.

This is a textbook example of the repo's pattern: a real mathematical proof
followed by a smaller but stubborn formal packaging obstacle.


### 6. Section 3 Closure, Section 4, And Monomial-Ideal Expansion (`2026-04-04` to `2026-04-07`)

This was the period of highest commit density:

- `39` commits on `2026-04-03`;
- `24` on `2026-04-04`;
- `10` on `2026-04-05`;
- `28` on `2026-04-06`;
- `18` on `2026-04-07`.

Several strands moved in parallel.

First strand: the repo replaced the placeholder CM definition.

- `2026-04-04`: `replace IsCohenMacaulay placeholder with real definition`.
- The follow-up commits immediately fixed an over-weak or trivialized
  `IsCohenMacaulayRing` packaging issue and re-synced the status docs.

Second strand: the theorem layer for Sections 3 and 4 closed rapidly.

- `2026-04-05`: finish the unmixed branch of `Cor 3.7`;
- `2026-04-05`: prove `complete_is_CM` and `path_is_CM`;
- `2026-04-05` to `2026-04-06`: build the Proposition 1.6 algebraic reduction;
- `2026-04-06`: prove `Cor 3.4`;
- `2026-04-06`: prove the CM branch of `Cor 3.7`;
- `2026-04-06`: complete Section 4 CI ideal transfer theorems.

Third strand: monomial-ideal support theory expanded quickly.

Between `2026-04-06` and `2026-04-07`, the repo added:

- `IsMonomial` API;
- radical-of-monomial-ideal results;
- prime classification;
- primary characterization (`isPrimary_iff`);
- squarefree monomial prime API.

Major obstacle:

- the repo needed to avoid overstating what "CM" now meant, because some
  results were BEI-specific consequences while the general CM infrastructure was
  still thin.

Breakthroughs:

- `2026-04-06`: the theorem layer for most of Section 3 and all of Section 4
  became available in Lean.
- `2026-04-07`: monomial-ideal classification reached a mature enough state to
  support later Prop. 1.6 work.


### 7. Proposition 1.6 Splits Into Two Narratives (`2026-04-07` to `2026-04-10`)

This is the most conceptually important phase after Theorem 2.1.

There are two distinct stories here.

#### 7A. Direct Equidimensional Proposition 1.6

The repo found a direct BEI-specific route to the Proposition 1.6 consequence.

The key commits were:

- `2026-04-07`: `Advance Prop 1.6 dimension and CM reductions`;
- `2026-04-08`: `Prove Proposition 1.6 via direct equidimensionality
  (0 sorries)`;
- `2026-04-09`: `Finish direct Prop 1.6 equidim proof`.

The direct proof used:

- interval behavior of edges in closed graphs;
- convexity of components of `G[V \ S]`;
- `c(S) ≤ |S| + 1`;
- and then equality for minimal-prime sets via the cut-vertex description.

Breakthrough:

- the repo no longer needed to wait for full paper-faithful CM infrastructure to
  recover a strong BEI consequence for connected closed graphs.

But this created a new honesty problem:

- the theorem obtained was an equidimensional surrogate consequence, not yet the
  same thing as the paper's genuine Cohen-Macaulay route.

#### 7B. Honest Separation Of Surrogate And Real CM Work

The history then corrected the narrative instead of blurring it.

Key commits:

- `2026-04-09`: `Refactor CM surrogate layer to equidim`;
- `2026-04-09`: `Add first real Cohen-Macaulay foundation file`;
- `2026-04-10`: `Add basic regular-quotient CM lemmas`;
- `2026-04-10`: `Clarify Prop 1.6 CM critical path`;
- `2026-04-10`: three HH-route checkpoint commits on regular-sequence and
  substitution machinery.

What changed structurally:

- `BEI/CohenMacaulay.lean` became `BEI/Equidim.lean`;
- `toMathlib/Equidim/Defs.lean` was separated from the new
  `toMathlib/CohenMacaulay/Defs.lean` and `Basic.lean`;
- guides and public docs were rewritten to say explicitly that the full
  paper-faithful CM branch was still unfinished.

Main obstacle:

- the project had a proven BEI-specific consequence, but not yet the general
  theory needed for the paper's CM proof strategy.

Main breakthroughs:

- `2026-04-09`: the repo cleanedly separated surrogate equidimensionality from
  genuine CM theory.
- `2026-04-10`: the first real CM foundation files landed, with the critical
  path narrowed to the HH bipartite regular-sequence theorem and the Gröbner
  transfer theorem.


## Major Obstacles Across The Whole History

### 1. Incorrect Or Over-Weak Early Definitions

This happened multiple times early:

- `IsClosedGraph` needed correction (`2026-02-20`);
- `IsChordal` needed replacement (`2026-02-25`);
- `prop_1_4` and `cor_1_3` needed statement repair (`2026-02-27`);
- the placeholder `IsCohenMacaulay` packaging later needed replacement
  (`2026-04-04`).

Pattern: the repo repeatedly chose to repair the statement to match the paper
instead of proving a convenient substitute.


### 2. Theorem 2.1 Proof Explosion

This was the dominant technical bottleneck.

Symptoms:

- repeated checkpoint commits without theorem closure;
- large internal helper lemmas, especially around covered walks;
- strategic pivot away from the Rauh route;
- a long tail of telescope, coprime, and mixed-walk subcases.

The final closure on `2026-03-28` marks the single biggest theorem-engineering
breakthrough in the history.


### 3. Missing Commutative-Algebra Infrastructure

Section 3 progress depended on local `toMathlib/` development:

- variable-ideal heights;
- determinantal ideal height;
- height additivity;
- quotient-dimension formulas;
- later, the first real CM definitions and regular-quotient lemmas.

This was not wasted abstraction. It was the minimum general infrastructure
needed to make the paper's Section 3 statements formalizable.


### 4. False Routes Were Real, Not Hypothetical

Two especially important examples:

- `componentCount_mono`-style monotonicity claims were removed as false on
  `2026-02-25`;
- `isPrime_transferred` was explicitly documented as false on `2026-04-02`.

Pattern: the project improved when it stopped papering over bad generalizations
and instead documented exact counterexamples or narrow correct statements.


### 5. Honesty About Cohen-Macaulayness Became A Project-Level Issue

By early April the repo had enough local material that it would have been easy
to overclaim.

The history instead shows corrective moves:

- public-doc wording toned down on `2026-04-08`;
- the surrogate layer renamed to `Equidim` on `2026-04-09`;
- new real-CM files added separately on `2026-04-09` and `2026-04-10`.

This is an important breakthrough in project governance, not just wording.


## Main Breakthrough Dates

- `2026-03-09`: `Theorem 1.1` fully proved in `BEI/ClosedGraphs.lean`.
- `2026-03-28`: `Theorem 2.1` fully proved in `BEI/GroebnerBasis.lean`.
- `2026-04-02`: `Lemma 3.1` fully proved in the Section 3 algebra layer.
- `2026-04-04`: `Corollary 3.3` fully proved.
- `2026-04-06`: `Corollary 3.4`, the CM branch of `Corollary 3.7`, and Section
  4 CI results all landed.
- `2026-04-08` to `2026-04-09`: direct equidimensional `Proposition 1.6`
  completed.
- `2026-04-09` to `2026-04-10`: the repo separated `Equidim` from real
  `CohenMacaulay` theory and started the genuine CM foundation track.


## Structural Turning Points

These commits changed the shape of the project, not only the proof count.

- `2026-02-19`: add full paper scaffold.
- `2026-03-05`: replace the fake Gröbner-basis stub with `BEI/GroebnerAPI.lean`.
- `2026-03-21`: move the Rauh approach aside and switch Theorem 2.1 to the
  Herzog direct proof.
- `2026-03-29` to `2026-03-30`: start `toMathlib/` as a real support layer for
  Section 3.
- `2026-04-04`: replace the placeholder CM definition.
- `2026-04-09`: rename the surrogate CM layer to `Equidim`.
- `2026-04-09` to `2026-04-10`: begin the first genuinely separate real CM
  foundation files.


## Present Endpoint Of The History (`2026-04-10`)

By the end of the recorded history:

- the Section 1, Section 2, and most Section 3 theorem layers had been proved;
- Section 4 CI results had been added;
- a direct equidimensional version of Proposition 1.6 had been proved;
- the repo had deliberately separated that surrogate from the unfinished
  paper-faithful Cohen-Macaulay route;
- the remaining critical path for the real CM version of Proposition 1.6 was
  identified as:
  - the Herzog-Hibi bipartite regular-sequence theorem;
  - the Gröbner transfer theorem;
  - with the forward depth inequality as useful support rather than the
    immediate blocker.

That is the clearest high-level reading of the whole git history: the project
first fought through the Gröbner bottleneck, then completed most of the paper's
Section 3/4 formalization, and finally turned from "getting a result" to
"getting the right result honestly."

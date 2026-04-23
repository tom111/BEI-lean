# Answer: Lean Performance Research

## Preserved task

The user asked:

> Do some research on how to achieve faster running and more efficient Lean code so that
> we don't need to increase the heartbeats and the full build is faster. Document your
> findings in a markdown file.

## Short answer

Yes. The main recommendation from the Lean and mathlib-side sources is:

1. measure first;
2. identify whether the cost comes from `simp`, instance search, elaboration, compilation,
   or a specific tactic;
3. fix that specific cause with narrower automation, fewer inferred arguments, local
   instances, or smaller helper lemmas; and only then
4. keep a heartbeat raise if the declaration is still genuinely expensive.

For this repository, the highest-value targets are not spread uniformly. The biggest
heartbeat concentration is in `BEI/Equidim.lean`, followed by `BEI/PrimeIdeals.lean`,
`BEI/ClosedGraphs.lean`, and `toMathlib/CohenMacaulay/Polynomial.lean`.

## Repo snapshot

Current heartbeat raises in the repo, from a direct `rg` scan:

- total local heartbeat overrides: `37`
- worst file by count: `BEI/Equidim.lean` with `12`
- next: `BEI/PrimeIdeals.lean` with `8`
- then `BEI/ClosedGraphs.lean` with `5`
- then `toMathlib/CohenMacaulay/Polynomial.lean` with `5`
- then `BEI/GroebnerDeformation.lean` with `3`
- then `BEI/MinimalPrimes.lean` with `2`
- then `BEI/GroebnerBasisSPolynomial.lean` and `BEI/Corollary3_4.lean` with `1` each

Worst single heartbeat raise:

- `BEI/MinimalPrimes.lean` sets `maxHeartbeats 4000000`

Large hotspot files, from `wc -l`:

- `BEI/Equidim.lean`: `8489` lines
- `BEI/GroebnerDeformation.lean`: `2232` lines
- `BEI/PrimeIdeals.lean`: `2007` lines
- `toMathlib/CohenMacaulay/Polynomial.lean`: `1652` lines
- `BEI/ClosedGraphs.lean`: `988` lines
- `BEI/MinimalPrimes.lean`: `919` lines

Observed local patterns worth checking first:

- `BEI/PrimeIdeals.lean` already contains a comment saying `aeval_X` unfolding is expensive.
- `BEI/Equidim.lean` has both `maxHeartbeats` and `synthInstance.maxHeartbeats` overrides,
  so at least some of its slowness is probably instance-search related.
- The big Section 3 and CM-support files are large enough that splitting them is likely to
  help both declaration-local performance and rebuild scope.
- There are many uses of `convert` and many arithmetic side-goals discharged by `omega`.
  That does not prove they are the main bottleneck, but they are standard suspects once
  profiler output points at them.

## Source-backed findings

### 1. Profile before editing

The mathlib speedup note recommends starting with:

```lean
set_option profiler true
set_option profiler.threshold 100
```

and then lowering the threshold as needed. It also recommends removing the profiling
options again after the speedup work is done.

Lean 4.9 added `trace.profiler.useHeartbeats`, which switches the profiler threshold from
milliseconds to heartbeats. That is useful here because the concrete problem is excessive
heartbeat use.

Practical consequence for this repo:

- use the profiler before changing proof scripts;
- use heartbeat-based profiling on declarations that already need `maxHeartbeats`;
- only optimize what actually shows up as expensive.

### 2. Use `#count_heartbeats` to justify or eliminate heartbeat raises

Mathlib's `#count_heartbeats in ...`, `#count_heartbeats! in ...`, and
`guard_min_heartbeats` tooling is specifically meant for long-running declarations.

Two points from the docs matter here:

- it is useful for choosing a reasonable `maxHeartbeats`;
- but the docs explicitly warn against setting the limit as low as possible, because
  unrelated library changes can make the declaration brittle.

So the right use is:

- first try to remove the heartbeat raise entirely;
- if that fails, measure the declaration;
- keep a moderate margin rather than a knife-edge limit.

### 3. When `simp` is slow, make it narrower

The mathlib speedup note says that when profiling points at `simp` or `simpa`, the first
move is to replace it by `simp?` or `simpa?` and use the suggested `simp only` call.

This is probably the single highest-value generic optimization in a repository like this,
because many long algebraic proofs accumulate large local contexts and large simp sets.

Practical consequence for this repo:

- any hotspot declaration with a big `simp`, `simpa`, `simp [*]`, or `simp at *` should be
  treated as suspicious immediately;
- switch from global simp search to a curated lemma list once profiler output confirms
  simplifier cost.

Advanced diagnostic note:

- Lean 4.9 also added diagnostics for bad simp indexing and a `Simp.Config.index` switch.
  This is probably second-line tooling, but it is worth trying if a declaration remains
  slow even after converting to `simp only`.

### 4. When instance search is slow, materialize the instance

The mathlib speedup note recommends:

```lean
set_option trace.Meta.synthInstance true in
```

before the slow declaration, then replacing repeated expensive synthesis by an explicit
term, a `letI`, or a local instance.

This is directly relevant here because `BEI/Equidim.lean` already raises
`synthInstance.maxHeartbeats`.

Practical consequence for this repo:

- in `BEI/Equidim.lean`, first profile declarations with `synthInstance.maxHeartbeats`;
- then run `trace.Meta.synthInstance`;
- if the same instance is being rediscovered repeatedly, bind it once with `letI` or an
  explicit local term instead of asking Lean to search for it over and over.

### 5. When elaboration is slow, reduce inference burden

The mathlib speedup note says that if profiling reports slow elaboration, a common cause
is placeholders `_` that force Lean to perform expensive inference. The recommended fix is
to replace them with explicit arguments.

The Lean reference also says that explicitly annotating structural recursion can speed up
elaboration because it avoids termination-search work.

Practical consequence for this repo:

- replace `_` in hotspot declarations once profiling points at elaboration rather than
  tactic execution;
- prefer small typed helper lemmas and intermediate `have`s to giant proof terms with
  many inferred coercions and metavariables;
- if a recursive helper can be structural, make it structural rather than relying on
  inferred well-founded recursion.

### 6. Avoid expensive or unhelpful unfolding

Lean 4.9 added `seal` and `unseal`, and it also marks well-founded recursive functions
`@[irreducible]` by default to avoid expensive and often unfruitful unfolding.

The recursive-definitions reference also explains that structural recursion is preferable
when definitional reduction matters, and that well-founded recursion is typically slower
in the kernel.

Practical consequence for this repo:

- if a hotspot is caused by aggressive unfolding of a helper definition, consider local
  transparency control rather than more heartbeats;
- if a recursive helper is only there for proof organization, be deliberate about whether
  it should compute definitionally;
- avoid accidentally turning cheap opaque helpers into widely-unfolded abbreviations.

### 7. Replace broad tactics with direct proof steps when profiling points at them

The mathlib speedup note explicitly calls out slow `convert` and slow `nontriviality`, and
recommends rewriting those proofs using simpler steps such as prior rewrites followed by
`refine` or `exact`.

Practical consequence for this repo:

- if profiler output blames `convert`, rewrite first and finish with `exact` or `refine`;
- if a large arithmetic proof repeatedly invokes `omega`, isolate the arithmetic facts into
  smaller lemmas so `omega` is applied once to a compact goal rather than many times to a
  cluttered goal;
- be suspicious of large one-block tactic proofs that mix rewriting, instance search,
  simplification, and arithmetic all at once.

### 8. Compilation speed and build speed are related, but not identical

The mathlib speedup note says that when profiling reports slow compilation of a
definition, one possible fix is to make it `noncomputable`.

That only applies in the right situations, but it matters for support definitions that are
proof-oriented and do not need executable code.

On the build-system side, the Lake reference explains that Lake reuses prior build
products via saved trace files. From that, I infer:

- smaller modules reduce rebuild radius;
- slimmer imports reduce the dependency graph touched by a change; and
- moving stable support lemmas out of giant hotspot files can improve full-build behavior
  as more artifacts become independently reusable.

That last point is an inference from Lake's artifact-trace model, not a direct sentence in
the docs, but it is the right operational reading for a repo with very large Lean files.

## Recommended workflow for this repo

### Phase 1: stop guessing

For every declaration that currently needs a heartbeat raise:

1. temporarily add profiler options;
2. run the declaration or file;
3. identify whether the cost is `simp`, instance search, elaboration, compilation, or a
   specific tactic;
4. remove the profiler options after the diagnosis.

Suggested temporary pattern:

```lean
set_option profiler true in
set_option profiler.threshold 50 in
set_option trace.profiler.useHeartbeats true in
theorem ... := by
  ...
```

Then measure the stabilized version with:

```lean
#count_heartbeats in
theorem ... := by
  ...
```

and, if variance matters:

```lean
#count_heartbeats! 20 in
theorem ... := by
  ...
```

### Phase 2: attack the biggest hotspot files first

Recommended order:

1. `BEI/Equidim.lean`
2. `BEI/PrimeIdeals.lean`
3. `BEI/ClosedGraphs.lean`
4. `toMathlib/CohenMacaulay/Polynomial.lean`
5. `BEI/GroebnerDeformation.lean`

Reason:

- this order captures most heartbeat raises in the repo;
- the first two files are also structurally large, so they are good candidates for both
  proof-speed improvements and future file splitting.

### Phase 3: use the right fix for the diagnosed cause

If profiler says:

- `simp took a long time`:
  switch to `simp?`/`simpa?`, then prune to `simp only`.
- `typeclass inference took a long time`:
  use `trace.Meta.synthInstance`, then bind the expensive instance explicitly.
- `elaboration took a long time`:
  replace `_`, add type annotations, and factor huge terms into typed helper lemmas.
- `tactic execution of <tactic> took a long time`:
  replace broad tactics with smaller direct steps.
- `compilation of <name> took a long time`:
  check whether the declaration should be `noncomputable`.

### Phase 4: split giant files only after profiling confirms the shape

File splitting is probably high leverage here, especially for `BEI/Equidim.lean`.
But it should be driven by profiler output and import structure, not by aesthetic cleanup
alone.

The most promising split pattern is:

- isolate stable support lemmas used by many later theorems;
- isolate declarations that still need expensive local CM or localization machinery;
- keep paper-facing wrapper theorems in thinner public files.

That should improve both readability and rebuild scope.

## Bottom line

If the goal is "fewer heartbeat raises and faster builds", the highest-yield plan is:

1. profile `BEI/Equidim.lean` and `BEI/PrimeIdeals.lean` first;
2. replace broad `simp` and repeated instance search with targeted local structure;
3. reduce elaboration work by making arguments and helper lemmas more explicit;
4. control unfolding where automation is expanding the wrong definitions; and
5. split the largest hotspot files once the profiling data tells us where the stable cuts
   are.

That is much more likely to pay off than globally lowering heartbeat limits or doing
blind proof golf.

## Sources consulted

Primary sources used for this note:

- Lean community note: <https://leanprover-community.github.io/extras/speedup.html>
- Lean 4 language reference, 4.9.0 release notes:
  <https://lean-lang.org/doc/reference/latest/releases/v4.9.0/>
- Lean language reference, recursive definitions:
  <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>
- Lake reference:
  <https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/>
- Lean API docs for tracing/profiler options:
  <https://lean-lang.org/doc/api/Lean/Util/Trace.html>
- Mathlib heartbeat-counting docs:
  <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Util/CountHeartbeats.html>

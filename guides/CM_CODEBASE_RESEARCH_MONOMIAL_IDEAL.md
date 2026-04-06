# Guide: CM Codebase Research for the Monomial-Ideal Step

## Original task / question

User request on 2026-04-06:

> Remember that pull request on Cohen–Macaulay things? Search that codebase
> thoroughly if there is not some way to solve our monomial ideal question or
> go for equivalent and more accessible notions of CM.

This guide records the result of that search and the concrete recommendation for the
next BEI-facing route.


## Short answer

After searching the local codebase thoroughly, the answer is:

1. there is **no hidden full Cohen–Macaulay package** in the vendored mathlib
   `v4.28.0` that would directly solve the monomial-ideal step;
2. there is **regular-sequence infrastructure**, but it explicitly stops short of
   depth / Cohen–Macaulay theory;
3. there is **no local squarefree monomial ideal / Stanley–Reisner / shellability**
   layer that would make the Herzog–Hibi monomial ideal step cheap;
4. there is **no initial-ideal-to-original-ideal CM transfer theorem** in the local
   codebase;
5. the only genuinely usable “equivalent and more accessible notion of CM” already
   present in this repo is the local equidimensionality-style definition in
   `toMathlib/CohenMacaulay/Defs.lean`.

So the realistic accessible route is:

- prove the relevant **monomial ideal quotient is equidimensional** by describing and
  comparing its minimal primes;
- then use the repo’s local `IsCohenMacaulay` definition, which is exactly that
  equidimensionality property.


## What was searched

### 1. Stored PR notes

Files inspected:

- `guides/cm_pr_26218/INDEX.md`
- `guides/cm_pr_26218/MINIMAL_IMPORT_AND_BACKPORT.md`

Findings:

- those notes were written for an older repo state where CM was still described as a
  placeholder branch;
- they are still useful for provenance and policy (“import the minimum”), but they do
  **not** point to any already-landed theorem solving Proposition 1.6’s monomial-ideal
  step;
- their most relevant surviving lesson is still correct:
  import only the smallest consequence actually needed, not a whole speculative CM tower.

### 2. Vendored mathlib (`.lake/packages/mathlib/Mathlib`)

Searches run for:

- `CohenMacaulay`, `IsCohenMacaulay`
- `depth`
- `regular sequence`, `IsWeaklyRegular`
- `Stanley`, `Reisner`, `shellable`, `squarefree monomial`
- `initial ideal`, `deformation`, `flat family`, `associated graded`

Findings:

- `rg "CohenMacaulay|IsCohenMacaulay"` over vendored mathlib returns nothing;
- `Mathlib/RingTheory/Regular/RegularSequence.lean` exists, but its header explicitly says:
  - regular sequences are present;
  - **TODO: ... depth**;
  - no CM package is built on top of it there;
- there is no Stanley–Reisner / shellability / monomial-edge-ideal package in the
  commutative-algebra part of the local mathlib;
- there is no theorem giving CM transfer from an initial ideal or Gröbner degeneration.

### 3. Local project code

Files inspected:

- `toMathlib/CohenMacaulay/Defs.lean`
- `BEI/CohenMacaulay.lean`
- `BEI/PrimeDecompositionDimension.lean`

Findings:

- `toMathlib/CohenMacaulay/Defs.lean` defines `IsCohenMacaulayRing` as:
  all minimal primes have the same quotient dimension;
- `BEI/CohenMacaulay.lean` already honestly identifies the two remaining external inputs
  for `prop_1_6`:
  1. the Herzog–Hibi CM theorem for the associated bipartite edge ideal;
  2. CM transfer from `S / in_<(J_G)` to `S / J_G`;
- `BEI/PrimeDecompositionDimension.lean` already shows the repo is comfortable working
  directly with minimal-prime dimensions and equidimensionality.


## What this means for the monomial-ideal question

The search does **not** reveal a ready-made route based on:

- depth = dimension;
- regular sequences;
- shellability / Stanley–Reisner equivalences;
- or Gröbner-degeneration CM transfer.

So if the question is:

> can we solve the monomial-ideal step by pulling more from that PR / codebase?

the answer is:

- not in any cheap direct way.

The codebase does **not** currently contain theorems that would let us say:

```text
bipartite edge monomial ideal satisfying HH conditions -> CM
```

or

```text
S / in_<(I) CM -> S / I CM
```

just by importing a small local file.


## The accessible notion of CM that we do have

The repo’s local notion already gives the accessible surrogate:

```text
R is CM  <=>  all minimal primes of R have the same quotient dimension
```

That is the operative notion in:

- `toMathlib/CohenMacaulay/Defs.lean`
- `BEI/CohenMacaulay.lean`
- `BEI/PrimeDecompositionDimension.lean`

So the real alternative to the full classical CM route is not “find another notion”.
It is:

- prove equidimensionality directly for the monomial quotient we care about.


## Best concrete research direction

If we want an honest accessible route for the monomial ideal appearing in Proposition 1.6,
the most plausible program is:

### Step 1: isolate the right monomial ideal as a graph edge ideal

This is already essentially packaged in `BEI/CohenMacaulay.lean`:

- `bipartiteEdgeMonomialIdeal`
- `rename_yPredVar_monomialInitialIdeal`
- `prop_1_6_herzogHibi`

So the graph-theoretic reduction is already in place.

### Step 2: formalize minimal primes of that monomial edge ideal

This is the first real missing algebra/combinatorics layer.

For a squarefree monomial edge ideal of a graph, the classical description is:

- minimal primes correspond to minimal vertex covers.

The repo currently does **not** have that theorem.

### Step 3: prove equidimensionality from the Herzog–Hibi conditions

Under the HH conditions, the bipartite graph should have all minimal vertex covers of
the same size. In the repo’s local CM framework, that is exactly the sort of result that
would imply the quotient is Cohen–Macaulay.

This is much more realistic than importing full depth theory, because it matches the
local CM definition already in use.

### Step 4: only then revisit the transfer back to `J_G`

Even if Step 3 succeeds, Proposition 1.6 still needs the passage from the monomial /
initial ideal side back to `J_G`.

So this route may solve the **monomial-ideal CM question** honestly, without yet solving
the final transfer theorem.


## Recommendation

### Recommendation 1: do not sink time into the PR for a hidden CM theorem

The local evidence says that PR-style CM code is not going to hand us a quick solution
to the monomial-ideal step.

### Recommendation 2: treat equidimensionality as the main accessible notion

This is already the repo’s working notion of CM.

So if we pursue the monomial ideal directly, the right target theorem is something like:

```text
all minimal primes of bipartiteEdgeMonomialIdeal G have the same quotient dimension
```

or a height-equivalent version.

### Recommendation 3: separate the two remaining jobs

Do not blur:

1. proving the monomial ideal quotient is CM/equidimensional;
2. transferring CM from the initial ideal side back to `J_G`.

The search only supports a plausible route for job 1.


## Concrete next work packet if this route is chosen

If Claude is assigned this branch, the right concrete task is not
“search for more CM theory”.

It is:

1. define the bipartite graph whose edge ideal is `bipartiteEdgeMonomialIdeal`;
2. prove the minimal-prime / minimal-vertex-cover description for that monomial edge ideal;
3. prove that under `HerzogHibiConditions`, all minimal vertex covers have the same size;
4. deduce equal quotient dimensions of minimal primes;
5. conclude CM for the monomial quotient using the local equidimensional definition.

This is a real theorem program, but it is the only codebase-supported accessible route
the current search suggests.


## Warnings

- Do not say the PR search “found CM” in local mathlib. It did not.
- Do not say regular-sequence infrastructure is enough by itself. It is not: the file
  explicitly still has TODOs for depth.
- Do not present the monomial-ideal route as solving Proposition 1.6 entirely.
  It only addresses the monomial / initial-ideal side unless a separate transfer theorem
  is proved.
- Do not overclaim that unmixedness alone is enough. Under the repo’s local CM
  definition, we need the equal quotient-dimension statement, not just a slogan.


## Definition of done for this research guide

This guide has done its job if future work proceeds from the following honest conclusion:

- the local codebase does **not** contain a hidden full CM package we can simply import;
- the accessible route available **inside the current repo** is direct equidimensionality
  of the relevant monomial edge ideal via its minimal primes / vertex covers.

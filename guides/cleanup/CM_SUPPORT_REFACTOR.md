# Guide: Refactor the Cohen-Macaulay Support Layer

## Goal

Turn the Cohen-Macaulay support files in `toMathlib/CohenMacaulay/` into
clean theorem-role modules rather than one long accumulation of support proofs.


## Why this matters

[toMathlib/CohenMacaulay/Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean)
is now a real maintenance hotspot:

- it is large;
- it carries many style warnings;
- it mixes ring-equivalence helpers, polynomial base cases, quotient-local
  identifications, and regular-quotient descent.

That makes it difficult to tell what is upstream-facing infrastructure and what
is merely BEI support plumbing.


## Main refactor idea

Separate:

- generic CM transport lemmas;
- polynomial-ring CM theorems;
- quotient-localization equivalences;
- BEI-consumer-facing wrapper theorems.


## Work package 1: generic transport lemmas

Current content to isolate or move:

- ring-equivalence CM invariance lemmas;
- weakly-regular transfer through ring equivalences;
- generic regular-quotient descent helpers that are not specific to
  polynomial rings.

Candidate destinations:

- `toMathlib/CohenMacaulay/Basic.lean`
- `toMathlib/CohenMacaulay/Localization.lean`
- or a small new auxiliary file if the dependency graph needs it.

The point is to keep generic infrastructure out of the polynomial-specific file.


## Work package 2: polynomial base cases

Target contents:

- fields are Cohen-Macaulay;
- `MvPolynomial (Fin n) K` over a field is CM;
- domain-to-polynomial CM extension results.

Suggested file:

- `toMathlib/CohenMacaulay/PolynomialBase.lean`

This is the upstream-facing core. It should read as a coherent theorem packet.


## Work package 3: quotient-localization identification

Target contents:

- the `A[X]_P / (X) ≃ A_{P ∩ A}` construction;
- evaluation-at-zero localization lemmas;
- polynomial quotient comparison lemmas;
- the proof-engineering machinery needed for the prime-by-prime argument.

Suggested file:

- `toMathlib/CohenMacaulay/PolynomialQuotient.lean`

This is the most technical part and should be separated from the public base case.


## Work package 4: public wrapper and API boundary

Tasks:

- decide which theorems should be public and documented;
- decide which helper lemmas should stay private;
- expose any currently private theorem that downstream files legitimately need,
  rather than making consumers replay it.

In particular, if a downstream theorem depends on a private regular-quotient
descent lemma, either expose that lemma honestly or give the consumer its own
short wrapper theorem with a clear name.


## Work package 5: warning cleanup in the support layer

After the split or boundary cleanup:

- replace `show` with `change` in theorem scripts;
- add scoped `maxHeartbeats` comments;
- remove unused section variables;
- shorten long lines;
- delete unused `simp` arguments.

This should be done after theorem-role boundaries are clearer, not before.


## Anti-patterns to avoid

- mixing upstream-style generic infrastructure with BEI-local assembly code;
- leaving essential downstream theorems `private` while depending on them elsewhere;
- treating warning cleanup as a substitute for API cleanup;
- reopening dormant `GradedCM.lean` work under the cover of polynomial cleanup.


## Definition of done

This guide is complete when:

1. the polynomial CM support layer has clear file boundaries by theorem role;
2. the generic transport lemmas are no longer buried in a giant polynomial file;
3. downstream CM files can import a small, honest API rather than deep plumbing.

# GroebnerBasis Organization Guide

## Preserved task

Write a high-level guide for reorganizing `BEI/GroebnerBasis.lean`.
The goal is not to change the mathematics of Theorem 2.1, but to make the proof
shorter at the public layer, easier for humans to read, and easier to maintain.

## Purpose

`BEI/GroebnerBasis.lean` currently contains a complete formal proof of the Gröbner basis
and reducedness story, but the file boundary is wrong.

At the moment it mixes:

1. paper-facing theorem packaging,
2. the full Buchberger case analysis,
3. walk and mixed-walk remainder engineering,
4. degree-comparison contradictions,
5. reducedness machinery,
6. squarefree-leading-monomial machinery.

That is too much for a single file. The theorem is difficult, but it is still highly
splittable.

## Current diagnosis

The main problem is not that any single local lemma is bad. The problem is that
`theorem_2_1` carries almost the entire S-polynomial infrastructure inline.

Concretely:

- the public theorem is far too long,
- several large subcases repeat the same algebraic template,
- there is still dead code left in the file,
- and the reducedness half is jammed into the same module as the Buchberger proof.

This makes the file hard to trust and hard to navigate even if the proof is correct.

## What is already good

These parts are already reasonable:

- `groebnerBasisSet_span`
- the leading-coefficient lemmas
- the existence of a separate reducedness theorem
- the final wrapper theorem `theorem_2_1_isReducedGroebnerBasis`

Those pieces show the right public architecture. The problem is that the implementation
layer under them was not extracted into separate modules.

## Main organizational problem

Theorem 2.1 should read like:

1. the basis spans the ideal,
2. all generators have unit leading coefficient,
3. all S-polynomials reduce to zero by a case split,
4. therefore Buchberger applies.

Instead, the file currently inlines the entire proof object for all those cases.

That means a reader cannot see the top-level proof structure without scrolling through
hundreds of lines of internal walk coverage arguments.

## Recommended file split

Use a split like this:

1. `BEI/GroebnerBasisCore.lean`
   Put:
   - `groebnerBasisSet_span`
   - `groebnerElement_leadingCoeff`
   - `groebnerElement_leadingCoeff_isUnit`
   - a short public `theorem_2_1` that delegates to case lemmas

2. `BEI/GroebnerBasisSPolynomial.lean`
   Put:
   - the large Buchberger case analysis
   - shared-first-endpoint case machinery
   - shared-last-endpoint case machinery
   - coprime case machinery
   - the internal algebraic equalities with `Q₁/Q₂/R₁/R₂`
   - any private remainder lemmas that exist only to prove the S-polynomial cases

3. `BEI/GroebnerBasisReduced.lean`
   Put:
   - degree computation helpers
   - `groebnerElement_degree_inl`
   - `groebnerElement_degree_inr`
   - endpoint degree lemmas
   - `groebnerElement_reduced_same_endpoints`
   - `theorem_2_1_reduced`
   - `groebnerElement_leadingMonomial_squarefree`
   - the paper-faithful wrapper theorem

If that is too much movement at once, the minimum useful split is:

- extract the entire Buchberger case analysis into `GroebnerBasisSPolynomial.lean`,
- leave reducedness in the current file for one pass,
- then split reducedness afterward.

## What should be extracted first

The first extractions should be by proof role, not by arbitrary line count.

Extract these first:

1. Shared-first-endpoint S-polynomial proof.
2. Shared-last-endpoint S-polynomial proof.
3. Coprime case with shared-vertex subcase.
4. Coprime case with different-components subcase.

Each of those should become a named private lemma with a statement of the form:

- given admissible paths `π`, `σ` with this endpoint configuration,
- the corresponding S-polynomial is a remainder modulo `groebnerBasisSet`.

Then `theorem_2_1` becomes an assembly theorem that does only:

- destruct basis elements,
- split on endpoint equalities,
- apply the corresponding case lemma.

That is the single most important cleanup.

## Repeated templates that should become helper lemmas

The current file repeats several proof templates many times.
Those should become named helpers.

### 1. Degree-vanishing helpers for `fij`

Patterns like:

- degree at `Sum.inr v` is zero when `v ≠ j`,
- degree at `Sum.inl v` is zero when `v ≠ i`.

These occur everywhere in the Buchberger proof and should not be re-proved ad hoc in
each case.

### 2. Quotient-monomial growth helpers

Patterns like:

- `Q₁ s ≥ D s`,
- `Q₂ s ≥ D s`,
- `R₁ s ≥ D s`,
- `R₂ s ≥ D s`.

These are currently repeated local arithmetic facts. They should be abstracted into a
small API for “add one variable or two variables to a monomial degree”.

### 3. Degree-separation contradictions

The proof repeatedly shows two monomials have distinct degree by evaluating at a single
coordinate and getting an arithmetic contradiction.

That should be turned into a helper pattern:

- prove the degree formulas,
- evaluate at a strategic variable,
- derive contradiction.

Do not leave these as one-off local blocks in four different branches.

### 4. Mixed-walk coverage lemmas

The file currently reconstructs walk coverage proofs inline for several endpoint orders.

These should be packaged as named lemmas of the form:

- if a walk’s internal vertices come from these path pieces and the quotient monomial
  covers the relevant x/y variables, then `monomial Q * fij a b` is a remainder.

This is exactly the proof engineering layer that should sit below the public theorem.

## What should move out of this file entirely

These lemmas are not Groebner-basis-specific and should live in the lower combinatorial
API instead of this file:

- `not_head_of_internal'`
- `not_last_of_internal'`

They belong with the path/internal-vertex utility layer, not with Buchberger.

## Dead code policy

Delete the dead code block once the final proof is stable.

Leaving large commented proof attempts inside the theorem file is actively harmful:

- it makes the file look unfinished,
- it obscures where the real proof starts and ends,
- and it is not a substitute for version control.

If some ideas are still useful, move them into a guide file, not the theorem file.

## Documentation fixes

Before or during the refactor, correct the documentation.

In particular:

- the module header should not say the file formalizes Corollary 2.2 if the radical
  corollary is actually proved in `BEI/Radical.lean`,
- the file intro should explain that the main content is Theorem 2.1 plus helper
  squarefree facts used downstream,
- the paper-facing theorem should stay near the top or near the end in a clearly marked
  wrapper section.

## Public theorem layer target

After refactoring, a human should be able to open the core file and see:

1. what the basis set is,
2. why it spans,
3. why Buchberger applies,
4. what reducedness means here,
5. and the final paper-faithful wrapper.

The reader should not have to read all mixed-walk or `Finsupp` bookkeeping to understand
the mathematical structure.

## Suggested execution order

1. Delete the dead code block.
2. Extract the S-polynomial subcases into named private lemmas.
3. Make `theorem_2_1` a short assembly theorem.
4. Move the entire S-polynomial layer into `GroebnerBasisSPolynomial.lean`.
5. Move reducedness and squarefree material into `GroebnerBasisReduced.lean`.
6. Only after the split, simplify duplicated local arithmetic and degree arguments.

## Constraints

- Do not change the statement of the paper-facing theorems unless there is a clear
  paper-fidelity reason.
- Do not “simplify” by weakening the theorem.
- Do not leave low-level walk-coverage arguments inside the public theorem if they can
  be named and moved.
- Do not keep stale header claims or abandoned proof text in the final file.

## Success condition

The reorganization is successful if:

- `theorem_2_1` is short enough to read top-to-bottom,
- the Buchberger cases live in a dedicated implementation file,
- reducedness is visibly separate from Buchberger,
- and a human can see the paper structure without reading 2000 lines of local algebra.

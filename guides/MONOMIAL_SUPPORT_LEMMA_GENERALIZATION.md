# General Polynomial-to-Monomial Non-Membership Cleanup

## Original request

There was the observation that if a polynomial is not in an ideal, then one of its
monomials is not in the ideal. Write a guide that asks Claude to prove that more
general statement, then specialize it to the monomial ideal situation.

Most of the code should already be there and working, but it looks as if this is
somehow written backwards, with the more special lemma proven and then lifted.
Ask Claude to check this all carefully and then beautify.


## Why this matters

This is a basic support-extraction fact that is useful beyond the monomial-ideal
packet. If it is already available in sufficiently general form, the code should
make that clear. Right now the risk is not a mathematical bug but an API/story bug:
the file may read as if the general fact is just a local helper inside the primary
monomial ideal proof, when really the direction should be:

1. prove the general polynomial/ideal lemma;
2. then use it as a specialization inside the monomial-ideal arguments.


## Current live state to inspect

The relevant file is:

- `/home/tom/BEI-lean/toMathlib/MonomialIdeal.lean`

There is already a general lemma in the file:

- `Ideal.not_mem_exists_monomial_notMem`

Current shape:

- assumptions are only `{R : Type*} [CommRing R] {σ : Type*}`
- statement is genuinely general:
  if `p ∉ I`, then there exists `d ∈ p.support` with `monomial d 1 ∉ I`

There is already at least one downstream use in the monomial-ideal primary proof:

- `Ideal.IsMonomial.isPrimary_of_criterion`

So the job is not automatically “invent a new theorem”. The first job is to check
carefully whether the existing theorem is already the correct general result and,
if yes, make the code read that way.


## Task

Check the whole local story carefully and then clean it up so the code flows from
general fact to monomial-ideal specialization.

More concretely:

1. inspect the current statement and proof of `Ideal.not_mem_exists_monomial_notMem`;
2. confirm whether its assumptions are genuinely minimal and whether its current
   namespace/location are appropriate;
3. inspect the surrounding file organization and determine whether the theorem is
   currently placed too late, too locally, or too monomial-specifically;
4. if the API is backwards, refactor it so the general lemma is presented first and
   the monomial-ideal uses are clearly downstream specializations;
5. beautify theorem names, docstrings, comments, and local proof structure so this
   is easy to find and understand later.


## What to check carefully

### Mathematical content

The general fact should be:

- if `p ∉ I`, then at least one support monomial of `p` with coefficient `1`
  is not in `I`

This is just the contrapositive of the fact that if all support monomials belong to
`I`, then `p ∈ I` by summing the support expansion.

So verify:

- the proof really only uses `p.as_sum`;
- the proof really only needs the ring structure required to rewrite
  `monomial d (coeff d p)` as `C (coeff d p) * monomial d 1`;
- there are no hidden monomial-ideal assumptions left over.

### API / organization

Check whether the current file structure tells the story backwards. In particular:

- is the general lemma buried inside a section whose header sounds specific to the
  primary monomial ideal proof?
- is there an older or more specialized version elsewhere that is now redundant?
- would it be cleaner to move this lemma earlier in
  `toMathlib/MonomialIdeal.lean`, so later proofs visibly depend on it?

Do not move it to a different file unless that is clearly cleaner and low-risk. A
small local reordering is preferable to gratuitous churn.

### Naming / readability

Check whether the current name

- `Ideal.not_mem_exists_monomial_notMem`

is the right public API name. It is acceptable if it is already consistent with the
repo style. Only rename if the new name is clearly better and the churn is small.

Regardless of naming, improve:

- docstrings;
- section headers;
- nearby comments;
- proof readability.


## Recommended plan

### Step 1: audit first, do not refactor blindly

Before changing code, answer these questions from the actual file:

1. Is `Ideal.not_mem_exists_monomial_notMem` already fully general?
2. Is there any more special lemma that has become redundant?
3. Is the current theorem placement making the narrative backwards?

If the answer to (1) is yes and there is no redundancy, then the task is primarily
beautification and local reordering, not new mathematics.

### Step 2: present the general lemma first

If the theorem is already right, make it read as a foundational helper rather than a
late proof-local trick. Possible improvements:

- move it earlier within `toMathlib/MonomialIdeal.lean`;
- add a short section header such as “General support extraction lemma”;
- add a short explanatory docstring making the contrapositive argument explicit.

### Step 3: make the specialization explicit

After the general lemma, the monomial-ideal code should use it transparently.

If useful, add a tiny wrapper or comment showing the specialization pattern, for
example:

- in monomial-ideal proofs, choose a support monomial outside the ideal via
  `Ideal.not_mem_exists_monomial_notMem`, then use `Ideal.IsMonomial` structure to
  reason further.

Do not add redundant wrapper lemmas unless they improve actual readability.

### Step 4: remove stale or backwards-looking structure

If there is any leftover local helper or comment that makes it sound as if the
general theorem is derived from the monomial case, fix that.


## False routes / cautions

- Do not claim a new theorem was needed if the general theorem is already there.
- Do not introduce extra algebraic assumptions just to fit the current proof.
- Do not create a second nearly-identical lemma unless there is a real API need.
- Do not move the theorem across files unless the benefit is clear; the likely right
  outcome is a local cleanup, not a large refactor.
- Do not let beautification turn into broad file churn.


## Definition of done

Best outcome:

- `Ideal.not_mem_exists_monomial_notMem` is clearly presented as the general theorem;
- the file structure now reads from general lemma to monomial-ideal application;
- any redundant specialized formulation is removed;
- docstrings/comments/sectioning are improved.

Minimum acceptable outcome:

- confirm in code that the general theorem already exists with the right
  assumptions;
- make a small cleanup so later readers can see that the monomial-ideal argument is
  specializing a general fact rather than inventing one ad hoc.


## Status docs

This is proof-engineering / API cleanup, not a new mathematical milestone. Only
update repo status files if the public theorem surface changes in a meaningful way.

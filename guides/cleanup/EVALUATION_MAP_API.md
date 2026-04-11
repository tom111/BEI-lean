# Guide: Build a Reusable Evaluation-Map API

## Goal

Factor out the repeated "evaluation-map contradiction" pattern that appears throughout
Section 3 and related ideal-containment arguments.


## Why this matters

Several proofs follow the same template:

1. define an evaluation map `σ`;
2. show every generator of some ideal vanishes under `eval σ`;
3. show one specific binomial evaluates to a nonzero value;
4. derive contradiction.

This appears in:

- [PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
- [MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)
- parts of [PrimeIdeals.lean](/home/tom/BEI-lean/BEI/PrimeIdeals.lean)
- related scratch/archive files.

Right now each proof reimplements too much of the same reasoning.


## Main refactor idea

Create a small internal API for the following kinds of facts.

### Type A: generator-vanishing lemmas

Examples:

- variables in the support set evaluate to zero;
- determinantal generators evaluate to zero under a chosen point;
- all generators of `primeComponent G S` vanish.

Target style:

```text
primeComponent_le_ker_eval_someWitness
```

or narrower helper lemmas that can be assembled quickly.


### Type B: distinguished-binomial nonvanishing lemmas

Examples:

- `eval σ (x_u * y_v - x_v * y_u) = 1`;
- `eval σ (X (Sum.inl i)) = 1`.

These should be named and reused instead of proved inline.


### Type C: generic contradiction wrappers

If a map `φ` kills ideal `I` and `f ∈ I` but `φ f ≠ 0`, contradiction.

Even a tiny helper lemma for this improves readability:

```text
have hker : I ≤ RingHom.ker (MvPolynomial.eval σ) := ...
have : f ∉ I := ...
```

The point is not sophistication. The point is standardizing the shape.


## Recommended implementation location

Good candidates:

- `BEI/HerzogLemmas.lean` if renamed to something content-based;
- or a new file like `BEI/EvalContradictions.lean`.

Do not leave these lemmas scattered ad hoc across theorems.


## Immediate extraction targets

## 1. `prop_3_8_var_not_mem`

File:

- [MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)

This is already a good seed for the API.
Generalize the pattern slightly if that does not make the statement ugly.


## 2. `primeComponent_le_prime`

File:

- [PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)

The telescope argument plus containment proof should read as a reusable ideal-membership
engine, not a one-off block.


## 3. component-preservation contradiction lemmas

File:

- [MinimalPrimes.lean](/home/tom/BEI-lean/BEI/MinimalPrimes.lean)

The proof of `prop_3_8_sameComponent_preserved` is exactly the kind of thing that
becomes much clearer if the evaluation-map mechanics are abstracted away.


## Practical rule

When you see a proof introducing:

```text
let σ : ...
have hker : I ≤ RingHom.ker ...
```

ask immediately whether that belongs in the evaluation API.


## Anti-patterns to avoid

- over-generalizing into an unreadable monster theorem;
- keeping every evaluation map specialized to one theorem when the pattern is identical;
- mixing evaluation setup with graph-theoretic reasoning in one giant proof block.


## Definition of done

This guide is complete when the main ideal-containment proofs use short named
evaluation lemmas instead of rebuilding the same contradiction pattern inline.

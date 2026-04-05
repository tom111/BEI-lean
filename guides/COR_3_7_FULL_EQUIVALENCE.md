# Guide: Corollary 3.7 Full Equivalence

## Paper statement

For a cycle of length `n`, the paper proves equivalence of:

- `(a)` `n = 3`
- `(b)` `J_G` is prime
- `(c)` `J_G` is unmixed
- `(d)` `S / J_G` is Cohen–Macaulay`

Current Lean state:

- `(a) <-> (b)` is formalized in [corollary_3_7](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
- `(b) <-> (c)` is fully proved in `corollary_3_7_unmixed` (MinimalPrimes.lean)
- `(d) <-> (b)` has a stub in `corollary_3_7_CM` — blocked on CM infrastructure


## Recommended order inside this corollary

Do not start with the CM direction.

Prove the cycle corollary in this order:

1. add an `IsUnmixed` notion or use the existing Mathlib one if available;
2. prove `(c) -> (b)` using the paper's dimension argument;
3. derive `(b) -> (d)` only after a real CM foundation exists;
4. then assemble the four-way equivalence.


## Part 1: formalize the unmixed branch

The paper's proof of `(c) -> (b)` is independent of CM infrastructure.

This is the next reachable piece.

### Step 1: choose a definition of unmixed

Search Mathlib first.

If no suitable notion exists, define a project-local one carefully, for example:

```text
all minimal primes of I have the same quotient dimension
```

or equivalently:

```text
all minimal primes of I have the same height
```

Prefer the formulation that best matches already available lemmas in `Ideal.minimalPrimes`.


### Step 2: prove a cycle-specific lemma about nonempty `S`

The paper computes for a cycle:

```text
dim(R / P_S(G)) <= n    for S nonempty
dim(R / P_∅(G)) = n + 1
```

So once `corollary_3_3` or the prime-component quotient formula exists, the argument is short.

Break this into:

1. classify `componentCount G S` for cycle graphs enough to show
   `- |S| + c(S) <= 0` for nonempty `S`;
2. conclude `dim(R / P_S) <= n`.

You do not need the full interval decomposition from the paper if a simpler graph
bound suffices.


### Step 3: prove `(c) -> (b)`

Use:

- `P_∅` is a minimal prime of `J_G`;
- `dim(R / P_∅) = n + 1`;
- every other minimal prime has dimension `<= n`.

Therefore, if `J_G` is unmixed, `P_∅` must be the only minimal prime.
Then radicality implies primeness.


## Part 2: prepare the CM branch

The equivalence `(b) -> (d)` in the paper uses the classical fact that determinantal
ideals of `2 x k` minors are Cohen–Macaulay. That is not currently available in Lean.

So do not try to finish the whole four-way equivalence until there is an honest CM base.

Instead:

1. prove the unmixed branch first;
2. leave the final theorem split if necessary:
   - one theorem for `(a) <-> (b) <-> (c)`;
   - one later theorem for the CM extension.


## Suggested theorem packaging

Intermediate theorem:

```text
theorem corollary_3_7_unmixed ...
  : Fintype.card V = 3 ↔ (binomialEdgeIdeal G).IsPrime ↔ IsUnmixed (...)
```

or separate lemmas:

- `cycle_unmixed_implies_prime`
- `cycle_prime_implies_unmixed`

The second direction may be easy once `prime -> only minimal prime` is packaged.


## Dependencies

Needed before this guide is really finishable:

- `corollary_3_3` or at least `dim(R / P_S)` for cycle `S`;
- a usable notion of unmixedness;
- minimal-prime infrastructure already present.


## Definition of done

This guide is complete when:

1. the unmixed branch `(c)` is formalized honestly;
2. there is a theorem covering `(a)`, `(b)`, `(c)`;
3. the remaining CM branch is isolated as a separate dependency on CM infrastructure.

# Answer to Q2: Radical Ideals and Dimension as a Supremum over Minimal Primes

## Preserved question

We have:

```text
J_G = ⋂_S P_S(G)
```

with each `P_S` prime and `J_G` radical, and need:

```text
ringKrullDim (R ⧸ J_G) = ⨆ S, ringKrullDim (R ⧸ P_S(G)).
```

The original question asked whether this should be proved abstractly for radical ideals
with finitely many minimal primes, how to obtain both inequalities, and whether such a
theorem belongs in `toMathlib/`.

## Short answer

Yes, this is the right abstract theorem to isolate, and it likely belongs in
`toMathlib/` if you can state it cleanly.

Needed theorem:

```text
If I is radical and has finitely many minimal primes P_i,
then ringKrullDim (R ⧸ I) = ⨆ i, ringKrullDim (R ⧸ P_i).
```

## Lower bound

This is the easy half.

If `I ≤ P`, then `R ⧸ P` is a quotient of `R ⧸ I`, so:

```text
ringKrullDim (R ⧸ P) ≤ ringKrullDim (R ⧸ I).
```

If Mathlib lacks the exact lemma, prove the general monotonicity statement under a
surjective ring hom and specialize it to quotient maps.

## Upper bound

Use:

```lean
ringKrullDim_quotient I :
  ringKrullDim (R ⧸ I) = Order.krullDim (PrimeSpectrum.zeroLocus I)
```

Then prove a poset lemma saying:

- if every element of a subset lies above some minimal element from a finite family,
  the Krull dimension of the whole subset is the supremum of the Krull dimensions of the
  corresponding upper intervals.

For radical ideals, the minimal elements are the minimal primes.

## Recommended architecture

1. Prove or locate the lemma that every prime above a radical ideal contains a minimal
   prime above it.
2. Prove the generic or prime-spectrum-specific "dimension of union of upper sets" lemma.
3. Identify each upper interval above a prime `P` with `zeroLocus P`, hence with
   `ringKrullDim (R ⧸ P)`.

## Recommendation

This should be proved once as infrastructure and then used by BEI, rather than re-proved
inside `PrimeDecomposition.lean`.

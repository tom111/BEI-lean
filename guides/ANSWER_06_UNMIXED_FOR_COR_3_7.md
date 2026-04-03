# Answer to Q6: Unmixedness for the Cycle Corollary

## Preserved question

For a cycle graph `G`, the paper proves:

```text
(a) n = 3 ↔ (b) J_G prime ↔ (c) J_G unmixed ↔ (d) S/J_G Cohen–Macaulay.
```

The original question asked how to formalize the unmixed branch independently of the CM
infrastructure, what definition of unmixedness to use, and whether full Corollary 3.3 is
actually needed.

## Short answer

Yes: the `(a) ↔ (b) ↔ (c)` part of Corollary 3.7 should be formalizable now, without
full Corollary 3.3 and without any CM infrastructure.

## Recommended definition

Use the minimal-prime-height version:

```text
I is unmixed := all minimal primes of I have the same height.
```

This is exactly what the paper uses in the cycle proof.

## Why full Corollary 3.3 is unnecessary

The paper's proof only needs:

1. `height(P_∅) = n - 1` for a connected cycle;
2. `height(P_S) ≥ n` for every nonempty `S`;
3. radicality and minimal-prime classification.

All of that can be obtained from:

- `lemma_3_1`
- cycle combinatorics
- minimal prime infrastructure

## Proof plan

1. Define a local `IsUnmixed` if Mathlib does not already provide the right predicate.
2. Compute `height(P_∅)` using `lemma_3_1` and connectedness.
3. Prove the cycle combinatorial lemma `componentCount G S ≤ S.card` for nonempty `S`.
4. Deduce `height(P_S) ≥ n` for nonempty `S`.
5. Conclude unmixedness forces `P_∅` to be the only minimal prime, hence `J_G` is prime.
6. The converse `(b) -> (c)` is immediate because a prime ideal has exactly one minimal
   prime.

## Recommendation

This is a good next theorem after the Section 3 dimension work, and it should be treated
as independent of the CM branch.

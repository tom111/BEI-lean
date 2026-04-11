# Answer to Q4: Repairing `HeightAdditivity.lean`

## Preserved question

`toMathlib/HeightAdditivity.lean` was aiming at height additivity for sums of ideals in
disjoint polynomial variable sets, but its route through a theorem called
`isPrime_transferred` failed because that statement is false in general.

The original question asked:

- what the correct replacement strategy should be;
- whether the BEI-specific complete-graph ideals behave better;
- whether the file is still needed for the current BEI pipeline; and
- whether the partial going-down setup can still be salvaged.

## Short answer

Do not try to salvage the false `isPrime_transferred` route as a general theorem.
The correct strategy is to reframe the file around **minimal primes of the sum**, not
primality of the sum itself.

For the current BEI critical path, this file is not blocking.

## Most important practical point

`height_sup_disjoint` is not currently needed to finish the live Section 3 pipeline,
because `lemma_3_1` has already been proved by a different explicit chain construction.

That means:

- do not let this file block Corollary 3.3;
- treat it as infrastructure debt unless a later theorem genuinely needs it.

## If you do repair it

The right shape is:

1. take a minimal prime `Q` over the disjoint-variable sup;
2. analyze contractions of `Q` back to the two blocks;
3. prove the height of `Q` is the sum of the heights of those contractions;
4. conclude the height of the sup from its minimal primes.

This avoids the false claim that the sup itself is prime.

## About the BEI-specific case

Even if the complete-graph BEI pieces behave better than arbitrary primes over a field,
that should be handled as a specific theorem, not by pretending the general statement was
almost right.

## Recommendation

For now:

1. keep the correct reusable lemmas already proved;
2. document clearly that the primality route is false in general;
3. postpone a full repair unless a future theorem actually needs the additive-height
   statement in a reusable form.

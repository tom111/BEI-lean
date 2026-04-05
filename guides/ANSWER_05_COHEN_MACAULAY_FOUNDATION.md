# Answer to Q5: What CM Foundation to Build

## Preserved question

The paper uses Cohen–Macaulayness in:

- Proposition 1.6,
- Corollary 3.4,
- and the CM branch of Corollary 3.7.

The original question asked what foundation, if any, should be built locally:

- a real depth-based definition,
- a weaker equidimensional/unmixed surrogate,
- or an axiomatized placeholder carrying only the needed consequences.

## Short answer

Do not build a fake local `IsCohenMacaulay` definition and then use it as if the CM
branch were formalized. That would blur the line between real algebra and scaffolding.

The pragmatic choice was:

1. build a real local working notion based on equidimensionality;
2. formalize the non-CM reductions honestly;
3. isolate exactly which CM/equidimensionality consequences are still missing.

That is now the actual state of the repo.

## What this means in practice

### Corollary 3.4

This should be reframed around the exact equidimensionality consequence needed, not a
broader depth-based theory.

### Corollary 3.7

Do the unmixed branch now; leave the CM branch deferred.

### Proposition 1.6

The repo can now legitimately explore two routes:

- the paper-faithful reduction to the associated bipartite edge-ideal setup;
- a direct equidimensionality proof over the local definition.

But do not pretend the final CM implication is proved until one of those routes is actually completed.

## On full CM infrastructure

The package needed by the paper is substantial:

- depth / regular sequences;
- CM transfer from initial ideals;
- determinantal CM results.

That is a real subproject, not a small local patch.

## Recommendation

Treat the remaining CM work as a precise theorem problem, not as a vague missing-foundation problem.

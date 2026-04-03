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
branch were formalized. That will blur the line between real algebra and scaffolding.

The pragmatic choice is:

1. formalize the non-CM reductions honestly;
2. isolate weaker properties like equidimensionality or unmixedness when those are the
   actual statements used;
3. leave genuinely CM-dependent conclusions blocked on a real CM foundation.

## What this means in practice

### Corollary 3.4

This should be reframed around the exact equidimensionality consequence needed, not full
Cohen–Macaulayness.

### Corollary 3.7

Do the unmixed branch now; leave the CM branch deferred.

### Proposition 1.6

Formalize the reduction to the associated bipartite edge-ideal setup, but do not pretend
the final CM implication is proved until there is a real CM theory behind it.

## On full CM infrastructure

The package needed by the paper is substantial:

- depth / regular sequences;
- CM transfer from initial ideals;
- determinantal CM results.

That is a real subproject, not a small local patch.

## Recommendation

Treat Cohen–Macaulayness as an external foundation problem.
Build around it for now, rather than through it.

# Answer to Q17: Should Proposition 1.6 use the direct equidimensionality route?

## Preserved question

The question asks whether Proposition 1.6 should now be finished by switching to the
direct equidimensionality route, rather than continuing with the paper-faithful route.

Current context:

- the paper-side reduction is now fully packaged on the BEI side:
  - `initialIdeal_closed_eq`
  - `yPredVar`
  - `rename_yPredVar_generator`
  - `bipartiteEdgeMonomialIdeal`
  - `prop_1_6_herzogHibi`
- the remaining `sorry` in `prop_1_6` depends on external algebraic inputs:
  - the Herzog–Hibi CM theorem for bipartite edge ideals satisfying (i)–(iii)
  - CM transfer from `S / in_<(I)` to `S / I`

The question is whether the direct equidimensionality route should now be preferred.

## Short answer

No.

The direct equidimensionality route is still a legitimate fallback, but it should not be
the preferred route now that the paper-side reduction has been fully packaged.

## Why this is the right decision

### 1. The paper route is now in a very good state

Earlier, the direct route looked tempting because the paper route was only partially
formalized.

That is no longer true. The repository now already contains the full BEI-side
translation of the paper’s reduction. So changing proof strategy now would move the
project away from `BEI.tex` just when it has become nicely aligned with it.

### 2. The direct route would require a new graph theorem

To finish Proposition 1.6 directly by equidimensionality, one would need a theorem like:

```text
For connected closed graphs on Fin n satisfying SatisfiesProp1_6Condition,
every minimal-prime set S satisfies componentCount G S = S.card + 1.
```

This is not the route taken in the paper, and the repo currently has no clean
combinatorial infrastructure suggesting that this theorem will be easier than the
remaining algebraic inputs.

So this route would not be a small shortcut. It would be a new theorem program.

### 3. The current blocker is now accurately understood

The right current description of Proposition 1.6 is:

- graph reduction: done;
- algebraic packaging: mostly done;
- remaining gap: external algebraic CM inputs.

That is a healthy and honest project state. The repo should preserve that clarity.

## Answers to the specific questions

### 1. Is `componentCount G S = S.card + 1` plausible?

Possibly, yes.

But plausibility is not enough to make it the preferred route. The repository does not
yet have a theorem package making this look local or cheap, and the paper does not use
this route.

### 2. Would such a proof count as a satisfactory formalization?

Yes.

If the final theorem statement matches the paper, then a different proof would still be
a satisfactory formalization.

But it would be a satisfactory **alternative proof**, not a paper-faithful completion.
That distinction matters in this repository.

### 3. Or should Proposition 1.6 remain `sorry` until HH + transfer are available?

Yes, by default.

Unless the user explicitly wants the alternative equidimensionality theorem program, the
project should keep Proposition 1.6 on the paper route and leave the theorem open only
at the remaining algebraic inputs.

## Practical recommendation for Claude

The next worker on Proposition 1.6 should:

1. stay on the paper-faithful route;
2. avoid switching to the direct equidimensionality route in this round;
3. focus on the remaining algebraic packaging and the exact external theorem statements
   still needed.

## Bottom line

The direct equidimensionality route remains a backup plan.

It is not the preferred route now that the paper reduction has already been formalized.

# Question 9: Cycle component count combinatorics

## Context

For the unmixed branch of Corollary 3.7, we need:

```
cycle_componentCount_le_card: For a cycle graph G on n ≥ 4 vertices and
nonempty S ⊆ V, componentCount G S ≤ S.card.
```

## Mathematical argument

Removing k vertices from a cycle of length n creates at most k connected
components (each removed vertex can "break" at most one connection, and
the cycle has a single component to start with). More precisely:

If S = {v_1,...,v_k} and we remove them from the cycle, the remaining
vertices form at most k path segments (arcs of the cycle between
consecutive removed vertices).

## Question

1. What Mathlib graph theory API exists for cycle graphs that would help?
   In particular: `SimpleGraph.IsCycle` for walks vs our `IsCycleGraph`
   (every vertex has exactly 2 neighbors). Can we use `pathGraph` results?

2. The argument needs: "the induced subgraph G[V\S] of a cycle on V\S is a
   disjoint union of paths." Is this a reasonable Lean theorem to state and
   prove, or should we use a counting argument instead?

3. Simpler counting approach: by induction on |S|. Base case |S| = 1:
   removing one vertex from a cycle gives a connected path, so c({v}) = 1 ≤ 1.
   Inductive step: removing one more vertex can increase c by at most 1
   (it splits one path segment into at most two). Is this induction clean
   enough to formalize?

4. Does the definition of `componentCount` via `Nat.card` of
   `ConnectedComponent` interact well with removing one vertex? Is there
   a Mathlib lemma about how the number of connected components changes
   when removing a vertex?

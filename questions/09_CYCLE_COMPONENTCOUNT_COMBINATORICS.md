# Question 9: Four cycle graph combinatorial lemmas

## Context

For the unmixed branch of Corollary 3.7 (prime ↔ unmixed for cycles), the proof
structure is complete in `BEI/MinimalPrimes.lean` with exactly 4 graph-theoretic
sorries. The height arithmetic and minimal prime assembly are fully proved.

The definition of `IsCycleGraph G` is:
```lean
def IsCycleGraph (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ v : V, ∃ u w : V, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ ∀ z : V, G.Adj v z → z = u ∨ z = w
```

The definition of `componentCount G S` is:
```lean
noncomputable def componentCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce {v : V | v ∉ S}).ConnectedComponent
```

## The 4 lemmas needed

### Lemma 1: `cycle_componentCount_singleton`
```lean
theorem cycle_componentCount_singleton (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    componentCount G {v} = 1
```
Removing one vertex from a cycle gives a connected path (one component).

### Lemma 2: `cycle_exists_nonadj`
```lean
theorem cycle_exists_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 4 ≤ Fintype.card V) :
    ∃ u w : V, u ≠ w ∧ ¬G.Adj u w
```
On a cycle with ≥ 4 vertices, some pair is non-adjacent (every vertex has exactly 2 neighbors, so for n ≥ 4 it has non-neighbors).

### Lemma 3: `cycle_componentCount_pair_nonadj`
```lean
theorem cycle_componentCount_pair_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (u w : V) (hne : u ≠ w) (hnadj : ¬G.Adj u w) (hn : 4 ≤ Fintype.card V) :
    componentCount G {u, w} = 2
```
Removing two non-adjacent vertices from a cycle gives exactly 2 components.

### Lemma 4: cut-vertex verification (inline sorry)
```
Given u, w non-adjacent on a cycle with c({u,w}) = 2 and c({u}) = c({w}) = 1:
For i ∈ {u, w}: componentCount G ({u,w}.erase i) < componentCount G {u,w}
```
This is: c({w}) < c({u,w}) i.e. 1 < 2, which follows from Lemmas 1 and 3.

## What makes these hard in Lean

- `componentCount` uses `Nat.card` of `ConnectedComponent`, which is opaque
- `G.induce {v | v ∉ S}` creates a subtype graph that's hard to reason about
- Cycle graph theory in Mathlib works with `Walk.IsCycle`, not our `IsCycleGraph`
- No existing Mathlib lemma for "induced subgraph of cycle minus vertex is connected"

## What would help most

1. A strategy for proving `(G.induce {v | v ∉ {w}}).Connected` when G is a cycle
   graph — this is Lemma 1 essentially.

2. For Lemma 2: can `Fintype.exists_ne_of_card_lt` + the degree-2 property work?

3. For Lemma 3: once Lemma 1 gives c({u}) = c({w}) = 1, can we show removing a
   non-neighbor of u from the path G[V\{u}] disconnects it? The path has u's two
   cycle-neighbors as endpoints; w is an internal vertex, so removing it splits
   the path into 2 pieces.

4. Lemma 4 follows immediately from Lemmas 1 and 3: `1 < 2`.

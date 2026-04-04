# Question 13: Two cycle graph lemmas blocking Cor 3.7

## Context

BEI/MinimalPrimes.lean has 2 sorry'd lemmas blocking the unmixed branch of
Corollary 3.7. Multiple agent attempts have failed due to the difficulty of
reasoning about induced subgraphs with subtype vertices.

## IsCycleGraph definition

```lean
def IsCycleGraph (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ v : V, ∃ u w : V, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ ∀ z : V, G.Adj v z → z = u ∨ z = w
```

## componentCount definition

```lean
noncomputable def componentCount (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (G.induce {v : V | v ∉ S}).ConnectedComponent
```

## Lemma 1: cycle_induce_preconnected

```lean
private lemma cycle_induce_preconnected (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    (G.induce {x : V | x ∉ ({v} : Finset V)}).Preconnected
```

**Why it's hard:** G.induce creates a graph on subtypes `{x // x ∉ {v}}`. Building
walks in this subtype graph from walks in G requires showing vertices avoid v.
The "shortest walk avoids v" argument is FALSE (a shortest walk CAN go through v
on a cycle). The reachability closure argument is correct but requires showing
the complement of the reachable set is empty via G.Connected.

**Key mathematical fact:** Removing one vertex from a cycle of length ≥ 3 gives a
connected path. This is because every remaining vertex has degree ≥ 1 in the
induced subgraph (had degree 2, lost at most 1 neighbor).

**What would help:** A Lean proof that constructs Reachable in G.induce S from
G.Connected by showing: for any t ∈ S, at least one G-neighbor of t is in S,
giving a G'-edge. Then by closure, everything in S is reachable from n1.

The key sub-lemma needed:
```lean
-- Every vertex in V\{v} has at least one G-neighbor also in V\{v}
lemma cycle_neighbor_in_complement (hCyc : IsCycleGraph G) (t : V) (ht : t ≠ v) :
    ∃ s, s ≠ v ∧ G.Adj t s
```
This follows from: t has 2 neighbors, at most 1 is v, so at least 1 is not v.

Then the connectivity proof uses: the reachable set R from n1 in G' is closed
under this neighbor operation, contains n1, and by G.Connected + the neighbor
lemma, must be all of V\{v}.

## Lemma 2: cycle_componentCount_pair_nonadj

```lean
theorem cycle_componentCount_pair_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (u w : V) (hne : u ≠ w) (hnadj : ¬G.Adj u w) (hn : 4 ≤ Fintype.card V) :
    componentCount G {u, w} = 2
```

**Key fact:** Removing two non-adjacent vertices from a cycle gives exactly 2 arcs.

**Approach:** This could use Lemma 1 + the fact that removing w from the connected
graph G[V\{u}] disconnects it (w has degree 2 in G[V\{u}] and is a "cut vertex"
of the path G[V\{u}]).

Please provide COMPLETE Lean 4 proofs. The proofs can be long.

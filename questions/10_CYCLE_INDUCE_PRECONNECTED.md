# Question 10: Prove cycle_induce_preconnected

## What we need

```lean
private lemma cycle_induce_preconnected (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    (G.induce {x : V | x ∉ ({v} : Finset V)}).Preconnected
```

This is the last blocker for Corollary 3.7 unmixed branch. Once this and
`cycle_componentCount_pair_nonadj` are proved, the full (a)↔(b)↔(c) equivalence
for cycles is complete.

## Current state of the proof

File: BEI/MinimalPrimes.lean, line 552. The proof has:
- `hConn : G.Connected`, `hDeg : ∀ v, ∃ u w, ...` (from IsCycleGraph)
- `n1, n2` are v's two neighbors, `hn12 : n1 ≠ n2`
- `G' := G.induce S` where `S = {x | x ≠ v}`
- Reduced to: `∀ t ∈ S, G'.Reachable ⟨t, ht⟩ ⟨n1, hn1S⟩`

## What makes this hard

1. `G.induce` creates a subtype graph `SimpleGraph {x // x ∈ S}` — all vertices
   are subtypes, making API awkward.
2. We need to construct walks in the induced subgraph, but our walks come from G.
3. The IsCycleGraph definition gives local structure (each vertex has 2 neighbors)
   but not global structure (no explicit cycle walk).

## Suggested approach for the thinking model

Write a complete Lean 4 proof. The cleanest strategies seem to be:

**Strategy A (reachability closure):**
Let R = {t ∈ S | G'.Reachable t n1}. Show R = S by:
- R is nonempty (n1 ∈ R)
- If c ∈ R and G.Adj c d and d ∈ S, then d ∈ R (lift the G-edge to G'-edge)
- G.Connected means R ∪ {v} = V (everything is reachable from n1 via G,
  and any G-path must enter/exit R through G'-edges unless it passes through v)
- n2 ∈ R (key step: parity argument or direct walk construction)
- Once n2 ∈ R: any d ∈ S \ R has no G-edges to R or to v, contradicting G.Connected

**Strategy B (walk transfer):**
For any t ∈ S, take a walk from t to n1 in G (exists by G.Connected).
If the walk doesn't pass through v, transfer it to G'.
If it does pass through v, reroute: the walk enters v from some neighbor of v
(which is n1 or n2), so splice the walk to go through n2 → ... → n1 instead.

Please provide a COMPLETE Lean 4 proof, not just a strategy. The proof can be
long — correctness matters more than elegance.

## Available Mathlib API

- `SimpleGraph.induce_adj`: `(G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ ↔ G.Adj a b`
- `SimpleGraph.Connected.exists_walk_of_adj`: walks exist between adjacent vertices
- `SimpleGraph.Reachable`: transitive closure of adjacency
- `SimpleGraph.Walk.transfer`: transfer walks between graphs with same edges

# Question 12: Two small Lean problems

## Problem A: ℕ → WithBot ℕ∞ cast through iSup

In BEI/PrimeDecomposition.lean (corollary_3_3), after all mathematical content
is proved, there remains a cast lemma:

```
⊢ ⨆ S, ↑(Fintype.card V - S.card + componentCount G S) =
    ↑(⨆ S, Fintype.card V - S.card + componentCount G S)
```

where:
- LHS: `iSup` in `WithBot ℕ∞` of `ℕ → WithBot ℕ∞` casts
- RHS: `WithBot ℕ∞` cast of `iSup` in `ℕ`
- `S : Finset V` with `[Fintype V]`

The ≤ direction is proved. The ≥ direction needs: the ℕ-iSup achieves its
max (since Finset V is finite), say at S₀, then `↑(f S₀) ≤ ⨆ S, ↑(f S)`.

What Mathlib lemma handles `↑(ciSup f) ≤ iSup (↑ ∘ f)` for finite types?
Or how to extract the argmax of a finite iSup in ℕ?

## Problem B: cycle_induce_preconnected

In BEI/MinimalPrimes.lean, prove:

```lean
private lemma cycle_induce_preconnected (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    (G.induce {x : V | x ∉ ({v} : Finset V)}).Preconnected
```

Available: `hConn : G.Connected`, `hDeg : ∀ v, ∃ u w, ...`, `n1 n2` neighbors
of v, `G' = G.induce S`, reduced to `∀ t ∈ S, G'.Reachable ⟨t, ht⟩ ⟨n1, hn1S⟩`.

Strategy: for each t ∈ S:
1. Get path p from t to n1 in G via `Walk.toPath` of a connectedness walk
2. If v ∉ p.support: transfer p to G' (every edge has both endpoints in S)
3. If v ∈ p.support: since p is a path (no repeated vertices) and t ≠ v, n1 ≠ v,
   v is an internal vertex. Split at v. The predecessor and successor of v in p
   are among {n1, n2}. Since p is a path, the predecessor ≠ n1 (as n1 = last),
   so predecessor = n2. Then we can shortcut: t →p₁→ n2 →(path in G')→ n1.
   But we need n2 reachable from n1 in G'...

This is circular. Please provide a COMPLETE working Lean 4 proof, even if long.
Key API: `Walk.toPath`, `Walk.IsPath.support_nodup`, `SimpleGraph.induce_adj`.

# Question: How to prove `closedGraph_cutVertex_preserved_of_erase` sorry

## Location

`BEI/PrimeDecompositionDimension.lean`, line 1278.

## Goal

```
⊢ ¬SameComponent G (S.erase i) a b
```

Full context: `n : ℕ`, `G : SimpleGraph (Fin n)`, `hClosed : IsClosedGraph G`,
`hConn : G.Connected`, `hCond : SatisfiesProp1_6Condition n G`, `S : Finset (Fin n)`,
`i j : Fin n`, `hjSi : j ∈ S.erase i`, `hcutj : IsCutVertexRelative G S j`,
`hjS : j ∈ S`, `hij : j ≠ i`, `a b : Fin n`, `haS : a ∉ S`, `hbS : b ∉ S`,
`hsc_ej : SameComponent G (S.erase j) a b`, `hnotsc_S : ¬SameComponent G S a b`,
`haSi : a ∉ S.erase i`, `hbSi : b ∉ S.erase i`,
`herase_sub : (S.erase i).erase j ≤ S.erase j`,
`hsc_eij : SameComponent G ((S.erase i).erase j) a b`.

## Mathematical proof (verified by hand)

Proof by contradiction. Assume `SameComponent G (S.erase i) a b`.
Derive `SameComponent G S a b`, contradicting `hnotsc_S`.

### Step 0 — Trivial case

If `i ∉ S`, then `S.erase i = S` and `hsc_Si` directly contradicts `hnotsc_S`.

### Step 1 — Extract bridge vertices

**From `hsc_ej` and `hnotsc_S`**:

Show j is reachable from a in `G[V \ (S \ {j})]` (contrapositive: if not
reachable, the path from a to b avoids j and lifts to `G[V \ S]`,
contradicting `¬SC(S) a b`). This argument is already proved inline at
lines 1154–1181 of the same file (`componentCount_lt_of_merged`).

From the Walk from a to j: at the *first* visit to j, the predecessor
`u₁ ∈ V \ S` satisfies `G.Adj u₁ j` and the prefix walk (before the first
j-visit) is entirely in `V \ S`, giving `SameComponent G S a u₁`.

Similarly j is reachable from b. Extract `v₁ ∈ V \ S` with `G.Adj j v₁`
and `SameComponent G S v₁ b`.

**From `hsc_Si` (the contradiction assumption) and `hnotsc_S`**: same
extraction for i, giving `u₂, v₂ ∈ V \ S` with `G.Adj u₂ i`, `G.Adj i v₂`,
`SameComponent G S a u₂`, `SameComponent G S v₂ b`.

### Step 2 — Gap analysis: u₁ < j < v₁ (and u₂ < i < v₂)

Since `u₁ ∈ C_a` and `v₁ ∈ C_b` (components of a and b in `G[V \ S]`),
and `C_a ≠ C_b`, the closedness conditions force:

- If `u₁ > j` and `v₁ > j`: condition (1) of `IsClosedGraph` gives
  `G.Adj u₁ v₁`, so `SC(S) u₁ v₁ → SC(S) a b`. Contradiction.
- If `u₁ < j` and `v₁ < j`: condition (2) gives `G.Adj u₁ v₁`. Same.
- If `u₁` and `v₁` are in the same "range" as j (e.g., j is inside C_a's
  interval): `closedGraph_adj_between` applied to `G.Adj j v₁` gives
  `G.Adj j w` for every `w` between j and v₁, including any C_a element
  past j; then condition (1) gives `G.Adj w v₁`, merging C_a and C_b.

Therefore `u₁ < j < v₁`. Same argument gives `u₂ < i < v₂`.

### Step 3 — Apply `SatisfiesProp1_6Condition`

WLOG `i < j` (case `j < i` is symmetric, swapping roles of the bridge
vertices).

From `G.Adj u₁ j` with `u₁ < j`, and `i < j` (so `i + 1 ≤ j`),
`closedGraph_adj_between` gives `G.Adj u₁ ⟨i.val + 1, _⟩`.

Case `v₂.val > i.val + 1`:
Apply `SatisfiesProp1_6Condition` with `α = u₁`, `β = i`, `γ = v₂ - 1`:
  - `u₁ < i < v₂ - 1` ✓
  - `G.Adj u₁ ⟨i.val + 1, _⟩` ✓ (derived above)
  - `G.Adj i ⟨(v₂-1).val + 1, _⟩ = G.Adj i v₂` ✓

Conclusion: `G.Adj u₁ v₂`.

Case `v₂.val = i.val + 1`: `G.Adj u₁ v₂ = G.Adj u₁ ⟨i.val + 1, _⟩`,
already derived from `closedGraph_adj_between`.

### Step 4 — Contradiction

`G.Adj u₁ v₂` with `u₁, v₂ ∈ V \ S` gives `SameComponent G S u₁ v₂`.
By transitivity: `SC(S) a u₁ → SC(S) u₁ v₂ → SC(S) v₂ b → SC(S) a b`.
Contradicts `hnotsc_S`. QED.

## Implementation obstacles

### 1. Bridge vertex extraction (Step 1)

The hardest part to formalize. Requires:
- Showing j (resp. i) is reachable from a and from b in the erased
  induced subgraph (contrapositive argument, already done inline for
  `componentCount_lt_of_merged` at lines 1154–1181).
- Converting `Reachable` to `Walk`, then extracting the *first visit*
  to j by induction on the Walk, yielding the predecessor vertex and
  the lifted prefix.

Consider factoring a helper lemma:
```lean
private lemma exists_adj_bridge_of_sameComponent_erase
    {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} {j a b : Fin n}
    (hjS : j ∈ S) (haS : a ∉ S) (hbS : b ∉ S)
    (hsc : SameComponent G (S.erase j) a b)
    (hnotsc : ¬SameComponent G S a b) :
    (∃ u, u ∉ S ∧ G.Adj u j ∧ SameComponent G S a u) ∧
    (∃ v, v ∉ S ∧ G.Adj j v ∧ SameComponent G S v b)
```

### 2. Gap analysis (Step 2)

Requires case-splitting on `u₁ < j ∨ u₁ > j` (and same for v₁) using
`Fin.lt_or_gt_of_ne` or `Nat.lt_or_gt_of_ne`, then applying the two
closedness conditions. About 4 cases, each ~5 lines.

### 3. Fin arithmetic for Prop 1.6 (Step 3)

`SatisfiesProp1_6Condition` uses `⟨j.val + 1, hj⟩` syntax. Need to
carefully construct the `Fin n` witnesses and prove the bounds
(`j.val + 1 < n`, etc.) from the gap ordering.

## Estimated size

~100–150 lines of Lean total (including the helper lemma if factored).

## Key lemmas to use

- `closedGraph_adj_between` (CohenMacaulay.lean:711)
- `closedGraph_adj_consecutive` (GraphProperties.lean:502)
- `SameComponent.trans`, `SameComponent.symm` (PrimeIdeals.lean)
- `SameComponent_mono` (MinimalPrimes.lean:267)
- `sameComponent_to_reachable` (MinimalPrimes.lean:275)
- `reachable_induce_imp_sameComponent` (PrimeIdeals.lean:1277)
- `IsClosedGraph` conditions (1) and (2) via `hClosed.1` and `hClosed.2`
- `SatisfiesProp1_6Condition` via `hCond`

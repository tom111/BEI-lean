# Answer Guide: `closedGraph_cutVertex_preserved_of_erase`

## Preserved question

Claude asked how to prove the remaining `sorry` in:

- `/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean`

The target subgoal is:

```lean
⊢ ¬ SameComponent G (S.erase i) a b
```

inside:

```lean
closedGraph_cutVertex_preserved_of_erase
```

The hand proof has already been worked out. The problem is no longer mathematical
discovery. The problem is Lean packaging.


## Current status

The direct equidimensional Prop. 1.6 route is the active track.

The current proof attempt is looping because it tries to formalize the whole
contradiction at once. That is too large. The right move is to split off the
bridge-vertex extraction as a helper theorem and only then return to the main lemma.


## Main recommendation

Do **not** attack `closedGraph_cutVertex_preserved_of_erase` as one 100–150 line proof.

Instead:

1. factor the bridge-vertex extraction into a dedicated helper;
2. prove that helper by reusing the path-lifting pattern already present in
   `componentCount_lt_of_merged`;
3. only then do the gap analysis and the final contradiction.


## Why this is the right decomposition

The hard part is not the closed-graph combinatorics. Claude already has that on paper.

The hard part in Lean is:

- start from `SameComponent G (S.erase j) a b` and `¬ SameComponent G S a b`;
- show a path from `a` to `b` in `G[V \ (S \ {j})]` must touch `j`;
- extract a predecessor/successor of the first/last `j`-visit that lies in `V \ S`;
- lift the relevant prefixes back to `G[V \ S]`.

That is exactly the kind of local path bookkeeping that should be isolated once and then
reused.


## Recommended helper theorem

First prove a helper of roughly this shape:

```lean
private lemma exists_adj_bridge_of_sameComponent_erase
    {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)} {j a b : Fin n}
    (hjS : j ∈ S) (haS : a ∉ S) (hbS : b ∉ S)
    (hsc : SameComponent G (S.erase j) a b)
    (hnotsc : ¬ SameComponent G S a b) :
    (∃ u, u ∉ S ∧ G.Adj u j ∧ SameComponent G S a u) ∧
    (∃ v, v ∉ S ∧ G.Adj j v ∧ SameComponent G S v b) := by
  ...
```

This is the real missing interface.

Once you have it, apply it twice:

- once with `j` and `hsc_ej`
- once with `i` and the contradiction assumption `SameComponent G (S.erase i) a b`

That gives the four bridge vertices `u₁, v₁, u₂, v₂` cleanly.


## How to prove the helper

Reuse the exact proof pattern from:

```lean
componentCount_lt_of_merged
```

in the same file.

That lemma already proves a path in `G[V \ (T.erase j)]` from `a` to `b` cannot avoid
`j`, by lifting any `j`-avoiding path to `G[V \ T]`.

So do not rediscover that argument. Extract it.

### Suggested sub-helpers

If the combined bridge lemma is too large, split it into:

```lean
private lemma reachableErase_forces_reachable_to_erased_vertex
    ...
```

and then

```lean
private lemma exists_adj_predecessor_of_reachable_erased_vertex
    ...
```

but only if needed. Prefer one helper theorem if the proof stays readable.


## Concrete proof packaging advice

### Step 1. Reachability to `j`

From `SameComponent G (S.erase j) a b` and `¬ SameComponent G S a b`,
show `j` is reachable from `a` in `G[V \ (S.erase j)]`.

This is already essentially present inside `componentCount_lt_of_merged`.

### Step 2. Convert reachability to a walk

Use the existing `sameComponent_to_reachable` / reachable-to-walk API already used in
the repo. Do not invent a separate path encoding.

### Step 3. First-visit extraction

Induct on the walk and stop at the first visit to `j`.

Target output:

- `u ∉ S`
- `G.Adj u j`
- `SameComponent G S a u`

Then apply the same argument from the other end to get `v`.

If orientation is awkward, derive the second half by symmetry:

- use `SameComponent.symm`
- run the same helper from `b` to `a`
- flip the edge witness back

That is usually simpler than writing a separate “last visit” induction.


## After the helper lands

Return to:

```lean
closedGraph_cutVertex_preserved_of_erase
```

Then the proof should split into:

1. contradiction assumption `SameComponent G (S.erase i) a b`
2. bridge extraction for `j`
3. bridge extraction for `i`
4. gap analysis:
   - show `u₁ < j < v₁`
   - show `u₂ < i < v₂`
5. apply `SatisfiesProp1_6Condition` plus `closedGraph_adj_between`
6. derive an edge in `G[V \ S]` across the gap
7. contradict `hnotsc_S`


## False routes

- Do not keep expanding the long comment inside the source.
- Do not try to prove the whole theorem before extracting the bridge helper.
- Do not switch back to the CM-transfer route.
- Do not touch docs in this round unless the theorem genuinely lands.


## Definition of done

Best outcome:

- `exists_adj_bridge_of_sameComponent_erase` proved
- `closedGraph_cutVertex_preserved_of_erase` proved
- the direct Prop. 1.6 route builds without `sorry`

Minimum acceptable outcome:

- the bridge helper proved
- the remaining gap reduced to the closed-graph gap analysis only


## Files likely involved

- `/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean`
- `/home/tom/BEI-lean/BEI/CohenMacaulay.lean`

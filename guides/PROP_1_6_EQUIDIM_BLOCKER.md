# Guide: Proposition 1.6 Direct Equidim Blocker

## Task

Finish the active direct proof blocker for Proposition 1.6 under the repo's local
equidimensional surrogate.

The current unfinished theorem is:

```lean
closedGraph_cutVertex_preserved_of_erase
```

in:

- `/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean`

This is the live blocker on the direct route. Do not switch back to the Gröbner
transfer route in this packet.


## Current Lean status

The direct route now lives in `BEI/PrimeDecompositionDimension.lean`:

- `componentCount_lt_of_merged` is proved
- `closedGraph_minimalPrime_componentCount_eq` has been restructured around erasing one
  vertex from `S`
- direct `prop_1_6` now depends on this route

The remaining `sorry` is inside
`closedGraph_cutVertex_preserved_of_erase`.

The key missing step is proving that after erasing `i` from `S`, the witnesses `a, b`
for the cut-vertex role of `j` are still separated:

```lean
¬ SameComponent G (S.erase i) a b
```


## Why the current attempt is looping

The current proof has already gone in circles on arithmetic and then on a vague
"path through `i`" contradiction. Do not continue by growing that comment block.

The job is now to isolate one correct graph lemma and prove it cleanly.


## Recommended strategy

Work locally around the missing separation statement.

1. Keep the existing setup:
   - `i ∈ S`
   - `j ∈ S.erase i`
   - witnesses `a, b` from the cut-vertex property of `j` relative to `S`
2. Assume for contradiction:

```lean
SameComponent G (S.erase i) a b
```

3. Analyze a path in `G[V \ (S.erase i)]` from `a` to `b`.
4. Because `a` and `b` are not in the same component of `G[V \ S]`, any such path must
   use `i`.
5. Use the closed-graph interval lemmas from `BEI/CohenMacaulay.lean`:
   - `closedGraph_adj_between`
   - `reflTransGen_convex_closed`
   - `closedGraph_componentCount_le_card_add_one`
6. Use `SatisfiesProp1_6Condition` exactly where needed to rule out the bad configuration
   in which a path through `i` reconnects the two sides after `j` is removed.


## Good intermediate theorem

If the direct contradiction is still too messy, first isolate a smaller helper.

Example shape:

```lean
private theorem sameComponent_erase_forces_sameComponent_original
    ...
    (hpath : SameComponent G (S.erase i) a b) :
    SameComponent G S a b := by
  ...
```

or an equivalent lemma saying that any `a`-to-`b` path in `G[V \ (S.erase i)]`
avoiding `j` can be pushed to one in `G[V \ S]`.

That is the real structural gap. Prove that first if needed.


## False routes

- Do not go back to the broken arithmetic squeeze.
- Do not keep a long exploratory comment in the source as a placeholder for proof.
- Do not restart the full paper-faithful CM-transfer route.
- Do not touch docs or guides unless this theorem genuinely lands.


## Definition of done

Best outcome:

- `closedGraph_cutVertex_preserved_of_erase` fully proved
- `closedGraph_minimalPrime_componentCount_eq` fully proved
- direct `prop_1_6` route builds with no `sorry` on this path

Minimum acceptable outcome:

- one smaller helper theorem isolating the `SameComponent` contradiction cleanly
- and one exact Lean blocker if the main theorem still does not land


## Files likely involved

- `/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean`
- `/home/tom/BEI-lean/BEI/CohenMacaulay.lean`

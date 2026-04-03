# Answer to Q9: Cycle `componentCount` Combinatorics

## Preserved question

For the unmixed branch of Corollary 3.7, the remaining work is a small cluster of
cycle-graph combinatorial lemmas stated in terms of:

```lean
componentCount G S := Nat.card (G.induce {v : V | v ∉ S}).ConnectedComponent
```

The four target facts are:

1. removing one vertex from a cycle leaves one component;
2. on a cycle of length at least 4, there exist nonadjacent vertices;
3. removing two nonadjacent vertices leaves two components;
4. then the cut-vertex inequalities needed for the minimal-prime argument follow.

The question asked for the best strategy, especially because:

- `componentCount` is defined via `Nat.card` of `ConnectedComponent`;
- induced subgraphs on subtypes are awkward;
- the repo uses `IsCycleGraph`, not Mathlib's walk-cycle structures.


## Short answer

Do **not** attack these lemmas by reasoning directly with `Nat.card` of connected
components from the start.

Instead, prove them in two layers:

1. graph-structure lemmas about induced subgraphs of a cycle after deleting vertices;
2. convert those structural results into `componentCount` values.

This keeps the `Nat.card` / subtype machinery at the very end.


## Best strategy

## Layer 1: structural lemmas on induced subgraphs

The core facts you want are really:

### A. Removing one vertex from a cycle gives a connected acyclic graph with degree ≤ 2

This should characterize a path-like graph, hence exactly one connected component.

### B. Removing two nonadjacent vertices from a cycle gives exactly two connected pieces

Again, prove this structurally before touching `componentCount`.

In other words, first show:

- connectivity / non-connectivity;
- number of connected pieces via explicit decomposition;

and only then translate to `componentCount`.


## Layer 2: `componentCount` conversion lemmas

Create small helper lemmas like:

- `componentCount_eq_one_iff_connected` for nonempty induced subgraphs;
- a lemma that a graph with exactly two connected components has `componentCount = 2`;
- or a direct bijection from connected components to `Fin 2` when you have an explicit
  two-piece decomposition.

Do not try to prove `componentCount = 1` or `= 2` from scratch each time.


## Answers to the specific lemma questions

## Lemma 1: singleton removal

This should be handled by proving the induced graph after deleting one vertex is connected.

The cleanest route is:

1. use `IsCycleGraph` to note every vertex has exactly two neighbors and the graph is connected;
2. deleting one vertex turns the cycle into a path-like graph;
3. therefore the induced graph is connected;
4. hence `componentCount G {v} = 1`.

Do not reason via `Nat.card` first.


## Lemma 2: existence of nonadjacent vertices

This one should be easy.

Choose any vertex `u`.
It has exactly two neighbors.
If `|V| ≥ 4`, there exists some `w ≠ u` not equal to either neighbor.
Then `w` is not adjacent to `u`.

This is mainly a finite-cardinality argument plus the "exactly two neighbors" clause.


## Lemma 3: pair of nonadjacent deletions

Use a two-step structural argument:

1. remove `u` first; by Lemma 1, you get a connected path-like graph;
2. because `w` was not adjacent to `u` in the cycle, `w` is an internal vertex of that path;
3. removing an internal vertex of a path splits it into two connected components.

So this lemma reduces to a general path-graph fact:

```text
removing an internal vertex from a path gives exactly two components
```

That is the right abstraction to isolate.


## Lemma 4: cut-vertex verification

This should indeed be immediate once Lemmas 1 and 3 are in place:

- `componentCount G ({u,w}.erase u) = componentCount G {w} = 1`;
- `componentCount G {u,w} = 2`;
- so `1 < 2`.

This part should stay very short.


## Recommended proof decomposition

## Step 1: add path-like lemmas, not cycle lemmas, where possible

The key reusable helper is not "cycle minus two vertices = two components" directly.
It is:

- path minus an internal vertex has two components.

This may help elsewhere too.

## Step 2: prove cycle-minus-one-vertex is path-like

This is the main cycle-specific bridge theorem.

## Step 3: derive the componentCount numerics

Once the structural theorems exist, the `componentCount` equalities should become short.


## Final recommendation

Treat these as a small graph-structure subproject:

1. prove cycle-minus-one-vertex is connected;
2. prove path-minus-internal-vertex has two components;
3. then convert to `componentCount = 1` and `componentCount = 2`.

That is cleaner than wrestling with `Nat.card` and induced-subtype graphs from the start.

# Proof Plan: What's Ready to Apply

## Proved in lean_run_code (not yet in the repo)

### cycle_induce_preconnected — PROVED

The proof compiles in `lean_run_code` but has not been written into
`BEI/MinimalPrimes.lean` yet due to Unicode encoding issues with the Edit tool.

**Guide followed:** ANSWER_13 (IsCycles approach)

**Proof strategy:**
1. Bridge `IsCycleGraph → IsCycles` via `isCycles_of_isCycleGraph`
2. Get Hamiltonian cycle walk `c : G.Walk v v` from
   `IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp`
3. `c.tail` is a path (by `IsCycle.isPath_tail`)
4. Every vertex `t ≠ v` is in `c.tail.support` (by `G.Connected` + component)
5. `c.tail.takeUntil t` gives a walk from `c.snd` to `t`
6. `v ∉` that walk's support (by `endpoint_notMem_support_takeUntil`)
7. Transfer to `G.induce S` via `reachable_induce_of_walk` helper
8. Compose two such walks (to `t` and to `n1`) for the final Reachable

**Helpers needed (also proved):**
- `reachable_induce_of_walk`: induction on Walk, lifting G-edges to G'-edges
- `isCycles_of_isCycleGraph`: `Set.ncard_eq_two` + extensionality

**What blocks applying it:**
The `Edit` tool cannot match the existing sorry text because the file contains
multi-byte Unicode characters (∈, ≠, ⟨, ⟩). A manual file write or a Python
script that works by line number (not string matching) is needed.

**Needed imports:** `Mathlib.Combinatorics.SimpleGraph.Matching` (already added)

**MaxHeartbeats:** 1600000 (the proof is expensive)

## What remains after this proof

### cycle_componentCount_pair_nonadj (line 620)

Still sorry. The ANSWER_13 approach (split cycle at internal vertex w using
`takeUntil`/`dropUntil`) is mathematically clear but has not been attempted
in code yet. This is harder than Lemma 1 because it needs to prove exactly
2 components (lower bound + upper bound).

### Corollary 3.4 assembly (PrimeDecompositionDimension.lean)

The equidimensionality step is proved (third isomorphism via
`factor_ker` + `quotientKerEquivOfSurjective`). The remaining sorry is
the final assembly: "sup of equal values = common value". This needs
showing that for every S, `dim(R/P_S) ≤ dim(R/P_∅)` using the CM
equidimensionality + monotonicity.

### Corollary 3.7 CM (PrimeDecomposition.lean)

Blocked on deeper CM theory (determinantal CM results).

## Summary of sorry counts if cycle_induce_preconnected is applied

| File | Before | After |
|------|--------|-------|
| MinimalPrimes.lean | 2 | 1 |
| PrimeDecompositionDimension.lean | 1 | 1 |
| PrimeDecomposition.lean | 1 | 1 |
| CohenMacaulay.lean | 3 | 3 |
| HeightAdditivity.lean | 2 | 2 |
| **Total** | **9** | **8** |

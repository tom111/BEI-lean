# Handoff: Theorem 2.1 — Coprime Case Completion

## Status

**File:** `BEI/GroebnerBasis.lean`
**Commit:** `2ee1cfd` — compiles cleanly, 0 errors
**Theorem 2.1 sorries:** 5 in same-component case (lines 2410, 2417, 2488, 2492, 2573)
**Other:** 1 pre-existing sorry in Corollary 2.2 (line 3454, out of scope)

The **different-components case** (Sorry 2) is **fully proved** (~lines 2347-2560).

## What was accomplished

1. **Different-components case:** Complete proof using cross-condition divisibility, `isRemainder_fij_via_groebnerElement` for each term, combined via `isRemainder_add`.

2. **Same-component case structure:**
   - `fij_coprime_swap` applied to rewrite the S-polynomial
   - Walk construction via `walk_from_shared_first` with drops of reversed paths through shared vertex v
   - Q₁ = D + single(inl l) + single(inr j), Q₂ = D + single(inl k) + single(inr i)
   - Case split `i < k` vs `k < i` (line 2404/2573)
   - Sub-case split `j < l` vs `l < j` (lines 2411/2486)
   - Algebraic equality, degree inequality, `isRemainder_add` combination: all proved for the `i < k, j < l` sub-case (lines 2419-2484)
   - Symmetric sub-cases structured via `fij_antisymm`

3. **Infrastructure added:**
   - `isRemainder_fij_via_two_walks` (line ~1317): splits walk at intermediate vertex, x-coverage for first half, y-coverage for second half
   - Various coverage helper lemmas

## The core remaining problem

All 5 sorries reduce to proving:

```
IsRemainder (monomial Q 1 * fij a b) (groebnerBasisSet G) 0
```

given a walk from `a` to `b` whose internal vertices come from two admissible paths π and σ that share a vertex. The walk has **mixed x/y coverage**: π-vertices need `d_q(inl w) ≥ 1` and σ-vertices need `d_q(inr w) ≥ 1`.

### Why existing lemmas don't work

| Lemma | Problem |
|-------|---------|
| `isRemainder_fij_of_covered_walk` (x-variant) | Needs `d_q(inl w) ≥ 1` for ALL bad vertices. σ-vertices between endpoints only have `d_q(inr w) ≥ 1`. |
| `isRemainder_fij_of_covered_walk_y` (y-variant) | Needs `d_q(inr w) ≥ 1` for ALL bad vertices. π-vertices between endpoints only have `d_q(inl w) ≥ 1`. |
| `isRemainder_fij_via_two_walks` | Uses x for first half, y for second. But π and σ vertices are interleaved in the walk — no clean split separates them. |
| `isRemainder_fij_via_groebnerElement` | Needs `d_α ≤ d_q` for a specific admissible path α. The pathMonomial uses fixed inl/inr at each position, but available coverage is `∨`. |

### What IS true (the mathematical argument)

For each internal vertex w of the walk between a and b:
- If w comes from π: `dπ(inl w) = 1`, both fij degrees at inl w are 0, so `sPolyD_ge_of_zero` gives `D(inl w) ≥ 1`, hence `Q(inl w) ≥ 1`.
- If w comes from σ: `dσ(inr w) = 1`, both fij degrees at inr w are 0, so `D(inr w) ≥ 1`, hence `Q(inr w) ≥ 1`.
- If w = j (between i and k when j < k): `Q₁(inr j) = D(inr j) + 1 ≥ 1` from the explicit `single(inr j)` term.
- If w = k (between j and l when j < k): `Q₂(inl k) = D(inl k) + 1 ≥ 1` from the explicit `single(inl k)` term.
- If w = v (shared vertex): covered by π or σ membership.

So every vertex has `d_q(inl w) ≥ 1 ∨ d_q(inr w) ≥ 1`, but which side of the ∨ varies by vertex.

## Recommended approach: `isRemainder_fij_of_mixed_walk`

Write a new lemma with statement:

```lean
private theorem isRemainder_fij_of_mixed_walk (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b : V) (τ : List V) (d_q : BinomialEdgeVars V →₀ ℕ),
    τ.length ≤ n → a < b →
    τ.head? = some a → τ.getLast? = some b →
    τ.Nodup → τ.Chain' (fun u v => G.Adj u v) →
    (∀ w ∈ internalVertices τ, d_q (Sum.inl w) ≥ 1 ∨ d_q (Sum.inr w) ≥ 1) →
    binomialEdgeMonomialOrder.IsRemainder
      (monomial d_q 1 * fij (K := K) a b) (groebnerBasisSet G) 0
```

### Proof strategy: first-vertex induction

Induct on `n` (walk length bound). Process the **first internal vertex** v₁ (the second element of the walk):

1. **Base case** (walk = [a, b]): a adj b (from chain). Use `isRemainder_fij_via_groebnerElement` with trivial admissible path [a, b] (pathMonomial = 1, divisibility trivial).

2. **Inductive step** (walk = [a, v₁, rest..., b]):
   - From chain: a adj v₁.
   - From coverage ∨: `d_q(inl v₁) ≥ 1 ∨ d_q(inr v₁) ≥ 1`.
   - Choose telescope based on coverage:

   **If `d_q(inl v₁) ≥ 1` (x-telescope):**
   ```
   x(v₁) * fij(a, b) = x(a) * fij(v₁, b) + x(b) * fij(a, v₁)
   ```
   - `fij(a, v₁)`: single edge (a adj v₁). IsRemainder via trivial admissible path.
   - `fij(v₁, b)`: shorter walk [v₁, rest..., b]. Coverage transfers because d₁ = d_q − single(inl v₁) + single(inl a) agrees with d_q on all internal vertices of the shorter walk (v₁ and a are NOT internal vertices of [v₁, rest..., b]).
   - Handle v₁ > b case separately (walk reversal, `fij_antisymm`).
   - Combine via `isRemainder_add` + `degree_bounds_of_ne`.

   **If `d_q(inr v₁) ≥ 1` (y-telescope):**
   ```
   y(v₁) * fij(a, b) = y(b) * fij(a, v₁) + y(a) * fij(v₁, b)
   ```
   - Same structure with inr instead of inl.

### Why this works (coverage transfer)

After x-telescope at v₁, the monomial for the recursive piece is d₁ = d_q − single(inl v₁) + single(inl a).

For any internal vertex w of the shorter walk [v₁, rest..., b]:
- w ≠ v₁ (v₁ is the head, not internal)
- w ≠ a (a is not in the shorter walk; nodup from original walk)
- So d₁(inl w) = d_q(inl w) and d₁(inr w) = d_q(inr w)
- Coverage transfers: d₁(inl w) ≥ 1 ∨ d₁(inr w) ≥ 1. ✓

### Implementation notes

- The proof follows the same structure as `isRemainder_fij_of_covered_walk` (lines ~600-780) but with per-vertex telescope choice.
- The `fij_x_telescope` and `fij_telescope` (y-version) identities are in HerzogLemmas.lean.
- For the degree bounds in `isRemainder_add`, follow the pattern at lines 828-857.
- `unfold BinomialEdgeVars` is needed for Finsupp arithmetic.
- Handle a < v₁ < b (bad vertex), v₁ < a (below), v₁ > b (above) as separate sub-cases.
- Estimated size: ~200 lines (similar to existing covered walk proof).

### Alternative: avoid the mixed-walk lemma entirely

If writing the mixed-walk lemma proves too difficult, an alternative approach:

1. Case-split on `le_or_lt k j` (whether j is between i and k):
   - `k ≤ j`: ALL walk bad-vertices are from σ (π-vertices satisfy w > j ≥ k, outside (i,k)). Use y-variant directly.
   - `j < k`: Use `isRemainder_fij_via_two_walks` with split at j. Walk i→j = π (no bad vertices, vacuous coverage). Walk j→k needs SEPARATE construction via `walk_from_shared_first G v j k (π.drop(π.idxOf v)) (σ.reverse.drop(σ.reverse.idxOf v)) ...`. This walk's bad vertices (j < w < k) are all from σ → y-coverage works.

   **Caveat:** The walk j→k might include π-vertices > j between j and k. But I verified that π-vertices in the π.drop(idxOf v) sub-path satisfy w < i or w > j (admissible condition). Those with w > j and j < w < k ARE problematic for y-coverage if they're not in σ. This approach only works if such vertices don't appear in the walk from j to k — which is NOT guaranteed.

2. Similarly case-split for fij(j,l).

The mixed-walk lemma is the cleanest solution.

## Using the mixed-walk lemma to fill the sorries

Once `isRemainder_fij_of_mixed_walk` compiles, fill each sorry with:

```lean
exact isRemainder_fij_of_mixed_walk G τ.length a b τ Q d_q le_rfl hab
  hτ_h hτ_l hτ_nd hτ_w (by
    intro w hw_int
    -- Trace w through walk construction to π or σ membership
    -- Use sPolyD_ge_of_zero + pathMonomial exponent lemmas
    -- Handle w = j or w = k via the explicit extra single terms in Q
    sorry)
```

The coverage proof at each call site requires:
1. From `hτ_ik_v`: w ∈ internalVertices(π.reverse.drop) ∨ w ∈ internalVertices(σ.reverse.drop) ∨ w = v
2. For each case, show `Q(inl w) ≥ 1 ∨ Q(inr w) ≥ 1`:
   - From π: w ∈ π, w satisfies admissible condition → dπ exponent ≥ 1 at appropriate position → sPolyD_ge → D ≥ 1 → Q ≥ 1
   - From σ: similar
   - w = v: v ∈ π ∩ σ, same analysis
3. For w = j (in fij(i,k) case): Q₁(inr j) = D(inr j) + 1 ≥ 1 from explicit term
4. For w = k (in fij(j,l) case): Q₂(inl k) = D(inl k) + 1 ≥ 1 from explicit term

## Stashed work

`git stash list` shows broken attempt at mixed-walk lemma with first-vertex induction. It has the right STRUCTURE but 16+ compilation errors in degree-bounds proofs (wrong argument order for `fij_degree`, Finsupp arithmetic needing `unfold BinomialEdgeVars`). May be salvageable with mechanical fixes, but the stash also modified the theorem_2_1 proof structure in ways that introduced additional errors.

## File map (relevant sections)

| Lines | Content |
|-------|---------|
| 600-780 | `isRemainder_fij_of_covered_walk` (x-variant) — TEMPLATE for mixed-walk |
| 780-960 | `isRemainder_fij_of_covered_walk_y` (y-variant) |
| 1317-1415 | `isRemainder_fij_via_two_walks` |
| 1460-1680 | `walk_from_shared_first` infrastructure |
| 2200-2340 | `theorem_2_1` — different-components case (DONE) |
| 2340-2580 | `theorem_2_1` — same-component case (5 sorries) |
| 2410 | Sorry: `IsRemainder (Q₁ * fij i k) G 0` (i<k, j<l) |
| 2417 | Sorry: `IsRemainder (Q₂ * fij j l) G 0` (i<k, j<l) |
| 2488 | Sorry: `IsRemainder (Q₁ * fij i k) G 0` (i<k, l<j) |
| 2492 | Sorry: `IsRemainder (Q₂ * fij l j) G 0` (i<k, l<j) |
| 2573 | Sorry: full k<i case |

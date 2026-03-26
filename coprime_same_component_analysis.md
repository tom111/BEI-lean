# Coprime Same-Component Case Analysis

## Location
`BEI/GroebnerBasis.lean`, line 2200, inside `theorem_2_1`.

## Goal
```
hshared : ∃ v ∈ π, v ∈ σ
⊢ IsRemainder (monomial D (1 * 1) * (x l * y k * fij i j - x j * y i * fij k l)) (groebnerBasisSet G) 0
```

where π is an admissible path from i to j, σ is an admissible path from k to l,
with i ≠ k, j ≠ l, i < j, k < l, and fij(i,j) and fij(k,l) have coprime leading monomials.

## Why Existing Approaches Fail

### Direct approach (no coprime swap)
Express as `monomial Q₁ 1 * fij i j - monomial Q₂ 1 * fij k l` where
Q₁ = D + single(inl l) + single(inr k) and Q₂ = D + single(inl j) + single(inr i).

**Issue**: dπ ≤ Q₁ fails at `inl k` when `k ∈ internalVertices π` (dπ(inl k) = 1 but D(inl k) = 0).
Similarly, dσ ≤ Q₂ fails at `inr j` when `j ∈ internalVertices σ`.

### Coprime swap approach
Rewrite using fij_coprime_swap: RHS = `x l * y j * fij i k - x k * y i * fij j l`.
Express as monomial R₁ 1 * fij i k - monomial R₂ 1 * fij j l.

For fij(i,k) with i < k: need walk from i to k through shared vertex v.

**Issue with isRemainder_fij_of_covered_walk (x-variant)**:
Bad vertices w with i < w < k from σ (w < k): have R₁(inr w) ≥ 1 but need R₁(inl w) ≥ 1. Fails.

**Issue with isRemainder_fij_of_covered_walk_y (y-variant)**:
Bad vertices w with i < w < k from π (w > j): have R₁(inl w) ≥ 1 but need R₁(inr w) ≥ 1. Fails.

**Mixed coverage issue**: Bad vertices from π need x-coverage, bad vertices from σ need y-coverage.
Neither the x-variant nor y-variant handles both uniformly.

### Mixed-coverage covered walk lemma
Attempted to generalize coverage to allow `d_q(inl v) ≥ 1 ∨ d_q(inr v) ≥ 1` for bad vertices.

**Issue**: After telescoping, the sub-walk's above/below endpoint conditions require SPECIFIC
variable (inl for above, inr for below). Mixed coverage doesn't guarantee the right one.

## Correct Approach (Proposed)

### Manual y-telescope at shared vertex v (when i < v < k)
When the shared vertex v satisfies i < v < k, R₁(inr v) ≥ 1 always holds (shown in analysis).
Use y-telescope: y_v * fij(i,k) = y_k * fij(i,v) + y_i * fij(v,k).

- fij(i,v): walk from prefix of π (i to v). Bad vertices from π only: w > j, so dπ(inl w) ≥ 1.
  Use isRemainder_fij_of_covered_walk (x-variant). ✓

- fij(v,k): walk from reversed prefix of σ (v to k). Bad vertices from σ only: w < k, so dσ(inr w) ≥ 1.
  Use isRemainder_fij_of_covered_walk_y (y-variant). ✓

### When v is NOT between i and k
Need to find or construct an intermediate vertex between i and k to telescope at.
Options:
1. Find another shared vertex in (i,k) if one exists.
2. Use a "pivot" vertex: any vertex on the walk with appropriate coverage.
3. Two-stage telescoping: first at a π-vertex (x-variant), then at a σ-vertex (y-variant).

### Alternative: New lemma combining two covered walks
```
isRemainder_fij_via_two_walks G a c b τ₁ τ₂ d_q
  (walk from a to c with x-coverage) (walk from c to b with y-coverage) d_q(inr c) ≥ 1
  → IsRemainder (monomial d_q 1 * fij a b) G 0
```
This uses y-telescope at c, then delegates sub-walks to existing lemmas.

## Infrastructure Available
- `walk_from_shared_first`: construct nodup walk from b to c given paths from shared vertex a
- `isRemainder_fij_of_covered_walk`: x-variant covered walk
- `isRemainder_fij_of_covered_walk_y`: y-variant covered walk
- `fij_coprime_swap`: algebraic identity for coprime S-polynomial
- `fij_telescope`, `fij_x_telescope`: y and x telescope identities
- `isRemainder_add`, `isRemainder_neg'`: combining IsRemainder results
- `degree_bounds_of_ne`: degree bounds for isRemainder_add

## Estimated Effort
~200-400 lines for the new lemma + ~200 lines for using it in the sorry.

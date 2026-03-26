# Handoff: Theorem 2.1 Coprime Case

## Status (2026-03-26)

`theorem_2_1` in `BEI/GroebnerBasis.lean` has **2 sorries remaining** (plus 1 deferred corollary_2_2).

Both sorries are in the **coprime case** (i≠k, j≠l) of the Buchberger criterion, at lines ~2197 and ~2200. The case is split by `by_cases hshared : ∃ v, v ∈ π ∧ v ∈ σ`.

Everything else in Theorem 2.1 (Cases 1, 4, 5) is fully proved.

## The Coprime Case Goal

After `sPolynomial_monomial_mul` + `sPolynomial_fij_coprime`:
```
IsRemainder (monomial D (1*1) * (x l * y k * fij i j - x j * y i * fij k l)) groebnerBasisSet 0
```
where D = (dπ + deg(fij i j)) ⊔ (dσ + deg(fij k l)) - deg(fij i j) ⊔ deg(fij k l).

## Key Identity (already proved, in HerzogLemmas.lean)

```
fij_coprime_swap : x l * y k * fij i j - x j * y i * fij k l
                 = x l * y j * fij i k - x k * y i * fij j l
```
This swaps pairs (i,j),(k,l) → (i,k),(j,l). Proved by `simp [fij, x, y]; ring`.

## Sorry 1: Same Component (line ~2197)

**Context**: `hshared : ∃ v, v ∈ π ∧ v ∈ σ` — paths share a vertex.

After `rw [fij_coprime_swap]`, the goal becomes:
```
IsRemainder (monomial D (1*1) * (x l * y j * fij i k - x k * y i * fij j l)) groebnerBasisSet 0
```

**Why the swap helps**: The original form has a coverage failure when k ∈ internalVertices π (above j): D(Sum.inl k) = 0 but dπ(Sum.inl k) = 1. In the swapped form, k is an ENDPOINT of fij i k (not internal), so no coverage is needed for it. The coefficient `x_k` in the second term provides `single(Sum.inl k)` which covers k as a "bad" vertex in the walk from j to l.

**Proof plan**:
1. DON'T factor out monomial D — it's needed for coverage.
2. Express as sum of two terms: `monomial(D + single(inl l) + single(inr j)) * fij i k` minus `monomial(D + single(inl k) + single(inr i)) * fij j l`.
3. For each term, apply `isRemainder_fij_of_covered_walk` (or `_y` variant):
   - Walk from min(i,k) to max(i,k): construct from subpaths of π and σ through the shared vertex v.
   - Walk from min(j,l) to max(j,l): similarly.
   - Coverage: D covers internal vertices from π and σ (via sPolyD_ge_of_zero). The extra `single(inr j)` covers j if it's internal to the i→k walk. The extra `single(inl k)` covers k if it's internal to the j→l walk.
4. Combine with `isRemainder_add` (handling subtraction via `isRemainder_neg'`).
5. Degree bounds: the two terms have different leading monomials. Need to prove this — it's analogous to `coprime_degrees_ne` but for the swapped pairs. Since x_i y_k and x_j y_l share no variables (i≠j, k≠l, and Sum.inl ≠ Sum.inr), the degrees differ.

**Walk construction**: Use `walk_from_shared_first` (already proved, ~200 lines). Given shared vertex v ∈ π ∩ σ:
- Subpath of π from i to v: walk from i to v.
- Subpath of σ from k to v: walk from k to v.
- `walk_from_shared_first G v i k (subpath_π) (subpath_σ) ...` gives walk from i to k.
- Similarly for j to l.

**Estimated effort**: ~80-120 lines. The walk construction via shared vertex is the trickiest part.

## Sorry 2: Different Components (line ~2200)

**Context**: `hshared : ∀ v, v ∈ π → v ∉ σ` — no shared vertex.

**Why it's simpler**: When π and σ have disjoint vertex sets:
- dσ(w) = 0 for w involving π's vertices, and vice versa
- deg(fij k l)(w) = 0 for w involving π's vertices, and vice versa
- Therefore D(w) = dπ(w) for π-variables and D(w) = dσ(w) for σ-variables
- So D = dπ + dσ componentwise

**Proof plan**:
1. Show D ≥ dπ componentwise (need: dσ(w) = 0 and deg_kl(w) = 0 for π-variables).
2. Factor: `monomial D * x l * y k * fij i j = monomial(D - dπ) * x l * y k * groebnerElement_π`.
   Since `groebnerElement_π = monomial dπ * fij i j = pathMonomial_π * fij i j ∈ groebnerBasisSet`,
   this is a monomial multiple of a groebnerBasisSet element. `isRemainder_single_mul` applies.
3. Similarly for the second term using groebnerElement_σ.
4. Combine with `isRemainder_sub_mul`:
   - f₁ = groebnerElement_π ∈ groebnerBasisSet ✓
   - f₂ = groebnerElement_σ ∈ groebnerBasisSet ✓
   - f₁ ≠ f₂ (different components → different leading monomials) ✓
   - Degree bounds from `coprime_degrees_ne` + `degree_bounds_of_sub` ✓

**Key lemma needed**: D - dπ = dσ (componentwise, when paths are disjoint). This requires showing dπ and dσ have disjoint support, which follows from hshared + the pathMonomial structure (pathMonomial variables correspond to path vertices).

**Estimated effort**: ~50-80 lines. Mainly Finsupp arithmetic.

## Critical Files

- `BEI/GroebnerBasis.lean` — the sorry locations (~2197, ~2200)
- `BEI/HerzogLemmas.lean` — `fij_coprime_swap`, `isRemainder_add`, `degree_bounds_of_ne`, `isRemainder_fij_via_groebnerElement`
- `BEI/ClosedGraphs.lean` — `isRemainder_sub_mul`, `coprime_degrees_ne`, `degree_bounds_of_sub`, `isRemainder_single_mul`
- `BEI/AdmissiblePaths.lean` — `groebnerElement_mem`, `generator_in_groebnerBasisSet`

## Key Available Infrastructure

| Lemma | File | What it does |
|-------|------|-------------|
| `isRemainder_single_mul` | ClosedGraphs | q * f has IsRemainder 0 when f ∈ G |
| `isRemainder_sub_mul` | ClosedGraphs | q₁*f₁ - q₂*f₂ has IsRemainder 0 with degree bounds |
| `isRemainder_monomial_mul'` | GroebnerBasis | monomial * f preserves IsRemainder 0 |
| `isRemainder_neg'` | GroebnerBasis | -f preserves IsRemainder 0 |
| `isRemainder_add` | HerzogLemmas | f₁ + f₂ has IsRemainder 0 with degree bounds |
| `isRemainder_fij_of_covered_walk` | GroebnerBasis | monomial * fij has IsRemainder 0 via walk |
| `isRemainder_fij_of_covered_walk_y` | GroebnerBasis | y-telescope variant |
| `walk_from_shared_first` | GroebnerBasis | construct walk from shared-endpoint paths |
| `coprime_degrees_ne` | ClosedGraphs | coprime fij terms have different degrees |
| `degree_bounds_of_sub` | ClosedGraphs | degree bounds when toSyn-degrees differ |
| `degree_bounds_of_ne` | HerzogLemmas | degree bounds for addition |
| `sPolyD_ge_of_zero` | GroebnerBasis | D ≥ dπ and D ≥ dσ when degree terms vanish |
| `pathMonomial_exponent_inl_one/_inr_one` | GroebnerBasis | pathMonomial exponent = 1 at internal vertices |
| `pathMonomial_is_monomial` | GroebnerBasis | pathMonomial = monomial d 1 |
| `fij_coprime_swap` | HerzogLemmas | the coprime swap identity |

## Technical Notes

- `unfold BinomialEdgeVars at ... ⊢` is essential for monomial arithmetic (Finsupp type class synthesis).
- `congr` + `monomial_mul` + `one_mul` for combining monomials.
- `set_option maxHeartbeats 800000` is set for `theorem_2_1`.
- The `by_cases hshared` split is on `∃ v, v ∈ π ∧ v ∈ σ` which is `Decidable` since V is Fintype and List membership is decidable.

## Recommended Order

1. **Sorry 2 (different components)** — simpler, ~50-80 lines, pure Finsupp arithmetic
2. **Sorry 1 (same component)** — harder, ~80-120 lines, needs walk construction through shared vertex

## What NOT To Do

- Don't try `isRemainder_fij_via_groebnerElement` for the coprime case without the swap — the divisibility D(Sum.inl k) ≥ dπ(Sum.inl k) fails when k ∈ internalVertices π.
- Don't try `isRemainder_sub_mul` with the groebnerElements directly on the S-polynomial form (degree bounds fail because leading terms cancel at degree = lcm).
- Don't try to prove a general `isRemainder_arbitrary_mul_fij` (can't divide out pathMonomial from IsRemainder).

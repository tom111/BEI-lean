# Plan: Overcoming the ℓ ∉ p Obstacle in Route B

## The obstacle, restated

For Route B's induction step on `dim A_{𝒜₊}` with NZD `ℓ ∈ 𝒜₊`:

- **`ℓ ∈ p` case**: proved (`isCohenMacaulayLocalRing_of_quotient_cm_of_mem`).
- **`ℓ ∉ p` case**: blocked. The naive approach "`A[1/ℓ]_{𝒜₊}` inherits
  CM" fails because `𝒜₊ · A[1/ℓ] = A[1/ℓ]` is improper: `ℓ ∈ 𝒜₊` is a unit
  in `A[1/ℓ]`. The ℕ-graded structure breaks under localization at a
  positive-degree element (the induced grading on `A[1/ℓ]` is ℤ-graded and
  not connected).

## Diagnosis

The obstacle is a structural one: **Route B's induction variable
`dim A_{𝒜₊}` does not descend naturally under localization at `ℓ`**,
whereas it does descend under quotient by `ℓ`. This asymmetry is the
root cause.

## Key insight: split Case C by `p ⊆ 𝒜₊` vs `p ⊄ 𝒜₊`

Case B (homogeneous `p`) in `GradedCM.lean:109` was proved using that
`p ≤ 𝒜₊`, derived from homogeneity. **Homogeneity is not actually
needed — only `p ≤ 𝒜₊` is.** The proof uses `p` disjoint from
`𝒜₊.primeCompl` to extract a localization tower.

**Refactored Case B** would cover all primes `p ⊆ 𝒜₊`, homogeneous or
not. After this refactor, **the genuinely hard Case C residual is only
primes `p ⊄ 𝒜₊`**.

## The residual: primes `p ⊄ 𝒜₊`

For `p` prime of `A` with `p ⊄ 𝒜₊`: `p` contains an element `c` whose
degree-0 component `k := proj_0(c) ∈ 𝒜 0 = K` is nonzero. `k` is a unit,
but `k ∉ p` (else `p = ⊤`). So the map `A → A/p` is injective on
`𝒜 0 = K`, meaning the residue field `κ(p) = Frac(A/p)` is a field
extension of `K` that may transcend the "graded" structure.

Examples: `A = K[x]`, `p = (x - 1)`. Then `p ⊄ (x) = 𝒜₊`, and
`κ(p) ≅ K`.

## The proposed recovery: use that `Ass(A)` is homogeneous

**Classical fact** (BH 1.5.6 / Eisenbud Cor 3.5, **not in Mathlib**):
Associated primes of a graded module over a graded Noetherian ring are
homogeneous.

**Consequence**: For `A` connected ℕ-graded Noetherian, every
homogeneous proper ideal is `⊆ 𝒜₊`
(`homogeneous_le_irrelevant_of_ne_top`). Combining:

> `Ass(A) ⊆ {homogeneous primes} ⊆ {primes ⊆ 𝒜₊}`.

Under this: **every associated prime of `A` lives inside `𝒜₊`**.

**Upshot for induction**: For a prime `p` of positive height, `p` is
NOT contained in any associated prime. Hence `p` contains a NZD of `A`.

This NZD needn't be homogeneous or lie in `𝒜₊`. We now have:

- **Alternative `ℓ ∈ p` with arbitrary NZD**: For prime `p` of positive
  height, pick any NZD `ℓ' ∈ p` (not necessarily homogeneous, not
  necessarily in `𝒜₊`). Apply the **`ℓ ∈ p` case** to this new NZD.

- But then the quotient `A ⧸ ⟨ℓ'⟩` might not inherit a graded structure
  (since `ℓ'` is not homogeneous), and the induction invariant on
  `dim A_{𝒜₊}` breaks.

## Refined induction scheme

Instead of inducting on `dim A_{𝒜₊}`, **induct on `ringKrullDim A_p`**
(= height of `p`).

**Invariant**: For every prime `p` of `A`, `A_p` is CM.

**Base**: `ringKrullDim A_p = 0` ⟹ `A_p` is Artinian local ⟹ CM.

**Step**: `ringKrullDim A_p = n ≥ 1`. Apply the refactored Case B to
handle `p ⊆ 𝒜₊`. For `p ⊄ 𝒜₊`:

- Using Ass-is-homogeneous: every associated prime of `A` is ⊆ `𝒜₊`.
- `p ⊄ 𝒜₊` and all `Ass(A) ⊆ 𝒜₊` ⟹ `p ⊄ any prime in Ass(A)`.
- Prime avoidance: `p ⊄ ⋃ Ass(A)` ⟹ ∃ `ℓ' ∈ p` with `ℓ' ∉ ⋃ Ass(A)`,
  i.e., `ℓ'` is a NZD on `A`.
- Apply the **`ℓ ∈ p` case**: CM of `(A ⧸ ⟨ℓ'⟩)_{p/⟨ℓ'⟩}` ⟹ CM of `A_p`.
- Recurse: `(A ⧸ ⟨ℓ'⟩)_{p/⟨ℓ'⟩}` has smaller `ringKrullDim` (via the
  dim formula `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`), so IH
  applies to its CM.

**Wait** — the issue: the IH requires `(A ⧸ ⟨ℓ'⟩)` to satisfy the same
hypotheses as `A`. If `ℓ'` is not homogeneous, `A ⧸ ⟨ℓ'⟩` is NOT
naturally graded, and we lose the hypothesis "`A'_{𝒜'₊}` is CM".

**Fix**: strengthen the induction invariant to avoid needing a graded
structure on the quotient. The invariant should be something like:

> For any Noetherian K-algebra `B` (not necessarily graded) with
> "CM at some maximal ideal `𝔪`", and `B` having the property that
> every associated prime of `B` is `⊆ 𝔪`, for every prime `p` of `B`
> with `ringKrullDim B_p ≤ n`, `B_p` is CM.

This invariant survives quotient by any NZD `ℓ' ∈ p` (not just
homogeneous), because:

- `B / ⟨ℓ'⟩` is still Noetherian K-algebra.
- Image of `𝔪` is a max ideal of `B / ⟨ℓ'⟩`.
- CM of `(B / ⟨ℓ'⟩)_{image of 𝔪}` follows from CM of `B_𝔪` + NZD
  `ℓ'` in maximal ideal.

But we still need: **every associated prime of `B / ⟨ℓ'⟩` is ⊆ image of 𝔪**.
This requires "`Ass(A/ℓ') ⊆ Ass(A) ∪ Ass(A) + stuff`", which is not
straightforward to maintain.

## Alternative: Route A refined (via *-depth)

Instead of inducting on dim, use the classical Bruns–Herzog 2.1.27
proof directly:

- Define **`*-depth`**: depth along graded (homogeneous) regular
  sequences only.
- Prove **BH 1.5.8**: `*-depth(p, A) = depth(A_p) - dim(A_p / p* · A_p)`.
- Combined with graded CM hypothesis: depth formulas collapse to give
  `depth(A_p) = dim(A_p)` for non-homogeneous `p`.

Estimated LOC: ~600-800 for the full *-depth machinery.

## Recommended path

### Option 1 (smaller first, then bigger if needed):

1. **Prove Phase 1 — `Ass(A)` is homogeneous for graded Noetherian `A`** (~80-150 LOC).
   This is a classical, upstreamable lemma with well-known proof
   (induction on annihilator colon ideals + graded decomposition).

2. **Prove the refactored Case B covering all `p ⊆ 𝒜₊`** (~30 LOC).
   Drop the `p.IsHomogeneous` hypothesis from `isCohenMacaulayLocalRing_atPrime_of_isHomogeneous`.

3. **For `p ⊄ 𝒜₊`**: by Phase 1 + Case B strengthening,
   `p` is not contained in any associated prime, so `p` contains a
   NZD of `A`. The image of this NZD in `A_p` is in `maxId A_p` and
   regular. Now try to recurse.

   **The recursion is the hard part**. Need an invariant that
   survives quotient by a non-homogeneous NZD. Options:

   - **Option 1a**: abandon graded induction; state the theorem in
     ungraded form with "`A` Noetherian K-algebra + all associated
     primes `⊆` a fixed maximal ideal `𝔪` + `A_𝔪` CM ⟹ `A_p` CM for
     all `p`". Prove this by height induction on `p`.
   - **Option 1b**: stay in graded induction by requiring `ℓ'` to be
     homogeneous, but then we need `p` to contain a homogeneous NZD.
     For `p ⊄ 𝒜₊`, `p` contains a NZD but not a homogeneous one
     (homogeneous elements are either in `𝒜₊` or in `K \ {0}` which
     are units).

   **Option 1a is cleaner** and is the likely path forward.

### Option 2 (heavier, more classical):

Pursue Route A (BH 1.5.8 / *-depth) for a complete, modular
treatment. Estimated 600-800 LOC. More work, more reusable for other
graded-CM applications.

## Decision point

Before committing either way, verify one critical prerequisite:

**Verification task**: Prove "`Ass(A)` is homogeneous for graded
Noetherian `A`" as a standalone lemma (Phase 1, ~80-150 LOC). This is
a useful lemma regardless of which Route we pursue.

- If Phase 1 compiles quickly (one session): commit to **Option 1**
  and attack the Option 1a refactor next.
- If Phase 1 is harder than expected: re-evaluate, possibly pivot to
  **Option 2 (Route A)**.

## Pragmatic fallback

If both routes prove too heavy, consider:

- **Narrower BEI-specific approach**: prove CM of `S[t] / tildeJ`
  directly using properties of the Gröbner deformation, without going
  through the full `GradedCM` LTG theorem. The consumer
  `tildeJ_quotient_isCohenMacaulay` may admit a direct proof via
  Stanley-Reisner / initial ideal / flatness arguments.
- Estimated: specialized to BEI, possibly ~200-400 LOC, but not
  upstreamable.

## Summary

| Route | LOC | Upstreamable | Risk |
|-------|-----|--------------|------|
| Option 1 (Ass homog + height induction, ungraded) | ~300-500 | Yes | Medium |
| Option 2 (Route A / BH 1.5.8 via *-depth) | ~600-900 | Yes | Low |
| BEI-specific bypass | ~200-400 | No | Low |

**Recommendation**: Start with **Phase 1 of Option 1** (`Ass(A)`
homogeneous for graded Noetherian) in the next session. This yields a
reusable lemma regardless of which larger route is pursued. After
Phase 1, reassess based on actual LOC spent.

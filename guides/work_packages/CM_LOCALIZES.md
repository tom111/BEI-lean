# Guide: CM Localizes — current packet for the HH global CM step

## Context

`isCohenMacaulayLocalRing_at_augIdeal` proves that the localization of
`S ⧸ bipartiteEdgeMonomialIdeal G` at the augmentation ideal (kernel of
`constantCoeff`) is `IsCohenMacaulayLocalRing` under HH conditions.

To close the HH-side CM theorem, we need `IsCohenMacaulayRing` (CM at
**every** prime localization), not just at the augmentation ideal.


## Why the augmentation ideal does not suffice

The augmentation ideal `m = ker(constantCoeff)` is maximal but is **not**
the unique maximal ideal of `S/I`.  Other maximal ideals of `K[x₁,...,xₙ]`
containing `I` exist (e.g., `(x₁-1, x₂, ..., xₙ)` whenever the zero
locus of `I` includes a point with `x₁ = 1`).  So primes of `S/I` not
contained in `m` exist, and we cannot reach them by localizing `(S/I)_m`.

For primes `p ⊆ m`: `(S/I)_p ≅ ((S/I)_m)_{p'}` where `p' = p(S/I)_m`.
So CM at `m` gives CM at `p` **if** we know the following theorem.


## Current recommended theorem packet

The current best-identified next theorem is:

**Theorem (CM localizes):**
If `(R, m)` is a Noetherian CM local ring and `p` is a prime of `R`,
then `R_p` is a CM local ring.

In our definition:
```
theorem isCohenMacaulayLocalRing_of_localization
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsCohenMacaulayLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    IsCohenMacaulayLocalRing (Localization.AtPrime p)
```

This is Bruns–Herzog Theorem 2.1.3(b→a), a standard result in commutative
algebra.  It is **not** currently available in Lean/Mathlib.

This guide treats it as the current recommended blocker packet for finishing the
HH-side global CM step.  If a smaller honest route is later found, that should
replace this packet rather than being forced into its framing.


## What is available

The repo and Mathlib already provide:

| Result | Location |
|--------|----------|
| Easy depth inequality `depth(R/xR) + 1 ≤ depth(R)` | `ringDepth_quotSMulTop_succ_le` |
| Dim formula `dim(R/xR) + 1 = dim(R)` for regular `x` | `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim` |
| Depth ≤ dim | `ringDepth_le_ringKrullDim` |
| Converse CM transfer (CM `R/(x)` + `x` regular → CM `R`) | `isCohenMacaulayLocalRing_of_regular_quotient` |
| CM from full-length weakly regular sequence | `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim` |
| Regular sequence permutability (local rings) | `IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal` |
| Regular sequence localization at prime | `IsWeaklyRegular.isRegular_of_isLocalization_of_mem` |
| `dim(R_p) = height(p)` | `IsLocalization.AtPrime.ringKrullDim_eq_height` |
| `height(p) ≤ dim(R)` | `Ideal.primeHeight_le_ringKrullDim` |
| Localization transitivity | `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` |
| 0-dimensional ⇒ CM | `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero` |


## Why this is the current blocker packet

### Approach A: Forward CM transfer

If we could prove **forward CM transfer** (CM `R` + `x` regular → CM `R/(x)`),
then "CM localizes" follows by induction on `dim(R) - height(p)`:

1. Pick `x ∈ m \ p` that is `R`-regular (exists by prime avoidance + unmixedness).
2. `R/(x)` is CM of dim `d-1` by forward CM transfer.
3. `p/(x)` has height `h` in `R/(x)`.
4. By induction, `(R/(x))_{p/(x)}` is CM.
5. Since `x ∉ p`, `x` is a unit in `R_p`, so `R_p ≅ (R/(x))_{p/(x)}`. ✗

Step 5 is wrong: `x ∉ p` does NOT mean `R_p ≅ (R/(x))_{p/(x)}` in general.
The correct inductive argument is more subtle (see Bruns–Herzog).

**Blockers for forward CM transfer:**

The forward CM transfer requires showing `depth(R/(x)) ≥ dim(R/(x))`.
We have `depth(R/(x)) ≤ dim(R/(x))` (always).

To get `≥`: we need either:
- The hard depth inequality `depth(R) ≤ depth(R/(x)) + 1` (Rees theorem), OR
- A proof that every regular element extends to a maximal regular sequence.

Both of these require the **Rees theorem**: all maximal regular sequences in
`m` have the same length.  The standard proof of Rees uses Ext functors or
Koszul homology, neither of which are in Mathlib v4.28.0.

### Approach B: Direct CM at every prime via the specific regular sequence

Our regular sequence `[x₀+y₀, …, x_{n-2}+y_{n-2}, x_{n-1}, y_{n-1}]`
lives at the augmentation ideal.  For another prime `p`, only the elements
IN `p` contribute to depth at `p`.

Problem: The diagonal sums `xᵢ + yᵢ` are NOT in most monomial primes
(a minimal vertex cover picks one of `{xᵢ, yᵢ}`, so `xᵢ + yᵢ` is not
in the corresponding variable-generated prime).  So the number of sequence
elements in a monomial prime is typically ≤ 2, while the height can be
`n - 1 ≫ 2`.  Hence our specific sequence cannot certify CM at all primes.

### Approach C: Polynomial extension preserves CM

If `R` is CM, then `R[x]` is CM (Bruns–Herzog 2.1.10).  This would let us
work in the smaller ring `K[x₀,...,x_{n-2}, y₀,...,y_{n-2}]` and extend.
But the proof of this result also requires "CM localizes" (for primes of
`R[x]` not of the form `pR[x]`), so this doesn't bypass the blocker.


## Recommended approach

### Shortest path: Prove the forward CM transfer directly for CM rings

Theorem: If `(R, m)` is CM Noetherian local and `x ∈ m` is `R`-regular,
then `R/(x)` is CM.

Required new infrastructure (minimal list):

1. **Associated primes have height 0 in a CM ring** (unmixedness).
   This can be proved by induction on `dim(R)`.  Base: `dim = 0` is trivial.
   Inductive step: choose a regular `x ∈ m`, quotient by it (circular?).

   Alternative: prove directly that if `depth = dim` and `p ∈ Ass(R)`, then
   `p` is a minimal prime.  Use: `p ∈ Ass(R)` means `m ∉ Ass(R)` (since
   depth > 0), so `p ≠ m`, and by Krull's PIT applied to a regular element,
   `height(p) = 0`.

2. **Regular element extension**: In a CM local ring, any regular element
   `x ∈ m` can be part of a regular sequence of length `dim(R)`.

   Once we know associated primes have height 0 and `x` is regular (hence
   not in any associated prime), quotient `R/(x)` has `dim = d - 1` and
   `depth ≥ d - 1` (from the tail of the extended sequence).  This gives
   CM of `R/(x)`.

3. **CM localizes** (from forward CM transfer by induction, choosing regular
   elements outside the target prime).

### Estimated scope

- Step 1 (unmixedness): ~50 lines.  Needs `Ideal.IsPrime` membership of
  associated primes, Krull's PIT, and depth-0 characterization.
- Step 2 (extension): ~30 lines.  Needs prime avoidance for associated primes.
- Step 3 (localizes): ~50 lines.  Needs localization transitivity and careful
  dimension/depth bookkeeping.

Total: ~130 lines of new infrastructure in `toMathlib/CohenMacaulay/`.

### Alternative: axiomatize and move forward

If the full CM-localizes proof is too costly, consider:

```lean
axiom isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_maximal
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {m : Ideal R} [m.IsMaximal]
    (hCM : IsCohenMacaulayLocalRing (Localization.AtPrime m))
    (hall : ∀ (p : Ideal R) [p.IsPrime], p ≤ m) :
    IsCohenMacaulayRing R
```

This isolates the gap explicitly and lets the rest of the proof proceed.


## Not needed for this step

- Ext/Koszul infrastructure (Rees theorem can be avoided for the forward
  CM transfer if we take the direct unmixedness route)
- Grading theory (graded local-to-global is a special case of CM-localizes)
- Reisner's theorem / simplicial complex theory
- The Gröbner CM transfer (that is a separate packet)

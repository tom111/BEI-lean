# Guide: HH Global CM from the Augmentation Ideal

## Status: 1 sorry — only the `p ⊄ m⁺` case remains

The theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` is
stated in `BEI/Equidim.lean` with a two-case split. The `p ⊆ m⁺` case is
**fully proved**; the `p ⊄ m⁺` case has one remaining sorry.


## What is proved

### In `BEI/Equidim.lean` — structural lemmas (all proved):

1. **`augIdeal_le_of_forall_mkI_X_mem`**: If all variable images `mk(X v)` lie in
   a prime `p`, then `augIdeal ≤ p`. Uses `MvPolynomial.mem_ideal_span_X_image`.

2. **`exists_var_not_mem_of_not_le_augIdeal`**: If `p ⊄ augIdeal`, then some
   variable image `mk(X v) ∉ p`. By contrapositive of (1) + maximality of
   `augIdeal`.

3. **`isUnit_algebraMap_mkI_X`**: A variable image not in `p` becomes a unit in
   `Localization.AtPrime p`. By `IsLocalization.map_units`.

4. **`algebraMap_mkI_X_eq_zero_of_edge`**: If `X v * X w ∈ I` (an edge of the HH
   bipartite graph) and `X v$ is a unit in `R_p`, then `X w` maps to zero.
   By `IsUnit.mul_right_eq_zero`.

5. **`algebraMap_mkI_y_eq_zero_of_x_not_mem`**: Under HH conditions, if `x_i ∉ p`
   then `y_i = 0` in `R_p`. Uses the HH diagonal edge `x_i · y_i ∈ I`.

6. **`algebraMap_mkI_x_eq_zero_of_y_not_mem`**: Symmetric version.

### In `BEI/Equidim.lean` — already proved:
- `isCohenMacaulayLocalRing_at_augIdeal`: CM at the augmentation ideal.

### In `toMathlib/CohenMacaulay/Localization.lean`:
- `isCohenMacaulayLocalRing_localization_atPrime`: CM localizes (complete).
- `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`: global CM from local CM (complete).


## The exact remaining blockers

### ~~Blocker A: `p ≤ augIdeal`~~ — **CLOSED**

Fully proved via:
1. `isWeaklyRegular_map_ringEquiv`: transfers weak regularity through `RingEquiv`
   by chaining `LinearEquiv.isWeaklyRegular_congr` (module transfer) with
   `isWeaklyRegular_map_algebraMap_iff` (scalar tower transfer).
2. `isCohenMacaulayLocalRing_of_ringEquiv`: transfers CM local ring through
   `RingEquiv`, using (1) for the depth direction and
   `ringKrullDim_eq_of_ringEquiv` for the dimension direction.
3. The main proof uses `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`
   to get `R_p ≃ (R_m)_{p'}`, then transfers CM via (2).

### Blocker B: `p ⊄ augIdeal` — CM of the localized HH quotient

**Mathematical gap: now isolated as a dehomogenization / Laurent-extension
packet.**

**Important negative result**: The approach via minimal primes below `p` does
NOT work. If `q ⊆ p` with `q` a minimal prime, then `q ⊆ augIdeal` (minimal
primes of a monomial ideal are variable-generated, hence below augIdeal), and
`R_q` is CM. However, the localization direction is WRONG: `q ⊆ p` gives
`R_q` as a further localization of `R_p` (not the other way), so we cannot
derive `R_p` CM from `R_q` CM by the "CM localizes" theorem. The correct
direction for localization transitivity is `p ⊆ q`, not `q ⊆ p`.

**The correct standard argument** (Bruns–Herzog 2.1.3, Goto–Watanabe):

For a standard graded K-algebra `R = K ⊕ R₁ ⊕ R₂ ⊕ ...` with `R₀ = K`:
1. Since `p ⊄ augIdeal = R₊`, some degree-1 element `r ∈ R₊ \ p` is a unit
   in `R_p`.
2. **Dehomogenize**: `R[r⁻¹] ≅ R[r⁻¹]₀[r, r⁻¹]` (Laurent polynomial over
   the degree-0 part). The degree-0 ring `R[r⁻¹]₀` is a polynomial ring
   quotient.
3. `R_{augIdeal} ≅ (R[r⁻¹]₀)_{m₀}` for the augmentation ideal `m₀` of the
   degree-0 part. Since `R_{augIdeal}` is CM by hypothesis, so is
   `(R[r⁻¹]₀)_{m₀}`.
4. For the prime `p₀` of `R[r⁻¹]₀` corresponding to `p`, we have `p₀ ⊆ m₀`.
   By `p ≤ augIdeal` case of `R[r⁻¹]₀`, `(R[r⁻¹]₀)_{p₀}` is CM.
5. `R_p ≅ (R[r⁻¹]₀)_{p₀}[r, r⁻¹]`. The Laurent extension preserves CM.

**What's needed to formalize this**:
- Graded ring structure for `MvPolynomial` quotients
- Dehomogenization isomorphism `R[r⁻¹] ≅ R[r⁻¹]₀[r, r⁻¹]`
- CM preservation under Laurent polynomial extension
- The identification `R_{augIdeal} ≅ (R[r⁻¹]₀)_{m₀}`

This is general commutative-algebra infrastructure, not specific to the HH case.
The variable-inversion structural lemmas (exists_var_not_mem, isUnit_algebraMap_mkI_X,
algebraMap_mkI_X_eq_zero_of_edge) capture the first step but the full
dehomogenization isomorphism is not yet formalized in this repo.

The active supporting packet for this branch is now:

- [DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md](DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md)


## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localization backport.
- Do not switch to the Gröbner CM transfer yet (that is a separate downstream gap).
- Do not reopen the already-closed `p ≤ augIdeal` branch.
- Do not restart the failed minimal-prime route.

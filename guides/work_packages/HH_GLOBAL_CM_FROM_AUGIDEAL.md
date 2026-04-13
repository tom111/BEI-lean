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

**Mathematical gap: now isolated as a graded-induction packet.**

**Important negative result**: The approach via minimal primes below `p` does
NOT work. If `q ⊆ p` with `q` a minimal prime, then `q ⊆ augIdeal` (minimal
primes of a monomial ideal are variable-generated, hence below augIdeal), and
`R_q` is CM. However, the localization direction is WRONG: `q ⊆ p` gives
`R_q` as a further localization of `R_p` (not the other way), so we cannot
derive `R_p` CM from `R_q` CM by the "CM localizes" theorem. The correct
direction for localization transitivity is `p ⊆ q`, not `q ⊆ p`.

**Current active route**:

Use graded induction on `dim(R_{augIdeal})`, with the already-proved forward
and converse CM transfer theorems.

For the remaining hard case `p ⊄ augIdeal` with positive height:

1. find a homogeneous non-zero-divisor `r ∈ p`;
2. use forward CM transfer to show `(R/(r))_{augIdeal/(r)}` is CM;
3. apply the induction hypothesis to `R/(r)`;
4. localize at `p/(r)` and use converse CM transfer to recover CM of `R_p`.

The only genuinely new theorem family now identified is:

- a graded prime-avoidance / homogeneous regular-element lemma for the HH quotient.

The active supporting packet for this branch is now:

- [GRADED_CM_INDUCTION.md](GRADED_CM_INDUCTION.md)

The earlier dehomogenization route is kept only as a superseded reference:

- [DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md](DEHOMOGENIZATION_CM_LOCAL_TO_GLOBAL.md)


## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localization backport.
- Do not switch to the Gröbner CM transfer yet (that is a separate downstream gap).
- Do not reopen the already-closed `p ≤ augIdeal` branch.
- Do not restart the failed minimal-prime route.
- Do not restart the superseded dehomogenization route unless the graded
  induction packet fails sharply.

# Guide: HH Global CM from the Augmentation Ideal

## Status: 1 sorry — the final polynomial-ring base case

The theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` is
stated in `BEI/Equidim.lean` with a two-case split. The `p ⊆ m⁺` case is
**fully proved**. The `p ⊄ m⁺` case has one remaining sorry, now isolated to
the base case where the localized HH quotient collapses to a localization of a
polynomial ring over a field.


## What is proved

### Graded contraction section (all proved):

1. **`homogeneousComponent_mul_eq_zero_of_low_degrees`**: Degree-counting core.
2. **`homogeneousComponent_sum_low_eq`**: Component recovery for sums.
3. **`mem_of_mul_mem_of_isUnit_constantCoeff`**: **Graded contraction theorem.**
4. **`bipartiteEdgeMonomialIdeal_isMonomial`**: HH ideal is monomial.
5. **`isMonomial_homogeneousComponent_mem`**: Monomial ideals are homogeneous.

### Structural lemmas (all proved):

6. **`exists_var_not_mem_of_not_le_augIdeal`**: Variable outside `p`.
7. **`isUnit_algebraMap_mkI_X`**: Variable unit in `R_p`.
8. **`algebraMap_mkI_X_eq_zero_of_edge`**: Edge partner killed.
9. **`algebraMap_mkI_y_eq_zero_of_x_not_mem`** / `..._x_eq_zero_of_y_not_mem`.

### Regular sequence infrastructure (all proved):

10. **`fullRegSeq_isWeaklyRegular_localization`**: Full reg seq weakly regular
    on `R_p` for ALL primes (flat base change).
11. **`minimalPrime_le_augIdeal`**: Minimal primes ⊆ augIdeal.
12. **`isCohenMacaulayLocalRing_at_augIdeal`**: CM at augIdeal.


## The exact remaining blocker

### ~~Blocker A: `p ≤ augIdeal`~~ — **CLOSED**
### ~~Blocker B1: Graded contraction lemma~~ — **CLOSED**

### Blocker B2: polynomial-ring base case

The main inductive step is now understood. The only remaining gap is the
base case `ℓ = 0`.

In that base case:
1. all parameter elements are units in `R_p`;
2. by the HH local-ring dichotomy, every variable becomes `0` or a unit;
3. all monomial relations vanish;
4. `R_p` identifies with a localization of a polynomial ring over the field
   `K`;
5. need: such a localization is Cohen–Macaulay.

### Key resources for this base case

- structural localization lemmas already proved in `BEI/Equidim.lean`;
- the graded contraction theorem;
- `isCohenMacaulayLocalRing_localization_atPrime`;
- a still-missing theorem showing polynomial rings over fields are CM.

The current smallest support packet for this step is:

- [POLYNOMIAL_RING_CM_BASE_CASE.md](POLYNOMIAL_RING_CM_BASE_CASE.md)

Current execution order:

1. finish the final remaining sorry in
   `toMathlib/CohenMacaulay/Polynomial.lean`;
2. then build the HH base-case ring isomorphism
   `R_p ≅ (MvPolynomial σ' K)_q`;
3. then close the last sorry in `BEI/Equidim.lean`.


## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localization backport.
- Do not switch to the Gröbner CM transfer yet.
- Do not reopen the `p ≤ augIdeal` branch.
- Do not restart the minimal-prime, graded-induction, dehomogenization, or
  broad parameter-prefix routes.
- Do not broaden into regular-local / embedding-dimension infrastructure unless
  the polynomial-CM route sharply fails.

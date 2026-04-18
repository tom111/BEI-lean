# Guide: Graded Contraction NZD for HH Global CM

## Status: **support packet completed**

The graded contraction lemma (`mem_of_mul_mem_of_isUnit_constantCoeff`) is proved
in `BEI/Equidim.lean`.

This file is now a completed support packet. The remaining sorry no longer
depends on the contraction theorem itself; it depends on the final
dimension-counting step for prefixes of the parameter sequence.

The active support packet is now:

- [CM_PARAMETER_PREFIX_UNMIXED.md](CM_PARAMETER_PREFIX_UNMIXED.md)


## What is proved

### Graded contraction section:

1. **`homogeneousComponent_mul_eq_zero_of_low_degrees`**
2. **`homogeneousComponent_sum_low_eq`**
3. **`mem_of_mul_mem_of_isUnit_constantCoeff`** (the main contraction theorem)
4. **`bipartiteEdgeMonomialIdeal_isMonomial`**
5. **`isMonomial_homogeneousComponent_mem`**


## Available proof infrastructure for the sorry

The following pieces are proved and available for the `p ⊄ augIdeal` branch:

- The full regular sequence is weakly regular on `R_p` for all `p`
  (`fullRegSeq_isWeaklyRegular_localization`).
- Regular sequences can be permuted in a local ring
  (`IsLocalRing.isRegular_of_perm` in Mathlib).
- The contraction lemma transfers regularity from `R_{m⁺}` to `R`: if a
  sequence is regular in `R_{m⁺}` and consists of homogeneous elements,
  it is weakly regular on `R`, because each successive quotient ideal
  `I + (a₁,…,aₖ)` is homogeneous and the contraction lemma applies.
- `IsWeaklyRegular.isRegular_of_isLocalization_of_mem` (Mathlib): a weakly
  regular sequence on `R` with elements in `p` localizes to a regular
  sequence in `R_p`.
- `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim`: a regular
  sequence in the maximal ideal of length = dim gives CM.
- `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular` (Mathlib):
  `dim(R/(a₁,…,a_ℓ)) + ℓ = dim(R)` for a regular sequence.


## What this packet unlocked

After permuting the full reg seq to put `p`-elements first and transferring
to a weakly regular sequence on `R`, then localizing at `p`:

- depth(`R_p`) ≥ ℓ (from the regular sequence of length ℓ in pR_p).
- dim(`R_p`) = ℓ + dim(`R_p / (a₁,…,a_ℓ)`).

The remaining gap is now:

- show `dim(R_p / (a₁,…,a_ℓ)) = 0`, equivalently `height(p) = ℓ`,
  after the contraction step has produced the correct regular-sequence setup.

The current preferred route is the narrower parameter-ideal/unmixedness
argument recorded in:

- [CM_PARAMETER_PREFIX_UNMIXED.md](CM_PARAMETER_PREFIX_UNMIXED.md)


## What NOT to do

- Do not reopen the `p ≤ augIdeal` branch.
- Do not restart dehomogenization or graded induction routes.
- Do not switch to the Gröbner CM transfer theorem.

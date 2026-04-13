---
title: toMathlib
---

# toMathlib: Supporting Infrastructure

This page lists the supporting material in `toMathlib/`: local backports,
general algebra lemmas, and project-specific results used by the main BEI files.

## Scope

The `toMathlib/` directory has three roles:

1. **local support for the equidimensional surrogate track**;
2. **real Cohen–Macaulay foundations**, partially adapted from Mathlib PR
   [`#26218`](https://github.com/leanprover-community/mathlib4/pull/26218);
3. **project-specific algebra and combinatorics** needed for the BEI proofs.

This page records what is formalized now.

## Equidimensional surrogate support

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/Equidim/Defs.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/Equidim/Defs.lean) | `IsEquidimRing` | formalized | Local working definition of equidimensionality used in the surrogate branch |

`toMathlib/Equidim/Defs.lean` provides the local equidimensional stand-in used
by the direct surrogate route. It is not the paper's full
Cohen–Macaulay definition.

## Real Cohen–Macaulay foundations

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/CohenMacaulay/Defs.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Defs.lean) | `ringDepth`, `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`, `weaklyRegular_length_le_ringKrullDim`, `ringDepth_le_ringKrullDim` | formalized | First real CM definition layer in the repo |
| [toMathlib/CohenMacaulay/Basic.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Basic.lean) | `quotSMulTop_nontrivial`, `quotSMulTopLocalRing`, `ringDepth_quotSMulTop_succ_le`, `isCohenMacaulayLocalRing_of_regular_quotient` | formalized | Quotient-local-ring setup, the easy depth inequality, and the converse regular-quotient CM transfer |
| [toMathlib/CohenMacaulay/Localization.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Localization.lean) | `isCohenMacaulayLocalRing_quotient`, `associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing`, `isCohenMacaulayLocalRing_localization_atPrime`, `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` | formalized | Ext/Rees machinery, forward CM transfer, unmixedness, and localization/globalization for CM local rings |

These files build the real Cohen–Macaulay layer used by the Proposition 1.6
work:

- `Defs.lean` gives a local working CM definition via regular-sequence depth;
- `Basic.lean` sets up the quotient-local-ring layer and the basic local criteria;
- `Localization.lean` now completes the local CM localization packet.

This still does **not** finish the paper's Proposition 1.6 route:
the remaining HH-side gap is now the graded local-to-global step from
augmentation-ideal CM to a genuine global CM theorem for the HH quotient, plus
the separate Gröbner CM transfer theorem.

## Monomial ideal infrastructure

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/MonomialIdeal.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/MonomialIdeal.lean) | `Ideal.not_mem_exists_monomial_notMem`, `Ideal.IsMonomial`, `MvPolynomial.isPrime_span_X_image_set`, `Ideal.exists_variable_mem_of_monomial_mem_prime`, `Ideal.IsMonomial.isPrime_iff_eq_span_X_image`, `Ideal.IsMonomial.isPrimary_iff` | formalized | Prime and primary theory for monomial ideals in `MvPolynomial` |

This file contains the main monomial-ideal tools used in the BEI proofs:

- support extraction for ideals in `MvPolynomial`;
- classification of prime monomial ideals as variable-generated ideals;
- characterization of primary monomial ideals.

## Squarefree monomial primes and vertex covers

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/SquarefreeMonomialPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/SquarefreeMonomialPrimes.lean) | `MvPolynomial.variablePairIdeal`, `MvPolynomial.IsVertexCover`, `MvPolynomial.IsMinimalVertexCover`, `MvPolynomial.variablePairIdeal_le_span_X_iff`, `MvPolynomial.minimalPrime_variablePairIdeal_iff`, `MvPolynomial.variablePairIdeal_isRadical` | formalized | Edge-ideal / vertex-cover / minimal-prime support layer |

This file packages the squarefree monomial ideal facts needed on the
Herzog–Hibi side of Proposition 1.6:

- variable-pair ideals for edge sets;
- minimal vertex covers;
- minimal prime classification;
- radicality of the variable-pair ideal.

## Variable ideal quotient and dimension formulas

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/HeightVariableIdeal.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/HeightVariableIdeal.lean) | `ker_killS_eq_span_X_image`, `killS_surjective`, `quotientSpanXEquiv`, `MvPolynomial.ringKrullDim_quotient_span_X_image`, `MvPolynomial.ringKrullDim_quotient_span_X_eq_of_card_eq` | formalized | Quotient equivalences and dimension formulas for variable-generated ideals |

These theorems are used in Proposition 1.6 to compare quotient dimensions after
reducing to variable-generated prime ideals.

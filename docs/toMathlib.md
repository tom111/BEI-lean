---
title: toMathlib
---

# toMathlib: Supporting Infrastructure

This page documents the supporting material in `toMathlib/`.

These files are not part of the paper statement list itself. They collect
background theorems, local backports, and project-specific support lemmas that
the main BEI development uses.

Some of these files are intended as possible future upstream contributions.
Others are explicitly local to this repository.

## Scope

The `toMathlib/` directory currently has three different roles:

1. **local support for the equidimensional surrogate track**;
2. **real Cohen–Macaulay foundations**, partially adapted from Mathlib PR
   [`#26218`](https://github.com/leanprover-community/mathlib4/pull/26218);
3. **project-specific algebra and combinatorics** needed for the BEI proofs.

This page records only what is actually formalized now. It does not claim that
all of these files are upstream-quality or that the full paper-level
Cohen–Macaulay theory is already available.

## Equidimensional surrogate support

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/Equidim/Defs.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/Equidim/Defs.lean) | `IsEquidimRing` | formalized | Local working definition of equidimensionality used in the surrogate branch |

### Provenance

`toMathlib/Equidim/Defs.lean` is adapted from Mathlib PR `#26218`, but it is
used here only as a local surrogate layer. It does **not** represent the full
depth-based Cohen–Macaulay definition from commutative algebra.

## Real Cohen–Macaulay foundations

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/CohenMacaulay/Defs.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Defs.lean) | `ringDepth`, `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`, `weaklyRegular_length_le_ringKrullDim`, `ringDepth_le_ringKrullDim` | formalized | First real CM definition layer in the repo |
| [toMathlib/CohenMacaulay/Basic.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Basic.lean) | `quotSMulTop_nontrivial`, `quotSMulTopLocalRing`, `ringDepth_quotSMulTop_succ_le`, `isCohenMacaulayLocalRing_of_regular_quotient` | formalized | Quotient-local-ring setup, the easy depth inequality, and the converse regular-quotient CM transfer |
| [toMathlib/CohenMacaulay/Localization.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/CohenMacaulay/Localization.lean) | `isCohenMacaulayLocalRing_quotient`, `associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing`, `isCohenMacaulayLocalRing_localization_atPrime`, `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` | formalized | Ext/Rees machinery, forward CM transfer, unmixedness, and localization/globalization for CM local rings |

### Notes

These files are part of the real Cohen–Macaulay track, but they do **not** yet
finish the paper's CM branch.

In particular:

- `Defs.lean` gives a local working CM definition via regular-sequence depth;
- `Basic.lean` sets up the quotient-local-ring layer and the basic local criteria;
- `Localization.lean` now completes the local CM localization packet.

This still does **not** mean the paper's full Proposition 1.6 CM route is done:
the remaining HH-side gap is now the graded local-to-global step from
augmentation-ideal CM to a genuine global CM theorem for the HH quotient, plus
the separate Gröbner CM transfer theorem.

### Provenance

Both `toMathlib/CohenMacaulay/Defs.lean` and
`toMathlib/CohenMacaulay/Basic.lean` are documented in the source files
themselves as adapted/backported from Mathlib PR `#26218`, with local changes
for compatibility with the pinned `v4.28.0` environment.

The adaptation is not claimed to be a verbatim port of the full PR dependency
cone.

## Monomial ideal infrastructure

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/MonomialIdeal.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/MonomialIdeal.lean) | `Ideal.not_mem_exists_monomial_notMem`, `Ideal.IsMonomial`, `MvPolynomial.isPrime_span_X_image_set`, `Ideal.exists_variable_mem_of_monomial_mem_prime`, `Ideal.IsMonomial.isPrime_iff_eq_span_X_image`, `Ideal.IsMonomial.isPrimary_iff` | formalized | Prime and primary theory for monomial ideals in `MvPolynomial` |

### Notes

This file contains a substantial project-local theorem layer:

- support extraction for ideals in `MvPolynomial`;
- classification of prime monomial ideals as variable-generated ideals;
- characterization of primary monomial ideals.

These are genuine supporting theorems used by the BEI formalization, not direct
rephrasings of statements from the paper.

## Squarefree monomial primes and vertex covers

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/SquarefreeMonomialPrimes.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/SquarefreeMonomialPrimes.lean) | `MvPolynomial.variablePairIdeal`, `MvPolynomial.IsVertexCover`, `MvPolynomial.IsMinimalVertexCover`, `MvPolynomial.variablePairIdeal_le_span_X_iff`, `MvPolynomial.minimalPrime_variablePairIdeal_iff`, `MvPolynomial.variablePairIdeal_isRadical` | formalized | Edge-ideal / vertex-cover / minimal-prime support layer |

### Notes

This file packages the squarefree monomial ideal facts needed for the
Herzog–Hibi side of Proposition 1.6:

- variable-pair ideals for edge sets;
- minimal vertex covers;
- minimal prime classification;
- radicality of the variable-pair ideal.

## Variable ideal quotient and dimension formulas

| File | Lean declarations | Status | Notes |
|---|---|---|---|
| [toMathlib/HeightVariableIdeal.lean](https://github.com/tom111/BEI-lean/blob/master/toMathlib/HeightVariableIdeal.lean) | `ker_killS_eq_span_X_image`, `killS_surjective`, `quotientSpanXEquiv`, `MvPolynomial.ringKrullDim_quotient_span_X_image`, `MvPolynomial.ringKrullDim_quotient_span_X_eq_of_card_eq` | formalized | Quotient equivalences and dimension formulas for variable-generated ideals |

### Notes

These theorems are used in the Proposition 1.6 support work to compare quotient
dimensions after reducing to variable-generated prime ideals.

## What this page does not claim

This support layer is substantial, but the following points remain important:

- the existence of `toMathlib/CohenMacaulay/` does **not** mean the full
  Cohen–Macaulay part of the paper is already formalized;
- the equidimensional surrogate in `toMathlib/Equidim/Defs.lean` is still only
  a surrogate;
- the real CM branch is still incomplete;
- some support files are local to this project rather than general Mathlib
  results already accepted upstream.

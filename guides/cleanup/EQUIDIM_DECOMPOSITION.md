# Guide: Decompose `BEI/Equidim.lean` by Mathematical Role

## Goal

Break [BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean) into a small set of
files whose boundaries match the actual mathematics:

- initial-ideal setup;
- HH regular-sequence work;
- HH-side Cohen-Macaulay theorems;
- localization / tensor transport;
- public equidimensional surrogate endpoints.


## Why this matters

`Equidim.lean` is now doing too many jobs at once.

It currently mixes:

- the equidimensional surrogate API;
- the initial-ideal / `y`-shift setup for Proposition 1.6;
- HH graph combinatorics;
- regular-sequence and non-zero-divisor lemmas;
- local and global CM theorems at the augmentation ideal;
- localization-away and tensor-product transport;
- examples and paper-facing wrapper theorems.

That makes the file hard to navigate and easy to destabilize.


## Splitting principle

Keep the paper-facing route readable.

Do not split by arbitrary line ranges. Split so that each file answers one
clear question.


## Recommended package structure

## 1. Initial ideal and shift package

Candidate contents:

- `initialIdeal_closed_eq`
- `yPredVar`
- `rename_yPredVar_generator`
- `rename_yPredVar_monomialInitialIdeal`
- `bipartiteEdgeMonomialIdeal`
- the HH combinatorial setup statements that belong directly to the
  paper's monomial-side reduction

Suggested file name:

- `BEI/InitialIdeal.lean`

This package should cover the algebraic setup from `J_G` to the bipartite
edge monomial ideal, without carrying the later CM machinery.


## 2. HH regularity package

Candidate contents:

- diagonal-sum ideals and regular-sequence lemmas
- `sum_XY_isSMulRegular_mod_diagonalSum`
- `X_inl_last_isSMulRegular_mod_diagonalSum`
- `X_inr_last_isSMulRegular_mod_diagonalSum_sup`
- `bipartiteEdgeMonomialIdeal_isWeaklyRegular`
- `bipartiteEdgeMonomialIdeal_isWeaklyRegular_full`

Suggested file name:

- `BEI/HHRegularity.lean`

This package is the heart of the HH proof engineering and should not be buried
among localization transport and examples.


## 3. HH Cohen-Macaulay package

Candidate contents:

- `isCohenMacaulayLocalRing_at_augIdeal`
- `isCohenMacaulayLocalRing_at_augIdealReduced`
- `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
- `isCohenMacaulayRing_at_augIdealReduced`
- the public monomial-side endpoint
  `monomialInitialIdeal_isCohenMacaulay`

Suggested file name:

- `BEI/HHCohenMacaulay.lean`

This file should read as the honest HH-side completion of Step 1 of
Proposition 1.6, not as a continuation of the surrogate branch.


## 4. Localization and tensor transport package

Candidate contents:

- `E_U`
- the `pick-U` support lemmas
- contraction / localization comparison lemmas
- tensor-localization bridge applications specific to the HH route

Suggested file name:

- `BEI/HHLocalisation.lean`

This is the most technical transport layer. Isolating it will make later CM
maintenance much safer.


## 5. Public surrogate wrapper

Keep [BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean) as either:

- a thin public wrapper re-exporting the decomposed files; or
- a short public theorem layer for the equidimensional surrogate branch.

Candidate public residents:

- `IsEquidim`
- `SatisfiesProp1_6Condition`
- `HerzogHibiConditions`
- `prop_1_6_herzogHibi`
- the complete-graph example

If examples remain, keep them clearly separated from the HH transport chain.


## Migration strategy

Recommended local sequence:

1. add section headers and module comments inside the current file;
2. move the initial-ideal block first;
3. move the HH regularity block second;
4. move the localization/tensor transport block third;
5. leave the public wrapper last.

Do not combine this with major theorem edits in the same round.


## Important cautions

- Do not blur the equidimensional surrogate branch with the real
  Cohen-Macaulay branch.
- Do not turn `Equidim.lean` into a catch-all import hub again after splitting.
- Do not split while simultaneously changing the mathematical statements of the
  public endpoints.


## Definition of done

This guide is complete when:

1. the initial-ideal setup, HH regularity, HH CM theorem, and localization
   transport each live in their own coherent file;
2. the public `Equidim` surface is short enough to read as a theorem layer;
3. future Prop 1.6 work no longer requires scrolling through unrelated
   surrogate material.

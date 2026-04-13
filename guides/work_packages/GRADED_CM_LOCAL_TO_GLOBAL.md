# Guide: Graded Local-to-Global CM for the HH Quotient

## Task

This file is now mainly the theorem-context memo for the remaining HH-side
global Cohen–Macaulay step.

The new CM backport packet in
[toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean)
is now complete:

- forward CM transfer is proved;
- unmixedness for CM local rings is proved;
- `CM localizes` is proved;
- the local-to-global wrapper for already-local rings is proved.

That means the old packet
[CM_LOCALIZES.md](/home/tom/BEI-lean/guides/work_packages/CM_LOCALIZES.md)
is no longer the active blocker.


## Why Proposition 1.6 is still open

In
[BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean),
the theorem
`isCohenMacaulayLocalRing_at_augIdeal`
proves that the localization of the HH quotient at the augmentation ideal is
Cohen–Macaulay.

But the HH endpoint we still need is a genuine global theorem of the form:

```text
IsCohenMacaulayRing (S ⧸ bipartiteEdgeMonomialIdeal G)
```

The new theorem `CM localizes` does **not** by itself bridge that gap, because:

- it lets us move from one CM local ring to smaller prime localizations inside it;
- but `S ⧸ I` is not known to be local;
- and CM at the augmentation ideal does not automatically imply CM at every prime.

So the remaining HH-side blocker is now:

**a graded / standard-graded local-to-global CM theorem, or another honest theorem
specialized to this quotient that serves the same role.**


## Current verified state

### In `BEI/Equidim.lean`

Proved:

- `prop_1_6_herzogHibi`
- `sum_XY_isSMulRegular_mod_diagonalSum`
- `bipartiteEdgeMonomialIdeal_isWeaklyRegular`
- `ringKrullDim_bipartiteEdgeMonomialIdeal`
- `X_inl_last_isSMulRegular_mod_diagonalSum`
- `X_inr_last_isSMulRegular_mod_diagonalSum_sup`
- `bipartiteEdgeMonomialIdeal_isWeaklyRegular_full`
- `isCohenMacaulayLocalRing_at_augIdeal`

So the HH quotient now has:

- the full regular-sequence package;
- the right dimension formula;
- and CM at the augmentation / irrelevant maximal ideal.

### In `toMathlib/CohenMacaulay/Localization.lean`

Proved:

- `isCohenMacaulayLocalRing_quotient`
- `associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing`
- `exists_smulRegular_mem_of_isCohenMacaulayLocalRing`
- `isCohenMacaulayLocalRing_localization_atPrime`
- `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`

This packet is done. The remaining HH problem is no longer “prove CM localizes”.


## Recommended next theorem

The most honest next target is a theorem of the form:

```text
If R is a standard graded finitely generated K-algebra and
R localized at the irrelevant maximal ideal is Cohen–Macaulay,
then R is Cohen–Macaulay.
```

For the current repo, an even narrower theorem is acceptable if it is sufficient
for the HH quotient and stays mathematically truthful.

Examples of acceptable target shapes:

1. a standard-graded local-to-global theorem specialized to quotients of
   `MvPolynomial` over a field;
2. a theorem directly for homogeneous ideals in a polynomial ring;
3. a theorem specialized even further to the HH quotient, if the specialization
   is mathematically clean and clearly documented.


## Active execution packet

The current smaller active work packet is now:

- [HH_GLOBAL_CM_FROM_AUGIDEAL.md](HH_GLOBAL_CM_FROM_AUGIDEAL.md)

That guide should be preferred for the next implementation round. This file is
kept as the broader mathematical context memo.


## What to avoid

- Do **not** present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do **not** reopen the finished CM-localization packet.
- Do **not** switch yet to the Gröbner CM transfer theorem; that remains a
  separate paper-critical gap after the HH global CM theorem lands.
- Do **not** blur a graded local-to-global theorem with the already-finished
  theorem `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`, which applies only
  when the ambient ring is already local.


## Definition of done

Best outcome:

- a truthful theorem proving global Cohen–Macaulayness of the HH quotient from
  the already-proved augmentation-ideal CM theorem;
- an HH-side theorem in `BEI/Equidim.lean` concluding
  `IsCohenMacaulayRing` for the bipartite edge-ideal quotient.

Minimum acceptable outcome:

- the exact smallest graded local-to-global theorem needed is isolated cleanly,
  with a new support packet if necessary.

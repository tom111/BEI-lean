# Guide: Backport the CM Localization Slice from mathlib PR #28599

## Status: COMPLETE

File:
- `toMathlib/CohenMacaulay/Localization.lean`


## What landed

- Ext vanishing infrastructure (generalized to arbitrary modules)
- Degenerate LES consequences (surjectivity of δ, vanishing transfers)
- Ext^0 ↔ regular element (for arbitrary modules)
- Rees theorem (both directions, module + ring versions)
- Hard depth inequality (`ringDepth R ≤ ringDepth(R/(x)) + 1`)
- **Forward CM transfer** (`isCohenMacaulayLocalRing_quotient`)
- **Unmixedness for CM local rings**
- **CM localizes**
- **Global CM wrapper for local rings**

The file is now sorry-free.


## Downstream impact

With `isCohenMacaulayLocalRing_localization_atPrime` proved:
- `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` is available;
- the old CM-localization blocker for the HH route is removed;
- the remaining HH-side gap is now the graded local-to-global step from
  augmentation-ideal CM to a genuine global HH CM theorem.

That downstream packet is now tracked separately in:

- [../GRADED_CM_LOCAL_TO_GLOBAL.md](../GRADED_CM_LOCAL_TO_GLOBAL.md)

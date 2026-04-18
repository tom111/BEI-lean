# Guide: Polynomial Ring CM Base Case for HH Global CM

## Status: COMPLETED — sorry-free

`toMathlib/CohenMacaulay/Polynomial.lean` has **0 sorries** and builds cleanly.
The main theorem `isCohenMacaulayRing_mvPolynomial_field` is fully proved and
verifies with only `propext`, `Classical.choice`, `Quot.sound`.

## What is provided

- `isCohenMacaulayRing_of_isField` — fields are CM rings.
- `height_eq_one_of_comap_C_eq_bot` — height-1 primes over ⊥ in domains.
- `quotSMulTopPolynomialLocalizationEquiv` — `A[X]_P/(X) ≃+* A_{P∩A}`.
- `exists_smulRegular_of_isCohenMacaulayRing` — NZD in prime of positive
  height.
- `isCohenMacaulayRing_quotient_of_smulRegular` — CM / NZD is CM.
- `cm_localize_polynomial_of_cm_aux` — induction on primeHeight.
- `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing_domain` — the
  polynomial extension theorem for CM domains.
- `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing` and
  `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing` — the
  general (non-domain) polynomial CM extension, backported from
  Mathlib PR #28599 (2026-04-18).
- **`isCohenMacaulayRing_mvPolynomial_field`** — MvPolynomial rings over
  fields are CM.
- Public ring-equiv CM transfer: `isCohenMacaulayLocalRing_of_ringEquiv'`,
  `isWeaklyRegular_map_ringEquiv`.

## Usage in the F2 route

This theorem feeds into the reduced-HH-at-augmentation CM chain as the
base case "polynomial rings over a field are CM". See
[HH_GLOBAL_CM_FROM_AUGIDEAL.md](HH_GLOBAL_CM_FROM_AUGIDEAL.md) for the
current state of the F2 plan; the polynomial CM result is a DONE input
to that larger plan.

## Known limitation (RESOLVED 2026-04-18)

Previously the domain-only version required `[IsDomain A]`. The PR #28599
backport lifts this restriction: `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing`
takes only `[IsNoetherianRing R] [IsCohenMacaulayRing R]`. Stanley-Reisner
CM quotients (not domains) are now covered.

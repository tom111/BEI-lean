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

## Known limitation

The theorem requires `A` to be a **domain** (`[IsDomain A]`). For the F2
route's L7 (tensor-CM base lemma), we need polynomial CM for non-domain
CM local rings — specifically for `A = A_H^red` localized at its
augmentation, which is CM local but not a domain (Stanley-Reisner rings
with multiple minimal primes).

Generalizing to non-domain A is a separate project (substantial rewrite
of the X ∉ Q branch) and is tracked under L7 in
`HH_GLOBAL_CM_FROM_AUGIDEAL.md`.

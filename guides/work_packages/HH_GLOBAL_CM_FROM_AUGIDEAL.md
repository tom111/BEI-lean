# Guide: HH Global CM from the Augmentation Ideal

## Status: 1 sorry — graded local-to-global

The theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` is
stated in `BEI/Equidim.lean` with one sorry. The sorry requires a graded
local-to-global CM theorem.


## What is proved

In `BEI/Equidim.lean`:
- `isCohenMacaulayLocalRing_at_augIdeal`: CM at the augmentation ideal.
- `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`: **stated with sorry**.

In `toMathlib/CohenMacaulay/Localization.lean`:
- `isCohenMacaulayLocalRing_localization_atPrime`: CM localizes (complete).
- `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`: global CM from local CM (complete).


## The exact remaining blocker

The sorry reduces to the following theorem:

> **Graded local-to-global**: For a standard graded Noetherian K-algebra R
> with R₀ = K (a field) and irrelevant ideal m⁺, if R_{m⁺} is CM, then R is CM.

This breaks into two cases:

### Case 1: primes p ⊆ m⁺

**Already solved by existing infrastructure.**

R_p ≅ (R_{m⁺})_{p'} via `localizationLocalizationAtPrimeIsoLocalization`.
R_{m⁺} is CM by hypothesis. By `isCohenMacaulayLocalRing_localization_atPrime`,
(R_{m⁺})_{p'} is CM. So R_p is CM.

### Case 2: primes p ⊄ m⁺

**Requires new infrastructure.**

If p ⊄ m⁺: some degree-1 element t is not in p. Then t is a unit in R_p.
The argument uses dehomogenization: R[t⁻¹] is a polynomial ring of lower
dimension (the "degree-0 part" of R[t⁻¹]) and R_p = (R[t⁻¹])_{pR[t⁻¹]}.
For standard graded K-algebras, R[t⁻¹] is CM iff R is CM (classical result).

This dehomogenization argument is not yet formalized.


## Recommended approach

The narrowest honest path:

1. Prove the graded local-to-global for MvPolynomial quotients over a field,
   specialized to the case where the ideal is homogeneous (or monomial).
2. The case p ⊆ m⁺ is immediate from existing infrastructure.
3. The case p ⊄ m⁺ needs either:
   (a) a dehomogenization argument showing R[t⁻¹] is CM when R_{m⁺} is, or
   (b) a direct argument for monomial ideal quotients that every prime outside
       m⁺ gives a CM localization (possibly by induction on number of variables).

Option (b) might be simpler for the specific BEI case: for a monomial ideal I,
R_p with some variable invertible simplifies to a quotient of fewer variables,
and induction on the number of variables may close it.


## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localization backport.
- Do not switch to the Gröbner CM transfer yet (that is a separate downstream gap).

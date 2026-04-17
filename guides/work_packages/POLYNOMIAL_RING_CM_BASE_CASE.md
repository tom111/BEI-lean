# Guide: Polynomial Ring CM Base Case for HH Global CM

## Status: 1 sorry remains, technical and isolated

The polynomial CM infrastructure is in `toMathlib/CohenMacaulay/Polynomial.lean`.
The file builds cleanly. The proof architecture is complete; one final dim-1
corner-case sorry remains.


## What is fully proved

- **All ring-equiv CM infrastructure** (public).
- **`isCohenMacaulayRing_of_isField`**: fields are CM rings.
- **`height_eq_one_of_comap_C_eq_bot`**: height-1 for primes over ⊥ in domains.
- **`quotSMulTopPolynomialLocalizationEquiv`**: `A[X]_P/(X) ≃+* A_{P∩A}`.
- **`exists_smulRegular_of_isCohenMacaulayRing`**: NZD in a prime of pos height
  (modulo sorry 1 below).
- **`isCohenMacaulayRing_quotient_of_smulRegular`**: quotient of CM ring by NZD
  is CM (modulo sorry 2 below).
- **`cm_localize_polynomial_of_cm_aux`**: full induction on primeHeight
  with positive-height case (modulo sorry 3) and height-zero case (modulo sorry 4).
- **`isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing_domain`**: X∈P case
  fully proved; X∉P case delegates to the auxiliary lemma.
- **`isCohenMacaulayRing_mvPolynomial_field`**: by induction + ring equiv.


## Remaining sorry

The only remaining sorry is the dim-1 corner case in the `X ∉ Q` branch.

Current form of the subcase:

- `Q.primeHeight = 1`;
- `q := Q.comap C` has prime height `0`;
- `X ∉ Q`.

What is already done:

- the quotient/localization commutation lemmas are proved;
- the polynomial quotient/localization equivalence is proved;
- the `X ∈ Q` branch is proved;
- the broad structural proof of the polynomial CM theorem is complete.

Current preferred route:

- work directly in the height-1, `X ∉ Q` corner;
- produce an element of `Q` that is regular on `B[X]_Q`;
- use the already-proved 1-element weakly regular-sequence criterion in
  dimension `1` to conclude Cohen–Macaulayness.

Rejected route:

- direct monic-lift from `B/q` was too optimistic because `B/q` need not be a
  field.

Current mathematical route:

- use associated-prime control for `B[X]` in this branch to find
  `g ∈ Q \ q.map C` that is regular;
- then conclude CM of the 1-dimensional local ring.


## Dependency chain to BEI

After this final sorry is filled:
1. `isCohenMacaulayRing_mvPolynomial_field` becomes sorry-free.
2. Closing `BEI/Equidim.lean:4214` then requires the HH ring isomorphism
   `R_p ≅ (MvPolynomial σ' K)_q` for `p ⊄ augIdeal`.

Immediate work order:

1. complete the final polynomial-CM subcase;
2. only then return to the HH ring isomorphism in `BEI/Equidim.lean`.

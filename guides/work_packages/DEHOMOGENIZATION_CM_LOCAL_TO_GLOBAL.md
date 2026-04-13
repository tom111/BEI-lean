# Guide: Dehomogenization Packet for HH Global CM

## Status: superseded route memo

This guide is no longer the active packet for the last HH-side blocker.

It is kept only as a record of the dehomogenization / Laurent-extension route
that was investigated and then set aside in favor of the graded-induction
route in:

- [GRADED_CM_INDUCTION.md](GRADED_CM_INDUCTION.md)

## Task

This is the new supporting packet for the last HH-side blocker in
Proposition 1.6.

The consumer theorem remains in
[BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean):

- `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`

That theorem now has exactly one remaining `sorry`, and the `p ⊆ augIdeal`
branch is already closed.  The only remaining branch is `p ⊄ augIdeal`.


## Why this packet exists

The earlier hope was that the `p ⊄ augIdeal` case could be closed by a direct
HH-specific localization argument after inverting one variable and killing its
neighbors.  That work was still valuable:

- it proved the structural localization lemmas in `BEI/Equidim.lean`;
- it ruled out false shortcuts through minimal primes;
- it reduced the problem to a standard graded commutative-algebra theorem.

The remaining blocker is now best understood as a dehomogenization / Laurent
extension packet, not as another HH combinatorics packet.


## Current verified state

### In `BEI/Equidim.lean`

Already proved:

- `isCohenMacaulayLocalRing_at_augIdeal`
- `augIdeal_le_of_forall_mkI_X_mem`
- `exists_var_not_mem_of_not_le_augIdeal`
- `isUnit_algebraMap_mkI_X`
- `algebraMap_mkI_X_eq_zero_of_edge`
- `algebraMap_mkI_y_eq_zero_of_x_not_mem`
- `algebraMap_mkI_x_eq_zero_of_y_not_mem`
- `ringEquiv_isLocalHom`
- `isWeaklyRegular_map_ringEquiv`
- `isCohenMacaulayLocalRing_of_ringEquiv`

Also already closed inside the main theorem:

- the branch `p ≤ augIdeal`

Still open:

- the branch `p ⊄ augIdeal`

### In `toMathlib/CohenMacaulay/Localization.lean`

Completed and available:

- forward CM transfer;
- unmixedness for CM local rings;
- `CM localizes`;
- the wrapper `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`.

So the remaining work is no longer “prove CM localizes”.


## Exact mathematical target

For the HH quotient

```text
R = S ⧸ bipartiteEdgeMonomialIdeal G
```

and a prime `p` with `p ⊄ augIdeal`, the standard route is:

1. choose a degree-1 element `r ∈ augIdeal \ p`, so `r` is a unit in `Rₚ`;
2. dehomogenize:
   `R[r⁻¹] ≅ R[r⁻¹]₀[r, r⁻¹]`;
3. identify
   `R_{augIdeal} ≅ (R[r⁻¹]₀)_{m₀}`
   for the augmentation / irrelevant maximal ideal `m₀` of the degree-0 part;
4. transfer CM from `R_{augIdeal}` to `(R[r⁻¹]₀)_{m₀}`;
5. localize further to `(R[r⁻¹]₀)_{p₀}`;
6. use Laurent polynomial extension to conclude `Rₚ` is CM.


## Recommended theorem decomposition

The smallest honest development is probably:

1. A dehomogenization isomorphism for homogeneous polynomial quotients after
   inverting a degree-1 element.
2. The identification of the augmentation localization with the localization of
   the degree-0 part.
3. CM preservation under Laurent polynomial extension, or a theorem reducing it
   to the already available polynomial-CM results if those are backported.

If a narrower theorem specialized to quotients of `MvPolynomial` over a field
is enough, that is acceptable.


## What this packet is not

- It is **not** another attempt to prove the `p ≤ augIdeal` case.
- It is **not** the Gröbner CM transfer theorem.
- It is **not** broad graded-ring infrastructure for its own sake.

The only goal is to remove the last `sorry` in the HH-side global CM theorem.


## Warnings

- Do not overclaim the HH theorem as proved until the `p ⊄ augIdeal` branch is
  actually closed.
- Do not reopen the already-completed CM-localization backport.
- Do not replace this packet with vague references to Goto–Watanabe unless the
  exact Lean theorems to implement are identified.


## Definition of done

Best outcome:

- the dehomogenization / Laurent-extension infrastructure is formalized at the
  smallest truthful level needed;
- the remaining `sorry` in
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
  disappears.

Minimum acceptable outcome:

- the exact theorem interface for dehomogenization is isolated cleanly in Lean,
  with a follow-up support packet if one more layer is needed.

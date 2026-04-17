# Guide: CM Parameter Prefix — Final Base Case

## Status: superseded route memo

This file is kept as a record of the parameter-prefix route exploration.
That route was useful for narrowing the proof, but the active remaining
base-case blocker is now the polynomial-ring-over-a-field CM theorem, tracked
in [POLYNOMIAL_RING_CM_BASE_CASE.md](POLYNOMIAL_RING_CM_BASE_CASE.md).

## Historical endpoint of this route

The sorry in `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
reduces to one standard algebraic fact not yet in Mathlib:

> **Localizations of polynomial rings over fields are Cohen–Macaulay.**

Equivalently: regular local rings are CM (Serre / Auslander–Buchsbaum).


## Proof structure for the sorry

The `p ⊄ augIdeal` case has the following clean argument:

1. By `exists_var_not_mem_of_not_le_augIdeal`: some variable `x_v ∉ p`.
2. In the local ring `R_p`: the HH diagonal gives `x_v · y_v = 0` with
   `x_v + y_v` a unit (from the reg seq). By the local-ring dichotomy
   (`ab = 0, a + b` unit → one is 0), one of `{x_v, y_v}` is 0 and the
   other is a unit.
3. Propagating through all diagonal sums and cross-edges: EVERY variable
   in `R_p` is 0 or a unit.
4. Each monomial generator `x_i y_j ∈ I` has at least one zero factor, so
   it vanishes in `R_p`.
5. The ideal `I` becomes trivial in `R_p`, giving
   `R_p ≅ (K[surviving variables])_{p'}`.
6. This is a localization of a polynomial ring over `K`.
7. **Need**: localizations of polynomial rings over fields are CM.


## The isolated gap

```lean
-- NOT YET IN MATHLIB
theorem isCohenMacaulayRing_mvPolynomial (K : Type*) [Field K]
    (σ : Type*) [Fintype σ] [DecidableEq σ] :
    IsCohenMacaulayRing (MvPolynomial σ K)
```


## Comparison of routes

### Route A: Direct induction on number of variables

- Base: `MvPolynomial ∅ K ≅ K` → field → CM.
- Step: Need "polynomial extension preserves CM."
  `A[X]` CM when `A` CM — requires showing for each prime `Q` of `A[X]`:
  - If `X ∈ Q`: quotient by `X` gives `A`, apply IH + converse CM transfer.
  - If `X ∉ Q`: the fiber structure (primes of `k(P)[X]`) + going-down.
- **Verdict**: moderate complexity; needs going-down for polynomial extensions.

### Route B: Regular local rings are CM

- Need `IsRegularLocalRing` definition (embedding dimension = Krull dimension).
- Need `MvPolynomial` localizations are regular.
- Need regular → CM.
- **Verdict**: large dependency cone (embedding dimension not in Mathlib).

### Route C: Direct induction on height of the prime

- Base: height 0 → fraction field → field → CM.
- Step: height `h > 0` → pick nonzero `f ∈ q` (NZD in domain) → quotient
  → dimension drops by 1 → IH on the quotient localization.
- **Issue**: quotient of polynomial ring by `f` is NOT a polynomial ring.
  Need: either (a) IH strong enough for all quotients, or (b) pick `f` to be
  a variable.  For (b): `q` might not contain a variable.
- **Verdict**: Route C works ONLY if combined with Route A's variable-splitting.

### Recommendation at the time

Route A is the most accessible. The key theorem to prove:

```lean
theorem isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsCohenMacaulayRing A] :
    IsCohenMacaulayRing A[X]
```

With this, `isCohenMacaulayRing_mvPolynomial` follows by induction on `|σ|`.


## What NOT to do

- Do not reopen the `p ≤ augIdeal` branch.
- Do not reopen graded contraction, graded induction, or dehomogenization.
- Do not switch to the Gröbner CM transfer theorem.
- Do not implement embedding dimension unless Route B is strictly chosen.

# Guide: Graded CM Induction for HH Global CM

## Status: superseded route memo

This file is kept as a record of the graded-induction branch that narrowed the
last HH-side blocker. The active support packet is now
[GRADED_CONTRACTION_NZD.md](GRADED_CONTRACTION_NZD.md).

## Task

Close the last sorry in `BEI/Equidim.lean`:
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`, case `p ⊄ augIdeal`.

## Why dehomogenization and HH induction fail

### Dehomogenization (Route 1)
Requires formalizing: graded ring structure on MvPolynomial quotients,
the dehomogenization isomorphism `R[r⁻¹] ≅ R[r⁻¹]₀[r±¹]`, CM of Laurent
extensions, and several localization identifications. Very large dependency
cone with no existing Lean infrastructure.

### HH induction (Route 2)
When we invert a variable and kill its neighbors, the surviving graph does
NOT satisfy the HH conditions (the diagonal condition breaks because some
x/y pairs lose their partner). So pure HH induction is impossible. The
surviving quotient is a general squarefree monomial quotient, not HH-type.

### "Every prime contains a minimal prime" (wrong direction)
If q ⊆ p are primes, then R_q is a further localization of R_p (NOT the
reverse). So CM of R_q does NOT imply CM of R_p. The localization
direction is: q ⊆ p ⟹ q^c ⊇ p^c ⟹ R_q = (R_p)_{q'}, and CM descends
(from R_p to R_q), not ascends.

## Correct approach: graded CM induction

The standard proof from Bruns–Herzog 2.1.3 adapted to this setting.

### Key theorem

For R = K[x₁,...,xₘ]/I (I monomial, hence homogeneous), if R_{m⁺} is CM
then R is CM.

### Proof by induction on dim(R_{m⁺})

**Base case**: dim = 0. R = K, trivially CM.

**Inductive step**: dim(R_{m⁺}) = d > 0. Given R_{m⁺} is CM.

For any prime p of R:
- **p ⊆ m⁺**: R_p is a further localization of R_{m⁺}, hence CM by CM
  localization. ✓ (Already proved in the repo.)

- **p ⊄ m⁺, height(p) = 0**: p is a minimal prime. R_p is a
  0-dimensional Noetherian local ring. Since R is reduced (I is radical,
  proved), R_p is a reduced 0-dimensional local ring = a field. Hence CM.
  ✓ (Uses `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero`.)

- **p ⊄ m⁺, height(p) > 0**: This is the hard case. The proof:
  1. Find a **homogeneous** element r ∈ p that is a **non-zero-divisor**
     on R (graded prime avoidance).
  2. r ∈ m⁺ (since r is homogeneous of positive degree), and r is regular
     on R_{m⁺}. Forward CM transfer: R_{m⁺}/(r) is CM.
  3. R/(r) is a graded ring with dim((R/(r))_{m⁺/(r)}) = d - 1.
  4. By **induction**: R/(r) is CM.
  5. Now r ∈ p ⊆ maxIdeal(R_p), and r is regular on R_p (localization
     preserves non-zero-divisors). And R_p/(r) ≅ (R/(r))_{p/(r)} is CM
     (since R/(r) is CM by step 4).
  6. **Converse CM transfer**: r regular on R_p, r ∈ maxIdeal(R_p),
     R_p/(r) CM ⟹ R_p CM. ✓

### Infrastructure needed

All available EXCEPT graded prime avoidance:

| Component | Status | Location |
|-----------|--------|----------|
| Forward CM transfer | ✅ proved | `toMathlib/CohenMacaulay/Localization.lean` |
| Converse CM transfer | ✅ proved | `toMathlib/CohenMacaulay/Basic.lean:166` |
| CM localization | ✅ proved | `toMathlib/CohenMacaulay/Localization.lean` |
| `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero` | ✅ proved | `toMathlib/CohenMacaulay/Basic.lean:214` |
| `Ideal.exists_minimalPrimes_le` | ✅ in Mathlib | `Mathlib.RingTheory.Ideal.MinimalPrime.Basic` |
| Localization-localization iso | ✅ in Mathlib | `Mathlib.RingTheory.Localization.LocalizationLocalization` |
| Radical/reduced for I | ✅ proved | `bipartiteEdgeMonomialIdeal_isRadical` |
| **Graded prime avoidance** | ❌ needed | new lemma |

### Graded prime avoidance for the HH quotient

**Statement**: For R = K[vars]/I (I squarefree monomial, R reduced), and a
prime p of R with height(p) > 0, there exists a homogeneous element r ∈ p
that is a non-zero-divisor on R.

**Proof strategy**: The minimal primes P₁,...,Pₛ of R are variable-generated
(from `minimalPrime_bipartiteEdgeMonomialIdeal_iff`). Since height(p) > 0, p
is not a minimal prime, so p ⊄ Pᵢ for each i. The zero-divisors of R equal
∪ Pᵢ (since R is reduced). By graded prime avoidance (the ideal p restricted
to homogeneous elements is not contained in any single Pᵢ), there exists a
homogeneous element in p \ ∪ Pᵢ.

**Subtlety**: p might not be a graded ideal. The graded core p* of p might
be contained in some Pᵢ. In that case, we need degree > 1 elements or a
more careful argument.

**Simplification for variable-generated primes**: Since each Pᵢ = span(X '' Cᵢ)
for a vertex cover Cᵢ, a monomial m is in Pᵢ iff every variable of m is in Cᵢ.
So a homogeneous element r = Σ aₐ mₐ avoids Pᵢ if some monomial mₐ (with
aₐ ≠ 0) has a variable outside Cᵢ.

## Preparatory lemmas (ordered by dependency)

### Lemma 1: Minimal primes ≤ augIdeal

```
minimalPrime_le_augIdeal : q ∈ minimalPrimes R → q ≤ augIdeal G
```

Uses: `minimalPrime_bipartiteEdgeMonomialIdeal_iff`, `mkI_X_mem_augIdeal`.
Self-contained, no new infrastructure needed.

### Lemma 2: The HH quotient is reduced

```
bipartiteEdgeMonomialIdeal_quotient_isReduced :
    IsReduced (MvPolynomial _ K ⧸ bipartiteEdgeMonomialIdeal G)
```

Uses: `bipartiteEdgeMonomialIdeal_isRadical` + `Ideal.isRadical_iff_quotient_isReduced`.

### Lemma 3: Height-zero CM

For any minimal prime q of R: R_q is a field, hence CM.

### Lemma 4: Graded prime avoidance

For the HH quotient and a non-minimal prime p: ∃ homogeneous r ∈ p,
r regular on R.

### Lemma 5: Main induction

The graded local-to-global theorem, by induction on dimension using
Lemmas 1–4 + forward/converse CM transfer.

## What NOT to do

- Do not try to close the sorry with localization-localization alone
  (the direction is wrong for q ⊆ p).
- Do not build full Goto–Watanabe or general graded ring infrastructure.
- Do not switch to the Gröbner CM transfer theorem.
- Do not reopen the p ≤ augIdeal branch.

## Definition of done

The sorry in `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
disappears. The proof uses the graded induction argument with existing
forward/converse CM transfer infrastructure.

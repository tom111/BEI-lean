# Next-Session Prompt: attack `tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant`

## One-line goal

Close the remaining R1 leaf sorry
`tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant` in
`BEI/GroebnerDeformation.lean` — local Cohen–Macaulayness of `S[t] ⧸ Ĩ` at
its irrelevant ideal, via the regular-quotient lift through `t` (already
known to be a non-zero-divisor by `tildeJ_t_isSMulRegular`). Together with
the already-applied graded local-to-global principle from
`toMathlib/GradedCM.lean`, this closes `tildeJ_quotient_isCohenMacaulay` and
hence Proposition 1.6 modulo the GradedCM Case-C dormant sorry.

## What landed in the previous session

All BEI-side graded plumbing for R1.f.1 is now formalised with clean
axioms `{propext, Classical.choice, Quot.sound}`:

- `defWeight n : DefVars n → ℕ` — weight function with positive values.
- `isWeightedHomogeneous_fijTilde` — each `f̃_{i,j}` (with `i < j`) is
  weighted-homogeneous of degree `2(n+1-i) + (n+1-j)`.
- `defGrading n` — the weight grading on `DefRing n K`, with a registered
  `GradedAlgebra` instance.
- `tildeJ_isHomogeneous` — `tildeJ G` is homogeneous.
- `tildeJQuotGrading G` — induced grading on `DefRing n K ⧸ tildeJ G`,
  with a registered `GradedRing` instance.
- `tildeJQuotGrading_connectedGraded` — connected graded (`𝒜 0 = K`).
- `tildeJ_ne_top` / `tildeJ_quotient_nontrivial` — properness and
  `Nontrivial` of the quotient.

`tildeJ_quotient_isCohenMacaulay` is now a one-liner application of
`GradedCM.isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`
fed the connectedness proof and the new sub-sorry. The old monolithic
`sorry` is gone from this theorem.

## State at start of session

**R1.d chain is fully closed.** The following are all proved with clean
axioms `{propext, Classical.choice, Quot.sound}`:

- `DefVars n := BinomialEdgeVars (Fin n) ⊕ Unit` (opaque wrapper)
- `defLE` with `t = inr ()` as LARGEST (least significant in lex)
- `fijTilde_lex_lt`, `degree_fijTilde`, `leadingCoeff_fijTilde`
- `tildeJ_div`, `polyTInclude_mul_support_avoids`
- `tildeJ_isGroebnerBasis` (Buchberger + closed graph case analysis)
- `tildeJ_gbProperty` (via `exists_degree_le_of_mem` from `BEI/Radical.lean`)
- `tildeJ_polyT_colon_eq`
- `tildeJ_flat_over_polyT`, `tildeJ_tMinusOne_isSMulRegular`,
  `tildeJ_t_isSMulRegular`
- `groebnerDeformation_cm_transfer` (four-arrow assembly; depends on
  `tildeJ_quotient_isCohenMacaulay` + regular-quotient descent)

The remaining open sorry in R1:

```lean
theorem tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant
    {n : ℕ} {G : SimpleGraph (Fin n)} (_hClosed : IsClosedGraph G)
    (_hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    haveI := (GradedIrrelevant.irrelevant_isMaximal (tildeJQuotGrading G)
      (tildeJQuotGrading_connectedGraded G)).isPrime
    IsCohenMacaulayLocalRing (Localization.AtPrime
      (HomogeneousIdeal.irrelevant (tildeJQuotGrading G)).toIdeal)
```

`proposition_1_6` axiom check is `{propext, sorryAx, Classical.choice, Quot.sound}`,
with `sorryAx` coming only from this one remaining sub-sorry (and from the
dormant GradedCM Case-C sorry, transitively via the graded LTG theorem).

## Strategy (documented in existing guides)

See:

- `guides/work_packages/FULL_PROP_1_6_PLAN.md` — overall 3-phase plan
- `guides/work_packages/PROP_1_6_CM_TRANSFER.md` — overall CM transfer strategy
- `guides/work_packages/GROEBNER_CM_TRANSFER.md` — the Gröbner deformation transfer

### Narrow strategy for the remaining sub-sorry

`L := Localization.AtPrime (irrelevant of DefRing ⧸ tildeJ G)` is the local
ring we need to prove CM. Strategy (= the local branch of the classical
Eisenbud 15.17 argument):

1. Produce `t̂ : L`, the image of `tDef n` through `DefRing ⧸ tildeJ G → L`.
2. Show `t̂ ∈ maximalIdeal L` (since `tDef` has positive weight, hence in
   the irrelevant ideal of the quotient).
3. Show `t̂` is regular on `L` — follows from `tildeJ_t_isSMulRegular`
   (already proved) plus flatness of localisation
   (`IsSMulRegular.of_flat`).
4. Show `L ⧸ (t̂)` is CM local. This reduces via a localisation-quotient
   commutation step (see `quotSMulTopLocalizationEquiv_of_mem` pattern in
   `toMathlib/CohenMacaulay/Polynomial.lean`) to the localisation of
   `(DefRing ⧸ tildeJ G) ⧸ (tDef-class)` at the image of the irrelevant
   ideal. That double quotient is isomorphic (via `specZero` + the first
   isomorphism theorem, using `tildeJ_specZero_eq`) to
   `S ⧸ monomialInitialIdeal G`, which is globally CM by hypothesis, so
   any localisation is CM.
5. Apply `isCohenMacaulayLocalRing_of_regular_quotient` to conclude
   `L` is CM local.

The new BEI-side hypothesis and helpers to reach for:

- `tildeJ_t_isSMulRegular` — already in the file.
- `algebraMap_polyT_t` — the map of `tDef n` into the quotient.
- `tildeJ_specZero_eq` — `specZero(tildeJ) = monomialInitialIdeal G`.
- The `quotSMulTopLocalizationEquiv_of_mem` construction pattern from
  `toMathlib/CohenMacaulay/Polynomial.lean:470`.

## Do not

- Touch `toMathlib/HeightAdditivity.lean`.
- Refactor unrelated BEI files.

# Plan: Close the HH `p ⊄ m⁺` sorry — final chain (revised 2026-04-19)

## Context

The F2 route to Proposition 1.6 CM at non-augmentation primes has landed
seven of the eight pre-assembly pieces:

| Piece | Status | Name / location |
|---|---|---|
| L3 (one-sided survivors isolated) | ✓ done | `hhSurvivor_{x,y}_isolated` |
| L4 (surviving-graph decomposition) | ✓ done | `L4Iso`, `BEI/Equidim.lean` |
| L5 (reduced HH at aug is CM, original form) | ✓ done | `isCohenMacaulayLocalRing_reducedHH_at_augIdeal` |
| L6 (polynomial-away tensor merge) | ✓ done | `polynomialAwayTensorEquiv` |
| L7 replacement (tensor-poly-loc CM) | ✓ done | `isCohenMacaulayRing_tensor_away` |
| L1 (monomial-localisation iso) | ✓ done | `L1Iso`, `BEI/Equidim.lean` |
| Session A′ (reduced-HH aug-ideal CM bridge) | ✓ done | `isCohenMacaulayLocalRing_at_augIdealReduced` (r = 0 base + inductive step, `BEI/Equidim.lean`) |
| **Sessions B, C1, C2, C3 (global CM + final chain)** | pending | `BEI/Equidim.lean:6786` |

The sole remaining sorry is the `p ⊄ m⁺` branch of
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`.

## Revision note (2026-04-18, post thinking-model consult)

A deep-model consultation produced two refinements to the original plan:

1. **Session A is simpler than the full trailing-pair tensor iso**. The
   direct bridge `((R_G)_m ⧸ x_r) ⧸ y_r  ≅  (reducedHHRing G)_{m_red}`
   suffices; the full iso `R_G ≅ reducedHHRing G ⊗_K K[Fin 2]` is not
   needed. This uses the same underlying no-last-pair fact but avoids
   building a tensor decomposition at the ring level.

2. **A new micro-lemma — "tensor-left-localisation bridge" — is
   needed** as part of Session C: for a K-algebra `A`, a K-algebra `B`,
   and a prime `𝔓 ⊂ A ⊗_K B` with `𝔓 ∩ A = m`,

       (A ⊗_K B)_𝔓  ≅  (A_m ⊗_K B)_𝔓'.

   Without this, L7 applies to the wrong ring: the L1/L4/L6 chain
   lands in `(reducedHHRing G' ⊗ B)_𝔓`, but our CM input is for
   `(reducedHHRing G')_m` (the localised form from Session A).

## The L5 form mismatch (recap)

L5 currently proves CM of

    ((R_G ⊗ localisation at augIdeal) ⧸ x_last) ⧸ y_last  (in L5's specific form)

for the **original** HH ring `R_G`. What we need is

    Localization.AtPrime (augIdealReduced G') (reducedHHRing G')  is CM local

for the **abstract** reduced HH ring of the smaller graph `G'`.

## Revised three-session plan

### Session A′ — reduced-augmentation CM bridge

Split into two sub-sessions after a size-estimate reality-check (the
original "100-200 LOC" substantially underestimated the inductive
bridge).

#### Session A′.1 — augIdealReduced + base case (DONE, ~130 LOC)

**Status**: landed in commit `6c47f83`.

Exports:
- `augIdealReduced G'` (definition) + `_isMaximal` / `_isPrime` /
  `mkI_X_mem_` (all in `BEI/ReducedHH.lean`).
- `reducedHHRing_equiv_K_of_r_zero` (base-case iso in `BEI/Equidim.lean`).
- `isCohenMacaulayLocalRing_at_augIdealReduced_base` — the `r = 0`
  base case, via `isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero`.

#### Session A′.2 — inductive case `r ≥ 1` (DONE, ~1100 LOC including already-drafted support)

**Status**: landed in commit `9067040`.

Exports:
- `isCohenMacaulayLocalRing_at_augIdealReduced_step` — inductive case
  (`hr : 1 ≤ r`), via the 4-step bridge.
- `isCohenMacaulayLocalRing_at_augIdealReduced` — the combined
  `hr`-free version (base + step).

Support infrastructure added in the same session:
`killLastPairIdeal`, `killLastPairPoly*`, `killLastPairEquiv`,
`augIdealQuot`, `RpModLastPairEquivLoc`, and
`locAugIdealQuotEquivLocAugIdealReduced`.

**Bridge (as landed)**: 4 non-trivial ring equivalences plus a transport of L5:

1. `QuotSMulTop mkyL RpQ ≃+* (Rp ⧸ span{xL}) ⧸ span{mkyL}` — via
   `quotSMulTopRingEquivIdealQuotient`.
2. `(Rp ⧸ span{xL}) ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}` — via
   `DoubleQuot.quotQuotEquivQuotSup`, then `Ideal.quotEquivOfEq`
   (with `Set.insert_eq` + `Ideal.span_union`) to reshape
   `span{xL} ⊔ span{yL}` into `span {xL, yL}`.
3. `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot`
   (on `R_G ⧸ killLastPairIdeal`) — **built by hand** using
   `Localization.localRingHom` with explicit surjectivity/injectivity
   arguments. No clean Mathlib candidate matched this shape.
4. `Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced` —
   via `killLastPairEquiv` (polynomial-level `aeval` + quotient descent)
   and `IsLocalization.algEquiv` to transport the localisation across
   the primes (Step 4 implementation is in
   `locAugIdealQuotEquivLocAugIdealReduced`).

Then `isCohenMacaulayLocalRing_of_ringEquiv'` composes Steps 1–4 with
L5 as the CM hypothesis.

**Retrospective note on Step 3**: Mathlib does not (in this snapshot)
offer a direct lemma for "localisation of quotient = quotient of
localisation of a prime containing the quotienting ideal." Building
it inline via `Localization.localRingHom` + bijectivity was the
pragmatic choice. If the pattern recurs, it would be worth factoring
out a `toMathlib/LocalizationQuotient.lean` helper.

### Session B — promote local CM to global CM (~20–50 LOC)

**Goal**:

    isCohenMacaulayRing_of_augIdealReduced_localisation
      (G : SimpleGraph (Fin (r + 1))) [HH G] :
      IsCohenMacaulayRing
        (Localization.AtPrime (augIdealReduced G) (reducedHHRing G))

via `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing` applied to
Session A′'s conclusion. Near-mechanical.

**Location**: same file as Session A′.

**Risk**: trivial.

### Session C — final chain composition (~250–450 LOC)

Broken into three sub-sessions as the thinking-model recommended.

#### Session C1 — bundled unlocalised equivalence (~100–180 LOC)

Build a **single** ring/algebra equivalence:

    E_U : R[(mkI s_U)⁻¹]  ≅ₐ[K]  reducedHHRing G' ⊗_K Localization.Away s_ΛU

where `s_ΛU : MvPolynomial (lambdaSet G U ⊔ U) K` is the renamed
product of U-variables. Construct via a chain of existing isos:

- `L1Iso` : `R[(mkI s_U)⁻¹] ≅ restrictedHHRing G (hhSurvivors G U) ⊗_K Localization.Away s_U^U`.
- `L4Iso` applied to the left tensor factor:
  `restrictedHHRing G (hhSurvivors G U) ≅ reducedHHRing G' ⊗_K MvPolynomial (lambdaSet G U) K`.
- `polynomialAwayTensorEquiv` (L6) applied to the rightmost two tensor
  factors after re-associating:
  `MvPolynomial Λ K ⊗_K Localization.Away s_U^U ≅ Localization.Away s_ΛU`.
- `Algebra.TensorProduct.assoc`, `congr`, etc. for the re-associations.

**Location**: `BEI/Equidim.lean`, immediately before the main theorem.

**Risk**: moderate. Mostly mechanical tensor-associativity and
`AlgEquiv.trans` gluing, but with heavy universe/instance pressure.

#### Session C2 — tensor-left-localisation bridge (~80–150 LOC)

Build a new reusable lemma:

    tensor_left_localisation_of_comap_eq_maximal
      {K A B : Type*} [Field K] [CommRing A] [Algebra K A]
      [CommRing B] [Algebra K B]
      (m : Ideal A) [m.IsMaximal]
      (𝔓 : Ideal (TensorProduct K A B)) [𝔓.IsPrime]
      (h : 𝔓.comap (includeLeft) = m) :
      Localization.AtPrime 𝔓
        ≃+* Localization.AtPrime
          (Ideal.map (someTensorLocAlgebra) 𝔓)

**Mathematical content**: localising `A ⊗_K B` at a prime `𝔓` whose
contraction to `A` is `m` is the same as first localising the `A`
factor at `m` (yielding `A_m ⊗_K B`) and then localising at the
induced prime.

**Location**: `toMathlib/CohenMacaulay/TensorPolynomialAway.lean`
(augmenting the existing L7 replacement file) or a new
`toMathlib/TensorLocalisation.lean` if there are more such bridges.

**Risk**: moderate. Conceptually clean, but the Mathlib API for
tensor-product localisations may not offer exactly this shape — may
need `IsLocalization` instance composition by hand.

**Alternative** (worth considering): restate L7 replacement to accept
`A_m ⊗_K B` form directly — i.e.,

    isCohenMacaulayRing_tensor_away_of_maximal
      ... (m : Ideal A) [m.IsMaximal] (h : IsCohenMacaulayLocalRing A_m)
          (𝔓 : Ideal (A ⊗_K B)) (h𝔓 : 𝔓.comap includeLeft = m) ...

This internalises the bridge inside L7. Fewer external dependencies
but more invasive edit of `toMathlib/CohenMacaulay/TensorPolynomialAway.lean`.

Recommendation: prove the bridge as a standalone lemma; easier to
reason about and reuse.

#### Session C3 — assembly and close the sorry (~70–120 LOC)

Inside the main theorem's `p ⊄ augIdeal` branch:

1. Define `U := unit variables at p` (`Finset.univ.filter`).
2. Show `hhIndep G (U : Set _)` via primality.
3. Apply `IsLocalization.localizationLocalizationAtPrimeIsoLocalization`
   to get `R_p ≅ (R[(mkI s_U)⁻¹])_{p'}`.
4. Apply `E_U` from Session C1 via localisation-of-equivalence to get
   `(R[(mkI s_U)⁻¹])_{p'} ≅ (reducedHHRing G' ⊗_K B)_𝔓` where
   `𝔓 = E_U.map p'`.
5. Show `𝔓.comap includeLeft = augIdealReduced G'` (= `m` in the
   bridge). By construction: every reduced HH variable maps to a paired
   survivor, which is in `W ⊆ p`, so its image in the tensor lies in
   `𝔓`. Hence `augIdealReduced ⊆ 𝔓.comap`. Since `augIdealReduced` is
   maximal and `𝔓.comap` is proper, equality.
6. Apply Session C2's bridge: `(reducedHHRing G' ⊗_K B)_𝔓 ≅
   ((reducedHHRing G')_m ⊗_K B)_𝔓'`.
7. Apply L7 replacement with `A := (reducedHHRing G')_m` (globally CM
   by Session B) and `s := s_ΛU` to conclude `IsCohenMacaulayRing ((reducedHHRing G')_m ⊗_K B)`.
8. Apply `IsCohenMacaulayRing.CM_localize` at `𝔓'`.
9. Transport CM back to `Localization.AtPrime p R` through the composed
   RingEquiv via `isCohenMacaulayLocalRing_of_ringEquiv'`.

**Risk**: moderate. Bookkeeping heavy, but each step has a direct
Lean analogue.

### Total effort (revised after Session A′.1 landed)

- Session A′.1 (DONE): ~130 LOC.
- Session A′.2 inductive bridge: ~400–700 LOC (moderate-high risk).
- Session B: ~20–50 LOC (trivial).
- Session C1: ~100–180 LOC (moderate).
- Session C2: ~80–150 LOC (moderate).
- Session C3: ~70–120 LOC (moderate).
- **Total remaining**: ~670–1200 LOC.

Upper-range estimate revised upward: the Session A′ inductive bridge
was substantially underestimated. Step 3 (localisation-quotient
commutation) is the single biggest unknown — if Mathlib's
`IsLocalization` API cannot express this directly, a bespoke proof
could push the session further still.

## Execution order

Strongly recommend:
1. Session A′ first (enables B; smaller than the old Session A).
2. Session B (trivial once A′ lands).
3. Session C1 (bundled equivalence; can be attempted in parallel with C2).
4. Session C2 (tensor-left-localisation bridge; independent).
5. Session C3 (consumes B, C1, C2 to close the sorry).

## Notes from the thinking-model consult

- **Trailing-pair iso form**: mathematically exactly right; the full
  tensor iso `R_G ≅ reducedHHRing G ⊗_K K[Fin 2]` is correct but
  heavier than necessary. Use the direct quotient bridge instead.
- **Prime transport**: bundle L1/L4/L6 before localising. One prime
  comap suffices for the whole chain, plus one extra for the
  tensor-left-localisation bridge.
- **Base case `r = 0`**: no mathematical risk. Handle uniformly
  inside Session A′ via `by_cases hr : r = 0`.
- **Instance / universe hygiene**: `Fintype` / `DecidableEq` on
  `Λ ⊔ U` should be routine. May need explicit local instances for
  instance search speed.

## Open risk (documented for posterity)

The tensor-left-localisation bridge (Session C2) is the single most
likely source of a nasty Lean surprise. If Mathlib's `IsLocalization`
machinery does not compose cleanly for this specific shape, the
bridge may balloon from ~100 LOC to ~300+ LOC.

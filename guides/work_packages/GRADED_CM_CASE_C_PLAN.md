# Plan: Close `GradedCM.caseC_CM_transfer` (Bruns–Herzog 2.1.27, non-homogeneous primes)

## Why this matters

"Dormant" was misleading shorthand. The sorry is **load-bearing** — it is
the sole remaining transitive `sorryAx` for `proposition_1_6`, and the
only gap on the Proposition 1.6 formalization path. "Dormant" just means
"not currently being actively worked on", not "harmless".

Axiom check (2026-04-21):
- `proposition_1_6`: `{propext, sorryAx, Classical.choice, Quot.sound}`
  — `sorryAx` enters **only** via `caseC_CM_transfer`.
- Every other piece on the Prop 1.6 critical path is axiom-clean.

**Closing `caseC_CM_transfer` makes Proposition 1.6 fully axiom-clean.**

## The gap

`toMathlib/GradedCM.lean:349`:

```lean
private theorem caseC_CM_transfer
    (p p_star : Ideal A) (_hp_prime : p.IsPrime)
    [_hpstar_prime : p_star.IsPrime]
    (_hpstar_sub_irr : p_star ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (_hCM_pstar : IsCohenMacaulayLocalRing (Localization.AtPrime p_star))
    (_hp_not_hom : ¬ p.IsHomogeneous 𝒜) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p)
```

Context: `A` is a connected ℕ-graded Noetherian `K`-algebra, `p` is a
*non-homogeneous* prime, `p_star = p.homogeneousCore 𝒜` is its
homogeneous core, and CM at the homogeneous `p_star` is given.

## Why the easy routes fail (already verified)

1. **Homogeneous-core localisation trick**: documented as structurally
   wrong in `toMathlib/GradedCM.lean:261–301`. The algebra map goes the
   wrong direction; `A_{p*}` is a *further* localisation of `A_p`, not
   the other way.
2. **BEI-specific bypass via `A[1/t]`**: reduces circularly to
   `IsCohenMacaulayRing (S ⧸ J_G)` — the very thing we are proving.
3. **Conca–Varbaro (squarefree Gröbner degeneration preserves Betti)**:
   requires F-purity in positive characteristic; no Mathlib infra;
   heavier than the graded-depth route.
4. **Hilbert-series invariance**: needs graded Betti numbers and a
   "same Hilbert series ⇒ same depth under deformation" theorem; also
   not in Mathlib.

## Classical argument (Bruns–Herzog 1.5.8 / 2.1.27)

Let `A` be a finitely generated connected ℕ-graded `K`-algebra, `p` a
non-homogeneous prime, `p* := p.homogeneousCore 𝒜`. The argument chains:

* **Dim formula**: `dim A_p = dim A_{p*} + tr.deg_K(κ(p) / κ(p*))`.
* **Depth formula**: `depth A_p + dim(A_p / p·A_p) = depth A_{p*} + dim(A_{p*} / p*·A_{p*})`.
* Combining, with `depth A_{p*} = dim A_{p*}` (CM hypothesis) and
  `dim(A_p / p·A_p) = tr.deg_K(κ(p) / κ(p*))` (a residue-field identity),
  one gets `depth A_p = dim A_p`.

The key tool is the *-**local theory of graded rings**: a graded ring `A`
can be localised at a homogeneous prime `p*` by inverting only homogeneous
elements not in `p*`, producing the *-**local** ring `A_{(p*)}`. Its *-depth
equals the ordinary depth at `p*`, and has good behaviour under further
non-homogeneous localisation.

## Mathlib-side building blocks (surveyed 2026-04-21)

**Already available**:

* `Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization`: the
  *-local ring `HomogeneousLocalization 𝒜 x` for a submonoid
  `x ⊆ A`. In particular for `x = (𝒜 \ p*).degZeroSubmonoid` or similar,
  this realises `A_{(p*)}`.
  - `HomogeneousLocalization.isLocalRing` — it is local.
  - `HomogeneousLocalization.val` — canonical embedding into the full
    localisation.
* `Mathlib.RingTheory.AlgebraicIndependent.Transcendental`: `trdeg R A`,
  `lift_trdeg_add_le`, `trdeg_add_le` (tower inequality).
* `Mathlib.RingTheory.KrullDimension.*`: height, coheight, local
  dimension formulas.
* `Mathlib.RingTheory.Flat.*`: flatness preservation of regular sequences.

**Not yet available** (to be built in `toMathlib/`):

* *-depth of a graded module = longest regular sequence in the irrelevant
  homogeneous submodule.
* Identity `*-depth A = depth A_m` where `m = 𝒜₊` (equality for
  finitely generated graded modules over Noetherian K-algebras; BH 1.5.8).
* Depth additivity under localisation: `depth A_p ≥ depth A_{p*} - dim(κ(p) / κ(p*))`
  (sharpness via CM hypothesis).
* Dim formula for residue field extensions over a graded K-algebra:
  `dim A_p = dim A_{p*} + tr.deg(κ(p) / κ(p*))`.

## Phased plan

### Phase CC-1 — `*-depth` definition + basic API (~100–200 LOC)

In a new file `toMathlib/GradedDepth.lean`:

- Define `gradedRegularSequence 𝒜 (rs : List A)`: the list is homogeneous
  of positive degree and forms an ordinary regular sequence.
- Define `starDepth 𝒜 = sSup {rs.length : gradedRegularSequence 𝒜 rs}`.
- Show `starDepth 𝒜 ≤ ringDepth (Localization.AtPrime 𝒜₊)`.
- (Goal of this phase) Show `starDepth 𝒜 = ringDepth (Localization.AtPrime 𝒜₊)`
  for finitely generated graded Noetherian K-algebras.

### Phase CC-2 — residue-field dim identity (~100–200 LOC)

- For connected ℕ-graded A and a prime p with core p*:
  `dim A_p = dim A_{p*} + tr.deg_K(κ(p) / κ(p*))`.
- Requires Noether normalisation for finitely generated graded K-algebras
  (essentially existing in Mathlib for ungraded; needs graded refinement).
- Mathlib already has `RingTheory.Dimension.NoetherNormalization` partially;
  assess reuse.

### Phase CC-3 — *-depth at non-homogeneous primes (~100–200 LOC)

- Show `depth A_p = *-depth A_{p*} + (something)`.
- Or equivalently: `depth A_p + dim(A_p / pA_p) = depth A_{p*} + dim(A_{p*} / p*A_{p*})`.
- With `dim(A_{p*} / p*A_{p*}) = 0` and `dim(A_p / pA_p) = tr.deg κ(p)/κ(p*)`,
  this reduces to `depth A_p = depth A_{p*} - tr.deg κ(p)/κ(p*)`.

### Phase CC-4 — assemble Case C (~30–50 LOC)

Given:
- `depth A_{p*} = dim A_{p*}` (CM hypothesis).
- `depth A_p = depth A_{p*} - tr.deg κ(p)/κ(p*)` (Phase CC-3).
- `dim A_p = dim A_{p*} + tr.deg κ(p)/κ(p*)`? **WAIT — this doesn't work
  sign-wise.** Let me re-check.

Actually BH 1.5.8 says:
- `*-dim A_p = *-dim A_{p*} + tr.deg_{κ(p*)}(κ(p))` — this is for *-dim.
- Ordinary `dim A_p ≤ dim A_{p*}` because `p* ⊆ p` are different primes
  of `A`, so `A_p` inverts more and has smaller height.

Hmm, actually the direction is subtle. Let me refer to the source:

> **Bruns–Herzog Theorem 1.5.8**: `grade(p*, A) = depth(A_p) - dim(A_p/p*A_p)`.

Rewriting: `depth A_p = grade(p*, A) + dim(A_p / p*A_p)`.

When `A_{p*}` is CM: `grade(p*, A) = depth(A_{p*}) = dim(A_{p*}) = ht(p*)`.

So: `depth A_p = ht(p*) + dim(A_p / p*A_p) ≥ ht(p) = dim A_p`
(since `depth ≤ dim` with equality iff CM).

The needed inequality: `ht(p*) + dim(A_p / p*A_p) ≥ ht(p)`.

This is the classical dim formula: `ht(p) ≤ ht(p*) + ht(p/p*) = ht(p*) + 1`
(since `p ⊋ p*` with `p/p*` a height-1 prime of `A/p*`).

Actually `dim(A_p / p*A_p)` is the coheight of `p*A_p` in `A_p`, which
equals `dim(A/p*)` localised at `p/p*`, which is `ht(p/p*)` (height of
`p/p*` in `A/p*`).

**Sanity check**: `ht(p) ≥ ht(p*)` (chain of primes containing p contains
chains containing p*, after intersection with p*). For non-homogeneous p,
`ht(p) ≥ ht(p*) + 1` generically.

### Phase CC-5 (alternative) — BH 1.5.8 direct

The cleanest path is to port **BH Theorem 1.5.8 itself** verbatim:

```
grade(p*, A) = depth(A_p) - dim(A_p / p* A_p)
```

as a standalone lemma, then plug it in. This still requires:

- Graded grade theory.
- Dim-coheight equality at localisations.

**Total refined estimate**: 500–900 LOC split into 3–5 sub-files. The
biggest risk is Phase CC-1 (graded depth API), since it may require
extensive reworking of existing Mathlib depth infrastructure.

## Recommended concrete next action

**Phase CC-0: Mathlib survey (1 session)**

Before building anything, do an exhaustive survey of:

1. `Mathlib.RingTheory.KrullDimension.*` — what height/depth/dim formulas
   already exist? Specifically look for:
   - `Ideal.height` vs `primeHeight` infrastructure.
   - `Ideal.coheight` and `ringKrullDim_quot` identities.
   - Noether normalisation + dimension-transfer.

2. `Mathlib.RingTheory.GradedAlgebra.*` — what is already built?
   - `HomogeneousLocalization` — usable as `A_{(p*)}`?
   - Any `*-depth` or `*-dim` yet?

3. `Mathlib.RingTheory.Depth.*` (if it exists) — how is ordinary depth
   defined? We can build `*-depth` to mirror it.

4. `Mathlib.RingTheory.Flat.*` — regular-sequence-through-flat arguments.

Produce a short report: for each of the 4 needed building blocks (Phase
CC-1, CC-2, CC-3, CC-4/5), what is already in Mathlib, what needs to be
built, and the estimated LOC. This lets us refine the total estimate and
pick the smallest viable Phase 1.

**Decision fork**: after the survey, decide whether to:

- Pursue the full general-purpose Case C (heavy, reusable upstream).
- Find a narrower BEI-specific reformulation that avoids the residue-field
  transcendence-degree machinery (lighter, not upstreamable).

## Alternative strategy: the Eisenbud 18.3 "generic hyperplane" trick

A separate classical approach avoids *-depth entirely, using:

1. Pick a generic linear form `ℓ ∈ 𝒜₁`, which is regular on `A` (by
   prime avoidance + CM of `A_{𝒜₊}`).
2. Show `A / ℓ` is again a finitely generated graded CM K-algebra of dim
   one less.
3. Induction on dimension: base case `dim = 0` is trivial; inductive step
   descends along `ℓ`.

**Pros**: sidesteps `*-depth` and residue-field trdeg theory entirely.
**Cons**: requires prime avoidance at the generic fibre and a graded
regular-sequence API; still needs some new `toMathlib/` work.

**Prima facie estimate**: 300–500 LOC, noticeably less than the
BH 1.5.8 route. Worth considering seriously in the survey.

## Survey results (2026-04-21)

A thorough survey of Mathlib v4.28.0 and the BEI `toMathlib/` identified:

**In Mathlib**:
- `HomogeneousLocalization` + `HomogeneousLocalization.AtPrime` (full
  ring structure, `isLocalRing`, num/den/deg API, 1043 lines).
- `Ideal.height`, `Ideal.primeHeight`, `Ideal.coheight`, `ringKrullDim`
  + `IsLocalization.AtPrime.ringKrullDim_eq_height` +
  `supportDim_quotSMulTop_succ_eq_ringKrullDim_of_mem_jacobson`.
- `IsWeaklyRegular`, `IsSMulRegular`, `IsRegular` (~500 LOC).
- `trdeg R A` + algebraic independence tower lemmas.
- Noether normalisation for fg K-algebras.
- Prime avoidance.

**In BEI `toMathlib/`**:
- `ringDepth` (regular-sequence based, equivalent to ordinary depth).
- `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`.
- `isCohenMacaulayLocalRing_localization_atPrime` (CM localizes).
- `HeightAdditivity.lean` / `HeightVariableIdeal.lean` for polynomial
  extensions.

**Missing** — must be built in `toMathlib/`:
- Connection `height(p) = height(p*) + tr.deg(κ(p)/κ(p*))` or the
  dual depth formula (~150–250 LOC for the BH 1.5.8 route).
- *-depth / graded regular sequences (~150–200 LOC for BH route).
- Residue-field extension `κ(p*) ↪ κ(p)` + trdeg computation
  (~100–150 LOC).

**LOC estimates (refined)**:
- **Route A (BH 2.1.27, homogeneous-core)**: 630–960 LOC total.
  Modular, upstreamable.
- **Route B (Eisenbud 18.3, generic linear form induction)**: 230–280
  LOC total. Smaller, less modular.

## Recommendation (2026-04-21)

**Pursue Route B first** (generic linear form induction):

- ~3× smaller LOC budget.
- Reuses existing BEI infrastructure:
  `isCohenMacaulayLocalRing_of_regular_quotient`
  (already in `toMathlib/CohenMacaulay/Basic.lean`),
  `isCohenMacaulayRing_quotient_of_smulRegular`
  (already in `toMathlib/CohenMacaulay/Polynomial.lean`),
  `quotSMulTopLocalizationEquiv_of_mem`
  (un-privated 2026-04-20).
- Does not require building `*-depth` or residue-field trdeg theory.
- Mathematical content: induction on `dim A` via a homogeneous
  non-zero-divisor `ℓ ∈ 𝒜₊`, reducing CM at `A_p` to CM at
  `(A/ℓ)_{p/(ℓ)}` of dimension one lower.

The core sub-lemmas to build:

1. **Graded prime avoidance**: given finitely many graded primes each
   containing none of `𝒜₊`, produce a homogeneous element of positive
   degree outside all of them. Mathlib has ungraded prime avoidance;
   graded refinement is mechanical but new. (~80 LOC)

2. **Generic NZD existence**: for a graded Noetherian ring `A` with
   `A_{𝒜₊}` CM of dim ≥ 1, there exists a homogeneous `ℓ ∈ 𝒜₊` that
   is a non-zero-divisor on `A`. Uses graded prime avoidance on
   `AssPrime(A)`. (~50 LOC)

3. **Inductive descent**: Given `ℓ` as above, `A/ℓ` is again a graded
   Noetherian K-algebra with `(A/ℓ)_{𝒜₊/(ℓ)}` CM of one-lower dim.
   (~50 LOC: mostly re-plumbing existing instances.)

4. **Case-split on `ℓ ∈ p`**: (~50 LOC)
   - If `ℓ ∈ p`: apply IH to `A/ℓ` at `p/(ℓ)`, then lift back via
     `quotSMulTopLocalizationEquiv_of_mem` +
     `isCohenMacaulayLocalRing_of_regular_quotient`.
   - If `ℓ ∉ p`: `A_p` equals a further localisation of `A[1/ℓ]_{p}`.
     Apply the `CM localizes` theorem
     (`isCohenMacaulayLocalRing_localization_atPrime`) to a known-CM
     localisation.

5. **Base case**: `dim A = 0` → A_{𝒜₊} is Artinian local, every prime
   equals 𝒜₊, hence `A_p = A_{𝒜₊}` is CM by hypothesis. (~20 LOC)

**Total Route B estimate: ~250 LOC**, matching the survey's upper bound.

## Summary

1. **What "dormant" meant**: not being worked on. The sorry IS
   load-bearing — closing it makes Prop 1.6 fully axiom-clean.
2. **To fully formalise Prop 1.6**: close `caseC_CM_transfer`.
3. **Recommended next step**: pursue **Route B** (generic linear form
   induction, ~250 LOC, spread over 2–3 sessions).
4. **Backup**: if Route B stalls at the "ℓ ∉ p" case, fall back to
   Route A (BH 2.1.27, ~800 LOC) which is more classical but heavier.
5. **Do not**: start Route A before Route B has been given at least
   one session of attempted implementation.

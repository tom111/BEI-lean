# Handoff: Session A′.2 — reduced-HH CM inductive case

## Current problem

The F2 route's final chain needs a bridge theorem (Session A′.2) which
the previous subagent dispatch failed to close. Summary of what went wrong:

- The previous agent estimated the step at 400–700 LOC and stopped
  after landing only the r = 0 base case (~130 LOC), citing uncertainty
  around the localisation-quotient commutation lemma (Step 3 of the
  4-step bridge).
- On a follow-up dispatch attempt with the same 4-step plan, the agent
  was visibly going in circles — not using the lean-lsp MCP tools
  (`lean_leansearch`, `lean_loogle`, `lean_diagnostic_messages`) to
  locate the right Mathlib names, and was slow.
- We aborted that dispatch. This document hands off to a fresh agent
  with cleared context.

## What is already landed (commits)

All the following are committed on `master`. The project builds with
exactly 3 sorries: one target at `BEI/Equidim.lean:6786`, two dormant
in `toMathlib/HeightAdditivity.lean`.

- `302a55c` — L7 replacement: `isCohenMacaulayRing_tensor_away` in
  `toMathlib/CohenMacaulay/TensorPolynomialAway.lean`.
- `a1a8d26`, `7499999` — L4 `L4Iso` (surviving-graph decomposition):
  `BEI/ReducedHH.lean` + `BEI/Equidim.lean`.
- `30860bb` — L1 `L1Iso` (monomial-localisation iso): `BEI/Equidim.lean`.
- `6c47f83` — **Session A′.1**: `augIdealReduced` definition in
  `BEI/ReducedHH.lean`, + r = 0 base case
  `isCohenMacaulayLocalRing_at_augIdealReduced_base` in
  `BEI/Equidim.lean`.

## What is needed (Session A′.2)

Prove

```
private theorem isCohenMacaulayLocalRing_at_augIdealReduced
    {r : ℕ} {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (augIdealReduced (K := K) G))
```

handling both `r = 0` (via the existing
`isCohenMacaulayLocalRing_at_augIdealReduced_base` — just do a `by_cases
hr : r = 0`) and `r ≥ 1` (the real work).

Location: `BEI/Equidim.lean`, after the existing base-case declaration
and before the main theorem at line 6786.

## Strategy for r ≥ 1 (4-step bridge)

Existing L5 (`isCohenMacaulayLocalRing_reducedHH_at_augIdeal`, in
`BEI/Equidim.lean:3882`) takes `n : ℕ` with `hn : 2 ≤ n`, `G :
SimpleGraph (Fin n)`, `hHH : HerzogHibiConditions n G`, and delivers:

    IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ)

with
- `Rp := Localization.AtPrime (augIdeal G)` (full HH quotient)
- `xL := algebraMap _ Rp (mkI (X (Sum.inl ⟨n-1, _⟩)))`
- `yL := algebraMap _ Rp (mkI (X (Sum.inr ⟨n-1, _⟩)))`
- `RpQ := Rp ⧸ Ideal.span {xL}`
- `mkyL := Ideal.Quotient.mk _ yL`

Apply L5 with `n := r + 1`, `hn := by omega`. Bridge the output to
`Localization.AtPrime (augIdealReduced G) (reducedHHRing G)` in 4 steps:

1. **Step 1 (free)**: `QuotSMulTop mkyL RpQ ≃+* RpQ ⧸ Ideal.span {mkyL}`
   via `quotSMulTopRingEquivIdealQuotient` (already in the file; search
   for the name).

2. **Step 2**: `RpQ ⧸ span {mkyL} ≃+* Rp ⧸ (span{xL} ⊔ span{yL}) = Rp ⧸ span {xL, yL}`.
   Use `DoubleQuot.quotQuotEquivQuotSup` or an equivalent from Mathlib.
   Expected ~30–60 LOC of ideal manipulation.

3. **Step 3** (the hard step): `Rp ⧸ span {xL, yL} ≃+* (R_G ⧸ span {mkI X(inl r), mkI X(inr r)})_{augIdeal image}`.
   This is the **localisation-quotient commutation**.

   Concretely: if `p : Ideal R` is prime, `J : Ideal R`, and `J ⊆ p`
   (so `p.map (Ideal.Quotient.mk J)` is still proper and prime in
   `R ⧸ J`), then

       (Localization.AtPrime p R) ⧸ (J.map (algebraMap R _))
         ≃+* Localization.AtPrime (p.map (Ideal.Quotient.mk J)) (R ⧸ J).

   In our case: `R = R_G`, `p = augIdeal G`, `J = span {mkI X(inl r),
   mkI X(inr r)}`. The containment `J ⊆ p` holds because variable
   images are in the augmentation ideal (see the existing
   `mkI_X_mem_augIdeal`).

   **SCOUT THIS LEMMA FIRST**. Use the lean-lsp MCP tools:
   - `lean_leansearch` with queries like:
     - `"IsLocalization quotient commute"`
     - `"Localization.AtPrime quotient ring ideal equiv"`
     - `"ideal quotient localization ringEquiv"`
   - `lean_loogle` with type patterns like:
     - `Localization.AtPrime _ ⧸ _ ≃+* Localization.AtPrime _ (_ ⧸ _)`
     - `IsLocalization.AtPrime _ ⧸ _`
   - Check module `Mathlib.RingTheory.Localization.Ideal` and
     `Mathlib.RingTheory.Localization.AtPrime.*`.
   - If Mathlib has it under a clean name, the whole step is ~20 LOC.
   - If not, build it by hand from `IsLocalization.liftRingHom` +
     `Ideal.Quotient.lift` + bijectivity. Budget ~100–200 LOC.

4. **Step 4**: `R_G ⧸ span {mkI X(inl r), mkI X(inr r)} ≃+* reducedHHRing G`
   as a `K`-algebra iso. The **no-last-pair** fact.

   Forward: `aeval` on variables of `MvPolynomial (BinomialEdgeVars
   (Fin (r + 1))) K` with
   - `Sum.inl i ↦ mk_reduced (X (Sum.inl i'))` where `i' : Fin r` is
     the `Fin r`-index for `i < r`, and `0` for `i = r`.
   - Similar for `Sum.inr i`.

   Well-definedness: every generator `X i * X j` of the full HH ideal
   has `i ≤ j, j.val + 1 < r + 1`, so `j.val < r`, hence `i.val < r`.
   Both map to products of reduced generators, which lie in
   `reducedHHIdeal`. Need to check generator-for-generator.

   Inverse: `aeval` on reduced variables into the full quotient, via
   the embedding `Fin r ↪ Fin (r + 1)` by castSucc. Well-defined because
   reduced generators come from actual full-HH edges.

   Quotient descent, then ideal identification `Ideal.map φ (augIdeal G) =
   augIdealReduced G` (prove by showing containment both ways on
   generators).

   Expected ~150–250 LOC. This step is analogous to L4's
   forward+backward+bijectivity and can reuse the `L4*` patterns.

5. **Assemble**: compose Steps 1–4 into a single `RingEquiv` and apply
   `isCohenMacaulayLocalRing_of_ringEquiv'` (in
   `toMathlib/CohenMacaulay/Polynomial.lean:70`) with the existing L5
   as the CM hypothesis. ~30–50 LOC.

**Total budget**: ~300–550 LOC depending on Step 3.

## Constraints for the fresh agent

1. **USE THE MCP TOOLS** — `lean_leansearch`, `lean_loogle`,
   `lean_diagnostic_messages` — at every step. Do NOT try to recall
   Mathlib names from training.
2. **Scope small**: if a single step balloons past 250 LOC or hits a
   Mathlib-API uncertainty that doesn't resolve in 5 minutes, stop
   and report rather than grind.
3. **Break each step into a named private lemma** before composing.
   This makes diagnosis easier on failure.
4. **Zero new sorries**. Build must pass with `lake build`.
5. `set_option maxHeartbeats 400000` is fine where needed; NOT
   `set_option backward.isDefEq.respectTransparency false`.
6. Work entirely within `BEI/Equidim.lean` and `BEI/ReducedHH.lean`.
   Avoid touching `toMathlib/` unless Step 3's commutation lemma truly
   doesn't exist in Mathlib and needs to be a new reusable helper.

## Pre-scouted Mathlib candidates (verify each)

Found during earlier scouting; verify with `lean_hover_info` before using:

- `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` (for
  localisation-of-localisation, already used elsewhere in the repo).
- `DoubleQuot.quotQuotEquivQuotSup` (Step 2).
- `Ideal.Quotient.algEquivOfEq`, `quotientEquivAlgOfEq` (for minor
  ideal-rewriting).
- `MvPolynomial.algHom_ext`, `Ideal.Quotient.algHom_ext` (extensionality
  for descended ring homs).

For Step 3, names to try or verify existence of:
- `IsLocalization.quotientEquiv` / `Ideal.localizationQuotient` — may
  or may not exist under these exact names.
- `Localization.AtPrime.quotientAtPrime` — speculative.

## Deliverable

Report:
1. Whether `isCohenMacaulayLocalRing_at_augIdealReduced` is fully
   proved.
2. Total LOC added and line range in `BEI/Equidim.lean`.
3. How Step 3 resolved: Mathlib lemma name OR hand-built bridge (with
   LOC).
4. `lean_verify` axiom list for the exported theorem (expected:
   propext / Classical.choice / Quot.sound only).
5. Any genuine surprises or Mathlib API shape discoveries that the
   rest of the project should know about.

Do not commit. The human driver will commit after review.

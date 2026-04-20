# Handoff: Session C3 — close the last `p ⊄ m⁺` sorry

## Current problem

This is the **final session** to close the only sorry on the critical
path of Proposition 1.6. The F2 chain has landed all support pieces
(L1–L7, Session A′, Session B, Sessions C1, C2, C3a-inl). Only two
deliverables remain: a symmetric companion lemma (C3a-inr) and the
final assembly (C3b) that wires everything into the existing
`p ⊄ m` branch.

A previous attempt at C3b died on a 500 API error mid-write after
~400 LOC of broken edits; that state was reverted. A separate earlier
attempt aborted at the same step, citing budget overflow on the
contraction-arithmetic step. Both attempts identified that **C3a
forward-trace lemmas (one per `Sum.inl`/`Sum.inr` branch) are the
right factoring** to shrink C3b into something tractable.

## What is already landed (commits, all on `master`)

The project builds; the only sorry on the critical path is at
`BEI/Equidim.lean:6787`. Two dormant sorries in
`toMathlib/HeightAdditivity.lean` and a few archived ones in
`Supplement/RauhApproach.lean` are off-path.

Recent landed commits (newest first):

- `45c6870` — **Session C3a (inl)**: forward trace
  `E_U_algebraMap_mkI_X_pairedSurvivor_inl` (`BEI/Equidim.lean`,
  ~lines 8063–8166).
- `62b0247` — **Session C2**: tensor-left-localisation bridge in
  `toMathlib/TensorLocalisation.lean` (`Algebra.tensorLeftLocalisationEquiv`,
  `Algebra.TensorLeftLocalisation.tensorLeftLocalisedPrime` +
  `_isPrime`).
- `a7f9982` — **Session C1**: bundled monomial-localisation equiv
  `E_U` (`BEI/Equidim.lean`, ~lines 7994–8039). Specialised to
  `K : Type` (universe 0).
- `b0f95f9` — **Session B**: global CM of
  `Localization.AtPrime (augIdealReduced G')` via
  `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`.
- `9067040` — **Session A′.2**: inductive bridge
  `isCohenMacaulayLocalRing_at_augIdealReduced` (closes the L5 form
  mismatch).

All exports have axioms `{propext, Classical.choice, Quot.sound}`.

## What is needed

### Task A — `E_U_algebraMap_mkI_X_pairedSurvivor_inr` (~80–130 LOC)

Symmetric companion to the existing `_inl` lemma at line ~8063. Same
shape, just swap `Sum.inl ↔ Sum.inr` throughout. The L4 helper to
search for is `L4ForwardInr_of_paired` (or similar — use
`lean_local_search L4ForwardInr`). Statement (template):

```lean
private theorem E_U_algebraMap_mkI_X_pairedSurvivor_inr
    {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : Fin (pairedCount G (U : Set _))) :
    (E_U hHH U hU) (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr (pairedSurvivorsVal G (U : Set _) a))))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
        (smallerHHGraph G (U : Set _)))) (X (Sum.inr a)))
          ⊗ₜ[K] (1 : Localization.Away
            (rename Sum.inr (hhUnitProductSub (K := K) U)))
```

Land Task A as its own commit before attempting Task B. This isolates
the (mechanical) symmetry from the (delicate) assembly.

### Task B — close the sorry at `BEI/Equidim.lean:6787` (~80–130 LOC)

Inside the `p ⊄ m` branch of
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`. The
proof outline (each step has an existing API anchor — verify with
`lean_hover_info` / `lean_loogle` before using):

1. **Pick `U`**:
   `let U : Finset (BinomialEdgeVars (Fin n)) :=
       Finset.univ.filter (fun v => (Ideal.Quotient.mk I (X v) : R) ∉ p)`.
2. **Prove `hU : hhIndep G (↑U)`** by primality of `p`: an HH edge
   monomial `X u · X v` is in `I`, so `mkI(Xu)·mkI(Xv) = 0 ∈ p`,
   contradicting `Xu, Xv ∉ p`.
3. **Prove `hsU : mkI (hhUnitProduct U) ∉ p`** by
   `Ideal.IsPrime.prod_mem_iff` plus `U`'s defining filter.
4. **Loc-of-loc** (mirror of the `p ≤ m` branch): set
   `Lsu := Localization.Away (mkI (hhUnitProduct U))`, build
   `p_Lsu := Ideal.map (algebraMap R Lsu) p` (prime by
   `IsLocalization.isPrime_of_isPrime_disjoint`), and use
   `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` to get
   `Localization.AtPrime p ≃+* Localization.AtPrime p_Lsu` (apply `.symm`
   as needed).
5. **Push `p_Lsu` through `E_U`**: define
   `𝔓 := Ideal.map (E_U hHH U hU).toRingHom p_Lsu`
   in `reducedHHRing G' ⊗[K] Lnew` where
   `Lnew := Localization.Away (rename Sum.inr (hhUnitProductSub U))`.
   Primality of `𝔓` follows from the `RingEquiv` being bijective
   (`Ideal.map_isPrime_of_equiv` or similar — scout).
   Get `Localization.AtPrime p_Lsu ≃+* Localization.AtPrime 𝔓`
   from `E_U` via `Localization.localRingHom` or
   `IsLocalization.algEquiv` lifted from the equiv.
6. **Contraction equality** `𝔓.comap includeLeft = augIdealReduced G'`:
   - `⊆`: by `Ideal.IsMaximal.eq_of_le` plus `properness` (since `𝔓`
     is prime, the contraction is proper).
   - For `augIdealReduced ⊆ contraction`: by `Ideal.span_le` over the
     generators of `augIdealReduced` (which are the `mkI_red(X v)` for
     `v` ranging over `BinomialEdgeVars (Fin (pairedCount + 1))`). For
     each such generator, split `Sum.inl a` / `Sum.inr a` and apply
     **C3a-inl** / **C3a-inr** (Task A). Each lemma says
     `E_U (algebraMap R Lsu (mkI(X(Sum.inX (pairedSurvivorsVal a))))) =
       mkI_red(X(Sum.inX a)) ⊗ₜ 1`, and the LHS argument is in
     `p_Lsu` because `pairedSurvivorsVal G ↑U a ∈ hhSurvivors` ⇒
     `∉ U` ⇒ `mkI(X …) ∈ p`.
7. **Apply C2 bridge** with `m := augIdealReduced G'` and `𝔓` from
   step 5 plus the comap witness from step 6:
    `Localization.AtPrime 𝔓 ≃+* Localization.AtPrime 𝔓'`
   where `𝔓' := Algebra.TensorLeftLocalisation.tensorLeftLocalisedPrime K m 𝔓`.
8. **L7 to globally CM the tensor**: `isCohenMacaulayRing_tensor_away`
   applied to `A := Localization.AtPrime (augIdealReduced G')` (CM
   global by Session B) and the polynomial inside `Lnew`'s
   `Localization.Away` gives
    `IsCohenMacaulayRing ((Localization.AtPrime (augIdealReduced G')) ⊗[K] Lnew)`.
9. **Localise at 𝔓'**:
   `isCohenMacaulayLocalRing_localization_atPrime 𝔓'` (or the
   equivalent named lemma — search `lean_local_search`).
10. **Transport back** via `isCohenMacaulayLocalRing_of_ringEquiv'`
    composed with the inverses of steps 4, 5, 7. Yields
    `IsCohenMacaulayLocalRing (Localization.AtPrime p)`.

### Imports to add at the top of `BEI/Equidim.lean`

```lean
import toMathlib.CohenMacaulay.TensorPolynomialAway
import toMathlib.TensorLocalisation
```

**Watch for re-export collisions** with the file's existing `private`
copies of `isCohenMacaulayLocalRing_of_ringEquiv'`,
`isWeaklyRegular_map_ringEquiv`, `ringEquiv_isLocalHom` (around
lines 3777–3806). The previous attempt found these collide with the
public versions transitively re-exported from
`toMathlib/CohenMacaulay/Polynomial.lean`. Either:

- **Option A (preferred)**: delete the local `private` versions and
  update the 7 call sites (`grep -n isCohenMacaulayLocalRing_of_ringEquiv'`
  in `BEI/Equidim.lean`) to use the public form. Public signature is
  the same; the only change is removing `private` and the `' ` prime.
- **Option B**: rename the local `private` versions to
  `BEI_isCohenMacaulayLocalRing_of_ringEquiv'` etc. and update the
  same 7 call sites. Less invasive.

### Universe restriction

`E_U` is specialised to `K : Type` (universe 0) because of
`polynomialAwayTensorEquiv`'s universe constraint. The current
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` is
declared at `K' : Type*`. Either:

- restrict the **theorem** to `K : Type` (downstream callers all use
  universe 0 — verify with `grep -rn isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`); or
- keep the outer `K' : Type*` and add a `letI` cast inside the `p ⊄ m`
  branch (likely to fail elaboration; not recommended).

The first option is cleaner.

## Constraints for the fresh agent

1. **USE THE MCP TOOLS** — `lean_leansearch`, `lean_loogle`,
   `lean_diagnostic_messages`, `lean_multi_attempt`, `lean_hover_info`,
   `lean_verify` — at every step. Do NOT recall Mathlib names from
   training.
2. **Land Task A as its own commit before starting Task B.** Do not
   bundle them. If Task B blocks, Task A is still progress.
3. **Scope small**: if a single sub-step balloons past 100 LOC of
   fiddly manipulation, stop and either factor the sub-step into a
   private helper lemma or report the blocker.
4. **Zero new sorries.** `lake build` must pass at every committed
   state.
5. `set_option maxHeartbeats 800000` (file-local) is already in use
   for the C3a-inl lemma; reuse the same setting for C3a-inr if
   needed. NOT `set_option backward.isDefEq.respectTransparency false`.
6. Work entirely within `BEI/Equidim.lean`. Do NOT touch
   `toMathlib/`. The C2 bridge's API surface
   (`Algebra.tensorLeftLocalisationEquiv`, `tensorLeftLocalisedPrime`,
   `tensorLeftLocalisedPrime_isPrime`) is fixed.
7. **Commit after each task lands cleanly.** Do not let the working
   tree accumulate broken state across multiple tasks.

## Pre-scouted Mathlib candidates

Verify each with `lean_hover_info` before using:

- `IsLocalization.isPrime_of_isPrime_disjoint` — for primality of `p_Lsu`.
- `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` —
  the two-step localisation bridge (used in step 4 and consumed by C2 internally).
- `IsLocalization.algEquiv` — to lift a ring equiv between two
  localisations at the same submonoid.
- `Localization.localRingHom` — alternative for transporting between
  localisations across a ring hom respecting prime-ideal structure.
- `Ideal.IsMaximal.eq_of_le` (or direct
  `(IsLocalRing.isMaximal_iff _).mp …`) — to upgrade `⊆` plus
  properness to equality (step 6).
- `Ideal.span_le` — for `augIdealReduced ⊆ contraction` via
  generators (step 6).
- `Ideal.IsPrime.prod_mem_iff` — for step 3.
- `Algebra.TensorProduct.includeLeft` — left inclusion `A → A ⊗[K] B`,
  needed for C2 hypothesis.

## Deliverable

Report (≤ 500 words):

1. Whether the sorry at `BEI/Equidim.lean:6787` is fully closed.
2. Total LOC added, split Task A vs Task B.
3. How step 6 (contraction equality) and step 10 (transport) resolved
   in practice (Mathlib lemma names or inline construction).
4. Final `lean_verify` axiom list for
   `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
   (expected: `{propext, Classical.choice, Quot.sound}`).
5. Final sorry inventory across the repo.
6. Any genuine Mathlib API surprises that the rest of the project
   should know about.

If Task B blocks on a specific sub-step despite landing Task A: name
the exact sub-goal, the closest Mathlib API candidates you tried, and
why they didn't fit.

Do not commit Task B if it doesn't fully close the sorry. The human
driver will commit after review.

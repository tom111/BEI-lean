# Next-Session Prompt: Close Proposition 1.6 via finite-free Case C route

## Mission

Make `proposition_1_6` in `BEI/Proposition1_6.lean` fully axiom-clean
(`{propext, Classical.choice, Quot.sound}`, no `sorryAx`). The sole
remaining blocker is `caseC_CM_transfer` in `toMathlib/GradedCM.lean:349`,
which will be closed by assembling the finite-free parameter-subring
chain A→B→C→D (strategy in
`guides/answers/ANSWER_CASE_C_FINITE_FREE_ROUTE.md`).

## What is already proved (all axiom-clean)

| Step | Theorem | File |
|------|---------|------|
| Phase 1 / BH 1.5.6 | `GradedAssociatedPrime.isAssociatedPrime_isHomogeneous` | `toMathlib/GradedAssociatedPrime.lean` |
| B1 | `GradedFiniteFree.mul_left_injective_of_notMem_irrelevant` | `toMathlib/GradedFiniteFree.lean` |
| B2a | `GradedFiniteFree.irrelevant_isNilpotent_of_isArtinianRing_atIrrelevant` | same |
| B2b | `GradedFiniteFree.finite_over_K_of_isArtinianRing_atIrrelevant` | same |
| D (Flat) | `GradedFiniteFree.isCohenMacaulayRing_of_module_flat_of_mvPolynomial` | same |
| D (Free) | `GradedFiniteFree.isCohenMacaulayRing_of_module_free_of_mvPolynomial` | same (thin wrapper) |
| A (single-step) | `GradedRegularSop.exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos` | `toMathlib/GradedRegularSop.lean` |

Phase 1 + Steps B1/B2/D of Phase 2 are fully closed. Step A partial
(single-step descent) is closed; iteration to length d is still pending.

## The four-step chain (mathematical outline)

```
A_𝒜₊ CM local   ⟹   ∃ homog regular sop θ of length d = dim A_𝒜₊  [Step A iterated]
                ⟹   A/(θ) is finite-dim K-vector space              [Step B2 applied]
                ⟹   A finite free over K[T_1, …, T_d] via T_i ↦ θ_i [Step C]
                ⟹   A globally CM                                   [Step D]
```

For BEI downstream: `A = DefRing n K ⧸ tildeJ G` is a f.g. K-algebra so
`Algebra.FiniteType K A` holds trivially (quotient of `MvPolynomial`);
supply this instance at the assembly site.

## What remains

### Task 1 — Full Step A (iterated descent)

**Goal**: given `A` connected ℕ-graded Noetherian `K`-algebra of f.t.
with `A_𝒜₊` CM local, produce `θ : List A` of length `dim A_𝒜₊` forming
a homogeneous A-regular sequence in `𝒜₊`, with the further property
that the localization of `A/(θ)` at the image of `𝒜₊` is Artinian
local.

**Strategy**: strong induction on `d := ringKrullDim (Localization.AtPrime 𝒜₊)`
(finite because Noetherian). Each step invokes the already-proved
single-step descent
`GradedRegularSop.exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos`,
pulls back the IH result from the quotient `A/⟨ℓ⟩`, and prepends `ℓ`.

**Known subtleties**:
- Recursion must quantify over **varying rings** — state as
  `∀ d : ℕ, ∀ {A : Type u} [hypotheses], …`, then `induction d`.
  Inductive hypothesis will be `∀ A' …`, usable on the quotient.
- Lifting the IH output (a list in `A/⟨ℓ⟩`) back to elements of `A`:
  iterate `Quotient.Quotient.mk`-lifting on each list element, pick
  arbitrary lift (homogeneity is preserved since each element of
  the quotient's graded piece `gradedQuotientPiece 𝒜 ⟨ℓ⟩ i` is by
  definition the image of an element of `𝒜 i`).
- Showing the lifted sequence is A-regular: use that an element is
  A-regular on `A` iff its image is regular on `A/(previous
  elements)` iff it's regular on the further quotient, by identifying
  quotient rings.
- Final quotient ≅ quotient-of-quotient: `A/(ℓ, lifted-tail) ≅
  (A/⟨ℓ⟩)/(tail)` — use `DoubleQuot.quotQuotEquivQuotSup` or similar.
- Dimension drops by exactly 1 at each step — use
  `isCohenMacaulayLocalRing_of_regular_quotient` variant from
  `toMathlib/CohenMacaulay/Basic.lean`, combined with a dim-formula
  lemma (may need to prove: `dim(R/xR) + 1 = dim R` for NZD `x` in
  max ideal of CM local).

**Estimated size**: 200–300 LOC.

### Task 2 — Step C (graded finite-free over polynomial subring)

**Goal**: given homogeneous A-regular sop `θ_1, …, θ_d ∈ 𝒜₊` with
`A/(θ)` finite-dim over K, produce `Algebra P A` (with `T_i ↦ θ_i`),
`Module.Free P A`, and `Module.Finite P A`, where `P := MvPolynomial (Fin d) K`.

**Strategy** (from `project_step_c_scope.md` memory — split into 5
sub-lemmas):

1. **C.a** — already in Mathlib: `Ideal.homogeneous_span` gives
   `(Ideal.span (Set.range θ)).IsHomogeneous 𝒜` once elements are
   homogeneous.
2. **C.b** — new: homogeneous K-basis of `A/(θ)` assembled from bases
   of each graded piece. Requires iterating `Basis.ofVectorSpace` over
   the finite support of `decompose 𝒜' (A/(θ))`. Wire via
   `DirectSum.Decomposition.basis` or similar. ~80 LOC.
3. **C.c** — new: surjectivity of `Φ : P^r → A`,
   `Φ(f_1, …, f_r) := ∑ aeval θ f_i · b_i`. Proof by strong degree
   induction on homogeneous `a`: reduce mod `(θ)`, take combination
   of `b_i`, remainder in `(θ)` decomposes into strictly
   smaller-degree terms. ~80 LOC.
4. **C.d** — new: injectivity by induction on `d`. Reduce a relation
   mod `θ_1`; by IH over `K[T_2, …, T_d]` coefficients are divisible
   by `T_1`; divide (using `θ_1` is NZD — part of our hypothesis);
   iterate. Infinite `T_1`-divisibility in `MvPolynomial`
   forces zero (need a small helper:
   `MvPolynomial.X_not_infinitely_divides`). ~100 LOC.
5. **C.e** — assemble into a single theorem producing the algebra
   instance + `Module.Free` + `Module.Finite`, OR alternatively,
   package as: "there exists an `AlgHom (MvPolynomial (Fin d) K) A`
   whose domain module structure makes A finite free" — match Step
   D's expected typeclass pattern (see "Signature note" below). ~40 LOC.

**Signature note**: Step D takes `[Algebra P A] [Module.Flat P A]
[Module.Finite P A]` as typeclass instances. Step C's output must
install these instances at the caller. The cleanest pattern: make
Step C produce an `Algebra P A` instance via `letI` + `inferInstance`
at the call site, rather than trying to bundle through `∃`.

**Estimated total size**: 350–500 LOC. Split into the five sub-lemmas;
dispatch each as its own focused subagent task (each ≤ 250 LOC).

### Task 3 — Assembly

Once Tasks 1 and 2 are done, replace the sorry at
`toMathlib/GradedCM.lean:349` (`caseC_CM_transfer`) by a direct proof
of `IsCohenMacaulayRing A`. Concretely:

1. In `toMathlib/GradedFiniteFree.lean`, add:
```lean
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree
    [Algebra.FiniteType K A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    IsCohenMacaulayRing A := by
  -- Step A: get homogeneous regular sop θ of length d.
  obtain ⟨d, θ, hθ_hom, hθ_irr, hθ_reg, hArt_quot⟩ := ???
  -- Step B2b applied to A/(θ): finite-dim over K.
  haveI : Module.Finite K (A ⧸ Ideal.ofList θ) := ???
  -- Step C: obtain finite free structure over MvPolynomial.
  haveI : Algebra (MvPolynomial (Fin d) K) A := ???
  haveI : Module.Finite (MvPolynomial (Fin d) K) A := ???
  haveI : Module.Free (MvPolynomial (Fin d) K) A := ???
  -- Step D: conclude globally CM.
  exact isCohenMacaulayRing_of_module_free_of_mvPolynomial
```

2. In `toMathlib/GradedCM.lean:349`, derive `caseC_CM_transfer` from the
   new theorem. Specifically: given its hypotheses, the existing Case
   A/B split supplies CM at `p_star`. The new theorem supplies
   `IsCohenMacaulayRing A`, from which `CM_localize p (hp_prime)` gives
   CM at `p`.

3. Verify `proposition_1_6` has axioms `{propext, Classical.choice, Quot.sound}`.

4. Propagate: `tildeJ_quotient_isCohenMacaulay` and
   `groebnerDeformation_cm_transfer` should become axiom-clean.

### Task 4 — BEI downstream verification

Check that `DefRing n K ⧸ tildeJ G` satisfies `[Algebra.FiniteType K _]`
trivially (quotient of `MvPolynomial (...) K`). Supply this instance at
the call site of the new theorem (not automatic due to universe / quotient
bookkeeping).

## Existing infrastructure (reusable)

- `toMathlib/GradedAssociatedPrime.lean` — BH 1.5.6.
- `toMathlib/GradedPrimeAvoidance.lean` — graded avoidance,
  `isCohenMacaulayLocalRing_atPrime_of_le_irrelevant`,
  `exists_homogeneous_nonZeroDivisor_of_isCohenMacaulay_dim_pos`,
  `isCohenMacaulayLocalRing_of_quotient_cm_of_mem`,
  `connectedGraded_quotient`, `isHomogeneous_span_singleton_of_homogeneous`.
- `toMathlib/GradedQuotient.lean` — `gradedQuotientPiece`, `gradedRing`.
- `toMathlib/GradedIrrelevant.lean` — `ConnectedGraded`, `irrelevant_isMaximal`.
- `toMathlib/GradedFiniteFree.lean` — B1, B2a, B2b, D-Flat, D-Free.
- `toMathlib/GradedRegularSop.lean` — Step A single-step.
- `toMathlib/CohenMacaulay/Basic.lean` — `isCohenMacaulayLocalRing_of_regular_quotient`,
  `isCohenMacaulayRing_quotient_of_smulRegular`.
- `toMathlib/CohenMacaulay/Polynomial.lean` —
  `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing`,
  `isCohenMacaulayRing_mvPolynomial_field`,
  `quotSMulTopLocalizationEquiv_of_mem`.
- `toMathlib/CohenMacaulay/Localization.lean` — CM localizes,
  `exists_weaklyRegular_in_prime` (PUBLIC as of 2026-04-21).

## Tactics / discipline

- **MCP lean-lsp tools may be intermittently unavailable.** If they
  disconnect, fall back to `lake build toMathlib.X` cycles.
- `classical` + `attribute [local instance] Classical.propDecidable` is
  the idiomatic pattern for DFinsupp bookkeeping in graded modules.
- For typeclass-heavy hypotheses (`haveI := (...irrelevant_isMaximal
  𝒜 h𝒜₀).isPrime; ...`), match the existing style in `GradedCM.lean`
  and `GradedPrimeAvoidance.lean`.
- **Dispatch subagents** for any sub-lemma > 150 LOC. Give each a
  tight spec with bail-out criteria. Do NOT run more than one agent
  per file at a time (they'll conflict on writes).
- Axiom-check each new theorem with
  `#print axioms MyNS.myTheorem`, targeting
  `{propext, Classical.choice, Quot.sound}`.
- Commit secured progress in small, honest commits. Do NOT bundle
  broken proof attempts or stale updates.

## Priority order for the session

1. Task 1 (full Step A iteration) — **start here**, ~200-300 LOC. The
   single-step foundation exists; this is mostly Lean bookkeeping over
   varying rings. Dispatch a focused subagent.
2. Task 2 (Step C) — **this is the session's real workload**. Split
   into the 5 sub-lemmas (C.a is already in Mathlib). Dispatch each
   as a separate subagent with ≤ 250 LOC budget.
3. Task 3 (Assembly) — once Tasks 1 and 2 compile. ~50 LOC.
4. Task 4 (BEI downstream) — ~20 LOC, verify axiom-cleanness of
   `proposition_1_6`.

If Task 2's Step C gets bogged down (likely — it's the hard one),
commit partial progress on individual sub-lemmas and resume in a
future session. Each sub-lemma that compiles is a permanent win.

## Status-doc discipline at end of session

Update `TODO.md`, `FORMALIZATION_MAP.md`, and `guides/INDEX.md` once
`proposition_1_6` is axiom-clean (or to reflect additional sub-lemma
progress if not). Delete or refresh this file (`NEXT_SESSION_PROMPT.md`)
to match actual state. Do not push commits unless explicitly
instructed.

## Memory anchors

- `project_bh156_done.md` — BH 1.5.6 and current route progress.
- `project_step_c_scope.md` — Step C split into 5 sub-lemmas.
- `guides/answers/ANSWER_CASE_C_FINITE_FREE_ROUTE.md` — full math
  strategy from the deep-thinking model.
- `guides/work_packages/GRADED_CM_CASE_C_PLAN.md` — broader plan
  context.

## Success criteria

- `caseC_CM_transfer` sorry is replaced by a real proof.
- `lake build` succeeds with no new warnings beyond existing dormant
  sorries in `HeightAdditivity.lean`.
- `#print axioms BEI.Proposition1_6.proposition_1_6` reports
  `{propext, Classical.choice, Quot.sound}` — no `sorryAx`.
- `TODO.md` sorry table updated.

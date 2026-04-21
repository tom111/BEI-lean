# Next-Session Prompt: Close Case C via finite-free parameter subring

## Status (2026-04-21)

**Phase 1 done.** `GradedAssociatedPrime.isAssociatedPrime_isHomogeneous`
(BH 1.5.6) is proved axiom-clean.

**Phase 2 strategy chosen:** finite-free parameter subring route. See
`guides/answers/ANSWER_CASE_C_FINITE_FREE_ROUTE.md` for the full
mathematical plan. Key insight: prime-by-prime induction is the wrong
frame for non-homogeneous primes; instead prove the global structural
property `A` is finite free over `K[T_1, …, T_d]`, and derive global CM
from there.

## Four-step plan

```
A_𝔪 CM   ⟹   P(A)   ⟹   A globally CM
```

where `P(A) := ∃ θ_1, …, θ_d ∈ 𝒜₊ homogeneous regular sop with
A/(θ) finite-dim over K and A finite free over K[T_1, …, T_d]`.

| Step | Lemma | Status |
|------|-------|--------|
| B1 | `mul_left_injective_of_notMem_irrelevant` | **DONE** (axiom-clean) — `toMathlib/GradedFiniteFree.lean` |
| B2a | `irrelevant_isNilpotent_of_isArtinianRing_atIrrelevant` | **DONE** (axiom-clean) |
| B2b | `finite_over_K_of_isArtinianRing_atIrrelevant` | **DONE** (axiom-clean); requires `[Algebra.FiniteType K A]` |
| D | `isCohenMacaulayRing_of_module_free_of_mvPolynomial` | **DONE** (axiom-clean) |
| C | `finiteFree_of_homogeneous_regular_sop` | Dispatched to subagent on `toMathlib/GradedFiniteFree.lean` |
| A (partial) | `exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos` (single-step descent) | **DONE** (axiom-clean) — `toMathlib/GradedRegularSop.lean`. Full iterated version (via varying-ring induction) still pending. |
| Assembly | Replace `caseC_CM_transfer` sorry at `toMathlib/GradedCM.lean:349` | Pending — direct proof of `IsCohenMacaulayRing A` via A→B2b→C→D chain |

## Existing infrastructure to reuse

- `toMathlib/GradedAssociatedPrime.lean` — BH 1.5.6, axiom-clean.
- `toMathlib/GradedPrimeAvoidance.lean` — graded prime avoidance,
  `exists_homogeneous_nonZeroDivisor`,
  `isCohenMacaulayLocalRing_atPrime_of_le_irrelevant`,
  `isCohenMacaulayLocalRing_of_quotient_cm_of_mem`.
- `toMathlib/CohenMacaulay/Basic.lean` — `isCohenMacaulayLocalRing_of_regular_quotient`,
  `isCohenMacaulayRing_quotient_of_smulRegular` (now public).
- `toMathlib/CohenMacaulay/Polynomial.lean` —
  `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing`.
- `toMathlib/CohenMacaulay/Localization.lean` — "CM localizes".

## BEI-specific shortcut

If the Gröbner deformation ring `A = S[t]/Ĩ` already has an explicit
homogeneous regular sop (check `BEI/Equidim.lean` and
`BEI/GroebnerDeformation.lean` for `fullRegSeq` or
`bipartiteEdgeMonomialIdeal_isWeaklyRegular_full`), skip Step A and go
directly to B→C→D with the explicit parameters. This specialization is
substantially lighter than the general theorem.

## Discipline

- All Steps B1/B2/D are done and axiom-clean. Only Steps A, C, and
  assembly remain.
- Each lemma ≤ 250 LOC; dispatch sub-agents for bigger ones.
- Axiom-check each with `#print axioms` before declaring done.
- `classical` + `attribute [local instance] Classical.propDecidable` is
  the pattern for DFinsupp bookkeeping in graded modules.
- Do not bundle speculative cleanup or restructure unrelated files.

## Assembly strategy (when Steps A & C land)

The finite-free route gives `IsCohenMacaulayRing A` **directly** from
`A_{𝒜₊}` CM, avoiding the homogeneous/non-homogeneous case split that
`caseC_CM_transfer` was addressing. Plan:

1. State and prove new theorem in `toMathlib/GradedFiniteFree.lean`:
```lean
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree
    [Algebra.FiniteType K A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : ...) :
    IsCohenMacaulayRing A
```
   by chaining Step A (get regular sop θ) → Step B2b (get A/(θ) finite-dim
   over K) → Step C (get A finite free over `K[T_1,…,T_d]`) → Step D (get
   global CM).

2. Replace `caseC_CM_transfer` sorry by deriving it from the new theorem:
   given the hypotheses of `caseC_CM_transfer`, apply the new theorem to
   get `IsCohenMacaulayRing A`, then extract the prime-p localization via
   `CM_localize`.

3. For BEI downstream (`tildeJ_quotient_isCohenMacaulay`): verify
   `[Algebra.FiniteType K DefRing]` holds (should be trivial since
   `DefRing = MvPolynomial _ K ⧸ Ĩ` is a quotient of f.t. algebra).

4. `#print axioms proposition_1_6` should become
   `{propext, Classical.choice, Quot.sound}` — fully clean.

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
| B1 | `mul_left_injective_of_notMem_irrelevant` | **DONE** (axiom-clean) — `toMathlib/GradedFiniteFree.lean:47` |
| B2a | `irrelevant_isNilpotent_of_isArtinianRing_atIrrelevant` | **DONE** (axiom-clean) — same file, line 154 |
| B2b | `finite_over_K_of_isArtinianRing_atIrrelevant` | **DONE** (axiom-clean) — same file, line 245 |
| C | `finiteFree_over_mvPolynomial_of_homogeneous_regular_sop` | Pending — main new algebra lemma |
| D | `isCohenMacaulayRing_of_finiteFree_over_mvPolynomial` | Pending — flat base change + Artinian ingestion |
| A | `exists_homogeneous_regular_sop_of_cm_at_irrelevant` | Pending — iterate existing tools |
| Assembly | Replace `caseC_CM_transfer` sorry | Pending — final step |

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

- Tackle lemmas in order B1 → B2 → C → D → A → assembly.
- Each lemma ≤ 250 LOC; dispatch sub-agents for bigger ones.
- Axiom-check each with `#print axioms` before declaring done.
- `classical` + `attribute [local instance] Classical.propDecidable` is
  the pattern for DFinsupp bookkeeping in graded modules.
- Do not bundle speculative cleanup or restructure unrelated files.

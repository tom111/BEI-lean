# Next-Session Prompt: Close Case C of graded local-to-global CM

## Status (2026-04-21)

**Phase 1 is done.** BH 1.5.6 / Eisenbud 3.5 —
`GradedAssociatedPrime.isAssociatedPrime_isHomogeneous` in
`toMathlib/GradedAssociatedPrime.lean:418` — is proved axiom-clean
(`{propext, Classical.choice, Quot.sound}`). This gives us
`Ass(A) ⊆ 𝒜₊` for connected ℕ-graded Noetherian `A`.

**Phase 2 is blocked on strategy**, not on formalization tactics. The
naive induction (Option 1a in `ROUTE_B_OBSTACLE_PLAN.md`) has a real
obstacle: quotienting by a non-homogeneous NZD `ℓ' ∈ p ⊄ 𝒜₊` breaks
the invariant "`Ass(B) ⊆ 𝔪`" for `B := A/⟨ℓ'⟩`.

## What to do first

**Read `guides/work_packages/CASE_C_MATH_QUESTION.md`.** This is the
mathematical question sent to a deep-thinking model. Its answer — once
returned — should name a concrete strategy (induction invariant, algebraic
identity, or BEI-specific bypass) that unblocks Phase 2.

If the math model's answer is available in the conversation / a file, work
from that. Otherwise, re-read `ROUTE_B_OBSTACLE_PLAN.md` and
`GRADED_CM_CASE_C_PLAN.md` for the existing sketch.

## Building blocks already proved (as of 2026-04-21)

In `toMathlib/GradedPrimeAvoidance.lean`:
- `exists_homogeneous_notMem_of_forall_not_le` (BH 1.5.10, graded prime
  avoidance).
- `exists_homogeneous_nonZeroDivisor` + `…_isCohenMacaulay_dim_pos`
  combinator.
- `isCohenMacaulayLocalRing_of_quotient_cm_of_mem` (the `ℓ ∈ p`
  descent case).
- `isCohenMacaulayLocalRing_atPrime_of_le_irrelevant` (strengthened
  Case B — covers **all** primes `p ⊆ 𝒜₊`, homogeneous or not).

In `toMathlib/GradedAssociatedPrime.lean`:
- `annihilator_singleton_isHomogeneous_of_homogeneousElem`.
- `annihilator_mul_eq_of_prime_notMem`.
- `isAssociatedPrime_isHomogeneous` (BH 1.5.6, **Phase 1 goal**).

## What's left for Phase 2 (sketch, awaiting math model)

Likely one of:
- **Route A refined (via `*-depth`)**: ~600–800 LOC, classical Bruns–Herzog
  2.1.27 proof using graded-depth/dim identity (BH 1.5.8).
- **Route B refined (better invariant)**: smaller, if such an invariant
  exists.
- **BEI-specific bypass (Route D)**: if there's structural feature of
  `S[t]/Ĩ` that lets us conclude CM globally without the general LTG
  theorem, this is cheapest.

## Files

- **Primary target**: `toMathlib/GradedCM.lean:349` —
  `caseC_CM_transfer` (single remaining sorry on the Prop 1.6 path).
- **Consumer**: `BEI/GroebnerDeformation.lean` —
  `tildeJ_quotient_isCohenMacaulay` currently depends transitively on
  this sorry.
- **Downstream**: `BEI/Proposition1_6.lean` — becomes fully axiom-clean
  once `caseC_CM_transfer` is closed.

## Discipline reminders

- Do **not** expand scope beyond `caseC_CM_transfer` and its direct
  dependencies.
- Once strategy is clear, write a focused work packet (not a running
  commentary) and dispatch sub-agents for individual lemmas ≤ 250 LOC.
- `classical` + `attribute [local instance] Classical.propDecidable` is
  the established pattern for DFinsupp bookkeeping in graded modules.
- Axiom-check every new theorem with `#print axioms` before declaring
  done.

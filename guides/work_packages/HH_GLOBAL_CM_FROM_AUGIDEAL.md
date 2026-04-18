# Guide: HH Global CM from the Augmentation Ideal

## Status: 1 sorry remains — F2 route, final chain and L1/L2/L4/L7 pending

The theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` is
stated in `BEI/Equidim.lean` with a two-case split. The `p ⊆ m⁺` case is
**fully proved**. The `p ⊄ m⁺` case has one remaining sorry, now being
approached via the **F2 route** (see the expert-provided 7-lemma plan).

F2 route: 3 of 7 lemmas fully proved (L3, L5 CM-corollary, L6). Remaining:
L1, L2, L4, L7, plus the final chain assembly.

## F2 route: the seven lemmas

The expert's plan packages the `p ⊄ m⁺` closure as a chain of ring
isomorphisms ending with a tensor-CM base lemma:

  R_p ≅ (A_H^red ⊗_K K[Λ ⊔ U][m_U⁻¹])_Q

where `A_H^red` is a "reduced" HH ring (HH with trailing isolated pair
dropped), `Λ ⊔ U` are free variables, and `m_U = ∏ u, X_u`.

The seven lemmas and their status:

- **L1** (pending). `R[s_U⁻¹] ≅ K[W]/I(Γ_W) ⊗_K L(U)` — monomial localization
  iso. Inverts the unit-variable product, kills neighbors.
- **L2** (pending). `R_p ≅ (K[W]/I(Γ_W) ⊗_K L(U))_P` — localization of L1.
- **L3** **DONE** (`3aeef2a`). One-sided survivors are isolated in `Γ_W`.
  Lemmas `hhSurvivor_x_isolated`, `hhSurvivor_y_isolated` in
  `BEI/Equidim.lean`.
- **L4** (pending). `K[W]/I(Γ_W) ≅ A_H^red ⊗_K K[Λ]` — decompose the
  surviving subgraph via paired-index set `C` and isolated set `Λ`.
  Uses L3.
- **L5** **DONE** (`9f32f99`, `06a8e8f`). Reduced HH at augmentation is CM.
  Lemma `isCohenMacaulayLocalRing_reducedHH_at_augIdeal` in
  `BEI/Equidim.lean`. (CM corollary; full ring iso A_H ≅ A_H^red ⊗ K[s,t]
  not built but not needed.)
- **L6** **DONE** (`1d3a620`). `K[α] ⊗_K K[β][m⁻¹] ≅ K[α ⊔ β][(rename m)⁻¹]`.
  Lemma `polynomialAwayTensorEquiv` in `toMathlib/PolynomialAwayTensor.lean`.
- **L7** (pending — largest risk). Tensor-CM base lemma: for CM local
  K-algebra A and polynomial-ring localization B = K[τ][b⁻¹], the
  localization `(A ⊗_K B)_P` at a prime over m_A is CM. Needs either:
  (a) the flat-local CM criterion (not in Mathlib), or
  (b) generalizing `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing_domain`
      to non-domain CM rings.

## What else is proved (pre-F2 infrastructure)

### Graded contraction section (all proved):

1. `homogeneousComponent_mul_eq_zero_of_low_degrees`.
2. `homogeneousComponent_sum_low_eq`.
3. `mem_of_mul_mem_of_isUnit_constantCoeff` — graded contraction theorem.
4. `bipartiteEdgeMonomialIdeal_isMonomial` — HH ideal is monomial.
5. `isMonomial_homogeneousComponent_mem` — monomial ideals are homogeneous.

### Structural lemmas (all proved):

6. `exists_var_not_mem_of_not_le_augIdeal`.
7. `isUnit_algebraMap_mkI_X`.
8. `algebraMap_mkI_X_eq_zero_of_edge`.
9. `algebraMap_mkI_y_eq_zero_of_x_not_mem` / `..._x_eq_zero_of_y_not_mem`.

### Regular sequence infrastructure (all proved):

10. `fullRegSeq_isWeaklyRegular_localization` (flat base change).
11. `minimalPrime_le_augIdeal`.
12. `isCohenMacaulayLocalRing_at_augIdeal` — CM at augIdeal.

### L5-specific infrastructure (all proved):

13. `lastPair_prefix_isWeaklyRegular_at_augIdeal` — permuted fullRegSeq
    with last pair at the front is weakly regular.
14. `isSMulRegular_X_inl_last_at_augIdeal`, `isSMulRegular_mk_y_last`.
15. `X_inl_last_mem_maximalIdeal`, `X_inr_last_mem_maximalIdeal`.
16. `isCohenMacaulayLocalRing_quot_lastInl` — CM of first quotient
    (QuotSMulTop view).
17. `smul_top_eq_span_singleton` — key bridge identity.
18. `quotSMulTopRingEquivIdealQuotient` — RingEquiv `QuotSMulTop x R ≃+* R ⧸ Ideal.span {x}`.
19. `isCohenMacaulayLocalRing_idealQuot_lastInl` — CM of first quotient
    (Ideal.Quotient view).
20. `isCohenMacaulayLocalRing_reducedHH_at_augIdeal` — L5 CM corollary.

## Non-obvious Lean insights from the L5 session

See `memory/bridge_QuotSMulTop_idealQuotient.md` for two reusable tricks:

1. **Type bridge**: `QuotSMulTop x R` and `R ⧸ Ideal.span {x}` are semantically
   the same ring but not definitionally equal in Lean. Bridge via
   `Submodule.Quotient.equivOfEq` / `Ideal.quotEquivOfEq` applied to
   `smul_top_eq_span_singleton`.
2. **Typeclass heartbeats**: when working across these two quotient views,
   `set_option synthInstance.maxHeartbeats 400000` is needed to synthesize
   the `SMul` and `Membership` instances.

## Execution order for remaining work

1. **L7** first (biggest risk — if unprovable, whole F2 route dies).
   Tensor-CM base lemma. Attempt either:
   - Flat-local CM criterion (Mathlib-scale new infrastructure).
   - Case-specific proof for our A = reduced HH ring localized at aug.
2. **L4** — uses L3 (done) and mirrors L6's complexity.
3. **L1** — monomial localization ring iso.
4. **L2** — localization-of-localization on L1.
5. **Final chain** — compose L1, L2, L4, L5, L6, L7 to close the sorry at
   `BEI/Equidim.lean:isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
   on the `p ⊄ m⁺` branch.

## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localization backport.
- Do not switch to the Gröbner CM transfer yet.
- Do not reopen the `p ≤ augIdeal` branch.
- Do not restart the minimal-prime, graded-induction, dehomogenization, or
  broad parameter-prefix routes.
- Do not build the full L5 ring isomorphism A_H ≅ A_H^red ⊗_K K[s,t] —
  the CM corollary suffices for F2.

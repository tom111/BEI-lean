# Guide: HH Global CM from the Augmentation Ideal

## Status: 1 sorry remains — F2 route, pending L1, L2, L4 (L7 replacement now DONE)

The theorem `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
in `BEI/Equidim.lean` has a two-case split. The `p ⊆ m⁺` case is fully
proved. The `p ⊄ m⁺` case is the remaining sorry, and is approached via
the **F2 decomposition route**, validated by the deep-model answer at
[../answers/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md](../answers/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md).

**Route chosen**: F2 decomposition with a small tensor-polynomial-
localisation CM endpoint replacing the earlier flat-local L7. The
alternative "induct on graph size" (Strategy I) was explicitly rejected:
the natural factor after localisation is a *reduced* HH ring, not a full
one, which makes induction on full HH rings awkward.

## The decomposition

For a prime `p ⊄ m⁺` of `R = S / I`, there is a canonical isomorphism

    R_p  ≅  (A^red_{G', m^red_{G'}}  ⊗_K  K[Λ ⊔ U][s_U⁻¹])_𝔓

where:

- `U` = variables `v` with `v̄ ∉ p` (units in `R_p`; independent in `Γ_G`).
- `N(U)` = vars adjacent in `Γ_G` to something in `U`; these become zero in `R_p`.
- `W = σ \ (U ∪ N(U))` = surviving nonunits.
- `C = { i < n-1 : x_i ∈ W and y_i ∈ W }`, `Λ = W \ {x_i, y_i : i ∈ C}`.
- Every variable in `Λ` is isolated in `Γ_G|_W` (HH transitivity; this is L3).
- `G'` on `{0, …, r}` where `r = |C|`, with `{a, b+1} ∈ E(G') ⟺ {c_a, c_b+1} ∈ E(G)`
  (the canonical smaller HH graph). **G' satisfies HH** (diagonal and transitivity
  both check directly).
- `s_U = ∏_{u ∈ U} u`.
- `A^red_{G'}` = reduced HH ring of `G'` (no trailing isolated pair).

The prime `𝔓` contracts to the augmentation ideal `m^red_{G'}`, because every
variable of `A^red_{G'}` comes from `W ⊆ p`.

See the answer file for the full derivation including the generator-level
formulas for each ring isomorphism and the counterexample verification
(n=4, G=K_4: G' is K_3 on {0, 1, 2}, Λ = ∅, U = {x_2, x_3, y_3}, the HH factor
is `A^red_{K_3}`).

## The six lemmas (F2 worklist)

All six targets come with explicit generator formulas in the answer file.

- **L1** (pending). Monomial localisation iso:

      R[s_U⁻¹]  ≅  (K[W] / I(Γ_G|_W))  ⊗_K  K[U][s_U⁻¹]

  with `v̄ ↦ v̄ ⊗ 1` for `v ∈ W`, `0` for `v ∈ N(U)`, `1 ⊗ v` for `v ∈ U`.
  Well-definedness: check every original edge, using that `U` is independent.

- **L2** (pending). Localising L1 at `p` (formal localisation-of-localisation,
  using `s_U ∉ p`):

      R_p  ≅  ((K[W] / I(Γ_G|_W))  ⊗_K  K[U][s_U⁻¹])_𝔓.

- **L3** — **DONE** (`3aeef2a`). One-sided survivors in `W` are isolated in
  `Γ_G|_W`. Formalised as `hhSurvivor_x_isolated`, `hhSurvivor_y_isolated`
  in `BEI/Equidim.lean`.

- **L4** (pending). Surviving-graph decomposition:

      K[W] / I(Γ_G|_W)  ≅  A^red_{G'}  ⊗_K  K[Λ]

  with `x̄_{c_a} ↦ x̄'_a ⊗ 1`, `ȳ_{c_a} ↦ ȳ'_a ⊗ 1`, `λ̄ ↦ 1 ⊗ λ`.
  Uses L3 (isolation of Λ). The side computation `G' satisfies HH` lives
  alongside this lemma.

- **L5** — **DONE** (`9f32f99`, `06a8e8f`). Reduced HH at augmentation is CM.
  Formalised as `isCohenMacaulayLocalRing_reducedHH_at_augIdeal` in
  `BEI/Equidim.lean`.

- **L6 / L7 replacement** — **DONE** (`302a55c`). Tensor-polynomial-localisation CM:

      isCohenMacaulayRing_tensor_away :
        [CommRing A] [Algebra K A] [IsNoetherianRing A] [IsCohenMacaulayRing A]
          [Finite τ] → (s : MvPolynomial τ K) →
        IsCohenMacaulayRing (TensorProduct K A (Localization.Away s))

  Formalised in `toMathlib/CohenMacaulay/TensorPolynomialAway.lean` (200 LOC,
  0 sorries, propext/Classical.choice/Quot.sound only). The A-algebra iso
  `A ⊗_K K[τ][s⁻¹] ≅ Localization.Away (map s)` is the new `tensorAwayEquiv`,
  mirroring `polynomialAwayTensorEquiv`. The support lemma
  `isCohenMacaulayRing_localization` (localisation of globally CM is globally
  CM) is also exported.

  Application to L7: take `A = A^red_{G', m^red_{G'}}` promoted to a global
  `IsCohenMacaulayRing` via CM-localises on the formalised local CM at the
  augmentation. Take `B = K[Λ ⊔ U][s_U⁻¹]`.

## What is already proved (pre-F2 infrastructure, unchanged)

### Graded contraction section:

1. `homogeneousComponent_mul_eq_zero_of_low_degrees`.
2. `homogeneousComponent_sum_low_eq`.
3. `mem_of_mul_mem_of_isUnit_constantCoeff` — graded contraction theorem.
4. `bipartiteEdgeMonomialIdeal_isMonomial` — HH ideal is monomial.
5. `isMonomial_homogeneousComponent_mem` — monomial ideals are homogeneous.

### Structural lemmas:

6. `exists_var_not_mem_of_not_le_augIdeal`.
7. `isUnit_algebraMap_mkI_X`.
8. `algebraMap_mkI_X_eq_zero_of_edge`.
9. `algebraMap_mkI_y_eq_zero_of_x_not_mem` / `..._x_eq_zero_of_y_not_mem`.

### Regular-sequence infrastructure:

10. `fullRegSeq_isWeaklyRegular_localization` (flat base change).
11. `minimalPrime_le_augIdeal`.
12. `isCohenMacaulayLocalRing_at_augIdeal`.

### L5-specific infrastructure:

13. `lastPair_prefix_isWeaklyRegular_at_augIdeal`.
14. `isSMulRegular_X_inl_last_at_augIdeal`, `isSMulRegular_mk_y_last`.
15. `X_inl_last_mem_maximalIdeal`, `X_inr_last_mem_maximalIdeal`.
16. `isCohenMacaulayLocalRing_quot_lastInl`.
17. `smul_top_eq_span_singleton`.
18. `quotSMulTopRingEquivIdealQuotient`.
19. `isCohenMacaulayLocalRing_idealQuot_lastInl`.
20. `isCohenMacaulayLocalRing_reducedHH_at_augIdeal`.

## Non-obvious Lean insights from the L5 session

See `memory/bridge_QuotSMulTop_idealQuotient.md` for two reusable tricks:

1. **Type bridge**: `QuotSMulTop x R` and `R ⧸ Ideal.span {x}` are
   semantically the same ring but not definitionally equal. Bridge via
   `Submodule.Quotient.equivOfEq` / `Ideal.quotEquivOfEq` applied to
   `smul_top_eq_span_singleton`.
2. **Typeclass heartbeats**: when working across these two quotient
   views, `set_option synthInstance.maxHeartbeats 400000` is needed to
   synthesise the `SMul` and `Membership` instances.

## Execution order for remaining work

1. **L6 / L7 replacement** — DONE (`302a55c`).
2. **L4** — uses L3 (done). Surviving-graph decomposition:
   `K[W] / I(Γ_G|_W) ≅ A^red_{G'} ⊗_K K[Λ]`. Also checks G' satisfies HH.
   The concrete setup in `BEI/Equidim.lean` already has `hhSurvivors`,
   `hhNbhd`, `hhIndep` and the L3 one-sided-isolation lemmas
   `hhSurvivor_x_isolated`, `hhSurvivor_y_isolated`. Still needed:
   define the abstract reduced HH ring `A^red_G` for any HH graph,
   define the canonical smaller-graph construction `G'` from `(G, C)`
   where `C` is the paired-survivor index set, prove G' is HH, then
   construct the ring iso.
3. **L1** — monomial localisation ring iso. Parametrises
   `U ⊆ σ` independent in `Γ_G`, sets `s_U := ∏_{u ∈ U} u`, and gives
   `R[s_U⁻¹] ≅ (K[W] / I(Γ_G|_W)) ⊗_K K[U][s_U⁻¹]`.
4. **L2** — routine localisation-of-localisation on L1 at `p`.
5. **Final chain** — compose L1, L2, L4, L5, L6/L7 replacement to close
   the sorry at
   `BEI/Equidim.lean:isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal`
   on the `p ⊄ m⁺` branch.

## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localisation backport.
- Do not switch to the Gröbner CM transfer yet.
- Do not reopen the `p ≤ augIdeal` branch.
- Do not restart the minimal-prime, graded-induction, dehomogenisation, or
  broad parameter-prefix routes.
- Do not attempt induction on graph size (Strategy I) — the deep-model
  answer explicitly rejects it; the natural factor is reduced HH, not
  full HH, so induction on full HH would be awkward.
- Do not build a full flat-local CM criterion. The new F2 endpoint does
  not need it.
- Do not build the full L5 ring isomorphism `A_H ≅ A^red_H ⊗_K K[s, t]` —
  the CM corollary suffices for F2.

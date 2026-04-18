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
  localization `(A ⊗_K B)_P` at a prime over m_A is CM. Since 2026-04-18
  the non-domain polynomial CM extension is DONE
  (`isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing`, PR #28599
  backport); this does not on its own give L7, since A ⊗_K B localized
  is not quite a polynomial over A, but combined with an A-globally-CM
  step (by induction on graph size, Strategy I in
  `questions/HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md`) it can be closed.
  The remaining risk is the flat-base-change step and the structural
  decomposition, not a polynomial CM extension.

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

## L7 blocker analysis (2026-04-18)

A focused Mathlib survey (see session at 2026-04-18) found:

1. **Flat-local CM criterion is absent** from Mathlib v4.28.0 and from the
   local `toMathlib/CohenMacaulay/` backport. There is no theorem shaped like
   `isCohenMacaulay_of_flat_local`, no depth identity under flat maps, and
   no `isCohenMacaulay_baseChange` / `tensorProduct` lemma.

2. **Ingredients that do exist** (Mathlib): `IsWeaklyRegular.of_flat`,
   `IsWeaklyRegular.of_flat_of_isBaseChange`, `IsRegular.of_faithfullyFlat`,
   `IsSMulRegular.of_flat`. These move regular sequences across flat maps,
   which is one ingredient of a flat-local CM proof, but on their own are
   not the theorem.

3. **The local backport** has `isCohenMacaulayLocalRing_of_regular_quotient`
   (converse transfer), `isCohenMacaulayLocalRing_quotient` (forward transfer),
   and `isCohenMacaulayLocalRing_localization_atPrime`. A flat-local CM
   proof can be built on top, but requires a flat-local dim identity
   `dim R_P = dim A + dim fiber_{P'}` which itself is not in Mathlib.

4. **Polynomial CM extension now available without `IsDomain`**
   (RESOLVED 2026-04-18). The domain-only theorem
   `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing_domain`
   (`toMathlib/CohenMacaulay/Polynomial.lean:1161`) has been complemented
   by the backport of Mathlib PR #28599 ("polynomial over CM ring is CM"):
   - `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing`
     (`toMathlib/CohenMacaulay/Polynomial.lean:1557`)
   - `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing`
     (`toMathlib/CohenMacaulay/Polynomial.lean:1630`)
   Both take only `[IsNoetherianRing R] [IsCohenMacaulayRing R]` — no
   `IsDomain` hypothesis. The reduced HH ring is no longer an obstacle on
   the polynomial-extension side.

5. **"A is a polynomial-ring localization" shortcut does not apply.**
   If `A` in L7 were itself a localization of `K[α]` at a prime, then
   `A ⊗_K B` with `B = Localization.Away m` of `K[β]` would collapse via
   `toMathlib/PolynomialAwayTensor.lean` to a localization of `K[α ⊔ β]`,
   and `isCohenMacaulayRing_mvPolynomial_field` + CM-localizes would close
   immediately. But the HH `A` in L7 is the reduced HH ring `K[C]/I(Γ_C)`,
   which is a Stanley-Reisner quotient, not a polynomial localization.

### Rough effort estimate

- **Flat-local CM from scratch** (mirrors the structure of
  `cm_localize_polynomial_of_cm_aux`, adapted to a general flat local map):
  ~500-900 lines spread over (i) A-flatness of `A ⊗_K B` from K-flatness
  of `B`, (ii) fiber identification as `B ⊗_K (A/m_A) ≅ B` when residue
  field is K, (iii) dimension identity for flat local maps, (iv) regular
  sequence concatenation.
- **Non-domain polynomial CM extension**: same order of magnitude; the
  domain hypothesis is genuine in the current proof skeleton.

### Options for the user

1. **Invest in the flat-local CM criterion.** ~500-900 lines of new
   infrastructure. Reusable across Lean mathematical libraries. Highest
   value, highest cost.

2. **Non-domain polynomial CM extension (DONE).** Now available as
   `isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing` /
   `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing`. Still does
   not directly close L7 as stated (A_H^red ⊗ poly localized is not quite
   poly over A_H^red), but it unblocks the **Strategy I** route: induct on
   graph size `n`, at each step use this theorem to handle polynomial
   tensor factors on top of a globally-CM smaller HH ring. See the open
   deep-model question at `questions/HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md`
   for the structural decomposition that Strategy I still requires.

3. **Rethink F2.** Abandon the tensor route. Candidates:
   - Direct Stanley-Reisner CM argument for `S ⧸ bipartiteEdgeMonomialIdeal G`
     via Reisner's criterion or shellability. Requires a lot of
     simplicial-complex infrastructure, likely not in Mathlib either.
   - Gröbner degeneration from `J_G` to its initial ideal, inheriting CM
     via upper semicontinuity. Not in Mathlib.
   - Leave global CM as a paper-faithful open branch and ship the
     equidimensional surrogate as the formalized substitute (already
     done in `PrimeDecompositionDimension.lean`).

4. **Narrow scope.** Target only the closed-graph sub-case of Prop 1.6,
   where stronger structure (quadratic Gröbner basis on `J_G`) might make
   CM easier to access directly. Does not close the full Prop 1.6.

### Recommendation

Given the cost, option 3 or 4 is probably the pragmatic call. Option 1
(build the flat-local CM criterion) unlocks this and any future CM-via-
base-change claim, so if the project expects more such claims, it pays
back. Option 2 alone does not close L7.

## What NOT to do

- Do not present `isCohenMacaulayLocalRing_at_augIdeal` as global CM.
- Do not reopen the CM localization backport.
- Do not switch to the Gröbner CM transfer yet.
- Do not reopen the `p ≤ augIdeal` branch.
- Do not restart the minimal-prime, graded-induction, dehomogenization, or
  broad parameter-prefix routes.
- Do not build the full L5 ring isomorphism A_H ≅ A_H^red ⊗_K K[s,t] —
  the CM corollary suffices for F2.

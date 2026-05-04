# `IteratedRegularity`: extract `diagSubstHom_edge_support_singleton`

## Status

**Pre-investigation proposal.** Spun out 2026-05-04 from the
ITERATED_REGULARITY_BIND1 Stage 0 abort. The BIND1 audit
identified this as the *actual* leverage point in the file — it is
independent of whether `diagSubstHom` is built via `aeval` or
`bind₁`, so it stands on its own.

## TL;DR

`BEI/Equidim/IteratedRegularity.lean` contains a ~15-LOC
"image-of-edge-monomial has singleton support" body that is
duplicated verbatim across **6 sites** (lines 745–760, 911–929,
1273–1291, 1903–1920, 2103–2117, 2228–2242). Each site does the
same `split_ifs hcond` on `b.val < k`, then in both branches
re-derives the singleton support of `±X(inl a) * X(inl b)` (resp.
`X(inl a) * X(inr b)`) via the `MvPolynomial.monomial` form.

A single private lemma packaging that body would replace ~75–90
LOC of duplication.

**Estimated reduction: ~75–90 LOC.** **Risk: low.** The body is
mechanical Finsupp/`monomial`/`support` arithmetic; no
mathematical subtlety. Refactor is *file-local*; no public
declaration changes.

## Math content

`diagSubstHom k` substitutes `y_b ↦ -x_b` for `b.val < k` and
`y_b ↦ y_b` otherwise. For an adjacent pair `(a, b)` with
`a.val < b.val`, the image of `X(inl a) * X(inr b)` under
`diagSubstHom k` is therefore one of:

- `X(inl a) * (-X(inl b))  =  -(X(inl a) * X(inl b))` — when `b.val < k`
- `X(inl a) * X(inr b)` — when `b.val ≥ k`

Both are (up to sign) products `X(inl a) * X(s)` where
`s ∈ {inl b, inr b}`, which is the `monomial` of a 2-element
Finsupp with coefficient `±1`. Its support is a singleton.

## Goal

1. Public-facing declaration statements **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check
   passes after every stage commit. `proposition_1_6` and
   `monomialInitialIdeal_isCohenMacaulay` remain
   `[propext, Classical.choice, Quot.sound]`.
3. The 6 duplicated bodies collapse to a single helper invocation.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read all 6 sites side-by-side. Confirm they are textually
  parallel modulo the surrounding wrapper (`refine ⟨…, ?_⟩` vs
  `exact ⟨…, by …⟩` vs `· …`).
- Decide the helper's exact signature. Two viable shapes:
  - **(a) Single helper, existential hides the case split**:
    ```
    private lemma diagSubstHom_edge_support_singleton
        (k n : ℕ) (a b : Fin n) :
        ∃ e, ((diagSubstHom k).toRingHom
                (X (Sum.inl a) * X (Sum.inr b))).support ⊆ {e}
    ```
    Pros: drop-in for sites that only need `∃ e, …`. Cons: the
    *witness* `e` differs by case; sites that need `e` later
    must still split.
  - **(b) Two helpers, one per branch**:
    `diagSubstHom_edge_support_singleton_lt` (for `b.val < k`)
    and `diagSubstHom_edge_support_singleton_ge` (for `b.val ≥ k`).
    Pros: each call site gets the explicit witness. Cons: 6 × 2 =
    12 invocations needed if sites alternate; less clean.
- Audit which sites only need `∃ e, support ⊆ {e}` versus which
  need the explicit witness for downstream `Finsupp.single`
  arithmetic. **If ≥ 4 of 6 sites only need the existential,
  prefer (a). Otherwise consider (b).**
- If neither (a) nor (b) is uniform across all 6 sites — i.e.,
  some sites do extra Finsupp work that does not factor through
  the helper — STOP and document as INTRINSIC.

### Stage 1: write the helper

Add a single private lemma (or pair of lemmas, per Stage 0
decision) near the top of the file, after `diagSubstHom` is
defined and before its consumers.

Body sketch (option (a)):

```
private lemma diagSubstHom_edge_support_singleton
    {n : ℕ} (k : ℕ) (a b : Fin n) :
    ∃ e, ((diagSubstHom (n := n) (K := K) k).toRingHom
            (X (Sum.inl a) * X (Sum.inr b))).support ⊆ {e} := by
  simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    diagSubstHom, MvPolynomial.aeval_X, diagSubstFun,
    Sum.elim_inl, Sum.elim_inr]
  split_ifs with hcond
  · refine ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1, ?_⟩
    rw [show X (Sum.inl a) * -X (Sum.inl b) =
      -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring,
      show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
        MvPolynomial.monomial
          (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1) 1
        from by simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
    rw [MvPolynomial.support_neg]
    exact MvPolynomial.support_monomial_subset
  · refine ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1, ?_⟩
    rw [show (X (Sum.inl a) * X (Sum.inr b) : MvPolynomial _ K) =
      MvPolynomial.monomial
        (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1) 1
      from by simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
    exact MvPolynomial.support_monomial_subset
```

Build + AxiomCheck + commit (no call-site changes yet).

### Stage 2: rewire the small sites

Replace the 4 simpler sites (lines 745–760, 1273–1291, 2103–2117,
2228–2242 — adjust per Stage 0 audit) with helper invocations.

Each call site shrinks ~15 LOC → ~2 LOC. Build + AxiomCheck +
commit per site or per batch of 2.

### Stage 3: rewire the wrapped sites

The remaining 2 sites (lines 911–929, 1903–1920) wrap the body
inside an `exact ⟨…, by …⟩` rather than calling it as standalone
tactic. Adjust the wrapper to call the helper. Build +
AxiomCheck + commit.

### Stage 4: tighten

Look for `set`s, `have`s, or `rintro` patterns that became dead
once the body is gone.

## Verification recipe

After each stage commit:

```
lake build
lake build BEI.AxiomCheck
```

Spot-check `proposition_1_6` and `monomialInitialIdeal_isCohenMacaulay`
via `lean_verify`.

## Risks

1. **Helper signature growth.** If the 6 sites use different
   `n` / `k` / type-class context (e.g., some sites have
   `[Fintype V]` in scope, others don't), the helper signature may
   need extra implicit arguments. Stage 0 must check this.
2. **Witness coupling.** Some sites may use the explicit Finsupp
   witness `e` later in the proof (for example, to compute
   `coeff e p` directly). Option (a)'s existential hides this; in
   that case the rewrite either uses `obtain ⟨e, he⟩ := …` (mild
   tax) or option (b) instead.
3. **Heartbeat / `noncomputable` differences.** Six sites have
   six surrounding contexts; one of them may have a heartbeat
   override or `noncomputable section` boundary that the helper
   crosses awkwardly.

## Coupling

Independent of `ITERATED_REGULARITY_BIND1.md` (which aborted).
Compatible with `ITERATED_REGULARITY_INL_INR_FOLD.md` and
`ITERATED_REGULARITY_CORE_INNER.md`; the helper would be reusable
inside the inl/inr sister-fold if it lands.

## Methodology reminders

See `feedback_fat_proof_carving.md`. **Negative-value rule
applies**: if Stage 0 reveals the helper signature would grow
beyond ~6 args or the body savings drop below ~50 LOC, abort and
document the failure mode in the Status section. Pattern source:
identified during the BIND1 Stage 0 audit (see
`ITERATED_REGULARITY_BIND1.md` Status section, "Where the actual
win lives").

# `IteratedRegularity`: replace `diagSubstHom k` with `MvPolynomial.bind₁`

## Status

**Stage 0 investigated 2026-05-04 → CLEAN ABORT.**
The bind₁ rewrite is structurally a no-op for this file. See
"Stage 0 outcome" section below. The actual leverage point is a
*different* refactor (closed-form support helper for edge images),
which is independent of bind₁ vs aeval.

## Stage 0 outcome (2026-05-04)

**Findings.**

1. `diagSubstHom k = aeval (diagSubstFun k)` literally
   (line 332-334 of `BEI/Equidim/IteratedRegularity.lean`).
   By `MvPolynomial.aeval_eq_bind₁`, `diagSubstHom k = bind₁ (diagSubstFun k)`
   is a one-line bridge — Stage 1 would be trivial.

2. Audit of the 25 occurrences of the canonical simp pattern
   `simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
     diagSubstHom, MvPolynomial.aeval_X, diagSubstFun,
     Sum.elim_inl, Sum.elim_inr]`
   shows the rewrite would only swap `diagSubstHom`/`aeval_X`
   for `diagSubstHom_eq_bind₁`/`bind₁_X_right`. Same simp-list
   length, same number of tokens, same downstream `split_ifs`
   on `b.val < k ∧ b.val + 1 < n`. **0 LOC saved per call.**

3. The big bookkeeping helpers (`caseB_*`, `caseC_*`, `caseD_*`,
   `isMonomial_map_diagSubstHom`, `support_divisible_by_generator`)
   spend their bulk on:
   - extracting edge data via `obtain ⟨a, b, hb, hadj, hab, rfl⟩`,
   - computing the singleton support of `±X(inl a) * X(inl b)` or
     `X(inl a) * X(inr b)` (the *result* of the simp),
   - propagating exponent constraints through `Finsupp.single`
     arithmetic.
   None of this work is touched by `bind₁` rewrites — `bind₁` is
   an `AlgHom` so `map_mul`/`map_neg`/`map_add` apply identically
   to `aeval`. Mathlib has no `bind₁`-specific lemma for
   `bind₁ f (X i * X j)` beyond what `map_mul + bind₁_X_right`
   gives, which is exactly what `map_mul + aeval_X` already gives.

4. **Cross-file impact**: `diagSubstHom` and `diagSubstFun` are
   `private` to `IteratedRegularity` (verified with grep — no uses
   in `BEI/Equidim/Bipartite.lean`, `BEI/Equidim.lean`, or any
   other file). Refactor scope is purely file-local.

**Decision.** The guide's negative-value rule (Stage 0 reveals
"the bind₁ rewrites give marginal savings on small AND big
bookkeeping → STOP, document with concrete LOC measurements,
abort cleanly") fires here.

**Where the actual win lives.**

The 5–6 places in the file with the body
```
split_ifs with hcond
· exact ⟨single (inl a) 1 + single (inl b) 1, by ...⟩  -- ~9 LOC
· exact ⟨single (inl a) 1 + single (inr b) 1, by ...⟩  -- ~6 LOC
```
duplicate ~15 LOC each (lines 745-760, 911-929, 1273-1291,
1903-1920, 2103-2117, 2228-2242). A single closed-form helper
```
private lemma diagSubstHom_edge_support_singleton
    (k : ℕ) (a b : Fin n) :
    ∃ e, ((diagSubstHom k).toRingHom (X (inl a) * X (inr b))).support ⊆ {e}
```
could replace ~75–90 LOC of duplication. **This is a separate
refactor** — it is not the `bind₁` refactor proposed in this
guide, and it is independent of whether `diagSubstHom` is
implemented via `aeval` or `bind₁`. It belongs in a new guide
("`IteratedRegularity`: extract `diagSubstHom` edge-image
helpers") if pursued.

**No commits made.** No edits made to `BEI/Equidim/IteratedRegularity.lean`.

## TL;DR

`diagSubstHom k : MvPolynomial (BinomialEdgeVars (Fin n)) K → MvPolynomial …`
substitutes `y_j ↦ −x_j` for `j < k` and is the identity elsewhere.
This is *exactly* `MvPolynomial.bind₁ (substitution function)`.

Mathlib has a rich `bind₁` / `aeval` API:
`bind₁_X`, `bind₁_C`, `bind₁_comp_bind₁`, `aeval_eq_bind₁`,
`map_bind₁`, etc. Most of the "image of a generator under
`diagSubstHom`" bookkeeping in `IteratedRegularity` is hand-rolled
and could ride on these instead.

**Estimated reduction: ~150–250 LOC** of bookkeeping inside
`IteratedRegularity`, with the bonus that proofs become more
idiomatic with Mathlib MvPolynomial API. **Risk: low–medium.** Main
hazard is universe / instance plumbing.

This refactor is *file-local* — the public statements of theorems
that use `diagSubstHom` should not change; only their bodies.

## Math content

`diagSubstHom k` is a custom ring homomorphism encoding the
diagonal substitution used in the F2/HH route. Its purpose:
the iterated image of `bipartiteEdgeMonomialIdeal G` chases the
diagonal-sum regular sequence step by step. Conceptually, the same
substitution is what `MvPolynomial.bind₁` does for any vertex-indexed
substitution function.

## Goal

1. **Public-facing declarations unchanged**: `diagSubstHom`
   itself can stay as a `def` (or become a thin wrapper around
   `bind₁`); names of all theorems using it are byte-identical.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes
   after every stage commit. `proposition_1_6` and
   `monomialInitialIdeal_isCohenMacaulay` remain
   `[propext, Classical.choice, Quot.sound]`.
3. The "image of generator under `diagSubstHom`" bookkeeping
   inside `IteratedRegularity` shrinks materially.
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read `diagSubstHom` and `diagSubstFun` definitions in
  `BEI/Equidim/IteratedRegularity.lean` (or wherever they live).
- Confirm `diagSubstHom k = MvPolynomial.bind₁ (diagSubstFun k)` is
  literally true (or one-step `simp` away).
- Audit how many `unfold diagSubstHom` / `simp [diagSubstFun, …]`
  call sites exist. Classify by what they're trying to prove
  (image of `X v`, image of a product, kernel containment, etc.).
- Check Mathlib for `bind₁`-flavoured equivalents:
  `MvPolynomial.bind₁_X`, `bind₁_C`, `bind₁_comp_bind₁`,
  `bind₁_X_left`, `bind₁_X_right`, `aeval_X`, `aeval_C`,
  `aeval_eq_bind₁`. Document which custom helpers each Mathlib
  lemma can replace.
- Decision point: if the audit shows >100 LOC of `diagSubstHom`
  bookkeeping that maps cleanly to `bind₁` / `aeval`, proceed.
  Otherwise document and skip.

### Stage 1: prove the bridge lemma

Add a single private lemma:
`diagSubstHom_eq_bind₁ : diagSubstHom k = MvPolynomial.bind₁ f`
where `f` is the substitution function. Should be `rfl` or
one-line `simp`.

If `diagSubstHom` is already definitionally equal to `bind₁ f`,
this stage is trivial. If not, it's a proof obligation.

### Stage 2: rewrite the small bookkeeping lemmas

Identify 5–10 lemmas of the form "diagSubstHom acts on `X v` /
`X u * X v` / `monomial d c` like XYZ" and replace each with a
direct `bind₁` rewrite. Build + AxiomCheck + commit.

### Stage 3: rewrite the big bookkeeping lemmas

Bigger consumers: `caseB_*`, `caseC_*`, `caseD_*` helpers,
`isMonomial_map_diagSubstHom`, `support_divisible_by_generator`.
Each may shrink as their handwritten case splits become `bind₁` /
`map_mul` rewrites. Build + AxiomCheck + commit per helper.

### Stage 4: tighten

Look for `set`s and `have`s that became dead after Stages 2–3.

## Verification recipe

After each stage commit:

```
lake build
lake build BEI.AxiomCheck
```

Plus spot-check the two flagship downstream theorems via
`lean_verify`:
- `BEI/Proposition1_6.lean` :: `proposition_1_6`
- `BEI/Equidim.lean` :: `monomialInitialIdeal_isCohenMacaulay`

## Risks

1. **Universe / instance plumbing.** `bind₁` infrastructure may
   require explicit `(K := K)` / `(σ := σ)` annotations at call
   sites. Watch diagnostics.
2. **`bind₁` may not unify trivially with `aeval`.** Some Mathlib
   helpers are stated for one and not the other. May need
   `bind₁_eq_aeval` / `aeval_eq_bind₁` rewrites at call sites.
3. **Definition might not be exactly `bind₁`.** If the existing
   `diagSubstHom` is built via `aeval` instead, the bridge lemma
   is `diagSubstHom = aeval f` or similar — same idea, slightly
   different proof.

## Cross-file impact

This refactor is *file-local* in scope. However: if `diagSubstHom`
is exported from `IteratedRegularity` and used in other files
(e.g., `BEI/Equidim/Bipartite.lean` or `BEI/Equidim.lean`), those
consumers may also benefit from the cleaner API. Audit during
Stage 0.

## Methodology reminders

See `feedback_fat_proof_carving.md`. The Buchberger refactor's
"Mathlib helper hiding in plain sight" pattern is the precedent
here — `bind₁` is the Mathlib API; `diagSubstHom` is the local
re-derivation.

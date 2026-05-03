# `IteratedRegularity`: replace `diagSubstHom k` with `MvPolynomial.bind₁`

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review. Has not yet been confirmed by a read-only
investigator. Stage 0 of the refactor plan below MUST start with
such an investigation.

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

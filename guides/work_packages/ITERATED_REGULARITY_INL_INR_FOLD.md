# `IteratedRegularity` Sections 5–6: sister-fold the inl/inr last-NZD pair

## Status

**Pre-investigation proposal.** Identified during the 2026-05-03
bird's-eye review of the three biggest files in the repo. Has not yet
been confirmed by a read-only investigator. Stage 0 of the refactor
plan below MUST start with such an investigation.

## TL;DR

`BEI/Equidim/IteratedRegularity.lean` Sections 5 and 6 are sister
branches of textually parallel "last-variable NZD" arguments:

| Lines | Section | LOC |
|---|---|---|
| 1777–2016 | NZD of `X(inl ⟨n−1, _⟩)` on quotient | **239** |
| 2017–2373 | NZD of `X(inr ⟨n−1, _⟩)` on quotient | **356** |

Same shape — kill the bipartite ideal modulo earlier diagonals plus a
chosen variable, prove the next chosen variable is a non-zero-divisor.
Differ in `Sum.inl ↔ Sum.inr` and a tweak in which earlier variable is
added to the modulus.

The corresponding sister-fold worked in the 2026-05-03 mixed_walk and
covered_walk carves: `subWalk_drop` / `subWalk_take` were used 10×
across three theorems after a `Side`-style parameterisation. The same
playbook plausibly applies here.

**Estimated reduction: ~300 LOC** (folding 595 LOC into a ~250-LOC
`Side`-parameterised helper + thin per-side instantiations).
**Risk: medium** — the same `Sum.inl` / `Sum.inr` simp-set
non-uniformity hazard the mixed_walk carve faced, which was solvable.

## Math content

The end-of-section sequence: assuming the diagonal sums
`x_0 + y_0, …, x_{n−2} + y_{n−2}` form a regular sequence on `S /
bipartiteEdgeMonomialIdeal G`, prove that `x_{n−1}` is a NZD on the
quotient by that sequence (Section 5), and then that `y_{n−1}` is a
NZD on the further quotient by `x_{n−1}` (Section 6). Together they
extend the diagonal-sum regular sequence to length n+1.

## Goal

1. Statements of `theorem`-level declarations in both sections
   **byte-identical**.
2. **No new axioms**: `BEI/AxiomCheck.lean` regression check passes
   after every stage commit. `proposition_1_6` and
   `monomialInitialIdeal_isCohenMacaulay` (the two consumers of this
   file's flagship results) must remain `[propext, Classical.choice,
   Quot.sound]`.
3. The two section bodies materially shorter via 1–2 new private
   helpers parameterised on a `Side` (Bool or inductive
   `BinomialSide`).
4. `lake build` clean, no new heartbeat overrides.

## Concrete refactor plan

### Stage 0: investigate

- Read both sections end-to-end. Confirm the textual symmetry claim
  by diffing 5 vs 6.
- Identify *exactly* what's parameterised: the variable chosen
  (`inl` vs `inr`), the prior modulus (which earlier diagonals + which
  earlier variables), and any tactic-level differences (e.g., simp
  sets that don't unify trivially).
- Document either: (a) sister symmetry confirmed → proceed; or
  (b) divergence found → re-plan.

### Stage 1: thin `Sum`-direction wrapper

Following the mixed_walk playbook, write a small wrapper helper that
makes `d (Sum.inl i)` and `d (Sum.inr i)` reasoning uniform under a
`Side` parameter. Prove it collapses via `simp` so the parameterised
main helper can call it.

### Stage 2: extract the parameterised NZD helper

One private helper, `last_variable_nzd_on_quotient_step`, taking:
- `side : Side`
- the current modulus (prior diagonals + prior killed variables)
- the proof that the next variable on `side` is in (or out of) the
  appropriate places.

Returns the NZD claim. Replace both inline section bodies with calls.

### Stage 3: tighten

Look for now-redundant `set`s and `have`s in the surrounding
scaffolding.

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

Both must report `[propext, Classical.choice, Quot.sound]`.

## Risks

1. **`Sum.inl` / `Sum.inr` simp-set non-uniformity** — the same
   hazard the mixed_walk carve faced. Mitigation: write the
   `Sum`-direction wrapper helper FIRST, prove it collapses via
   simp, then parameterise the main helper.
2. **Asymmetry in the prior modulus.** Section 6 includes the
   already-proved-NZD `x_{n−1}` in its modulus, so the two sections
   aren't perfectly parallel — they're "next-step" sisters, not
   "same-step". The helper signature must allow this.
3. **Heartbeat regressions** — extract sub-helpers if needed, do not
   raise heartbeats.

## Methodology reminders

See `feedback_fat_proof_carving.md`. Especially: do Stage 0 first;
abort if the symmetry is not real; the negative-value rule applies
if the helper signature would grow beyond its body savings.

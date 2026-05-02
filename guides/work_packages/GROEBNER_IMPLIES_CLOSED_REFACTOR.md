# `groebner_implies_closed`: deduplicate the 4 sister branches

## TL;DR

`groebner_implies_closed` (`BEI/ClosedGraphs.lean:452`) is **513 LOC** —
fifth-largest declaration in the repo and the largest never-investigated
proof after the just-completed Buchberger refactor.

The proof has **4 nearly-identical branches** of ~120 LOC each, arising
from `constructor` (Conditions 1 and 2 of `IsClosedGraph`) × two
`rcases lt_or_gt_of_ne` sub-cases. Each branch follows the *same*
skeleton — build `hp_mem`, `hp_eq`, `hdeg1`/`hdeg2`, invoke `lex_lt`
(already extracted), invoke `contra` (already extracted), then a
~30-LOC `extract a,b` epilogue — differing only in which inl/inr index
plays which role.

Three private helpers (`lex_lt`, `contra`, `extract_b`) are already
extracted as inline `have`s. Three more natural extractions remain:

1. `cubic_degree` — wraps the 9-line `simp + degree_mul + degree_X`
   incantation used **8×** (twice per branch).
2. `cubic_witness` — packages `hp_mem + hp_eq + hp_deg + lex_lt`
   parameterised by index permutation.
3. `extract_ab_from_le` — the divisibility-extraction epilogue.

Estimated **513 → 280–320 LOC** (~40% reduction). Risk: **medium** —
the four branches differ in which inl/inr index is the discriminator,
so the helpers need careful parameterisation, but the symmetry is
real and textual.

## Status

- Discovered: 2026-05-02 broader fat-proof scan.
- Investigated by a read-only subagent 2026-05-02; classified as
  `[CARVE-CANDIDATE]` with the structure above.
- Proof is **stable and axiom-clean**
  (`{propext, Classical.choice, Quot.sound}`); do not touch unless
  committed to the full refactor.
- Marked `[ ]` in the "Newly-discovered fat proofs" table of `TODO.md`.

## Goal

Refactor `groebner_implies_closed` so that:

1. The statement is **byte-identical** (signature, name, namespace,
   declaration kind — `theorem`, not `private`, with the
   `omit [DecidableEq V]` decoration intact).
2. **No new axioms** are introduced. After the refactor,
   `lean_verify` on `groebner_implies_closed` and on `theorem_2_1`
   (the closest downstream consumer; closure ↔ Gröbner is the whole
   point of Section 2) must still report exactly
   `[propext, Classical.choice, Quot.sound]`.
3. The body is materially shorter, structured around 2–3 new top-level
   private helpers (or inline `have ∀ ...` blocks if that's cleaner).
4. `lake build` is clean, with no new heartbeat overrides.

## Where the proof lives

| Block | Lines | Role |
|---|---|---|
| Header (`hGenUnit`) | 458–462 | All generators have unit leading coefficient. |
| Inline `lex_lt` | 466–482 | `(M2 <lex M1)` when M2 missing inr d, M1 has it. **Already extracted.** |
| Inline `contra` | 484–514 | Core contradiction: `p ∈ J_G`, `degree p = D`, no quadratic generator divides `D`. **Already extracted.** |
| Inline `extract_b` | 517–527 | Extract `b = j` from a divisibility constraint. **Already extracted.** Note: agent flagged this as possibly unused. Verify before deleting. |
| `constructor` | 528 | Splits `IsClosedGraph` into Conditions 1 and 2. |
| Condition 1 | 529–763 | `∀ i j k, i<j → i<k → j≠k → adj(i,j) → adj(i,k) → adj(j,k)`. Two sub-cases via `rcases lt_or_gt_of_ne hjk`. |
| ... Sub-case `j < k` | 533–~640 | ~110 LOC. |
| ... Sub-case `k < j` | ~640–763 | ~125 LOC. |
| Condition 2 | 764–end | Symmetric to Condition 1 with the indices swapped. Two sub-cases. ~115 LOC each. |

## The four-way symmetry

Each of the 4 branches has the same shape:

```
have hp_mem : <some y_α * fij i_β j_γ - y_δ * fij i_β j_ε> ∈ J_G := …
have hp_eq  : <that polynomial> = <ring-normalised cubic difference> := by ring
have hdeg1  : degree <cubic₁> = single(inl _) 1 + single(inr _) 1 + single(inr _) 1 := by
  simp only [x, y]
  rw [degree_mul …, degree_mul …, degree_X, degree_X, degree_X]
have hdeg2  : degree <cubic₂> = single(inl _) 1 + single(inr _) 1 + single(inr _) 1 := by
  simp only [x, y]
  rw [degree_mul …, degree_mul …, degree_X, degree_X, degree_X]
have hp_deg : degree p = <some D> := by
  rw [hp_eq, degree_sub_of_lt (lex_lt … hdeg2 hdeg1 …)]
exact contra _ _ hp_mem hp_deg <D ne 0> <hno_gen via extract a,b>
```

The only things that vary across branches:

- **Which** of `(i, j, k)` (Condition 1) or `(i, j, l)` (Condition 2)
  plays each role.
- **Which** `inl`/`inr` index is the "missing" coordinate `d` for
  `lex_lt`.
- **Which** generator `fij a b` the contradiction extraction targets.

Everything else is textually identical or a uniform permutation.

## The proposed helpers

### Helper 1: `cubic_degree`

```
private lemma cubic_degree {R : Type*} [CommRing R] [Nontrivial R] (a b c : V) :
    binomialEdgeMonomialOrder.degree
      (x a * y b * y c : MvPolynomial (BinomialEdgeVars V) R) =
    Finsupp.single (Sum.inl a) 1 +
      Finsupp.single (Sum.inr b) 1 + Finsupp.single (Sum.inr c) 1 := by
  simp only [x, y]
  rw [MonomialOrder.degree_mul (mul_ne_zero (X_ne_zero _) (X_ne_zero _)) (X_ne_zero _),
      MonomialOrder.degree_mul (X_ne_zero _) (X_ne_zero _),
      MonomialOrder.degree_X, MonomialOrder.degree_X, MonomialOrder.degree_X]
```

Replaces 8 inline copies of the 9-line block. Net save: ~80 LOC across
the 4 branches.

You may also want a `(y a * x b * x c)` mirror, depending on what the
Condition 2 cubics look like — read those branches before settling on
the signature.

### Helper 2: `cubic_witness`

The four-line skeleton "build `hp_mem`, normalise via `hp_eq`, derive
`hp_deg` from `lex_lt`" can be packaged into one helper that takes:

- the two cubics (or an index permutation that determines them),
- the underlying edge-adjacency hypotheses,
- the order witnesses (`hij`, `hik`, `hjk`),

and returns `⟨p, hp_mem, hp_deg⟩` (or directly the `False` produced
by `contra`).

Carving this requires care — the four cubics are not all literal
permutations of one expression. Sketch the helper signature **after**
landing `cubic_degree` so you can see what's left to abstract.

### Helper 3: `extract_ab_from_le`

The ~30-LOC epilogue that extracts `a, b` from a divisibility
`single(inl a) + single(inr b) ≤ D` and contradicts `hjk` (or its
mirror in Condition 2) is the same pattern in all 4 branches. Extract
once with the right `D` parameter.

## Concrete refactor plan

Work in **stages**, with `lake build` clean and
`lean_verify --theorem groebner_implies_closed` axiom-clean after
each checkpoint. Commit each stage separately.

### Stage 0: clarify what's actually used (cheap)

- Confirm whether the inline `extract_b` (line 517) is actually used
  in any branch. If not, delete it. If it's used, keep it.
- Read all four branches end-to-end to confirm the agent's claim that
  they are uniform up to index permutation.
- If you find a branch that diverges materially, **stop and re-plan**;
  the helper signatures depend on the symmetry holding.

### Stage 1: extract `cubic_degree` (low risk)

- Add `cubic_degree` as a top-level `private lemma` immediately above
  `groebner_implies_closed`.
- Replace each of the ~8 inline `hdeg1`/`hdeg2` blocks with a one-line
  call. (Some may need an `x ↔ y` mirror — extract a `cubic_degree_y`
  variant if needed.)
- Build, verify axioms.

### Stage 2: extract `extract_ab_from_le` (low–medium risk)

- Add the helper.
- Replace each of the 4 epilogues. Each takes the same shape but with
  permuted `i / j / k`-style indices.
- Build, verify axioms.

### Stage 3: extract `cubic_witness` (medium risk)

- This is the hardest one because the 4 cubics differ in their
  underlying edge structure. The helper might take the form of a
  "given two cubics with the right degree relation, here's the
  contradiction" wrapper around `contra` — or it might naturally
  parameterise over an index permutation `ι : Fin 3 → V`.
- Sketch on paper before writing. If the parameterisation gets
  ugly, **stop here** — the gain may not justify the helper's
  complexity.
- Build, verify axioms.

### Stage 4: tighten the result

- After Stages 1–3, look for now-redundant `have`s in the surrounding
  scaffolding.
- Final build + axiom check.

## Verification recipe

After every commit:

```
lake build
```

Then via the Lean MCP:

```
lean_verify
  file=BEI/ClosedGraphs.lean
  theorem=groebner_implies_closed
```

Must report `axioms = [propext, Classical.choice, Quot.sound]`,
no warnings.

Plus the standard flagship-theorem cross-check (closure ↔ Gröbner is
the heart of Section 2):

```
lean_verify file=BEI/GroebnerBasisSPolynomial.lean theorem=theorem_2_1
lean_verify file=BEI/Proposition1_6.lean theorem=proposition_1_6
lean_verify file=BEI/Corollary3_4.lean theorem=corollary_3_4
lean_verify file=BEI/Corollary3_4.lean theorem=corollary_3_7_cm_fin
lean_verify file=BEI/Equidim.lean theorem=monomialInitialIdeal_isCohenMacaulay
```

All five must remain axiom-clean.

## Risks

1. **Symmetry breaks.** If one of the four branches has a subtle
   variation the agent missed, the helper signatures derived from the
   "uniform" branches won't fit. Mitigation: read all 4 branches
   end-to-end in Stage 0 before extracting helpers.
2. **Helper-signature bloat.** If `cubic_witness` ends up taking 8+
   parameters, the LOC saved in the call site is eaten by the
   signature. Mitigation: stop at Stage 2 if Stage 3 won't pay for
   itself.
3. **Heartbeat regressions.** Watch for `set_option maxHeartbeats`
   raises after each stage; mitigate by sub-helpers if needed.
4. **`extract_b` confusion.** The agent flagged the existing inline
   `extract_b` (line 517) as possibly unused. If it's truly dead,
   delete it in Stage 0; if a branch uses it, account for that in the
   `extract_ab_from_le` design.

## Rollback

Revert with `git revert` of the specific stage commits. The original
proof is preserved in the git history.

## Methodology reminders (from `feedback_fat_proof_carving.md`)

- Before touching the proof, **state in your own words** what
  `groebner_implies_closed` is mathematically trying to prove. Don't
  paraphrase the docstring — describe the math (Conditions (b1) and
  (b2) of Herzog Theorem 1.1 are encoded by the predicate
  `IsClosedGraph G`).
- **Sketch the simpler proof** ignoring the existing one. Both
  conditions follow the same template: assume a missing edge, build
  a polynomial in the ideal whose leading monomial is cubic, observe
  no quadratic generator can divide it, contradict the Gröbner-basis
  hypothesis.
- The **Buchberger guide** (`guides/archive/BUCHBERGER_DECOMPOSITION_REFACTOR.md`)
  is a good template for how a multi-stage carve was structured and
  verified — the playbook applies here.
- After each stage, **run the verification recipe above**. If
  `lean_verify` reports a new axiom, stop and investigate.
- **Do not extract sub-`have`s into named lemmas as a first resort.**
  The win here is real because the four branches duplicate the same
  9-line `simp + rw` and the same 30-LOC epilogue, not because every
  inline `have` deserves its own name.

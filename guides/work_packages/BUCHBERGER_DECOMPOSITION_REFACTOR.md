# Buchberger criterion: replace manual k-induction with Mathlib's `sPolynomial_decomposition'`

## TL;DR

`isGroebnerBasis_iff_sPolynomial_isRemainder` (`BEI/GroebnerAPI.lean:127`)
is **1066 LOC**, the second-largest declaration in the repo after
`theorem_2_1`. About **900 LOC of its backward direction** is a manual
strong induction on the count `k` of top-degree terms in a representation
`c : ↑G →₀ MvPolynomial σ R`. That induction re-derives, by hand,
exactly what Mathlib's `MonomialOrder.sPolynomial_decomposition'` already
proves in two lines. Three of the proof's own comments explicitly
reference `sPolynomial_decomposition'` but the body never actually calls
it — the proof was apparently written before that Mathlib lemma was
available, or the author chose not to use it.

Replacing the inner k-induction with a direct application of
`sPolynomial_decomposition'` should shrink the proof from
**1066 → ~250 LOC** (~75% reduction), with no statement change and no
new axioms.

This is the **single biggest available LOC win** in the repo. The catch
is risk: this is a load-bearing public theorem on the Section 2
critical path (`theorem_2_1` calls it), so a botched refactor breaks
the build. Plan for a multi-hour session and verify aggressively.

## Status

- Discovered: 2026-05-02 during a broader fat-proof scan.
- Original proof is **stable and axiom-clean** (`{propext,
  Classical.choice, Quot.sound}`); do not touch unless committed to
  the full refactor.
- Marked `[ ]` in the "Newly-discovered fat proofs" table of `TODO.md`.

## Goal

Refactor `isGroebnerBasis_iff_sPolynomial_isRemainder` so that:

1. The statement is **byte-identical** (signature, name, namespace,
   declaration kind — `theorem`, not `private`).
2. **No new axioms** are introduced. After the refactor,
   `lean_verify` on `theorem_2_1` (its main consumer) must still
   report exactly `[propext, Classical.choice, Quot.sound]`.
3. The body is materially shorter, structured around
   `MonomialOrder.sPolynomial_decomposition'` instead of the manual
   k-induction.
4. `lake build` is clean, with no new heartbeat overrides.

The split between "forward" and "backward" directions can become
two private helper lemmas joined by `⟨forward, backward⟩` if that
helps clarity. The public iff statement and name must not change.

## Where the proof lives

| Block | Lines | Role |
|---|---|---|
| Forward (→) | 132–167 | "If GB then S-polynomials reduce to 0." Already clean (~36 LOC). Likely needs no change. |
| Backward (←) | 167–end | The 900-LOC giant. |
| `suffices hkey ...` framing | 191–223 | Reduces "lt(span G) ⊆ span(lt G)" to a key existence lemma. |
| Outer WFI on `D` (max syntactic-degree of representation) | 225+ | Strong induction on `D : m.syn`. |
| Case A: `D = m.toSyn (m.degree f)` | 237–270 | Easy: pick `b₀` achieving the max; use `degree_mul`. |
| Case B: `D > m.toSyn (m.degree f)` | 271+ | Hard. |
| Easy sub-case (all terms < D) | 285–292 | One-liner via outer IH. |
| **Hard sub-case (some terms achieve D)** | 293+ | The bulk. |
| Inner strong induction on `k` (count of top-D terms) | 329–end | **~700 LOC**. This is what `sPolynomial_decomposition'` replaces. |

## The Mathlib lemma to use

```
-- Mathlib/RingTheory/MvPolynomial/MonomialOrder.lean line 1044
lemma MonomialOrder.sPolynomial_decomposition' {d : m.syn} {ι : Type*}
    {B : Finset ι} (g : ι → MvPolynomial σ R)
    (hd : ∀ b ∈ B, (m.toSyn <| m.degree <| g b) = d ∨ g b = 0)
    (hfd : (m.toSyn <| m.degree <| ∑ b ∈ B, g b) < d) :
    ∃ (c : ι → ι → R),
      ∑ b ∈ B, g b = ∑ b₁ ∈ B, ∑ b₂ ∈ B, (c b₁ b₂) • m.sPolynomial (g b₁) (g b₂)
```

In English: if you have a finite family of polynomials each of which
either has the same syntactic degree `d` or is zero, and the family's
sum has syntactic degree strictly less than `d`, then the sum
decomposes as a (scalar) linear combination of S-polynomials of
pairs from the family.

The lemma lives in the `Field` section of `MonomialOrder.lean`, which
matches the `[Field R]` hypothesis already present on the BEI theorem.

## The simpler proof sketch

Inside the hard sub-case at line 293, after entering with
`hall_lt : ¬ ∀ b ∈ c.support, m.toSyn (m.degree (c b * b)) < D`, the
target is to produce a representation `c' : ↑G →₀ MvPolynomial σ R`
such that `c'.sum smul = f` and every term has syntactic degree `< D`.

Use Mathlib's lemma like this:

1. Let `B_hi := c.support.filter (fun b => m.toSyn (m.degree (c b * b)) = D)`
   — the top-D indices.
2. Define `g : ↑G → MvPolynomial σ R` by
   `g ⟨b, _⟩ := if b ∈ B_hi then m.leadingTerm (c b) * b else 0`.
3. Each `g _` is either zero or has syntactic degree exactly `D`
   (the leading-term part of a top-D element, with a unit leading
   coefficient since `R` is a field and `b ≠ 0`).
4. The sum `∑ x ∈ G_finset, g x` has syntactic degree `< D` —
   because the original representation `c.sum smul = f` has degree
   `m.toSyn (m.degree f) < D` (this is `hf_lt_D` in scope), and the
   "lower part" `∑ x, (c x - leadingTerm (c x)) * x` has degree `< D`
   componentwise.
5. Apply `sPolynomial_decomposition'` to `g` over `B_hi` to obtain
   coefficients `c'' : ↑G → ↑G → R` such that
   `∑ x ∈ B_hi, g x = ∑ x₁ x₂, c'' x₁ x₂ • m.sPolynomial (g x₁) (g x₂)`.
6. Each `m.sPolynomial (g x₁) (g x₂) = monomial_factor * m.sPolynomial x₁ x₂`
   by `MonomialOrder.sPolynomial_monomial_mul` (already used at line 99).
7. Each `m.sPolynomial x₁ x₂` reduces to `0` mod `G` by the
   hypothesis `hSP` of the iff.
8. Therefore `∑ x ∈ B_hi, g x` has a representation with all terms
   of degree `< D` (combine steps 5–7).
9. Combine with the lower part of `c` to build the desired `c'`.

In code, steps 6–8 collapse into a Finsupp construction that closes
out the hard sub-case. The expected size of the rewritten body is
~150–200 LOC (vs the current ~700 LOC of inner k-induction).

## Concrete refactor plan

Work in **stages**, with `lake build` clean and
`lean_verify --theorem theorem_2_1` axiom-checking after each
checkpoint. Commit each checkpoint separately.

### Stage 0: scaffolding (low risk)

- Optionally split the iff into two private helpers
  `isGroebnerBasis_of_sPolynomial_isRemainder` (←) and
  `sPolynomial_isRemainder_of_isGroebnerBasis` (→). The public iff
  becomes `⟨…, …⟩`. This is structural cleanup with zero proof
  change. Skip if you prefer to keep the iff intact.
- Verify build + axioms.

### Stage 1: replace the hard sub-case (the big win)

- Locate the inner `suffices ∀ (k : ℕ) (c : MvPolynomial σ R →₀ ...
  ...` block at `BEI/GroebnerAPI.lean:329` (current line numbers).
  This is the body to delete.
- Replace it with a direct application of `sPolynomial_decomposition'`
  along the sketch above.
- Anchor the rewrite at the top of the hard sub-case (`push_neg at
  hall_lt; classical`) and end at the `apply ihk k' ...` site
  (current line 632) — i.e., produce the same `c'` data structure
  the rest of the surrounding proof expects.
- After this stage the proof should already build and be axiom-clean.

### Stage 2: clean up the surrounding scaffolding

- The `set ev₀ := ...`, `set h12_scaled := ...`, `set h12_lifted := ...`,
  `set ratio := ...`, `set scale_poly := ...`, `set adj_b1 := ...`,
  `set adj_b2 := ...`, `set c1 := ...` block (lines 583–631) is no
  longer used after Stage 1; delete it.
- The 700+ LOC of `· -- k' < k`, `· -- c1.support ⊆ G`, `· -- c1.sum
  smul = f` sub-proofs (lines 633–end) are also no longer needed.

### Stage 3: tighten the outer structure

- After Stages 1–2, look for now-redundant `set`/`have` blocks in
  the outer Case B / WFI scaffolding that the simpler proof made
  obsolete.
- Run `lake build` and `lean_verify` one more time.

## Verification recipe

After every commit on this work, run:

```
lake build
```

Then via the Lean MCP (or in a scratch file):

```
lean_verify
  file=BEI/GroebnerBasisSPolynomial.lean
  theorem=theorem_2_1
```

Must report `axioms = [propext, Classical.choice, Quot.sound]` with
no warnings. Also re-verify any other downstream consumers of the
iff (search with `grep -rn "isGroebnerBasis_iff_sPolynomial_isRemainder"`):

- `BEI/GroebnerBasisSPolynomial.lean` (`theorem_2_1`).
- Any other call sites surfaced by the grep.

A safety check across other flagship theorems:

```
lean_verify file=BEI/Proposition1_6.lean theorem=proposition_1_6
lean_verify file=BEI/Corollary3_4.lean theorem=corollary_3_4
lean_verify file=BEI/Corollary3_4.lean theorem=corollary_3_7_cm_fin
lean_verify file=BEI/Equidim.lean theorem=monomialInitialIdeal_isCohenMacaulay
```

All must remain axiom-clean.

## Risks

1. **Build break on `theorem_2_1`.** This iff is the foundation of
   Section 2's main theorem. Any incompatibility in the produced `c'`
   data shape immediately breaks the whole Section 2 chain. Mitigation:
   develop on a feature branch; do not merge until all
   downstream theorems still build and axiom-check.
2. **Subtle hypothesis mismatch.** The Mathlib lemma's `hd` requires
   `(m.toSyn (m.degree (g b)) = d) ∨ (g b = 0)`. The local code may
   need `g b ≠ 0 → IsUnit (m.leadingCoeff (g b))` (the stronger form
   from `sPolynomial_decomposition`, no apostrophe). With `R` a field
   the unit condition is automatic, but double-check the apostrophe
   when wiring up.
3. **Field assumption scope.** `sPolynomial_decomposition'` is in the
   Field section of Mathlib's file. `[Field R]` is already a hypothesis
   of the BEI theorem, so this is fine — but if you ever need to weaken
   to `[CommRing R]`, the apostrophe-less `sPolynomial_decomposition`
   is the substitute (with the extra `IsUnit` condition).
4. **Heartbeat regressions.** A new `set_option maxHeartbeats` raise is
   a smell; mitigate by extracting a private helper lemma instead.

## Rollback

If the refactor stalls or regresses, revert with `git revert` of the
specific stage commits. The original proof is preserved in the git
history.

## Methodology reminders (from `feedback_fat_proof_carving.md`)

- Before touching the proof, **state in your own words** what
  `isGroebnerBasis_iff_sPolynomial_isRemainder` is mathematically
  trying to prove. Don't paraphrase the docstring — describe the math.
- **Sketch the simpler proof** ignoring the existing one. The sketch
  above is a starting point but you should re-derive it from the
  Mathlib lemma's signature.
- **Test the skeleton** with `lean_multi_attempt` or
  `lean_run_code` before committing the carve. Validate the type of
  the result of `sPolynomial_decomposition'` on a stub `g`.
- **Do not extract sub-`have`s into named lemmas** as a first
  resort; the goal is to *delete* the manual induction, not to rename
  it.
- After each stage, **run the verification recipe above**. If
  `lean_verify` reports a new axiom, stop and investigate.

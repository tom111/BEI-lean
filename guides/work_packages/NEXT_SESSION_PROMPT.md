# Next-Session Prompt: close `tildeJ_polyT_colon_eq` for closed graphs

## One-line goal

Close the R1.d leaf sorry `tildeJ_polyT_colon_eq` in `BEI/GroebnerDeformation.lean`
for closed graphs. This is the single active step for Prop 1.6's R1 branch.

## State at start of session

Two sub-sorries on the Prop 1.6 critical path, both in
`BEI/GroebnerDeformation.lean`:

1. `tildeJ_quotient_isCohenMacaulay` (graded LTG; depends on dormant Case C
   of `toMathlib/GradedCM.lean`). **Not this session's target.**
2. `tildeJ_polyT_colon_eq` (BEI Gröbner colon-ideal statement).
   **This session's target.**

```lean
-- at BEI/GroebnerDeformation.lean:498
theorem tildeJ_polyT_colon_eq
    {n : ℕ} (G : SimpleGraph (Fin n))
    (q : PolyT K) (_hq : q ≠ 0)
    (c : DefRing n K) (_hmul : polyTInclude (K := K) n q * c ∈ tildeJ (K := K) G) :
    c ∈ tildeJ (K := K) G := by
  sorry
```

Once this sorry is closed, `tildeJ_flat_over_polyT`,
`tildeJ_tMinusOne_isSMulRegular`, `tildeJ_t_isSMulRegular` all unlock
(they are already proved conditional on this).

## Scaffolding already in place (do not rebuild)

Registered in `BEI/GroebnerDeformation.lean`:

- `PolyT K := MvPolynomial Unit K`, with `IsPrincipalIdealRing` via
  `pUnitAlgEquiv` transport.
- `polyTInclude n : PolyT K →ₐ[K] DefRing n K = rename Sum.inr`.
- `Algebra (PolyT K) (DefRing n K)` + scalar tower `K → PolyT K → DefRing n K`.
- `defLE` — paper's `x_1 > x_2 > … > y_1 > … > y_n` order, extended with
  `t = Sum.inr ()` strictly at the bottom.
- `defVars_Finite`, `defVars_LinearOrder`, `defVars_WellFoundedGT`.
- `deformationMonomialOrder n : MonomialOrder (BinomialEdgeVars (Fin n) ⊕ Unit)`.

## Plan: four concrete lemmas + final assembly

Work through these in order. Each is self-contained.

### Step 1: `leadingCoeff_fijTilde = 1`

```lean
theorem leadingCoeff_fijTilde {n : ℕ} {i j : Fin n} (hij : i < j) :
    (deformationMonomialOrder n).leadingCoeff (fijTilde (K := K) i j) = 1 := by
  sorry
```

`fijTilde i j = X (inl (inl i)) * X (inl (inr j)) - X (inr ())^(j-i) * X (inl (inl j)) * X (inl (inr i))`.
Under `deformationMonomialOrder`:
- Term 1 support: `inl (inl i) ↦ 1, inl (inr j) ↦ 1`.
- Term 2 support: `inl (inl j) ↦ 1, inl (inr i) ↦ 1, inr () ↦ j - i`.

Lex comparison starts at the largest variable. Under `defLE`, `inl (inl i)` is
largest (smallest `i`). Term 1 has exponent 1 there; Term 2 has 0. So Term 1
dominates, and `leadingCoeff = 1` (the coefficient of Term 1).

Approach: reduce to `MonomialOrder.leadingCoeff_sub_of_lt`, or compute
directly via `MonomialOrder.leadingCoeff` + `MvPolynomial.coeff_sub`.
Scout via `lean_leansearch "MonomialOrder leadingCoeff sub"`.

### Step 2: `degree_fijTilde`

```lean
theorem degree_fijTilde {n : ℕ} {i j : Fin n} (hij : i < j) :
    (deformationMonomialOrder n).degree (fijTilde (K := K) i j) =
      Finsupp.single (Sum.inl (Sum.inl i)) 1 + Finsupp.single (Sum.inl (Sum.inr j)) 1 := by
  sorry
```

This is the multi-index of `x_i y_j`. Proof parallels Step 1.

### Step 3: apply `MonomialOrder.div_set`

Use Mathlib's division algorithm. Signature:

```lean
-- Mathlib/RingTheory/MvPolynomial/Groebner.lean
theorem MonomialOrder.div_set
    {σ R} [CommRing R] {B : Set (MvPolynomial σ R)}
    (hU : ∀ b ∈ B, IsUnit (m.leadingCoeff b))
    (f : MvPolynomial σ R) :
    ∃ g r,
      f = (Finsupp.linearCombination _ (↑·)) g + r ∧
      (∀ b : ↑B, m.toSyn (m.degree (↑b * g b)) ≤ m.toSyn (m.degree f)) ∧
      ∀ c ∈ r.support, ∀ b ∈ B, ¬m.degree b ≤ c
```

Apply with `B = { fijTilde i j | G.Adj i j, i < j }` and unit leading coeffs
from Step 1. Get:

```lean
lemma tildeJ_div {n : ℕ} (G : SimpleGraph (Fin n)) (c : DefRing n K) :
    ∃ (g : ↑(_ : Set (DefRing n K)) →₀ DefRing n K) (r : DefRing n K),
      c = (Finsupp.linearCombination _ (↑·)) g + r ∧
      (∀ α ∈ r.support,
        ∀ (i j : Fin n), G.Adj i j → i < j →
          ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α)) ∧
      (Finsupp.linearCombination _ (↑·)) g ∈ tildeJ (K := K) G
```

Note: `B`'s set structure can be messy. A cleaner alternative: apply
`MonomialOrder.div_set` with `B = tildeJ_generators G` (a concrete
`Set (DefRing n K)`).

### Step 4: the **Gröbner basis property** (new BEI lemma)

This is the only genuinely new BEI mathematical content. Add
`IsClosedGraph G` as a hypothesis — see the "Decision" section below.

```lean
theorem tildeJ_gbProperty {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (p : DefRing n K)
    (hp : p ∈ tildeJ (K := K) G)
    (hsupp : ∀ α ∈ p.support,
      ∀ (i j : Fin n), G.Adj i j → i < j →
        ¬ ((deformationMonomialOrder n).degree (fijTilde (K := K) i j) ≤ α)) :
    p = 0 := by
  sorry
```

Proof outline (classical):
- `{fij}` is a reduced Gröbner basis of `J_G` for closed graphs
  (`BEI/GroebnerBasis.lean`: `theorem_2_1_isReducedGroebnerBasis`).
- Specialize at `t = 1` (via `specOne`). `specOne(p)` then has support
  avoiding `x_i y_j`-divisibility, and `specOne(p) ∈ J_G`. By the
  closed-graph GB, `specOne(p) = 0`. [But the `t`-info is lost — needs care.]
- Alternative: direct Buchberger argument on `{f̃_{i,j}}` for closed graphs,
  showing all S-polynomials reduce to 0 in the deformation.

Either route is ~100–300 LOC. The simplest might be: show
`{f̃_{i,j}}` inherits reducedness from `{fij}` via the `t`-grading, and
that the S-polynomial reduction carries over uniformly.

### Step 5: assemble `tildeJ_polyT_colon_eq`

```lean
theorem tildeJ_polyT_colon_eq
    {n : ℕ} {G : SimpleGraph (Fin n)} (hClosed : IsClosedGraph G)
    (q : PolyT K) (hq : q ≠ 0)
    (c : DefRing n K) (hmul : polyTInclude (K := K) n q * c ∈ tildeJ (K := K) G) :
    c ∈ tildeJ (K := K) G := by
  obtain ⟨g, r, hdecomp, hrSupp, hgbPart⟩ := tildeJ_div G c
  -- c = (Σ g_b · f̃_b) + r  with r's support all "standard"
  -- polyTInclude q · c = (Σ polyTInclude q · g_b · f̃_b) + polyTInclude q · r
  -- polyTInclude q · r has support also "standard" (multiplying by K[t] doesn't
  -- introduce x_i y_j divisibility)
  have hprod_mem : polyTInclude (K := K) n q * r ∈ tildeJ G := by
    -- from hmul and hgbPart
    sorry
  have hprod_supp : ∀ α ∈ (polyTInclude n q * r).support, … := sorry
  have hprod_zero : polyTInclude n q * r = 0 :=
    tildeJ_gbProperty hClosed _ hprod_mem hprod_supp
  -- DefRing n K is a domain, polyTInclude q ≠ 0, so r = 0
  have hrzero : r = 0 := by
    have : polyTInclude n q ≠ 0 := by
      rw [polyTInclude]; exact (rename_injective _ Sum.inr_injective).ne hq
    exact (mul_eq_zero.mp hprod_zero).resolve_left this
  -- Hence c = Σ g_b · f̃_b ∈ tildeJ
  rw [hrzero, add_zero] at hdecomp
  rw [hdecomp]
  exact hgbPart
```

## Decision: add `IsClosedGraph G` hypothesis?

The Gröbner-basis property only holds for closed graphs. For non-closed
graphs, `{f̃_{i,j}}` is not a GB of `Ĩ`, and the colon statement needs a
different proof (or may fail for our specific `Ĩ`). Recommendation:

**Add `IsClosedGraph G` to `tildeJ_polyT_colon_eq`**. Propagate upward:

- `tildeJ_flat_over_polyT` (add hypothesis, use it in the call).
- `tildeJ_tMinusOne_isSMulRegular`, `tildeJ_t_isSMulRegular` (add hypothesis).
- `tildeJ_quotient_isCohenMacaulay` (add hypothesis; currently sorry).
- `groebnerDeformation_cm_transfer` (add hypothesis).
- `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` — **already has it**.

No change needed at `proposition_1_6` (it already passes `hClosed`).

## Workflow rules

Use lean-lsp MCP tools, **not** `lake build` for iteration:

- `lean_diagnostic_messages BEI/GroebnerDeformation.lean` — file errors.
- `lean_goal <file> <line>` — proof state before a tactic.
- `lean_multi_attempt <file> <line> ["tac1", "tac2", …]` — cheap tactic trials.
- `lean_leansearch` / `lean_loogle` / `lean_local_search` — Mathlib/project
  name lookup. Scout before writing.
- Reserve `lake build` for the final sanity check.

## Potential Mathlib lookup targets

Use these queries when you get stuck:

- `MonomialOrder.leadingCoeff_sub` / `leadingCoeff_sub_of_degree_lt`
- `MonomialOrder.degree_sub_of_lt`
- `MvPolynomial.coeff_sub`, `MvPolynomial.support_sub`
- `MvPolynomial.X_pow`, `MvPolynomial.support_X`
- `MonomialOrder.div_set`, `MonomialOrder.div_single`
- `MonomialOrder.not_mem_support_of_lt` / similar support lemmas.

## Commit discipline

After `tildeJ_polyT_colon_eq` closes:

1. Update `TODO.md` — sorry count drops to 1 in `BEI/GroebnerDeformation.lean`.
2. Update `FORMALIZATION_MAP.md` — Prop 1.6 row.
3. Update `guides/work_packages/GROEBNER_CM_TRANSFER.md` — mark R1.d ~~struck~~.
4. Update `MEMORY.md` — Sorry Summary and key-files line.
5. `lake build` — final sanity.
6. Commit with focused message (e.g. "Close R1.d via Gröbner colon argument").
7. Push to both `origin` and `github`.

Do **not** auto-commit intermediate progress unless explicitly asked.

## Definition of done

**Best**: `tildeJ_polyT_colon_eq` closed for closed graphs, build green,
Prop 1.6 sorry count in `BEI/GroebnerDeformation.lean` drops to 1.

**Acceptable**: Steps 1–3 closed, Step 4 isolated as a clean named lemma
with Buchberger-style scope, everything below still reduces to that lemma.

**Do not**:
- chase the universe generalization (`K : Type → Type u`);
- restate Cor 3.4 / Cor 3.7 CM branches;
- touch `toMathlib/HeightAdditivity.lean` or
  `toMathlib/GradedCM.lean` (dormant sorries);
- refactor unrelated BEI files.

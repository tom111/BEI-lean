# Work Package: Corollary 3.4 and 3.7 (full CM statements)

## Task

Implement the paper-faithful Cohen–Macaulay statements of Corollaries 3.4 and 3.7.

**Corollary 3.4**: Let `G` be a simple graph on `[n]` with `c` connected
components. If `S / J_G` is Cohen–Macaulay, then `dim(S / J_G) = n + c`.

**Corollary 3.7**: For a cycle `G` of length `n ≥ 3`, the following are
equivalent: (a) `n = 3`, (b) `J_G` is prime, (c) `J_G` is unmixed,
(d) `S / J_G` is Cohen–Macaulay.

Both rest on the same missing bridge. This package closes that bridge, then
wraps 3.4 and 3.7 around the already-proved equidim surrogates.

## Prior attempt

A previous implementation attempt followed an earlier version of this guide
that cited a nonexistent theorem `primeHeight(P) + dim(R/P) = dim R` for CM
local rings. That theorem is **not** in Mathlib and is itself the catenary /
dimension-formula theorem for CM local rings. The previous attempt correctly
stopped rather than land a fake proof.

This rewrite replaces that skeleton with a concrete inductive proof (following
Bruns–Herzog 2.1.2) that uses only primitives already available in Mathlib and
`toMathlib/CohenMacaulay/`.

## The real blocker and how to close it

The missing bridge is the **local** theorem:

```lean
theorem ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R] [Small.{u} R]
    [IsLocalRing R] [IsCohenMacaulayLocalRing R]
    {P : Ideal R} (hP : P ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ P) = ringKrullDim R
```

Global `IsCohenMacaulayRing R → IsEquidimRing R` is **false** for the repo's
local-at-all-primes notion of `IsCohenMacaulayRing` (counterexample `k × k[X]`).
Do not try to prove that.

The correct architecture:

1. prove the **local** theorem above;
2. wrap it into `isEquidimRing_of_isCohenMacaulayLocalRing`;
3. build a **BEI-specific** global bridge, localizing at the augmentation
   maximal ideal, using the fact that every minimal prime of `J_G` is a graded
   prime contained in the augmentation ideal;
4. make `corollary_3_4` a one-line wrapper around `corollary_3_4_equidim`;
5. make `corollary_3_7` wrap 3.4 plus small BEI-combinatorial facts about
   triangles / complete graphs.

## Phase A (hard): the local theorem

Place in
[toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean).

### Proof plan (Bruns–Herzog 2.1.2, specialised)

Induct on `d = ringKrullDim R` for `R` CM local of dim `d`. Prove by induction
the stronger statement:

> For every `R` CM local Noetherian of dim `d`, and every prime `P` with
> `P.primeHeight = 0`, `ringKrullDim (R ⧸ P) = d`.

Use the existing private helper pattern
`unmixedness_of_dim_le` (same file, lines 406–495) as a template — this new
induction has the same shape.

**Base case `d = 0`.** The only prime is the maximal ideal `m`, and
`primeHeight P = 0` forces `P = m`, so `R ⧸ P` has dim 0.

**Step `d > 0`.**

1. **Find a nonzerodivisor `x ∈ m \ ⋃ Ass(R)`.**
   - `Ass(R)` is finite (`associatedPrimes.finite R R`).
   - `m ⊄ ⋃ Ass(R)`: otherwise `m ⊆ p` for some `p ∈ Ass(R)` (prime avoidance
     for primes, `Ideal.subset_union_prime_finite`), so `m = p`, so
     `ringDepth R = 0`, contradicting `depth R = dim R = d > 0`.
   - Extract `x` by the same pattern as in `unmixedness_of_dim_le` (the
     `biUnion_associatedPrimes_eq_compl_regular` + `Set.not_subset` trick).
   - By `biUnion_associatedPrimes_eq_compl_regular`, `x` is `R`-regular
     (`IsSMulRegular R x`).
   - By CM unmixedness (`associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing`),
     every minimal prime of `R` is in `Ass(R)`, so `x ∉ P`.

2. **`R/(x)` is CM local of dim `d - 1`.** Use `isCohenMacaulayLocalRing_quotient`
   (CM quotient by nzd in `m`) and `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`
   (dim drops by exactly 1). `QuotSMulTop x R` is the repo's `R/(x)` notation.

3. **`x̄` is nonzero in `R/P`.** Since `x ∉ P`, the image `x̄ := Ideal.Quotient.mk P x`
   is nonzero. `R ⧸ P` is a domain (`P` is prime), so `x̄` is a nonzerodivisor
   in `R ⧸ P`.

4. **Krull's principal-ideal theorem in `R ⧸ P`.** The ideal `Ideal.span {x̄}`
   in `R ⧸ P` is principal and nonzero. By
   `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`
   (`Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean`), any minimal prime of
   `span {x̄}` has height `≤ 1`. Since `x̄` is nzd in the domain `R ⧸ P`, any
   such minimal prime is nonzero, so height `= 1`.

5. **Height-drop via quotient by `x̄` (the `dim(R/P) - 1` step).**
   `(R ⧸ P) ⧸ span {x̄}` is isomorphic to `R ⧸ (P ⊔ span {x})` and also to
   `(R ⧸ span {x}) ⧸ (P.map (Ideal.Quotient.mk _))`. Any chain of primes in
   `(R ⧸ P) ⧸ span {x̄}` lifts to a chain in `R ⧸ P` strictly above the image
   of `span {x̄}`, so

   ```
   ringKrullDim (R ⧸ P) ≥ ringKrullDim ((R ⧸ P) ⧸ span {x̄}) + 1.
   ```

   This direction is available from `Ideal.primeHeight_add_one_le_of_lt`
   applied along a height-realising chain. (If this exact packaging is
   missing, build a small helper `ringKrullDim_quotient_succ_le_of_nzd` from
   `LTSeries` lengths; ≤ 40 LOC.)

6. **Apply IH inside `R/(x)`.** The ring `R ⧸ span {x}` is CM local of dim
   `d - 1`. The image ideal `P' := P.map (Ideal.Quotient.mk (span {x}))` in
   `R ⧸ span {x}` is some ideal (not necessarily prime), and

   ```
   (R ⧸ span {x}) ⧸ P'  ≃+*  R ⧸ (P ⊔ span {x}).
   ```

   Its dimension is the sup over minimal primes `Q` of `P'` in `R ⧸ span {x}`
   of `ringKrullDim ((R ⧸ span {x}) ⧸ Q)`. For each such `Q`, apply IH to the
   minimal prime of `R ⧸ span {x}` contained in `Q` (minimal primes always
   exist by Noetherian). IH gives that every minimal prime `Q₀` of
   `R ⧸ span {x}` satisfies `ringKrullDim ((R ⧸ span {x}) ⧸ Q₀) = d - 1`, and
   since `Q₀ ⊆ Q` implies `ringKrullDim (… ⧸ Q) ≤ ringKrullDim (… ⧸ Q₀)`, the
   sup is at most `d - 1`. The opposite direction — there **exists** a minimal
   prime with coheight `d - 1` — comes from the fact that `R ⧸ span {x}` has
   dim exactly `d - 1` and dim is attained at some minimal prime's quotient
   (standard: `ringKrullDim_eq_iSup_coheight_minimalPrimes` or inline it from
   an `LTSeries` of length `d-1`).

   Conclusion: `ringKrullDim (R ⧸ (P ⊔ span {x})) ≥ d - 1`. Combined with
   `ringKrullDim (R ⧸ (P ⊔ span {x})) ≤ d - 1` (subquotient of R/(x) which has
   dim d-1), equality.

7. **Combine.** From step 5,
   `ringKrullDim (R ⧸ P) ≥ ringKrullDim (R ⧸ (P ⊔ span {x})) + 1 = (d - 1) + 1 = d`.
   The upper bound `ringKrullDim (R ⧸ P) ≤ d` is immediate
   (`ringKrullDim_quotient_le`). So `ringKrullDim (R ⧸ P) = d`.

### Required helper lemma (small)

Before Phase A main theorem, prove:

```lean
lemma ringKrullDim_eq_of_exists_minimalPrime_coheight
    {R : Type u} [CommRing R] [IsNoetherianRing R] :
    ringKrullDim R =
    sSup ((fun P : Ideal R => ringKrullDim (R ⧸ P)) '' minimalPrimes R)
```

or the packaged form we actually need (existence of a minimal prime achieving
`ringKrullDim R` as its quotient dimension). Prove from `LTSeries` at the
bottom — build chain `⊥ ≤ P_0 ⊊ P_1 ⊊ … ⊊ P_d` starting at a minimal prime
below the bottom of any realising chain.

This is ~40 LOC and is used inside step 6.

### What existing primitives you will use

All public (or easy to make public) in the current repo:

- `associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing`
  (Localization.lean:602)
- `biUnion_associatedPrimes_eq_compl_regular` (Mathlib)
- `Ideal.subset_union_prime_finite` (Mathlib)
- `associatedPrimes.finite` (Mathlib)
- `isCohenMacaulayLocalRing_quotient` (Localization.lean:350, already public)
- `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim` (Mathlib)
- `IsSMulRegular` API (Mathlib)
- `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` (Mathlib)
- `Ideal.Quotient.mk` + `DoubleQuot.quotQuotEquivQuotSup` (Mathlib)
- `ringKrullDim_quotient_le` (Mathlib)
- `Ideal.primeHeight_add_one_le_of_lt` (Mathlib)

## Phase B (tiny): equidim wrapper

Also in
[toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean)
— add an import of `toMathlib/Equidim/Defs.lean` if it does not already flow
through. If imports tangle, create
[toMathlib/Equidim/CohenMacaulay.lean](/home/tom/BEI-lean/toMathlib/Equidim/CohenMacaulay.lean)
and put the wrapper there.

```lean
theorem isEquidimRing_of_isCohenMacaulayLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [Small.{u} R]
    [IsLocalRing R] [IsCohenMacaulayLocalRing R] :
    IsEquidimRing R := by
  refine ⟨?_⟩
  intro P Q hP hQ
  exact (ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes hP).trans
        (ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes hQ).symm
```

## Phase C (medium): BEI-specific global bridge

Place in
[BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean).

```lean
theorem binomialEdgeIdeal_isEquidim_of_isCohenMacaulay
    (G : SimpleGraph V)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    IsEquidimRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)
```

Route via localization at the augmentation maximal ideal:

1. Let `A := S ⧸ J_G` where `S := MvPolynomial (BinomialEdgeVars V) K` and
   `J_G := binomialEdgeIdeal (K := K) G`.
2. Let `mA` be the image in `A` of the augmentation maximal ideal of `S`
   (the kernel of `MvPolynomial.eval 0`). `mA` is maximal because
   `A ⧸ mA ≃+* K` — `J_G` sits inside the augmentation ideal since every
   generator `x_i y_j - x_j y_i` has zero constant term. Reuse the existing
   augmentation-ideal machinery from `BEI/Equidim.lean`.
3. From `IsCohenMacaulayRing A`, obtain `IsCohenMacaulayLocalRing (A_mA)`
   via `IsCohenMacaulayRing.CM_localize mA`.
4. Apply `isEquidimRing_of_isCohenMacaulayLocalRing` to `A_mA`.
5. **Transfer equidim from `A_mA` back to `A`.** This is the delicate step.
   It works because every minimal prime of `A` is a graded prime (minimal
   primes of any graded ideal in a graded ring are graded; `J_G` is generated
   by homogeneous degree-2 elements). Every graded prime of `A` is contained
   in `mA` (graded primes of a graded connected K-algebra lie below the
   irrelevant max).

   Consequently:
   - the map `minimalPrimes A → minimalPrimes A_mA` given by extension
     `P ↦ P · A_mA` is a bijection (using that all min primes are already
     contained in `mA`);
   - `ringKrullDim (A ⧸ P) = ringKrullDim (A_mA ⧸ P · A_mA)` for each minimal
     prime `P` (localization at `mA` preserves the quotient dimension because
     `A ⧸ P` is a graded domain whose dim equals the dim of its localization
     at the irrelevant max).

   If the “localization at irrelevant max preserves quotient dim for graded
   domains” step is not already available, borrow the identical pattern we
   used in `BEI/GroebnerDeformation.lean` / `toMathlib/GradedCM.lean` for the
   graded local-to-global proof of Case C. Do not rebuild a broad graded
   framework; reuse.

## Phase D (one line): Corollary 3.4

```lean
theorem corollary_3_4 (G : SimpleGraph V)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    Fintype.card V + componentCount G ∅ := by
  exact corollary_3_4_equidim (K := K) G
    (binomialEdgeIdeal_isEquidim_of_isCohenMacaulay (K := K) G hCM)
```

Do not rename `corollary_3_4_equidim`. Keep both around.

## Phase E (small): Corollary 3.7

Four implications; three of the four are free given Phase A–D:

| Direction | Proof |
|---|---|
| (a) ⇒ (b) | `n = 3` cycle is `K_3`; use `SimpleGraph.completeGraph` and `prop_3_6` (prime iff each component complete) |
| (b) ⇒ (c) | Prime ideals are trivially unmixed (only one minimal prime) |
| (c) ⇒ (a) | **Reuse existing `corollary_3_7_equidim`**: unmixed → equidim surrogate → `n = 3` |
| (a) ⇒ (d) | `K_3` is closed and satisfies Prop 1.6's transitivity vacuously (`complete_graph_satisfiesProp1_6Condition`); apply `proposition_1_6` |
| (d) ⇒ (c) | `corollary_3_4`-style: CM → equidim (via Phase C) → unmixed |

“Unmixed” at the abstract level should be stated as “all minimal primes have
the same quotient dim” — i.e., identical to `IsEquidimRing` for this repo.
Do not invent a new `IsUnmixed` class unless truly required; if the paper
asks for `Ass = Min`, state the TFAE via `IsEquidimRing` and give a remark.

Place in
[BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean),
next to `corollary_3_7_equidim`. Keep `corollary_3_7_equidim` too.

New helpers probably needed:

- `completeGraph_isClosedGraph` (if missing) — complete graphs are trivially
  closed.
- `completeGraph_satisfiesProp1_6Condition` — the transitivity condition is
  vacuous for `K_n` because all pairs are adjacent.
- `cycle_length_three_iff_completeGraph_fin_three` or equivalent — cycle on
  `Fin 3` is `K_3`.

All of these are small.

## What not to do

- Do not “solve” 3.4 or 3.7 by specializing to Prop 1.6 graphs.
  `proposition_1_6_dim_formula` is not the general Section 3 statement.
- Do not rename `corollary_3_4_equidim` / `corollary_3_7_equidim`. Keep both.
- Do not attempt a global `IsCohenMacaulayRing R → IsEquidimRing R`. False.
- Do not attempt a global `IsCohenMacaulayRing → IsUnmixed`. False.
- Do not bring in a broad new catenary / Hilbert-series / graded-algebra
  theory. The BH induction and graded localization described above suffice.
- Do not land `sorry` placeholders. If a sub-step in Phase A step 5 or 6 is
  stuck, write a focused question in `questions/` rather than a fake proof.

## Existing declarations you should use

From
[BEI/PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean):

```lean
theorem minimalPrimes_characterization (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).minimalPrimes =
    { P | ∃ S : Finset V,
        P = primeComponent (K := K) G S ∧
        ∀ T : Finset V, primeComponent (K := K) G T ≤ primeComponent (K := K) G S →
          primeComponent (K := K) G S ≤ primeComponent (K := K) G T }
```

From
[BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean):

```lean
theorem corollary_3_4_equidim (G : SimpleGraph V)
    (hEq : IsEquidim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    Fintype.card V + componentCount G ∅

theorem corollary_3_7_equidim (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    IsEquidim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) ↔
    (binomialEdgeIdeal (K := K) G).IsPrime

theorem ringKrullDim_quot_primeComponent (G : SimpleGraph V) (S : Finset V) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸
      primeComponent (K := K) G S) =
    (Fintype.card V - S.card + componentCount G S : ℕ)
```

From
[BEI/Proposition1_6.lean](/home/tom/BEI-lean/BEI/Proposition1_6.lean):

```lean
theorem proposition_1_6
theorem pathGraph_satisfiesProp1_6Condition
```

From
[BEI/Equidim.lean](/home/tom/BEI-lean/BEI/Equidim.lean):
augmentation ideal constructors; localisation-at-augmentation API used in the
HH CM theorem proof. Reuse patterns, don't rebuild.

From
[toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean):

```lean
theorem associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing
theorem isCohenMacaulayLocalRing_quotient      -- already public
theorem isCohenMacaulayLocalRing_localization_atPrime
theorem IsCohenMacaulayRing.CM_localize
theorem IsCohenMacaulayRing.of_isCohenMacaulayLocalRing
```

## Verification

```bash
lake build toMathlib.CohenMacaulay.Localization
lake build BEI.PrimeDecompositionDimension
```

If imports change:

```bash
lake build
```

`#print axioms` checks on the new public theorems:

- `ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes`
- `isEquidimRing_of_isCohenMacaulayLocalRing`
- `binomialEdgeIdeal_isEquidim_of_isCohenMacaulay`
- `corollary_3_4`
- `corollary_3_7`

Expected: `{propext, Classical.choice, Quot.sound}` throughout. No `sorryAx`.

## Success condition

Repo contains, with clean axioms:

1. the local CM theorem `ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes`;
2. the wrapper `isEquidimRing_of_isCohenMacaulayLocalRing`;
3. the BEI-specific global bridge
   `binomialEdgeIdeal_isEquidim_of_isCohenMacaulay`;
4. paper-faithful `corollary_3_4`;
5. paper-faithful `corollary_3_7`;
6. existing `corollary_3_4_equidim` and `corollary_3_7_equidim` preserved;
7. status docs (`TODO.md`, `FORMALIZATION_MAP.md`, `MEMORY.md`) updated.

## Scope discipline

- Phase A is the real mathematical work (~250–350 LOC). Phases B, C, D, E are
  plumbing.
- Do not bundle speculative cleanup with this change.
- Commit in the natural order: Phase A first (self-contained in `toMathlib`),
  then Phase C (BEI bridge), then Phases D+E (paper-facing theorems + status
  doc updates).
- If Phase A step 6 or step 5 turns out harder than the sketch above, write a
  focused question in `questions/` naming the exact sublemma that is stuck.
  Do not silently broaden scope.

# Guide: Gröbner CM Transfer for Proposition 1.6 (Step 2)

## Task

Transfer Cohen–Macaulayness from the initial-ideal quotient back to the
original ideal quotient:

```text
S ⧸ in_<(J_G) is CM   ⟹   S ⧸ J_G is CM.
```

This is the second paper-critical gap for the full formalization of
Proposition 1.6. Step 1 (monomial-side CM via HH) is done as of 2026-04-20
(`monomialInitialIdeal_isCohenMacaulay` in `BEI/Equidim.lean`). The input of
Step 2 is therefore already available; only the transfer theorem is missing.

## What we already have

- `monomialInitialIdeal_isCohenMacaulay`: `S ⧸ monomialInitialIdeal G` is CM
  under HH conditions (`K : Type`).
- `initialIdeal_closed_eq`: for closed `G`,
  `Ideal.span (binomialEdgeMonomialOrder.leadingTerm '' J_G) = monomialInitialIdeal G`.
- `closed_implies_groebner`: the quadratic generators form a Gröbner basis.
- Dimension equality `dim(S/J_G) = dim(S/in_<(J_G)) = n + 1` under HH conditions
  (via `ringKrullDim_bipartiteEdgeMonomialIdeal` + `prop_1_6_equidim`).
- A fairly complete local CM infrastructure in `toMathlib/CohenMacaulay/`:
  `ringDepth`, `IsCohenMacaulayLocalRing`, `IsCohenMacaulayRing`, forward and
  backward CM transfer along `RingEquiv`, CM localizes, local-to-global
  wrapper, polynomial CM (Mathlib PR #28599 slice backported).

## What Mathlib does NOT have (as of 2026-04-20)

- No `Module.depth` or `ringDepth` — only our local `toMathlib/CohenMacaulay/Defs.lean`.
- No `initialIdeal : Ideal (MvPolynomial σ K) → MonomialOrder σ → Ideal (...)`.
  Only `MonomialOrder.leadingCoeff` / `leadingTerm` on individual polynomials.
- No Rees-style one-parameter deformation to the initial ideal. `Mathlib.RingTheory.ReesAlgebra`
  only supplies the classical `I^n t^n` Rees algebra.
- No flat-family / one-parameter-deformation API.
- No semicontinuity of depth for flat families.
- No Conca–Varbaro squarefree-degeneration theorem.
- No "flat local with CM fibers" preservation theorem.

## What Mathlib / `toMathlib/` DOES have that shortens R1

An audit on 2026-04-20 found the following reusable infrastructure. The picture
for R1 is substantially better than the raw gap list above suggests — **depth
semicontinuity can be bypassed** for R1 in favour of the graded
local-to-global + regular-quotient route (which is the classical elementary
proof anyway).

### Mathlib-side

- `Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous` —
  `weightedTotalDegree`, `IsWeightedHomogeneous`, `weightedHomogeneousSubmodule`,
  `weightedHomogeneousComponent`, and a substantial lemma library. Covers what
  R1.c (order-homogenization of polynomials) needs at the level of individual
  polynomials; the ideal-level wrapping is new but thin.
- `Mathlib.RingTheory.Regular.Flat` — `IsWeaklyRegular.of_flat`,
  `IsWeaklyRegular.of_flat_of_isBaseChange`. This is the exact package that
  converts "`K[t] → B` is flat" into "any `K[t]`-regular sequence is `B`-regular",
  and in particular "`t` regular on `K[t]` lifts to `t` regular on `B`".
- Standard grading on `MvPolynomial` via `Mathlib.RingTheory.MvPolynomial.Homogeneous`.

### `toMathlib/` side

- `isCohenMacaulayLocalRing_of_regular_quotient`
  (`toMathlib/CohenMacaulay/Basic.lean:166`) — **exactly** the local-side
  lifting theorem needed in R1: if `x ∈ m` is regular and `R ⧸ xR` is CM local,
  then `R` is CM local.
- `isCohenMacaulayRing_quotient_of_smulRegular`
  (`toMathlib/CohenMacaulay/Polynomial.lean:578`, private) — **exactly** the
  global-side descent theorem needed in R1: if `R` is a global CM Noetherian
  ring and `a : R` is regular, then `R ⧸ (a)` is a global CM ring. It is
  currently `private`; R1 will need to either expose it or replay its one-page
  proof.
- `toMathlib/GradedCM.lean` —
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`: for a
  connected ℕ-graded Noetherian `K`-algebra, local CM at the irrelevant ideal
  implies global CM. **One remaining sorry in the non-homogeneous prime case
  (Case C)**; the homogeneous-prime case is proved.
- `toMathlib/GradedQuotient.lean`, `toMathlib/GradedIrrelevant.lean` — grading
  on quotients by homogeneous ideals; irrelevant-ideal maximality; homogeneous
  core below irrelevant. These are exactly the ingredients used by the
  homogeneous-prime case of `GradedCM`.
- `toMathlib/CohenMacaulay/Localization.lean` — forward CM transfer,
  unmixedness, CM localizes, and the local-ring global-CM wrapper. Already
  used in Step 1; reusable without changes.

### Consequence: the revised R1 shape

The classical Eisenbud 15.17 proof via depth semicontinuity is **not** what R1
has to formalize. The reusable shape is:

```text
S/in_<(J_G) CM    ──(regular-quotient lift)──▶    S[t]/Ĩ CM at irrelevant
                  ──(graded local-to-global)──▶   S[t]/Ĩ CM globally
                  ──(flatness ⇒ t-1 regular)──▶   t-1 is NZD on S[t]/Ĩ
                  ──(quotient by regular)──▶     S/J_G = S[t]/Ĩ ⧸ (t-1) CM
```

No step in this chain requires depth semicontinuity. The heavy lifting is
concentrated on **flatness of `S[t] ⧸ Ĩ` over `K[t]`**; everything else is a
short composition of existing tools.

Every algebraic building block that remains must still be built in `toMathlib/`,
but the net line-count for R1 drops substantially.

## Candidate routes

### Route R1: graded local-to-global + regular-quotient (revised 2026-04-20)

This is the classical elementary proof of Eisenbud 15.17 for the case where
the flat family `S[t] ⧸ Ĩ` can be organized as a standard ℕ-graded
`K`-algebra. The audit below shows that for the BEI Gröbner deformation this
organization is available and that **depth semicontinuity is not required** —
it is replaced by a composition of local CM lifting through a regular element
and global CM descent through a regular element, both of which are already
formalized in this repository.

**Chain to prove**:

```text
S ⧸ in_<(J_G) CM   ──(regular-quotient lift at irrelevant)──▶
S[t] ⧸ Ĩ CM at the irrelevant ideal                         ──(graded L-to-G)──▶
S[t] ⧸ Ĩ CM globally                                         ──(flatness over K[t])──▶
t-1 is regular on S[t] ⧸ Ĩ                                   ──(regular-quotient descent)──▶
S ⧸ J_G = (S[t] ⧸ Ĩ) ⧸ (t-1) CM globally
```

**Reusable infrastructure (already present, no new work needed)**:

- `isCohenMacaulayLocalRing_of_regular_quotient`
  (`toMathlib/CohenMacaulay/Basic.lean:166`) closes the first arrow.
- `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`
  (`toMathlib/GradedCM.lean:433`) closes the second arrow, modulo one
  pre-existing sorry in the non-homogeneous-prime Case C.
- `IsWeaklyRegular.of_flat` (`Mathlib.RingTheory.Regular.Flat`) closes the
  third arrow once flatness is established.
- `isCohenMacaulayRing_quotient_of_smulRegular`
  (`toMathlib/CohenMacaulay/Polynomial.lean:578`, currently `private`)
  closes the fourth arrow.
- `Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous` provides
  `IsWeightedHomogeneous`, `weightedTotalDegree`, and
  `weightedHomogeneousComponent` for R1.c.

**New prerequisites to build in `toMathlib/`**:

- **R1.a** — `MonomialOrder.inIdeal` wrapper on an ideal. ~30 lines.
  Defines `Ideal.span (ord.leadingTerm '' (I : Set _))`. For the BEI
  application specifically, `initialIdeal_closed_eq` plus `monomialInitialIdeal`
  already supply the concrete ideal; this wrapper is only needed if the R1
  theorem is stated generically.

- **R1.b** — weight vector realizing `binomialEdgeMonomialOrder`, or at
  minimum a weight-grading under which `fij i j = x_i y_j - x_j y_i` admits a
  `t`-homogenization whose `t = 0` specialization is `x_i y_j`. The paper
  uses the standard choice: assign weights so `x_i y_j` strictly dominates
  `x_j y_i` for `i < j`, e.g. `w(x_i) = n - i`, `w(y_j) = -j` (or any
  refinement of lex). ~50–150 lines.

- **R1.c** — `t`-homogenization of `fij` and of the ideal. Concretely:
  `f̃_{i,j} := x_i y_j - t · x_j y_i ∈ S[t]`, and
  `Ĩ := Ideal.span {f̃_{i,j} : edges, i < j} ⊂ S[t]`. Builds on Mathlib's
  `WeightedHomogeneous` for the polynomial-level proofs. ~100–200 lines.

- **R1.d** — flatness of `S[t] ⧸ Ĩ` over `K[t]`, or equivalently
  `IsSMulRegular (S[t] ⧸ Ĩ) t`. **This is the technical heart of R1.**
  Classical proofs:

  - *Via reduced Gröbner basis + normal forms*: since
    `{x_i y_j - x_j y_i : edges, i < j}` is a reduced Gröbner basis of `J_G`,
    the `t`-graded version `{f̃_{i,j}}` is a Gröbner basis in `S[t]` whose
    leading terms `x_i y_j` contain no `t`, so division by `t` terminates in
    `S[t] ⧸ Ĩ` — giving `t` is NZD.
  - *Via Hilbert series*: `S[t] ⧸ Ĩ` has the same Hilbert series as
    `(S ⧸ J_G)[t]` in both the generic and special fibers, so flatness is
    forced by dimension-counting.

  Either proof is substantial and specific to the BEI reduced GB. Realistic
  estimate: ~300–700 lines.

- **R1.e** — fiber identification:
  `S[t] ⧸ (Ĩ + (t-1)S[t]) ≃ S ⧸ J_G` and
  `S[t] ⧸ (Ĩ + t·S[t]) ≃ S ⧸ monomialInitialIdeal G` as rings. Both reduce
  to generator-level computations in `S[t]`. ~100–200 lines.

- **R1.f** — apply the four-step chain. ~50–100 lines, assuming R1.a–e.
  Sub-steps:

  1. `S[t] ⧸ Ĩ` is Noetherian finitely-generated `K`-algebra with standard
     ℕ-grading induced from the weight; irrelevant ideal is `(x, y, t)`.
  2. Local CM at irrelevant: the regular-quotient-lift via `t` reduces to
     local CM of the `t = 0` specialization, which is `S ⧸ monomialInitialIdeal G`
     at its own irrelevant ideal; the latter is an instance of Step 1
     (`monomialInitialIdeal_isCohenMacaulay`) at its irrelevant prime.
  3. Graded local-to-global: feed the result into
     `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`. This is
     where the `GradedCM.lean` Case-C sorry would become load-bearing; if that
     sorry is still open when R1 lands, R1 inherits it. Either close Case C
     (heavy) or take a narrower global-CM path that stays in the homogeneous-
     prime case (likely possible since we only need CM at primes that contain
     `(t)` or `(t-1)`, and those primes are "graded enough").
  4. Flatness ⇒ `(t-1)` regular ⇒ `S ⧸ J_G` CM via
     `isCohenMacaulayRing_quotient_of_smulRegular`.

**Total R1 (revised)**: ~600–1400 lines, with R1.d holding most of the
weight. The previous estimate (1100–2400 lines including a full depth
semicontinuity backport) is superseded.

**Mathlib reusability**: R1.a–c and the small flatness specializations of
R1.d are upstreamable to Mathlib; R1.e is specific to BEI; R1.f is BEI
assembly.

**Dependency on the `GradedCM.lean` Case-C sorry**: this is the one
pre-existing open item R1 touches. Two honest options:

  1. Close Case C (nontrivial — see that file's own status notes).
  2. Replace the graded local-to-global step with a bespoke argument that
     only uses the homogeneous-prime half (a.k.a. Case A + Case B) plus the
     fact that primes of `S[t] ⧸ Ĩ` containing `(t)` or `(t-1)` lie in the
     homogeneous locus we can handle. Likely viable for the BEI deformation,
     but needs a small separate lemma.

### Route R2: Conca–Varbaro squarefree degeneration

**Statement to prove** (Conca–Varbaro, *Squarefree Gröbner degenerations*,
Invent. Math. 2020):

```text
If in_<(I) is squarefree, then S/I and S/in_<(I) have the same
(graded) Betti numbers over S. In particular
  depth(S/I) = depth(S/in_<(I)),
  projdim(S/I) = projdim(S/in_<(I)).
```

Combined with `dim(S/I) = dim(S/in_<(I))` (already in hand for BEI), CM
transfers.

**Classical proof sketch**: reduction to positive characteristic, F-purity of
squarefree monomial rings (Fedder's criterion), a Frobenius-stable flat
family argument.

**Prerequisites to build in `toMathlib/`**:

- squarefree monomial ideals are F-pure in char p;
- Frobenius-stable degeneration preserves depth;
- lifting from char p back to char 0.

All of this is genuinely hard. No Mathlib support for F-purity, Frobenius
splitting, or reduction mod p exists.

**Total R2**: likely larger than R1 once you count the F-purity machine.
Not recommended.

### Route R3: direct regular sequence on `S ⧸ J_G`

Bypass Gröbner transfer entirely. The HH proof constructed an explicit
regular sequence of length `n + 1 = dim` on `S ⧸ bipartiteEdgeMonomialIdeal G`
(diagonal sums + two free variables). Attempt the analogous construction
directly on `S ⧸ J_G`.

**Prerequisites**:

- identify candidate elements in `S ⧸ J_G` (lifts of the HH diagonal sums);
- verify they form a regular sequence of length `n + 1`;
- verify the quotient is Artinian (dim 0).

**Pros**: avoids Gröbner deformation entirely; reuses the HH regularity
infrastructure; stays inside the BEI combinatorics.

**Cons**:

- the HH proof is written for the monomial side; transferring each NZD
  step to the binomial side may fail — the whole point of the Gröbner
  argument in the paper is that the monomial side is easier;
- each NZD step on the binomial side becomes a nontrivial commutative-algebra
  statement about the quotient by a collection of `2 × 2` minors.

**Effort**: unclear. Could be shorter than R1 *or* could stall. High
variance.

### Route R4: axiomatize the transfer, apply to BEI

State the minimal missing CM-transfer theorem as an axiom (or a lemma with
`sorry`), use it to close Proposition 1.6 cleanly, and separately pursue
R1/R2/R3 as follow-up work.

**Statement of the axiom** (narrow BEI form):

```lean
theorem groebner_cm_transfer
    {K : Type} [Field K]
    {σ : Type*} [Fintype σ] [DecidableEq σ] [LinearOrder σ]
    (ord : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K))
    (hCM : IsCohenMacaulayRing (MvPolynomial σ K ⧸ inIdeal ord I)) :
    IsCohenMacaulayRing (MvPolynomial σ K ⧸ I)
```

Or even narrower, specialized to BEI:

```lean
theorem binomialEdgeIdeal_cm_of_initialIdeal_cm
    {K : Type} [Field K] {n : ℕ} {G : SimpleGraph (Fin n)}
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G)
```

**Pros**: unblocks the paper-faithful `proposition_1_6` assembly (Step 3)
immediately; makes the exact gap precise and visible; Mathlib-wide progress
on depth semicontinuity can later turn this into a theorem.

**Cons**: a `sorry` in the critical path. Must be loudly flagged, not buried.

**Effort**: ~50 lines to state + ~100–200 lines to assemble Step 3 on top.

## Recommendation

The honest picture: **R1 is the right long-term target. After the 2026-04-20
audit, its scale is substantially smaller than originally estimated** —
~600–1400 lines, concentrated in the flatness of the BEI Gröbner deformation
`S[t] ⧸ Ĩ` over `K[t]`. Depth semicontinuity is not needed; everything else
is either already formalized (regular-quotient lift and descent, graded
local-to-global modulo one pre-existing sorry) or routine
(`WeightedHomogeneous` plumbing).

Recommended sequencing:

1. **Immediately: Route R4** (narrow axiomatized transfer) to unblock Step 3
   and state the paper-faithful `proposition_1_6` behind one clearly
   documented `sorry`. This takes ~1 session.
2. **Next: Route R1** as a long project. The natural first sub-deliverable
   is R1.a + R1.b + R1.c (initial-ideal API + order-homogenization), which
   is self-contained and Mathlib-upstreamable independently of the CM transfer.
3. **Do not pursue R2 or R3** unless R1 hits a concrete blocker. R2's F-purity
   machine is heavier than R1's semicontinuity machine; R3 trades a
   well-understood classical theorem for an unknown amount of BEI-specific
   commutative algebra.

## Detailed plan for R4 (the immediate next round)

### R4.1 — build the `initialIdeal` wrapper (~30 lines)

In `BEI/Groebner.lean` or a new `toMathlib/MonomialOrder/InitialIdeal.lean`:

```lean
/-- The initial (leading-term) ideal of `I` under the given monomial order. -/
def MonomialOrder.inIdeal {σ : Type*} {R : Type*} [CommRing R]
    (ord : MonomialOrder σ) (I : Ideal (MvPolynomial σ R)) :
    Ideal (MvPolynomial σ R) :=
  Ideal.span (ord.leadingTerm '' (I : Set _))
```

One small lemma: for closed `G`,
`binomialEdgeMonomialOrder.inIdeal (binomialEdgeIdeal G) = monomialInitialIdeal G`
— this is exactly `initialIdeal_closed_eq`, reshaped.

### R4.2 — state the narrow BEI transfer as a named sorry (~30 lines)

In a new `BEI/GroebnerCMTransfer.lean`:

```lean
/-- Gröbner CM transfer for the binomial edge ideal. Currently unproved; tracks
the Eisenbud 15.17 / depth-semicontinuity content of Proposition 1.6. -/
theorem binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm
    {K : Type} [Field K] {n : ℕ} {G : SimpleGraph (Fin n)}
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G)) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) := by
  sorry
```

Flag this prominently: it is the one remaining paper-critical sorry.

### R4.3 — assemble `proposition_1_6` (~50 lines)

In `BEI/Proposition1_6.lean` (new) or appended to
`BEI/PrimeDecompositionDimension.lean`:

```lean
theorem proposition_1_6
    {K : Type} [Field K] {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) := by
  have hHH := prop_1_6_herzogHibi G hConn hClosed hCond
  have hIn := monomialInitialIdeal_isCohenMacaulay hn hHH
  exact binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm hIn
```

### R4.4 — update status docs (~same round)

- `TODO.md`: Prop 1.6 now `[!]` with one clearly marked sorry.
- `FORMALIZATION_MAP.md`: Prop 1.6 fidelity `Sorry` with explicit pointer.
- `guides/INDEX.md`: update.
- This guide: record R4 as landed, R1 as open.

### R4.5 — corollary refresh (~30 lines, optional, can be deferred)

Restate `corollary_3_4` and the CM branch of `corollary_3_7` in real CM
terms rather than equidimensional surrogate; both follow formally from
`proposition_1_6`.

## Detailed plan for R1 (revised 2026-04-20)

The revised plan replaces depth semicontinuity with a four-arrow chain
that reuses the repo's existing CM infrastructure. Numbering below follows
the chain in the overview.

### R1.a — `inIdeal` wrapper (~30 lines, optional)

Only needed if R1 is stated at Mathlib generality. For the BEI-specific
application, `monomialInitialIdeal G` together with `initialIdeal_closed_eq`
already play the role of `binomialEdgeMonomialOrder.inIdeal (binomialEdgeIdeal G)`.
Writing the wrapper is easy and is a natural Mathlib upstream target
independently of the CM transfer.

### R1.b — weight / `t`-grading setup (~50–150 lines)

Pick a weight vector `w : BinomialEdgeVars (Fin n) → ℕ` under which every
binomial generator `fij i j = x_i y_j - x_j y_i` (with `i < j`) has the
property `w(x_i y_j) > w(x_j y_i)`. Any refinement of `binomialEdgeMonomialOrder`
by a positive weight works; the simplest choice is a weight that strictly
orders the monomials on each generator.

Extend the grading to `S[t] := MvPolynomial (BinomialEdgeVars (Fin n) ⊕ Unit) K`
with `w(t) = 1` (or the unique value that makes each `f̃_{i,j}` weighted-homogeneous).
Everything needed at the polynomial level is in
`Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous`.

### R1.c — `t`-homogenization of the BEI generators (~100–200 lines)

Define

```lean
def fijTilde (i j : Fin n) (hij : i < j) : MvPolynomial (BinomialEdgeVars (Fin n) ⊕ Unit) K :=
  X (Sum.inl (Sum.inl i)) * X (Sum.inl (Sum.inr j))
    - X (Sum.inr ()) * X (Sum.inl (Sum.inl j)) * X (Sum.inl (Sum.inr i))
```

(or however the variable indexing is set up for `S[t]`) and

```lean
def tildeJ (G : SimpleGraph (Fin n)) : Ideal (MvPolynomial (BinomialEdgeVars (Fin n) ⊕ Unit) K) :=
  Ideal.span { f̃ | ∃ i j (hij : i < j), G.Adj i j ∧ f̃ = fijTilde i j hij }
```

Prove:

- `Ĩ` is weighted-homogeneous of degree 2;
- `S[t] ⧸ (Ĩ + (t - 1)·S[t]) ≃ S ⧸ J_G` (R1.e item 1);
- `S[t] ⧸ (Ĩ + t·S[t]) ≃ S ⧸ monomialInitialIdeal G` (R1.e item 2).

R1.c and R1.e are tightly coupled. The identifications are generator-level
substitutions; the only subtlety is that the `t = 0` side must yield the
squarefree monomial ideal, which requires noting that every term dropped by
the substitution is already a leading term in the reduced GB.

### R1.d — flatness of `S[t] ⧸ Ĩ` over `K[t]` (~300–700 lines)

**The technical heart of R1.** Equivalent formulations, pick one:

- `t` is NZD on `S[t] ⧸ Ĩ`. Since `K[t]` is a PID and `S[t] ⧸ Ĩ` is
  finitely generated, flatness ⟺ torsion-free ⟺ every generator of the
  maximal ideal of `K[t]` is NZD, and `K[t]` has principal maximal ideals
  `(t - a)`. Actually for global flatness we need `t - a` NZD for *every* `a`,
  but because `S[t] ⧸ Ĩ` is a finitely generated `K[t]`-algebra in one
  variable, flatness follows from NZD-ness of `t` alone combined with
  `K`-finiteness of each graded component. Spell this out carefully.

- Alternative: directly construct a `K[t]`-basis of `S[t] ⧸ Ĩ` via the
  standard-monomial normal form associated to the reduced Gröbner basis of
  `J_G`. The `K[t]`-basis consists of the standard monomials of `J_G`, each
  multiplied by arbitrary `K[t]`-coefficients; this is exactly the content of
  the "fundamental Gröbner basis theorem for deformations" that Eisenbud 15.17
  formalizes.

Needs, for whichever formulation:

- division algorithm for `MvPolynomial (σ ⊕ Unit) K`-polynomials under the
  lifted weighted order;
- normal-form uniqueness for the reduced GB;
- finiteness of each graded component.

Half of this infrastructure is already in `BEI/GroebnerAPI.lean` and
`BEI/GroebnerBasis.lean` for `J_G` itself; the technical new work is
lifting it to `S[t]`.

### R1.e — fiber identification (~100–200 lines)

Already sketched in R1.c. Uses `Ideal.quotientEquiv` and the quotient of
`S[t]` by `t` (resp. `t - 1`) being `S`.

### R1.f — assembly of the four-arrow chain (~100–200 lines)

```lean
-- Step F1: local CM of S[t] ⧸ Ĩ at its irrelevant ideal.
-- Step 1 gives S ⧸ monomialInitialIdeal G CM globally, hence CM at its
-- irrelevant ideal. By R1.d/R1.e, S[t] ⧸ Ĩ ⧸ (t) ≃ S ⧸ monomialInitialIdeal G
-- and t is regular on S[t] ⧸ Ĩ. So
-- isCohenMacaulayLocalRing_of_regular_quotient gives CM at the irrelevant
-- ideal of S[t] ⧸ Ĩ.

-- Step F2: global CM of S[t] ⧸ Ĩ.
-- Feed F1 into isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant
-- (requires the graded structure from R1.b and, strictly, the GradedCM
-- Case-C sorry; see the "dependency" note below).

-- Step F3: (t-1) is regular on S[t] ⧸ Ĩ.
-- By R1.d, S[t] ⧸ Ĩ is flat over K[t]; (t-1) is regular on K[t], so
-- by IsWeaklyRegular.of_flat it is regular on S[t] ⧸ Ĩ.

-- Step F4: S ⧸ J_G CM.
-- By R1.e, S ⧸ J_G ≃ S[t] ⧸ Ĩ ⧸ (t-1). Apply
-- isCohenMacaulayRing_quotient_of_smulRegular (which may need to be
-- un-privated first, or its proof replayed).
```

### Dependency on `toMathlib/GradedCM.lean`

Step F2 uses the graded local-to-global CM theorem, which currently has one
dormant sorry in the non-homogeneous-prime case (Case C). Two options:

- **R1.f-a**: close the Case C sorry. This was deliberately left open when
  the F2 route for the HH-side global CM theorem (2026-04-20) picked a
  bespoke alternative to this theorem. A fresh attempt is a separate
  multi-session project.
- **R1.f-b**: avoid the dependency. All primes of `S[t] ⧸ Ĩ` that we actually
  need CM at are either in the homogeneous locus or contain one of `(t)` /
  `(t-1)`. In the latter case, a direct regular-quotient argument gives CM
  without invoking Case C at all. This is likely a cleaner path.

### R1.g — apply to `J_G` (~50 lines)

Combine R1.a–f. Replace the `sorry` in
`binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm`.

## False routes to avoid

- Presenting an equidimensionality transfer as a CM transfer.
- Assuming Mathlib has depth semicontinuity or CM-under-flat results — it
  does not (verified 2026-04-20).
- Starting R2 (F-purity) without a concrete reason to prefer it over R1.
- Letting R3 stall into an open-ended regular-sequence hunt on `S ⧸ J_G`.
- Using R4 as the long-term ending state without a follow-up plan for R1.

## Definition of done

**R4 (immediate)**: `proposition_1_6` stated and proved modulo exactly one
named `sorry` (`binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm`), with the
gap documented in this guide, `TODO.md`, and `FORMALIZATION_MAP.md`.

**R1 (long-term)**: that named `sorry` closed via the graded-local-to-global
route, with the prerequisite infrastructure (weighted homogenization of the
BEI deformation, flatness of `S[t] ⧸ Ĩ` over `K[t]`, fiber identification)
landed in `toMathlib/` and/or `BEI/`. Depth semicontinuity is not required.

## Status

- R4.1 (`inIdeal` wrapper): deferred — `monomialInitialIdeal` + `initialIdeal_closed_eq`
  already suffice for the narrow form of R4.2, so no generic wrapper was added.
- R4.2 (narrow BEI transfer as named sorry): **DONE 2026-04-20** —
  `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm` in `BEI/Proposition1_6.lean`.
- R4.3 (`proposition_1_6` assembly): **DONE 2026-04-20** —
  `proposition_1_6` in `BEI/Proposition1_6.lean` combines
  `prop_1_6_herzogHibi`, `monomialInitialIdeal_isCohenMacaulay`, and
  `binomialEdgeIdeal_cm_of_monomialInitialIdeal_cm`.
- R1 framework (deformation ring, deformed generators, fiber identifications,
  assembly chain): **DONE 2026-04-20** — `BEI/GroebnerDeformation.lean`.
  - `DefRing`, `tDef`, `baseInclude`, `specZero`, `specOne`: deformation
    ring and specialization maps.
  - `fijTilde`, `tildeJ`: deformed generators and ideal.
  - `tildeJ_specZero_eq`, `tildeJ_specOne_eq`: fiber identifications PROVED.
  - `binomialEdgeIdeal_le_baseInclude_comap_sup`: kernel containment for the
    backward iso direction PROVED.
  - `groebnerDeformation_cm_transfer`: the four-arrow assembly PROVED
    modulo three sub-sorries.
  - `BEI/Proposition1_6.lean`'s sorry is now reduced to
    `:= groebnerDeformation_cm_transfer hCM`.
- **R1 sub-sorries: all BEI-side sub-sorries are CLOSED (2026-04-20)**.
  - ~~`baseQuotEquiv`~~: CLOSED — via `specOne_baseInclude` +
    `quot_baseInclude_specOne_X`.
  - ~~`specZeroQuotEquiv`~~ (new 2026-04-20): CLOSED — the t=0 analogue
    of `baseQuotEquiv`, giving
    `DefRing / (tildeJ ⊔ span{tDef}) ≃+* S / monomialInitialIdeal G`.
  - ~~`tildeJ_polyT_colon_eq`~~: CLOSED — via `tildeJ_div` +
    `tildeJ_gbProperty` + `DefRing` being a domain.
  - ~~`tildeJ_flat_over_polyT`~~: CLOSED — torsion-free over PID via
    `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`.
  - ~~`tildeJ_tMinusOne_isSMulRegular`, `tildeJ_t_isSMulRegular`~~:
    CLOSED — via flatness + `Module.Flat.isSMulRegular_of_isRegular`.
  - ~~`tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant`~~ (new 2026-04-20):
    CLOSED with clean axioms — proved via `specZeroQuotEquiv` +
    `DoubleQuot.quotQuotEquivQuotSup` +
    `quotSMulTopLocalizationEquiv_of_mem` (un-privated from
    `toMathlib/CohenMacaulay/Polynomial.lean`) +
    `isCohenMacaulayLocalRing_of_regular_quotient`.
  - ~~`tildeJ_quotient_isCohenMacaulay`~~: CLOSED as a one-line application
    of `GradedCM.isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`.
    Inherits `sorryAx` transitively only from GradedCM Case C.
- Total active sorries after this round: **0** in `BEI/GroebnerDeformation.lean`.
  The ONLY remaining transitive gap on the Proposition 1.6 critical path
  is the dormant `caseC_CM_transfer` sorry in `toMathlib/GradedCM.lean`
  (non-BEI-specific, graded-depth commutative algebra infrastructure).

### Note on route 2b (routing around `GradedCM.lean` Case C)

The 2026-04-20 closer attempt at the `tildeJ_quotient_isCohenMacaulay` sub-sorry
(via the "homogeneous-core localization" trick) ran into the obstacle
documented at `toMathlib/GradedCM.lean:280–301`: the canonical map
`A_{p*} → A_p` does **not** exist as an algebra map, because the inclusion
`p* ⊆ p` of ideals goes the wrong way for localization. The "further
localization" reduction is a structural mistake that the GradedCM file
explicitly warns against.

In our specific BEI setting the deformation `S[t] ⧸ Ĩ` has no extra structure
beyond being a finitely generated graded `K`-algebra, so the strategies open
to us are exactly the ones listed in `GradedCM.lean`'s strategy comment:

1. Build the `*-local` graded-depth machinery (~400–800 LOC, not in Mathlib).
2. Build graded Noether normalization + finite-extension CM transfer (also
   several hundred LOC, not in Mathlib).
3. Find a BEI-specific bypass that avoids the LTG theorem entirely.

Strategy 3 is feasible *for `S ⧸ in_<(J_G)`* via Stanley–Reisner methods, but
that's already proved (Step 1) and is the **input** to the deformation, not
the target. For the target `S[t] ⧸ Ĩ`, no analogous BEI-specific bypass is
visible — Stanley–Reisner doesn't apply because `Ĩ` is not a squarefree
monomial ideal.

The honest revised assessment: **R1 cannot be closed without genuinely new
graded commutative algebra infrastructure or a new mathematical idea**.
Closing GradedCM Case C is the blocker; once that's done, the rest of R1
follows from the framework already in place.

**Update 2026-04-20**: the BEI-side graded plumbing has now been built, so
the R1 critical path has contracted to exactly two sorries: (i) the dormant
`GradedCM.lean` Case C, and (ii) the new narrower
`tildeJ_quotient_isCohenMacaulayLocal_at_irrelevant`. The latter is the
regular-quotient-by-`t` argument locally at the irrelevant ideal; it does
not require new graded infrastructure, only the iso
`(DefRing/Ĩ) / (t-class) ≃ S / monomialInitialIdeal G` + a
localisation-quotient commutation step, both well-documented routine
arguments.

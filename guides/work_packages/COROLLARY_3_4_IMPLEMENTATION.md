# Work Package: Corollary 3.4 (full CM statement)

## Task

Implement the full paper-faithful Cohen-Macaulay statement of Corollary 3.4:

> Let `G` be a simple graph on `[n]` with `c` connected components. If `S / J_G`
> is Cohen-Macaulay, then `dim(S / J_G) = n + c`.

This package is for a Lean implementation agent. It is not a math-question note.


## Current status

Already proved:

- `corollary_3_4_equidim` in
  [BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean)
- `minimalPrimes_characterization` in
  [BEI/PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
- `ringKrullDim_quot_primeComponent` in
  [BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean)

What is missing is **not** the combinatorial dimension argument. The missing gap is
the CM-to-equidimensionality bridge needed to feed `corollary_3_4_equidim`.

At handoff time, there is still **no public theorem in the repo** of any of the
following forms:

```lean
IsCohenMacaulayRing R -> IsEquidimRing R
IsCohenMacaulayRing R -> I.IsUnmixed
IsCohenMacaulayRing (R ⧸ I) -> all minimal primes of I have equal quotient dimension
```

So this package is closing a missing CM consequence theorem, not repairing a
BEI combinatorial gap.


## Mathematical conclusion already fixed

Do **not** try to prove a global theorem

```lean
IsCohenMacaulayRing R -> IsEquidimRing R
```

This is false for the repo’s current meaning of `IsCohenMacaulayRing`, which is
the local-at-all-primes notion. Disconnected examples such as `k × k[X]` are
counterexamples.

Do **not** try to prove a global theorem

```lean
Ideal.isUnmixed_of_isCohenMacaulayRing_quotient
```

without extra hypotheses. That is also false globally.

The correct route is:

1. prove a **local** CM theorem;
2. use it to build a **BEI-specific** global bridge;
3. then make `corollary_3_4` a short wrapper around `corollary_3_4_equidim`.


## Deliverables

### 1. Local CM theorem

Add in
[toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean):

```lean
theorem ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsCohenMacaulayLocalRing R]
    {P : Ideal R} (hP : P ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ P) = ringKrullDim R
```

If imports allow it cleanly, also add:

```lean
theorem isEquidimRing_of_isCohenMacaulayLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsCohenMacaulayLocalRing R] :
    IsEquidimRing R
```

If importing `toMathlib/Equidim/Defs.lean` into the CM layer causes an import
cycle or looks ugly, keep only the first theorem in `Localization.lean` and put
the wrapper in a small new file such as:

- [toMathlib/Equidim/CohenMacaulay.lean](/home/tom/BEI-lean/toMathlib/Equidim/CohenMacaulay.lean)


### 2. BEI-specific bridge

Add in
[BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean):

```lean
theorem binomialEdgeIdeal_isEquidim_of_isCohenMacaulay
    (G : SimpleGraph V)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    IsEquidimRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)
```


### 3. Final paper theorem

Then add:

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


## Exact proof plan

### Phase A: local CM implies minimal-prime quotients have full dimension

Preferred proof for
`ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes`:

1. Take `P ∈ minimalPrimes R`.
2. Use the standard theorem for CM local rings:

   `primeHeight(P) + dim(R / P) = dim(R)`.

3. Use `P ∈ minimalPrimes R` to get `primeHeight P = 0`.
4. Conclude `dim(R / P) = dim(R)`.

Lean skeleton:

```lean
theorem ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsCohenMacaulayLocalRing R]
    {P : Ideal R} (hP : P ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ P) = ringKrullDim R := by
  classical
  have hPheight : P.primeHeight = 0 := by
    ...
  have hdim :
      P.primeHeight + ringKrullDim (R ⧸ P) = ringKrullDim R := by
    ...
  simpa [hPheight] using hdim
```

If the height-plus-dimension theorem is missing under the expected name, the
fallback route is:

1. minimal prime implies associated prime;
2. CM local implies associated primes are minimal;
3. use support-dimension / quotient-dimension comparison to show
   `dim(R / P) = dim R`.

Do not broaden beyond that.


### Phase B: wrap the local theorem into local equidimensionality

If the wrapper theorem lives outside `Localization.lean`, prove:

```lean
theorem isEquidimRing_of_isCohenMacaulayLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsCohenMacaulayLocalRing R] :
    IsEquidimRing R := by
  classical
  refine ⟨?_⟩
  intro P Q hP hQ
  have hPdim :=
    ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes (R := R) hP
  have hQdim :=
    ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes (R := R) hQ
  exact hPdim.trans hQdim.symm
```


### Phase C: BEI-specific global bridge

Let:

```lean
S := MvPolynomial (BinomialEdgeVars V) K
J := binomialEdgeIdeal (K := K) G
A := S ⧸ J
```

Goal: prove `IsEquidimRing A` from `[IsCohenMacaulayRing A]`.

The intended route is via localization at the irrelevant / augmentation maximal
ideal.

Subgoals:

1. Define the irrelevant ideal `mA` of `A` as the image of the augmentation
   ideal of `S`.
2. Show `J ≤ augIdeal`, equivalently every generator of `J_G` has zero constant
   term.
3. Show the image ideal `mA` is maximal because `A ⧸ mA ≃ K`.
4. Use global CM to obtain:

   ```lean
   have hCMloc :
       IsCohenMacaulayLocalRing (Localization.AtPrime mA) :=
     IsCohenMacaulayRing.CM_localize mA
   ```

5. Apply the local theorem to get:

   ```lean
   have hEqloc :
       IsEquidimRing (Localization.AtPrime mA) :=
     isEquidimRing_of_isCohenMacaulayLocalRing _
   ```

6. Show every minimal prime of `A` lies under `mA`.
   This should be BEI-specific and use `minimalPrimes_characterization`, because
   every minimal prime comes from some `primeComponent G S`, and those ideals are
   generated by variables and binomials with zero constant term.
7. Transfer equality of minimal-prime quotient dimensions back from
   `Localization.AtPrime mA` to `A`.

This last subgoal is the only delicate one. The deep-model answer recommends a
BEI-shaped bridge, not a broad graded theorem. If needed, introduce a helper
with a narrow statement, for example equality of quotient dimensions for the
localized prime-component quotients. But prefer the smallest theorem that
actually closes the proof.


## Existing declarations you should use

### Paper-side BEI facts already formalized

From [BEI/PrimeDecomposition.lean](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean):

```lean
theorem minimalPrimes_characterization (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).minimalPrimes =
    { P | ∃ S : Finset V,
        P = primeComponent (K := K) G S ∧
        ∀ T : Finset V, primeComponent (K := K) G T ≤ primeComponent (K := K) G S →
          primeComponent (K := K) G S ≤ primeComponent (K := K) G T }
```

From [BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean):

```lean
theorem ringKrullDim_quot_primeComponent (G : SimpleGraph V) (S : Finset V) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) =
    (Fintype.card V - S.card + componentCount G S : ℕ)
```

and:

```lean
theorem corollary_3_4_equidim (G : SimpleGraph V)
    (hEq : IsEquidim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    Fintype.card V + componentCount G ∅
```


### Existing CM infrastructure

Public local unmixedness theorem in
[toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean):

```lean
theorem associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing
    [IsCohenMacaulayLocalRing R] :
    associatedPrimes R R ⊆ minimalPrimes R
```

Private global helper in
[toMathlib/CohenMacaulay/Polynomial.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Polynomial.lean):

```lean
private lemma primeHeight_zero_of_mem_associatedPrimes_of_isCohenMacaulayRing
```

This is a clue about what should be exposed or repackaged, but do not move the
new theorem into `Polynomial.lean` unless you truly need polynomial-specific API.
The theorem is local CM geometry and belongs with the localization CM file.


## What not to do

- Do not “solve” Corollary 3.4 by specializing to Proposition 1.6 graphs.
  `proposition_1_6_dim_formula` is not the general Section 3 theorem.
- Do not rename `corollary_3_4_equidim` to `corollary_3_4`.
- Do not add a false global theorem `IsCohenMacaulayRing -> IsEquidimRing`.
- Do not launch a broad new graded-algebra theory unless the narrow BEI bridge
  clearly fails.


## Expected file changes

Likely touched files:

- [toMathlib/CohenMacaulay/Localization.lean](/home/tom/BEI-lean/toMathlib/CohenMacaulay/Localization.lean)
- optionally new
  [toMathlib/Equidim/CohenMacaulay.lean](/home/tom/BEI-lean/toMathlib/Equidim/CohenMacaulay.lean)
- [BEI/PrimeDecompositionDimension.lean](/home/tom/BEI-lean/BEI/PrimeDecompositionDimension.lean)
- status docs only after the Lean theorem lands


## Verification

At minimum:

```bash
lake build BEI.PrimeDecompositionDimension
```

If imports change:

```bash
lake build
```

If the new public theorem lives in a new file, also check `#print axioms` on:

- `ringKrullDim_quot_eq_ringKrullDim_of_mem_minimalPrimes`
- `binomialEdgeIdeal_isEquidim_of_isCohenMacaulay`
- `corollary_3_4`


## Success condition

The package is complete when the repo contains:

1. a correct **local** CM theorem for minimal-prime quotients;
2. a BEI-specific theorem turning CM of `S / J_G` into equidimensionality;
3. the full paper-faithful theorem `corollary_3_4`;
4. no overclaim that the false global theorem `IsCohenMacaulayRing -> IsEquidimRing`
   has been proved.

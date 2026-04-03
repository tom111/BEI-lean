# Guide: Corollary 3.3 Dimension Formula

## Paper statement

The paper proves:

```text
dim S/J_G = max_{S subset [n]} ((n - |S|) + c(S))
```

and in particular:

```text
dim S/J_G ≥ n + c(G).
```

In the current code, the open targets are:

- [corollary_3_3](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)
- [corollary_3_3_lower_bound](/home/tom/BEI-lean/BEI/PrimeDecomposition.lean)


## Why this is the main next theorem

This is the best remaining non-CM target because:

- `theorem_3_2` is already proved;
- `lemma_3_1` is already proved;
- the result is central to Section 3;
- finishing it will clarify exactly what abstract dimension theory is still missing.


## Current obstacle

The comments say "blocked on catenary", but that diagnosis may be too vague.

Before attempting the final theorem, isolate the exact abstract statement needed.
The missing ingredient is probably one of:

1. a quotient-dimension formula in terms of heights of minimal primes;
2. a formula `dim(R/P) = dim(R) - ht(P)` for the ambient polynomial ring;
3. a way to compute `ringKrullDim (R ⧸ P_S)` directly from the explicit structure of `P_S`.

The third route is the safest.


## Recommended strategy

Do not attack `corollary_3_3` directly first.

Instead, break it into three layers:

1. compute `dim(R ⧸ primeComponent G S)` for fixed `S`;
2. prove a general or BEI-specific theorem relating `dim(R ⧸ inf_i P_i)` to `sup_i dim(R ⧸ P_i)`
   when the `P_i` are the minimal primes of a radical ideal;
3. combine with `theorem_3_2` and `lemma_3_1`.


## Layer 1: dimension of a prime component quotient

Set:

```text
R := MvPolynomial (BinomialEdgeVars V) K
```

Target theorem shape:

```text
ringKrullDim (R ⧸ primeComponent G S) = Fintype.card V - S.card + componentCount G S
```

This is the key theorem.

### Why it should be approachable

`primeComponent G S` is built from:

- the variable ideal killing `x_i, y_i` for `i in S`;
- one complete-graph determinantal ideal for each connected component of `G[V \ S]`.

So the quotient should decompose into a tensor/product-like combination of:

- surviving free coordinates from the deleted variables;
- one rank-1 determinantal piece per connected component.

### Practical proof routes

#### Route A: use heights if the quotient-dimension theorem exists

If Mathlib already gives a convenient theorem:

```text
dim(R ⧸ P) = dim(R) - ht(P)
```

for prime `P` in the ambient polynomial ring, then `lemma_3_1` finishes the job quickly.

But do not assume this exists in usable form.

#### Route B: compute the quotient by explicit ring equivalence

This is the preferred fallback.

The quotient by `primeComponent G S` should be equivalent to a polynomial ring modulo
one complete-graph determinantal ideal per connected component, with the killed variables removed.

Then use:

- already-proved height/dimension results for the complete-graph piece;
- additivity over disjoint variable sets;
- explicit variable counting.

This route may need the remaining `toMathlib/HeightAdditivity` lemmas, but only in a
narrowed and trustworthy form.


## Layer 2: dimension of the radical/intersection quotient

Need a theorem of the shape:

```text
if I = inf S, P_S and the P_S are the minimal primes of I,
then dim(R ⧸ I) = sup_S dim(R ⧸ P_S)
```

Possible approaches:

### Approach 2A: abstract commutative algebra theorem

Search Mathlib first.

If present, use it.

### Approach 2B: BEI-specific minimal-prime argument

If no theorem exists, write a BEI-specific result in `PrimeDecomposition.lean` using:

- `theorem_3_2`;
- `minimalPrimes_characterization`;
- radicality from `corollary_2_2`.

This may still require a general lemma about Krull dimension of a quotient by a radical
ideal being the supremum over minimal primes. If so, isolate that lemma into `toMathlib/`.


## Layer 3: finish the corollaries

Once Layer 1 and Layer 2 are in place:

### `corollary_3_3`

Compute:

- `dim(R ⧸ J_G) = sup_S dim(R ⧸ P_S)`
- `dim(R ⧸ P_S) = |V| - |S| + c(S)`

and combine.

### `corollary_3_3_lower_bound`

This should become immediate by taking `S = ∅`.

If the full supremum formula is hard, prove the lower bound separately first:

1. `J_G ≤ P_∅`;
2. quotient dimension is monotone under surjections;
3. compute `dim(R ⧸ P_∅)`.

That gives usable progress even before the full max formula.


## Suggested file breakdown

Likely new helper theorems:

- in `PrimeDecomposition.lean`:
  - `ringKrullDim_quot_primeComponent`
  - `ringKrullDim_quot_binomialEdgeIdeal_eq_iSup_primeComponents`
- in `toMathlib/` if needed:
  - quotient-dimension over minimal primes;
  - dimension additivity for disjoint-variable quotients.


## Dependency checklist

Already proved:

- `lemma_3_1`
- `theorem_3_2`
- `corollary_2_2`
- `primeComponent_isPrime`
- complete-graph height infrastructure

Likely needed:

- quotient dimension monotonicity;
- dimension of quotient by prime component;
- some additivity lemma over disjoint variable sets.


## Definition of done

This guide is complete when:

1. `corollary_3_3` is proved;
2. `corollary_3_3_lower_bound` is proved;
3. the proof no longer relies on vague "catenary needed" comments, but on a precise
   chain of proved helper lemmas.

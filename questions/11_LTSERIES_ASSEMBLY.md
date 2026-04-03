# Question 11: LTSeries assembly for ringKrullDim_quot_primeComponent_ge

## Context

All chain infrastructure lemmas are proved in BEI/PrimeDecomposition.lean:
- `dimChainMap G S Ux Uy` — the variable-killing map (definition)
- `dimChainMap_ker_isPrime` — kernel is prime
- `primeComponent_le_dimChainMap_ker` — P_S ≤ ker
- `dimChainMap_ker_mono` — Ux ⊆ Ux' ∧ Uy ⊆ Uy' → ker(Ux,Uy) ≤ ker(Ux',Uy')
- `dimChainMap_inl_eq_zero` / `_ne_zero` — X(inl v) witnesses for strict inclusion
- `dimChainMap_inr_rep_eq_zero` / `_ne_zero` — X(inr v) witnesses for reps

## What remains

Prove `ringKrullDim_quot_primeComponent_ge`:
```lean
theorem ringKrullDim_quot_primeComponent_ge (G : SimpleGraph V) (S : Finset V) :
    (Fintype.card V - S.card + componentCount G S : ℕ) ≤
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S)
```

## Approach

Need: `LTSeries (PrimeSpectrum.zeroLocus (primeComponent G S : Set R))` of length
`|V| - |S| + c(S)`, then apply `ringKrullDim_quotient` + `Order.le_krullDim_iff`.

The chain consists of kernels `ker(dimChainMap G S Ux_k Uy_k)` with increasing
(Ux_k, Uy_k). Three phases (from ANSWER_08):

1. Phase 1: Ux grows through non-reps (|V\S| - c(S) steps)
2. Phase 2: Uy grows through reps (c(S) steps)
3. Phase 3: Ux grows through reps (c(S) steps)

Total = |V\S| + c(S) = |V| - |S| + c(S).

## Specific question

How to construct the LTSeries in Lean 4? I see two approaches:

**Approach A: Build from Finset.induction**
Enumerate the non-reps and reps via Finset.toList, then build the chain
inductively using `RelSeries.cons` / `RelSeries.append`.

**Approach B: Direct Fin function**
Define `f : Fin (n+1) → PrimeSpectrum.zeroLocus P_S` by a carefully indexed
function that maps `k` to the appropriate kernel.

**Approach C: Use height + LTSeries existence**
If we can show `Order.height (maximal ideal in zeroLocus) ≥ n + c` in the
`zeroLocus P_S` suborder, then `le_krullDim_iff` gives the result.

Which approach is simplest in Lean 4 / Mathlib v4.28.0? Please provide
a concrete proof outline with the exact API calls.

## Available definitions

```
nonReps G S := Finset.univ.filter (fun v => v ∉ S ∧ compRep G S v ≠ v)
reps G S := Finset.univ.filter (fun v => v ∉ S ∧ compRep G S v = v)
```

These are already used in the lemma_3_1 proof in PrimeIdeals.lean.

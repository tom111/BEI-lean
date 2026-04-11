# Guide: HH CM Bridge — Remaining IsWeaklyRegular Plumbing

## Status

The hard algebraic content for the HH bipartite CM packaging is now **done**.
Three key bridge lemmas have been proved in `BEI/Equidim.lean`:

1. **`mem_map_mk_iff_mem_sup`**: `mk_I(x) ∈ J.map mk_I ↔ x ∈ I ⊔ J`
2. **`isSMulRegular_of_doubleQuot`**: if `r` is a NZD on `R ⧸ (I ⊔ J)`, then
   `mk_I(r)` is a NZD on `(R ⧸ I) ⧸ J.map mk_I` (scalar action via R ⧸ I)
3. **`ideal_smul_top_self`**: `I • (⊤ : Submodule R R) = I.restrictScalars R`
   (self-module ideal smul equals the ideal)

Additionally, two CM infrastructure theorems have been proved in
`toMathlib/CohenMacaulay/Basic.lean`:

4. **`isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim`**: if a weakly
   regular sequence in the maximal ideal has length = Krull dimension, the ring
   is CM.
5. **`isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero`**: a 0-dimensional
   Noetherian local ring is CM.


## What's left: `IsWeaklyRegular` list plumbing

The remaining step to prove `bipartiteEdgeMonomialIdeal_isWeaklyRegular` is
Lean-level plumbing, not new mathematical content:

### Step A: Define the diagonal list and match ideals

Define `diagList n : List (MvPolynomial ...)` as `[x₀+y₀, ..., x_{n-2}+y_{n-2}]`
and prove:

```
Ideal.ofList ((diagList n).take k) = diagonalSumIdeal n k   (for k ≤ n-1)
```

This is a set/list equality involving `List.finRange`, `List.take`, and
`Ideal.span`. The math is trivial but the Lean list manipulation needs care
with `Fin` casting.

### Step B: Wire the `IsWeaklyRegular.mk` constructor

Using the `regular_mod_prev` constructor:

```
∀ (i : ℕ) (h : i < rs.length),
  IsSMulRegular ((S ⧸ I) ⧸ Ideal.ofList (take i rs) • ⊤) rs[i]
```

The proof at each step `i`:
1. Use `ideal_smul_top_self` to convert the module quotient to a ring quotient
2. Use Step A to match `Ideal.ofList (take i ...)` with `diagonalSumIdeal n i`
3. Use `isSMulRegular_of_doubleQuot` to transfer from `S ⧸ (I ⊔ diag_i)`
4. Apply `sum_XY_isSMulRegular_mod_diagonalSum` (already proved)

The `diagList[i]` element needs to be identified with `X(inl i') + X(inr i')`
for the right `Fin n` index, which is a `Fin` arithmetic exercise.

### Step C: From `IsWeaklyRegular` to `IsCohenMacaulayRing`

Once `IsWeaklyRegular` is established:

1. Use `IsWeaklyRegular.isRegular_of_isLocalization_of_mem` (in Mathlib) to
   localize the regular sequence at each prime
2. Use `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim` to conclude
   CM at each prime localization
3. For this, need `dim((S'/I)_P) = n-1` when all diagonal elements are in `P`
   — this follows from dimension additivity for regular sequences
   (`ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`)

Step C involves localization infrastructure (checking elements are in the
maximal ideal of localizations, dimension formulas at localizations). This is
a separate nontrivial step beyond the `IsWeaklyRegular` plumbing.


## Recommended approach

Focus on Steps A and B first (maybe 50–100 lines of Lean). They are pure
plumbing with no mathematical risk. Once `IsWeaklyRegular` is established,
Step C can be approached as a separate packet.


## Definition of done

- `bipartiteEdgeMonomialIdeal_isWeaklyRegular` is proved (0 sorries)
- OR: the exact remaining list/Fin manipulation lemma is isolated with a
  minimal sorry and clear type signature

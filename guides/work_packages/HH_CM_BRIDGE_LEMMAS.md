# Guide: HH CM Bridge — IsWeaklyRegular Plumbing (COMPLETED)

## Status

Steps A and B are **done**. `bipartiteEdgeMonomialIdeal_isWeaklyRegular` is
proved with 0 sorries. Step C (localization to CM) remains open.
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

**Status: Blocker identified. This step does NOT close cleanly.**

The Mathlib localization theorem
`IsWeaklyRegular.isRegular_of_isLocalization_of_mem` localizes a weakly
regular sequence to a regular sequence at a prime, but only for the elements
that are in that prime.

For `IsCohenMacaulayRing (S ⧸ I)`, we need CM at EVERY prime `p`:

1. The sub-sequence of diagonal elements in `p` localizes to a regular
   sequence at `(S ⧸ I)_p`.
2. This sub-sequence has length equal to `dim((S ⧸ I)_p)`.
3. All localized elements land in the maximal ideal of the local ring.
4. Use `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim`.

**The hard part is (2).** For primes `p` that don't contain all diagonal
elements, only a sub-sequence contributes. Showing its length matches the
local dimension requires understanding which diagonal elements are in which
primes, and how the dimension at each prime relates to the number of
"missing" diagonal elements.

**Possible approaches:**

- **Graded CM theorem**: For graded rings, CM at the irrelevant maximal ideal
  implies global CM. All diagonal elements are in the irrelevant maximal
  ideal, so the full sequence contributes. The dimension at the irrelevant
  max is `n - 1` = sequence length, so CM there follows easily. But proving
  "graded CM at irrelevant max ⟹ global CM" is itself non-trivial.

- **Monomial ideal combinatorics**: Since `I` is a squarefree monomial ideal,
  its minimal primes have a nice combinatorial description (vertex covers),
  and the local dimensions can be computed explicitly. But this requires
  linking the Stanley-Reisner theory to the regular sequence.

- **Direct approach at each prime**: For each prime `p` of height `h`,
  exactly `h` diagonal elements are in `p`, and these form a regular
  sequence of length `h` at the localization. This is provable from the
  combinatorics of bipartite graphs but requires significant infrastructure.

**Recommendation**: The graded CM approach is the most economical.
It requires one new theorem:
```
IsCohenMacaulayRing_of_graded_CM_at_irrelevant_max
```
plus showing the irrelevant maximal ideal exists and has the right
dimension. This is a natural separate packet.


## Definition of done (updated)

- ✅ Steps A and B: `bipartiteEdgeMonomialIdeal_isWeaklyRegular` is proved
- ⬜ Step C: requires a graded CM theorem or per-prime dimension analysis

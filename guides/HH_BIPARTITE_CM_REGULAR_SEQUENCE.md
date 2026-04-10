# Guide: HH Bipartite CM via a Regular Sequence

## Task

This is the current paper-critical packet for the Herzog–Hibi half of the
paper-faithful Proposition 1.6 route.

The current direct equidimensional surrogate route is already complete and is
not the target here. The goal is the genuine Cohen–Macaulay statement needed in
the paper's initial-ideal proof.


## Current Lean status

Already proved:

- the closed-graph initial-ideal reduction;
- the y-shift to the bipartite edge ideal;
- the Herzog–Hibi conditions for the graph `Γ`;
- `variablePairIdeal_isRadical` in
  `toMathlib/SquarefreeMonomialPrimes.lean`;
- `bipartiteEdgeMonomialIdeal_isRadical` in `BEI/Equidim.lean`;
- `sum_X_not_mem_minimalPrime` in `BEI/Equidim.lean`;
- `sum_XY_isSMulRegular` in `BEI/Equidim.lean`.
- `diagonalSumIdeal` in `BEI/Equidim.lean`;
- `isSMulRegular_of_radical_not_mem_minimalPrimes` in `BEI/Equidim.lean`;
- `both_vars_mem_prime_sup_diagonalSum` in `BEI/Equidim.lean`;
- `sum_X_not_mem_prime_sup_diagonalSum` in `BEI/Equidim.lean`;
- `sum_X_not_mem_minimalPrime_sup_diagonalSum` in `BEI/Equidim.lean`.

So for each active diagonal index `i`, the element

```text
X (Sum.inl i) + X (Sum.inr i)
```

is a non-zero-divisor on the quotient by the bipartite edge ideal.


## Exact next blocker

We do **not** yet have a full regular sequence.

The current theorem statement is already in the file:

```lean
sum_XY_isSMulRegular_mod_diagonalSum
```

and the remaining gap is no longer the whole quotient analysis from scratch.

The missing step is specifically to show that the sequence of linear forms

```text
x_0 + y_0, x_1 + y_1, ..., x_{n-2} + y_{n-2}
```

remains regular on the successive quotients

```text
S / (I + (x_0+y_0, ..., x_{k-1}+y_{k-1})).
```

In other words: the current theorem proves individual regularity on `S / I`, and
much of the iterated-quotient setup is now formalized, but the CM route still
needs one nilradical-module step to finish the persistence argument.


## Recommended strategy

Treat this as a targeted theorem-design packet first.

### Step 1: use the current theorem statement as the fixed target

Do not redesign the theorem now. The theorem

```lean
sum_XY_isSMulRegular_mod_diagonalSum
```

already isolates the right sequence-level statement.

The task is now to fill the remaining gap in that theorem, not to restate the
whole packet again.

### Step 2: focus on the exact missing module step

The proof architecture has now changed.

The current route uses the substitution

```text
φ : y_j ↦ -x_j   for j < k
```

and reduces `sum_XY_isSMulRegular_mod_diagonalSum` to two precise sublemmas
about the monomial ideal `I.map φ`.

The next targets are exactly:

1. `ell_not_mem_minimalPrime_map_diagSubstHom`
2. `nilradical_nzd_map_diagSubstHom`

So this packet is now specifically about those two sublemmas, not about the old
filtration route in general.

### Step 3: only then decide the route

Good outcomes:

- minimal-prime avoidance for `I.map φ` is proved cleanly;
- the nilradical NZD step for `I.map φ` is proved;
- `sum_XY_isSMulRegular_mod_diagonalSum` is then completed from those two lemmas.

If none of those happen, report the exact obstruction instead of forcing a long
proof attempt.


## False routes to avoid

- Do not overstate `sum_XY_isSMulRegular` or the new diagonal-sum infrastructure
  as if they already gave a regular sequence.
- Do not switch back to the forward depth inequality packet here; that is useful
  general CM infrastructure but not the immediate paper-critical step.
- Do not move on to Gröbner transfer until the HH bipartite CM side is either
  genuinely closed or sharply blocked.


## Definition of done

Best outcome:

- `ell_not_mem_minimalPrime_map_diagSubstHom` proved;
- `nilradical_nzd_map_diagSubstHom` proved;
- `sum_XY_isSMulRegular_mod_diagonalSum` proved.

Minimum acceptable outcome:

- one of the two sublemmas is proved;
- the other is reduced to one exact monomial-ideal statement.

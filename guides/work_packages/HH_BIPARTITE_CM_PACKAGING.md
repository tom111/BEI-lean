# Guide: HH Bipartite CM Packaging

## Task

This is the current HH-side packet for the paper-faithful Proposition 1.6
route.

The old regular-sequence blocker is now closed in code. The remaining job is to
package that finished iterated regularity infrastructure into a genuine
Cohen–Macaulay theorem for the Herzog–Hibi bipartite quotient, or to isolate the
exact missing real-CM theorem that still prevents that step.


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
- `sum_X_not_mem_minimalPrime_sup_diagonalSum` in `BEI/Equidim.lean`;
- `ell_not_mem_minimalPrime_map_diagSubstHom` in `BEI/Equidim.lean`;
- `nilradical_nzd_map_diagSubstHom` in `BEI/Equidim.lean`;
- `isSMulRegular_map_diagSubstHom` in `BEI/Equidim.lean`;
- `sum_XY_isSMulRegular_mod_diagonalSum` in `BEI/Equidim.lean`.

So for each active diagonal index `i`, the element

```text
X (Sum.inl i) + X (Sum.inr i)
```

is now proved to remain a non-zero-divisor on the successive diagonal-sum
quotients used in the HH route.


## Exact remaining blocker

We still do **not** have a final genuine Cohen–Macaulay theorem on the HH side.

What is finished is the iterated non-zero-divisor theorem
`sum_XY_isSMulRegular_mod_diagonalSum`.

The missing step is now to turn that theorem chain into an honest CM conclusion
for the bipartite edge-ideal quotient, in a form that the Proposition 1.6 paper
route can actually use.


## Recommended strategy

Treat this as a targeted theorem-packaging packet.

### Step 1: treat the old regular-sequence packet as finished

Do not spend time reproving the nilradical or substitution machinery.
`sum_XY_isSMulRegular_mod_diagonalSum` is already done.

### Step 2: identify the smallest missing bridge to real CM

Good outcomes:

- a direct theorem that the HH quotient is Cohen–Macaulay, using the completed
  iterated regularity result plus existing depth infrastructure;
- or a precise statement of the one additional real-CM lemma still needed to
  convert that regularity chain into a CM theorem.

The likely candidates are:

- the forward regular-quotient depth inequality from
  `guides/work_packages/cm_pr_26218/BASIC_FORWARD_DEPTH.md`;
- or equivalent regular-sequence / depth packaging not yet present in the local
  `toMathlib/CohenMacaulay` layer.

### Step 3: keep the paper endpoint explicit

The actual paper-critical object is an HH-side CM theorem strong enough to
combine with the already formalized initial-ideal reduction and the still-missing
Gröbner CM transfer theorem.


## False routes to avoid

- Do not describe the HH side as complete merely because the iterated
  non-zero-divisor theorem is done.
- Do not fall back to the equidimensional surrogate and present it as the
  paper's CM theorem.
- Do not reopen the finished nilradical/substitution packet unless a genuine
  defect is found.


## Definition of done

Best outcome:

- a genuine HH-side Cohen–Macaulay theorem is formalized from the completed
  regularity infrastructure.

Minimum acceptable outcome:

- the exact missing bridge from `sum_XY_isSMulRegular_mod_diagonalSum` to a real
  CM theorem is isolated precisely enough to become its own focused packet.

# Guide: Forward Depth Inequality for Regular Quotients

## Preserved task

The current real Cohen–Macaulay track has already landed:

- `toMathlib/CohenMacaulay/Defs.lean`
- `toMathlib/CohenMacaulay/Basic.lean`

with the following one-directional regular-quotient results:

- `ringDepth_quotSMulTop_succ_le`
- `isCohenMacaulayLocalRing_of_regular_quotient`

The missing next step is the opposite depth inequality needed for the forward
regular-quotient CM transfer.


## Exact blocker

The missing theorem is morally:

```lean
theorem ringDepth_le_ringDepth_quotSMulTop_succ {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    ringDepth R ≤ @ringDepth (QuotSMulTop x R) _ (quotSMulTopLocalRing hx) + 1 := by
  ...
```

This would combine with `ringDepth_quotSMulTop_succ_le` to give the expected
equality

```text
depth(R/xR) + 1 = depth(R)
```

for regular `x ∈ maximalIdeal R`, and hence the forward local CM transfer

```text
CM(R) -> CM(R/xR).
```


## Current Lean status

Already available:

- `quotSMulTop_nontrivial`
- `quotSMulTopLocalRing`
- `ringDepth_quotSMulTop_succ_le`
- `isCohenMacaulayLocalRing_of_regular_quotient`

The classical proof obstacle identified so far is:

- from the current `ringDepth` definition as a supremum over weakly regular
  sequence lengths, the easy direction is obtained by lifting a quotient
  sequence and prepending `x`;
- the reverse direction needs a way to start with a weakly regular sequence in
  `R` and produce a long enough weakly regular sequence in `R/(x)`;
- the standard proof uses a stronger theorem such as Rees/permutability of
  maximal regular sequences, which is not currently available in this local
  backport.


## Recommended strategy

Treat this as a theorem-design and dependency-isolation packet first, not as a
promise that the full proof will land in one round.

### Step 1: inspect whether a weaker but still useful theorem is enough

Check whether the next paper-facing use really needs the full inequality above,
or whether a more local theorem suffices, for example:

- a forward CM transfer theorem under an explicit extra hypothesis stronger than
  mere regularity;
- a depth equality theorem for the specific quotient situations used later in
  the BEI project;
- or an upstream theorem already present in mathlib `v4.28.0` under a different
  name or packaging.

Do **not** silently weaken the theorem without documenting the mismatch.

### Step 2: inspect PR `#26218` and its dependency cone

Determine whether the missing forward direction is already proved in the PR, and
if so:

- what exact theorem names it uses;
- whether it depends on Rees or other deeper depth infrastructure;
- whether the dependency cone is still realistically backportable.

### Step 3: only then choose one of two routes

#### Route A: small local proof

If the forward inequality can be proved directly from the current `ringDepth`
definition plus existing regular-sequence lemmas, do that in
`toMathlib/CohenMacaulay/Basic.lean`.

#### Route B: explicit blocker isolation

If the proof genuinely requires deeper theorems (Rees, permutation of maximal
regular sequences, or equivalent depth infrastructure), stop and document the
smallest exact missing theorem instead of forcing a brittle proof attempt.


## False routes to avoid

- Do not present the already proved converse result as a full regular-quotient
  characterization.
- Do not silently switch back to the equidimensional surrogate branch.
- Do not start broad Gröbner transfer work before the regular-quotient CM layer
  is actually strong enough.
- Do not import large unrelated CM machinery unless the dependency cone has been
  checked carefully.


## Definition of done

Best outcome:

- the forward depth inequality is proved;
- the forward regular-quotient CM transfer becomes available;
- the next real CM induction step is unblocked.

Minimum acceptable outcome:

- one smaller but real forward-direction theorem is proved; or
- the exact missing imported theorem/dependency is isolated precisely, with file
  and declaration names.

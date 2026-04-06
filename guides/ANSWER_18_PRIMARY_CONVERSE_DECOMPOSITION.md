# Guide: Breaking Up the Primary Converse After Q18

## Original question

Question file:
`questions/Q18_PRIMARY_CONVERSE_CANCELLATION.md`

Original blocker summary from Claude:

> To prove the converse of the primary monomial characterization, I need a contradiction
> from `x * y ∈ I`, `x ∉ I`, and a support monomial `d_y` of `y` supported outside `s`.
> The obvious attempt was to force `d_x + d_y ∈ (x * y).support`. But the proposed
> `coeff_mul_lexMax_left` route is false in general: if only `d_x` is lex-maximal in `x`,
> then lower `a < d_x` terms can still pair with higher `b > d_y` terms and contribute to
> the same sum.

That diagnosis is correct. Do not keep pushing on `coeff_mul_lexMax_left`.

## Current live state

Already proved in `toMathlib/MonomialIdeal.lean`:

- `coeff_mul_lexMax`
- `Ideal.IsMonomial.exists_monomial_notMem`
- `criterion_buildUp`
- `coeff_pow_lexMax`
- `Ideal.IsMonomial.radical_isMonomial`
- `Ideal.IsMonomial.isPrimary_radical_eq_span_X`

Still open:

- the converse direction of the primary iff

Current false route:

- trying to prove a general `coeff_mul_lexMax_left`

## Recommendation

Do not attack `isPrimary_of_criterion` directly as one theorem.
Break it into smaller pieces that remove the outside-variable noise first.

The best next route is:

1. prove that monomial membership in `I` depends only on the exponents on `s`;
2. repackage `I` as an extension of a monomial ideal in the `s`-variables;
3. only then revisit the converse in that reduced setting.

This is a better decomposition than fighting general cancellation in `x * y` immediately.

## Why this route is better

The criterion already says:

```text
if monomial d ∉ I and e is supported outside s,
then monomial (d + e) ∉ I
```

By contraposition, this should give:

```text
if monomial (d + e) ∈ I and e is supported outside s,
then monomial d ∈ I
```

Together with ideal closure, that means:

```text
monomial d ∈ I  iff  monomial (d + e) ∈ I
```

for any `e` supported outside `s`.

So monomial membership should depend only on the `s`-part of the exponent.
That is the structural simplification you want before doing any more product algebra.

## Concrete subgoals

### Packet 1: make the criterion bidirectional

Prove a clean contrapositive wrapper around `criterion_buildUp`.

Suggested target shape:

```lean
theorem monomial_mem_iff_add_outside_mem
    (hcrit : ...)
    {d e : σ →₀ ℕ}
    (he : ∀ i ∈ s, e i = 0 := ...) :
    MvPolynomial.monomial d 1 ∈ I ↔
      MvPolynomial.monomial (d + e) 1 ∈ I
```

You may package the support condition however is Lean-convenient, e.g.
`e.support ⊆ sᶜ`.

This is the most important missing local lemma.

### Packet 2: prove “membership depends only on the `s`-part”

Define the projection of an exponent to the coordinates in `s`, or an equivalent
normal form that deletes the coordinates outside `s`.

Then prove:

```text
monomial membership in I is determined by that projected exponent
```

Do not over-engineer the API. A BEI-specific finite-support helper is enough.

### Packet 3: split off the outside variables

Once Packet 2 lands, prove an extension/restriction statement:

```text
I is the extension of a monomial ideal in the variables from s
```

It does not need to be abstractly beautiful. The point is to reduce the converse to the
ring where only the radical variables remain relevant.

This should make the remaining algebra much smaller and may eliminate the bad
cross-cancellation patterns that are defeating the current proof attempt.

### Packet 4: only then revisit the converse

After the reduction above, re-open the converse.

If the reduced setting still needs a leading-term lemma for products, it should now be
for a smaller and cleaner target than the full original theorem.

## What not to do

- Do not keep trying to rescue `coeff_mul_lexMax_left`.
- Do not keep adding more and more global lex-max lemmas on the full ring before proving
  the “membership depends only on `s`” structure.
- Do not attempt the squarefree minimal-primes / vertex-cover packet until this converse
  has either landed or been cleanly reduced to a genuinely separate algebra lemma.

## Suggested next working order

1. prove the contrapositive / iff version of `criterion_buildUp`;
2. prove that monomial membership depends only on the `s`-part;
3. package `I` as an extension from the `s`-variables;
4. reassess the converse in the reduced setting;
5. only if still necessary, isolate a smaller product leading-term lemma there.

## Definition of done for this guide

This guide has done its job if the next round does **not** start with
`coeff_mul_lexMax_left`, and instead starts with the structural “outside variables do not
matter for monomial membership” lemma.

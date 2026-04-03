# Answer to Q7: Catenary for `MvPolynomial`

## Preserved question

The original question asked whether one should prove a full catenary/height-plus-coheight
theorem for `MvPolynomial σ K` with finite `σ`, in order to recover formulas like:

```text
Ideal.primeHeight P + ringKrullDim (R ⧸ P) = Nat.card σ.
```

It also asked whether the standard induction-on-variables proof is feasible in Lean, and
whether this should replace the BEI-specific workarounds.

## Short answer

Do not make full catenarity of `MvPolynomial σ K` the next project.
It is mathematically natural, but much larger than what the BEI critical path needs.

## Why not

The induction-on-variables proof opens a broad commutative-algebra front:

- contraction/extension of primes;
- exact height behavior in polynomial extensions;
- quotient-dimension behavior;
- order-theoretic assembly of height + coheight equality.

That is a serious standalone development.

## What to do instead

Work around catenarity by proving only what BEI needs:

1. `ringKrullDim (R ⧸ P_S)` directly for `P_S = primeComponent G S`;
2. `ringKrullDim (R ⧸ I)` for radical `I` as the supremum over minimal primes;
3. derive Corollary 3.3 from those.

## Recommendation

Treat catenarity as optional future infrastructure, not a current bottleneck.
Only revisit it if the BEI project is otherwise basically complete or if later work
demands a general theorem.

# Answer to Q1: Dimension of the Quotient by `primeComponent G S`

## Preserved question

We work in `R = MvPolynomial (V ⊕ V) K` with `K` a field and `V` finite.
We already know:

```text
height(P_S) = |S| + |V| - c(S)
```

for `P_S = primeComponent G S`, and we need:

```text
ringKrullDim (R ⧸ P_S) = |V| - |S| + c(S).
```

The original question asked for the cleanest Lean/Mathlib route to this quotient-dimension
formula without assuming a general catenary theorem for `MvPolynomial`.

## Short answer

Do not try to prove the full catenary property of `MvPolynomial` first.
For this project, the cleanest route is to prove the dimension formula directly for
`primeComponent G S`, using its explicit decomposition.

Target:

```lean
theorem ringKrullDim_quot_primeComponent (G : SimpleGraph V) (S : Finset V) :
  ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) =
    Fintype.card V - S.card + componentCount G S
```

## Recommended route

1. Prove dimension of the complete-graph quotient piece.
2. Prove additivity for quotients in disjoint variable blocks, only in the specific
   polynomial-ring setting actually needed here.
3. Remove killed variables first, then split the surviving quotient by connected
   components of `G[V \ S]`.

## Why this is better than catenarity

- the primes `P_S` have explicit structure;
- the quotient decomposition is visible from the definition;
- the full catenary theorem is a much larger project than Corollary 3.3 needs.

## Specific recommendations

- Avoid the transcendence-degree route unless you discover a direct existing theorem that
  turns the Segre-parameterization intuition into a quotient-dimension theorem.
- Avoid the general tensor-product-of-domains route. You likely only need the
  disjoint-variable polynomial case.
- Use order-theoretic / spectrum arguments later for the radical ideal step, not for the
  fixed prime-component step.

## Practical next theorem

The first subtarget should be a theorem computing:

```text
ringKrullDim (R ⧸ J_{K_m}) = m + 1
```

for the complete graph on `m` vertices. Once that exists, the `P_S` quotient formula
becomes a structured assembly problem.

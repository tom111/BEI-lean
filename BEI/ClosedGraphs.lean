import BEI.MonomialOrder
import BEI.GraphProperties
import BEI.GroebnerAPI
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Closed graphs and the Gröbner basis condition (Theorem 1.1)

This file formalizes Theorem 1.1 of Herzog et al. (2010): the quadratic generators
`f_{ij} = x_i y_j - x_j y_i` of the binomial edge ideal `J_G` form a Gröbner basis
with respect to the lex order if and only if G is a closed graph.

## Key definitions
- `generatorSet G`: the set of quadratic generators of `J_G`

## Reference: Herzog et al. (2010), Theorem 1.1
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## The generator set -/

/--
The set of quadratic generators of `binomialEdgeIdeal G`:
  `{f_{ij} = x_i y_j - x_j y_i | {i,j} ∈ E(G), i < j}`
-/
def generatorSet (G : SimpleGraph V) :
    Set (MvPolynomial (BinomialEdgeVars V) K) :=
  { f | ∃ i j : V, G.Adj i j ∧ i < j ∧ f = x i * y j - x j * y i }

/-- The generator set spans `binomialEdgeIdeal G`. -/
theorem generatorSet_span (G : SimpleGraph V) :
    Ideal.span (generatorSet (K := K) G) = binomialEdgeIdeal (K := K) G := rfl

/-! ## Theorem 1.1 -/

/--
**Theorem 1.1** (Herzog et al. 2010): The quadratic generators of `J_G` form a
Gröbner basis with respect to the lex order iff G is a closed graph.

Proof outline:
- (⇒) "generators form GB → G closed": If G is not closed, there exist edges
  `{i,k}` and `{i,j}` sharing vertex i with i < j, i < k but {j,k} ∉ E(G).
  Then the S-polynomial of `f_{ij}` and `f_{ik}` does not reduce to 0
  modulo the generators.
- (⇐) "G closed → generators form GB": For any two generators `f_{ij}` and
  `f_{ik}` (resp. `f_{ij}` and `f_{kj}`) sharing a variable, the closed
  condition guarantees the S-polynomial reduces to 0.

Reference: Herzog et al. (2010), Theorem 1.1.
-/
theorem theorem_1_1 (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis (generatorSet (K := K) G)
      (binomialEdgeIdeal (K := K) G) ↔
    IsClosedGraph G := by
  sorry

/-- Forward direction of Theorem 1.1: closed graph → Gröbner basis. -/
theorem closed_implies_groebner (G : SimpleGraph V) (h : IsClosedGraph G) :
    binomialEdgeMonomialOrder.IsGroebnerBasis (generatorSet (K := K) G)
      (binomialEdgeIdeal (K := K) G) := by
  sorry

/-- Backward direction of Theorem 1.1: Gröbner basis → closed graph. -/
theorem groebner_implies_closed (G : SimpleGraph V)
    (h : binomialEdgeMonomialOrder.IsGroebnerBasis (generatorSet (K := K) G)
      (binomialEdgeIdeal (K := K) G)) :
    IsClosedGraph G := by
  sorry

end

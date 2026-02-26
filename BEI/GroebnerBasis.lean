import BEI.AdmissiblePaths
import BEI.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# The reduced Gröbner basis and the radical property (Theorems 2.1 and 2.2)

This file formalizes:
- **Theorem 2.1**: `{ u_π · f_{ij} }` is a reduced Gröbner basis of `J_G`.
- **Corollary 2.2**: `J_G` is a radical ideal.

## Reference: Herzog et al. (2010), Theorems 2.1 and Corollary 2.2
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## Theorem 2.1: Reduced Gröbner basis -/

/--
**Theorem 2.1** (Herzog et al. 2010): The set
  `{ u_π · f_{ij} | i < j, π admissible path from i to j in G }`
is a reduced Gröbner basis of `J_G` with respect to the lex monomial order.

The proof proceeds in three steps:
1. Each `u_π · f_{ij} ∈ J_G` (see `groebnerElement_mem` in `AdmissiblePaths.lean`).
2. Buchberger: all S-polynomials reduce to 0 modulo the set.
3. Reducedness: no leading monomial divides another.

Reference: Herzog et al. (2010), Theorem 2.1.
-/
theorem theorem_2_1 (G : SimpleGraph V) :
    -- Part 1: the Gröbner basis set spans J_G
    Ideal.span (groebnerBasisSet (K := K) G) = binomialEdgeIdeal (K := K) G := by
  sorry

theorem theorem_2_1_leading (G : SimpleGraph V) (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) :
    -- Part 2: the leading term of f is divisible by some leading term in the basis set
    ∃ (i j : V) (π : List V) (_ : IsAdmissiblePath G i j π),
      binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) ≤
      binomialEdgeMonomialOrder.degree f := by
  sorry

theorem theorem_2_1_reduced (G : SimpleGraph V)
    (i₁ j₁ : V) (π₁ : List V) (_ : IsAdmissiblePath G i₁ j₁ π₁)
    (i₂ j₂ : V) (π₂ : List V) (_ : IsAdmissiblePath G i₂ j₂ π₂)
    (hne : (i₁, j₁, π₁) ≠ (i₂, j₂, π₂)) :
    -- Part 3: no leading monomial divides another
    ¬ (binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₁ j₁ π₁) ≤
       binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₂ j₂ π₂)) := by
  sorry

/-! ## Corollary 2.2: J_G is radical -/

/--
**Corollary 2.2** (Herzog et al. 2010): `J_G` is a radical ideal.

**Proof**: By Theorem 2.1 the initial ideal `in_<(J_G)` is squarefree
(each leading monomial `u_π · x_i · y_j` has distinct variables). A general
result states that if `in_<(I)` is squarefree then `I` is radical.

Reference: Herzog et al. (2010), Corollary 2.2.
-/
theorem corollary_2_2 (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).IsRadical := by
  sorry

/--
The leading monomials of the Gröbner basis elements are squarefree:
each variable appears at most once in `u_π · x_i · y_j`.
-/
theorem groebnerElement_leadingMonomial_squarefree
    (G : SimpleGraph V) (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π)
    (v : BinomialEdgeVars V) :
    binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) v ≤ 1 := by
  sorry

end

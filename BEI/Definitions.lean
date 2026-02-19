import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Basic

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] -- variables are ordered

noncomputable section

open MvPolynomial

-- The set of variables contains two copies of the same set
abbrev BinomialEdgeVars (V : Type*) := V ⊕ V

-- Abbreviations for x i and y j notation.
def x (i : V) : MvPolynomial (BinomialEdgeVars V) K := X (Sum.inl i)
def y (i : V) : MvPolynomial (BinomialEdgeVars V) K := X (Sum.inr i)

def binomialEdgeIdeal (G : SimpleGraph V) : Ideal (MvPolynomial (BinomialEdgeVars V) K) :=
  Ideal.span { f | ∃ i j, G.Adj i j ∧ i < j ∧ f = x i * y j - x j * y i }


/--
A graph is closed with respect to the linear order on V if it
satisfies Condition (b) of Theorem 1.1 in Herzog et al. (2010).

It requires that for any pair of edges (i,j) and (i,k)
sharing a vertex:
1. If they diverge from a common minimum (i.e. i < j and i < k),
   the endpoints are connected: (j,k) ∈ G.
2. If they converge to a common maximum (i < k and j < k),
  the startpoints are connected: (i,j) ∈ G.
-/
def IsClosedGraph (G : SimpleGraph V) : Prop :=
  (∀ {i j k : V}, i < j → i < k → G.Adj i j → G.Adj i k → G.Adj j k) ∧
  (∀ {i j k : V}, i < k → j < k → G.Adj i k → G.Adj j k → G.Adj i j)

end

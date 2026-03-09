import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Data.Finite.Sum

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] -- variables are ordered

noncomputable section

open MvPolynomial

/--
The set of variables for the binomial edge ideal polynomial ring.
Contains two copies of V: `Sum.inl i` represents `x_i` and `Sum.inr i` represents `y_i`.

This is intentionally a `def` (opaque) rather than `abbrev` to prevent Lean from
finding `Sum.instLESum`/`Sum.instLTSum` (which use `Sum.LiftRel`, a product ordering)
when resolving `LE`/`LT` on `BinomialEdgeVars V`. This avoids an instance diamond
between `Finsupp.instLTLex` and the LT derived from our custom `LinearOrder`.
-/
def BinomialEdgeVars (V : Type*) := V ⊕ V

instance [DecidableEq V] : DecidableEq (BinomialEdgeVars V) :=
  inferInstanceAs (DecidableEq (V ⊕ V))

instance [Finite V] : Finite (BinomialEdgeVars V) :=
  inferInstanceAs (Finite (V ⊕ V))

instance [Fintype V] : Fintype (BinomialEdgeVars V) :=
  inferInstanceAs (Fintype (V ⊕ V))

-- Abbreviations for x i and y j notation.
def x (i : V) : MvPolynomial (BinomialEdgeVars V) K := X (Sum.inl i)
def y (i : V) : MvPolynomial (BinomialEdgeVars V) K := X (Sum.inr i)

def binomialEdgeIdeal (G : SimpleGraph V) : Ideal (MvPolynomial (BinomialEdgeVars V) K) :=
  Ideal.span { f | ∃ i j, G.Adj i j ∧ i < j ∧ f = x i * y j - x j * y i }


/--
A graph is closed with respect to the linear order on V if it
satisfies Condition (b) of Theorem 1.1 in Herzog et al. (2010).

It requires that for any pair of edges (i,j) and (i,k)
sharing a distinct pair of endpoints:
1. If they diverge from a common minimum (i.e. i < j, i < k, j ≠ k),
   the endpoints are connected: (j,k) ∈ G.
2. If they converge to a common maximum (i < k, j < k, i ≠ j),
   the startpoints are connected: (i,j) ∈ G.

The distinctness conditions j ≠ k (resp. i ≠ j) are necessary because
SimpleGraph.Adj is irreflexive: without them, applying condition 1 with
k := j would require G.Adj j j, which is always false.
-/
def IsClosedGraph (G : SimpleGraph V) : Prop :=
  (∀ {i j k : V}, i < j → i < k → j ≠ k → G.Adj i j → G.Adj i k → G.Adj j k) ∧
  (∀ {i j k : V}, i < k → j < k → i ≠ j → G.Adj i k → G.Adj j k → G.Adj i j)

end

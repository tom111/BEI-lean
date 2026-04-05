import BEI.PrimeIdeals
import BEI.GraphProperties
import toMathlib.CohenMacaulay.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

noncomputable section

open MvPolynomial SimpleGraph

/-!
# Cohen-Macaulay rings and binomial edge ideals

Uses `IsCohenMacaulayRing` from `toMathlib/CohenMacaulay/Defs.lean`, which defines
CM via equidimensionality (all minimal primes have the same height). This is a
consequence of the full CM definition (depth = dim), adapted from mathlib PR #26218.

Formalizes Proposition 1.6 of Herzog et al. (2010):
  If G is a connected closed graph satisfying an additional interval condition,
  then S/J_G is Cohen-Macaulay.

## Reference: Herzog et al. (2010), Section 1
-/

-- Re-export for backward compatibility
abbrev IsCohenMacaulay (R : Type*) [CommRing R] := IsCohenMacaulayRing R

/-- An integral domain is CM: it has a unique minimal prime (⊥),
so the equidimensionality condition holds vacuously. -/
instance IsDomain.isCohenMacaulayRing {R : Type*} [CommRing R] [IsDomain R] :
    IsCohenMacaulayRing R where
  equidimensional P Q hP hQ := by
    have h := IsDomain.minimalPrimes_eq_singleton_bot (R := R)
    rw [h, Set.mem_singleton_iff] at hP hQ
    rw [hP, hQ]

/--
The additional condition from Proposition 1.6: whenever {i, j+1} and {j, k+1}
are edges with i < j < k then {i, k+1} is also an edge.

Stated for `Fin n` so that successor makes sense.
-/
def SatisfiesProp1_6Condition (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (i j k : Fin n) (hj : j.val + 1 < n) (hk : k.val + 1 < n),
    i < j → j < k →
    G.Adj i ⟨j.val + 1, hj⟩ →
    G.Adj j ⟨k.val + 1, hk⟩ →
    G.Adj i ⟨k.val + 1, hk⟩

/--
The three conditions of the Herzog–Hibi criterion for CM bipartite graphs,
translated back from the bipartite graph Γ to conditions on the original graph G.

In the proof of Proposition 1.6, the initial ideal `in_<(J_G)` is identified with the
edge ideal of a bipartite graph Γ on `{x₁,…,x_{n-1},y₁,…,y_{n-1}}` where
`{xᵢ, yⱼ} ∈ E(Γ)` iff `{i, j+1} ∈ E(G)` and `i ≤ j`. The three HH conditions are:

- (i)  **Diagonal**: `{xᵢ, yᵢ}` is an edge for all `i`, i.e., `G.Adj i (i+1)`.
- (ii) **Upper triangularity**: if `{xᵢ, yⱼ}` is an edge then `i ≤ j`.
       Automatic from the orientation `i < j+1`.
- (iii) **Transitivity**: if `{xᵢ, yⱼ}` and `{xⱼ, yₖ}` are edges then `{xᵢ, yₖ}` is.
        This is exactly `SatisfiesProp1_6Condition`.

Reference: Herzog, Hibi (2005); used in Herzog et al. (2010), Proposition 1.6.
-/
structure HerzogHibiConditions (n : ℕ) (G : SimpleGraph (Fin n)) : Prop where
  /-- Condition (i): consecutive vertices are adjacent (diagonal edges of Γ). -/
  diagonal : ∀ (i : Fin n) (hi : i.val + 1 < n), G.Adj i ⟨i.val + 1, hi⟩
  /-- Condition (iii): the transitivity property (= Prop 1.6 hypothesis). -/
  transitivity : SatisfiesProp1_6Condition n G

/--
Under the hypotheses of Proposition 1.6, the associated bipartite graph Γ satisfies
all three conditions of the Herzog–Hibi criterion.

This is the graph-combinatorial content of the paper's reduction. The diagonal
condition (i) follows from `closedGraph_adj_consecutive` (Proposition 1.4),
and the transitivity condition (iii) is exactly the hypothesis.

The remaining steps to complete Proposition 1.6 are purely algebraic:
1. Initial ideal: `in_<(J_G) = ⟨xᵢ yⱼ : {i,j} ∈ E(G), i < j⟩` (from Theorem 1.1)
2. Herzog–Hibi theorem: edge ideal of Γ satisfying (i)–(iii) is Cohen–Macaulay
3. CM transfer: `S/in_<(I)` is CM → `S/I` is CM
-/
theorem prop_1_6_herzogHibi (n : ℕ) (G : SimpleGraph (Fin n))
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    HerzogHibiConditions n G :=
  ⟨fun i hi => closedGraph_adj_consecutive hClosed hConn i hi, hCond⟩

/--
Proposition 1.6: If G is connected, closed with respect to its labeling, and satisfies
the interval condition, then S/J_G is Cohen-Macaulay.

**Status**: The graph-combinatorial reduction is completed by `prop_1_6_herzogHibi`,
which proves that the associated bipartite graph Γ satisfies the Herzog–Hibi conditions
(i)–(iii). The remaining algebraic inputs needed to close this sorry are:

1. **Initial ideal description**: `in_<(J_G) = ⟨xᵢ yⱼ : {i,j} ∈ E(G), i < j⟩`
   for closed graphs (a consequence of Theorem 1.1 already in the repo).
2. **Herzog–Hibi CM theorem**: the edge ideal of a bipartite graph satisfying
   conditions (i)–(iii) gives a Cohen–Macaulay quotient ring.
3. **CM transfer from initial ideal**: `S/in_<(I)` CM implies `S/I` CM.

Reference: Herzog et al. (2010), Proposition 1.6.
-/
theorem prop_1_6 (n : ℕ) (G : SimpleGraph (Fin n))
    (hConn : G.Connected)
    (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsCohenMacaulay
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal G) := by
  -- The graph-combinatorial reduction is done:
  have _hHH := prop_1_6_herzogHibi n G hConn hClosed hCond
  -- Missing: algebraic steps (HH CM theorem + initial ideal CM transfer)
  sorry

/-- Example 1.7(a): The complete graph K_n yields a Cohen-Macaulay quotient.
The complete graph has J_G = P_∅(G), which is prime, so R/J_G is a domain and
hence trivially CM (unique minimal prime). -/
theorem complete_is_CM (n : ℕ) :
    IsCohenMacaulay
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
       binomialEdgeIdeal (⊤ : SimpleGraph (Fin n))) := by
  -- P_∅(K_n) ≤ J_{K_n}: every SameComponent minor is an edge in K_n
  have hP0_le : primeComponent (K := K) (⊤ : SimpleGraph (Fin n)) ∅ ≤
      binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin n)) := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_union, Set.mem_setOf_eq] at hf
    rcases hf with ⟨i, hi, _⟩ | ⟨j, k, hjk, _, rfl⟩
    · exact absurd hi (Finset.notMem_empty i)
    · exact Ideal.subset_span ⟨j, k, (top_adj j k).mpr (ne_of_lt hjk), hjk, rfl⟩
  -- J_{K_n} = P_∅(K_n), and P_∅ is prime
  rw [show binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin n)) =
      primeComponent (K := K) (⊤ : SimpleGraph (Fin n)) ∅ from
    le_antisymm (binomialEdgeIdeal_le_primeComponent (⊤ : SimpleGraph (Fin n)) ∅) hP0_le]
  haveI := primeComponent_isPrime (K := K) (⊤ : SimpleGraph (Fin n)) ∅
  exact inferInstance

-- Example 1.7(b) (path_is_CM) is proved in PrimeDecompositionDimension.lean
-- where the dimension formula and minimal prime characterization are available.

end

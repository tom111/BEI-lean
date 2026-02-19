import BEI.PrimeIdeals
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Minimal prime ideals of J_G (Propositions 3.8 and 3.9)

This file characterizes the containment order of `{P_S(G)}` and identifies
which `P_S(G)` are minimal primes of `J_G`.

## Main results

- **Proposition 3.8**: `P_T(G) ⊆ P_S(G)` iff T ⊆ S and components of G[V\T]
  refine into components of G[V\S].
- **Corollary 3.9**: `P_S(G)` is minimal iff S = ∅ or every vertex of S is a
  cut-vertex in the appropriate induced subgraph.

## Reference: Herzog et al. (2010), Proposition 3.8, Corollary 3.9
-/

noncomputable section

open MvPolynomial SimpleGraph

/-! ## Cut vertices -/

/--
A vertex `i ∈ S` is a **cut-vertex relative to S** if
  `c(S \ {i}) < c(S)`
i.e., removing `i` from S strictly decreases the component count.
Equivalently, `i` separates some component of G[V \ (S \ {i})].

Reference: Herzog et al. (2010), Corollary 3.9.
-/
def IsCutVertexRelative (G : SimpleGraph V) (S : Finset V) (i : V) : Prop :=
  i ∈ S ∧ componentCount G (S.erase i) < componentCount G S

/-! ## Proposition 3.8: Containment of prime ideals -/

/--
**Proposition 3.8** (Herzog et al. 2010):
`P_T(G) ⊆ P_S(G)` if and only if:
- `T ⊆ S`, and
- every connected component of `G[V \ T]` whose vertices intersect `V \ S`
  is contained (on `V \ S`) in a single component of `G[V \ S]`.

Reference: Herzog et al. (2010), Proposition 3.8.
-/
theorem prop_3_8 (G : SimpleGraph V) (S T : Finset V) :
    primeComponent (K := K) G T ≤ primeComponent (K := K) G S ↔
    T ≤ S ∧
    ∀ (u v : V), u ∉ T → v ∉ T → u ∉ S → v ∉ S →
      SameComponent G T u v → SameComponent G S u v := by
  sorry

/-! ## Corollary 3.9: Minimal prime characterization -/

/--
**Corollary 3.9** (Herzog et al. 2010): Assuming G is connected,
`P_S(G)` is a minimal prime of `J_G` if and only if either:
- S = ∅ (then P_∅(G) = J_G is the "generic" prime), or
- every vertex in S is a cut-vertex relative to S.

Reference: Herzog et al. (2010), Corollary 3.9.
-/
theorem corollary_3_9 (G : SimpleGraph V) (S : Finset V)
    (hConn : G.Connected) :
    primeComponent (K := K) G S ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes ↔
    S = ∅ ∨ ∀ i ∈ S, IsCutVertexRelative G S i := by
  sorry

/-- The set of minimal primes of J_G is finite. -/
theorem minimalPrimes_finite (G : SimpleGraph V) :
    Set.Finite (binomialEdgeIdeal (K := K) G).minimalPrimes := by
  sorry

/-! ## Monotonicity of component count -/

/--
`c(S)` is monotone non-decreasing in S:
adding more vertices to S can only create more components in G[V\S].
-/
theorem componentCount_mono (G : SimpleGraph V) {S T : Finset V} (hST : S ≤ T) :
    componentCount G S ≤ componentCount G T := by
  sorry

/--
Adding a single vertex to S increases c by at most 1:
  `c(S) ≤ c(S ∪ {i}) ≤ c(S) + 1`
-/
theorem componentCount_insert_le (G : SimpleGraph V) (S : Finset V) (i : V) (hi : i ∉ S) :
    componentCount G S ≤ componentCount G (insert i S) ∧
    componentCount G (insert i S) ≤ componentCount G S + 1 := by
  constructor <;> sorry

/--
`i` is a cut-vertex relative to S iff adding i to `S \ {i}` strictly increases c(S):
  `c(S) > c(S \ {i})`
-/
theorem cutVertex_iff_componentCount (G : SimpleGraph V) (S : Finset V) (i : V) :
    IsCutVertexRelative G S i ↔
    i ∈ S ∧ componentCount G (S.erase i) < componentCount G S := by
  rfl

end

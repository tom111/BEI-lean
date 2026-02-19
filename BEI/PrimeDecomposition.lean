import BEI.PrimeIdeals
import BEI.CohenMacaulay
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Prime decomposition of J_G (Theorem 3.2) and dimension corollaries

This file formalizes:
- **Theorem 3.2**: `J_G = ⋂_{S ⊆ V} P_S(G)`
- **Corollary 3.3**: dimension formula `dim(S/J_G) = max_S (|V\S| + c(S))`
- **Corollary 3.4**: if S/J_G is Cohen-Macaulay then `dim = n + c`
- **Corollary 3.7**: cycle characterization

## Reference: Herzog et al. (2010), Theorem 3.2 and Section 3
-/

noncomputable section

open MvPolynomial SimpleGraph

/-! ## Krull dimension placeholder -/

/--
Placeholder for the Krull dimension of a commutative ring.
The correct Mathlib API depends on the Mathlib version; use a sorry stub.
-/
noncomputable def ringKrullDim (R : Type*) [CommRing R] : ℕ := sorry

/-! ## Theorem 3.2: Prime decomposition -/

/--
**Theorem 3.2** (Herzog et al. 2010):
  `J_G = ⋂_{S ⊆ V} P_S(G)`

The proof has two inclusions:
- `J_G ⊆ P_S(G)` for all S: shown in `PrimeIdeals.lean`.
- `⋂ P_S(G) ⊆ J_G`: uses that J_G is radical (Corollary 2.2) and that the
  minimal primes of J_G are exactly the minimal `P_S(G)`.

Reference: Herzog et al. (2010), Theorem 3.2.
-/
theorem theorem_3_2 (G : SimpleGraph V) :
    binomialEdgeIdeal (K := K) G = ⨅ S : Finset V, primeComponent (K := K) G S := by
  sorry

/--
The minimal primes of `J_G` are exactly the minimal elements among `{P_S(G)}`.

Reference: Herzog et al. (2010), Theorem 3.2.
-/
theorem minimalPrimes_characterization (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).minimalPrimes =
    { P | ∃ S : Finset V,
        P = primeComponent (K := K) G S ∧
        ∀ T : Finset V, primeComponent (K := K) G T ≤ primeComponent (K := K) G S →
          primeComponent (K := K) G S ≤ primeComponent (K := K) G T } := by
  sorry

/-! ## Corollary 3.3: Dimension formula -/

/--
**Corollary 3.3** (Herzog et al. 2010):
  `dim(K[x,y]/J_G) = max_{S ⊆ V} (|V| - |S| + c(S))`

Reference: Herzog et al. (2010), Corollary 3.3.
-/
theorem corollary_3_3 (G : SimpleGraph V) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    ⨆ S : Finset V, (Fintype.card V - S.card + componentCount G S) := by
  sorry

/--
Lower bound: `dim(K[x,y]/J_G) ≥ |V| + c(G)`, where `c(G)` is the number of
connected components of G (taking S = ∅).

Reference: Herzog et al. (2010), Corollary 3.3.
-/
theorem corollary_3_3_lower_bound (G : SimpleGraph V) :
    Fintype.card V + componentCount G ∅ ≤
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) := by
  sorry

/-! ## Corollary 3.4: Cohen-Macaulay implies dimension equality -/

/--
**Corollary 3.4** (Herzog et al. 2010): If `K[x,y]/J_G` is Cohen-Macaulay, then
  `dim(K[x,y]/J_G) = |V| + c(G)`
where `c(G)` is the number of connected components of G.

Reference: Herzog et al. (2010), Corollary 3.4.
-/
theorem corollary_3_4 (G : SimpleGraph V)
    (hCM : IsCohenMacaulay (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    Fintype.card V + componentCount G ∅ := by
  sorry

/-! ## Corollary 3.7: Cycles -/

/-- A graph G on V is a cycle (every vertex has exactly 2 neighbors). -/
def IsCycleGraph (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ v : V, ∃ u w : V, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ ∀ z : V, G.Adj v z → z = u ∨ z = w

/--
**Corollary 3.7** (Herzog et al. 2010): For a cycle G of length n ≥ 3:
  (a) n = 3
  (b) J_G is prime
  (c) J_G is unmixed
  (d) K[x,y]/J_G is Cohen-Macaulay
are all equivalent.

Reference: Herzog et al. (2010), Corollary 3.7.
-/
theorem corollary_3_7 (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    Fintype.card V = 3 ↔ (binomialEdgeIdeal (K := K) G).IsPrime := by
  sorry

theorem corollary_3_7_CM (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    IsCohenMacaulay (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) ↔
    (binomialEdgeIdeal (K := K) G).IsPrime := by
  sorry

end

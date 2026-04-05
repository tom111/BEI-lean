import BEI.PrimeIdeals
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
Proposition 1.6: If G is connected, closed with respect to its labeling, and satisfies
the interval condition, then S/J_G is Cohen-Macaulay.

Reference: Herzog et al. (2010), Proposition 1.6.
-/
theorem prop_1_6 (n : ℕ) (G : SimpleGraph (Fin n))
    (hConn : G.Connected)
    (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsCohenMacaulay
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal G) := by
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

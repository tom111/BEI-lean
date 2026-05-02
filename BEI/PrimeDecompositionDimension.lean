import BEI.PrimeDecompositionDimensionCore
import BEI.CycleUnmixed
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Section 3 equidimensional surrogate package (Cor 3.4 + Cor 3.7)

This file collects the equidimensional surrogate forms of Corollaries 3.4 and
3.7, used downstream to assemble the paper-faithful theorems in
`BEI/Corollary3_4.lean`.

The dimension formula of Corollary 3.3 itself, together with the third-
isomorphism dimension lemma `ringKrullDim_quotQuot_eq`, lives in
`BEI/PrimeDecompositionDimensionCore.lean`. The path-graph (Example 1.7b) and
Proposition 1.6 surrogate machinery (together with the shared helper
`isEquidim_of_equidim_minimalPrimes`) lives in `BEI/Prop1_6Equidim.lean`.

## Public paper-facing endpoints

- `corollary_3_4_equidim`: equidimensional surrogate of Corollary 3.4.
- `corollary_3_7_equidim`: equidimensional surrogate of Corollary 3.7
  (cycle case).

## Reference: Herzog et al. (2010), Corollary 3.4, Corollary 3.7.
-/

noncomputable section

open MvPolynomial SimpleGraph

/-! ## Equidimensional variant of Corollary 3.4 -/

omit [DecidableEq V] in
/--
Direct equidimensional surrogate variant of Corollary 3.4: if
`K[x,y]/J_G` is equidimensional in the local BEI sense, then
  `dim(K[x,y]/J_G) = |V| + c(G)`
where `c(G)` is the number of connected components of G.

This is not the full depth-based Cohen-Macaulay statement from the paper.
-/
theorem corollary_3_4_equidim (G : SimpleGraph V)
    (hEq : IsEquidim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    Fintype.card V + componentCount G ∅ := by
  set J := binomialEdgeIdeal (K := K) G
  -- Step 1: CM equidimensionality → all minimal primes have equal quotient dimension
  have hequal : ∀ P Q : Ideal (MvPolynomial (BinomialEdgeVars V) K),
      P ∈ J.minimalPrimes → Q ∈ J.minimalPrimes →
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ Q) := by
    intro P Q hP hQ
    rw [Ideal.minimalPrimes_eq_comap] at hP hQ
    obtain ⟨P', hP'min, rfl⟩ := hP
    obtain ⟨Q', hQ'min, rfl⟩ := hQ
    rw [← ringKrullDim_quotQuot_eq J P', ← ringKrullDim_quotQuot_eq J Q']
    exact hEq.equidimensional P' Q' hP'min hQ'min
  -- Step 2: P_∅ is a minimal prime (T ≤ ∅ forces T = ∅ by prop_3_8)
  have hP0_min : primeComponent (K := K) G ∅ ∈ J.minimalPrimes := by
    rw [minimalPrimes_characterization]
    exact ⟨∅, rfl, fun T hT =>
      (Finset.subset_empty.mp ((prop_3_8 (K := K) G ∅ T).mp hT).1) ▸ le_refl _⟩
  -- Step 3: dim(R/P_∅) = |V| + c(G)
  have hdim0 : ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸
      primeComponent (K := K) G ∅) = ↑(Fintype.card V + componentCount G ∅) := by
    rw [ringKrullDim_quot_primeComponent]; simp
  -- Step 4: All minimal primes have the same quotient dimension
  have hall : ∀ P ∈ J.minimalPrimes,
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ↑(Fintype.card V + componentCount G ∅) := fun P hP =>
    (hequal P _ hP hP0_min).trans hdim0
  -- Step 5: dim(R/J) = sup over minimal primes = |V| + c(G)
  rw [ringKrullDim_quotient_radical _ (corollary_2_2 (K := K) G)]
  exact le_antisymm
    (iSup₂_le fun P hP => (hall P hP).le)
    (le_iSup₂_of_le _ hP0_min hdim0.ge)

/-! ## Corollary 3.7 equidimensional branch -/

/-- In a cycle graph with ≥ 4 vertices, the non-adjacent pair {u,w}
gives a minimal prime `P_{u,w}` (since both u and w are cut vertices
relative to {u,w}). -/
private lemma cycle_pair_minimalPrime (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (u w : V) (hne : u ≠ w) (hnadj : ¬G.Adj u w) (h4 : 4 ≤ Fintype.card V) :
    primeComponent (K := K) G {u, w} ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes := by
  rw [corollary_3_9 G {u, w} hCyc.1]
  right
  have hcuw := cycle_componentCount_pair_nonadj G hCyc u w hne hnadj h4
  have hcu := cycle_componentCount_singleton G hCyc u (by omega)
  have hcw := cycle_componentCount_singleton G hCyc w (by omega)
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  refine ⟨by rcases hi with rfl | rfl <;> simp, ?_⟩
  rcases hi with rfl | rfl
  · rw [show ({i, w} : Finset V).erase i = {w} from by simp [hne]]; omega
  · rw [show ({u, i} : Finset V).erase i = {u} from by rw [Finset.pair_comm]; simp [hne.symm]]
    omega

omit [DecidableEq V] in
/--
Direct equidimensional surrogate branch of Corollary 3.7: for a cycle graph `G`
with `|V| ≥ 3`, the local equidimensional surrogate for `K[x,y]/J_G` holds if and
only if `J_G` is prime (equivalently, `|V| = 3`).

The forward direction (equidim → prime) shows that when `|V| ≥ 4`, the minimal primes
`P_∅` and `P_{u,w}` (for non-adjacent u,w) have quotient dimensions |V|+1 and |V|
respectively, contradicting equidimensionality.

The reverse direction (prime → equidim) is immediate since prime ideals give domains,
and domains are equidimensional under the local surrogate.

This is not the full depth-based Cohen-Macaulay branch from the paper.
-/
theorem corollary_3_7_equidim (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    IsEquidim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) ↔
    (binomialEdgeIdeal (K := K) G).IsPrime := by
  constructor
  · -- CM → prime: by contradiction, |V| ≥ 4 has non-equidimensional minimal primes
    intro hCM
    rw [← corollary_3_7 G hCyc hn]
    by_contra h3
    have h4 : 4 ≤ Fintype.card V := by omega
    obtain ⟨u, w, hne, hnadj⟩ := cycle_exists_nonadj G hCyc h4
    set J := binomialEdgeIdeal (K := K) G
    -- P_∅ and P_{u,w} are both minimal primes
    have hP0 : primeComponent (K := K) G ∅ ∈ J.minimalPrimes := by
      rw [minimalPrimes_characterization]
      exact ⟨∅, rfl, fun T hT =>
        (Finset.subset_empty.mp ((prop_3_8 (K := K) G ∅ T).mp hT).1) ▸ le_refl _⟩
    have hPuw : primeComponent (K := K) G {u, w} ∈ J.minimalPrimes :=
      cycle_pair_minimalPrime G hCyc u w hne hnadj h4
    -- CM equidimensionality gives equal quotient dims
    have hequal : ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸
          primeComponent (K := K) G ∅) =
        ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸
          primeComponent (K := K) G {u, w}) := by
      rw [Ideal.minimalPrimes_eq_comap] at hP0 hPuw
      obtain ⟨P', hP'min, hP'eq⟩ := hP0
      obtain ⟨Q', hQ'min, hQ'eq⟩ := hPuw
      rw [← hP'eq, ← hQ'eq,
          ← ringKrullDim_quotQuot_eq J P', ← ringKrullDim_quotQuot_eq J Q']
      exact hCM.equidimensional P' Q' hP'min hQ'min
    -- Compute dimensions: |V|+1 vs |V|, contradiction
    rw [ringKrullDim_quot_primeComponent, ringKrullDim_quot_primeComponent] at hequal
    simp only [Finset.card_empty, Finset.card_pair hne] at hequal
    have hc0 : componentCount G ∅ = 1 := by
      rw [componentCount_empty]
      haveI := hCyc.1.preconnected.subsingleton_connectedComponent
      exact Nat.card_of_subsingleton (G.connectedComponentMk hCyc.1.nonempty.some)
    have hcuw := cycle_componentCount_pair_nonadj G hCyc u w hne hnadj h4
    rw [hc0, hcuw] at hequal
    norm_cast at hequal
    omega
  · -- prime → CM: domain is CM
    intro hPrime
    haveI := hPrime
    exact IsDomain.isEquidimRing

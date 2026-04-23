/-
Corollary 3.4 (Herzog et al. 2010): paper-faithful Cohen–Macaulay statement.

**Corollary 3.4.** Let `G` be a simple graph on `[n]` with `c` connected
components. If `S ⧸ J_G` is Cohen–Macaulay, then `dim(S ⧸ J_G) = n + c`.

The paper's proof uses that CM quotients are equidimensional, combined with
the fact that `P_∅(G)` is always a minimal prime of `J_G` with
`dim(S ⧸ P_∅) = n + c`.

This file assembles the paper-faithful version from:
- `GradedFiniteFree.isEquidimRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree`
  (graded CM ⟹ finite free over polynomial subring ⟹ equidim);
- `corollary_3_4_equidim` (equidim + `P_∅` minimal ⟹ dim = |V| + c(G,∅)).

The bridge between them uses the standard `ℕ`-grading on
`MvPolynomial (BinomialEdgeVars V) K` (each variable has degree 1) and the
descent to the quotient by the homogeneous ideal `J_G`.
-/

import BEI.PrimeDecompositionDimension
import BEI.Proposition1_6
import toMathlib.GradedEquidim
import toMathlib.GradedQuotient
import toMathlib.GradedIrrelevant
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

noncomputable section

open MvPolynomial SimpleGraph

universe u

variable {K : Type u} [Field K]
variable {V : Type u} [LinearOrder V] [DecidableEq V] [Fintype V]

/-- Standard `ℕ`-grading on `MvPolynomial (BinomialEdgeVars V) K`: each
variable has degree 1. -/
def beStandardWeight : BinomialEdgeVars V → ℕ := fun _ => 1

/-- Standard `ℕ`-grading submodule. -/
def beStandardGrading : ℕ → Submodule K (MvPolynomial (BinomialEdgeVars V) K) :=
  weightedHomogeneousSubmodule K (beStandardWeight : BinomialEdgeVars V → ℕ)

instance beStandardGrading_isGradedAlgebra :
    GradedAlgebra (beStandardGrading : ℕ → Submodule K (MvPolynomial (BinomialEdgeVars V) K)) :=
  weightedGradedAlgebra K _

/-- Under the standard grading, the binomial edge ideal `J_G` is homogeneous
of degree 2: each generator `x_i y_j - x_j y_i` has weighted degree 2 since
all variables have weight 1. -/
theorem binomialEdgeIdeal_isHomogeneous (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).IsHomogeneous beStandardGrading := by
  apply Ideal.homogeneous_span
  rintro f ⟨i, j, hij, hlt, rfl⟩
  refine ⟨2, ?_⟩
  change IsWeightedHomogeneous (beStandardWeight : BinomialEdgeVars V → ℕ)
    (x (K := K) i * y (K := K) j - x (K := K) j * y (K := K) i) 2
  refine (weightedHomogeneousSubmodule K beStandardWeight 2).sub_mem ?_ ?_
  · simpa [x, y] using
      (isWeightedHomogeneous_X (R := K) beStandardWeight (Sum.inl i)).mul
        (isWeightedHomogeneous_X (R := K) beStandardWeight (Sum.inr j))
  · simpa [x, y] using
      (isWeightedHomogeneous_X (R := K) beStandardWeight (Sum.inl j)).mul
        (isWeightedHomogeneous_X (R := K) beStandardWeight (Sum.inr i))

/-- Descend the grading to the quotient `R ⧸ J_G`. -/
abbrev beQuotientGrading (G : SimpleGraph V) :
    ℕ → Submodule K (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
  GradedQuotient.gradedQuotientPiece beStandardGrading (binomialEdgeIdeal (K := K) G)

set_option maxHeartbeats 400000 in
-- Building the quotient graded-ring instance unfolds the homogeneity witness aggressively.
noncomputable instance beQuotientGrading_isGradedRing (G : SimpleGraph V) :
    GradedRing (beQuotientGrading (K := K) G) :=
  GradedQuotient.gradedRing beStandardGrading (binomialEdgeIdeal (K := K) G)
    (binomialEdgeIdeal_isHomogeneous G)

/-- The quotient `R ⧸ J_G` is connected graded: its degree-0 piece is `K`. -/
theorem beQuotientGrading_connectedGraded (G : SimpleGraph V) :
    GradedIrrelevant.ConnectedGraded (beQuotientGrading (K := K) G) := by
  intro x hx
  obtain ⟨p, hp_mem, rfl⟩ := hx
  change p ∈ weightedHomogeneousSubmodule K (beStandardWeight : BinomialEdgeVars V → ℕ) 0 at hp_mem
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hp_mem
  obtain ⟨k, hk⟩ : ∃ k : K, p = MvPolynomial.C k := by
    refine ⟨p.coeff 0, ?_⟩
    ext d
    rw [coeff_C]
    split_ifs with hd
    · subst hd; rfl
    · by_contra hne
      have hsupp : d ∈ p.support := by
        rw [mem_support_iff]; exact hne
      have hw : Finsupp.weight beStandardWeight d = 0 :=
        hp_mem (by rwa [mem_support_iff] at hsupp)
      have hd_zero : d = 0 := by
        apply Finsupp.ext
        intro v
        have hv_le : d v ≤ Finsupp.weight beStandardWeight d := by
          rw [Finsupp.weight_apply]
          unfold beStandardWeight
          have : d v * 1 ≤ ∑ v ∈ d.support, d v * 1 := by
            by_cases hv : v ∈ d.support
            · exact Finset.single_le_sum (f := fun v => d v * 1)
                (fun _ _ => Nat.zero_le _) hv
            · simp [Finsupp.notMem_support_iff.mp hv]
          simpa [Finsupp.sum] using this
        rw [hw] at hv_le
        exact Nat.le_zero.mp hv_le
      exact hd hd_zero.symm
  refine ⟨k, ?_⟩
  rw [hk]
  simp

/-- `R ⧸ J_G` is nontrivial: `J_G ≠ ⊤`. -/
theorem beQuotient_nontrivial (G : SimpleGraph V) :
    Nontrivial (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) := by
  rw [Ideal.Quotient.nontrivial_iff]
  intro htop
  have h1 : (1 : MvPolynomial (BinomialEdgeVars V) K) ∈ binomialEdgeIdeal (K := K) G := by
    rw [htop]; exact Submodule.mem_top
  have hcc : MvPolynomial.constantCoeff (σ := BinomialEdgeVars V) (R := K)
      (1 : MvPolynomial (BinomialEdgeVars V) K) = 0 := by
    change (1 : MvPolynomial (BinomialEdgeVars V) K) ∈
      Ideal.span { f | ∃ i j, G.Adj i j ∧ i < j ∧ f = x i * y j - x j * y i } at h1
    refine Submodule.span_induction ?_ ?_ ?_ ?_ h1
    · rintro f ⟨i, j, hij, hlt, rfl⟩
      simp [x, y, MvPolynomial.constantCoeff_X]
    · simp
    · intro a b _ _ ha hb
      simp [ha, hb]
    · intro c a _ ha
      simp [ha]
  simp at hcc

noncomputable instance beQuotient_nontrivial_inst (G : SimpleGraph V) :
    Nontrivial (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
  beQuotient_nontrivial G

/-- The quotient is a finite-type `K`-algebra (quotient of a finitely generated algebra). -/
instance beQuotient_finiteType (G : SimpleGraph V) :
    Algebra.FiniteType K (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
  Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ K (binomialEdgeIdeal (K := K) G))
    (Ideal.Quotient.mkₐ_surjective K _)

/-- The quotient is Noetherian (quotient of Noetherian ring). -/
instance beQuotient_isNoetherian (G : SimpleGraph V) :
    IsNoetherianRing (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
  inferInstance

/-- **CM ⇒ equidim for binomial edge ideals.** The core bridge used by the
paper-faithful §3 statements: if `S ⧸ J_G` is Cohen–Macaulay, it is
equidimensional in the local surrogate sense.

Route: the standard `ℕ`-grading on `MvPolynomial (BinomialEdgeVars V) K`
descends to the quotient (since `J_G` is homogeneous). The quotient is a
connected graded f.g. Noetherian `K`-algebra, so CM globally ⇒ CM at the
irrelevant ideal (`CM_localize`) ⇒ finite free over a polynomial subring
⇒ equidimensional. -/
theorem isEquidim_of_isCohenMacaulayRing_binomialEdge (G : SimpleGraph V)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    IsEquidim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) := by
  letI : Nontrivial
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
    beQuotient_nontrivial G
  letI : GradedRing (beQuotientGrading (K := K) G) := inferInstance
  have hconn : GradedIrrelevant.ConnectedGraded (beQuotientGrading (K := K) G) :=
    beQuotientGrading_connectedGraded G
  haveI hirrMax := GradedIrrelevant.irrelevant_isMaximal (beQuotientGrading (K := K) G) hconn
  haveI : (HomogeneousIdeal.irrelevant (beQuotientGrading (K := K) G)).toIdeal.IsPrime :=
    hirrMax.isPrime
  have hCM_loc :
      IsCohenMacaulayLocalRing (Localization.AtPrime
        (HomogeneousIdeal.irrelevant (beQuotientGrading (K := K) G)).toIdeal) :=
    hCM.CM_localize _
  exact
    GradedFiniteFree.isEquidimRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree
      (beQuotientGrading (K := K) G) hconn hCM_loc

/-- **Paper-faithful Corollary 3.4.** If `S ⧸ J_G` is Cohen–Macaulay, then
`dim(S ⧸ J_G) = |V| + c(G)`. -/
theorem corollary_3_4 (G : SimpleGraph V)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    ↑(Fintype.card V + componentCount G ∅) :=
  corollary_3_4_equidim (K := K) G (isEquidim_of_isCohenMacaulayRing_binomialEdge G hCM)

/-- **Corollary 3.4 for connected graphs.** If `G` is connected and
`S ⧸ J_G` is CM, then `dim(S ⧸ J_G) = |V| + 1`. -/
theorem corollary_3_4_connected (G : SimpleGraph V) (hConn : G.Connected)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    ↑(Fintype.card V + 1) := by
  have hc : componentCount G ∅ = 1 := by
    rw [componentCount_empty]
    haveI := hConn.preconnected.subsingleton_connectedComponent
    exact Nat.card_of_subsingleton (G.connectedComponentMk hConn.nonempty.some)
  simpa [hc] using corollary_3_4 (K := K) G hCM

end

/-! ## Corollary 3.7, Cohen–Macaulay branch

The paper's Corollary 3.7 asserts the equivalence of

  (a) `n = 3`
  (b) `J_G` is prime
  (c) `J_G` is unmixed
  (d) `S ⧸ J_G` is Cohen–Macaulay

for a cycle `G` of length `n`. Existing files already handle the (a ↔ b) and
(a ↔ c) equivalences (`corollary_3_7` in `BEI/PrimeDecomposition.lean`,
`corollary_3_7_unmixed` in `BEI/MinimalPrimes.lean`) and the equidimensional
surrogate of the CM branch (`corollary_3_7_equidim` in
`BEI/PrimeDecompositionDimension.lean`).

Below we close (a ↔ d). The forward direction (CM → `n = 3`) chains

  CM  ⟹  IsEquidim  ⟹  IsPrime  ⟹  `n = 3`

using `isEquidim_of_isCohenMacaulayRing_binomialEdge` (above),
`corollary_3_7_equidim`, and `corollary_3_7`. The backward direction is
proved for `G : SimpleGraph (Fin n)` by invoking `proposition_1_6` on the
3-cycle (which coincides with `K_3` and is closed, satisfying the Prop 1.6
transitivity condition vacuously).
-/

section Corollary3_7_CM

variable {K : Type} [Field K]
variable {V : Type} [LinearOrder V] [DecidableEq V] [Fintype V]

/-- **Cor 3.7 forward (CM → cycle length = 3).** For a cycle `G` on `V` with
`|V| ≥ 3`, Cohen–Macaulayness of `S ⧸ J_G` forces `|V| = 3`.

Chain: `CM ⟹ IsEquidim` (`isEquidim_of_isCohenMacaulayRing_binomialEdge`)
`⟹ IsPrime` (`corollary_3_7_equidim`) `⟹ |V| = 3` (`corollary_3_7`). -/
theorem corollary_3_7_cm_forward (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V)
    (hCM : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    Fintype.card V = 3 := by
  have hEq := isEquidim_of_isCohenMacaulayRing_binomialEdge (K := K) G hCM
  have hPrime := (corollary_3_7_equidim (K := K) G hCyc hn).mp hEq
  exact (corollary_3_7 (K := K) G hCyc hn).mpr hPrime

/-- In a cycle graph with exactly three vertices, every pair of distinct
vertices is adjacent. -/
private theorem cycle_card3_adj_of_ne (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hcard : Fintype.card V = 3) {u w : V} (huw : u ≠ w) : G.Adj u w := by
  obtain ⟨_, hDeg⟩ := hCyc
  obtain ⟨n1, n2, hn12, hadj1, hadj2, honly⟩ := hDeg u
  -- {u, n1, n2} has 3 distinct elements = |V|, hence = univ.
  have h3 : ({u, n1, n2} : Finset V).card = Fintype.card V := by
    rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair hn12]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨G.ne_of_adj hadj1, G.ne_of_adj hadj2⟩
  have hw_mem := (Finset.eq_univ_of_card _ h3) ▸ Finset.mem_univ w
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
  rcases hw_mem.resolve_left (Ne.symm huw) with rfl | rfl
  · exact hadj1
  · exact hadj2

/-- **Cor 3.7 backward, Fin version (cycle length = 3 ⟹ CM).** For a cycle
graph `G` on `Fin n` with `n = 3`, `S ⧸ J_G` is Cohen–Macaulay.

Proof: `G` is the complete graph on 3 vertices (every pair adjacent), which
is closed and satisfies Proposition 1.6's transitivity condition vacuously
(the condition requires `k + 1 < n = 3`, impossible once `j < k` with
`i, j, k : Fin 3`). Apply `proposition_1_6`. -/
theorem corollary_3_7_cm_backward_fin {n : ℕ} {G : SimpleGraph (Fin n)}
    (hCyc : IsCycleGraph G) (hn : n = 3) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) := by
  have hcard : Fintype.card (Fin n) = 3 := by simp [hn]
  have hAdj : ∀ u w : Fin n, u ≠ w → G.Adj u w :=
    fun u w huw => cycle_card3_adj_of_ne G hCyc hcard huw
  have h2n : 2 ≤ n := by omega
  have hClosed : IsClosedGraph G := by
    refine ⟨?_, ?_⟩
    · intro i j k _ _ hjk _ _; exact hAdj j k hjk
    · intro i j k _ _ hij _ _; exact hAdj i j hij
  have hCond : SatisfiesProp1_6Condition n G := by
    intro i j k hj hk hij hjk _ _
    -- Need contradiction: i < j < k in Fin n = Fin 3, with k.val + 1 < 3.
    have : k.val + 1 < 3 := hn ▸ hk
    have : k.val < 2 := by omega
    have : j.val < k.val := hjk
    have : i.val < j.val := hij
    omega
  exact proposition_1_6 (K := K) h2n hCyc.1 hClosed hCond

/-- **Paper-faithful Corollary 3.7, Fin version, Cohen–Macaulay branch.**

For a cycle `G` on `Fin n` with `n ≥ 3`,
`S ⧸ J_G` is Cohen–Macaulay ↔ `n = 3`. -/
theorem corollary_3_7_cm_fin {n : ℕ} (hn : 3 ≤ n) {G : SimpleGraph (Fin n)}
    (hCyc : IsCycleGraph G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal (K := K) G) ↔
    n = 3 := by
  constructor
  · intro hCM
    have := corollary_3_7_cm_forward (K := K) G hCyc (by simpa using hn) hCM
    simpa using this
  · intro h3
    exact corollary_3_7_cm_backward_fin (K := K) hCyc h3

end Corollary3_7_CM

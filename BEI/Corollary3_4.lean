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
import toMathlib.GradedEquidim
import toMathlib.GradedQuotient
import toMathlib.GradedIrrelevant
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

set_option maxHeartbeats 400000

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
  have hx : ∀ v : V, IsWeightedHomogeneous
      (beStandardWeight : BinomialEdgeVars V → ℕ)
      (x (K := K) v) 1 :=
    fun v => isWeightedHomogeneous_X (R := K) beStandardWeight _
  have hy : ∀ v : V, IsWeightedHomogeneous
      (beStandardWeight : BinomialEdgeVars V → ℕ)
      (y (K := K) v) 1 :=
    fun v => isWeightedHomogeneous_X (R := K) beStandardWeight _
  have hxy : IsWeightedHomogeneous beStandardWeight
      (x (K := K) i * y (K := K) j) 2 := by
    have := (hx i).mul (hy j)
    simpa using this
  have hyx : IsWeightedHomogeneous beStandardWeight
      (x (K := K) j * y (K := K) i) 2 := by
    have := (hx j).mul (hy i)
    simpa using this
  exact (weightedHomogeneousSubmodule K beStandardWeight 2).sub_mem hxy hyx

/-- Descend the grading to the quotient `R ⧸ J_G`. -/
abbrev beQuotientGrading (G : SimpleGraph V) :
    ℕ → Submodule K (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
  GradedQuotient.gradedQuotientPiece beStandardGrading (binomialEdgeIdeal (K := K) G)

noncomputable instance beQuotientGrading_isGradedRing (G : SimpleGraph V) :
    GradedRing (beQuotientGrading (K := K) G) :=
  GradedQuotient.gradedRing beStandardGrading (binomialEdgeIdeal (K := K) G)
    (binomialEdgeIdeal_isHomogeneous G)

/-- The quotient `R ⧸ J_G` is connected graded: its degree-0 piece is `K`. -/
theorem beQuotientGrading_connectedGraded (G : SimpleGraph V) :
    GradedIrrelevant.ConnectedGraded (beQuotientGrading (K := K) G) := by
  intro x hx
  -- hx : x ∈ gradedQuotientPiece beStandardGrading (binomialEdgeIdeal G) 0
  -- which unfolds to image of beStandardGrading 0 under `Ideal.Quotient.mkₐ K _`.
  obtain ⟨p, hp_mem, rfl⟩ := hx
  -- p ∈ beStandardGrading 0, i.e. `IsWeightedHomogeneous beStandardWeight p 0`.
  change p ∈ weightedHomogeneousSubmodule K (beStandardWeight : BinomialEdgeVars V → ℕ) 0 at hp_mem
  rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hp_mem
  -- A weighted-homogeneous polynomial of degree 0 is a scalar (since weight ≥ 1 everywhere).
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
  -- Goal: algebraMap K (A⧸J) k = (Ideal.Quotient.mkₐ K J).toLinearMap (C k)
  simp [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mk_algebraMap,
    MvPolynomial.algebraMap_eq]

/-- `R ⧸ J_G` is nontrivial: `J_G ≠ ⊤`. -/
theorem beQuotient_nontrivial (G : SimpleGraph V) :
    Nontrivial (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) := by
  refine Ideal.Quotient.nontrivial ?_
  -- J_G ≠ ⊤: the ideal is homogeneous and contained in the irrelevant ideal of the
  -- polynomial ring (all generators have positive degree), hence proper.
  intro htop
  have h1 : (1 : MvPolynomial (BinomialEdgeVars V) K) ∈ binomialEdgeIdeal (K := K) G := by
    rw [htop]; exact Submodule.mem_top
  -- Apply the graded projection at degree 0: projects 1 ↦ 1, and all generators to 0.
  -- If 1 ∈ J_G (a homogeneous ideal), decompose 1 as sum of homogeneous pieces lying in J_G.
  -- 1 has a unique degree-0 component = 1, so 1 ∈ J_G at degree 0. But J_G at degree 0 = 0.
  have hhom := binomialEdgeIdeal_isHomogeneous (K := K) G 0 h1
  -- hhom: the degree-0 component of 1 is in J_G
  have h01 : (DirectSum.decompose beStandardGrading
      (1 : MvPolynomial (BinomialEdgeVars V) K) 0 : MvPolynomial (BinomialEdgeVars V) K) = 1 := by
    rw [DirectSum.decompose_of_mem_same beStandardGrading
      (show (1 : MvPolynomial (BinomialEdgeVars V) K) ∈ beStandardGrading 0 from
        SetLike.GradedOne.one_mem)]
  rw [h01] at hhom
  -- Now hhom : (1 : R) ∈ J_G at degree 0; but more importantly, 1 ∈ J_G.
  -- Actually hhom states "the decomposition at 0" is in J_G. That's just 1 ∈ J_G.
  -- We already have h1 : 1 ∈ J_G. We need to derive contradiction via grading piece argument.
  -- A homogeneous polynomial p ∈ J_G of degree 0 must be 0 (because J_G's generators have
  -- positive degree, and a nonzero degree-0 polynomial would be a unit).
  -- The simpler argument: the projection of 1 mod J_G at degree 0 is a scalar, and if
  -- J_G ∋ 1, the projection is 0, contradicting 1 ≠ 0 in K.
  -- But `beStandardGrading 0 = {constant polys}` and `J_G ∩ {constants} = {0}`.
  -- Because the generators' leading terms / constants give J_G ∩ constants = 0.
  -- Lean-friendly: `1 ∈ J_G ∩ (weightedHomogeneousSubmodule K beStandardWeight 0)` — but this
  -- needs the actual content that J_G's constant part is zero.
  -- Use: submodule of constants intersected with J_G = 0. This follows because all J_G
  -- generators are in the irrelevant ideal `𝔪 = ⟨X v⟩`, which is proper. So 1 ∉ 𝔪, hence 1 ∉ J_G.
  -- Cleaner: show J_G ≤ 𝔪, where 𝔪 = `binomialEdgeIdeal_le_span_inl` type argument, but we
  -- want a pure proof. Use the ring hom `MvPolynomial R → R` (eval at 0): evaluates x_i, y_j
  -- all to 0, so J_G generators → 0. If 1 ∈ J_G, then eval(1) = 1 = 0 in K, contradiction.
  have heval : (MvPolynomial.constantCoeff (σ := BinomialEdgeVars V) (R := K) :
      MvPolynomial (BinomialEdgeVars V) K →+* K) 1 = 0 := by
    have : (binomialEdgeIdeal (K := K) G).map
        (MvPolynomial.constantCoeff (σ := BinomialEdgeVars V) (R := K)) = ⊥ := by
      refine le_bot_iff.mp ?_
      rw [Ideal.map_le_iff_le_comap]
      intro f hf
      -- f ∈ J_G: need to show constantCoeff f = 0
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
      · rintro g ⟨i, j, hij, hlt, rfl⟩
        simp only [Ideal.mem_comap, Submodule.mem_bot, map_sub, map_mul]
        change (MvPolynomial.constantCoeff (x (K := K) i)) *
            (MvPolynomial.constantCoeff (y (K := K) j)) -
          (MvPolynomial.constantCoeff (x (K := K) j)) *
            (MvPolynomial.constantCoeff (y (K := K) i)) = 0
        simp [x, y, MvPolynomial.constantCoeff_X]
      · simp
      · intros a b _ _ ha hb
        rw [Ideal.mem_comap, Submodule.mem_bot] at ha hb ⊢
        simp [map_add, ha, hb]
      · intros c a _ ha
        rw [Ideal.mem_comap, Submodule.mem_bot] at ha ⊢
        simp [map_mul, ha]
    have h1map : MvPolynomial.constantCoeff (σ := BinomialEdgeVars V) (R := K) 1 ∈
        (binomialEdgeIdeal (K := K) G).map MvPolynomial.constantCoeff :=
      Ideal.mem_map_of_mem _ h1
    rw [this, Submodule.mem_bot] at h1map
    exact h1map
  rw [map_one] at heval
  exact one_ne_zero heval

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
  haveI : Nontrivial
      (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
    beQuotient_nontrivial G
  haveI hgr : GradedRing (beQuotientGrading (K := K) G) :=
    GradedQuotient.gradedRing beStandardGrading (binomialEdgeIdeal (K := K) G)
      (binomialEdgeIdeal_isHomogeneous G)
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
  have h := corollary_3_4 (K := K) G hCM
  have hc : componentCount G ∅ = 1 := by
    rw [componentCount_empty]
    haveI := hConn.preconnected.subsingleton_connectedComponent
    exact Nat.card_of_subsingleton (G.connectedComponentMk hConn.nonempty.some)
  rw [h, hc]

end

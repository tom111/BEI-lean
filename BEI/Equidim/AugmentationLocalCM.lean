import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import BEI.Equidim.Transport
import BEI.Equidim.ClosedGraphIntervals
import BEI.Equidim.IteratedRegularity
import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import BEI.ReducedHH
import toMathlib.Equidim.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
import toMathlib.QuotientDimension
import toMathlib.IdealQuotientHelpers
import toMathlib.MinimalPrimesRegular
import toMathlib.MvPolynomialHomogeneous
import toMathlib.CohenMacaulay.Defs
import toMathlib.CohenMacaulay.Basic
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.TensorPolynomialAway
import toMathlib.PolynomialAwayTensor
import toMathlib.TensorLocalisation
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.MvPolynomial

noncomputable section

open MvPolynomial SimpleGraph

/-!
# Equidimensional surrogate: augmentation ideal and local Cohen-Macaulayness

This file isolates the augmentation-ideal-level Cohen-Macaulay machinery
for the HH bipartite edge monomial ideal: the augmentation ideal `augIdeal`,
its primality / maximality, the last-pair-permutation lemmas
`isSMulRegular_mk_y_last`, and the local Cohen-Macaulay theorem
`isCohenMacaulayLocalRing_reducedHH_at_augIdeal`. Hosts the
`set_option synthInstance.maxHeartbeats 250000` block needed for the
local CM proof.

## Reference: Herzog et al. (2010), proof of Proposition 1.6
-/

/-! ### Augmentation ideal and local CM -/

section AugmentationCM

variable {K : Type*} [Field K]
open MvPolynomial RingTheory.Sequence

/-- All generators of the bipartite edge monomial ideal have zero constant term. -/
private lemma bipartiteEdgeMonomialIdeal_le_ker_constantCoeff {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    bipartiteEdgeMonomialIdeal (K := K) G ≤
      RingHom.ker (MvPolynomial.constantCoeff (R := K)
        (σ := BinomialEdgeVars (Fin n))) := by
  apply Ideal.span_le.mpr
  intro f hf
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  obtain ⟨a, b, _, _, _, rfl⟩ := hf
  simp [constantCoeff_X]

/-- The factored constant coefficient map `S/I → K`. -/
noncomputable def quotConstCoeff {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G →+* K :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff
    (bipartiteEdgeMonomialIdeal_le_ker_constantCoeff G)

/-- The factored constant coefficient map is surjective (via `C`). -/
private lemma quotConstCoeff_surjective {n : ℕ} (G : SimpleGraph (Fin n)) :
    Function.Surjective (quotConstCoeff (K := K) G) := by
  intro k
  exact ⟨Ideal.Quotient.mk _ (C k), by simp [quotConstCoeff, constantCoeff_C]⟩

/-- The augmentation ideal of `S/I`: kernel of the evaluation-at-zero map. -/
noncomputable def augIdeal {n : ℕ} (G : SimpleGraph (Fin n)) :
    Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
  RingHom.ker (quotConstCoeff (K := K) G)

/-- The augmentation ideal is maximal. -/
lemma augIdeal_isMaximal {n : ℕ} (G : SimpleGraph (Fin n)) :
    (augIdeal (K := K) G).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (quotConstCoeff_surjective G)

/-- Variable images are in the augmentation ideal. -/
lemma mkI_X_mem_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    (v : BinomialEdgeVars (Fin n)) :
    Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∈
      augIdeal (K := K) G := by
  rw [augIdeal, RingHom.mem_ker, quotConstCoeff]
  simp [constantCoeff_X]

/-- Sums of variable images are in the augmentation ideal. -/
private lemma mkI_X_add_X_mem_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : BinomialEdgeVars (Fin n)) :
    Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v + X w) ∈
      augIdeal (K := K) G := by
  rw [map_add]
  exact (augIdeal G).add_mem (mkI_X_mem_augIdeal G v) (mkI_X_mem_augIdeal G w)

/-- All elements of the full regular sequence are in the augmentation ideal. -/
private lemma fullRegSeq_mem_augIdeal {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    ∀ r ∈ (fullRegSeq (K := K) n hn).map
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)),
      r ∈ augIdeal (K := K) G := by
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨f, hf, rfl⟩ := hr
  simp only [fullRegSeq, List.mem_append, List.mem_cons] at hf
  rcases hf with hf | hf | hf
  · -- f is a diagonal element
    simp only [diagElems, List.mem_ofFn] at hf
    obtain ⟨j, rfl⟩ := hf
    exact mkI_X_add_X_mem_augIdeal G _ _
  · -- f = X(inl ⟨n-1, _⟩)
    subst hf; exact mkI_X_mem_augIdeal G _
  · -- f = X(inr ⟨n-1, _⟩)
    simp only [List.mem_nil_iff, or_false] at hf
    subst hf; exact mkI_X_mem_augIdeal G _

instance augIdeal_isPrime {n : ℕ} (G : SimpleGraph (Fin n)) :
    (augIdeal (K := K) G).IsPrime := (augIdeal_isMaximal G).isPrime

/-- **Cohen–Macaulay at the augmentation ideal**: Under HH conditions with `n ≥ 2`,
the localization of `S ⧸ bipartiteEdgeMonomialIdeal G` at the augmentation ideal
is a Cohen–Macaulay local ring. -/
theorem isCohenMacaulayLocalRing_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K) G)) := by
  set p := augIdeal (K := K) G with p_def
  set Rₚ := Localization.AtPrime p with Rₚ_def
  -- Step 1: Get the weakly regular sequence and its membership
  set rs := (fullRegSeq (K := K) n hn).map
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
  have hreg_R := bipartiteEdgeMonomialIdeal_isWeaklyRegular_full (K := K) hn hHH
  have hmem_p := fullRegSeq_mem_augIdeal (K := K) hn G
  -- Step 2: Transfer to regular → weakly regular at localization
  have hwreg : IsWeaklyRegular Rₚ (rs.map (algebraMap _ Rₚ)) :=
    (IsWeaklyRegular.isRegular_of_isLocalization_of_mem Rₚ p hreg_R hmem_p).toIsWeaklyRegular
  -- Step 3: All mapped elements are in the maximal ideal of Rₚ
  have hmem : ∀ r ∈ rs.map (algebraMap _ Rₚ), r ∈ IsLocalRing.maximalIdeal Rₚ := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hmem_p s hs)
  -- Step 4: Length = n + 1
  have hlen : (rs.map (algebraMap _ Rₚ)).length = n + 1 := by
    simp only [List.length_map, rs, fullRegSeq_length hn]
  -- Step 5: Dimension of Rₚ = n + 1
  have hdim : ringKrullDim Rₚ = ↑(n + 1 : ℕ) := by
    apply le_antisymm
    · -- dim(Rₚ) = height(p) ≤ dim(R) = n + 1
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ,
        Ideal.height_eq_primeHeight]
      exact Ideal.primeHeight_le_ringKrullDim.trans
        (ringKrullDim_bipartiteEdgeMonomialIdeal (by omega) hHH).le
    · -- n + 1 ≤ dim(Rₚ): from the weakly regular sequence
      calc ↑(↑(n + 1 : ℕ) : ℕ∞) = ↑(rs.map (algebraMap _ Rₚ)).length := by
              rw [hlen]; rfl
        _ ≤ ringKrullDim Rₚ :=
              weaklyRegular_length_le_ringKrullDim Rₚ hwreg hmem
  -- Step 6: Apply CM criterion
  exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim hwreg hmem
    (show ringKrullDim Rₚ = ↑(rs.map (algebraMap _ Rₚ)).length by
      rw [hdim, hlen])

/-! #### Last-pair permutation: [X(inl last), X(inr last), diagElems…] weakly regular -/

open List in
/-- The fullRegSeq permuted to have the last pair first is still weakly regular on
`(A_H)_aug`. This is a direct application of
`IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal`. -/
private lemma lastPair_prefix_isWeaklyRegular_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    let mk := Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
    let Rp := Localization.AtPrime (augIdeal (K := K) G)
    let last : Fin n := ⟨n - 1, by omega⟩
    let rs_perm : List Rp :=
      [algebraMap _ Rp (mk (X (Sum.inl last))),
       algebraMap _ Rp (mk (X (Sum.inr last)))] ++
      ((diagElems n).map mk).map (algebraMap _ Rp)
    RingTheory.Sequence.IsWeaklyRegular Rp rs_perm := by
  intro mk Rp last rs_perm
  set p := augIdeal (K := K) G
  -- Start from the regular sequence on Rp
  set rs : List Rp := ((fullRegSeq (K := K) n hn).map mk).map (algebraMap _ Rp)
  have hreg_R := bipartiteEdgeMonomialIdeal_isWeaklyRegular_full (K := K) hn hHH
  have hmem_p := fullRegSeq_mem_augIdeal (K := K) hn G
  have hwreg : RingTheory.Sequence.IsWeaklyRegular Rp rs :=
    (IsWeaklyRegular.isRegular_of_isLocalization_of_mem Rp p hreg_R hmem_p).toIsWeaklyRegular
  have hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal Rp := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hmem_p s hs)
  -- rs.Perm rs_perm: the two differ by moving last two elements to the front
  have hperm : rs.Perm rs_perm := by
    -- fullRegSeq = diagElems ++ [X(inl last)] ++ [X(inr last)]
    -- rs = mapped(diagElems ++ [X(inl last), X(inr last)])
    -- rs_perm = [X(inl last), X(inr last)] ++ mapped diagElems
    simp only [rs, rs_perm, fullRegSeq, List.map_append, List.map_cons, List.map_nil]
    -- Goal: ((diagElems n).map mk).map alg ++ [alg (mk X(inl)), alg (mk X(inr))] ~
    --       [alg (mk X(inl)), alg (mk X(inr))] ++ ((diagElems n).map mk).map alg
    exact List.perm_append_comm
  -- Apply permutation lemma
  exact IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hwreg hperm hmem

/-- Extract the first IsSMulRegular from the permuted regular sequence: `X(inl last)`
is `IsSMulRegular` in `(A_H)_aug`. -/
private lemma isSMulRegular_X_inl_last_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsSMulRegular (Localization.AtPrime (augIdeal (K := K) G))
      (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))) := by
  have hwreg := lastPair_prefix_isWeaklyRegular_at_augIdeal (K := K) hn hHH
  simp only [List.cons_append, List.nil_append] at hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hwreg
  exact hwreg.1

/-- `X(inl last)` lies in the maximal ideal of `(A_H)_aug`. -/
lemma X_inl_last_mem_maximalIdeal {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) :
    (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (augIdeal (K := K) G)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (mkI_X_mem_augIdeal G _)

/-- **Reduced HH CM, half 1**: quotient of `(A_H)_aug` by `X(inl last)` is CM local. -/
theorem isCohenMacaulayLocalRing_quot_lastInl {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    haveI : IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K) G)) :=
      isCohenMacaulayLocalRing_at_augIdeal hn hHH
    haveI := quotSMulTopLocalRing (X_inl_last_mem_maximalIdeal (K := K) (by omega) G)
    IsCohenMacaulayLocalRing (QuotSMulTop
      (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨n - 1, by omega⟩))))
      (Localization.AtPrime (augIdeal (K := K) G))) := by
  haveI : IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K) G)) :=
    isCohenMacaulayLocalRing_at_augIdeal hn hHH
  exact isCohenMacaulayLocalRing_quotient
    (isSMulRegular_X_inl_last_at_augIdeal hn hHH)
    (X_inl_last_mem_maximalIdeal (by omega) G)

/-- `X(inr last)` is `IsSMulRegular` on `QuotSMulTop x_last Rp` (as Rp-module). -/
lemma isSMulRegular_X_inr_last_quot_lastInl {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsSMulRegular
      (QuotSMulTop
        (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨n - 1, by omega⟩))))
        (Localization.AtPrime (augIdeal (K := K) G)))
      (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨n - 1, by omega⟩)))) := by
  have hwreg := lastPair_prefix_isWeaklyRegular_at_augIdeal (K := K) hn hHH
  simp only [List.cons_append, List.nil_append] at hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hwreg
  obtain ⟨_, hwreg2⟩ := hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hwreg2
  exact hwreg2.1

/-- `X(inr last)` lies in the maximal ideal of `(A_H)_aug`. -/
lemma X_inr_last_mem_maximalIdeal {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) :
    (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨n - 1, by omega⟩)))) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (augIdeal (K := K) G)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (mkI_X_mem_augIdeal G _)

set_option synthInstance.maxHeartbeats 250000 in
-- synth budget needed: nested quotient + localization instance search is heavy.
/-- `mk y_last` (image of `X(inr last)` in the first quotient) is `IsSMulRegular`
on `QuotSMulTop x_last Rp`, extracted via the *primed* cons_iff lemma which
produces the correct scalar type. -/
private lemma isSMulRegular_mk_y_last {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    let Rp := Localization.AtPrime (augIdeal (K := K) G)
    let x_last : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))
    let y_last : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨n - 1, by omega⟩)))
    IsSMulRegular (QuotSMulTop x_last Rp)
      (Ideal.Quotient.mk (Ideal.span {x_last}) y_last) := by
  intro Rp x_last y_last
  have hwreg := lastPair_prefix_isWeaklyRegular_at_augIdeal (K := K) hn hHH
  simp only [List.cons_append, List.nil_append] at hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff'] at hwreg
  obtain ⟨_, hwreg2⟩ := hwreg
  simp only [List.map_cons] at hwreg2
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff'] at hwreg2
  exact hwreg2.1

/-- `Ideal.span {x_last}` is proper (x_last is not a unit since it's in maximalIdeal). -/
lemma span_x_inl_last_ne_top {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))} ≠ (⊤ : Ideal _) := by
  intro htop
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))) :=
    Ideal.span_singleton_eq_top.mp htop
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (X_inl_last_mem_maximalIdeal (K := K) hn G) hunit

end AugmentationCM

end

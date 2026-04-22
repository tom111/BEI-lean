/-
Copyright: BEI Lean project.

# Homogeneous regular systems of parameters: single descent step

Step A of `guides/answers/ANSWER_CASE_C_FINITE_FREE_ROUTE.md`, packaged as a
**single-step** descent result:

For a connected ℕ-graded Noetherian `K`-algebra `A` with `A_{𝒜₊}`
Cohen–Macaulay local of strictly positive Krull dimension, there exists a
homogeneous `ℓ ∈ 𝒜₊` that is an `A`-regular non-zero-divisor and such that
`A ⧸ ⟨ℓ⟩` is still a connected ℕ-graded Noetherian `K`-algebra whose
localization at the image of the irrelevant ideal is Cohen–Macaulay local.

Iterating this step (possibly `d` times, with `d = dim A_{𝒜₊}`) produces the
full homogeneous regular system of parameters promised by Step A. The
iteration is pure Lean bookkeeping over a varying graded ring and is left to
the caller.

## Main result

* `exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos`: single-step
  descent as described above. Output packaged so callers can reuse the
  graded, Noetherian, and CM-at-irrelevant structures on the quotient.

## Proof strategy

* Take `ℓ` via `GradedPrimeAvoidance.exists_homogeneous_nonZeroDivisor_of_isCohenMacaulay_dim_pos`;
* transport the graded ring structure via `GradedQuotient.gradedRing`;
* transport connectedness via `GradedPrimeAvoidance.connectedGraded_quotient`;
* identify `(irrelevant 𝒜').toIdeal = (irrelevant 𝒜).toIdeal.map (Ideal.Quotient.mk ⟨ℓ⟩)`;
* transport CM-at-irrelevant via the forward CM transfer
  `CohenMacaulay.Localization.isCohenMacaulayLocalRing_quotient` on `A_m`,
  combined with
  `CohenMacaulay.Polynomial.quotSMulTopLocalizationEquiv_of_mem` and
  `isCohenMacaulayLocalRing_of_ringEquiv'`.
-/

import toMathlib.GradedPrimeAvoidance
import toMathlib.GradedQuotient
import toMathlib.GradedIrrelevant
import toMathlib.GradedFiniteFree
import toMathlib.CohenMacaulay.Basic
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.Polynomial
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Regular.RegularSequence

noncomputable section

namespace GradedRegularSop

open HomogeneousIdeal IsLocalRing GradedIrrelevant GradedPrimeAvoidance
open GradedQuotient

universe u

/-! ### Auxiliary facts about the image of `𝒜₊` in `A ⧸ ⟨ℓ⟩` -/

section IrrelevantMap

variable {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

/-- The image of the irrelevant ideal under the quotient map coincides with
the irrelevant ideal of the induced graded quotient ring. This rewrite
identifies the "image of `𝒜₊`" with the "`𝒜₊` of the quotient". -/
lemma irrelevant_map_quotient_span_singleton
    (_h𝒜₀ : ConnectedGraded 𝒜) {ℓ : A}
    (hℓ_hom : SetLike.IsHomogeneousElem 𝒜 ℓ)
    (_hℓ_irr : ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    [hgr : GradedRing
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A)))] :
    (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal =
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) := by
  classical
  apply le_antisymm
  · -- `(𝒜'₊).toIdeal ⊆ m.map (mk I)`: use
    -- `HomogeneousIdeal.toIdeal_irrelevant_le` to reduce to graded pieces.
    rw [HomogeneousIdeal.toIdeal_irrelevant_le]
    intro i hi x hx
    -- `x ∈ 𝒜' i` — pullback to an element of `𝒜 i`, which lies in `m`.
    simp only [GradedQuotient.gradedQuotientPiece, Submodule.mem_map] at hx
    obtain ⟨a, ha_mem, ha_eq⟩ := hx
    have ha_m : a ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
      HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi ha_mem
    rw [← ha_eq]
    exact Ideal.mem_map_of_mem _ ha_m
  · -- `m.map (mk I) ⊆ (𝒜'₊).toIdeal`: decompose an element of `m` and use
    -- that its `0`-th component vanishes, so the image lies in `𝒜'₊`.
    intro x hx
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨a, ha_m, rfl⟩ := hx
    -- The `0`-component of `a` vanishes since `a ∈ 𝒜₊`.
    have ha_proj : (DirectSum.decompose 𝒜 a 0 : A) = 0 := by
      have hproj0 : GradedRing.proj 𝒜 0 a = 0 :=
        (HomogeneousIdeal.mem_irrelevant_iff 𝒜 a).mp ha_m
      exact hproj0
    -- Decompose `a = ∑_i a_i` and show each image is in `(𝒜'₊).toIdeal`.
    have hdecomp : a = ∑ i ∈ (DirectSum.decompose 𝒜 a).support,
        (DirectSum.decompose 𝒜 a i : A) := (DirectSum.sum_support_decompose 𝒜 a).symm
    rw [hdecomp, map_sum]
    refine Ideal.sum_mem _ ?_
    intro i _
    by_cases hi : i = 0
    · subst hi
      rw [ha_proj, map_zero]
      exact Submodule.zero_mem _
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hi
      -- `(mk I) a_i ∈ 𝒜' i` by construction of `𝒜'`.
      have h_mem :
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))
              (DirectSum.decompose 𝒜 a i : A) : A ⧸ Ideal.span ({ℓ} : Set A)) ∈
            (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A)) i :
              Submodule K (A ⧸ Ideal.span ({ℓ} : Set A))) := by
        simp only [GradedQuotient.gradedQuotientPiece, Submodule.mem_map]
        refine ⟨(DirectSum.decompose 𝒜 a i : A), (DirectSum.decompose 𝒜 a i).2, ?_⟩
        rfl
      exact HomogeneousIdeal.mem_iff.mpr
        (HomogeneousIdeal.mem_irrelevant_of_mem
          (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) hi_pos h_mem)

end IrrelevantMap

/-! ### Graded-algebra structure transfer to `A ⧸ ⟨ℓ⟩` -/

section Transfer

variable {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

/-- `A ⧸ ⟨ℓ⟩` inherits a graded-ring structure from `A` through the
homogeneity of the principal ideal generated by a homogeneous element. -/
def quotientSpanSingletonGradedRing {ℓ : A} (hℓ : SetLike.IsHomogeneousElem 𝒜 ℓ) :
    GradedRing (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) :=
  GradedQuotient.gradedRing 𝒜 _
    (GradedPrimeAvoidance.isHomogeneous_span_singleton_of_homogeneous 𝒜 hℓ)

/-- The nontriviality of `A ⧸ ⟨ℓ⟩` when `ℓ` lies in the irrelevant ideal. -/
lemma nontrivial_quotient_span_singleton_of_mem_irrelevant
    (h𝒜₀ : ConnectedGraded 𝒜) {ℓ : A}
    (hℓ_irr : ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    Nontrivial (A ⧸ Ideal.span ({ℓ} : Set A)) := by
  have hirr_prop : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≠ ⊤ :=
    (irrelevant_isMaximal 𝒜 h𝒜₀).ne_top
  have hne_top : Ideal.span ({ℓ} : Set A) ≠ ⊤ := by
    intro htop
    apply hirr_prop
    rw [Ideal.eq_top_iff_one] at htop ⊢
    have hsub : Ideal.span ({ℓ} : Set A) ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_irr
    exact hsub htop
  exact (Ideal.Quotient.nontrivial_iff (I := Ideal.span ({ℓ} : Set A))).mpr hne_top

end Transfer

/-! ### Main descent step -/

section Descent

variable {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] [IsNoetherianRing A]

/-- A non-zero-divisor is globally `IsSMulRegular`. -/
private lemma isSMulRegular_of_mem_nonZeroDivisors
    {ℓ : A} (hℓ : ℓ ∈ nonZeroDivisors A) : IsSMulRegular A ℓ := by
  intro a b h
  -- `h : ℓ • a = ℓ • b`, i.e. `ℓ * a = ℓ * b`.
  have hℓa : ℓ * a = ℓ * b := h
  have hab_zero : ℓ * (a - b) = 0 := by rw [mul_sub, hℓa, sub_self]
  have hab : a - b = 0 := (mem_nonZeroDivisors_iff.mp hℓ).1 _ hab_zero
  exact sub_eq_zero.mp hab

/-- **Single-step descent.** For a connected ℕ-graded Noetherian `K`-algebra
`A` with `A_{𝒜₊}` Cohen–Macaulay of strictly positive Krull dimension, there
exists a homogeneous `ℓ ∈ 𝒜₊` which is an `A`-regular non-zero-divisor, and
such that the induced grading on the quotient `A ⧸ ⟨ℓ⟩`:

* is itself a graded ring structure;
* makes `A ⧸ ⟨ℓ⟩` nontrivial;
* is still connected graded;
* has the property that the localization at its irrelevant ideal is
  Cohen–Macaulay local.

This is the single descent step in the iterative construction of a
homogeneous regular system of parameters (Step A of the finite-free route for
graded Case C Cohen–Macaulay transfer). -/
theorem exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (hdim : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      (0 : WithBot ℕ∞) < ringKrullDim
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    ∃ ℓ : A,
      SetLike.IsHomogeneousElem 𝒜 ℓ ∧
      ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      IsSMulRegular A ℓ ∧
      ∃ _ : GradedRing
          (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))),
        ∃ _ : Nontrivial (A ⧸ Ideal.span ({ℓ} : Set A)),
          ∃ _ : ConnectedGraded (GradedQuotient.gradedQuotientPiece 𝒜
              (Ideal.span ({ℓ} : Set A))),
            haveI :=
              (GradedIrrelevant.irrelevant_isMaximal (K := K)
                (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A)))
                (by assumption)).isPrime
            IsCohenMacaulayLocalRing
              (Localization.AtPrime
                (HomogeneousIdeal.irrelevant
                  (GradedQuotient.gradedQuotientPiece 𝒜
                    (Ideal.span ({ℓ} : Set A)))).toIdeal) := by
  haveI hm_max : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal :=
    irrelevant_isMaximal 𝒜 h𝒜₀
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime := hm_max.isPrime
  -- Produce the homogeneous NZD.
  obtain ⟨ℓ, hℓ_hom, hℓ_irr, hℓ_reg⟩ :=
    exists_homogeneous_nonZeroDivisor_of_isCohenMacaulay_dim_pos 𝒜 h𝒜₀ hCM hdim
  refine ⟨ℓ, hℓ_hom, hℓ_irr, ?_, ?_⟩
  · exact isSMulRegular_of_mem_nonZeroDivisors hℓ_reg
  · -- Build quotient graded structure.
    haveI hgr : GradedRing
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) :=
      GradedQuotient.gradedRing 𝒜 _
        (isHomogeneous_span_singleton_of_homogeneous 𝒜 hℓ_hom)
    haveI hnt : Nontrivial (A ⧸ Ideal.span ({ℓ} : Set A)) :=
      nontrivial_quotient_span_singleton_of_mem_irrelevant 𝒜 h𝒜₀ hℓ_irr
    have hconn : ConnectedGraded
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) :=
      connectedGraded_quotient 𝒜 h𝒜₀ hℓ_hom
    refine ⟨hgr, hnt, hconn, ?_⟩
    -- The irrelevant ideal of the quotient is prime (maximal).
    haveI h_quot_irr_max :
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal.IsMaximal :=
      irrelevant_isMaximal _ hconn
    haveI h_quot_irr_prime :
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal.IsPrime :=
      h_quot_irr_max.isPrime
    -- Identify `(irrelevant 𝒜').toIdeal` with `m.map (Ideal.Quotient.mk I)`.
    have hmap_eq :
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal =
          (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
            (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) :=
      irrelevant_map_quotient_span_singleton 𝒜 h𝒜₀ hℓ_hom hℓ_irr
    -- Primality of the image.
    haveI h_mI_prime : ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))).IsPrime := by
      refine Ideal.isPrime_map_quotientMk_of_isPrime ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hℓ_irr
    -- Regularity of `ℓ` and its image in `A_m`.
    have hℓ_reg_global : IsSMulRegular A ℓ := isSMulRegular_of_mem_nonZeroDivisors hℓ_reg
    have hℓ_max : algebraMap A
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ ∈
        maximalIdeal (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hℓ_irr
    have hℓ_reg_loc :
        IsSMulRegular
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
          (algebraMap A
            (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ) :=
      hℓ_reg_global.of_flat
    have hcomap : ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))).comap
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
      refine sup_eq_left.mpr ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_irr
    haveI hloc_CM : IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := hCM
    haveI hloc := quotSMulTopLocalRing hℓ_max
    haveI hQCM : IsCohenMacaulayLocalRing
        (QuotSMulTop (algebraMap A
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ)
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :=
      isCohenMacaulayLocalRing_quotient hℓ_reg_loc hℓ_max
    have heq_ring :
        Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))) ≃+*
          QuotSMulTop (algebraMap A
            (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ)
            (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
      (quotSMulTopLocalizationEquiv_of_mem hℓ_irr hcomap).symm
    haveI hLoc_mI : IsLocalRing (Localization.AtPrime
        ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))))) :=
      IsLocalization.AtPrime.isLocalRing _
        ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))))
    have hCM_mI : IsCohenMacaulayLocalRing
        (Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))))) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hQCM heq_ring.symm
    -- Transport via equality `hmap_eq`: build a ring equivalence
    -- `Localization.AtPrime (𝒜'.irrelevant.toIdeal) ≃+* Localization.AtPrime (m.map (mk I))`
    -- from the equality of the two ideals.
    have hPC :
        @Ideal.primeCompl _ _ (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal h_quot_irr_prime =
          @Ideal.primeCompl _ _ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
            (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))) h_mI_prime := by
      apply Submonoid.ext
      intro x
      change x ∉ _ ↔ x ∉ _
      rw [hmap_eq]
    -- Both Localizations are at the SAME Submonoid (via hPC). Bridge via
    -- IsLocalization.algEquiv.
    haveI hLoc_q : IsLocalRing (Localization.AtPrime (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal) :=
      IsLocalization.AtPrime.isLocalRing _ (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal
    -- The second localization is also IsLocalization for the same submonoid
    -- (via the primeCompl equality).
    haveI hIL : IsLocalization
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal.primeCompl
        (Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))))) := by
      rw [hPC]
      exact Localization.isLocalization
    have hequiv_bridge :
        Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))) ≃+*
          Localization.AtPrime (HomogeneousIdeal.irrelevant
            (GradedQuotient.gradedQuotientPiece 𝒜
              (Ideal.span ({ℓ} : Set A)))).toIdeal :=
      (IsLocalization.algEquiv
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal.primeCompl
        (Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))))
        (Localization.AtPrime (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal)).toRingEquiv
    exact isCohenMacaulayLocalRing_of_ringEquiv' hCM_mI hequiv_bridge

end Descent

/-! ### Full iteration: homogeneous regular system of parameters

Iterate the single-step descent `exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos`
`d` times (where `d = dim A_{𝒜₊}`) to produce a homogeneous `A`-regular
sequence of length `d` in `𝒜₊` whose quotient is finite-dimensional over `K`. -/

section FullIteration

open HomogeneousIdeal IsLocalRing GradedIrrelevant GradedPrimeAvoidance
open GradedQuotient GradedFiniteFree RingTheory.Sequence
open scoped Pointwise

/-- The localization at the irrelevant ideal is Noetherian (forwarded from
a Noetherian ring hypothesis on `A`). -/
private lemma isNoetherian_localization_irrelevant
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] [IsNoetherianRing A]
    (h𝒜₀ : ConnectedGraded 𝒜) :
    haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
    IsNoetherianRing
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := by
  haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
  exact IsLocalization.isNoetherianRing
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.primeCompl
    (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) inferInstance

/-- Base case of the iteration: `d = 0` gives an empty regular sequence and
`A` itself is finite-dimensional over `K`. -/
private lemma exists_homogeneous_regular_sop_base
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    (_hCM : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (hdim : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      ringKrullDim
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) =
        (((0 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    ∃ θ : List A,
      θ.length = 0 ∧
      (∀ ℓ ∈ θ, SetLike.IsHomogeneousElem 𝒜 ℓ) ∧
      (∀ ℓ ∈ θ, ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ∧
      IsWeaklyRegular A θ ∧
      Module.Finite K (A ⧸ Ideal.ofList θ) := by
  haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
  haveI : IsNoetherianRing (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    isNoetherian_localization_irrelevant 𝒜 h𝒜₀
  -- From dim = 0 deduce `Ring.KrullDimLE 0` on the localization.
  have hdimLE : Ring.KrullDimLE 0 (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := by
    rw [Ring.krullDimLE_iff, hdim]
    simp
  -- Artinian by Hopkins–Levitzki.
  haveI : IsArtinianRing (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  -- Apply Step B2b.
  haveI hFinite : Module.Finite K A :=
    finite_over_K_of_isArtinianRing_atIrrelevant 𝒜 h𝒜₀ ‹_›
  refine ⟨[], rfl, ?_, ?_, IsWeaklyRegular.nil _ _, ?_⟩
  · intro _ hmem; simp at hmem
  · intro _ hmem; simp at hmem
  · -- `A ⧸ Ideal.ofList [] = A ⧸ ⊥ ≃+* A`.
    have hEq : Ideal.ofList ([] : List A) = (⊥ : Ideal A) := Ideal.ofList_nil
    let e : (A ⧸ Ideal.ofList ([] : List A)) ≃ₐ[K] A :=
      (Ideal.quotientEquivAlgOfEq K hEq).trans (AlgEquiv.quotientBot K A)
    exact Module.Finite.equiv e.symm.toLinearEquiv

/-- Map a homogeneous element of `𝒜' i = (𝒜 i).map (mk ⟨ℓ⟩)` back to a
homogeneous element of `𝒜 i`. -/
private lemma exists_homogeneous_preimage
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] (ℓ : A)
    {x : A ⧸ Ideal.span ({ℓ} : Set A)}
    (hx : SetLike.IsHomogeneousElem
      (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) x) :
    ∃ (i : ℕ) (a : A), a ∈ 𝒜 i ∧
      Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)) a = x := by
  obtain ⟨i, hxi⟩ := hx
  simp only [GradedQuotient.gradedQuotientPiece, Submodule.mem_map] at hxi
  obtain ⟨a, ha_mem, ha_eq⟩ := hxi
  exact ⟨i, a, ha_mem, ha_eq⟩

/-- Dimension drop: after quotienting by a homogeneous NZD `ℓ` in the irrelevant
ideal, the dimension of the localization at the image of the irrelevant ideal
drops by one. -/
private lemma ringKrullDim_irrelevant_quotient_eq
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] [IsNoetherianRing A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    {ℓ : A} (hℓ_hom : SetLike.IsHomogeneousElem 𝒜 ℓ)
    (hℓ_irr : ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (hℓ_reg : IsSMulRegular A ℓ)
    [hgr : GradedRing
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A)))]
    [hnt : Nontrivial (A ⧸ Ideal.span ({ℓ} : Set A))]
    (hconn : ConnectedGraded
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))))
    {d' : ℕ}
    (hdim : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      ringKrullDim
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) =
        (((d' + 1 : ℕ) : ℕ∞) : WithBot ℕ∞)) :
    haveI := (GradedIrrelevant.irrelevant_isMaximal
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A))) hconn).isPrime
    ringKrullDim
      (Localization.AtPrime
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal) =
      (((d' : ℕ) : ℕ∞) : WithBot ℕ∞) := by
  haveI hm_max : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal :=
    irrelevant_isMaximal 𝒜 h𝒜₀
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime := hm_max.isPrime
  haveI h_quot_irr_max :
      (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal.IsMaximal :=
    irrelevant_isMaximal _ hconn
  haveI h_quot_irr_prime :
      (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal.IsPrime :=
    h_quot_irr_max.isPrime
  -- Image-primality and identification.
  have hmap_eq :
      (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal =
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) :=
    irrelevant_map_quotient_span_singleton 𝒜 h𝒜₀ hℓ_hom hℓ_irr
  haveI h_mI_prime : ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
      (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))).IsPrime := by
    refine Ideal.isPrime_map_quotientMk_of_isPrime ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_irr
  -- Regularity of ℓ in the localization at the irrelevant ideal.
  have hℓ_max : algebraMap A
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ ∈
      maximalIdeal (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hℓ_irr
  have hℓ_reg_loc :
      IsSMulRegular
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
        (algebraMap A
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ) :=
    hℓ_reg.of_flat
  have hcomap : ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
      (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))).comap
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) =
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    refine sup_eq_left.mpr ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_irr
  -- `Localization.AtPrime (mI) ≃+* QuotSMulTop (image ℓ) (Localization.AtPrime m)`.
  have heq_ring :
      Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))) ≃+*
        QuotSMulTop (algebraMap A
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ)
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    (quotSMulTopLocalizationEquiv_of_mem hℓ_irr hcomap).symm
  -- The `Localization.AtPrime` of the quotient's irrelevant ideal agrees
  -- with the one of the image ideal, via a canonical bridge.
  haveI hLoc_q : IsLocalRing (Localization.AtPrime (HomogeneousIdeal.irrelevant
      (GradedQuotient.gradedQuotientPiece 𝒜
        (Ideal.span ({ℓ} : Set A)))).toIdeal) :=
    IsLocalization.AtPrime.isLocalRing _ (HomogeneousIdeal.irrelevant
      (GradedQuotient.gradedQuotientPiece 𝒜
        (Ideal.span ({ℓ} : Set A)))).toIdeal
  have hPC :
      @Ideal.primeCompl _ _ (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal h_quot_irr_prime =
        @Ideal.primeCompl _ _ ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
          (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))) h_mI_prime := by
    apply Submonoid.ext
    intro x
    change x ∉ _ ↔ x ∉ _
    rw [hmap_eq]
  haveI hIL : IsLocalization
      (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal.primeCompl
      (Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))))) := by
    rw [hPC]
    exact Localization.isLocalization
  have hequiv_bridge :
      Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))) ≃+*
        Localization.AtPrime (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal :=
    (IsLocalization.algEquiv
      (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal.primeCompl
      (Localization.AtPrime ((HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
        (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))))
      (Localization.AtPrime (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal)).toRingEquiv
  -- Compose: `Localization.AtPrime (𝒜'₊) ≃+* QuotSMulTop (image ℓ) ...`.
  have heq_total :
      Localization.AtPrime (HomogeneousIdeal.irrelevant
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A)))).toIdeal ≃+*
        QuotSMulTop (algebraMap A
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ)
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    hequiv_bridge.symm.trans heq_ring
  rw [ringKrullDim_eq_of_ringEquiv heq_total]
  -- Now we need `ringKrullDim QuotSMulTop (image ℓ) Loc = d'`.
  have hsub_eq : ringKrullDim (QuotSMulTop (algebraMap A
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ)
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) + 1 =
      ringKrullDim (Localization.AtPrime
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    ringKrullDim_quotSMulTop_succ_eq_ringKrullDim hℓ_reg_loc hℓ_max
  rw [hdim] at hsub_eq
  -- `X + 1 = (d'+1)` in `WithBot ℕ∞` forces `X = d'`.
  -- From `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`: Noetherian local is
  -- FiniteRingKrullDim, so QuotSMulTop (which is also quotient of a Noetherian
  -- local) has FiniteRingKrullDim too.
  set X := ringKrullDim (QuotSMulTop (algebraMap A
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ℓ)
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) with hX_def
  -- X ≠ ⊥: if X = ⊥, then X + 1 = ⊥, contradicting hsub_eq.
  have hne_bot : X ≠ ⊥ := by
    intro hbot
    rw [hbot] at hsub_eq
    -- `⊥ + 1 = ⊥` but RHS is a coerced nat, so not `⊥`.
    have : (⊥ : WithBot ℕ∞) = (((d' + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa [WithBot.bot_add] using hsub_eq
    exact absurd this.symm (by simp)
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp hne_bot
  rw [← he] at hsub_eq
  have hcast : ((e : WithBot ℕ∞) + (1 : WithBot ℕ∞)) = (((e + 1 : ℕ∞)) : WithBot ℕ∞) := by
    norm_cast
  rw [hcast] at hsub_eq
  have hsum_eq : e + 1 = ((d' + 1 : ℕ) : ℕ∞) := by exact_mod_cast hsub_eq
  have he_eq : e = (d' : ℕ∞) := by
    have h1 : e + 1 = ((d' : ℕ∞) + 1 : ℕ∞) := by
      rw [hsum_eq]; push_cast; rfl
    exact WithTop.add_right_cancel (by decide) h1
  rw [← he, he_eq]

/-- Auxiliary induction: for every `d : ℕ`, every connected ℕ-graded Noetherian
finitely-generated `K`-algebra with CM-at-irrelevant and dim exactly `d` admits
a homogeneous regular sop of length `d`. -/
private theorem exists_homogeneous_regular_sop_aux :
    ∀ (d : ℕ) {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
      (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
      [IsNoetherianRing A] [Algebra.FiniteType K A]
      (h𝒜₀ : ConnectedGraded 𝒜)
      (_hCM : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
        IsCohenMacaulayLocalRing
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
      (_hdim : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
        ringKrullDim
          (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) =
          (((d : ℕ) : ℕ∞) : WithBot ℕ∞)),
    ∃ θ : List A,
      θ.length = d ∧
      (∀ ℓ ∈ θ, SetLike.IsHomogeneousElem 𝒜 ℓ) ∧
      (∀ ℓ ∈ θ, ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ∧
      IsWeaklyRegular A θ ∧
      Module.Finite K (A ⧸ Ideal.ofList θ)
  | 0, K, A, _, _, _, _, 𝒜, _, _, _, h𝒜₀, hCM, hdim =>
      exists_homogeneous_regular_sop_base 𝒜 h𝒜₀ hCM hdim
  | d' + 1, K, A, _, _, _, _, 𝒜, _, _, _, h𝒜₀, hCM, hdim => by
    -- Get single-step descent data.
    haveI hm_prime := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
    -- Positivity of the dim.
    have hdim_pos : (0 : WithBot ℕ∞) < ringKrullDim
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := by
      rw [hdim]
      exact_mod_cast (Nat.succ_pos d')
    obtain ⟨ℓ, hℓ_hom, hℓ_irr, hℓ_reg, hgr, hnt, hconn, hCM'⟩ :=
      exists_homogeneous_nonZeroDivisor_quotient_cm_of_dim_pos 𝒜 h𝒜₀ hCM hdim_pos
    -- `A' := A ⧸ ⟨ℓ⟩` inherits the relevant instances. Register the ones
    -- coming out of the single-step descent as typeclass instances.
    classical
    letI hgrI : GradedRing
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) := hgr
    letI hntI : Nontrivial (A ⧸ Ideal.span ({ℓ} : Set A)) := hnt
    haveI : IsNoetherianRing (A ⧸ Ideal.span ({ℓ} : Set A)) :=
      Ideal.Quotient.isNoetherianRing _
    haveI : Algebra.FiniteType K (A ⧸ Ideal.span ({ℓ} : Set A)) := inferInstance
    -- Dimension drop.
    have hdim' := ringKrullDim_irrelevant_quotient_eq 𝒜 h𝒜₀ hℓ_hom hℓ_irr hℓ_reg
      hconn (d' := d') hdim
    -- Recursive call.
    haveI h_quot_irr_prime :
        (HomogeneousIdeal.irrelevant
          (GradedQuotient.gradedQuotientPiece 𝒜
            (Ideal.span ({ℓ} : Set A)))).toIdeal.IsPrime :=
      (irrelevant_isMaximal _ hconn).isPrime
    -- Cast `hCM'` to the instance-synthesized form before the recursive call.
    have hCM'_cast : haveI := (irrelevant_isMaximal
        (GradedQuotient.gradedQuotientPiece 𝒜
          (Ideal.span ({ℓ} : Set A))) hconn).isPrime
        IsCohenMacaulayLocalRing
          (Localization.AtPrime
            (HomogeneousIdeal.irrelevant
              (GradedQuotient.gradedQuotientPiece 𝒜
                (Ideal.span ({ℓ} : Set A)))).toIdeal) := hCM'
    have hrec :=
      exists_homogeneous_regular_sop_aux d'
        (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A)))
        hconn hCM'_cast hdim'
    obtain ⟨θ', hlen', hhom', hirr', hreg', hfin'⟩ := hrec
    -- Select a homogeneous lift for each element of `θ'`.
    choose lift_deg lift_elem lift_deg_spec lift_mk using
      (fun (x : A ⧸ Ideal.span ({ℓ} : Set A))
        (hx : SetLike.IsHomogeneousElem
          (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) x) =>
        exists_homogeneous_preimage 𝒜 ℓ hx)
    -- Lifter: for homogeneous x, pick the constructed lift; else `0`.
    set lifter : (A ⧸ Ideal.span ({ℓ} : Set A)) → A :=
      fun x =>
        if hx : SetLike.IsHomogeneousElem
            (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) x then
          lift_elem x hx
        else 0
      with hlifter_def
    -- `tail := θ'.map lifter`.
    set tail : List A := θ'.map lifter with htail_def
    -- Specs for elements of `tail`: they're homogeneous in 𝒜 and lift via `mk`.
    have lifter_hom : ∀ x ∈ θ', SetLike.IsHomogeneousElem 𝒜 (lifter x) := by
      intro x hx_mem
      have hxhom : SetLike.IsHomogeneousElem
          (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) x :=
        hhom' x hx_mem
      refine ⟨lift_deg x hxhom, ?_⟩
      simp only [hlifter_def, dif_pos hxhom]
      exact lift_deg_spec x hxhom
    have lifter_mk : ∀ x ∈ θ',
        Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)) (lifter x) = x := by
      intro x hx_mem
      have hxhom : SetLike.IsHomogeneousElem
          (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A))) x :=
        hhom' x hx_mem
      simp only [hlifter_def, dif_pos hxhom]
      exact lift_mk x hxhom
    -- Key: `tail.map (mk _) = θ'`.
    have htail_mk :
        tail.map (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) = θ' := by
      rw [htail_def, List.map_map]
      conv_rhs => rw [← List.map_id θ']
      refine List.map_congr_left ?_
      intro x hx_mem
      exact lifter_mk x hx_mem
    -- Each element of `tail` is homogeneous in 𝒜.
    have htail_hom : ∀ y ∈ tail, SetLike.IsHomogeneousElem 𝒜 y := by
      intro y hy
      rw [htail_def, List.mem_map] at hy
      obtain ⟨x, hx_mem, rfl⟩ := hy
      exact lifter_hom x hx_mem
    -- Each element of `tail` lies in 𝒜₊.
    have htail_irr : ∀ y ∈ tail, y ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
      intro y hy
      rw [htail_def, List.mem_map] at hy
      obtain ⟨x, hx_mem, rfl⟩ := hy
      -- Use `𝒜'₊ = (𝒜₊).map (mk I)`.
      have hmap_eq :
          (HomogeneousIdeal.irrelevant
            (GradedQuotient.gradedQuotientPiece 𝒜
              (Ideal.span ({ℓ} : Set A)))).toIdeal =
            (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map
              (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) :=
        irrelevant_map_quotient_span_singleton 𝒜 h𝒜₀ hℓ_hom hℓ_irr
      have hx_irr := hirr' x hx_mem
      rw [hmap_eq] at hx_irr
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx_irr
      obtain ⟨a, ha_irr, ha_mk⟩ := hx_irr
      have hmk_x : Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)) (lifter x) = x :=
        lifter_mk x hx_mem
      have hdiff : Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))
          (lifter x - a) = 0 := by
        rw [map_sub, hmk_x, ha_mk, sub_self]
      rw [Ideal.Quotient.eq_zero_iff_mem] at hdiff
      have hspan_sub : Ideal.span ({ℓ} : Set A) ≤
          (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hℓ_irr
      have hliftdiff : (lifter x - a) ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
        hspan_sub hdiff
      have heq : lifter x = a + (lifter x - a) := by ring
      rw [heq]
      exact Ideal.add_mem _ ha_irr hliftdiff
    -- Assemble the output: θ := ℓ :: tail.
    refine ⟨ℓ :: tail, ?_, ?_, ?_, ?_, ?_⟩
    · -- length
      simp [htail_def, hlen']
    · -- homogeneity
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hℓ_hom
      · exact htail_hom y hy
    · -- membership in 𝒜₊
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hℓ_irr
      · exact htail_irr y hy
    · -- weak regularity: ℓ :: tail, via cons_iff.
      rw [isWeaklyRegular_cons_iff]
      refine ⟨hℓ_reg, ?_⟩
      -- `IsWeaklyRegular (QuotSMulTop ℓ A) tail` (over A).
      -- Bridge: `ℓ • (⊤ : Submodule A A) = (Ideal.span {ℓ} : Submodule A A)`.
      have heq_submod :
          ℓ • (⊤ : Submodule A A) =
            ((Ideal.span ({ℓ} : Set A) : Ideal A) : Submodule A A) := by
        ext z
        refine ⟨fun hz => ?_, fun hz => ?_⟩
        · -- `z ∈ ℓ • ⊤` implies `z = ℓ • w` for some `w ∈ ⊤`.
          rw [Submodule.mem_smul_pointwise_iff_exists] at hz
          obtain ⟨w, _, rfl⟩ := hz
          change ℓ • w ∈ Ideal.span ({ℓ} : Set A)
          have hmul : ℓ • w = ℓ * w := rfl
          rw [hmul]
          exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
        · -- `z ∈ span {ℓ}` implies `ℓ ∣ z`, so `z = ℓ * c`.
          rw [Ideal.mem_span_singleton] at hz
          obtain ⟨c, rfl⟩ := hz
          rw [Submodule.mem_smul_pointwise_iff_exists]
          exact ⟨c, Submodule.mem_top, rfl⟩
      -- `QuotSMulTop ℓ A ≃ₗ[A] A ⧸ Ideal.span {ℓ}`.
      have heq_mod :
          (QuotSMulTop ℓ A) ≃ₗ[A] A ⧸ Ideal.span ({ℓ} : Set A) :=
        Submodule.quotEquivOfEq _ _ heq_submod
      -- Bridge via `isWeaklyRegular_congr`: regularity over A for tail.
      rw [heq_mod.isWeaklyRegular_congr tail]
      -- Convert to regularity over A ⧸ Ideal.span {ℓ}: scalar tower.
      rw [← isWeaklyRegular_map_algebraMap_iff (A ⧸ Ideal.span ({ℓ} : Set A))
        (A ⧸ Ideal.span ({ℓ} : Set A)) tail]
      -- `algebraMap A (A⧸I) = Ideal.Quotient.mk I` and `tail.map (mk I) = θ'`.
      change IsWeaklyRegular _
        (tail.map (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))))
      rw [htail_mk]
      exact hreg'
    · -- finiteness over K.
      -- `A ⧸ Ideal.ofList (ℓ :: tail) ≃ₐ[K] (A ⧸ ⟨ℓ⟩) ⧸ Ideal.ofList θ'`.
      have hle : Ideal.span ({ℓ} : Set A) ≤ Ideal.ofList (ℓ :: tail) := by
        rw [Ideal.ofList_cons]
        exact le_sup_left
      -- Establish that `Module.Finite K ((A ⧸ span {ℓ}) ⧸ Ideal.ofList θ')`
      -- transfers to `Module.Finite K (A ⧸ Ideal.ofList (ℓ :: tail))`.
      have hmap_span_eq_bot :
          (Ideal.span ({ℓ} : Set A)).map
              (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) = ⊥ := by
        rw [Ideal.map_span, Set.image_singleton,
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ℓ),
          Ideal.span_singleton_eq_bot.mpr rfl]
      have hsup_mk :
          (Ideal.ofList (ℓ :: tail)).map
              (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A))) =
            Ideal.ofList θ' := by
        rw [Ideal.ofList_cons, Ideal.map_sup, hmap_span_eq_bot, bot_sup_eq,
          Ideal.map_ofList, htail_mk]
      -- `(Ideal.Quotient.mkₐ K I : A →+* _) = Ideal.Quotient.mk I` as rings.
      have hsup_mkₐ :
          (Ideal.ofList (ℓ :: tail)).map
              (Ideal.Quotient.mkₐ K (Ideal.span ({ℓ} : Set A))) =
            Ideal.ofList θ' := by
        change (Ideal.ofList (ℓ :: tail)).map
            ((Ideal.Quotient.mkₐ K (Ideal.span ({ℓ} : Set A))).toRingHom) =
          Ideal.ofList θ'
        rw [show (Ideal.Quotient.mkₐ K
            (Ideal.span ({ℓ} : Set A))).toRingHom =
              Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)) from rfl]
        exact hsup_mk
      -- Use `quotQuotEquivQuotOfLEₐ` to get a K-algebra equivalence.
      let e_alg :
          ((A ⧸ Ideal.span ({ℓ} : Set A)) ⧸
              (Ideal.ofList (ℓ :: tail)).map
                (Ideal.Quotient.mkₐ K (Ideal.span ({ℓ} : Set A)))) ≃ₐ[K]
          A ⧸ Ideal.ofList (ℓ :: tail) :=
        DoubleQuot.quotQuotEquivQuotOfLEₐ K hle
      have e_alg' :
          ((A ⧸ Ideal.span ({ℓ} : Set A)) ⧸ Ideal.ofList θ') ≃ₐ[K]
          A ⧸ Ideal.ofList (ℓ :: tail) :=
        (Ideal.quotientEquivAlgOfEq K hsup_mkₐ.symm).trans e_alg
      exact Module.Finite.equiv e_alg'.toLinearEquiv

/-- **Step A (full iteration).** For a connected ℕ-graded Noetherian `K`-algebra
`A` of finite type over `K` whose localization at the irrelevant ideal is
Cohen–Macaulay local of Krull dimension `d`, there exists a homogeneous
`A`-regular sequence `θ` of length `d` in `𝒜₊` such that `A ⧸ Ideal.ofList θ`
is finite-dimensional as a `K`-module. -/
theorem exists_homogeneous_regular_sop_of_cm_at_irrelevant
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    ∃ (d : ℕ) (θ : List A),
      θ.length = d ∧
      (∀ ℓ ∈ θ, SetLike.IsHomogeneousElem 𝒜 ℓ) ∧
      (∀ ℓ ∈ θ, ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ∧
      IsWeaklyRegular A θ ∧
      Module.Finite K (A ⧸ Ideal.ofList θ) := by
  haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
  -- Extract `d : ℕ` from `ringKrullDim Loc`.
  haveI hNoethLoc : IsNoetherianRing (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    isNoetherian_localization_irrelevant 𝒜 h𝒜₀
  haveI : IsLocalRing (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :=
    IsLocalization.AtPrime.isLocalRing _ (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  haveI : FiniteRingKrullDim (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) := inferInstance
  have hne_bot : ringKrullDim (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ≠ ⊥ := ringKrullDim_ne_bot
  have hne_top : ringKrullDim (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) ≠ ⊤ := ringKrullDim_ne_top
  -- `ringKrullDim Loc` is in `WithBot ℕ∞`; unbot first, then use `toNat`.
  obtain ⟨d_enat, hd_enat⟩ := WithBot.ne_bot_iff_exists.mp hne_bot
  have hd_enat_ne_top : d_enat ≠ ⊤ := by
    intro h
    apply hne_top
    rw [← hd_enat, h]
    rfl
  set d : ℕ := d_enat.toNat with hd_def
  have hd_eq : d_enat = (d : ℕ∞) := (ENat.coe_toNat hd_enat_ne_top).symm
  have hdim_nat : ringKrullDim (Localization.AtPrime
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal) = (((d : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    rw [← hd_enat, hd_eq]
  obtain ⟨θ, hlen, hhom, hirr, hreg, hfin⟩ :=
    exists_homogeneous_regular_sop_aux d 𝒜 h𝒜₀ hCM hdim_nat
  exact ⟨d, θ, hlen, hhom, hirr, hreg, hfin⟩

end FullIteration

end GradedRegularSop

/-! ## Step A + Step C + Step D assembly

Package the three ingredients from the finite-free Case C route into a single
global-CM theorem: for a connected ℕ-graded Noetherian `K`-algebra `A` of finite
type over `K` whose localization at the irrelevant ideal is Cohen–Macaulay local,
`A` is globally Cohen–Macaulay. The argument goes through:

1. Step A (`exists_homogeneous_regular_sop_of_cm_at_irrelevant`): produces a
   homogeneous regular sequence `θ : List A` of length `d = dim A_{𝒜₊}` such
   that `A ⧸ Ideal.ofList θ` is finite over `K`.
2. Step C (`finiteFree_over_mvPolynomial_of_homogeneous_regular_sop`): `A` is
   a finite free `MvPolynomial (Fin d) K`-module via `T_i ↦ θ_i`.
3. Step D (`isCohenMacaulayRing_of_module_free_of_mvPolynomial`): finite free
   over `MvPolynomial (Fin d) K` ⟹ globally CM.
-/

namespace GradedFiniteFree

open GradedIrrelevant

universe u

/-- **Step A + Step C + Step D assembly.** For a connected ℕ-graded Noetherian
`K`-algebra `A` of finite type over `K` whose localization at the irrelevant
ideal is Cohen–Macaulay local, `A` is globally Cohen–Macaulay. -/
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    IsCohenMacaulayRing A := by
  classical
  obtain ⟨d, θ, hθ_len, hθ_hom, hθ_irr, hθ_reg, hA_fin⟩ :=
    GradedRegularSop.exists_homogeneous_regular_sop_of_cm_at_irrelevant 𝒜 h𝒜₀ hCM
  -- Convert `θ : List A` of length `d` to `Fin d → A`.
  let θ' : Fin d → A := fun i => θ.get (Fin.cast hθ_len.symm i)
  have hθ'_list : List.ofFn θ' = θ := by
    apply List.ext_getElem
    · simp [hθ_len]
    · intros n hn1 hn2
      simp only [θ', List.getElem_ofFn, List.get_eq_getElem, Fin.cast_mk]
  have hθ'_hom : ∀ i, SetLike.IsHomogeneousElem 𝒜 (θ' i) := fun i =>
    hθ_hom _ (List.get_mem _ _)
  have hθ'_irr : ∀ i, θ' i ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := fun i =>
    hθ_irr _ (List.get_mem _ _)
  have hθ'_reg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn θ') := by
    rw [hθ'_list]; exact hθ_reg
  have hA'_fin : Module.Finite K (A ⧸ Ideal.ofList (List.ofFn θ')) := by
    rw [hθ'_list]; exact hA_fin
  letI alg : Algebra (MvPolynomial (Fin d) K) A := (MvPolynomial.aeval θ').toAlgebra
  obtain ⟨hFinite, hFree⟩ :=
    finiteFree_over_mvPolynomial_of_homogeneous_regular_sop
      𝒜 h𝒜₀ θ' hθ'_hom hθ'_irr hθ'_reg hA'_fin
  exact isCohenMacaulayRing_of_module_free_of_mvPolynomial (d := d) (K := K) (A := A)

end GradedFiniteFree

end

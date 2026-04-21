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
import toMathlib.CohenMacaulay.Basic
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.Polynomial
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

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

end GradedRegularSop

end

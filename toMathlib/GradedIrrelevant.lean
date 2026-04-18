/-
Copyright: BEI Lean project.

# The irrelevant ideal of a connected graded `K`-algebra

For an `ℕ`-graded commutative `K`-algebra `A` with `𝒜 0 = K` (connected graded),
we show:

* `GradedIrrelevant.irrelevant_isMaximal`: the irrelevant ideal `𝒜₊` is maximal.
* `GradedIrrelevant.homogeneousCore_le_irrelevant`: for any proper ideal `p`
  of `A`, the homogeneous core `p.homogeneousCore 𝒜` is contained in `𝒜₊`.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maximal

noncomputable section

namespace GradedIrrelevant

open DirectSum HomogeneousIdeal

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

/-- The "connected graded" hypothesis: every element of `𝒜 0` is the image of a
scalar in `K` under the algebra map. -/
abbrev ConnectedGraded : Prop :=
  ∀ x ∈ 𝒜 0, ∃ k : K, algebraMap K A k = x

/-- A homogeneous element not in the irrelevant ideal must sit in `𝒜 0` and hence,
under the connected-graded hypothesis, is `algebraMap K A k` with `k ≠ 0`. -/
private lemma exists_scalar_of_homogeneous_not_mem_irrelevant
    (h𝒜₀ : ConnectedGraded 𝒜) {x : A} (hxhom : SetLike.IsHomogeneousElem 𝒜 x)
    (hxirr : x ∉ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    ∃ k : K, k ≠ 0 ∧ algebraMap K A k = x := by
  obtain ⟨i, hxi⟩ := hxhom
  rcases eq_or_ne i 0 with hi | hi
  · subst hi
    obtain ⟨k, hk⟩ := h𝒜₀ x hxi
    refine ⟨k, ?_, hk⟩
    rintro rfl
    apply hxirr
    have hx0 : x = 0 := by rw [← hk]; simp
    rw [hx0]; exact Submodule.zero_mem _
  · exact (hxirr
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (Nat.pos_of_ne_zero hi) hxi)).elim

/-- A homogeneous proper ideal of `A` is contained in the irrelevant ideal `𝒜₊`. -/
private lemma homogeneous_le_irrelevant_of_ne_top
    (h𝒜₀ : ConnectedGraded 𝒜)
    {J : Ideal A} (hJhom : J.IsHomogeneous 𝒜) (hJne : J ≠ ⊤) :
    J ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  classical
  intro x hxJ
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine Ideal.sum_mem _ fun i _ => ?_
  set xi : A := (DirectSum.decompose 𝒜 x i : A)
  have hximem : xi ∈ 𝒜 i := SetLike.coe_mem _
  have hxiJ : xi ∈ J := hJhom i hxJ
  by_contra hxi_notIrr
  obtain ⟨k, hk, hkxi⟩ := exists_scalar_of_homogeneous_not_mem_irrelevant
    𝒜 h𝒜₀ ⟨i, hximem⟩ hxi_notIrr
  apply hJne
  rw [Ideal.eq_top_iff_one,
    show (1 : A) = (algebraMap K A k⁻¹) * xi by
      rw [← hkxi, ← map_mul, inv_mul_cancel₀ hk, map_one]]
  exact Ideal.mul_mem_left _ _ hxiJ

/-- The irrelevant ideal is a proper ideal: it does not contain `1`. -/
private lemma irrelevant_ne_top [Nontrivial A] :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≠ ⊤ := by
  rw [Ne, Ideal.eq_top_iff_one]
  intro h1
  have h1' : GradedRing.proj 𝒜 0 (1 : A) = 0 :=
    (HomogeneousIdeal.mem_irrelevant_iff 𝒜 1).mp h1
  have hproj1 : GradedRing.proj 𝒜 0 (1 : A) = 1 := by
    rw [GradedRing.proj_apply,
      DirectSum.decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem]
  rw [hproj1] at h1'
  exact one_ne_zero h1'

/-- When `𝒜 0 = K` is a field (via the connected-graded hypothesis), the
irrelevant ideal is a maximal ideal of `A`. -/
theorem irrelevant_isMaximal [Nontrivial A] (h𝒜₀ : ConnectedGraded 𝒜) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal := by
  classical
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => irrelevant_ne_top 𝒜 ((Ideal.eq_top_iff_one _).mpr h1), ?_⟩
  intro J a hIJ ha haJ
  -- Decompose `a = a₀ + (a - a₀)`, where `a₀ := proj₀ a ∈ 𝒜 0` and `a - a₀ ∈ 𝒜₊`.
  set a₀ : A := GradedRing.projZeroRingHom 𝒜 a with ha₀_def
  have ha₀_mem : a₀ ∈ 𝒜 0 := by
    simp only [ha₀_def, GradedRing.projZeroRingHom_apply]
    exact (DirectSum.decompose 𝒜 a 0).2
  have hproj_a₀ : GradedRing.projZeroRingHom 𝒜 a₀ = a₀ := by
    simp [ha₀_def, GradedRing.projZeroRingHom_apply]
  have hdiff_irr : a - a₀ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
    change GradedRing.proj 𝒜 0 (a - a₀) = 0
    have heq : GradedRing.proj 𝒜 0 (a - a₀) =
        GradedRing.projZeroRingHom 𝒜 (a - a₀) := rfl
    rw [heq, map_sub, hproj_a₀, ← ha₀_def, sub_self]
  have ha₀_ne : a₀ ≠ 0 := fun hzero => ha <| by
    have heq : a = (a - a₀) := by rw [hzero]; ring
    rw [heq]; exact hdiff_irr
  obtain ⟨k, hk⟩ := h𝒜₀ a₀ ha₀_mem
  have hk_ne : k ≠ 0 := by
    rintro rfl; apply ha₀_ne; rw [← hk]; simp
  -- 1 = k⁻¹ * a - k⁻¹ * (a - a₀), so 1 ∈ J via a ∈ J and (a - a₀) ∈ 𝒜₊ ≤ J.
  have h1 : (1 : A) =
      (algebraMap K A k⁻¹) * a - (algebraMap K A k⁻¹) * (a - a₀) := by
    have h1' : (1 : A) = (algebraMap K A k⁻¹) * a₀ := by
      rw [← hk, ← map_mul, inv_mul_cancel₀ hk_ne, map_one]
    rw [h1']; ring
  rw [h1]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ haJ)
    (Ideal.mul_mem_left _ _ (hIJ hdiff_irr))

/-- For any proper ideal `p` of a connected graded `K`-algebra `A` with `𝒜 0 = K`
a field, the homogeneous core `p.homogeneousCore 𝒜` is contained in the
irrelevant ideal `𝒜₊`. -/
theorem homogeneousCore_le_irrelevant
    (h𝒜₀ : ConnectedGraded 𝒜) (p : Ideal A) (hp : p ≠ ⊤) :
    (p.homogeneousCore 𝒜).toIdeal ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  refine homogeneous_le_irrelevant_of_ne_top 𝒜 h𝒜₀
    (p.homogeneousCore 𝒜).isHomogeneous fun hcore_top => hp ?_
  rw [Ideal.eq_top_iff_one]
  refine p.toIdeal_homogeneousCore_le 𝒜 ?_
  rw [hcore_top]; trivial

end GradedIrrelevant

end

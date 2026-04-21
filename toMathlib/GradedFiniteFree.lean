/-
Copyright: BEI Lean project.

# Finite-free parameter subring route for graded CM

Infrastructure for closing the non-homogeneous-prime case of the graded
local-to-global Cohen–Macaulay theorem (Bruns–Herzog 2.1.27) via a
finite-free parameter subring, rather than prime-by-prime induction.

## Main results (currently in progress)

* `mul_left_injective_of_notMem_irrelevant` — **Step B1**: for a connected
  ℕ-graded `K`-algebra `A`, multiplication by any `s ∈ A` whose degree-0
  component is nonzero (equivalently, `s ∉ 𝒜₊`) is injective on `A`.
  The key fact underlying the nilpotence argument in Step B2.

## Proof strategy for the main theorem (not yet formalized)

See `guides/answers/ANSWER_CASE_C_FINITE_FREE_ROUTE.md`.
-/

import toMathlib.GradedIrrelevant
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

noncomputable section

namespace GradedFiniteFree

open DirectSum HomogeneousIdeal GradedIrrelevant

universe u

variable {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

attribute [local instance] Classical.propDecidable

/-! ### Step B1: multiplication by a non-irrelevant element is injective -/

omit [Nontrivial A] in
/-- **Step B1.** For a connected ℕ-graded `K`-algebra `A`, if `s ∈ A` is
not in the irrelevant ideal `𝒜₊` (equivalently, its degree-0 homogeneous
component is nonzero and hence a unit in `𝒜₀ = K`), then multiplication
by `s` is injective on `A`. -/
theorem mul_left_injective_of_notMem_irrelevant
    (h𝒜₀ : ConnectedGraded 𝒜)
    {s : A} (hs : s ∉ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    Function.Injective (fun u : A => s * u) := by
  classical
  -- Reduce to: `s * u = 0 ⟹ u = 0`.
  suffices hker : ∀ u : A, s * u = 0 → u = 0 by
    intro u v h
    have : s * (u - v) = 0 := by
      have := sub_eq_zero.mpr h
      rw [← mul_sub] at this
      exact this
    exact sub_eq_zero.mp (hker _ this)
  -- Extract the degree-0 component of `s`.
  set s0 : A := (DirectSum.decompose 𝒜 s 0 : A) with hs0_def
  have hs0_mem : s0 ∈ 𝒜 0 := SetLike.coe_mem _
  -- `s0 ≠ 0` because `s ∉ 𝒜₊`: the irrelevant ideal is the kernel of
  -- `proj₀`.
  have hs0_ne : s0 ≠ 0 := by
    intro heq
    apply hs
    -- `s ∈ 𝒜₊` iff `proj₀ s = 0`.
    change GradedRing.projZeroRingHom 𝒜 s = 0
    simp [GradedRing.projZeroRingHom_apply, heq, ← hs0_def]
  -- By connected graded, `s0 = algebraMap K A k` for some `k ∈ K^×`.
  obtain ⟨k, hk_eq⟩ := h𝒜₀ s0 hs0_mem
  have hk_ne : k ≠ 0 := by
    intro hzero
    apply hs0_ne
    rw [← hk_eq, hzero]; simp
  -- Now: `s · u = 0 ⟹ u = 0` by lowest-nonzero-component argument.
  intro u hsu
  by_contra hu
  -- Let `j` be the minimum of `supp u`.
  have hsupp_ne : (DirectSum.decompose 𝒜 u).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hu
    rw [← DirectSum.sum_support_decompose 𝒜 u, hempty, Finset.sum_empty]
  set j := (DirectSum.decompose 𝒜 u).support.min' hsupp_ne with hj_def
  have hj_mem : j ∈ (DirectSum.decompose 𝒜 u).support := Finset.min'_mem _ _
  have hj_min : ∀ i ∈ (DirectSum.decompose 𝒜 u).support, j ≤ i :=
    fun i hi => Finset.min'_le _ i hi
  -- Compute `(s · u)_j` using decompose_mul + coe_mul_apply.
  have hcoe_zero : (DirectSum.decompose 𝒜 (s * u) j : A) = 0 := by
    rw [hsu]; simp
  have hcoe_formula :
      (DirectSum.decompose 𝒜 (s * u) j : A) =
        ((DirectSum.decompose 𝒜 s * DirectSum.decompose 𝒜 u) j : A) := by
    rw [DirectSum.decompose_mul]
  rw [DirectSum.coe_mul_apply] at hcoe_formula
  -- The filtered sum: only `(0, j)` can contribute.
  have hfilter :
      ((DirectSum.decompose 𝒜 s).support ×ˢ
          (DirectSum.decompose 𝒜 u).support).filter
          (fun il : ℕ × ℕ => il.1 + il.2 = j) ⊆ {(0, j)} := by
    intro ⟨i, l⟩ hmem
    simp only [Finset.mem_filter, Finset.mem_product] at hmem
    obtain ⟨⟨_his, hlu⟩, hil⟩ := hmem
    have hl_ge : j ≤ l := hj_min l hlu
    simp only [Finset.mem_singleton, Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> omega
  -- 0 ∈ supp s (because s_0 = s0 ≠ 0) and j ∈ supp u.
  have h0_supp_s : (0 : ℕ) ∈ (DirectSum.decompose 𝒜 s).support := by
    rw [DFinsupp.mem_support_iff]
    intro habs
    apply hs0_ne
    change ((DirectSum.decompose 𝒜 s 0 : A)) = 0
    have : DirectSum.decompose 𝒜 s 0 = 0 := habs
    rw [this]; rfl
  have hpair_mem :
      ((0, j) : ℕ × ℕ) ∈
        ((DirectSum.decompose 𝒜 s).support ×ˢ
          (DirectSum.decompose 𝒜 u).support).filter
          (fun il : ℕ × ℕ => il.1 + il.2 = j) := by
    simp [h0_supp_s, hj_mem]
  have hfilter_eq :
      ((DirectSum.decompose 𝒜 s).support ×ˢ
          (DirectSum.decompose 𝒜 u).support).filter
          (fun il : ℕ × ℕ => il.1 + il.2 = j) = {(0, j)} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hpair_mem, fun ⟨i, l⟩ hm => by
        have := hfilter hm
        rwa [Finset.mem_singleton] at this⟩
  rw [hfilter_eq, Finset.sum_singleton] at hcoe_formula
  -- `(s * u)_j = s_0 * u_j = k • u_j ≠ 0`, contradiction.
  have huj_ne : (DirectSum.decompose 𝒜 u j : A) ≠ 0 := by
    intro h
    apply (DFinsupp.mem_support_iff.mp hj_mem)
    exact Subtype.ext h
  have hprod_ne :
      (DirectSum.decompose 𝒜 s 0 : A) *
        (DirectSum.decompose 𝒜 u j : A) ≠ 0 := by
    rw [← hs0_def, ← hk_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact smul_ne_zero hk_ne huj_ne
  exact hprod_ne (hcoe_formula ▸ hcoe_zero)

/-! ### Step B2a: nilpotence of the irrelevant ideal under Artinian localization

If `A_{𝒜₊}` is Artinian, then `𝒜₊` itself is nilpotent in `A`: there is some
`N` with `(𝒜₊)^N = (0)`. This combines Hopkins–Levitzki (maxIdeal of
Artinian local is nilpotent) with the Step B1 injectivity lemma to rule out
the usual "localization kernel" obstruction. -/

theorem irrelevant_isNilpotent_of_isArtinianRing_atIrrelevant
    (h𝒜₀ : ConnectedGraded 𝒜)
    [IsNoetherianRing A]
    (hArtinian : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsArtinianRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    IsNilpotent (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  classical
  haveI hm_max : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal :=
    irrelevant_isMaximal 𝒜 h𝒜₀
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime := hm_max.isPrime
  set m : Ideal A := (HomogeneousIdeal.irrelevant 𝒜).toIdeal with hm_def
  haveI : m.IsPrime := hm_prime
  let Am := Localization.AtPrime m
  haveI : IsArtinianRing Am := hArtinian
  -- `maxIdeal Am` is nilpotent. Noetherianness of Am auto-synthesizes from
  -- IsLocalization.instIsNoetherianRingLocalization.
  haveI : IsNoetherianRing Am := inferInstance
  have hmax_nilp : IsNilpotent (IsLocalRing.maximalIdeal Am) :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal Am).mp inferInstance
  obtain ⟨N, hN⟩ := hmax_nilp
  -- Pull back: image of `m^N` is `(maxIdeal Am)^N = 0`.
  have himage : Ideal.map (algebraMap A Am) (m ^ N) = 0 := by
    rw [Ideal.map_pow, Localization.AtPrime.map_eq_maximalIdeal, hN]
  -- Show `m^N = 0`, i.e., every x ∈ m^N is 0.
  refine ⟨N, ?_⟩
  rw [show (0 : Ideal A) = (⊥ : Ideal A) from rfl]
  rw [(Submodule.eq_bot_iff (m ^ N))]
  intro x hx
  -- `x ∈ m^N`, so `algebraMap A Am x = 0`.
  have hx_map : algebraMap A Am x = 0 := by
    have : algebraMap A Am x ∈ Ideal.map (algebraMap A Am) (m ^ N) :=
      Ideal.mem_map_of_mem _ hx
    rw [himage] at this
    rwa [show (0 : Ideal Am) = (⊥ : Ideal Am) from rfl,
      Ideal.mem_bot] at this
  -- By IsLocalization: ∃ s ∉ m, s * x = 0.
  rw [IsLocalization.map_eq_zero_iff m.primeCompl Am] at hx_map
  obtain ⟨s, hsx⟩ := hx_map
  -- s ∉ m = 𝒜₊. Apply B1.
  have hs_notMem : (s : A) ∉ m := s.2
  have hinj := mul_left_injective_of_notMem_irrelevant 𝒜 h𝒜₀ hs_notMem
  have hsx0 : s.1 * x = s.1 * 0 := by rw [hsx, mul_zero]
  exact hinj hsx0

/-! ### Step B2b: finite dimension over K

From nilpotent maximal `𝒜₊` in a Noetherian finitely generated `K`-algebra,
derive that `A` is Artinian, hence finite-dimensional over `K`. -/

private lemma isMaximal_of_isPrime_of_irrelevant_nilpotent
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hnilp : IsNilpotent (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (p : Ideal A) (hp : p.IsPrime) :
    p = (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  haveI hm_max : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal :=
    irrelevant_isMaximal 𝒜 h𝒜₀
  obtain ⟨N, hN⟩ := hnilp
  -- `𝒜₊^N = 0 ⊆ p`, so `𝒜₊ ⊆ p`.
  have hm_sub : (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p := by
    intro x hx
    have hxN : x ^ N ∈ p := by
      have hmem : x ^ N ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ N :=
        Ideal.pow_mem_pow hx N
      rw [hN] at hmem
      have : x ^ N = 0 := by
        rw [show (0 : Ideal A) = (⊥ : Ideal A) from rfl, Ideal.mem_bot] at hmem
        exact hmem
      rw [this]; exact Submodule.zero_mem _
    exact hp.mem_of_pow_mem _ hxN
  exact (hm_max.eq_of_le hp.ne_top hm_sub).symm

theorem krullDimLE_zero_of_isArtinianRing_atIrrelevant
    (h𝒜₀ : ConnectedGraded 𝒜)
    [IsNoetherianRing A]
    (hArtinian : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsArtinianRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    Ring.KrullDimLE 0 A := by
  have hnilp := irrelevant_isNilpotent_of_isArtinianRing_atIrrelevant
    𝒜 h𝒜₀ hArtinian
  refine Ring.KrullDimLE.mk₀ (fun p hp => ?_)
  have hp_eq : p = (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    isMaximal_of_isPrime_of_irrelevant_nilpotent 𝒜 h𝒜₀ hnilp p hp
  rw [hp_eq]; exact irrelevant_isMaximal 𝒜 h𝒜₀

/-- **Step B2b.** If `A` is a connected ℕ-graded finitely-generated Noetherian
`K`-algebra and `A_{𝒜₊}` is Artinian, then `A` is finite-dimensional as a
`K`-module. -/
theorem finite_over_K_of_isArtinianRing_atIrrelevant
    (h𝒜₀ : ConnectedGraded 𝒜)
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (hArtinian : haveI := (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsArtinianRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    Module.Finite K A := by
  haveI : Ring.KrullDimLE 0 A :=
    krullDimLE_zero_of_isArtinianRing_atIrrelevant 𝒜 h𝒜₀ hArtinian
  haveI : IsArtinianRing A := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  exact Module.finite_of_isArtinianRing K A

end GradedFiniteFree

end

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
import toMathlib.CohenMacaulay.Polynomial
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.KrullDimension.Regular

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

/-! ### Step D: finite-free over a polynomial ring ⟹ globally Cohen–Macaulay

If `A` is a finite free module over `P := MvPolynomial (Fin d) K` (via some
algebra structure), then `A` is globally Cohen–Macaulay.

Strategy at a prime `𝔭 ⊂ A`:
* Set `𝔮 := 𝔭.comap (algebraMap P A)`.
* `P_𝔮` is CM local (polynomial CM + CM localizes), of dimension `e := height 𝔮`.
* Extract a weakly regular sequence `rs` in `P` with all elements in `𝔮`
  and length `e` (using `exists_weaklyRegular_in_prime` on `P_𝔮`, lifted back).
* Map `rs` to `A_𝔭` through the composed algebra map. `A_𝔭` is flat over `P`
  (composition: `A` free over `P`, `A_𝔭` a localization of `A`), so the images
  form a weakly regular sequence on `A_𝔭`.
* Each image lies in `maxIdeal A_𝔭` since `𝔮 ⊆ 𝔭`.
* `dim A_𝔭 ≤ e` by Krull's height theorem: the images generate an ideal whose
  only prime containing it is `maxIdeal A_𝔭` (because `A_𝔭/(rs)` is a quotient
  of the Artinian-local `A_𝔭/𝔮A_𝔭`, finite over `P_𝔮/𝔮P_𝔮 = κ(𝔮)`).
* Combined with the length-`e` weakly regular sequence gives CM local.
-/

namespace GradedFiniteFree

open IsLocalRing RingTheory.Sequence

universe u

/-- In a finite algebra `P → A`, if `𝔭 ⊂ A` lies over `𝔮 ⊂ P` (both prime), the image
of `𝔭` in `A/𝔮·A` has height 0.

**Mathematics.** `A/𝔮·A` is integral over the domain `P/𝔮`, and the image of `𝔭`
lies over `(0) ⊂ P/𝔮`, so by incomparability of primes in integral extensions,
it is a minimal prime of `A/𝔮·A` (height 0).

**Formalization status.** Not proved here. The ingredients exist in Mathlib:
* `Ideal.comap_lt_comap_of_integral_mem_sdiff` (incomparability).
* `Ideal.Quotient.algebra_isIntegral_of_liesOver` (integral extension in the
  quotient), `Ideal.Quotient.algebraQuotientOfLEComap` (induced algebra).

The blocker is a non-trivial amount of defeq wrangling between the two
equivalent algebra structures on `A/𝔮·A` as a `P/𝔮`-algebra: the one coming
from `Ideal.Quotient.algebraQuotientOfLEComap` versus the one obtained by
first restricting scalars along `P → P/𝔮`. Closing this would require ~30 lines
of scalar-tower bookkeeping. A proper upstream lemma would be:

  `theorem Ideal.primeHeight_eq_zero_of_liesOver_bot [Algebra.IsIntegral R S]
      [IsDomain R] (P : Ideal S) [P.IsPrime] [P.LiesOver (⊥ : Ideal R)] :
      P.primeHeight = 0`

Such a lemma is a natural companion to `Ideal.eq_bot_of_liesOver_bot`
(which requires `IsDomain S`) but is strictly weaker (only asks height 0, not
equality with ⊥, so does not need `IsDomain S`). -/
private lemma mvPolynomial_finite_free_quotient_prime_height_zero
    (P A : Type*) [CommRing P] [CommRing A] [Nontrivial A]
    [Algebra P A] [Module.Finite P A] [IsNoetherianRing A]
    (𝔮 : Ideal P) [𝔮.IsPrime]
    (𝔭 : Ideal A) [𝔭.IsPrime] [h𝔭𝔮 : 𝔭.LiesOver 𝔮] :
    (𝔭.map (Ideal.Quotient.mk (𝔮.map (algebraMap P A)))).height = 0 := by
  classical
  haveI : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
  -- Let `B := A/𝔮·A` and `f := Ideal.Quotient.mk (𝔮·A) ∘ algebraMap P A : P → B`.
  -- This composes to a ring hom `P → B` whose kernel contains 𝔮 (actually equals it after
  -- quotienting by 𝔮). The image of the 𝔭 ≥ 𝔮·A is a prime P' in B with f.comap P' = 𝔭.comap.
  set B := A ⧸ 𝔮.map (algebraMap P A) with hB_def
  set fPA : P →+* A := algebraMap P A
  set πB : A →+* B := Ideal.Quotient.mk (𝔮.map fPA)
  set fPB : P →+* B := πB.comp fPA
  set P' : Ideal B := 𝔭.map πB with hP'_def
  have hker_le : 𝔮.map fPA ≤ 𝔭 := by
    rw [Ideal.map_le_iff_le_comap]; exact h𝔭𝔮.over.le
  haveI hP'_prime : P'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hker_le)
  -- Key: P'.comap fPB = 𝔮. (Same as 𝔭.comap fPA = 𝔮 up to the quotient.)
  have hcomap_P'_fPB : P'.comap fPB = 𝔮 := by
    ext y
    simp only [Ideal.mem_comap, fPB, RingHom.comp_apply, hP'_def, πB]
    rw [Ideal.mem_quotient_iff_mem hker_le]
    -- Quotient.mk (algebraMap P A y) ∈ 𝔭.map (Quotient.mk) ↔ algebraMap P A y ∈ 𝔭.
    -- y ∈ 𝔮 ↔ fPA y ∈ 𝔭 by LiesOver.
    have hover : 𝔮 = 𝔭.comap fPA := h𝔭𝔮.over
    rw [hover, Ideal.mem_comap]
  -- The image of P' under Quot.mk 𝔮 → Pbar, i.e., P' viewed relative to Pbar:
  -- Equivalently, use quotient-ring factoring.
  -- The ring hom fPB : P → B factors as P → P/𝔮 → B.
  -- Actually fPB(y) for y ∈ 𝔮: πB (fPA y) = Quot.mk (fPA y), and fPA y ∈ 𝔮.map fPA, so this is 0.
  -- So `fPB` factors through `P/𝔮 = Pbar`, giving a ring hom `gPB : Pbar → B`.
  have hfPB_ker : ∀ x ∈ 𝔮, fPB x = 0 := by
    intro x hx
    simp only [fPB, RingHom.comp_apply, πB]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem fPA hx
  -- Induced ring hom Pbar → B via the quotient of fPB by 𝔮.
  set gPB : P ⧸ 𝔮 →+* B := Ideal.Quotient.lift 𝔮 fPB hfPB_ker
  have hgPB_factor : gPB.comp (Ideal.Quotient.mk 𝔮) = fPB := by
    ext y
    exact Ideal.Quotient.lift_mk 𝔮 fPB hfPB_ker
  -- gPB is an integral ring hom.
  have hgPB_int : gPB.IsIntegral := by
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := 𝔮.map fPA) b
    obtain ⟨p, hp_mon, hp_eval⟩ := (Algebra.IsIntegral.isIntegral (R := P) (A := A) a)
    refine ⟨p.map (Ideal.Quotient.mk 𝔮), hp_mon.map _, ?_⟩
    rw [Polynomial.eval₂_map, hgPB_factor]
    -- eval₂ fPB (πB a) p = πB (eval₂ fPA a p) = πB 0 = 0.
    have : Polynomial.eval₂ fPB (πB a) p = πB (Polynomial.eval₂ fPA a p) := by
      simp only [fPB, ← Polynomial.hom_eval₂]
    rw [this, hp_eval, map_zero]
  -- Now P' is a prime of B, lies over gPB.comap P' in Pbar, and gPB.comap P' = ⊥.
  have hP'_comap_gPB : P'.comap gPB = ⊥ := by
    -- gPB.comap P' in Pbar. Equivalent to fPB.comap P' / 𝔮 = 𝔮/𝔮 = ⊥.
    apply le_antisymm _ bot_le
    intro x hx
    rw [Ideal.mem_comap] at hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := 𝔮) x
    -- gPB ((Ideal.Quotient.mk 𝔮) y) = fPB y
    have hfy : gPB ((Ideal.Quotient.mk 𝔮) y) = fPB y := Ideal.Quotient.lift_mk 𝔮 fPB _
    rw [hfy] at hx
    have : y ∈ 𝔮 := by
      have := hcomap_P'_fPB ▸ (show y ∈ P'.comap fPB from hx)
      exact this
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
    exact this
  -- Apply primeHeight = 0 iff minimal prime, using incomparability.
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff]
  refine ⟨⟨hP'_prime, bot_le⟩, ?_⟩
  rintro Q ⟨hQ_prime, _⟩ hQ_le
  by_contra hneQ
  have hQ_lt : Q < P' := lt_of_le_not_ge hQ_le hneQ
  obtain ⟨hQ_le', x, hxP', hxQ⟩ := SetLike.lt_iff_le_and_exists.mp hQ_lt
  -- x is integral over gPB.
  obtain ⟨p, hp_mon, hp_eval⟩ := hgPB_int x
  have hmap_ne : p.map (Ideal.Quotient.mk (Q.comap gPB)) ≠ 0 :=
    Polynomial.map_monic_ne_zero hp_mon
  have hincomp := Ideal.comap_lt_comap_of_root_mem_sdiff (f := gPB) hQ_le'
    ⟨hxP', hxQ⟩ hmap_ne
    (by rw [hp_eval]; exact Q.zero_mem)
  have hQ_comap_gPB : Q.comap gPB = ⊥ :=
    le_bot_iff.mp (hP'_comap_gPB ▸ Ideal.comap_mono hQ_le)
  rw [hQ_comap_gPB, hP'_comap_gPB] at hincomp
  exact lt_irrefl _ hincomp

/-- **Step D** of the finite-free Case C route.

Given a field `K`, a natural number `d`, and a nontrivial commutative `K`-algebra
`A` which is a finite free module over `P := MvPolynomial (Fin d) K`, then `A`
is globally Cohen–Macaulay.

The proof localizes at each prime `𝔭 ⊂ A`, transfers a weakly regular sequence
from the CM local ring `P_𝔮` (where `𝔮 = 𝔭 ∩ P`) via flat base change, and
uses Krull's height theorem to bound the dimension from above. -/
theorem isCohenMacaulayRing_of_module_free_of_mvPolynomial
    {d : ℕ} {K : Type u} [Field K] {A : Type u} [CommRing A] [Nontrivial A]
    [Algebra (MvPolynomial (Fin d) K) A]
    [Module.Free (MvPolynomial (Fin d) K) A]
    [Module.Finite (MvPolynomial (Fin d) K) A] :
    IsCohenMacaulayRing A := by
  classical
  -- Abbreviate.
  set P := MvPolynomial (Fin d) K with hP_def
  -- `P` is Cohen–Macaulay.
  haveI hCMP : IsCohenMacaulayRing P := isCohenMacaulayRing_mvPolynomial_field K d
  -- `P` is Noetherian.
  haveI : IsNoetherianRing P := MvPolynomial.isNoetherianRing
  -- `A` is Noetherian (finite module over Noetherian ring).
  haveI : IsNoetherianRing A := IsNoetherianRing.of_finite P A
  -- `A` is flat over `P` (free ⟹ flat).
  haveI : Module.Flat P A := Module.Flat.of_free
  refine ⟨fun 𝔭 h𝔭 => ?_⟩
  set 𝔮 : Ideal P := 𝔭.comap (algebraMap P A) with h𝔮_def
  haveI h𝔮_prime : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  set Pq := Localization.AtPrime 𝔮
  set Ap := Localization.AtPrime 𝔭
  -- `Pq` is Noetherian local, CM local.
  haveI : IsNoetherianRing Pq := IsLocalization.isNoetherianRing 𝔮.primeCompl _ inferInstance
  haveI : IsCohenMacaulayLocalRing Pq := hCMP.CM_localize 𝔮
  -- Universe-0 hypothesis for `exists_weaklyRegular_in_prime` — need `Small.{0} Pq`. Use the
  -- version in the prime complement of `P` directly via localization of a regular sop.
  haveI : IsLocalRing Pq := inferInstance
  -- `A_𝔭` is Noetherian (localization of Noetherian).
  haveI : IsNoetherianRing Ap := IsLocalization.isNoetherianRing 𝔭.primeCompl _ inferInstance
  haveI : IsLocalRing Ap := IsLocalization.AtPrime.isLocalRing _ 𝔭
  -- Flatness of `Ap` over `P`: `A` is flat over `P`, `Ap` is a localization of `A`.
  haveI hFlatAAp : Module.Flat A Ap := IsLocalization.flat Ap 𝔭.primeCompl
  haveI hFlatPAp : Module.Flat P Ap := Module.Flat.trans P A Ap
  -- Set up `Algebra Pq Ap`: every `s ∈ 𝔮.primeCompl` is a unit in `Ap`.
  have hq_units : ∀ s : 𝔮.primeCompl,
      IsUnit ((algebraMap P Ap) s) := by
    rintro ⟨s, hs⟩
    have hs_not_in_𝔮 : s ∉ 𝔮 := hs
    -- algebraMap P A s ∉ 𝔭, hence becomes a unit in Ap.
    have hsA : algebraMap P A s ∉ 𝔭 := hs_not_in_𝔮
    have : algebraMap P Ap s =
        algebraMap A Ap (algebraMap P A s) := by
      rw [IsScalarTower.algebraMap_apply P A Ap]
    rw [this]
    exact IsLocalization.map_units Ap (⟨algebraMap P A s, hsA⟩ : 𝔭.primeCompl)
  letI algPqAp : Algebra Pq Ap := (IsLocalization.lift (S := Pq)
    (g := algebraMap P Ap) hq_units).toAlgebra
  haveI hST_PqAp : IsScalarTower P Pq Ap := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap P Ap x = IsLocalization.lift hq_units (algebraMap P Pq x)
    rw [IsLocalization.lift_eq])
  -- `Module.Flat Pq Ap` from `Module.Flat P Ap` via `Module.flat_iff_of_isLocalization`.
  haveI : Module.Flat Pq Ap :=
    (Module.flat_iff_of_isLocalization (R := P) Pq 𝔮.primeCompl Ap).mpr hFlatPAp
  -- Get height `e = primeHeight 𝔮` as a `ℕ`.
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℕ∞) = 𝔮.primeHeight := by
    obtain ⟨e, he⟩ := WithTop.ne_top_iff_exists.mp (Ideal.primeHeight_ne_top 𝔮)
    exact ⟨e, he⟩
  -- `dim Pq = e`.
  have hPq_dim : ringKrullDim Pq = (e : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 Pq,
      Ideal.height_eq_primeHeight, ← he]
  -- `primeHeight (maxIdeal Pq) = dim Pq = e`.
  have hmax_ht : (IsLocalRing.maximalIdeal Pq).primeHeight = (e : ℕ∞) := by
    have := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := Pq)
    -- this : (maxIdeal Pq).primeHeight = ringKrullDim Pq (as WithBot ℕ∞)
    rw [hPq_dim] at this
    exact_mod_cast this
  -- Universe-0: `Pq` is in universe u. `exists_weaklyRegular_in_prime` needs `Small.{u}`.
  haveI : Small.{u, u} Pq := small_self _
  -- Build weakly regular sequence in Pq of length e, all in maxIdeal Pq.
  obtain ⟨ss, hss_len, hss_reg, _, hss_max⟩ :=
    exists_weaklyRegular_in_prime e Pq (IsLocalRing.maximalIdeal Pq) (le_of_eq hmax_ht.symm)
  -- Images in `A_𝔭` via flat base change `Pq → Ap`.
  set rsA : List Ap := ss.map (algebraMap Pq Ap)
  have hrsA_reg : IsWeaklyRegular Ap rsA := IsWeaklyRegular.of_flat hss_reg
  have hrsA_len : rsA.length = e := by simp [rsA, hss_len]
  -- Each element of rsA lies in maxIdeal Ap.
  -- Strategy: show `maxIdeal Pq ⊆ comap (algebraMap Pq Ap) (maxIdeal Ap)`.
  -- Since `comap` of a prime is prime, and lies over 𝔮 (by the scalar tower to P),
  -- and the only prime of Pq lying over 𝔮 is maxIdeal Pq, equality holds.
  have h_comap_eq :
      (IsLocalRing.maximalIdeal Ap).comap (algebraMap Pq Ap)
        = IsLocalRing.maximalIdeal Pq := by
    -- `comap` of a prime is prime. It suffices to check ≥, since `maxIdeal Pq` is
    -- maximal and the comap is a proper ideal (it doesn't contain 1).
    refine ((IsLocalRing.maximalIdeal.isMaximal Pq).eq_of_le ?_ ?_).symm
    · -- Comap ≠ ⊤: 1 ∉ maxIdeal Ap.
      intro hTop
      have h1 : algebraMap Pq Ap 1 ∈ IsLocalRing.maximalIdeal Ap := by
        have h : (1 : Pq) ∈ (IsLocalRing.maximalIdeal Ap).comap (algebraMap Pq Ap) := by
          rw [hTop]; exact Submodule.mem_top
        simp only [Ideal.mem_comap] at h
        exact h
      rw [map_one] at h1
      exact (IsLocalRing.maximalIdeal.isMaximal Ap).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
    · -- maxIdeal Pq ≤ Comap. Use that maxIdeal Pq = 𝔮.map (algebraMap P Pq).
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      change (algebraMap Pq Ap) ((algebraMap P Pq) x) ∈ IsLocalRing.maximalIdeal Ap
      have hxA : algebraMap P A x ∈ 𝔭 := hx
      have heq : (algebraMap Pq Ap) ((algebraMap P Pq) x)
          = (algebraMap A Ap) ((algebraMap P A) x) := by
        rw [← IsScalarTower.algebraMap_apply P Pq Ap,
          ← IsScalarTower.algebraMap_apply P A Ap]
      rw [heq]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff Ap 𝔭 _).mpr hxA
  have hrsA_mem : ∀ r ∈ rsA, r ∈ maximalIdeal Ap := by
    intro r hr
    obtain ⟨pq, hpq_mem, rfl⟩ := List.mem_map.mp hr
    have hpq_max : pq ∈ IsLocalRing.maximalIdeal Pq := hss_max pq hpq_mem
    rw [← h_comap_eq, Ideal.mem_comap] at hpq_max
    exact hpq_max
  -- `dim Ap ≤ e` via `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` applied to
  -- `P → A`. We have `𝔭.height = 𝔮.height + (𝔭/𝔮·A).height`. The second term is 0
  -- since the integral extension `P/𝔮 → A/𝔮·A` forces primes lying over `⊥` to have
  -- height 0 (incomparability via `Ideal.comap_lt_comap_of_integral_mem_sdiff`).
  have hdim_le : ringKrullDim Ap ≤ (e : ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 Ap]
    haveI : 𝔭.LiesOver 𝔮 := ⟨rfl⟩
    haveI : Algebra.HasGoingDown P A := Algebra.HasGoingDown.of_flat
    haveI : Algebra.IsIntegral P A := Algebra.IsIntegral.of_finite P A
    have hheight :=
      Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := P) (S := A) 𝔮 𝔭
    -- `𝔭 mod 𝔮·A` has height 0 in `A/𝔮·A`.
    have hP'_ht0 :
        (𝔭.map (Ideal.Quotient.mk (𝔮.map (algebraMap P A)))).height = 0 :=
      mvPolynomial_finite_free_quotient_prime_height_zero P A 𝔮 𝔭
    rw [hP'_ht0, add_zero] at hheight
    rw [hheight, Ideal.height_eq_primeHeight, ← he]
  -- `dim Ap ≥ e` via the length-e weakly regular sequence.
  have hdim_ge : (e : ℕ∞) ≤ ringKrullDim Ap := by
    have hlen_le_depth : (rsA.length : ℕ∞) ≤ ringDepth Ap :=
      ringDepth_le_of_isWeaklyRegular Ap hrsA_reg hrsA_mem
    have hdepth_le : (ringDepth Ap : WithBot ℕ∞) ≤ ringKrullDim Ap :=
      ringDepth_le_ringKrullDim Ap
    have : (e : ℕ∞) ≤ ringDepth Ap := by rw [← hrsA_len]; exact hlen_le_depth
    calc (e : WithBot ℕ∞) = ((e : ℕ∞) : WithBot ℕ∞) := by norm_cast
      _ ≤ (ringDepth Ap : WithBot ℕ∞) := by exact_mod_cast this
      _ ≤ ringKrullDim Ap := hdepth_le
  have hdim_eq : ringKrullDim Ap = (e : ℕ∞) := by
    apply le_antisymm hdim_le
    exact_mod_cast hdim_ge
  -- Conclude CM via `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim`.
  have hdim_eq' : ringKrullDim Ap = (rsA.length : ℕ∞) := by
    rw [hdim_eq, hrsA_len]
  exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim hrsA_reg hrsA_mem hdim_eq'

end GradedFiniteFree

end

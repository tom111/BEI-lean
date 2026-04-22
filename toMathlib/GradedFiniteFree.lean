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
import toMathlib.GradedQuotient
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
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Regular.RegularSequence

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

/-- **Step D (general flat version)** of the finite-free Case C route.

Given a field `K`, a natural number `d`, and a nontrivial commutative `K`-algebra
`A` which is a finite FLAT module over `P := MvPolynomial (Fin d) K`, then `A`
is globally Cohen–Macaulay. The Free variant is a direct consequence since
`Module.Free ⟹ Module.Flat`.

The proof localizes at each prime `𝔭 ⊂ A`, transfers a weakly regular sequence
from the CM local ring `P_𝔮` (where `𝔮 = 𝔭 ∩ P`) via flat base change, and
uses Krull's height theorem to bound the dimension from above. -/
theorem isCohenMacaulayRing_of_module_flat_of_mvPolynomial
    {d : ℕ} {K : Type u} [Field K] {A : Type u} [CommRing A] [Nontrivial A]
    [Algebra (MvPolynomial (Fin d) K) A]
    [Module.Flat (MvPolynomial (Fin d) K) A]
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

/-- **Step D (free variant).** Free hypothesis specialization of
`isCohenMacaulayRing_of_module_flat_of_mvPolynomial`; the primary Step D version
supplied as a convenience wrapper. -/
theorem isCohenMacaulayRing_of_module_free_of_mvPolynomial
    {d : ℕ} {K : Type u} [Field K] {A : Type u} [CommRing A] [Nontrivial A]
    [Algebra (MvPolynomial (Fin d) K) A]
    [Module.Free (MvPolynomial (Fin d) K) A]
    [Module.Finite (MvPolynomial (Fin d) K) A] :
    IsCohenMacaulayRing A := by
  haveI : Module.Flat (MvPolynomial (Fin d) K) A := Module.Flat.of_free
  exact isCohenMacaulayRing_of_module_flat_of_mvPolynomial (d := d) (K := K) (A := A)

/-! ### Step C: finite-free over `MvPolynomial (Fin d) K` from a homogeneous
regular system of parameters

Given a homogeneous regular sop `θ : Fin d → A` in the irrelevant ideal of a
connected ℕ-graded Noetherian `K`-algebra, with `A ⧸ Ideal.ofList (List.ofFn θ)`
finite over `K`, `A` becomes finite-free over `P := MvPolynomial (Fin d) K`
under `T_i ↦ θ_i`.

The proof goes by induction on `d`. The `d = 0` base case is immediate: the
polynomial ring is just `K`, and `A` is already finite-dimensional over `K`
(a vector space, hence automatically free).

The inductive step uses `MvPolynomial.finSuccEquiv` to identify
`MvPolynomial (Fin (d+1)) K ≃ₐ[K] (MvPolynomial (Fin d) K)[X]`, and lifts a
finite free structure on `A ⧸ (θ_d)` over `MvPolynomial (Fin d) K` to a
finite free structure on `A` over the `d+1`-variable polynomial ring.

**STATUS:** Proved axiom-clean via the three building blocks
`exists_homogeneous_basis_of_finite_graded`,
`span_aeval_eq_top_of_homogeneous_basis_lift` (surjectivity) and
`linearIndependent_aeval_of_basis_lift` (linear independence, proven by
induction on `d` combining `linearIndependent_aeval_fin_zero` and
`linearIndependent_aeval_cons_step`). -/

/-! ### Homogeneous basis for a finite-dimensional graded algebra

Any finite-dimensional ℕ-graded `K`-algebra admits a homogeneous `K`-basis,
obtained by concatenating `K`-bases of its finitely many nonzero graded
pieces. This is a standard ingredient for the finite-free parameter subring
construction. -/

/-- Any finite-dimensional ℕ-graded `K`-algebra admits a homogeneous `K`-basis
obtained by concatenating bases of the finitely many nonzero graded pieces. -/
theorem exists_homogeneous_basis_of_finite_graded
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] [Module.Finite K A] :
    ∃ (ι : Type u) (_ : Fintype ι) (deg : ι → ℕ) (b : Module.Basis ι K A),
      ∀ i, (b i : A) ∈ 𝒜 (deg i) := by
  classical
  -- Internal direct sum decomposition `A ≃ ⨁ n, 𝒜 n`.
  have h_int : DirectSum.IsInternal 𝒜 :=
    DirectSum.Decomposition.isInternal 𝒜
  -- For each graded piece, choose a `K`-vector-space basis.
  let α : ℕ → Type u := fun n => Module.Basis.ofVectorSpaceIndex K (𝒜 n)
  let v : ∀ n, Module.Basis (α n) K (𝒜 n) :=
    fun n => Module.Basis.ofVectorSpace K (𝒜 n)
  -- Concatenated basis of `A` indexed by `Σ n : ℕ, α n`.
  let B : Module.Basis (Σ n : ℕ, α n) K A := h_int.collectedBasis v
  -- From `Module.Finite K A` + existence of a basis, the index type is finite.
  have hfin : Finite (Σ n : ℕ, α n) := Module.Finite.finite_basis B
  haveI : Fintype (Σ n : ℕ, α n) := Fintype.ofFinite _
  refine ⟨Σ n : ℕ, α n, inferInstance, fun i => i.1, B, ?_⟩
  intro i
  -- Each collected-basis element lives in the corresponding graded piece.
  exact h_int.collectedBasis_mem v i

/-! ### Graded decomposition of ideal membership

If `r` is homogeneous of degree `n` and lies in the ideal generated by
homogeneous elements `θ i` of degrees `degθ i`, then `r` can be written
as a homogeneous-component sum `r = ∑ s i * θ i` with each `s i`
homogeneous of degree `n - degθ i` (and zero when `n < degθ i`). This
is the "graded lift of ideal membership" fact needed for degree-by-degree
induction arguments. -/

/-- Graded decomposition of the product `a * b` at a fixed degree, where
`b ∈ 𝒜 j` is homogeneous: the degree-`n` component of `a * b` equals the
degree-`(n - j)` component of `a` times `b` when `j ≤ n`, and vanishes
otherwise. -/
private lemma coe_decompose_mul_right_apply
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    {a b : A} {j : ℕ} (hb : b ∈ 𝒜 j) (n : ℕ) :
    (DirectSum.decompose 𝒜 (a * b) n : A) =
      if j ≤ n then (DirectSum.decompose 𝒜 a (n - j) : A) * b else 0 := by
  classical
  split_ifs with hjn
  · -- Case `j ≤ n`: apply `coe_decompose_mul_add_of_right_mem` with `i := n - j`.
    have heq : (n - j) + j = n := Nat.sub_add_cancel hjn
    have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (i := n - j) (j := j) hb (a := a)
    rw [heq] at this
    exact this
  · -- Case `n < j`: decompose `a = ∑_m a_m` and sum termwise.
    push_neg at hjn
    rw [show a * b = ∑ m ∈ (DirectSum.decompose 𝒜 a).support,
          (DirectSum.decompose 𝒜 a m : A) * b from by
      conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 a]
      rw [Finset.sum_mul]]
    rw [DirectSum.decompose_sum]
    rw [show ((∑ m ∈ (DirectSum.decompose 𝒜 a).support,
        DirectSum.decompose 𝒜
          ((DirectSum.decompose 𝒜 a m : A) * b)) n : A) =
        ∑ m ∈ (DirectSum.decompose 𝒜 a).support,
          (DirectSum.decompose 𝒜
            ((DirectSum.decompose 𝒜 a m : A) * b) n : A) from ?_]
    · apply Finset.sum_eq_zero
      intro m _
      -- `(decompose 𝒜 a m : A) * b ∈ 𝒜 (m + j)`; `m + j ≠ n` since `n < j ≤ m + j`.
      have hmul_mem : (DirectSum.decompose 𝒜 a m : A) * b ∈ 𝒜 (m + j) :=
        SetLike.mul_mem_graded (SetLike.coe_mem _) hb
      by_cases hmn : m + j = n
      · omega
      · exact DirectSum.decompose_of_mem_ne 𝒜 hmul_mem hmn
    · -- `((∑ f_k) n : A) = ∑ (f_k n : A)` — DFinsupp sum eval + coe.
      rw [DFinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]

/-- Graded decomposition of membership in an ideal generated by homogeneous
elements: if `r` is homogeneous of degree `n` and lies in
`Ideal.span (Set.range θ)` with each `θ i` homogeneous of degree `degθ i`,
then `r = ∑ i, s i * θ i` with each `s i` homogeneous of degree
`n - degθ i` (where the difference is interpreted as `0` when it would be
negative, in which case `s i = 0`). -/
theorem exists_homogeneous_decomposition_mem_span_range
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    {d : ℕ} (θ : Fin d → A) (degθ : Fin d → ℕ)
    (hθ_hom : ∀ i, (θ i : A) ∈ 𝒜 (degθ i))
    {n : ℕ} {r : A} (hr_hom : r ∈ 𝒜 n)
    (hr_mem : r ∈ Ideal.span (Set.range θ)) :
    ∃ s : Fin d → A, r = ∑ i, s i * θ i ∧
      (∀ i, if n < degθ i then s i = 0 else s i ∈ 𝒜 (n - degθ i)) := by
  classical
  -- Step 1: Extract a (non-homogeneous) presentation `r = ∑ i, c i * θ i`.
  rw [← Ideal.submodule_span_eq] at hr_mem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hr_mem
  -- Rewrite `c i • θ i = c i * θ i`.
  have hc_mul : r = ∑ i, c i * θ i := by
    rw [← hc]; simp [smul_eq_mul]
  -- Step 2: Define `s i` as the homogeneous component of `c i` at degree `n - degθ i`,
  -- zero when `n < degθ i`.
  refine ⟨fun i => if n < degθ i then 0
      else (DirectSum.decompose 𝒜 (c i) (n - degθ i) : A), ?_, ?_⟩
  · -- Key identity: `r = ∑ i, s i * θ i`.
    -- Project `r = ∑ i, c i * θ i` to degree `n`. Since `r ∈ 𝒜 n`, the LHS projects to `r`.
    have hrn : (DirectSum.decompose 𝒜 r n : A) = r :=
      DirectSum.decompose_of_mem_same 𝒜 hr_hom
    calc r = (DirectSum.decompose 𝒜 r n : A) := hrn.symm
      _ = (DirectSum.decompose 𝒜 (∑ i, c i * θ i) n : A) := by rw [hc_mul]
      _ = ∑ i, (DirectSum.decompose 𝒜 (c i * θ i) n : A) := by
          rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply,
            AddSubmonoidClass.coe_finset_sum]
      _ = ∑ i, if degθ i ≤ n
            then (DirectSum.decompose 𝒜 (c i) (n - degθ i) : A) * θ i else 0 := by
          apply Finset.sum_congr rfl
          intro i _
          exact coe_decompose_mul_right_apply 𝒜 (hθ_hom i) n
      _ = ∑ i, (if n < degθ i then 0
            else (DirectSum.decompose 𝒜 (c i) (n - degθ i) : A)) * θ i := by
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : n < degθ i
          · have : ¬ degθ i ≤ n := Nat.not_le.mpr h
            simp [this, h]
          · have hle : degθ i ≤ n := Nat.not_lt.mp h
            simp [hle, h]
  · -- Each `s i` is either 0 (when `n < degθ i`) or in `𝒜 (n - degθ i)`.
    intro i
    by_cases h : n < degθ i
    · simp [h]
    · simp only [h, if_false]
      exact SetLike.coe_mem _

/-! ### Step C sub-step B: generation of `A` over the polynomial subring

Given a connected ℕ-graded Noetherian `K`-algebra `A`, a sequence `θ : Fin d → A`
of homogeneous elements of positive degree, and homogeneous elements `b : ι → A`
whose images form a `K`-basis of `A ⧸ Ideal.span (Set.range θ)`, the `b`-span of
`A` over `MvPolynomial (Fin d) K` (via `T_i ↦ θ_i`) equals `⊤`. -/

/-- **Step C, sub-step B (surjectivity).** Given `A` a connected ℕ-graded
Noetherian `K`-algebra, a sequence `θ : Fin d → A` of homogeneous elements
of positive degree `n_i > 0`, and elements `b : ι → A` homogeneous of degrees
`deg i` whose images form a `K`-basis of `A ⧸ Ideal.span (Set.range θ)`, the
`aeval θ`-span of `Set.range b` equals `⊤`.

This implies that `A` is finitely generated as a module over
`MvPolynomial (Fin d) K` (acting via `T_i ↦ θ_i`) by the family `b`. -/
theorem span_aeval_eq_top_of_homogeneous_basis_lift
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    {d : ℕ} (θ : Fin d → A) (n : Fin d → ℕ)
    (hθ_deg : ∀ i, θ i ∈ 𝒜 (n i)) (hn_pos : ∀ i, 0 < n i)
    {ι : Type u} [Fintype ι] (deg : ι → ℕ) (b : ι → A)
    (hb_deg : ∀ i, b i ∈ 𝒜 (deg i))
    (hb_basis : Module.Basis ι K
      (A ⧸ Ideal.span (Set.range θ)))
    (hb_lift : ∀ i,
      (Ideal.Quotient.mk (Ideal.span (Set.range θ)) (b i) : A ⧸ _) =
        hb_basis i) :
    letI _alg : Algebra (MvPolynomial (Fin d) K) A :=
      (MvPolynomial.aeval θ).toAlgebra
    Submodule.span (MvPolynomial (Fin d) K) (Set.range b) = ⊤ := by
  classical
  letI alg : Algebra (MvPolynomial (Fin d) K) A :=
    (MvPolynomial.aeval θ).toAlgebra
  set P : Type u := MvPolynomial (Fin d) K with hP_def
  let I : Ideal A := Ideal.span (Set.range θ)
  -- `I` is a homogeneous ideal: each generator `θ i` is homogeneous.
  have hI_hom : I.IsHomogeneous 𝒜 := by
    apply Ideal.homogeneous_span
    rintro x ⟨i, rfl⟩
    exact ⟨n i, hθ_deg i⟩
  -- Convenient abbreviation for the target span.
  set S : Submodule P A := Submodule.span P (Set.range b) with hS_def
  -- The `P`-module action on `A` comes from `aeval θ`:
  -- `(p : P) • (a : A) = MvPolynomial.aeval θ p * a`.
  have h_smul_def : ∀ (p : P) (a : A), p • a = MvPolynomial.aeval θ p * a := by
    intro p a
    change alg.algebraMap p * a = _
    rfl
  -- For `k : K`, `C k • a = algebraMap K A k * a` (note `aeval θ (C k) = algebraMap K A k`).
  have h_C_smul : ∀ (k : K) (a : A),
      (MvPolynomial.C k : P) • a = algebraMap K A k * a := by
    intro k a
    rw [h_smul_def, MvPolynomial.aeval_C]
  -- `θ i = X i • 1`: the generator `θ i` is the scalar action of `X i` on `1`.
  have h_X_smul : ∀ (i : Fin d) (a : A),
      (MvPolynomial.X i : P) • a = θ i * a := by
    intro i a
    rw [h_smul_def, MvPolynomial.aeval_X]
  -- ## Step 1: K-linear combinations of `b i` are in `S`.
  -- Explicit: `algebraMap K A k * b i ∈ S`.
  have h_kb_mem : ∀ (k : K) (i : ι), algebraMap K A k * b i ∈ S := by
    intro k i
    rw [← h_C_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- `S` contains `θ j * s` whenever `s ∈ S`.
  have h_θ_mul_mem : ∀ (j : Fin d) {s : A}, s ∈ S → θ j * s ∈ S := by
    intro j s hs
    rw [← h_X_smul]
    exact Submodule.smul_mem _ _ hs
  -- ## Step 2: Strong induction.
  -- Goal: every `a ∈ 𝒜 n₀` is in `S`, for every `n₀ : ℕ`.
  -- We use strong induction via `Nat.strong_induction_on`.
  suffices h_homogeneous_mem : ∀ n₀ : ℕ, ∀ a : A, a ∈ 𝒜 n₀ → a ∈ S by
    -- Then every `a : A` is in `S` by decomposition into graded pieces.
    rw [eq_top_iff]
    intro a _
    rw [← DirectSum.sum_support_decompose 𝒜 a]
    refine Submodule.sum_mem _ ?_
    intro m _
    exact h_homogeneous_mem m _ (SetLike.coe_mem _)
  intro n₀
  induction n₀ using Nat.strong_induction_on with
  | _ n₀ IH =>
    intro a ha
    -- Compute the basis representation of `mk a` in `A/I`.
    set a_bar : A ⧸ I := Ideal.Quotient.mk I a with ha_bar_def
    set c : ι →₀ K := hb_basis.repr a_bar with hc_def
    -- Lift: `a_lift := ∑ i, algebraMap K A (c i) * b i`. (Only the support of `c`
    -- matters, but we can write the sum over a `Fintype ι`.)
    set a_lift : A := ∑ i, algebraMap K A (c i) * b i with ha_lift_def
    -- **(a)** `a_lift ∈ S`.
    have h_a_lift_mem : a_lift ∈ S := by
      refine Submodule.sum_mem _ ?_
      intro i _
      exact h_kb_mem (c i) i
    -- **(b)** `mk a_lift = a_bar` inside `A/I`.
    -- Using `hb_basis.sum_repr a_bar`.
    have h_mk_a_lift : Ideal.Quotient.mk I a_lift = a_bar := by
      -- `mk a_lift = ∑ i, (c i) • mk(b i) = ∑ i, (c i) • hb_basis i = a_bar`.
      rw [ha_lift_def, map_sum]
      conv_rhs => rw [← hb_basis.sum_repr a_bar]
      refine Finset.sum_congr rfl ?_
      intro i _
      -- `mk (algebraMap K A (c i) * b i) = (c i) • hb_basis i`.
      rw [map_mul]
      rw [hb_lift i]
      -- Now: `(mk (algebraMap K A (c i))) * hb_basis i = (c i) • hb_basis i`.
      rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
      rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    -- **(c)** Define `r := a - a_lift`. Then `r ∈ I`.
    set r : A := a - a_lift with hr_def
    have hr_mem_I : r ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h_mk_a_lift, sub_self]
    -- **(d)** `r_{n₀} := (decompose 𝒜 r n₀ : A) ∈ 𝒜 n₀ ∩ I` and is homogeneous.
    set r_n : A := (DirectSum.decompose 𝒜 r n₀ : A) with hr_n_def
    have hr_n_mem : r_n ∈ 𝒜 n₀ := SetLike.coe_mem _
    have hr_n_in_I : r_n ∈ I :=
      (Submodule.IsHomogeneous.mem_iff 𝒜 hI_hom).mp hr_mem_I n₀
    -- **(e)** Apply `exists_homogeneous_decomposition_mem_span_range`.
    obtain ⟨s, hs_sum, hs_deg⟩ :=
      exists_homogeneous_decomposition_mem_span_range (𝒜 := 𝒜) (θ := θ) (degθ := n)
        hθ_deg hr_n_mem hr_n_in_I
    -- By IH, each `s j ∈ S`.
    have h_sj_mem : ∀ j : Fin d, s j ∈ S := by
      intro j
      by_cases hlt : n₀ < n j
      · -- `s j = 0`.
        have hsj_zero : s j = 0 := by
          have := hs_deg j
          rw [if_pos hlt] at this
          exact this
        rw [hsj_zero]
        exact Submodule.zero_mem _
      · push_neg at hlt
        -- `s j ∈ 𝒜 (n₀ - n j)` and `n₀ - n j < n₀` since `n j > 0`.
        have hsj_hom : s j ∈ 𝒜 (n₀ - n j) := by
          have := hs_deg j
          rw [if_neg (Nat.not_lt.mpr hlt)] at this
          exact this
        have hlt' : n₀ - n j < n₀ := by
          have hnj : 0 < n j := hn_pos j
          omega
        exact IH _ hlt' _ hsj_hom
    -- **(f)** `r_n = ∑ j, s j * θ j`, and `s j * θ j ∈ S`.
    have h_rn_mem_S : r_n ∈ S := by
      rw [hs_sum]
      refine Submodule.sum_mem _ ?_
      intro j _
      rw [mul_comm]
      exact h_θ_mul_mem j (h_sj_mem j)
    -- **(g)** The degree-`n₀` component of `a_lift` is
    -- `∑_{i : deg i = n₀} algebraMap K A (c i) * b i ∈ S`.
    set a_lift_n : A := (DirectSum.decompose 𝒜 a_lift n₀ : A) with ha_lift_n_def
    have h_a_lift_n_mem_S : a_lift_n ∈ S := by
      -- `a_lift = ∑ i, algebraMap K A (c i) * b i`, with `algebraMap K A (c i) ∈ 𝒜 0`
      -- and `b i ∈ 𝒜 (deg i)`, so `(algebraMap K A (c i)) * b i ∈ 𝒜 (deg i)`.
      -- Hence the degree-`n₀` component is the sum over `{i : deg i = n₀}` of those terms.
      have h_each_mem_0 : ∀ k : K, algebraMap K A k ∈ 𝒜 0 := by
        intro k
        rw [Algebra.algebraMap_eq_smul_one]
        exact (𝒜 0).smul_mem k SetLike.GradedOne.one_mem
      -- Decompose the sum: `decompose (∑ i, t i) n₀ = ∑ i, decompose (t i) n₀`.
      have h_sum : a_lift_n =
          ∑ i, (DirectSum.decompose 𝒜 (algebraMap K A (c i) * b i) n₀ : A) := by
        rw [ha_lift_n_def, ha_lift_def]
        rw [DirectSum.decompose_sum, DFinsupp.finset_sum_apply,
          AddSubmonoidClass.coe_finset_sum]
      rw [h_sum]
      refine Submodule.sum_mem _ ?_
      intro i _
      -- Each term: `decompose 𝒜 (algebraMap K A (c i) * b i) n₀`.
      -- Since `algebraMap K A (c i) ∈ 𝒜 0`, we have
      -- `decompose 𝒜 (algebraMap K A (c i) * b i) n₀ =
      --    algebraMap K A (c i) * decompose 𝒜 (b i) n₀`.
      rw [DirectSum.coe_decompose_mul_of_left_mem_zero 𝒜 (h_each_mem_0 (c i))]
      -- Now `decompose 𝒜 (b i) n₀`: since `b i ∈ 𝒜 (deg i)`, this is `b i` if
      -- `deg i = n₀` else `0`.
      by_cases hdi : deg i = n₀
      · have hbn : b i ∈ 𝒜 n₀ := hdi ▸ hb_deg i
        rw [DirectSum.decompose_of_mem_same 𝒜 hbn]
        exact h_kb_mem (c i) i
      · rw [DirectSum.decompose_of_mem_ne 𝒜 (hb_deg i) hdi]
        simp only [mul_zero]
        exact Submodule.zero_mem _
    -- **(h)** `a = a_lift_n + r_n`.
    have h_a_eq : a = a_lift_n + r_n := by
      -- `decompose 𝒜 a n₀ = a` (since `a ∈ 𝒜 n₀`).
      have ha_eq : (DirectSum.decompose 𝒜 a n₀ : A) = a :=
        DirectSum.decompose_of_mem_same 𝒜 ha
      -- `r = a - a_lift`, so `decompose 𝒜 r n₀ = decompose 𝒜 a n₀ - decompose 𝒜 a_lift n₀`.
      have h_r_decomp : (DirectSum.decompose 𝒜 r n₀ : A) =
          (DirectSum.decompose 𝒜 a n₀ : A) -
            (DirectSum.decompose 𝒜 a_lift n₀ : A) := by
        rw [hr_def]
        rw [show (DirectSum.decompose 𝒜 (a - a_lift)) =
            DirectSum.decompose 𝒜 a - DirectSum.decompose 𝒜 a_lift from
          (DirectSum.decomposeAddEquiv 𝒜).map_sub a a_lift]
        rfl
      -- `r_n = a - a_lift_n` hence `a = a_lift_n + r_n`.
      rw [hr_n_def, h_r_decomp, ha_eq]
      rw [← ha_lift_n_def]
      ring
    rw [h_a_eq]
    exact Submodule.add_mem _ h_a_lift_n_mem_S h_rn_mem_S

/-- Linear independence over `MvPolynomial (Fin 0) K` reduces to linear
independence over `K`, since `MvPolynomial (Fin 0) K ≃+* K`. Specialized
form of the `d = 0` base case of Step C. -/
theorem linearIndependent_aeval_fin_zero
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (θ : Fin 0 → A) {ι : Type u} (b : ι → A)
    (hb_li_K : LinearIndependent K b) :
    letI alg : Algebra (MvPolynomial (Fin 0) K) A :=
      (MvPolynomial.aeval θ).toAlgebra
    LinearIndependent (MvPolynomial (Fin 0) K) b := by
  letI alg : Algebra (MvPolynomial (Fin 0) K) A :=
    (MvPolynomial.aeval θ).toAlgebra
  -- Any `θ : Fin 0 → A` equals `isEmptyElim`, so `aeval θ` is determined.
  have hθ : θ = (isEmptyElim : Fin 0 → A) := Subsingleton.elim _ _
  -- Identify `r • a` (as `MvPolynomial`-smul) with `(isEmptyAlgEquiv K (Fin 0) r) • a`
  -- (as `K`-smul), using `aeval isEmptyElim = (Algebra.ofId K A).comp isEmptyAlgEquiv`.
  have hsmul : ∀ (r : MvPolynomial (Fin 0) K) (a : A),
      r • a = (MvPolynomial.isEmptyAlgEquiv K (Fin 0) r) • a := by
    intro r a
    change MvPolynomial.aeval θ r * a = _
    rw [hθ]
    have heq : (MvPolynomial.aeval (isEmptyElim : Fin 0 → A) :
          MvPolynomial (Fin 0) K →ₐ[K] A)
        = (Algebra.ofId K A).comp (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toAlgHom := by
      ext i
      exact isEmptyElim i
    have hval : (MvPolynomial.aeval (isEmptyElim : Fin 0 → A) : MvPolynomial (Fin 0) K → A) r
        = ((Algebra.ofId K A).comp
            (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toAlgHom) r := by
      rw [heq]
    rw [hval]
    rw [Algebra.smul_def]
    rfl
  -- Reduce `P`-linear independence to `K`-linear independence.
  rw [linearIndependent_iff'] at hb_li_K ⊢
  intro s g hsum i hi
  -- Rewrite each summand via `hsmul`.
  have hsum' : ∑ j ∈ s, (MvPolynomial.isEmptyAlgEquiv K (Fin 0) (g j)) • b j = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl ?_
    intro j _
    exact (hsmul (g j) (b j)).symm
  have hgi_K : MvPolynomial.isEmptyAlgEquiv K (Fin 0) (g i) = 0 :=
    hb_li_K s (fun j => MvPolynomial.isEmptyAlgEquiv K (Fin 0) (g j)) hsum' i hi
  -- Use the ring iso to conclude `g i = 0`.
  exact (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).injective
    (show MvPolynomial.isEmptyAlgEquiv K (Fin 0) (g i)
        = MvPolynomial.isEmptyAlgEquiv K (Fin 0) 0 by rw [hgi_K, map_zero])

/-- **Linear independence cons step.** If `x ∈ A` is `A`-regular, and `b : ι → A`
is such that the images of `b` in `A ⧸ ⟨x⟩` are `MvPolynomial (Fin n) K`-linearly
independent via `aeval` of `(θ' i mod ⟨x⟩)`, then `b` itself is
`MvPolynomial (Fin (n+1)) K`-linearly independent in `A` via `aeval` of
`(Fin.cons x θ')`. This is the cons step for Step C's induction. -/
theorem linearIndependent_aeval_cons_step
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    {n : ℕ} (x : A) (θ' : Fin n → A)
    (hx_reg : IsSMulRegular A x)
    {ι : Type u} (b : ι → A)
    (hb_IH : letI : Algebra (MvPolynomial (Fin n) K) (A ⧸ Ideal.span ({x} : Set A)) :=
        (MvPolynomial.aeval (fun i =>
          (Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (θ' i) :
            A ⧸ Ideal.span ({x} : Set A)))).toAlgebra
      LinearIndependent (MvPolynomial (Fin n) K)
        (fun i => (Ideal.Quotient.mk (Ideal.span ({x} : Set A)) (b i) :
          A ⧸ Ideal.span ({x} : Set A)))) :
    letI _alg : Algebra (MvPolynomial (Fin (n+1)) K) A :=
      (MvPolynomial.aeval (Fin.cons x θ')).toAlgebra
    LinearIndependent (MvPolynomial (Fin (n+1)) K) b := by
  classical
  -- Unpack names.
  set I : Ideal A := Ideal.span ({x} : Set A) with hI_def
  set mk : A →+* A ⧸ I := Ideal.Quotient.mk I with hmk_def
  -- Install the ambient algebra instances.
  letI algA : Algebra (MvPolynomial (Fin (n+1)) K) A :=
    (MvPolynomial.aeval (Fin.cons x θ')).toAlgebra
  letI algB : Algebra (MvPolynomial (Fin n) K) (A ⧸ I) :=
    (MvPolynomial.aeval (fun i => (mk (θ' i) : A ⧸ I))).toAlgebra
  -- The `algebraMap` for these instances is just `aeval ...`.
  have halg_eq_A : ∀ f : MvPolynomial (Fin (n+1)) K,
      algebraMap (MvPolynomial (Fin (n+1)) K) A f =
        MvPolynomial.aeval (Fin.cons x θ') f := fun _ => rfl
  have halg_eq_B : ∀ g : MvPolynomial (Fin n) K,
      algebraMap (MvPolynomial (Fin n) K) (A ⧸ I) g =
        MvPolynomial.aeval (fun i => (mk (θ' i) : A ⧸ I)) g := fun _ => rfl
  -- Factorization identity:
  --   aeval (Fin.cons x θ') = Polynomial.aeval x
  --       ∘ (Polynomial.mapRingHom (aeval θ'))
  --       ∘ finSuccEquiv.
  -- We package this into a ring-hom equation so we can rewrite.
  have hfactor : ∀ f : MvPolynomial (Fin (n+1)) K,
      MvPolynomial.aeval (Fin.cons x θ') f =
        Polynomial.aeval x
          ((Polynomial.mapRingHom
              ((MvPolynomial.aeval (R := K) (θ' : Fin n → A)).toRingHom))
            (MvPolynomial.finSuccEquiv K n f)) := by
    -- Use `algHom_ext` on `MvPolynomial (Fin (n+1)) K`.
    have heq :
        (MvPolynomial.aeval (Fin.cons x θ') :
            MvPolynomial (Fin (n+1)) K →ₐ[K] A) =
        (((Polynomial.aeval (x : A) : Polynomial A →ₐ[A] A).restrictScalars K).comp
          (((Polynomial.mapAlgHom
              (MvPolynomial.aeval (θ' : Fin n → A) :
                MvPolynomial (Fin n) K →ₐ[K] A)).restrictScalars K).comp
            ((MvPolynomial.finSuccEquiv K n).toAlgHom))) := by
      apply MvPolynomial.algHom_ext
      intro i
      refine Fin.cases ?_ ?_ i
      · -- i = 0 case: LHS = x, RHS = aeval x (mapRingHom (aeval θ') (finSuccEquiv (X 0)))
        --                         = aeval x (mapRingHom (aeval θ') Polynomial.X) = aeval x X = x
        simp [MvPolynomial.finSuccEquiv_X_zero]
      · intro k
        -- i = k.succ: LHS = θ' k, RHS = aeval x (mapRingHom (aeval θ') (C (X k)))
        --                             = aeval x (C (aeval θ' (X k))) = aeval θ' (X k) = θ' k
        simp [MvPolynomial.finSuccEquiv_X_succ,
          MvPolynomial.aeval_X]
    intro f
    have := AlgHom.congr_fun heq f
    simpa [AlgHom.comp_apply, Polynomial.coe_mapRingHom] using this
  -- Reduction mod x via `comp_aeval_apply`. For `f : P`, `mk (aeval (Fin.cons x θ') f)`
  -- equals `aeval (Fin.cons 0 (mk ∘ θ')) f` in `A/I`, which further equals
  -- `aeval (mk ∘ θ') ((finSuccEquiv K n f).coeff 0)` because the 0-th variable is 0.
  -- We actually only need a weaker form: mod x kills everything but the X^0 coefficient.
  have hmod :
      ∀ f : MvPolynomial (Fin (n+1)) K,
        mk (MvPolynomial.aeval (Fin.cons x θ') f) =
          MvPolynomial.aeval (fun i => (mk (θ' i) : A ⧸ I))
            ((MvPolynomial.finSuccEquiv K n f).coeff 0) := by
    intro f
    -- Rewrite LHS via `hfactor`, then via `Polynomial.aeval`.
    rw [hfactor f]
    -- `mk (Polynomial.aeval x P') = ...`. Use `Polynomial.aeval_def` to unfold to eval₂.
    -- We'll compute both sides on a polynomial by induction.
    set P' := (Polynomial.mapRingHom
      ((MvPolynomial.aeval (R := K) (θ' : Fin n → A)).toRingHom))
      (MvPolynomial.finSuccEquiv K n f) with hP'_def
    -- `mk (Polynomial.aeval x P') = Polynomial.aeval (mk x) (Polynomial.map mk P')`.
    have hstep1 : mk (Polynomial.aeval x P') =
        Polynomial.aeval (mk x) (P'.map mk) := by
      rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map,
        Polynomial.hom_eval₂]
      congr 1
    rw [hstep1]
    -- `mk x = 0` because `x ∈ I`.
    have hmkx : mk x = 0 := by
      rw [hmk_def, hI_def]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hmkx]
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero]
    -- Now `(P'.map mk).coeff 0 = mk (P'.coeff 0)`.
    rw [Polynomial.coeff_map]
    -- `P'.coeff 0 = aeval θ' ((finSuccEquiv K n f).coeff 0)`.
    have hP'_coeff : P'.coeff 0 =
        MvPolynomial.aeval (θ' : Fin n → A) ((MvPolynomial.finSuccEquiv K n f).coeff 0) := by
      rw [hP'_def]
      exact Polynomial.coeff_map _ 0
    rw [hP'_coeff]
    -- `mk (aeval θ' g) = aeval (mk ∘ θ') g` via `comp_aeval_apply`.
    -- We use `Ideal.Quotient.mkₐ K I` as the `K`-algebra map lifting `mk`.
    have hmk_apply : ∀ a : A, mk a = (Ideal.Quotient.mkₐ K I) a := fun _ => rfl
    rw [hmk_apply]
    rw [MvPolynomial.comp_aeval_apply]
    rfl
  -- Scalar-action identity on `A`.
  have hsmulA : ∀ (f : MvPolynomial (Fin (n+1)) K) (a : A),
      f • a = MvPolynomial.aeval (Fin.cons x θ') f * a := fun f a => Algebra.smul_def f a
  -- Scalar-action identity on `A ⧸ I`.
  have hsmulB : ∀ (g : MvPolynomial (Fin n) K) (c : A ⧸ I),
      g • c = MvPolynomial.aeval (fun i => (mk (θ' i) : A ⧸ I)) g * c :=
    fun g c => Algebra.smul_def g c
  -- **Degree-bounded claim**: for any `N`, any finite `s : Finset ι`, any
  -- `g : ι → MvPolynomial (Fin (n+1)) K` with `(finSuccEquiv K n (g i)).natDegree ≤ N`
  -- for all `i ∈ s`, if `∑ i ∈ s, g i • b i = 0` then `g i = 0` for all `i ∈ s`.
  have key : ∀ (N : ℕ) (s : Finset ι) (g : ι → MvPolynomial (Fin (n+1)) K)
      (_hdeg : ∀ i ∈ s, (MvPolynomial.finSuccEquiv K n (g i)).natDegree ≤ N)
      (_hsum : ∑ i ∈ s, g i • b i = 0),
      ∀ i ∈ s, g i = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N IH =>
      intro s g hdeg hsum i hi
      -- Reduce hsum mod x. `mk (∑ i ∈ s, g i • b i) = 0`.
      have hsum_mod : ∑ i ∈ s,
          (MvPolynomial.finSuccEquiv K n (g i)).coeff 0 • (mk (b i) : A ⧸ I) = 0 := by
        have hmkzero : mk (∑ i ∈ s, g i • b i) = 0 := by rw [hsum]; exact map_zero _
        rw [map_sum] at hmkzero
        -- each summand: mk (g i • b i) = mk (aeval (Fin.cons x θ') (g i) * b i)
        --             = mk (aeval...) * mk (b i)
        --             = aeval (mk ∘ θ') ((finSuccEquiv g i).coeff 0) * mk (b i)
        --             = (finSuccEquiv g i).coeff 0 • mk (b i).
        convert hmkzero using 1
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hsmulA, map_mul, hmod]
        rw [hsmulB]
      -- Apply `hb_IH`.
      have hIH := hb_IH
      rw [linearIndependent_iff'] at hIH
      have hcoeff0_zero : ∀ j ∈ s, (MvPolynomial.finSuccEquiv K n (g j)).coeff 0 = 0 := by
        intro j hj
        exact hIH s (fun j => (MvPolynomial.finSuccEquiv K n (g j)).coeff 0) hsum_mod j hj
      -- So each finSuccEquiv (g j) has zero constant coefficient, hence is divisible by X.
      -- In fact (finSuccEquiv (g j)) = X * F_j with F_j = divX (finSuccEquiv (g j)).
      -- Its natDegree ≤ N-1.
      by_cases hN : N = 0
      · -- Base case: degree 0. Then finSuccEquiv (g i) is a constant equal to its coeff 0,
        -- which is 0. Hence g i = 0.
        subst hN
        have hdeg_i : (MvPolynomial.finSuccEquiv K n (g i)).natDegree ≤ 0 := hdeg i hi
        have hdeg_i' : (MvPolynomial.finSuccEquiv K n (g i)).natDegree = 0 :=
          Nat.le_zero.mp hdeg_i
        -- A polynomial of natDegree 0 equals C of its coeff 0.
        have hconst : MvPolynomial.finSuccEquiv K n (g i) =
            Polynomial.C ((MvPolynomial.finSuccEquiv K n (g i)).coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hdeg_i'
        rw [hcoeff0_zero i hi, map_zero] at hconst
        have : MvPolynomial.finSuccEquiv K n (g i) = 0 := hconst
        have : g i = 0 := by
          have := (MvPolynomial.finSuccEquiv K n).injective
            (show MvPolynomial.finSuccEquiv K n (g i) =
              MvPolynomial.finSuccEquiv K n 0 by rw [this, map_zero])
          exact this
        exact this
      · -- Inductive case. Define g' : ι → P so that g i = X_0 * g' i.
        --   finSuccEquiv (g' i) = divX (finSuccEquiv (g i)).
        -- This requires g' i = (finSuccEquiv)⁻¹ (divX (finSuccEquiv (g i))).
        let g' : ι → MvPolynomial (Fin (n+1)) K := fun j =>
          (MvPolynomial.finSuccEquiv K n).symm ((MvPolynomial.finSuccEquiv K n (g j)).divX)
        -- Relation: g i = X 0 * g' i on s.
        have hg_eq : ∀ j ∈ s, g j = MvPolynomial.X (0 : Fin (n+1)) * g' j := by
          intro j hj
          have hcoeff0j := hcoeff0_zero j hj
          -- finSuccEquiv (g j) = X * divX (finSuccEquiv (g j)) because coeff 0 = 0.
          have hXmul : MvPolynomial.finSuccEquiv K n (g j) =
              Polynomial.X * (MvPolynomial.finSuccEquiv K n (g j)).divX := by
            have : Polynomial.X *
                (MvPolynomial.finSuccEquiv K n (g j)).divX +
                Polynomial.C ((MvPolynomial.finSuccEquiv K n (g j)).coeff 0) =
                MvPolynomial.finSuccEquiv K n (g j) := Polynomial.X_mul_divX_add _
            rw [hcoeff0j, map_zero, add_zero] at this
            exact this.symm
          -- Apply (finSuccEquiv).symm.
          apply (MvPolynomial.finSuccEquiv K n).injective
          rw [map_mul, AlgEquiv.apply_symm_apply, MvPolynomial.finSuccEquiv_X_zero]
          exact hXmul
        -- New sum: 0 = ∑ g i • b i = ∑ (X 0 * g' i) • b i = X_0 • (∑ g' i • b i).
        -- Under the scalar action, `X 0 • a = x * a`.
        have hsum' : x * (∑ j ∈ s, g' j • b j) = 0 := by
          have hXA : (MvPolynomial.X (R := K) (0 : Fin (n+1))) •
              (∑ j ∈ s, g' j • b j) = 0 := by
            rw [Finset.smul_sum]
            calc ∑ j ∈ s, (MvPolynomial.X (R := K) (0 : Fin (n+1))) • g' j • b j
                = ∑ j ∈ s, (MvPolynomial.X (R := K) (0 : Fin (n+1)) * g' j) • b j := by
                  refine Finset.sum_congr rfl ?_
                  intro j _
                  rw [mul_smul]
              _ = ∑ j ∈ s, g j • b j := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  rw [hg_eq j hj]
              _ = 0 := hsum
          -- Interpret X_0 • a = x * a.
          have hX0 : MvPolynomial.aeval (Fin.cons x θ')
              (MvPolynomial.X (R := K) (0 : Fin (n+1))) = x := by
            simp
          rw [hsmulA] at hXA
          rw [hX0] at hXA
          exact hXA
        -- Regularity: strip x.
        have hsum'' : ∑ j ∈ s, g' j • b j = 0 := by
          have : x • (∑ j ∈ s, g' j • b j) = x • (0 : A) := by
            rw [smul_eq_mul, hsum', smul_zero]
          exact hx_reg this
        -- Degree bound: (finSuccEquiv (g' j)).natDegree ≤ N-1 < N.
        have hdeg' : ∀ j ∈ s,
            (MvPolynomial.finSuccEquiv K n (g' j)).natDegree ≤ N - 1 := by
          intro j hj
          simp only [g', AlgEquiv.apply_symm_apply]
          rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
          exact Nat.sub_le_sub_right (hdeg j hj) 1
        -- Apply IH at N-1.
        have hNpred_lt : N - 1 < N := Nat.sub_lt (Nat.pos_of_ne_zero hN) Nat.one_pos
        have hIH_apply : ∀ j ∈ s, g' j = 0 := IH (N - 1) hNpred_lt s g' hdeg' hsum''
        -- Conclude g i = X 0 * g' i = X 0 * 0 = 0.
        rw [hg_eq i hi, hIH_apply i hi, mul_zero]
  -- Apply `key` with sufficiently large `N`.
  rw [linearIndependent_iff']
  intro s g hsum i hi
  -- Choose N := max of natDegrees (or 0 if empty).
  let N : ℕ := s.sup fun j => (MvPolynomial.finSuccEquiv K n (g j)).natDegree
  have hdeg : ∀ j ∈ s, (MvPolynomial.finSuccEquiv K n (g j)).natDegree ≤ N := by
    intro j hj
    exact Finset.le_sup (f := fun j => (MvPolynomial.finSuccEquiv K n (g j)).natDegree) hj
  exact key N s g hdeg hsum i hi

/-! ### Linear independence for a homogeneous basis lift (combined induction)

Combines the base case `linearIndependent_aeval_fin_zero` with the cons step
`linearIndependent_aeval_cons_step` into a full inductive statement. -/

/-- Auxiliary: `Ideal.ofList (List.ofFn θ) = Ideal.span (Set.range θ)`. -/
private lemma ofList_ofFn_eq_span_range
    {A : Type*} [CommRing A] {d : ℕ} (θ : Fin d → A) :
    Ideal.ofList (List.ofFn θ) = Ideal.span (Set.range θ) := by
  unfold Ideal.ofList
  congr 1
  ext a
  exact List.mem_ofFn' θ a

/-- Auxiliary: for `θ : Fin 0 → A`, `Ideal.ofList (List.ofFn θ) = ⊥`. -/
private lemma ofList_ofFn_fin_zero_eq_bot
    {A : Type*} [CommRing A] (θ : Fin 0 → A) :
    Ideal.ofList (List.ofFn θ) = (⊥ : Ideal A) := by
  have hlist : (List.ofFn θ : List A) = [] := by simp [List.ofFn_zero]
  rw [hlist]; exact Ideal.ofList_nil

/-- Auxiliary for the inductive step: `Ideal.ofList (List.ofFn θ) =
    Ideal.span {θ 0} ⊔ Ideal.ofList (List.ofFn (θ ∘ Fin.succ))` when `d = n + 1`. -/
private lemma ofList_ofFn_succ
    {A : Type*} [CommRing A] {n : ℕ} (θ : Fin (n + 1) → A) :
    Ideal.ofList (List.ofFn θ) =
      Ideal.span ({θ 0} : Set A) ⊔ Ideal.ofList (List.ofFn (fun i => θ i.succ)) := by
  have hθcons : θ = Fin.cons (θ 0) (fun i => θ i.succ) := by
    ext i; refine Fin.cases ?_ ?_ i
    · simp
    · intro k; simp
  conv_lhs => rw [hθcons]
  rw [List.ofFn_cons]
  exact Ideal.ofList_cons (θ 0) _

open scoped Pointwise

/-- Full linear-independence statement: given `θ : Fin d → A` a weakly regular
sequence in `A` and `b : ι → A` lifting a K-basis of
`A ⧸ Ideal.ofList (List.ofFn θ)`, `b` is `MvPolynomial (Fin d) K`-linearly
independent in `A` via `MvPolynomial.aeval θ`. Proved by induction on `d`. -/
theorem linearIndependent_aeval_of_basis_lift :
    ∀ (d : ℕ) {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
      (θ : Fin d → A)
      (_hθ_reg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn θ))
      {ι : Type u} (b : ι → A)
      (hb_basis : Module.Basis ι K (A ⧸ Ideal.ofList (List.ofFn θ)))
      (_hb_lift : ∀ i,
        (Ideal.Quotient.mk (Ideal.ofList (List.ofFn θ)) (b i) :
          A ⧸ Ideal.ofList (List.ofFn θ)) = hb_basis i),
      letI _alg : Algebra (MvPolynomial (Fin d) K) A :=
        (MvPolynomial.aeval θ).toAlgebra
      LinearIndependent (MvPolynomial (Fin d) K) b
  | 0, K, A, _, _, _, _, θ, _hθ_reg, ι, b, hb_basis, hb_lift => by
      -- `A ⧸ Ideal.ofList (List.ofFn θ) ≃ₐ[K] A` since the ideal is `⊥`.
      have hbot : Ideal.ofList (List.ofFn θ) = (⊥ : Ideal A) :=
        ofList_ofFn_fin_zero_eq_bot θ
      -- Build a K-basis of `A` from `hb_basis` by transport.
      let e : (A ⧸ Ideal.ofList (List.ofFn θ)) ≃ₐ[K] A :=
        (Ideal.quotientEquivAlgOfEq K hbot).trans (AlgEquiv.quotientBot K A)
      let bK : Module.Basis ι K A := hb_basis.map e.toLinearEquiv
      -- Identify `bK i = b i`.
      have hbK_eq : ∀ i, bK i = b i := by
        intro i
        simp only [bK, Module.Basis.map_apply]
        rw [← hb_lift i]
        change e (Ideal.Quotient.mk (Ideal.ofList (List.ofFn θ)) (b i)) = b i
        -- `e` is the composition of `quotientEquivAlgOfEq K hbot` and `AlgEquiv.quotientBot K A`.
        -- Both act by lifting representative elements.
        change (AlgEquiv.quotientBot K A)
            ((Ideal.quotientEquivAlgOfEq K hbot)
              (Ideal.Quotient.mk (Ideal.ofList (List.ofFn θ)) (b i))) = b i
        simp [Ideal.quotientEquivAlgOfEq, AlgEquiv.quotientBot,
          Ideal.quotientEquivAlg]
      -- `b` is K-linearly independent because it equals `bK`.
      have hb_li_K : LinearIndependent K b := by
        have : b = bK := by funext i; exact (hbK_eq i).symm
        rw [this]
        exact bK.linearIndependent
      exact linearIndependent_aeval_fin_zero θ b hb_li_K
  | n + 1, K, A, _, _, _, _, θ, hθ_reg, ι, b, hb_basis, hb_lift => by
      classical
      -- Split θ = Fin.cons (θ 0) θ'.
      set x : A := θ 0 with hx_def
      set θ' : Fin n → A := fun i => θ i.succ with hθ'_def
      -- θ decomposes as Fin.cons x θ'.
      have hθ_cons : θ = Fin.cons x θ' := by
        ext i; refine Fin.cases ?_ ?_ i
        · simp [x]
        · intro k; simp [θ']
      -- `List.ofFn θ = x :: List.ofFn θ'`.
      have hlist_cons : List.ofFn θ = x :: List.ofFn θ' := by
        rw [hθ_cons, List.ofFn_cons]
      -- From the weak regular-sequence hypothesis, extract:
      -- * `hx_reg : IsSMulRegular A x`
      -- * `hθ'_reg_Q : IsWeaklyRegular (QuotSMulTop x A) (map (Q.mk ⟨x⟩) (List.ofFn θ'))`.
      rw [hlist_cons] at hθ_reg
      obtain ⟨hx_reg, hθ'_reg_Q⟩ :=
        (RingTheory.Sequence.isWeaklyRegular_cons_iff' _ x (List.ofFn θ')).mp hθ_reg
      -- Work in `B := A ⧸ Ideal.span {x}`. Split on whether `B` is nontrivial.
      set I0 : Ideal A := Ideal.span ({x} : Set A) with hI0_def
      by_cases htriv : Subsingleton (A ⧸ I0)
      · -- `A ⧸ I0` is trivial (i.e. `I0 = ⊤`, x is a unit).
        -- Then `A ⧸ Ideal.ofList (List.ofFn θ)` is also trivial, forcing ι empty.
        have hI0_top : I0 = (⊤ : Ideal A) :=
          Ideal.Quotient.subsingleton_iff.mp htriv
        have hAoL_top : Ideal.ofList (List.ofFn θ) = (⊤ : Ideal A) := by
          rw [hlist_cons, Ideal.ofList_cons]
          apply le_antisymm le_top
          calc (⊤ : Ideal A) = I0 := hI0_top.symm
            _ ≤ _ := le_sup_left
        haveI : Subsingleton (A ⧸ Ideal.ofList (List.ofFn θ)) :=
          Ideal.Quotient.subsingleton_iff.mpr hAoL_top
        -- In a trivial module, any basis forces its index to be empty.
        haveI hιEmp : IsEmpty ι := by
          by_contra h
          rw [not_isEmpty_iff] at h
          obtain ⟨i⟩ := h
          exact hb_basis.ne_zero i (Subsingleton.elim _ _)
        -- Empty index → vacuously linearly independent.
        letI algA : Algebra (MvPolynomial (Fin (n + 1)) K) A :=
          (MvPolynomial.aeval θ).toAlgebra
        exact linearIndependent_empty_type
      · haveI hBne : Nontrivial (A ⧸ I0) := not_subsingleton_iff_nontrivial.mp htriv
        -- Translate `hθ'_reg_Q` from `QuotSMulTop x A` to `A ⧸ I0`.
        -- `QuotSMulTop x A = A ⧸ (x • ⊤ : Submodule A A)`; we need the submodule equality
        -- `x • ⊤ = (I0 : Submodule A A)`.
        have hsubmod_eq : x • (⊤ : Submodule A A) = (I0 : Submodule A A) := by
          ext z
          refine ⟨fun hz => ?_, fun hz => ?_⟩
          · rw [Submodule.mem_smul_pointwise_iff_exists] at hz
            obtain ⟨w, _, rfl⟩ := hz
            change x • w ∈ I0
            have hmul : x • w = x * w := rfl
            rw [hmul, hI0_def]
            exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
          · rw [hI0_def, Ideal.mem_span_singleton] at hz
            obtain ⟨c, rfl⟩ := hz
            rw [Submodule.mem_smul_pointwise_iff_exists]
            exact ⟨c, Submodule.mem_top, rfl⟩
        -- The A-linear equiv between `QuotSMulTop x A` and `A ⧸ I0`.
        let eQL : QuotSMulTop x A ≃ₗ[A] (A ⧸ I0) :=
          Submodule.quotEquivOfEq _ _ hsubmod_eq
        -- Translate weak regularity following the pattern from GradedRegularSop.lean.
        have hθ'_reg_B :
            RingTheory.Sequence.IsWeaklyRegular (A ⧸ I0)
              ((List.ofFn θ').map (Ideal.Quotient.mk I0)) := by
          -- Step 1: strip the `algebraMap` in `hθ'_reg_Q` to regularity as A-module.
          have step1 : RingTheory.Sequence.IsWeaklyRegular (QuotSMulTop x A)
              (List.ofFn θ') := by
            -- `Q.mk (span {x}) = algebraMap A (A ⧸ I0)`, so by `isWeaklyRegular_map_algebraMap_iff`
            -- we can strip the map. But the hypothesis mentions `span {x}`, and
            -- `I0 = span {x}` by `rfl`.
            have hq_eq_am :
                (Ideal.Quotient.mk (Ideal.span ({x} : Set A)) :
                  A →+* A ⧸ Ideal.span ({x} : Set A)) =
                algebraMap A (A ⧸ Ideal.span ({x} : Set A)) := rfl
            -- Reinterpret hθ'_reg_Q with algebraMap.
            rw [hq_eq_am] at hθ'_reg_Q
            exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
              (R := A) (S := A ⧸ Ideal.span ({x} : Set A)) (M := QuotSMulTop x A)
              (List.ofFn θ')).mp hθ'_reg_Q
          -- Step 2: transfer via eQL to get IsWeaklyRegular (A ⧸ I0) (List.ofFn θ') as A-module.
          have step2 : RingTheory.Sequence.IsWeaklyRegular (A ⧸ I0) (List.ofFn θ') := by
            rwa [LinearEquiv.isWeaklyRegular_congr eQL] at step1
          -- Step 3: re-map via algebraMap = Q.mk.
          have step3 := (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff
              (R := A) (S := A ⧸ I0) (M := A ⧸ I0) (List.ofFn θ')).mpr step2
          -- `algebraMap A (A ⧸ I0) = Q.mk I0` definitionally.
          exact step3
        -- Rewrite list as `List.ofFn`.
        have hmap_ofFn : (List.ofFn θ').map (Ideal.Quotient.mk I0) =
            List.ofFn (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0)) := by
          rw [List.map_ofFn]; rfl
        rw [hmap_ofFn] at hθ'_reg_B
        -- Identify `A ⧸ Ideal.ofList (List.ofFn θ)` with
        -- `(A ⧸ I0) ⧸ Ideal.ofList (List.ofFn (Q.mk I0 ∘ θ'))`.
        have hsup_eq :
            I0 ⊔ Ideal.ofList (List.ofFn θ') = Ideal.ofList (List.ofFn θ) := by
          rw [hlist_cons, Ideal.ofList_cons]
        have hmap_ofList :
            Ideal.ofList (List.ofFn (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0))) =
              (Ideal.ofList (List.ofFn θ')).map (Ideal.Quotient.mk I0) := by
          rw [show Ideal.ofList (List.ofFn θ') = Ideal.span (Set.range θ') from
                ofList_ofFn_eq_span_range θ']
          rw [show Ideal.ofList (List.ofFn (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0)))
                = Ideal.span (Set.range (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0))) from
              ofList_ofFn_eq_span_range _]
          rw [Ideal.map_span]
          congr 1
          ext y
          simp only [Set.mem_range, Set.mem_image]
          constructor
          · rintro ⟨i, rfl⟩; exact ⟨θ' i, ⟨i, rfl⟩, rfl⟩
          · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
        -- The ring equivalence `(A ⧸ I0) ⧸ ofList(Q.mk θ') ≃+* A ⧸ ofList(θ)`.
        let eBI : ((A ⧸ I0) ⧸
            Ideal.ofList (List.ofFn
              (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0)))) ≃+*
              (A ⧸ Ideal.ofList (List.ofFn θ)) :=
          (Ideal.quotEquivOfEq hmap_ofList).trans
            ((DoubleQuot.quotQuotEquivQuotSup I0 (Ideal.ofList (List.ofFn θ'))).trans
              (Ideal.quotEquivOfEq hsup_eq))
        -- The ring equiv `eBI` is actually K-linear because both sides are K-algebras
        -- and all three constituents are K-algebra maps (they're all identity on
        -- representatives). Build the linear equiv directly via `AlgEquiv` composition.
        let eBI_A : ((A ⧸ I0) ⧸
            Ideal.ofList (List.ofFn
              (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0)))) ≃ₐ[K]
              (A ⧸ Ideal.ofList (List.ofFn θ)) :=
          (Ideal.quotientEquivAlgOfEq K hmap_ofList).trans
            ((DoubleQuot.quotQuotEquivQuotSupₐ K I0 (Ideal.ofList (List.ofFn θ'))).trans
              (Ideal.quotientEquivAlgOfEq K hsup_eq))
        let eBI_L : ((A ⧸ I0) ⧸
            Ideal.ofList (List.ofFn
              (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0)))) ≃ₗ[K]
              (A ⧸ Ideal.ofList (List.ofFn θ)) := eBI_A.toLinearEquiv
        -- Define `bB : ι → A ⧸ I0`.
        let bB : ι → A ⧸ I0 := fun i => (Ideal.Quotient.mk I0 (b i) : A ⧸ I0)
        -- Basis on the double-quotient side.
        let hb_basis_DQ : Module.Basis ι K
            ((A ⧸ I0) ⧸ Ideal.ofList (List.ofFn
              (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0)))) :=
          hb_basis.map eBI_L.symm
        -- Lift hypothesis transfers.
        have hbB_lift : ∀ i,
            (Ideal.Quotient.mk
              (Ideal.ofList (List.ofFn (fun j => (Ideal.Quotient.mk I0 (θ' j) : A ⧸ I0))))
              (bB i) : _) = hb_basis_DQ i := by
          intro i
          -- hb_basis_DQ i = eBI_L.symm (hb_basis i).
          simp only [hb_basis_DQ, Module.Basis.map_apply]
          apply eBI_L.injective
          rw [LinearEquiv.apply_symm_apply]
          -- Goal: eBI_L (Q.mk _ (bB i)) = hb_basis i.
          -- eBI_L is the three-fold composition; on representatives it's identity.
          have hrewrite :
              eBI_L (Ideal.Quotient.mk
                (Ideal.ofList (List.ofFn
                  (fun j => (Ideal.Quotient.mk I0 (θ' j) : A ⧸ I0)))) (bB i)) =
              Ideal.Quotient.mk (Ideal.ofList (List.ofFn θ)) (b i) := by
            -- bB i = Q.mk I0 (b i). eBI_L through DoubleQuot acts as identity on representatives.
            change eBI_A (Ideal.Quotient.mk _ (bB i)) = _
            simp only [bB, eBI_A, AlgEquiv.trans_apply,
              Ideal.quotientEquivAlgOfEq,
              DoubleQuot.quotQuotEquivQuotSupₐ]
            rfl
          rw [hrewrite]
          exact hb_lift i
        -- Recursive call for `d = n` on `A ⧸ I0`.
        have hb_IH : letI algB : Algebra (MvPolynomial (Fin n) K) (A ⧸ I0) :=
              (MvPolynomial.aeval
                (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0))).toAlgebra
            LinearIndependent (MvPolynomial (Fin n) K) bB :=
          linearIndependent_aeval_of_basis_lift n
            (fun i => (Ideal.Quotient.mk I0 (θ' i) : A ⧸ I0))
            hθ'_reg_B bB hb_basis_DQ hbB_lift
        -- Apply the cons step.
        have hfinal := linearIndependent_aeval_cons_step
          (K := K) (A := A) (n := n) x θ' hx_reg b hb_IH
        -- `hfinal` uses `aeval (Fin.cons x θ')`; we want `aeval θ`.
        -- Since `θ = Fin.cons x θ'`, they're equal.
        have halg_eq :
            (MvPolynomial.aeval (Fin.cons x θ') :
              MvPolynomial (Fin (n + 1)) K →ₐ[K] A) =
            MvPolynomial.aeval θ := by rw [← hθ_cons]
        -- The `letI` algebra instances agree; we need `LinearIndependent` for the
        -- θ-algebra. Since the two algebra instances agree as algebras, smul agrees.
        letI algθ : Algebra (MvPolynomial (Fin (n + 1)) K) A :=
          (MvPolynomial.aeval θ).toAlgebra
        convert hfinal using 2
        · rw [hθ_cons]

section StepC

open MvPolynomial GradedIrrelevant

variable {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]

/-- **Step C.** Given a homogeneous regular sop `θ : Fin d → A` in `𝒜₊` of a
connected ℕ-graded Noetherian `K`-algebra with `A ⧸ Ideal.ofList (List.ofFn θ)`
finite over `K`, the algebra `A` becomes a finite-free `MvPolynomial (Fin d) K`-
module via `T_i ↦ θ_i`.

The output packages the algebra instance, finiteness and freeness so the
caller can install them with `letI` / `haveI`. -/
theorem finiteFree_over_mvPolynomial_of_homogeneous_regular_sop
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (_h𝒜₀ : ConnectedGraded 𝒜)
    {d : ℕ} (θ : Fin d → A)
    (_hθ_hom : ∀ i, SetLike.IsHomogeneousElem 𝒜 (θ i))
    (_hθ_irr : ∀ i, θ i ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (_hθ_reg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn θ))
    (hA_fin : Module.Finite K (A ⧸ Ideal.ofList (List.ofFn θ))) :
    letI _alg : Algebra (MvPolynomial (Fin d) K) A :=
      (MvPolynomial.aeval θ).toAlgebra
    Module.Finite (MvPolynomial (Fin d) K) A ∧
    Module.Free (MvPolynomial (Fin d) K) A := by
  -- **STRATEGY:** Induction on `d`. Base case `d = 0` reduces to `Module.Finite K A`
  -- (immediate from `hA_fin` and `Ideal.ofList [] = ⊥`) plus `Module.Free K A` (free
  -- over a field). Inductive step uses `MvPolynomial.finSuccEquiv` and a regular-NZD
  -- quotient lift.
  --
  -- The crucial lift lemma ("finite free modulo regular ⟹ finite free over polynomial
  -- ring") is not in Mathlib and requires a graded/filtered Nakayama argument of
  -- ~100-200 LOC; documented as the remaining gap.
  letI alg : Algebra (MvPolynomial (Fin d) K) A :=
    (MvPolynomial.aeval θ).toAlgebra
  -- Fast handle on the base case.
  induction d with
  | zero =>
    -- `θ : Fin 0 → A` is the empty function; `List.ofFn θ = []`.
    have hlist : (List.ofFn (θ : Fin 0 → A)) = [] := by
      simp [List.ofFn_zero]
    -- `Ideal.ofList [] = ⊥`, so `A ⧸ ⊥ ≃ₐ[K] A`, and `Module.Finite K A`.
    have hbot : Ideal.ofList (List.ofFn θ) = (⊥ : Ideal A) := by
      rw [hlist]; exact Ideal.ofList_nil
    let e : (A ⧸ Ideal.ofList (List.ofFn θ)) ≃ₐ[K] A :=
      (Ideal.quotientEquivAlgOfEq K hbot).trans (AlgEquiv.quotientBot K A)
    haveI hFinKA : Module.Finite K A := Module.Finite.equiv e.toLinearEquiv
    -- `A` is a K-vector space, hence `Module.Free K A`.
    haveI hFreeKA : Module.Free K A := Module.Free.of_divisionRing K A
    -- Identify the algebra `MvPolynomial (Fin 0) K ≃ₐ[K] K` to transfer structures.
    -- Under the installed algebra `(aeval θ).toAlgebra`, for `f : MvPolynomial (Fin 0) K`
    -- we have `algebraMap P A f = aeval θ f = algebraMap K A (coeff 0 f)`.
    --
    -- In particular `algebraMap P A ∘ C = algebraMap K A`, which is the scalar-tower
    -- compatibility condition.
    have hST_algMap : (algebraMap (MvPolynomial (Fin 0) K) A).comp
        (algebraMap K (MvPolynomial (Fin 0) K)) = algebraMap K A := by
      ext k
      change aeval θ (algebraMap K (MvPolynomial (Fin 0) K) k) = algebraMap K A k
      rw [MvPolynomial.algebraMap_eq, MvPolynomial.aeval_C]
    haveI hST : IsScalarTower K (MvPolynomial (Fin 0) K) A :=
      IsScalarTower.of_algebraMap_eq' hST_algMap.symm
    -- `Module.Finite P A` follows from `Module.Finite K A` by scalar restriction.
    haveI hFinPA : Module.Finite (MvPolynomial (Fin 0) K) A :=
      Module.Finite.of_restrictScalars_finite K (MvPolynomial (Fin 0) K) A
    -- For freeness: use `Module.Finite.of_equiv_equiv`-style pattern with ring iso
    -- `P ≃+* K` from `isEmptyAlgEquiv`.
    refine ⟨hFinPA, ?_⟩
    -- **Freeness strategy.** We show `Module.Free P A` by exhibiting a basis.
    -- The ring iso `eRE : P ≃+* K` lets us transfer scalars. Define the submodule
    -- `Submodule.restrictScalars K (⊤ : Submodule P A) = ⊤`; the K-basis of A gives
    -- a generating set and linearly independent family over P.
    --
    -- Cleaner: use the fact that `Module.Free P A` ⟺ exists a basis. A K-basis of A
    -- doubles as a P-basis once we notice `r • a = eRE r • a` (scalar action via
    -- ring iso).
    classical
    -- Choose a K-basis of A.
    let bK := Module.Free.chooseBasis K A
    let ιA := Module.Free.ChooseBasisIndex K A
    -- The ring iso.
    let eRE : MvPolynomial (Fin 0) K ≃+* K := MvPolynomial.isEmptyRingEquiv K (Fin 0)
    -- For `r : P`, `a : A`, `r • a = algebraMap P A r * a = aeval θ r * a`.
    -- For `k : K`, `k • a = algebraMap K A k * a`.
    -- And `aeval θ r = algebraMap K A (eRE r)` because `aeval θ = (ofId K A).comp
    -- (isEmptyAlgEquiv K (Fin 0))`.
    have hsmul : ∀ (r : MvPolynomial (Fin 0) K) (a : A), r • a = (eRE r) • a := by
      intro r a
      rw [Algebra.smul_def, Algebra.smul_def]
      congr 1
      change MvPolynomial.aeval θ r = algebraMap K A (eRE r)
      have hfact : (MvPolynomial.aeval θ : MvPolynomial (Fin 0) K →ₐ[K] A) =
          (Algebra.ofId K A).comp (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toAlgHom := by
        ext i; exact isEmptyElim i
      have hr : (MvPolynomial.aeval θ : MvPolynomial (Fin 0) K →ₐ[K] A) r =
          (Algebra.ofId K A).comp (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toAlgHom r := by
        rw [hfact]
      simpa [Algebra.ofId_apply, AlgHom.comp_apply, eRE,
        MvPolynomial.isEmptyRingEquiv] using hr
    -- Build `Basis ιA P A` using `Basis.ofRepr` with explicit `LinearEquiv`.
    -- The repr map takes `a : A` to `(bK.repr a).mapRange eRE.symm` : `ιA →₀ P`.
    -- For this to be P-linear, scalar action on the target must match.
    -- We build the LinearEquiv manually.
    -- Scalar action on `ιA →₀ P`: coordinatewise by multiplication.
    let repr_fun : A → (ιA →₀ MvPolynomial (Fin 0) K) :=
      fun a => (bK.repr a).mapRange (fun k => (eRE.symm k : MvPolynomial (Fin 0) K))
        (by simp)
    let repr_inv : (ιA →₀ MvPolynomial (Fin 0) K) → A :=
      fun f => bK.repr.symm (f.mapRange (fun p => eRE p) (by simp))
    -- Additive structure.
    have repr_fun_add : ∀ a b : A, repr_fun (a + b) = repr_fun a + repr_fun b := by
      intro a b; ext i
      simp [repr_fun, Finsupp.mapRange_apply, bK.repr.map_add]
    have repr_fun_smul :
        ∀ (r : MvPolynomial (Fin 0) K) (a : A),
          repr_fun (r • a) = r • repr_fun a := by
      intro r a
      apply Finsupp.ext
      intro i
      rw [hsmul r a]
      simp only [repr_fun, Finsupp.mapRange_apply, bK.repr.map_smul, Finsupp.coe_smul,
        Pi.smul_apply]
      -- `eRE.symm (eRE r • (bK.repr a) i) = r • (eRE.symm ((bK.repr a) i))` — P-linear.
      -- Here `eRE r • (bK.repr a) i` in K means `eRE r * (bK.repr a) i`.
      -- RHS `r • eRE.symm ((bK.repr a) i)` = `r * eRE.symm ((bK.repr a) i)` in P.
      change eRE.symm (eRE r • (bK.repr a) i) = r • (eRE.symm ((bK.repr a) i))
      rw [smul_eq_mul, smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
    have repr_fun_invFun : ∀ f : (ιA →₀ MvPolynomial (Fin 0) K),
        repr_fun (repr_inv f) = f := by
      intro f
      apply Finsupp.ext
      intro i
      simp only [repr_fun, repr_inv, LinearEquiv.apply_symm_apply,
        Finsupp.mapRange_apply]
      exact RingEquiv.symm_apply_apply eRE (f i)
    have repr_fun_funInv : ∀ a : A, repr_inv (repr_fun a) = a := by
      intro a
      simp only [repr_fun, repr_inv]
      have hmap :
          ((bK.repr a).mapRange (fun k => (eRE.symm k : MvPolynomial (Fin 0) K))
            (by simp)).mapRange (fun p => eRE p) (by simp) = bK.repr a := by
        apply Finsupp.ext
        intro i
        simp only [Finsupp.mapRange_apply]
        exact RingEquiv.apply_symm_apply eRE _
      rw [hmap, LinearEquiv.symm_apply_apply]
    let repr_LE : A ≃ₗ[MvPolynomial (Fin 0) K] (ιA →₀ MvPolynomial (Fin 0) K) :=
      { toFun := repr_fun
        map_add' := repr_fun_add
        map_smul' := by
          intro r a
          simpa [RingHom.id_apply] using repr_fun_smul r a
        invFun := repr_inv
        left_inv := repr_fun_funInv
        right_inv := repr_fun_invFun }
    exact Module.Free.of_basis (⟨repr_LE⟩ : Module.Basis ιA (MvPolynomial (Fin 0) K) A)
  | succ d' _ih =>
    classical
    -- Extract homogeneous degrees for θ, then redefine to be positive by bumping to 1
    -- whenever `θ i = 0` (which is the only case that forces the original degree to be 0,
    -- via irrelevance).
    choose degθ_raw hθ_mem_raw using _hθ_hom
    let degθ : Fin (d' + 1) → ℕ :=
      fun i => if θ i = 0 then 1 else degθ_raw i
    have hθ_mem : ∀ i, θ i ∈ 𝒜 (degθ i) := by
      intro i
      by_cases hzero : θ i = 0
      · simp only [degθ, if_pos hzero, hzero, Submodule.zero_mem]
      · simp only [degθ, if_neg hzero]; exact hθ_mem_raw i
    have hdegθ_pos : ∀ i, 0 < degθ i := by
      intro i
      by_cases hzero : θ i = 0
      · simp [degθ, hzero]
      · simp only [degθ, if_neg hzero]
        -- `degθ_raw i ≠ 0` from irrelevance + `θ i ∈ 𝒜 (degθ_raw i)` + `θ i ≠ 0`.
        by_contra hne
        push_neg at hne
        -- `hne : degθ_raw i ≤ 0`, i.e. `degθ_raw i = 0`.
        have hzer : degθ_raw i = 0 := Nat.le_zero.mp hne
        have hmem0 : θ i ∈ 𝒜 0 := hzer ▸ hθ_mem_raw i
        have hproj : GradedRing.projZeroRingHom 𝒜 (θ i) = θ i :=
          DirectSum.decompose_of_mem_same 𝒜 hmem0
        have hirr := _hθ_irr i
        -- `irrelevant.toIdeal = ker projZero`, so `θ i ∈ irrelevant.toIdeal ↔ projZero (θ i) = 0`.
        rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker] at hirr
        rw [hirr] at hproj
        exact hzero hproj.symm
    -- **Build I and its homogeneous structure.** We use the `span` form directly
    -- so we can reuse the surjectivity theorem's API without a bridge.
    set I : Ideal A := Ideal.span (Set.range θ) with hI_def
    have hI_hom : I.IsHomogeneous 𝒜 := by
      rw [hI_def]
      apply Ideal.homogeneous_span
      rintro _ ⟨i, rfl⟩
      exact ⟨degθ i, hθ_mem i⟩
    haveI hGrQ : GradedRing (GradedQuotient.gradedQuotientPiece 𝒜 I) :=
      GradedQuotient.gradedRing 𝒜 I hI_hom
    -- To apply `exists_homogeneous_basis_of_finite_graded`, we need
    -- `Module.Finite K (A ⧸ I)`. This follows from `hA_fin` (which is over `A ⧸ ofList`)
    -- via the iso `A ⧸ I ≃ₐ[K] A ⧸ Ideal.ofList (List.ofFn θ)`.
    have hofL_eq_I : Ideal.ofList (List.ofFn θ) = I := by
      rw [hI_def]; exact ofList_ofFn_eq_span_range θ
    let eq_span_ofL : (A ⧸ Ideal.ofList (List.ofFn θ)) ≃ₐ[K] (A ⧸ I) :=
      Ideal.quotientEquivAlgOfEq K hofL_eq_I
    haveI hfinI : Module.Finite K (A ⧸ I) :=
      Module.Finite.equiv eq_span_ofL.toLinearEquiv
    -- **Homogeneous K-basis of A ⧸ I.**
    obtain ⟨ι, fintypeι, degB, bbar, hbbar_mem⟩ :=
      exists_homogeneous_basis_of_finite_graded (K := K) (A := A ⧸ I)
        (GradedQuotient.gradedQuotientPiece 𝒜 I)
    -- **Lift each bbar i to a homogeneous element of A.**
    have hbbar_lift_ex : ∀ i, ∃ x : A, x ∈ 𝒜 (degB i) ∧
        Ideal.Quotient.mk I x = (bbar i : A ⧸ I) := by
      intro i
      have hmem := hbbar_mem i
      simp only [GradedQuotient.gradedQuotientPiece, Submodule.mem_map] at hmem
      obtain ⟨x, hx, hxeq⟩ := hmem
      refine ⟨x, hx, ?_⟩
      exact hxeq
    choose b hb_deg hb_lift using hbbar_lift_ex
    -- **Apply surjectivity (Step C sub-step B).**
    have hspan := span_aeval_eq_top_of_homogeneous_basis_lift (K := K) (A := A)
      𝒜 θ degθ hθ_mem hdegθ_pos degB b hb_deg bbar hb_lift
    -- **For linear independence, transport `bbar` to a basis on `A ⧸ Ideal.ofList`.**
    let bbar_ofL : Module.Basis ι K (A ⧸ Ideal.ofList (List.ofFn θ)) :=
      bbar.map eq_span_ofL.symm.toLinearEquiv
    have hb_lift_ofL : ∀ i, (Ideal.Quotient.mk (Ideal.ofList (List.ofFn θ)) (b i) :
          A ⧸ Ideal.ofList (List.ofFn θ)) = bbar_ofL i := by
      intro i
      simp only [bbar_ofL, Module.Basis.map_apply]
      -- `bbar_ofL i = (eq_span_ofL.symm.toLinearEquiv) (bbar i)`
      --          = `eq_span_ofL.symm (bbar i)` as AlgEquiv.
      -- `eq_span_ofL` takes class of `a` to class of `a`. So `eq_span_ofL.symm`
      -- also takes class of `a` to class of `a`.
      rw [← hb_lift i]
      -- Goal: Q.mk ofL (b i) = eq_span_ofL.symm.toLinearEquiv (Q.mk I (b i)).
      -- Both sides are the class of `b i` in the respective quotients, which are
      -- equal via quotientEquivAlgOfEq.
      rfl
    -- **Apply linear independence (Task A).**
    have hli := linearIndependent_aeval_of_basis_lift (d' + 1)
      θ _hθ_reg b bbar_ofL hb_lift_ofL
    -- **Package as a basis.**
    letI algθ : Algebra (MvPolynomial (Fin (d' + 1)) K) A :=
      (MvPolynomial.aeval θ).toAlgebra
    let basis : Module.Basis ι (MvPolynomial (Fin (d' + 1)) K) A :=
      Module.Basis.mk hli (le_of_eq hspan.symm)
    -- **Conclude.**
    refine ⟨?_, Module.Free.of_basis basis⟩
    exact Module.Finite.of_basis basis

end StepC

end GradedFiniteFree

end

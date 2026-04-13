/-
This file proves the forward CM transfer and CM localization theorem.

Key upstream reference: mathlib PR #28599 (Nailin Guan).
The approach uses Ext vanishing via the covariant long exact sequence
as a technical tool, connecting back to the regular-sequence-based
`ringDepth` from Defs.lean.

The long-term goal is to delete this file once the relevant CM localization
infrastructure is available upstream in Mathlib.
-/

import toMathlib.CohenMacaulay.Basic
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.Depth
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Filtration

/-!
# Cohen-Macaulay Localization

## Main results

- `isCohenMacaulayLocalRing_quotient`: Forward CM transfer.
- `isCohenMacaulayLocalRing_localization_atPrime`: CM localizes.
- `IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`: Global CM from local CM.

## Strategy

The forward CM transfer requires showing `depth(R/(x)) ≥ dim(R) - 1`.
The proof uses the covariant long exact Ext sequence for `0 → M → M → M/xM → 0`
applied to modules over R. The key technical lemma shows that the induced map
on `Ext^n(k, M)` is zero when `x ∈ m`, making the LES degenerate into short
exact sequences. The Rees theorem connecting Ext vanishing with regular
sequences is proved for arbitrary modules, then specialized to `M = R`.
-/

noncomputable section

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian
open scoped Pointwise

universe u

/-! ### Module category abbreviations -/

section Abbrevs

variable (R : Type u) [CommRing R]

/-- The residue field as a module category object. -/
private abbrev k_ [IsLocalRing R] : ModuleCat.{u} R := ModuleCat.of R (R ⧸ maximalIdeal R)
/-- The ring as a module category object. -/
private abbrev R_ : ModuleCat.{u} R := ModuleCat.of R R

end Abbrevs

/-! ### Ext vanishing: the scalar zero lemma -/

section ExtVanishing

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{u} R]

/-- Scalar multiplication by `x ∈ maximalIdeal R` on `Ext(k, M, n)` is zero
for any module `M`. The proof uses the first-argument action: `x ∈ m` kills
`k = R/m`, so `mk₀(x • 𝟙_k) = 0`, hence `x • α = 0`. -/
lemma ext_smul_eq_zero_of_mem_maximalIdeal (M : ModuleCat.{u} R)
    {x : R} (hx : x ∈ maximalIdeal R) {n : ℕ} (α : Ext (k_ R) M n) :
    x • α = 0 := by
  have h1 : x • α = (Ext.mk₀ (x • 𝟙 (k_ R))).comp α (zero_add n) := by
    rw [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]
  have h2 : x • (𝟙 (k_ R)) = 0 := by
    ext
    simp
    show (Ideal.Quotient.mk (maximalIdeal R) x) * 1 = 0
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
  rw [h1, h2, Ext.mk₀_zero, Ext.zero_comp]

/-- The postcomposition map on `Ext(k, M, n)` induced by `S.f = x • 𝟙_M` is
zero when `x ∈ m`, for `S = smulShortComplex M x`. -/
lemma ext_postcomp_smulShortComplex_f_zero (M : ModuleCat.{u} R)
    {x : R} (hx : x ∈ maximalIdeal R) {n : ℕ} (α : Ext (k_ R) M n) :
    α.comp (Ext.mk₀ (ModuleCat.smulShortComplex M x).f) (add_zero n) = 0 := by
  have hf : (ModuleCat.smulShortComplex M x).f = x • (𝟙 M) := by
    ext; simp [ModuleCat.smulShortComplex]
  rw [hf, Ext.mk₀_smul, Ext.comp_smul, Ext.comp_mk₀_id,
    ext_smul_eq_zero_of_mem_maximalIdeal M hx]

end ExtVanishing

/-! ### Degenerate LES: surjectivity of δ and vanishing transfer -/

section DegenerateLES

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{u} R]

/-- When `x ∈ m` is `M`-regular, the connecting map `δ` in the covariant Ext
LES for `0 → M →^x M → M/xM → 0` is surjective. -/
lemma ext_connecting_surjective (M : ModuleCat.{u} R)
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁)
    (γ : Ext (k_ R) M n₁) :
    ∃ β : Ext (k_ R) (ModuleCat.smulShortComplex M x).X₃ n₀,
      β.comp (hreg.smulShortComplex_shortExact).extClass hn = γ := by
  exact Ext.covariant_sequence_exact₁ (k_ R) hreg.smulShortComplex_shortExact γ
    (ext_postcomp_smulShortComplex_f_zero M hx γ) hn

/-- **Vanishing transfer via δ**: if `Ext^n(k, M/xM)` is subsingleton and δ is
surjective, then `Ext^{n+1}(k, M)` is subsingleton. -/
lemma ext_subsingleton_succ_of_quotient_subsingleton (M : ModuleCat.{u} R)
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) {n : ℕ}
    (hq : Subsingleton (Ext (k_ R) (ModuleCat.smulShortComplex M x).X₃ n)) :
    Subsingleton (Ext (k_ R) M (n + 1)) := by
  constructor; intro a b
  obtain ⟨a', ha'⟩ := ext_connecting_surjective M hx hreg rfl a
  obtain ⟨b', hb'⟩ := ext_connecting_surjective M hx hreg rfl b
  rw [← ha', ← hb', hq.elim a' b']

/-- **Vanishing transfer via g***: if `Ext^n(k, M)` and `Ext^{n+1}(k, M)` are
both subsingleton, then `Ext^n(k, M/xM)` is subsingleton. -/
lemma ext_quotient_subsingleton_of_subsingleton (M : ModuleCat.{u} R)
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) {n : ℕ}
    (hM : Subsingleton (Ext (k_ R) M n))
    (hM' : Subsingleton (Ext (k_ R) M (n + 1))) :
    Subsingleton (Ext (k_ R) (ModuleCat.smulShortComplex M x).X₃ n) := by
  set S := ModuleCat.smulShortComplex M x
  set hS := hreg.smulShortComplex_shortExact
  constructor; intro a b
  have ha_δ : a.comp hS.extClass rfl = 0 := hM'.elim _ _
  have hb_δ : b.comp hS.extClass rfl = 0 := hM'.elim _ _
  obtain ⟨ca, hca⟩ := Ext.covariant_sequence_exact₃ (k_ R) hS a rfl ha_δ
  obtain ⟨cb, hcb⟩ := Ext.covariant_sequence_exact₃ (k_ R) hS b rfl hb_δ
  rw [← hca, ← hcb, hM.elim ca cb]

end DegenerateLES

/-! ### Ext^0 vanishing ↔ regular element -/

section ExtZero

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- If `x ∈ m` is `M`-regular, then `Ext^0(k, M) = 0`. -/
lemma ext_zero_subsingleton_of_smulRegular (M : ModuleCat.{u} R)
    [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x) :
    Subsingleton (Ext (k_ R) M 0) := by
  rw [show Subsingleton (Ext (k_ R) M 0) ↔ Subsingleton ((k_ R) ⟶ M) from
    (Ext.addEquiv₀ (C := ModuleCat.{u} R)).toEquiv.subsingleton_congr]
  constructor; intro f g
  have : f.hom = g.hom := by
    have hss : Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] M) := by
      rw [IsSMulRegular.subsingleton_linearMap_iff]
      exact ⟨x, by
        rw [Module.mem_annihilator]; intro q
        induction q using Quotient.inductionOn' with
        | h r =>
          show (Ideal.Quotient.mk (maximalIdeal R) x) * (Ideal.Quotient.mk _ r) = 0
          simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      , hreg⟩
    exact hss.elim f.hom g.hom
  exact ModuleCat.Hom.ext this

/-- If there exists a regular element in `m`, then `Ext^0(k, R)` vanishes. -/
lemma ext_zero_subsingleton_of_exists_regular
    (h : ∃ x ∈ maximalIdeal R, IsSMulRegular R x) :
    Subsingleton (Ext (k_ R) (R_ R) 0) := by
  obtain ⟨x, hx, hreg⟩ := h
  exact ext_zero_subsingleton_of_smulRegular (R_ R) hx hreg

/-- If `Ext^0(k, R)` vanishes, then there exists a regular element in `m`. -/
lemma exists_regular_of_ext_zero_subsingleton
    (h : Subsingleton (Ext (k_ R) (R_ R) 0)) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular R x := by
  have hss_hom : Subsingleton ((k_ R) ⟶ (R_ R)) :=
    ((Ext.addEquiv₀ (C := ModuleCat.{u} R)).toEquiv.subsingleton_congr).mp h
  have hss : Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] R) := by
    constructor; intro f g
    have := hss_hom.elim (ModuleCat.ofHom f) (ModuleCat.ofHom g)
    exact congrArg ModuleCat.Hom.hom this
  rw [IsSMulRegular.subsingleton_linearMap_iff] at hss
  obtain ⟨r, hr, hreg⟩ := hss
  refine ⟨r, ?_, hreg⟩
  rw [Module.mem_annihilator] at hr
  rw [mem_maximalIdeal]
  intro hu
  have h1 := hr (Ideal.Quotient.mk (maximalIdeal R) 1)
  change (Ideal.Quotient.mk _ r) * (Ideal.Quotient.mk _ 1) = 0 at h1
  simp only [mul_one, map_one, mul_one] at h1
  rw [Ideal.Quotient.eq_zero_iff_mem] at h1
  exact (mem_maximalIdeal _).mp h1 hu

end ExtZero

/-! ### Rees theorem: Ext vanishing from regular sequences (Direction 1) -/

section ReesDirection1

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- **Direction 1 of Rees (module version)**: If `rs` is a weakly regular sequence
on the module `M` with all elements in `m`, then `Ext^i(k, M) = 0` for `i < |rs|`. -/
theorem ext_subsingleton_of_weaklyRegular_module
    (M : ModuleCat.{u} R) [Module.Finite R M]
    {rs : List R} (hreg : IsWeaklyRegular M rs) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {i : ℕ} (hi : i < rs.length) :
    Subsingleton (Ext (k_ R) M i) := by
  induction rs generalizing M i with
  | nil => exact absurd hi (by simp)
  | cons x xs ih =>
    have hx_reg : IsSMulRegular M x := ((isWeaklyRegular_cons_iff M x xs).mp hreg).1
    have hx_mem : x ∈ maximalIdeal R := hmem x (List.mem_cons.mpr (Or.inl rfl))
    have hxs_reg : IsWeaklyRegular (QuotSMulTop x M) xs :=
      ((isWeaklyRegular_cons_iff M x xs).mp hreg).2
    have hxs_mem : ∀ r ∈ xs, r ∈ maximalIdeal R :=
      fun r hr => hmem r (List.mem_cons.mpr (Or.inr hr))
    simp only [List.length_cons] at hi
    by_cases hi0 : i = 0
    · subst hi0; exact ext_zero_subsingleton_of_smulRegular M hx_mem hx_reg
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hj : j < xs.length := by omega
      have hQ : Subsingleton (Ext (k_ R)
          (ModuleCat.smulShortComplex M x).X₃ j) := by
        change Subsingleton (Ext (k_ R) (ModuleCat.of R (QuotSMulTop x ↑M)) j)
        exact ih (ModuleCat.of R (QuotSMulTop x ↑M)) hxs_reg hxs_mem hj
      exact ext_subsingleton_succ_of_quotient_subsingleton M hx_mem hx_reg hQ

/-- **Direction 1 of Rees (ring version)**: -/
theorem ext_subsingleton_of_weaklyRegular
    {rs : List R} (hreg : IsWeaklyRegular R rs) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    {i : ℕ} (hi : i < rs.length) :
    Subsingleton (Ext (k_ R) (R_ R) i) :=
  ext_subsingleton_of_weaklyRegular_module (R_ R) hreg hmem hi

end ReesDirection1

/-! ### Rees theorem: regular sequences from Ext vanishing (Direction 2) -/

section ReesDirection2

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- **Direction 2 of Rees (module version)**: -/
theorem exists_weaklyRegular_module_of_ext_subsingleton
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (d : ℕ) (hvan : ∀ i, i < d → Subsingleton (Ext (k_ R) M i)) :
    ∃ rs : List R, rs.length = d ∧ IsWeaklyRegular M rs ∧
      ∀ r ∈ rs, r ∈ maximalIdeal R := by
  induction d generalizing M with
  | zero => exact ⟨[], rfl, IsWeaklyRegular.nil R _, fun _ h => nomatch h⟩
  | succ d ih =>
    have hss0 := hvan 0 (Nat.zero_lt_succ d)
    have hss_hom : Subsingleton ((k_ R) ⟶ M) :=
      ((Ext.addEquiv₀ (C := ModuleCat.{u} R)).toEquiv.subsingleton_congr).mp hss0
    have hss_lm : Subsingleton ((R ⧸ maximalIdeal R) →ₗ[R] M) := by
      constructor; intro f g
      exact congrArg ModuleCat.Hom.hom (hss_hom.elim (ModuleCat.ofHom f) (ModuleCat.ofHom g))
    rw [IsSMulRegular.subsingleton_linearMap_iff] at hss_lm
    obtain ⟨x, hx_ann, hx_reg⟩ := hss_lm
    have hx_mem : x ∈ maximalIdeal R := by
      rw [Module.mem_annihilator] at hx_ann
      rw [mem_maximalIdeal]; intro hu
      have h1 := hx_ann (Ideal.Quotient.mk (maximalIdeal R) 1)
      change (Ideal.Quotient.mk _ x) * (Ideal.Quotient.mk _ 1) = 0 at h1
      simp only [mul_one, map_one, mul_one] at h1
      rw [Ideal.Quotient.eq_zero_iff_mem] at h1
      exact (mem_maximalIdeal _).mp h1 hu
    set Q := (ModuleCat.smulShortComplex M x).X₃
    have hvan_Q : ∀ i, i < d → Subsingleton (Ext (k_ R) Q i) := by
      intro i hi
      exact ext_quotient_subsingleton_of_subsingleton M hx_mem hx_reg
        (hvan i (by omega)) (hvan (i + 1) (by omega))
    have : Module.Finite R Q := Module.Finite.quotient _ _
    obtain ⟨xs, hlen, hxs_reg, hxs_mem⟩ := ih Q hvan_Q
    refine ⟨x :: xs, by simp [hlen], ?_, ?_⟩
    · rw [isWeaklyRegular_cons_iff]
      exact ⟨hx_reg, by convert hxs_reg⟩
    · intro r hr
      cases List.mem_cons.mp hr with
      | inl h => exact h ▸ hx_mem
      | inr h => exact hxs_mem r h

/-- **Direction 2 of Rees (ring version)**: -/
theorem exists_weaklyRegular_of_ext_subsingleton
    (d : ℕ) (hvan : ∀ i, i < d → Subsingleton (Ext (k_ R) (R_ R) i)) :
    ∃ rs : List R, rs.length = d ∧ IsWeaklyRegular R rs ∧
      ∀ r ∈ rs, r ∈ maximalIdeal R :=
  exists_weaklyRegular_module_of_ext_subsingleton (R_ R) d hvan

end ReesDirection2

/-! ### Hard depth inequality -/

section HardDepth

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- **Hard depth inequality**: `ringDepth R ≤ ringDepth(R/(x)) + 1`. -/
theorem ringDepth_le_succ_ringDepth_quotSMulTop
    {x : R} (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    ringDepth R ≤
      @ringDepth (QuotSMulTop x R) _ (quotSMulTopLocalRing hx) + 1 := by
  haveI := quotSMulTopLocalRing hx
  apply sSup_le
  rintro n ⟨rs, rfl, hreg, hmem⟩
  rcases rs with _ | ⟨r, rs'⟩
  · simp
  · have hext_R : ∀ i, i < (r :: rs').length →
        Subsingleton (Ext (k_ R) (R_ R) i) :=
      fun i hi => ext_subsingleton_of_weaklyRegular hreg hmem hi
    set Q := (ModuleCat.smulShortComplex (R_ R) x).X₃
    have hext_Q : ∀ i, i < rs'.length →
        Subsingleton (Ext (k_ R) Q i) := by
      intro i hi
      exact ext_quotient_subsingleton_of_subsingleton (R_ R) hx reg
        (hext_R i (by simp; omega)) (hext_R (i + 1) (by simp; omega))
    have hfin : Module.Finite R Q := Module.Finite.quotient _ _
    obtain ⟨ss, hlen, hss_reg, hss_mem⟩ :=
      exists_weaklyRegular_module_of_ext_subsingleton Q rs'.length hext_Q
    set ss' := ss.map (algebraMap R (QuotSMulTop x R))
    have hss'_reg : IsWeaklyRegular (QuotSMulTop x R) ss' :=
      (isWeaklyRegular_map_algebraMap_iff (QuotSMulTop x R) (QuotSMulTop x R) ss).mpr
        (by convert hss_reg)
    have hss'_mem : ∀ s ∈ ss', s ∈ maximalIdeal (QuotSMulTop x R) := by
      intro s hs
      obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hs
      have : IsLocalHom (algebraMap R (QuotSMulTop x R)) :=
        Ideal.Quotient.mk_surjective.isLocalHom
      exact map_nonunit (algebraMap R (QuotSMulTop x R)) r' (hss_mem r' hr')
    have hlen' : ss'.length = rs'.length := by simp [ss', hlen]
    have hdepth_lb : (rs'.length : ℕ∞) ≤ ringDepth (QuotSMulTop x R) := by
      rw [← hlen']
      exact ringDepth_le_of_isWeaklyRegular (QuotSMulTop x R) hss'_reg hss'_mem
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    gcongr

end HardDepth

/-! ### Forward CM transfer -/

section ForwardTransfer

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- **Forward CM transfer**: CM `R` + `x` regular → CM `R/(x)`. -/
theorem isCohenMacaulayLocalRing_quotient [IsCohenMacaulayLocalRing R]
    {x : R} (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    haveI := quotSMulTopLocalRing hx
    IsCohenMacaulayLocalRing (QuotSMulTop x R) := by
  haveI := quotSMulTopLocalRing hx
  have hhard := ringDepth_le_succ_ringDepth_quotSMulTop reg hx
  have heasy := ringDepth_quotSMulTop_succ_le reg hx
  have hdepth_eq : @ringDepth (QuotSMulTop x R) _ (quotSMulTopLocalRing hx) + 1 =
      ringDepth R := le_antisymm heasy hhard
  have hdim_eq := ringKrullDim_quotSMulTop_succ_eq_ringKrullDim reg hx
  have hCM := IsCohenMacaulayLocalRing.depth_eq_dim (R := R)
  have heq : ringKrullDim (QuotSMulTop x R) + 1 =
      ↑(ringDepth (QuotSMulTop x R)) + 1 := by
    calc ringKrullDim (QuotSMulTop x R) + 1
        = ringKrullDim R := hdim_eq
      _ = ↑(ringDepth R) := hCM
      _ = ↑(ringDepth (QuotSMulTop x R) + 1) := by rw [hdepth_eq]
      _ = ↑(ringDepth (QuotSMulTop x R)) + ↑(1 : ℕ∞) := by push_cast; ring
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp
    (ringKrullDim_ne_bot (R := QuotSMulTop x R))
  obtain ⟨b, hb⟩ : ∃ b : ℕ∞, (↑(ringDepth (QuotSMulTop x R)) : WithBot ℕ∞) = ↑b :=
    ⟨_, rfl⟩
  rw [← ha] at heq; rw [hb] at heq
  have hab : a = b := by
    have h1 : (↑(a + 1) : WithBot ℕ∞) = ↑(b + 1) := by push_cast; exact heq
    have h2 : a + 1 = b + 1 := WithBot.coe_injective h1
    cases a with
    | top =>
      simp only [top_add] at h2
      cases b with | top => rfl | coe m => exact absurd h2.symm WithTop.coe_ne_top
    | coe n =>
      cases b with
      | top => simp only [top_add] at h2; exact absurd h2 WithTop.coe_ne_top
      | coe m => norm_cast at h2 ⊢; omega
  exact { depth_eq_dim := by rw [ha.symm, hb, hab] }

end ForwardTransfer

/-! ### Unmixedness for CM local rings -/

section Unmixedness

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- Auxiliary: `x` regular implies `ann(x·s) ⊇ I → ann(s) ⊇ I`. -/
private lemma colon_singleton_dvd_of_isSMulRegular {x s : R} (hreg : IsSMulRegular R x)
    {I : Ideal R} (h : I ≤ (⊥ : Submodule R R).colon ({x * s} : Set R)) :
    I ≤ (⊥ : Submodule R R).colon ({s} : Set R) := by
  intro a ha
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at *
  have h1 : a * (x * s) = 0 := by
    have := h ha; rwa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at this
  have h2 : x * (a * s) = 0 := by linear_combination h1
  exact hreg (show x * (a * s) = x * 0 from by rwa [mul_zero])

/-- Helper for unmixedness: the statement parameterized by a dimension bound. -/
private lemma unmixedness_of_dim_le (d : ℕ) :
    ∀ (S : Type u) [inst1 : CommRing S] [inst2 : IsLocalRing S] [inst3 : IsNoetherianRing S]
      [inst4 : Small.{u} S] [inst5 : IsCohenMacaulayLocalRing S],
      (IsLocalRing.maximalIdeal S).primeHeight ≤ d →
      associatedPrimes S S ⊆ minimalPrimes S := by
  induction d with
  | zero =>
    intro S _ _ _ _ _ hd q hq
    haveI : q.IsPrime := (show IsAssociatedPrime q S from hq).isPrime
    rw [← Ideal.primeHeight_eq_zero_iff]
    exact nonpos_iff_eq_zero.mp
      ((Ideal.primeHeight_mono (IsLocalRing.le_maximalIdeal
        (Ideal.IsPrime.ne_top ‹_›))).trans hd)
  | succ d ih =>
    intro S _ _ _ _ _ hd q hq
    haveI : q.IsPrime := (show IsAssociatedPrime q S from hq).isPrime
    rw [← Ideal.primeHeight_eq_zero_iff]
    by_contra hht
    -- q ∈ Ass(S) with primeHeight(q) ≥ 1
    have hq_pos : (0 : ℕ∞) < q.primeHeight := by rwa [pos_iff_ne_zero]
    -- primeHeight(m) ≥ primeHeight(q) ≥ 1
    have hm_pos : (0 : ℕ∞) < (maximalIdeal S).primeHeight := lt_of_lt_of_le hq_pos
      (Ideal.primeHeight_mono (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›)))
    -- depth ≠ 0 (from CM + dim ≥ 1)
    have hCM := IsCohenMacaulayLocalRing.depth_eq_dim (R := S)
    have hdepth_ne : ringDepth S ≠ 0 := by
      intro h; rw [h] at hCM
      have : (maximalIdeal S).primeHeight = 0 := by
        rw [← IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim] at hCM
        exact_mod_cast hCM
      exact ne_of_gt hm_pos this
    -- Extract a nonempty regular sequence from depth ≠ 0
    have ⟨rs, hrs_ne, hreg_rs, hmem_rs⟩ :
        ∃ rs : List S, rs ≠ [] ∧ IsWeaklyRegular S rs ∧
          ∀ r ∈ rs, r ∈ maximalIdeal S := by
      rw [ringDepth, ne_eq, ENat.sSup_eq_zero] at hdepth_ne
      push_neg at hdepth_ne
      obtain ⟨n, ⟨rs, hlen, hreg, hmem⟩, hn⟩ := hdepth_ne
      exact ⟨rs, fun h => by simp [h] at hlen; exact hn hlen.symm, hreg, hmem⟩
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hrs_ne
    have hxm : x ∈ maximalIdeal S := hmem_rs x (List.mem_cons.mpr (Or.inl rfl))
    have hxreg : IsSMulRegular S x :=
      ((isWeaklyRegular_cons_iff S x xs).mp hreg_rs).1
    -- x ∉ q (regular elements avoid associated primes)
    have hxq : x ∉ q := by
      intro hxq
      have : x ∈ ⋃ p ∈ associatedPrimes S S, (p : Set S) := Set.mem_biUnion hq hxq
      rw [biUnion_associatedPrimes_eq_compl_regular S S] at this; exact this hxreg
    -- R/(x) is CM
    haveI := quotSMulTopLocalRing hxm
    haveI : IsCohenMacaulayLocalRing (QuotSMulTop x S) :=
      isCohenMacaulayLocalRing_quotient hxreg hxm
    -- dim(R/(x)) ≤ d (from dim(R) ≤ d+1 and dim drops)
    have hd_quot : (maximalIdeal (QuotSMulTop x S)).primeHeight ≤ d := by
      have hdim := ringKrullDim_quotSMulTop_succ_eq_ringKrullDim hxreg hxm
      have hR := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := S)
      have hQ := IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim (R := QuotSMulTop x S)
      -- dim(Q) + 1 = dim(S) ≤ ↑(d+1) in WithBot ℕ∞
      have hle_Q1 : ringKrullDim (QuotSMulTop x S) + 1 ≤ ↑((d : ℕ∞) + 1) := by
        rw [hdim, ← hR]; exact_mod_cast hd
      -- Extract dim(Q) = ↑a for some a : ℕ∞, then a ≠ ⊤, then a = ↑n
      obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp
        (ringKrullDim_ne_bot (R := QuotSMulTop x S))
      rw [← ha] at hle_Q1 hQ
      have ha_le : a + 1 ≤ (d : ℕ∞) + 1 := by exact_mod_cast hle_Q1
      have ha_fin : a ≠ ⊤ := by
        intro h; rw [h, top_add] at ha_le
        exact (WithTop.add_ne_top.mpr ⟨WithTop.coe_ne_top, WithTop.one_ne_top⟩)
          (le_antisymm le_top ha_le)
      obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.mp ha_fin
      have : n ≤ d := by
        have h1 : (↑(n + 1) : ℕ∞) ≤ ↑(d + 1) := by push_cast; exact ha_le
        exact Nat.le_of_succ_le_succ (by exact_mod_cast h1)
      -- pH(m_Q) = n (from hQ), so pH(m_Q) ≤ d
      calc (maximalIdeal (QuotSMulTop x S)).primeHeight
          = ↑n := by exact_mod_cast hQ
        _ ≤ ↑d := by exact_mod_cast this
    -- By IH: Ass(R/(x)) ⊆ Min(R/(x))
    have ih_quot := ih (QuotSMulTop x S) hd_quot
    set Q := QuotSMulTop x S
    -- (a) From q ∈ Ass(S): get r ≠ 0 with q = ann(r)
    obtain ⟨r, hr_ann⟩ := (show IsAssociatedPrime q S from hq).2
    have hr_ne : r ≠ 0 := by
      intro h; rw [h] at hr_ann; simp [Submodule.colon_singleton_zero] at hr_ann
      exact (Ideal.IsPrime.ne_top ‹_›) hr_ann
    -- (b) Find s ≠ 0 with ann(s) ⊇ q and s ∉ x • ⊤ (= Ideal.span {x})
    -- By contradiction: if all such s are in (x), then r ∈ (x)^n for all n,
    -- contradicting Krull's intersection theorem.
    have hne_top : Ideal.span ({x} : Set S) ≠ ⊤ := by
      intro h; rw [Ideal.span_singleton_eq_top] at h
      exact (IsLocalRing.mem_maximalIdeal _).mp hxm h
    -- smul_top ↔ span in the argument for Krull
    have hxt_eq : (x • ⊤ : Submodule S S) = Ideal.span ({x} : Set S) := by
      ext r; constructor
      · rintro ⟨s, -, rfl⟩; exact Ideal.mem_span_singleton.mpr ⟨s, rfl⟩
      · intro h; obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp h; exact ⟨s, trivial, rfl⟩
    -- Witness existence by contradiction + Krull
    obtain ⟨s, hs_ne, hs_ann, hs_not⟩ : ∃ s : S, s ≠ 0 ∧
        q ≤ (⊥ : Submodule S S).colon ({s} : Set S) ∧
        s ∉ (x • ⊤ : Submodule S S) := by
      by_contra hall; push_neg at hall
      -- Every s ≠ 0 with q ≤ ann(s) satisfies s ∈ x • ⊤
      -- Show: r ∈ (Ideal.span {x})^n for all n, by induction
      have hmem_all : ∀ n, r ∈ Ideal.span ({x} : Set S) ^ n := by
        intro n; induction n with
        | zero => simp
        | succ n ih_n =>
          -- r ∈ (x)^n, so r = x^n * t for some t
          rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ih_n ⊢
          obtain ⟨t, rfl⟩ := ih_n
          -- ann(t) ⊇ ann(r) = q (from colon_singleton_dvd iterated n times)
          have ht_ann : q ≤ (⊥ : Submodule S S).colon ({t} : Set S) := by
            suffices ∀ k, q ≤ (⊥ : Submodule S S).colon ({x ^ k * t} : Set S) →
                q ≤ (⊥ : Submodule S S).colon ({t} : Set S) from
              this n (hr_ann ▸ le_refl _)
            intro k; induction k with
            | zero => simp
            | succ k ih_k =>
              intro hk; apply ih_k
              exact colon_singleton_dvd_of_isSMulRegular hxreg
                (show q ≤ (⊥ : Submodule S S).colon ({x * (x ^ k * t)} : Set S) by
                  rwa [show x * (x ^ k * t) = x ^ (k + 1) * t from by ring])
          have ht_ne : t ≠ 0 := by
            intro h; simp [h] at hr_ne
          -- By hypothesis: t ∈ x • ⊤
          have := hall t ht_ne ht_ann
          rw [hxt_eq, Ideal.mem_span_singleton] at this
          obtain ⟨u, rfl⟩ := this
          exact ⟨u, by ring⟩
      -- Contradicts Krull intersection
      have hkrull := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span ({x} : Set S)) hne_top
      have : r ∈ ⨅ n, Ideal.span ({x} : Set S) ^ n := by
        simp only [Submodule.mem_iInf]; exact hmem_all
      rw [hkrull, Submodule.mem_bot] at this; exact hr_ne this
    -- (c) Image of s in Q is nonzero (s ∉ ker(S → Q) = x • ⊤)
    have hs_bar_ne : algebraMap S Q s ≠ 0 := by
      intro h; apply hs_not
      have : Ideal.Quotient.mk (x • ⊤ : Ideal S) s = 0 := h
      rwa [Ideal.Quotient.eq_zero_iff_mem] at this
    -- (d) Find P ∈ Ass(Q) with P ⊇ ann_Q(ŝ) ⊇ image(q)
    obtain ⟨P, hP_ass, hP_le⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing Q
      (algebraMap S Q s) hs_bar_ne
    -- P ∈ Min(Q) by IH
    have hP_min := ih_quot hP_ass
    -- (e) comap P to S is in (x • ⊤).minimalPrimes
    have hP_comap_min : Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P ∈
        (x • ⊤ : Ideal S).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact Set.mem_image_of_mem _ hP_min
    -- height(comap P) ≤ 1 by Krull PIT
    have hP_ht : (Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P).height ≤ 1 := by
      have : Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P ∈
          (Ideal.span ({x} : Set S)).minimalPrimes := by rwa [← hxt_eq]
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ this
    -- (f) q ⊆ comap P (from ann_Q(ŝ) ⊇ image(q) and P ⊇ ann_Q(ŝ))
    have hq_le_comap : q ≤ Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P := by
      intro a ha
      rw [Ideal.mem_comap]
      apply hP_le
      rw [Submodule.mem_colon_singleton]
      show Ideal.Quotient.mk _ a * Ideal.Quotient.mk _ s = 0
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have : a ∈ q := ha
      have : a * s = 0 := by
        have := hs_ann this
        rwa [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul] at this
      rw [this]; exact zero_mem _
    -- x ∈ comap P (since x ∈ ker(S → Q) ⊆ comap P)
    have hx_in_comap : x ∈ Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P := by
      rw [Ideal.mem_comap]
      suffices h : Ideal.Quotient.mk (x • ⊤ : Ideal S) x = 0 from h ▸ P.zero_mem
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact ⟨1, Submodule.mem_top, show x • (1 : S) = x from mul_one x⟩
    -- q ⊊ comap P (since x ∈ comap P \ q)
    have hq_lt : q < Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P := by
      exact lt_of_le_of_ne hq_le_comap (fun h => hxq (h ▸ hx_in_comap))
    -- height(q) + 1 ≤ height(comap P) ≤ 1
    haveI : P.IsPrime := hP_ass.isPrime
    haveI : (Ideal.comap (Ideal.Quotient.mk (x • ⊤ : Ideal S)) P).IsPrime :=
      Ideal.comap_isPrime _ P
    have := Ideal.primeHeight_add_one_le_of_lt hq_lt
    rw [Ideal.height_eq_primeHeight] at hP_ht
    -- primeHeight(q) + 1 ≤ primeHeight(comap P) ≤ height(comap P) ≤ 1
    have : q.primeHeight + 1 ≤ 1 := le_trans this hP_ht
    -- primeHeight(q) = 0, contradicting hq_pos
    have : q.primeHeight = 0 := by
      have hfin := Ideal.primeHeight_ne_top q
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
      rw [← hk] at this ⊢
      have h1 : (k : ℕ∞) + 1 ≤ 1 := this
      have h2 : k + 1 ≤ 1 := by exact_mod_cast h1
      simp [show k = 0 from by omega]
    exact hht this

/-- **Unmixedness** (Bruns-Herzog 2.1.2(c)): In a CM Noetherian local ring,
every associated prime has height 0, i.e., is a minimal prime. -/
theorem associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing
    [IsCohenMacaulayLocalRing R] :
    associatedPrimes R R ⊆ minimalPrimes R := by
  have hlt := Ideal.primeHeight_lt_top (IsLocalRing.maximalIdeal R)
  have hne := (WithTop.lt_top_iff_ne_top.mp hlt)
  obtain ⟨n, hn⟩ := (WithTop.ne_top_iff_exists.mp hne)
  exact unmixedness_of_dim_le n R (le_of_eq hn.symm)

/-- In a CM Noetherian local ring, for any prime `p` with `height(p) > 0`,
there exists an `R`-regular element in `p ∩ m`. -/
theorem exists_smulRegular_mem_of_isCohenMacaulayLocalRing
    [IsCohenMacaulayLocalRing R]
    (p : Ideal R) [p.IsPrime]
    (hp : (0 : WithBot ℕ∞) < Ideal.height p) :
    ∃ x ∈ p, x ∈ maximalIdeal R ∧ IsSMulRegular R x := by
  have hunmixed := associatedPrimes_subset_minimalPrimes_of_isCohenMacaulayLocalRing (R := R)
  have hp_not_le : ∀ q ∈ associatedPrimes R R, ¬(p ≤ q) := by
    intro q hq hle
    have hq_prime : q.IsPrime := (show IsAssociatedPrime q R from hq).isPrime
    have hq_ht : q.primeHeight = 0 := Ideal.primeHeight_eq_zero_iff.mpr (hunmixed hq)
    have hle_ht := Ideal.primeHeight_mono hle
    rw [hq_ht] at hle_ht
    have hp_ht : p.primeHeight = 0 := nonpos_iff_eq_zero.mp hle_ht
    rw [Ideal.height_eq_primeHeight, hp_ht] at hp
    exact lt_irrefl _ hp
  have hfin := associatedPrimes.finite R R
  have hp_not_sub : ¬((p : Set R) ⊆ ⋃ q ∈ associatedPrimes R R, (q : Set R)) := by
    rw [Ideal.subset_union_prime_finite hfin 0 0
      (fun q hq _ _ => (show IsAssociatedPrime q R from hq).isPrime)]
    exact fun ⟨q, hq, hle⟩ => hp_not_le q hq hle
  obtain ⟨x, hxp, hx_not_mem⟩ := Set.not_subset.mp hp_not_sub
  rw [biUnion_associatedPrimes_eq_compl_regular R R] at hx_not_mem
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hx_not_mem
  exact ⟨x, hxp, IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹_›) hxp, hx_not_mem⟩

end Unmixedness

/-! ### CM localizes -/

section Localization

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Small.{u} R]

/-- Build a weakly regular sequence on `S` of length `d` with all elements in
`p ∩ m`, given a CM local ring `S` and a prime `p` with `primeHeight p ≥ d`. -/
private lemma exists_weaklyRegular_in_prime (d : ℕ) :
    ∀ (S : Type u) [inst1 : CommRing S] [inst2 : IsLocalRing S] [inst3 : IsNoetherianRing S]
      [inst4 : Small.{u} S] [inst5 : IsCohenMacaulayLocalRing S]
      (p : Ideal S) [p.IsPrime],
      (d : ℕ∞) ≤ p.primeHeight →
      ∃ rs : List S, rs.length = d ∧ IsWeaklyRegular S rs ∧
        (∀ r ∈ rs, r ∈ p) ∧ (∀ r ∈ rs, r ∈ maximalIdeal S) := by
  induction d with
  | zero =>
    intro S _ _ _ _ _ p _ _
    refine ⟨[], rfl, IsWeaklyRegular.nil S S, ?_, ?_⟩ <;> intro _ h <;> exact nomatch h
  | succ d ih =>
    intro S _ _ _ _ _ p _ hd
    -- height(p) ≥ d+1 > 0
    have hp_pos : (0 : WithBot ℕ∞) < Ideal.height p := by
      rw [Ideal.height_eq_primeHeight]
      exact_mod_cast lt_of_lt_of_le (show (0 : ℕ∞) < ↑(d + 1) by exact_mod_cast Nat.zero_lt_succ d) hd
    -- Regular x ∈ p ∩ m
    obtain ⟨x, hxp, hxm, hxreg⟩ := exists_smulRegular_mem_of_isCohenMacaulayLocalRing p hp_pos
    -- R/(x) is CM
    haveI := quotSMulTopLocalRing hxm
    haveI : IsCohenMacaulayLocalRing (QuotSMulTop x S) :=
      isCohenMacaulayLocalRing_quotient hxreg hxm
    -- p maps to a prime p' in R/(x) (since x ∈ p means ker ≤ p)
    set I := (x • ⊤ : Ideal S)
    have hI_le_p : I ≤ p := by
      intro a ha; obtain ⟨s, -, rfl⟩ := ha
      change x • s ∈ p; rw [smul_eq_mul]; exact Ideal.mul_mem_right s p hxp
    set p' := p.map (Ideal.Quotient.mk I) with p'_def
    have hker_le : RingHom.ker (Ideal.Quotient.mk I) ≤ p := by rw [Ideal.mk_ker]; exact hI_le_p
    haveI : p'.IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker_le
    -- primeHeight(p') ≥ d (from height(p) ≤ height(p') + 1 and height(p) ≥ d+1)
    have hp'_ht : (d : ℕ∞) ≤ p'.primeHeight := by
      have hle : p.height ≤ p'.height + 1 := by
        have h := Ideal.height_le_height_add_one_of_mem (p := p) hxp
        have hxt : Ideal.span ({x} : Set S) = I := by
          ext r; constructor
          · intro h; obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton.mp h; exact ⟨s, trivial, rfl⟩
          · rintro ⟨s, -, rfl⟩; exact Ideal.mem_span_singleton.mpr ⟨s, rfl⟩
        rw [hxt] at h; exact h
      rw [Ideal.height_eq_primeHeight, Ideal.height_eq_primeHeight] at hle
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (Ideal.primeHeight_ne_top p')
      rw [← hk] at hle ⊢
      have h1 : (↑(d + 1) : ℕ∞) ≤ (↑k : ℕ∞) + 1 := le_trans hd hle
      have h2 : (↑(d + 1) : ℕ∞) ≤ ↑(k + 1) := by push_cast; exact h1
      have h3 : d ≤ k := Nat.le_of_succ_le_succ (by exact_mod_cast h2)
      exact Nat.cast_le.mpr h3
    -- IH: weakly regular sequence of length d on R/(x) in p' ∩ m'
    obtain ⟨rs', hrs'_len, hrs'_reg, hrs'_p', hrs'_m'⟩ := ih (QuotSMulTop x S) p' hp'_ht
    -- Lift rs' to S via surjInv
    set σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
    set rs := rs'.map σ
    -- mk(σ(r')) = r' for all r'
    have hσ : ∀ r', Ideal.Quotient.mk I (σ r') = r' :=
      Function.surjInv_eq Ideal.Quotient.mk_surjective
    -- Mapped list equals rs'
    have hrs_map : rs.map (Ideal.Quotient.mk I) = rs' := by
      simp [rs, List.map_map, Function.comp_def, hσ]
    -- Each lift is in p (since σ(r') ≡ some preimage in p mod kernel ⊆ p)
    have hrs_p : ∀ r ∈ rs, r ∈ p := by
      intro r hr; obtain ⟨r', hr'_mem, rfl⟩ := List.mem_map.mp hr
      have := hrs'_p' r' hr'_mem
      rw [p'_def, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at this
      obtain ⟨a, ha_p, ha_eq⟩ := this
      have hsub : σ r' - a ∈ I := by
        rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; rw [hσ]; exact ha_eq.symm
      exact sub_add_cancel (σ r') a ▸ p.add_mem (hI_le_p hsub) ha_p
    -- Each lift is in maximalIdeal (non-unit ↔ image is non-unit)
    have hrs_m : ∀ r ∈ rs, r ∈ maximalIdeal S := by
      intro r hr; rw [mem_maximalIdeal]; intro hu
      obtain ⟨r', hr'_mem, rfl⟩ := List.mem_map.mp hr
      exact (mem_maximalIdeal _).mp (hrs'_m' r' hr'_mem) (by rw [← hσ r']; exact hu.map _)
    -- Weak regularity: rs is weakly regular on QuotSMulTop x S (via algebraMap transfer)
    have hrs_wreg_quot : IsWeaklyRegular (QuotSMulTop x S) rs :=
      (isWeaklyRegular_map_algebraMap_iff (QuotSMulTop x S) (QuotSMulTop x S) rs).mp
        (hrs_map ▸ hrs'_reg)
    -- x :: rs is weakly regular on S
    have hrs_len : rs.length = d := by show (rs'.map σ).length = d; simp [hrs'_len]
    exact ⟨x :: rs, by simp [hrs_len],
      (isWeaklyRegular_cons_iff S x rs).mpr ⟨hxreg, hrs_wreg_quot⟩,
      fun r hr => (List.mem_cons.mp hr).elim (· ▸ hxp) (hrs_p r),
      fun r hr => (List.mem_cons.mp hr).elim (· ▸ hxm) (hrs_m r)⟩

/-- **CM localizes**: CM local `R` → `R_p` is CM local for every prime `p`.

Build a weakly regular sequence in `p ∩ m` of length = height(p), localize
to R_p where it becomes regular in the maximal ideal, then apply
`isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim`. -/
theorem isCohenMacaulayLocalRing_localization_atPrime [IsCohenMacaulayLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  -- Get height(p) as a natural number
  obtain ⟨h, hh⟩ := WithTop.ne_top_iff_exists.mp (Ideal.primeHeight_ne_top p)
  -- Build weakly regular sequence in p ∩ m of length h
  obtain ⟨rs, hrs_len, hrs_reg, hrs_p, hrs_m⟩ :=
    exists_weaklyRegular_in_prime h R p (le_of_eq hh)
  -- Localize: rs becomes regular on R_p
  set Rp := Localization.AtPrime p
  have hrs_reg_loc : IsRegular Rp (rs.map (algebraMap R Rp)) :=
    hrs_reg.isRegular_of_isLocalization_of_mem Rp p hrs_p
  -- Mapped elements are in maximalIdeal R_p
  have hrs_m_loc : ∀ r ∈ rs.map (algebraMap R Rp), r ∈ maximalIdeal Rp := by
    intro r hr; obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hrs_p s hs)
  -- Length = height(p) = dim(R_p)
  have hdim : ringKrullDim Rp = ↑((rs.map (algebraMap R Rp)).length : ℕ∞) := by
    simp only [List.length_map, hrs_len]
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rp, Ideal.height_eq_primeHeight, ← hh]; rfl
  -- Apply CM criterion
  exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim
    hrs_reg_loc.toIsWeaklyRegular hrs_m_loc hdim

/-- A CM Noetherian local ring is a CM ring. -/
theorem IsCohenMacaulayRing.of_isCohenMacaulayLocalRing [IsCohenMacaulayLocalRing R] :
    IsCohenMacaulayRing R where
  CM_localize p _ := isCohenMacaulayLocalRing_localization_atPrime p

end Localization

end

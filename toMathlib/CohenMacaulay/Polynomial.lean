/-
This file proves that multivariate polynomial rings over fields are
Cohen-Macaulay. The main result used in the BEI project is
`isCohenMacaulayRing_mvPolynomial_field`, which provides the base case
for the HH global CM theorem.
-/

import toMathlib.CohenMacaulay.Localization
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.PID
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Cohen-Macaulay Polynomial Rings

## Main results

- `isCohenMacaulayRing_mvPolynomial_field`:
  `MvPolynomial (Fin n) K` is Cohen-Macaulay for any field `K`.

## Strategy

The multivariate polynomial CM theorem is proved by induction on the number
of variables using `MvPolynomial.finSuccEquiv`. Each inductive step reduces
to showing that `A[X]` is CM when `A` is a CM domain, which is proved by
case analysis on each prime `P`:

- **Case `X ∈ P`**: `X` is a regular element and `A[X]_P / (X) ≅ A_{P̄}`.
- **Case `X ∉ P`**: Structural induction on `dim(A_p)`.
-/

noncomputable section

open IsLocalRing RingTheory.Sequence Polynomial
open scoped Pointwise

universe u

/-! ### CM invariance under ring equivalences -/

section RingEquiv

variable {A₀ B₀ : Type u} [CommRing A₀] [CommRing B₀]

/-- A ring equivalence between local rings is a local ring homomorphism. -/
instance ringEquiv_isLocalHom [IsLocalRing A₀] [IsLocalRing B₀]
    (e : A₀ ≃+* B₀) : IsLocalHom e.toRingHom where
  map_nonunit a ha := by
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at ha
    exact (isUnit_map_iff e a).mp ha

/-- Weakly regular sequences transfer through ring equivalences. -/
lemma isWeaklyRegular_map_ringEquiv (e : A₀ ≃+* B₀) {rs : List A₀}
    (hreg : IsWeaklyRegular A₀ rs) : IsWeaklyRegular B₀ (rs.map e) := by
  letI : Algebra A₀ B₀ := e.toRingHom.toAlgebra
  let eₗ : A₀ ≃ₗ[A₀] B₀ :=
    { e.toAddEquiv with
      map_smul' := fun a x => by
        change e (a * x) = e.toRingHom a * e x
        exact e.map_mul a x }
  exact (isWeaklyRegular_map_algebraMap_iff B₀ B₀ rs).mpr
    ((LinearEquiv.isWeaklyRegular_congr eₗ rs).mp hreg)

/-- Cohen-Macaulay local rings are invariant under ring isomorphisms. -/
theorem isCohenMacaulayLocalRing_of_ringEquiv'
    [IsLocalRing A₀] [IsLocalRing B₀]
    (hCM : IsCohenMacaulayLocalRing A₀) (e : A₀ ≃+* B₀) :
    IsCohenMacaulayLocalRing B₀ where
  depth_eq_dim := by
    have hdim : ringKrullDim B₀ = ringKrullDim A₀ :=
      (ringKrullDim_eq_of_ringEquiv e).symm
    rw [hdim, hCM.depth_eq_dim]; congr 1
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨rs, rfl, hreg, hmem⟩
      exact le_sSup ⟨rs.map e, by simp, isWeaklyRegular_map_ringEquiv e hreg,
        fun r hr => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
          exact map_nonunit e.toRingHom a (hmem a ha)⟩
    · apply sSup_le
      rintro _ ⟨rs, rfl, hreg, hmem⟩
      exact le_sSup ⟨rs.map e.symm, by simp,
        isWeaklyRegular_map_ringEquiv e.symm hreg,
        fun r hr => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
          exact map_nonunit e.symm.toRingHom a (hmem a ha)⟩

/-- For a ring equiv `e : R ≃+* S`, mapping the prime complement of an ideal
backwards through `e.symm` gives the prime complement of the comap ideal. -/
private lemma primeCompl_map_ringEquiv_symm {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (q : Ideal S) [q.IsPrime] [(q.comap e).IsPrime] :
    q.primeCompl.map e.symm.toMonoidHom = (q.comap e).primeCompl := by
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
  constructor
  · rintro ⟨y, hy, heq⟩
    rw [show e x = y from by rw [← heq]; simp]; exact hy
  · intro hx
    exact ⟨e x, hx, by simp⟩

/-- Cohen-Macaulay rings are invariant under ring isomorphisms. -/
theorem isCohenMacaulayRing_of_ringEquiv
    [IsCohenMacaulayRing A₀] (e : A₀ ≃+* B₀) :
    IsCohenMacaulayRing B₀ where
  CM_localize q _ := by
    haveI : (q.comap e).IsPrime := Ideal.IsPrime.comap e.toRingHom
    have hCM_loc := IsCohenMacaulayRing.CM_localize (q.comap e) (R := A₀)
    have H : q.primeCompl.map e.symm.toMonoidHom = (q.comap e).primeCompl :=
      primeCompl_map_ringEquiv_symm e q
    exact isCohenMacaulayLocalRing_of_ringEquiv'
      hCM_loc (IsLocalization.ringEquivOfRingEquiv _ _ e.symm H).symm

end RingEquiv

/-! ### Fields are Cohen-Macaulay -/

section Field

variable (K : Type u) [Field K]

/-- A field is a Cohen-Macaulay ring. -/
instance isCohenMacaulayRing_of_isField : IsCohenMacaulayRing K where
  CM_localize p _ := by
    haveI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    apply isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p _]
    -- In a field, every prime is ⊥
    have hp : p = ⊥ := by
      ext x; simp only [Ideal.mem_bot]; constructor
      · intro hx; by_contra h
        exact (Ideal.IsPrime.ne_top ‹_›)
          (Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.mk0 x h))
      · intro h; rw [h]; exact p.zero_mem
    have hh : p.primeHeight = 0 := (Ideal.primeHeight_eq_zero_iff).mpr (by
      rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]; exact hp)
    simp [Ideal.height_eq_primeHeight, hh]

end Field

/-! ### Polynomial ring CM extension for domains -/

section PolynomialExtension

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]

/-- In a domain, any nonzero element is SMulRegular on any localization. -/
private lemma isSMulRegular_algebraMap_of_ne_zero
    (p : Ideal A) [p.IsPrime] {f : A} (hf : f ≠ 0) :
    IsSMulRegular (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) f) := by
  haveI : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have hf' : algebraMap A (Localization.AtPrime p) f ≠ 0 :=
    fun h => hf (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
      (by rw [h, map_zero]))
  intro a b hab; exact mul_left_cancel₀ hf' hab

/-- In a domain `A`, a nonzero prime `P` of `A[X]` with `P.comap C = ⊥` has
height 1. The proof localizes `A[X]` at `(nonZeroDivisors A).map C` to get
`(FractionRing A)[X]`, a PID. The image of `P` is a nonzero prime of the PID,
hence maximal of height 1, and `IsLocalization.height_map_of_disjoint` transfers
the height back. -/
private lemma height_eq_one_of_comap_C_eq_bot
    (P : Ideal (Polynomial A)) [P.IsPrime]
    (hP : P ≠ ⊥) (hcomap : P.comap (Polynomial.C : A →+* Polynomial A) = ⊥) :
    P.height = 1 := by
  set K := FractionRing A
  -- Set up K[X] as a localization of A[X] at (nonZeroDivisors A).map C
  letI algKX : Algebra (Polynomial A) (Polynomial K) :=
    (Polynomial.mapRingHom (algebraMap A K)).toAlgebra
  haveI hIL : @IsLocalization _ _ ((nonZeroDivisors A).map C) (Polynomial K) _
      algKX :=
    Polynomial.isLocalization (nonZeroDivisors A) K
  -- P is disjoint from the multiplicative set
  have disj : Disjoint (((nonZeroDivisors A).map C :
      Submonoid (Polynomial A)) : Set (Polynomial A))
      (P : Set (Polynomial A)) := by
    rw [Set.disjoint_left]; intro g hgM hgP
    obtain ⟨a, haM, rfl⟩ := Submonoid.mem_map.mp hgM
    have hmem : a ∈ P.comap C := hgP
    rw [hcomap] at hmem; exact nonZeroDivisors.ne_zero haM hmem
  -- Transfer height to K[X] via IsLocalization.height_map_of_disjoint
  haveI : (P.map (@algebraMap _ _ _ _ algKX)).IsPrime :=
    @IsLocalization.isPrime_of_isPrime_disjoint _ _ _ _ _ _ hIL P inferInstance disj
  have htransfer := @IsLocalization.height_map_of_disjoint _ _ _ _ _ _ hIL P ‹P.IsPrime› disj
  rw [← htransfer]
  -- Now goal: (map (algebraMap A[X] K[X]) P).height = 1
  set P' := P.map (@algebraMap _ _ _ _ algKX) with hP'_def
  have hP'_ne : P' ≠ ⊥ := by
    intro h; apply hP
    have hcm := @IsLocalization.comap_map_of_isPrime_disjoint
      _ _ _ _ _ _ hIL P inferInstance disj
    have hbot : Ideal.map (@algebraMap _ _ _ _ algKX) P = ⊥ := h
    rw [hbot, Ideal.comap_bot_of_injective _
      (Polynomial.map_injective _ (IsFractionRing.injective A K))] at hcm
    exact hcm.symm
  haveI : P'.IsMaximal := Ideal.IsPrime.isMaximal ‹_› hP'_ne
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal P' (Polynomial.not_isField K)

/-! ### Quotient-localization identification for polynomial rings

For a CM domain `A`, a prime `P` of `A[X]` containing `X`, the quotient
`A[X]_P / (X)` is isomorphic as a ring to `A_{P ∩ A}`. This section
builds the ring equivalence and transfers the CM property. -/

/-- For a polynomial `f`, the difference `f - C(f.eval 0)` lies
in `Ideal.span {X}`. -/
private lemma polynomial_sub_C_eval_mem_span_X (f : Polynomial A) :
    f - Polynomial.C (f.eval 0) ∈ Ideal.span ({Polynomial.X} : Set (Polynomial A)) := by
  rw [Ideal.mem_span_singleton, ← f.coeff_zero_eq_eval_zero]
  exact Polynomial.X_dvd_sub_C

/-- If `X ∈ P` and `s ∉ P`, then `s.eval 0 ∉ P.comap C`. -/
private lemma eval_zero_not_mem_comap_of_not_mem
    {P : Ideal (Polynomial A)} [P.IsPrime] (hX : Polynomial.X ∈ P)
    {s : Polynomial A} (hs : s ∉ P) :
    s.eval 0 ∉ (P.comap (Polynomial.C : A →+* Polynomial A)) := by
  intro hmem
  rw [Ideal.mem_comap] at hmem
  apply hs
  have hsub : s - Polynomial.C (s.eval 0) ∈ P :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hX) (polynomial_sub_C_eval_mem_span_X s)
  have hC_mem : Polynomial.C (s.eval 0) ∈ P := hmem
  have : s = (s - Polynomial.C (s.eval 0)) + Polynomial.C (s.eval 0) := by ring
  rw [this]; exact P.add_mem hsub hC_mem

/-- The evaluation-at-zero ring hom from `A[X]` to `Localization.AtPrime (P.comap C)`
maps `P.primeCompl` to units. -/
private lemma evalMap_map_units
    {P : Ideal (Polynomial A)} [P.IsPrime] (hX : Polynomial.X ∈ P) :
    ∀ s : P.primeCompl,
      IsUnit (((algebraMap A (Localization.AtPrime (P.comap (Polynomial.C : A →+* Polynomial A)))).comp
        (Polynomial.evalRingHom 0)) (s : Polynomial A)) := by
  rintro ⟨s, hs⟩
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom]
  exact IsLocalization.map_units _
    ⟨s.eval 0, (Ideal.mem_primeCompl_iff.mpr (eval_zero_not_mem_comap_of_not_mem hX
      (Ideal.mem_primeCompl_iff.mp hs)))⟩

set_option maxHeartbeats 800000 in
/-- Ring equiv between `QuotSMulTop aX Rp` and `Localization.AtPrime (P.comap C)`,
where `Rp = A[X]_P` and `aX` is the image of `X` in `Rp`. -/
private noncomputable def quotSMulTopPolynomialLocalizationEquiv
    (P : Ideal (Polynomial A)) [P.IsPrime] (hX : Polynomial.X ∈ P) :
    QuotSMulTop (algebraMap (Polynomial A) (Localization.AtPrime P) Polynomial.X)
      (Localization.AtPrime P) ≃+*
      Localization.AtPrime (P.comap (Polynomial.C : A →+* Polynomial A)) := by
  set p := P.comap (Polynomial.C : A →+* Polynomial A) with hp_def
  set Rp := Localization.AtPrime P
  set aX := algebraMap (Polynomial A) Rp Polynomial.X
  set Ap := Localization.AtPrime p
  -- Build backward map: Rp → Ap via eval₀
  set evalMap : Polynomial A →+* Ap :=
    (algebraMap A Ap).comp (Polynomial.evalRingHom 0) with evalMap_def
  have heval_units : ∀ s : P.primeCompl, IsUnit (evalMap s) := evalMap_map_units hX
  set ψ₀ : Rp →+* Ap := IsLocalization.lift heval_units with ψ₀_def
  -- ψ₀ kills aX
  have hψ₀_aX : ψ₀ aX = 0 := by
    simp only [ψ₀_def, aX, evalMap_def]
    rw [IsLocalization.lift_eq]; simp [Polynomial.eval_X]
  -- ψ₀ kills the submodule aX • ⊤
  have hψ₀_ker : ∀ z ∈ (aX • ⊤ : Submodule Rp Rp), ψ₀ z = 0 := by
    intro z hz
    rw [Submodule.mem_smul_pointwise_iff_exists] at hz
    obtain ⟨w, _, rfl⟩ := hz
    show ψ₀ (aX * w) = 0; rw [map_mul, hψ₀_aX, zero_mul]
  -- Factor ψ₀ through the quotient
  set ψ : QuotSMulTop aX Rp →+* Ap :=
    Ideal.Quotient.lift (aX • ⊤ : Ideal Rp) ψ₀ hψ₀_ker with ψ_def
  -- Build forward map: Ap → QuotSMulTop aX Rp via C embedding
  have hembed_units : ∀ s : p.primeCompl,
      IsUnit ((algebraMap Rp (QuotSMulTop aX Rp)).comp
        ((algebraMap (Polynomial A) Rp).comp Polynomial.C) s) := by
    rintro ⟨s, hs⟩
    simp only [RingHom.comp_apply]
    have hs' : s ∉ p := Ideal.mem_primeCompl_iff.mp hs
    have hCs : Polynomial.C s ∉ P := by rwa [Ideal.mem_comap] at hs'
    exact (IsLocalization.map_units Rp
      (⟨Polynomial.C s, Ideal.mem_primeCompl_iff.mpr hCs⟩ : P.primeCompl)).map
      (algebraMap Rp (QuotSMulTop aX Rp))
  set φ : Ap →+* QuotSMulTop aX Rp := IsLocalization.lift hembed_units with φ_def
  -- Helper: aX maps to 0 in the quotient
  have haX_zero : (algebraMap Rp (QuotSMulTop aX Rp)) aX = 0 := by
    show Submodule.Quotient.mk aX = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨1, Submodule.mem_top, by simp [Algebra.smul_def]⟩
  -- Helper: in the quotient, f and C(f.eval 0) are identified
  have hmkQ_eq : ∀ f : Polynomial A,
      (algebraMap Rp (QuotSMulTop aX Rp)) (algebraMap (Polynomial A) Rp f) =
      (algebraMap Rp (QuotSMulTop aX Rp)) (algebraMap (Polynomial A) Rp
        (Polynomial.C (f.eval 0))) := by
    intro f
    have hf_diff := polynomial_sub_C_eval_mem_span_X f
    rw [Ideal.mem_span_singleton] at hf_diff
    obtain ⟨g, hg⟩ := hf_diff
    have hf_eq : f = Polynomial.C (f.eval 0) + Polynomial.X * g := by
      linear_combination hg
    have hXg_zero : (algebraMap Rp (QuotSMulTop aX Rp))
        (algebraMap (Polynomial A) Rp (Polynomial.X * g)) = 0 := by
      rw [map_mul (algebraMap (Polynomial A) Rp), map_mul (algebraMap Rp (QuotSMulTop aX Rp)),
        haX_zero, zero_mul]
    conv_lhs => rw [hf_eq, map_add, map_add, hXg_zero, add_zero]
  -- Show ψ ∘ φ = id using IsLocalization.ringHom_ext
  have hψφ_id : ψ.comp φ = RingHom.id Ap := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext a
    simp only [RingHom.comp_apply, RingHom.id_apply]
    have hφ_a : φ (algebraMap A Ap a) = (algebraMap Rp (QuotSMulTop aX Rp))
        (algebraMap (Polynomial A) Rp (Polynomial.C a)) :=
      IsLocalization.lift_eq hembed_units a
    rw [hφ_a]
    change Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ _) = _
    rw [Ideal.Quotient.lift_mk, IsLocalization.lift_eq]
    simp [evalMap_def, Polynomial.eval_C]
  -- Show φ ∘ ψ = id
  -- (φ ∘ ψ = id is not needed since we prove ψ bijective directly)
  -- ψ is surjective (since ψ ∘ φ = id gives a section)
  have hψ_surj : Function.Surjective ψ := by
    intro y; exact ⟨φ y, by have := RingHom.congr_fun hψφ_id y; simpa using this⟩
  -- ψ is injective (kernel argument)
  have hψ_inj : Function.Injective ψ := by
    haveI : IsDomain Rp :=
      IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
    haveI : IsDomain Ap :=
      IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
    intro q1 q2 hq
    obtain ⟨z1, rfl⟩ := Submodule.Quotient.mk_surjective (p := aX • ⊤) q1
    obtain ⟨z2, rfl⟩ := Submodule.Quotient.mk_surjective (p := aX • ⊤) q2
    rw [Submodule.Quotient.eq]
    -- ψ(mk z1) = ψ(mk z2) means ψ₀(z1) = ψ₀(z2), i.e., ψ₀(z1 - z2) = 0
    change Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ z1) =
      Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ z2) at hq
    rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hq
    -- ψ₀(z1) = ψ₀(z2), so ψ₀(z1 - z2) = 0
    have hψ₀_diff : ψ₀ (z1 - z2) = 0 := by rw [map_sub, sub_eq_zero]; exact hq
    -- Need: z1 - z2 ∈ aX • ⊤
    -- Write z1 - z2 as mk'(f, s), then ψ₀(mk'(f, s)) = 0 implies f.eval 0 = 0
    -- implies f ∈ (X), so mk'(f, s) = aX * mk'(f/X, s) ∈ aX • ⊤
    obtain ⟨⟨f, s⟩, hz⟩ := IsLocalization.mk'_surjective P.primeCompl (z1 - z2)
    have hs_not_mem : (s : Polynomial A) ∉ P := Ideal.mem_primeCompl_iff.mp s.prop
    have hs_eval : (s : Polynomial A).eval 0 ∉ p :=
      eval_zero_not_mem_comap_of_not_mem hX hs_not_mem
    rw [show z1 - z2 = IsLocalization.mk' Rp f s from hz.symm] at hψ₀_diff ⊢
    -- ψ₀(mk'(f, s)) = mk'(f.eval 0, s.eval 0) = 0
    have hψ₀_mk' : ψ₀ (IsLocalization.mk' Rp f s) =
        IsLocalization.mk' Ap (f.eval 0)
          (⟨(s : Polynomial A).eval 0,
            Ideal.mem_primeCompl_iff.mpr hs_eval⟩ : p.primeCompl) := by
      rw [ψ₀_def, IsLocalization.lift_mk'_spec]
      simp only [evalMap_def, RingHom.comp_apply, Polynomial.coe_evalRingHom]
      exact (IsLocalization.mk'_spec' (M := p.primeCompl) Ap _ _).symm
    rw [hψ₀_mk'] at hψ₀_diff
    -- mk'(f.eval 0, s.eval 0) = 0 in Ap implies f.eval 0 = 0 (domain)
    have hf_eval_zero : f.eval 0 = 0 := by
      rw [IsLocalization.mk'_eq_zero_iff] at hψ₀_diff
      obtain ⟨⟨t, ht⟩, htf⟩ := hψ₀_diff
      have : t * (f.eval 0) = 0 := htf
      exact (mul_eq_zero.mp this).resolve_left fun h =>
        (ht : t ∉ p) (h ▸ p.zero_mem)
    -- f.eval 0 = 0 implies X ∣ f
    have hX_dvd : Polynomial.X ∣ f := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; exact hf_eval_zero
    obtain ⟨g, hfg⟩ := hX_dvd
    -- mk'(f, s) = aX * mk'(g, s) ∈ aX • ⊤
    rw [hfg]
    have : IsLocalization.mk' Rp (Polynomial.X * g) s =
        aX * IsLocalization.mk' Rp g s := by
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
    rw [this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  exact (RingEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩)

/-! ### Regular elements in primes of CM rings -/

/-- In a CM Noetherian ring, every associated prime has primeHeight 0.

This is CM unmixedness: `Ass(B) = Min(B)` when `B` is CM Noetherian. -/
private lemma primeHeight_zero_of_mem_associatedPrimes_of_isCohenMacaulayRing
    {B : Type u} [CommRing B] [IsNoetherianRing B] [IsCohenMacaulayRing B]
    {p : Ideal B} [p.IsPrime] (hp : p ∈ associatedPrimes B B) : p.primeHeight = 0 := by
  haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
    IsCohenMacaulayRing.CM_localize p
  by_contra hne
  have hpos : (0 : ℕ∞) < p.primeHeight := pos_iff_ne_zero.mpr hne
  -- Get the witness: p = Ann(b), so b ≠ 0 and ∀ a ∈ p, a * b = 0
  obtain ⟨b, hb_ann⟩ := hp.2
  -- b/1 ≠ 0 in B_p
  have hb_ne : algebraMap B (Localization.AtPrime p) b ≠ 0 := by
    intro h0
    rw [IsLocalization.map_eq_zero_iff p.primeCompl] at h0
    obtain ⟨⟨s, hs⟩, hsb⟩ := h0
    exact hs (hb_ann ▸ Submodule.mem_colon_singleton.mpr hsb)
  -- p * span{b} = ⊥ (from the annihilator definition)
  have hpb : p * Ideal.span {b} = ⊥ := by
    ext x; simp only [Ideal.mem_bot, Ideal.mem_mul_span_singleton]
    constructor
    · rintro ⟨a, ha, rfl⟩
      have : a ∈ (⊥ : Submodule B B).colon ({b} : Set B) := hb_ann ▸ ha
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at this
      rw [show a * b = a • b from rfl, this]
    · intro h; exact ⟨0, p.zero_mem, by simp [h]⟩
  -- maxIdeal(B_p) has positive height → ∃ regular element x ∈ maxIdeal
  have hht_loc : (0 : WithBot ℕ∞) <
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)).height := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
        IsLocalization.AtPrime.ringKrullDim_eq_height p _,
        Ideal.height_eq_primeHeight]
    exact_mod_cast hpos
  obtain ⟨x, hxp, _, hxreg⟩ :=
    exists_smulRegular_mem_of_isCohenMacaulayLocalRing
      (IsLocalRing.maximalIdeal (Localization.AtPrime p)) hht_loc
  -- x ∈ maxIdeal = p.map algebraMap, so x * algebraMap(b) = 0
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hxp
  have hmul_bot : Ideal.map (algebraMap B (Localization.AtPrime p)) p *
      Ideal.map (algebraMap B _) (Ideal.span {b}) = ⊥ := by
    rw [← Ideal.map_mul, hpb, Ideal.map_bot]
  have hkill : x * algebraMap B (Localization.AtPrime p) b = 0 := by
    have h1 := Ideal.mul_mem_mul hxp
      (Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime p))
        (Ideal.mem_span_singleton_self b))
    rw [hmul_bot] at h1; exact h1
  -- Contradicts regularity: x kills nonzero b/1
  exact hb_ne (hxreg (show x * algebraMap B _ b = x * 0 by rw [hkill, mul_zero]))

/-- In a CM Noetherian ring, for a prime `q` with positive height, there exists
a `B`-regular element in `q`.

The proof uses CM unmixedness: in a CM ring, all associated primes are minimal.
Since `q` has positive height, `q` is not contained in any associated prime.
By prime avoidance, we find an element of `q` outside all associated primes. -/
private lemma exists_smulRegular_of_isCohenMacaulayRing
    {B : Type u} [CommRing B] [IsNoetherianRing B] [IsCohenMacaulayRing B]
    (q : Ideal B) [q.IsPrime] (hq : (0 : WithBot ℕ∞) < q.height) :
    ∃ a ∈ q, IsSMulRegular B a := by
  -- q has positive height, so q is not contained in any associated prime.
  -- Each associated prime p has primeHeight 0 (= is minimal),
  -- because B_{p} is CM local and Ass(B_p) ⊆ Min(B_p).
  have hq_not_le : ∀ p ∈ associatedPrimes B B, ¬(q ≤ p) := by
    intro p hp hle
    haveI : p.IsPrime := (show IsAssociatedPrime p B from hp).isPrime
    have hp_ht : p.primeHeight = 0 :=
      primeHeight_zero_of_mem_associatedPrimes_of_isCohenMacaulayRing hp
    have hle_ht := Ideal.primeHeight_mono hle
    rw [hp_ht] at hle_ht
    have hq_ht : q.primeHeight = 0 := nonpos_iff_eq_zero.mp hle_ht
    rw [Ideal.height_eq_primeHeight, hq_ht] at hq
    exact lt_irrefl _ hq
  -- By prime avoidance, q is not contained in the union of associated primes
  have hfin := associatedPrimes.finite B B
  have hq_not_sub : ¬((q : Set B) ⊆ ⋃ p ∈ associatedPrimes B B, (p : Set B)) := by
    rw [Ideal.subset_union_prime_finite hfin 0 0
      (fun p hp _ _ => (show IsAssociatedPrime p B from hp).isPrime)]
    exact fun ⟨p, hp, hle⟩ => hq_not_le p hp hle
  obtain ⟨a, haq, ha_not_mem⟩ := Set.not_subset.mp hq_not_sub
  rw [biUnion_associatedPrimes_eq_compl_regular B B] at ha_not_mem
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at ha_not_mem
  exact ⟨a, haq, ha_not_mem⟩

/-- The quotient of a localization by a regular element coming from the base ring
is isomorphic to the localization of the quotient ring.

For `a ∈ p` where `p` is prime and `p' = p.map (Quotient.mk (span {a}))`,
`B_p / (a) ≃+* (B/(a))_{p'}`. -/
-- Localization-quotient commutation for a regular element.
private noncomputable def quotSMulTopLocalizationEquiv_of_mem
    {B : Type u} [CommRing B]
    {p : Ideal B} [p.IsPrime] {a : B} (ha : a ∈ p)
    {p' : Ideal (B ⧸ Ideal.span ({a} : Set B))} [p'.IsPrime]
    (hp' : p'.comap (Ideal.Quotient.mk (Ideal.span ({a} : Set B))) = p) :
    QuotSMulTop (algebraMap B (Localization.AtPrime p) a) (Localization.AtPrime p) ≃+*
      Localization.AtPrime p' := by
  let Bp := Localization.AtPrime p
  let aB : Bp := algebraMap B Bp a
  let mkQ : B →+* (B ⧸ Ideal.span ({a} : Set B)) := Ideal.Quotient.mk _
  let Bp' := Localization.AtPrime p'
  -- Helper: mkQ b ∉ p' ↔ b ∉ p
  have hmkQ_nmem : ∀ b : B, b ∉ p → mkQ b ∉ p' := by
    intro b hb h; exact hb (hp' ▸ h)
  have hmkQ_nmem' : ∀ b : B, mkQ b ∉ p' → b ∉ p := fun b h hb =>
    h (show mkQ b ∈ p' by have : b ∈ p'.comap mkQ := hp' ▸ hb; exact this)
  -- Forward map: Bp → Bp' via B →mkQ B/(a) →alg Bp'
  let φ : B →+* Bp' := (algebraMap _ Bp').comp mkQ
  have hφ_units : ∀ s : p.primeCompl, IsUnit (φ s) := by
    rintro ⟨s, hs⟩; show IsUnit ((algebraMap _ Bp') (mkQ s))
    exact IsLocalization.map_units Bp' ⟨mkQ s, Ideal.mem_primeCompl_iff.mpr (hmkQ_nmem s hs)⟩
  let ψ₀ : Bp →+* Bp' := IsLocalization.lift hφ_units
  have hψ₀_a : ψ₀ aB = 0 := by
    show IsLocalization.lift hφ_units (algebraMap B Bp a) = 0
    rw [IsLocalization.lift_eq]; show (algebraMap _ Bp') (mkQ a) = 0
    rw [show mkQ a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton a)), map_zero]
  have hψ₀_ker : ∀ z ∈ (aB • ⊤ : Ideal Bp), ψ₀ z = 0 := by
    intro z hz; obtain ⟨w, _, rfl⟩ := hz
    show ψ₀ (aB * w) = 0; rw [map_mul, hψ₀_a, zero_mul]
  let ψ : QuotSMulTop aB Bp →+* Bp' := Ideal.Quotient.lift _ ψ₀ hψ₀_ker
  -- Backward map
  have haB_zero : (algebraMap Bp (QuotSMulTop aB Bp)) aB = 0 := by
    show Submodule.Quotient.mk aB = 0
    rw [Submodule.Quotient.mk_eq_zero]; exact ⟨1, Submodule.mem_top, by simp⟩
  let embed : B →+* QuotSMulTop aB Bp := (algebraMap Bp _).comp (algebraMap B Bp)
  have hembed_ker : ∀ x ∈ Ideal.span ({a} : Set B), embed x = 0 := by
    intro x hx; rw [Ideal.mem_span_singleton] at hx; obtain ⟨c, rfl⟩ := hx
    show (algebraMap Bp _) ((algebraMap B Bp) (a * c)) = 0
    rw [map_mul, map_mul, haB_zero, zero_mul]
  let embed' : (B ⧸ Ideal.span ({a} : Set B)) →+* QuotSMulTop aB Bp :=
    Ideal.Quotient.lift _ embed hembed_ker
  have hembed'_units : ∀ s : p'.primeCompl, IsUnit (embed' s) := by
    rintro ⟨s, hs⟩; obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective s
    show IsUnit ((algebraMap Bp _) ((algebraMap B Bp) b))
    exact (IsLocalization.map_units Bp ⟨b, Ideal.mem_primeCompl_iff.mpr
      (hmkQ_nmem' b (Ideal.mem_primeCompl_iff.mp hs))⟩).map _
  let χ : Bp' →+* QuotSMulTop aB Bp := IsLocalization.lift hembed'_units
  -- ψ ∘ χ = id
  have hψχ : ψ.comp χ = RingHom.id Bp' := by
    apply IsLocalization.ringHom_ext p'.primeCompl; ext b
    simp only [RingHom.comp_apply, RingHom.id_apply]
    show ψ (χ ((algebraMap _ Bp') (mkQ b))) = (algebraMap _ Bp') (mkQ b)
    rw [show χ ((algebraMap _ Bp') (mkQ b)) = embed' (mkQ b) from
      IsLocalization.lift_eq hembed'_units b]
    change Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.lift _ embed hembed_ker (mkQ b)) = _
    rw [Ideal.Quotient.lift_mk]
    change Ideal.Quotient.lift _ ψ₀ hψ₀_ker ((algebraMap Bp _) ((algebraMap B Bp) b)) = _
    rw [show (algebraMap Bp (QuotSMulTop aB Bp)) ((algebraMap B Bp) b) =
      Ideal.Quotient.mk _ ((algebraMap B Bp) b) from rfl, Ideal.Quotient.lift_mk]
    show IsLocalization.lift hφ_units ((algebraMap B Bp) b) = _
    rw [IsLocalization.lift_eq]; rfl
  -- Surjectivity from section
  have hψ_surj : Function.Surjective ψ :=
    fun y => ⟨χ y, by simpa using RingHom.congr_fun hψχ y⟩
  -- Injectivity: kernel of ψ₀ is exactly aB • ⊤
  have hψ_inj : Function.Injective ψ := by
    intro q1 q2 hq
    obtain ⟨z1, rfl⟩ := Submodule.Quotient.mk_surjective (p := aB • ⊤) q1
    obtain ⟨z2, rfl⟩ := Submodule.Quotient.mk_surjective (p := aB • ⊤) q2
    rw [Submodule.Quotient.eq]
    change Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ z1) =
      Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ z2) at hq
    rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hq
    have hψ₀_diff : ψ₀ (z1 - z2) = 0 := by rw [map_sub, sub_eq_zero]; exact hq
    obtain ⟨⟨f, s⟩, hz⟩ := IsLocalization.mk'_surjective p.primeCompl (z1 - z2)
    have hz' : IsLocalization.mk' Bp f s = z1 - z2 := hz
    rw [← hz'] at hψ₀_diff ⊢
    have hs'_nmem : mkQ (s : B) ∉ p' := hmkQ_nmem s s.prop
    have hψ₀_val : ψ₀ (IsLocalization.mk' Bp f s) =
        IsLocalization.mk' Bp' (mkQ f) ⟨mkQ s, Ideal.mem_primeCompl_iff.mpr hs'_nmem⟩ := by
      show IsLocalization.lift hφ_units (IsLocalization.mk' Bp f s) = _
      rw [IsLocalization.lift_mk'_spec]; simp only [φ, RingHom.comp_apply]
      exact (IsLocalization.mk'_spec' Bp' (mkQ f) ⟨mkQ s, _⟩).symm
    rw [hψ₀_val, IsLocalization.mk'_eq_zero_iff] at hψ₀_diff
    obtain ⟨⟨t', ht'⟩, ht'f⟩ := hψ₀_diff
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t'
    have ht_nmem : t ∉ p := hmkQ_nmem' t (Ideal.mem_primeCompl_iff.mp ht')
    have htf_mem : t * f ∈ Ideal.span ({a} : Set B) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]; exact ht'f
    rw [Ideal.mem_span_singleton] at htf_mem; obtain ⟨c, hc⟩ := htf_mem
    have key : IsLocalization.mk' Bp f s =
        aB * IsLocalization.mk' Bp c
          (⟨t, Ideal.mem_primeCompl_iff.mpr ht_nmem⟩ * s : p.primeCompl) := by
      -- Goal: mk'(f, s) = aB * mk'(c, t*s)
      -- Expand aB and use mk' arithmetic:
      -- aB * mk'(c, t*s) = algebraMap(a)/1 * c/(t*s) = (a*c)/(t*s) = (t*f)/(t*s) = f/s
      rw [show aB = algebraMap B Bp a from rfl, IsLocalization.mul_mk'_eq_mk'_of_mul]
      -- Goal: mk'(f, s) = mk'(a*c, t*s)... but with ⟨t,..⟩*s
      apply IsLocalization.mk'_eq_of_eq
      show ↑s * (a * c) = ↑(⟨t, _⟩ * s : p.primeCompl) * f
      simp only [Submonoid.coe_mul]; rw [← hc]; ring
    rw [key]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  exact RingEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩

/-- In a CM Noetherian ring, the quotient by a regular element is CM.
This follows from forward CM transfer at each localization. -/
private lemma isCohenMacaulayRing_quotient_of_smulRegular
    {B : Type u} [CommRing B] [IsNoetherianRing B] [IsCohenMacaulayRing B]
    {a : B} (hreg : IsSMulRegular B a) :
    IsCohenMacaulayRing (B ⧸ Ideal.span {a}) where
  CM_localize p' _ := by
    -- p' is a prime of B/(a). The corresponding prime p in B contains a.
    set p := p'.comap (Ideal.Quotient.mk (Ideal.span ({a} : Set B))) with hp_def
    haveI : p.IsPrime := Ideal.IsPrime.comap _
    have ha_mem_p : a ∈ p := by
      rw [hp_def, Ideal.mem_comap]
      have : Ideal.Quotient.mk (Ideal.span ({a} : Set B)) a = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))
      rw [this]; exact p'.zero_mem
    -- B_p is CM local
    haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
      IsCohenMacaulayRing.CM_localize p
    haveI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    -- a maps to the maximal ideal of B_p
    have ha_max : algebraMap B (Localization.AtPrime p) a ∈
        maximalIdeal (Localization.AtPrime p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ ha_mem_p
    -- a is regular on B_p (by flatness of localization)
    have ha_reg_loc : IsSMulRegular (Localization.AtPrime p) (algebraMap B _ a) :=
      hreg.of_flat
    -- Forward CM transfer: B_p / (a) is CM local
    haveI := quotSMulTopLocalRing ha_max
    haveI hCM_quot := isCohenMacaulayLocalRing_quotient ha_reg_loc ha_max
    -- (B/(a))_{p'} ≅ B_p / (a) as local rings
    haveI : IsNoetherianRing (Localization.AtPrime p') :=
      IsLocalization.isNoetherianRing p'.primeCompl _ inferInstance
    exact isCohenMacaulayLocalRing_of_ringEquiv' hCM_quot
      (quotSMulTopLocalizationEquiv_of_mem ha_mem_p hp_def.symm)

/-! ### CM for polynomial localizations (general induction)

For a Noetherian CM ring `B`, every localization `B[X]_Q` at a prime `Q` of
`B[X]` is Cohen-Macaulay local. The proof uses induction on `Q.primeHeight`:

- Base case: `Q.primeHeight = 0` means `dim(B[X]_Q) = 0`, trivially CM.
- When `q = Q ∩ B` has positive height, we find a non-zero-divisor `a ∈ q`
  (by CM unmixedness + prime avoidance), apply converse CM transfer with
  `C(a)`, and recurse on `(B/(a))[X]` with smaller prime height.
- When `q` has height 0, the going-down formula + PID argument gives
  `Q.primeHeight ≤ 1`. Since `Q.primeHeight > 0`, it equals 1,
  handled by a 1-element weakly regular sequence.
-/

set_option maxHeartbeats 800000 in
/-- For a CM Noetherian ring `B` and prime `Q` of `B[X]` with
`Q.primeHeight ≤ d`, the localization `B[X]_Q` is CM local. -/
private lemma cm_localize_polynomial_of_cm_aux (d : ℕ) :
    ∀ (B : Type u) [CommRing B] [IsNoetherianRing B] [IsCohenMacaulayRing B]
      (Q : Ideal (Polynomial B)) [Q.IsPrime],
      Q.primeHeight ≤ d →
      IsCohenMacaulayLocalRing (Localization.AtPrime Q) := by
  induction d with
  | zero =>
    intro B _ _ _ Q _ hd
    haveI : IsNoetherianRing (Polynomial B) := inferInstance
    haveI : IsNoetherianRing (Localization.AtPrime Q) :=
      IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
    apply isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
        Ideal.height_eq_primeHeight]
    simp [nonpos_iff_eq_zero.mp hd]
  | succ d ih =>
    intro B _ _ _ Q _ hd
    haveI : IsNoetherianRing (Polynomial B) := inferInstance
    haveI : IsNoetherianRing (Localization.AtPrime Q) :=
      IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
    by_cases hQ_ht0 : Q.primeHeight = 0
    · exact ih B Q (hQ_ht0 ▸ zero_le _)
    -- Q.primeHeight > 0; set q = Q ∩ B
    set q := Q.comap (Polynomial.C : B →+* Polynomial B) with hq_def
    haveI : q.IsPrime := Ideal.IsPrime.comap Polynomial.C
    by_cases hq_pos : (0 : WithBot ℕ∞) < q.height
    · -- Case: q has positive height.
      -- Step 1: find a B-regular element a ∈ q
      obtain ⟨a, haq, ha_reg⟩ := exists_smulRegular_of_isCohenMacaulayRing q hq_pos
      -- Step 2: C(a) is regular on B[X] (flatness) and hence on B[X]_Q
      have hCa_reg_poly : IsSMulRegular (Polynomial B) (Polynomial.C a) := by
        rw [← Polynomial.algebraMap_eq]; exact ha_reg.of_flat
      set BXQ := Localization.AtPrime Q
      set ca := algebraMap (Polynomial B) BXQ (Polynomial.C a) with hca_def
      have hCa_reg : IsSMulRegular BXQ ca := by
        rw [hca_def]; exact hCa_reg_poly.of_flat
      -- Step 3: C(a) ∈ Q (since a ∈ q = Q.comap C)
      have hCa_mem_Q : Polynomial.C a ∈ Q := by
        rw [hq_def] at haq; exact haq
      -- C(a) maps to maximalIdeal(B[X]_Q)
      have hca_max : ca ∈ maximalIdeal BXQ := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hCa_mem_Q
      haveI := quotSMulTopLocalRing hca_max
      -- Step 4: The quotient B[X]_Q / C(a) is CM local
      -- It is isomorphic to ((B/(a))[X])_{Q'} for a suitable prime Q'
      -- B/(a) is CM (forward transfer) and Noetherian
      -- Q'.primeHeight ≤ d (height drops by ≥ 1)
      -- By IH, the localization is CM local
      -- Build the quotient ring (B/(a))[X] and show it's CM Noetherian
      set Ba := B ⧸ Ideal.span ({a} : Set B)
      haveI : IsNoetherianRing Ba := Ideal.Quotient.isNoetherianRing _
      haveI : IsCohenMacaulayRing Ba :=
        isCohenMacaulayRing_quotient_of_smulRegular ha_reg
      -- Build the prime Q' in Ba[X] corresponding to Q
      -- First, the quotient map B[X] → Ba[X]
      set π : Polynomial B →+* Polynomial Ba :=
        Polynomial.mapRingHom (Ideal.Quotient.mk (Ideal.span ({a} : Set B)))
      -- C(a) ∈ ker(π) since a ↦ 0 in Ba
      have hker_le_Q : Ideal.map Polynomial.C (Ideal.span ({a} : Set B)) ≤ Q := by
        rw [Ideal.map_span, Set.image_singleton]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hCa_mem_Q)
      -- The image of Q under π is a prime Q' (since ker ≤ Q)
      set Q' := Q.map π with hQ'_def
      haveI : Q'.IsPrime := by
        apply Ideal.map_isPrime_of_surjective (Polynomial.map_surjective _
          Ideal.Quotient.mk_surjective)
        rw [Polynomial.ker_mapRingHom, Ideal.mk_ker]
        exact hker_le_Q
      -- Build the isomorphism between the quotient and the localization
      -- QuotSMulTop ca BXQ ≃+* Localization.AtPrime Q'
      -- This follows from the localization-quotient commutation
      -- combined with B[X]/(C(a)) ≅ Ba[X]
      -- Establish the ring equiv between quotient-localization and
      -- localization of quotient polynomial ring
      have equiv : QuotSMulTop ca BXQ ≃+* Localization.AtPrime Q' := by
        -- Direct construction (same pattern as quotSMulTopLocalizationEquiv_of_mem
        -- but targeting Ba[X]_{Q'} directly via π).
        -- Forward: BXQ → Ba[X]_{Q'} via φ = algebraMap ∘ π, then quotient
        let φ : Polynomial B →+* Localization.AtPrime Q' :=
          (algebraMap (Polynomial Ba) (Localization.AtPrime Q')).comp π
        have hφ_units : ∀ s : Q.primeCompl, IsUnit (φ s) := by
          rintro ⟨s, hs⟩; show IsUnit ((algebraMap _ (Localization.AtPrime Q')) (π s))
          have : π s ∉ Q' := by
            intro hmem; apply hs
            have hcomap : (Q.map π).comap π = Q := by
              rw [Ideal.comap_map_of_surjective _ (Polynomial.map_surjective _
                Ideal.Quotient.mk_surjective)]
              have : Ideal.comap π ⊥ = Ideal.map Polynomial.C (Ideal.span ({a} : Set B)) := by
                ext f; simp only [Ideal.mem_comap, Ideal.mem_bot]
                rw [show π f = 0 ↔ f ∈ RingHom.ker π from Iff.rfl,
                    show RingHom.ker π = _ from Polynomial.ker_mapRingHom _, Ideal.mk_ker]
              rw [this, sup_eq_left.mpr hker_le_Q]
            exact hcomap ▸ Ideal.mem_comap.mpr hmem
          exact IsLocalization.map_units _ ⟨π s, Ideal.mem_primeCompl_iff.mpr this⟩
        let ψ₀ : BXQ →+* Localization.AtPrime Q' := IsLocalization.lift hφ_units
        have hψ₀_ca : ψ₀ ca = 0 := by
          show IsLocalization.lift hφ_units (algebraMap _ BXQ (Polynomial.C a)) = 0
          rw [IsLocalization.lift_eq]; show (algebraMap _ _) (π (Polynomial.C a)) = 0
          have : π (Polynomial.C a) = 0 := by
            show Polynomial.map (Ideal.Quotient.mk (Ideal.span ({a} : Set B))) (Polynomial.C a) = 0
            rw [Polynomial.map_C, Ideal.Quotient.eq_zero_iff_mem.mpr
              (Ideal.subset_span (Set.mem_singleton a)), map_zero]
          rw [this, map_zero]
        have hψ₀_ker : ∀ z ∈ (ca • ⊤ : Ideal BXQ), ψ₀ z = 0 := by
          intro z hz; obtain ⟨w, _, rfl⟩ := hz
          show ψ₀ (ca * w) = 0; rw [map_mul, hψ₀_ca, zero_mul]
        let ψ : QuotSMulTop ca BXQ →+* Localization.AtPrime Q' :=
          Ideal.Quotient.lift _ ψ₀ hψ₀_ker
        -- Backward: Ba[X]_{Q'} → QuotSMulTop via Ba[X] → QuotSMulTop
        have hca_zero : (algebraMap BXQ (QuotSMulTop ca BXQ)) ca = 0 := by
          show Submodule.Quotient.mk ca = 0; rw [Submodule.Quotient.mk_eq_zero]
          exact ⟨1, Submodule.mem_top, by simp⟩
        -- Ring hom Ba[X] → QuotSMulTop: use eval₂ with
        -- f : Ba → QuotSMulTop (coefficient map) and X ↦ image of X
        -- Build Ba → QuotSMulTop: send mk(b) ↦ quotient_image(C(b))
        let f_base : B →+* QuotSMulTop ca BXQ :=
          (algebraMap BXQ (QuotSMulTop ca BXQ)).comp
            ((algebraMap (Polynomial B) BXQ).comp Polynomial.C)
        have hf_base_ker : ∀ b ∈ Ideal.span ({a} : Set B), f_base b = 0 := by
          intro b hb; rw [Ideal.mem_span_singleton] at hb; obtain ⟨c, rfl⟩ := hb
          show (algebraMap BXQ _) ((algebraMap _ BXQ) (Polynomial.C (a * c))) = 0
          rw [Polynomial.C_mul, map_mul, map_mul, hca_zero, zero_mul]
        let f_coeff : Ba →+* QuotSMulTop ca BXQ :=
          Ideal.Quotient.lift _ f_base hf_base_ker
        -- Build Ba[X] → QuotSMulTop via Polynomial.eval₂RingHom
        let x_img : QuotSMulTop ca BXQ :=
          (algebraMap BXQ (QuotSMulTop ca BXQ)) ((algebraMap (Polynomial B) BXQ) Polynomial.X)
        let embed_Ba : Polynomial Ba →+* QuotSMulTop ca BXQ :=
          Polynomial.eval₂RingHom f_coeff x_img
        -- embed_Ba ∘ π = quotient ∘ algebraMap (check on generators)
        have hembed_comp : ∀ g : Polynomial B,
            embed_Ba (π g) = (algebraMap BXQ (QuotSMulTop ca BXQ)) (algebraMap _ BXQ g) := by
          intro g; show Polynomial.eval₂ f_coeff x_img (Polynomial.map _ g) = _
          rw [Polynomial.eval₂_map]
          show Polynomial.eval₂ (f_coeff.comp (Ideal.Quotient.mk _)) x_img g = _
          -- f_coeff ∘ mk = f_base = quotient ∘ algebraMap ∘ C
          -- So eval₂ (quotient ∘ algebraMap ∘ C) (quotient(algebraMap X)) g
          -- = quotient(algebraMap(eval₂ C X g)) = quotient(algebraMap(g))
          conv_lhs => rw [show f_coeff.comp (Ideal.Quotient.mk _) = f_base from
            Ideal.Quotient.lift_comp_mk _ _ _]
          -- f_base = (quot ∘ alg ∘ C) and x_img = quot(alg(X))
          -- So eval₂ f_base x_img g = (quot ∘ alg)(eval₂ C X g) = (quot ∘ alg)(g)
          rw [show f_base = ((algebraMap BXQ (QuotSMulTop ca BXQ)).comp
            (algebraMap _ BXQ)).comp Polynomial.C from rfl]
          rw [show x_img = ((algebraMap BXQ (QuotSMulTop ca BXQ)).comp
            (algebraMap _ BXQ)) Polynomial.X from rfl]
          rw [← Polynomial.hom_eval₂, Polynomial.eval₂_C_X, RingHom.comp_apply]
        have hembed_units : ∀ s : Q'.primeCompl, IsUnit (embed_Ba s) := by
          rintro ⟨s, hs⟩
          obtain ⟨g, rfl⟩ := Polynomial.map_surjective _
            Ideal.Quotient.mk_surjective s
          have hg_nmem : g ∉ Q := by
            intro hgQ; exact (Ideal.mem_primeCompl_iff.mp hs)
              (Ideal.mem_map_of_mem π hgQ)
          show IsUnit (embed_Ba (π g))
          rw [hembed_comp]
          exact (IsLocalization.map_units BXQ
            ⟨g, Ideal.mem_primeCompl_iff.mpr hg_nmem⟩).map _
        let χ : Localization.AtPrime Q' →+* QuotSMulTop ca BXQ :=
          IsLocalization.lift hembed_units
        -- ψ ∘ χ = id
        -- Key computation: χ(algebraMap f) = embed_Ba f, ψ₀(algebraMap g) = φ g
        have hχ_alg : ∀ f : Polynomial Ba,
            χ ((algebraMap (Polynomial Ba) (Localization.AtPrime Q')) f) = embed_Ba f :=
          fun f => RingHom.congr_fun (IsLocalization.lift_comp hembed_units) f
        have hψ₀_alg : ∀ g : Polynomial B, ψ₀ (algebraMap _ BXQ g) = φ g :=
          fun g => RingHom.congr_fun (IsLocalization.lift_comp hφ_units) g
        -- Core computation: for any g : B[X],
        -- ψ(embed_Ba(π g)) = ψ(quot(alg g)) = ψ₀(alg g) = φ(g) = algebraMap(π g)
        have hψ_embed_π : ∀ g : Polynomial B,
            ψ (embed_Ba (π g)) =
            (algebraMap (Polynomial Ba) (Localization.AtPrime Q')) (π g) := by
          intro g; rw [hembed_comp]
          change Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _
            ((algebraMap _ BXQ) g)) = _
          rw [Ideal.Quotient.lift_mk, hψ₀_alg]; rfl
        have hψχ : ψ.comp χ = RingHom.id (Localization.AtPrime Q') := by
          apply IsLocalization.ringHom_ext Q'.primeCompl
          -- Check on algebraMap Ba[X] → Localization.AtPrime Q'.
          -- By Polynomial.ringHom_ext: check C and X.
          apply Polynomial.ringHom_ext
          · -- Check on C(b) for b : Ba. Lift b = mk b₀.
            intro b; obtain ⟨b₀, rfl⟩ := Ideal.Quotient.mk_surjective b
            simp only [RingHom.comp_apply, RingHom.id_apply]
            rw [hχ_alg, show Polynomial.C (Ideal.Quotient.mk _ b₀) = π (Polynomial.C b₀) from by
              show Polynomial.C _ = Polynomial.map _ (Polynomial.C b₀)
              rw [Polynomial.map_C], hψ_embed_π]
          · -- Check on X
            simp only [RingHom.comp_apply, RingHom.id_apply]
            rw [hχ_alg, show (Polynomial.X : Polynomial Ba) = π Polynomial.X from by
              show Polynomial.X = Polynomial.map _ Polynomial.X
              rw [Polynomial.map_X], hψ_embed_π]
        have hψ_surj : Function.Surjective ψ :=
          fun y => ⟨χ y, by simpa using RingHom.congr_fun hψχ y⟩
        -- ψ injective: same kernel argument as quotSMulTopLocalizationEquiv_of_mem
        have hψ_inj : Function.Injective ψ := by
          intro q1 q2 hq
          obtain ⟨z1, rfl⟩ := Submodule.Quotient.mk_surjective (p := ca • ⊤) q1
          obtain ⟨z2, rfl⟩ := Submodule.Quotient.mk_surjective (p := ca • ⊤) q2
          rw [Submodule.Quotient.eq]
          change Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ z1) =
            Ideal.Quotient.lift _ ψ₀ hψ₀_ker (Ideal.Quotient.mk _ z2) at hq
          rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hq
          have hψ₀_diff : ψ₀ (z1 - z2) = 0 := by rw [map_sub, sub_eq_zero]; exact hq
          obtain ⟨⟨f, s⟩, hz⟩ := IsLocalization.mk'_surjective Q.primeCompl (z1 - z2)
          have hz' : IsLocalization.mk' BXQ f s = z1 - z2 := hz
          rw [← hz'] at hψ₀_diff ⊢
          -- ψ₀(mk'(f, s)) = mk'(π f, ⟨π s, ...⟩) in Localization.AtPrime Q'
          have hs_nmem : (s : Polynomial B) ∉ Q := s.prop
          have hπs_nmem : π (s : Polynomial B) ∉ Q' := by
            intro hmem; apply hs_nmem
            have hcomap : (Q.map π).comap π = Q := by
              rw [Ideal.comap_map_of_surjective _ (Polynomial.map_surjective _
                Ideal.Quotient.mk_surjective)]
              have : Ideal.comap π ⊥ = Ideal.map Polynomial.C (Ideal.span ({a} : Set B)) := by
                ext g; simp only [Ideal.mem_comap, Ideal.mem_bot]
                rw [show π g = 0 ↔ g ∈ RingHom.ker π from Iff.rfl,
                    show RingHom.ker π = _ from Polynomial.ker_mapRingHom _, Ideal.mk_ker]
              rw [this, sup_eq_left.mpr hker_le_Q]
            have hmem' : (s : Polynomial B) ∈ (Q.map π).comap π :=
              Ideal.mem_comap.mpr (hQ'_def ▸ hmem)
            rwa [hcomap] at hmem'
          have hψ₀_val : ψ₀ (IsLocalization.mk' BXQ f s) =
              IsLocalization.mk' (Localization.AtPrime Q') (π f)
                ⟨π s, Ideal.mem_primeCompl_iff.mpr hπs_nmem⟩ := by
            show IsLocalization.lift hφ_units (IsLocalization.mk' BXQ f s) = _
            rw [IsLocalization.lift_mk'_spec]; simp only [φ, RingHom.comp_apply]
            exact (IsLocalization.mk'_spec' (Localization.AtPrime Q') (π f)
              ⟨π s, _⟩).symm
          rw [hψ₀_val, IsLocalization.mk'_eq_zero_iff] at hψ₀_diff
          obtain ⟨⟨t', ht'⟩, ht'f⟩ := hψ₀_diff
          obtain ⟨t, rfl⟩ := Polynomial.map_surjective _
            Ideal.Quotient.mk_surjective t'
          have ht_nmem : t ∉ Q := by
            intro htQ; exact (Ideal.mem_primeCompl_iff.mp ht')
              (Ideal.mem_map_of_mem π htQ)
          -- π(t) * π(f) = 0, so t * f ∈ ker π = map C (span{a})
          have htf_ker : t * f ∈ Ideal.map Polynomial.C (Ideal.span ({a} : Set B)) := by
            have : π (t * f) = 0 := by rw [map_mul]; exact ht'f
            rwa [show π (t * f) = 0 ↔ t * f ∈ RingHom.ker π from Iff.rfl,
                 show RingHom.ker π = _ from Polynomial.ker_mapRingHom _,
                 Ideal.mk_ker] at this
          -- map C (span{a}) = span{C a}
          rw [Ideal.map_span, Set.image_singleton] at htf_ker
          rw [Ideal.mem_span_singleton] at htf_ker
          obtain ⟨c, hc⟩ := htf_ker
          -- mk'(f, s) = ca * mk'(c, ⟨t, _⟩ * s) ∈ ca • ⊤
          have key : IsLocalization.mk' BXQ f s =
              ca * IsLocalization.mk' BXQ c
                (⟨t, Ideal.mem_primeCompl_iff.mpr ht_nmem⟩ * s : Q.primeCompl) := by
            rw [show ca = algebraMap (Polynomial B) BXQ (Polynomial.C a) from rfl,
                IsLocalization.mul_mk'_eq_mk'_of_mul]
            apply IsLocalization.mk'_eq_of_eq
            show ↑s * (Polynomial.C a * c) = ↑(⟨t, _⟩ * s : Q.primeCompl) * f
            simp only [Submonoid.coe_mul]; rw [← hc]; ring
          rw [key]
          exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
        exact RingEquiv.ofBijective ψ ⟨hψ_inj, hψ_surj⟩
      -- Compute Q'.primeHeight ≤ d
      have hQ'_ht : Q'.primeHeight ≤ d := by
        have hdim_quot := ringKrullDim_quotSMulTop_succ_eq_ringKrullDim hCa_reg hca_max
        have hdim_BXQ := IsLocalization.AtPrime.ringKrullDim_eq_height Q BXQ
        rw [Ideal.height_eq_primeHeight] at hdim_BXQ
        have hdim_Q' :=
          (ringKrullDim_eq_of_ringEquiv equiv).trans
            (IsLocalization.AtPrime.ringKrullDim_eq_height Q' (Localization.AtPrime Q'))
        rw [Ideal.height_eq_primeHeight] at hdim_Q'
        have h1 : (Q'.primeHeight : WithBot ℕ∞) + 1 ≤ ↑(d + 1) := by
          calc (Q'.primeHeight : WithBot ℕ∞) + 1
              = ringKrullDim (QuotSMulTop ca BXQ) + 1 := by rw [hdim_Q']
            _ = ringKrullDim BXQ := hdim_quot
            _ = Q.primeHeight := hdim_BXQ
            _ ≤ d + 1 := by exact_mod_cast hd
        -- Q'.primeHeight + 1 ≤ d + 1 in WithBot ℕ∞ implies Q'.primeHeight ≤ d in ℕ∞
        have h2 : (Q'.primeHeight : ℕ∞) + 1 ≤ (d : ℕ∞) + 1 := by exact_mod_cast h1
        exact (WithTop.add_le_add_iff_right ENat.one_ne_top).mp h2
      -- Apply ih: (B/(a))[X]_{Q'} is CM local
      haveI : IsNoetherianRing (Polynomial Ba) := Polynomial.isNoetherianRing
      haveI : IsNoetherianRing (Localization.AtPrime Q') :=
        IsLocalization.isNoetherianRing Q'.primeCompl _ inferInstance
      haveI hCM_loc := ih Ba Q' hQ'_ht
      -- Transfer CM through the ring equiv to the quotient
      haveI : IsCohenMacaulayLocalRing (QuotSMulTop ca BXQ) :=
        isCohenMacaulayLocalRing_of_ringEquiv' hCM_loc equiv.symm
      -- Apply converse CM transfer
      exact isCohenMacaulayLocalRing_of_regular_quotient hCa_reg hca_max
        IsCohenMacaulayLocalRing.depth_eq_dim
    · -- Case: q has height 0 (q is a minimal prime of B).
      -- By going-down (B → B[X] is flat): Q.height = q.height + fiber_height.
      -- Since q.height = 0, Q.height = fiber_height.
      -- Step 1: Derive q.primeHeight = 0.
      have hq_ht0 : q.primeHeight = 0 := by
        rw [not_lt] at hq_pos
        have h : q.height ≤ 0 := by exact_mod_cast hq_pos
        rwa [Ideal.height_eq_primeHeight, nonpos_iff_eq_zero] at h
      -- Step 2: Show Q.primeHeight ≤ 1 via the height inequality + fiber argument.
      haveI : Q.LiesOver q := ⟨by rw [hq_def, Ideal.under_def, Polynomial.algebraMap_eq]⟩
      -- Fiber prime in B[X] / (q.map C)
      set Q_fiber := Q.map (Ideal.Quotient.mk (q.map (Polynomial.C : B →+* Polynomial B)))
      -- B/q is a domain
      haveI : IsDomain (B ⧸ q) := Ideal.Quotient.isDomain q
      haveI : IsNoetherianRing (B ⧸ q) := Ideal.Quotient.isNoetherianRing q
      -- Ring equiv: B[X]/(q·B[X]) ≃ (B/q)[X]
      -- Note: polynomialQuotientEquivQuotientPolynomial goes (B/q)[X] → B[X]/(q·B[X])
      set e := (Ideal.polynomialQuotientEquivQuotientPolynomial q).symm
      -- Image of Q_fiber under e is a prime of (B/q)[X]
      set Q_bar := Q_fiber.map e with hQ_bar_def
      -- Key: q.map C ≤ Q (since Q.comap C = q ⊇ q)
      have hker_le_Q : q.map (Polynomial.C : B →+* Polynomial B) ≤ Q := by
        rw [Ideal.map_le_iff_le_comap, hq_def]
      haveI : Q_fiber.IsPrime := by
        apply Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        rw [Ideal.mk_ker]; exact hker_le_Q
      haveI : Q_bar.IsPrime := Ideal.map_isPrime_of_equiv e
      -- Q_bar lies over ⊥ in B/q
      -- Key: q.map C ≤ Q (since Q.comap C = q ⊇ q)
      have hker_le_Q : q.map (Polynomial.C : B →+* Polynomial B) ≤ Q := by
        rw [Ideal.map_le_iff_le_comap, hq_def]
      have hQ_bar_comap : Q_bar.comap (Polynomial.C : B ⧸ q →+* Polynomial (B ⧸ q)) = ⊥ := by
        rw [eq_bot_iff]; intro x hx; rw [Ideal.mem_comap] at hx
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        -- C(mk b) ∈ Q_bar means e.symm(C(mk b)) ∈ Q_fiber
        have hmem : e.symm (Polynomial.C (Ideal.Quotient.mk q b)) ∈ Q_fiber := by
          have hx' := hx; rw [hQ_bar_def] at hx'
          rw [Ideal.mem_map_iff_of_surjective _ e.surjective] at hx'
          obtain ⟨w, hw, heq⟩ := hx'; rwa [← heq, e.symm_apply_apply]
        have he_symm : e.symm (Polynomial.C (Ideal.Quotient.mk q b)) =
            Ideal.Quotient.mk _ (Polynomial.C b) := by
          show (Ideal.polynomialQuotientEquivQuotientPolynomial q)
            (Polynomial.C (Ideal.Quotient.mk q b)) = _
          rw [← Polynomial.map_C, Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk]
        rw [he_symm] at hmem
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hmem
        obtain ⟨g, hgQ, hg_eq⟩ := hmem
        have hCb_mem_Q : Polynomial.C b ∈ Q := by
          have hdiff : g - Polynomial.C b ∈ Ideal.map (Polynomial.C : B →+* _) q := by
            rw [← Ideal.Quotient.eq]; exact hg_eq
          have := Q.sub_mem hgQ (hker_le_Q hdiff)
          rwa [sub_sub_cancel] at this
        simp only [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
        exact hq_def ▸ hCb_mem_Q
      -- Fiber height ≤ 1 (either ⊥ or height 1 by PID argument on domain)
      have hQ_fiber_ht : Q_fiber.height ≤ 1 := by
        rw [show Q_fiber.height = Q_bar.height from (e.height_map Q_fiber).symm]
        by_cases hQ_bar_bot : Q_bar = ⊥
        · simp [hQ_bar_bot]
        · exact le_of_eq (height_eq_one_of_comap_C_eq_bot Q_bar hQ_bar_bot hQ_bar_comap)
      -- Height inequality: Q.height ≤ q.height + fiber_height
      have h_ht_ineq :=
        Ideal.height_le_height_add_of_liesOver (S := Polynomial B) q Q
      have hq_ht_val : q.height = 0 := by rwa [Ideal.height_eq_primeHeight]
      have hQ_ht_le : Q.height ≤ 1 := by
        calc Q.height ≤ q.height + Q_fiber.height := h_ht_ineq
          _ ≤ 0 + 1 := add_le_add (le_of_eq hq_ht_val) hQ_fiber_ht
          _ = 1 := by ring
      have hQ_primeHeight_le : Q.primeHeight ≤ 1 := by
        have := Ideal.height_eq_primeHeight (I := Q)
        rw [this] at hQ_ht_le; exact_mod_cast hQ_ht_le
      -- Q.primeHeight = 1 (since > 0)
      have hQ_ht1 : Q.primeHeight = 1 := le_antisymm hQ_primeHeight_le (by
        rw [ENat.one_le_iff_ne_zero]; exact hQ_ht0)
      -- If d ≥ 1: Q.primeHeight ≤ d, apply IH
      by_cases hd1 : 1 ≤ d
      · exact ih B Q (by rw [hQ_ht1]; exact_mod_cast hd1)
      · -- d = 0, Q.primeHeight = 1: direct argument via X or C(a)
        push_neg at hd1; interval_cases d
        -- dim(B[X]_Q) = 1. Build a 1-element WR sequence.
        -- X is always regular on B[X] (degree argument).
        -- If X ∈ Q: use X. If X ∉ Q: X is a unit, use C(a) for suitable a.
        by_cases hXQ : (Polynomial.X : Polynomial B) ∈ Q
        · -- X ∈ Q: X is regular on B[X] (for any ring B)
          have hX_reg : IsSMulRegular (Polynomial B) (Polynomial.X : Polynomial B) := by
            intro f g hfg
            -- X • f = X • g means X * f = X * g (smul = mul for ring elements)
            have hmul : Polynomial.X * f = Polynomial.X * g := hfg
            ext n
            have := congrArg (Polynomial.coeff · (n + 1)) hmul
            simpa [Polynomial.coeff_X_mul] using this
          set xQ := algebraMap (Polynomial B) (Localization.AtPrime Q) Polynomial.X
          have hxQ_reg : IsSMulRegular (Localization.AtPrime Q) xQ := hX_reg.of_flat
          have hxQ_mem : xQ ∈ maximalIdeal (Localization.AtPrime Q) := by
            rw [← Localization.AtPrime.map_eq_maximalIdeal]
            exact Ideal.mem_map_of_mem _ hXQ
          have hreg1 : IsWeaklyRegular (Localization.AtPrime Q) [xQ] :=
            (isWeaklyRegular_cons_iff _ xQ []).mpr
              ⟨hxQ_reg, IsWeaklyRegular.nil _ _⟩
          have hmem1 : ∀ r ∈ [xQ], r ∈ maximalIdeal (Localization.AtPrime Q) := by
            intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; exact hxQ_mem
          exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim hreg1 hmem1 (by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q _, Ideal.height_eq_primeHeight,
                hQ_ht1]; rfl)
        · -- X ∉ Q: find a regular element of Q in B[X], and conclude CM from
          -- dim = 1. Q has primeHeight 1, so for every p ∈ Ass(B) we have
          -- Q ⊄ Ideal.map C p (because q = Q.comap C is a minimal prime and p
          -- is a minimal prime; if Q ≤ map C p then q ≤ p, hence q = p and
          -- Q = map C q, but then Q would be a minimal prime of B[X] with
          -- primeHeight 0, contradicting primeHeight 1). Prime avoidance then
          -- gives f ∈ Q with all coefficients outside every associated prime,
          -- and McCoy's theorem upgrades this to full regularity on B[X].
          have ⟨g, hg_reg, hg_mem⟩ :
              ∃ g : Polynomial B, IsSMulRegular (Polynomial B) g ∧ g ∈ Q := by
            have hq_min : q ∈ minimalPrimes B :=
              Ideal.primeHeight_eq_zero_iff.mp hq_ht0
            -- `(Ideal.map C I).comap C = I` for any ideal `I ⊆ B`, using that
            -- `Polynomial.C` is injective and `Ideal.mem_map_C_iff`.
            have hcomap_map_C : ∀ (I : Ideal B),
                (Ideal.map Polynomial.C I).comap Polynomial.C = I := by
              intro I
              apply le_antisymm
              · intro b hb
                rw [Ideal.mem_comap, Ideal.mem_map_C_iff] at hb
                have := hb 0
                simpa using this
              · intro b hb
                rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
                intro n
                by_cases hn : n = 0
                · simpa [hn] using hb
                · simp [Polynomial.coeff_C, hn, I.zero_mem]
            -- Step 1: Q ⊄ Ideal.map C p for every p ∈ Ass(B).
            have hQ_not_le : ∀ p ∈ associatedPrimes B B,
                ¬ Q ≤ Ideal.map Polynomial.C p := by
              intro p hp hle
              haveI hp_prime : p.IsPrime :=
                (show IsAssociatedPrime p B from hp).isPrime
              haveI : p.primeHeight = 0 → p ∈ minimalPrimes B :=
                Ideal.primeHeight_eq_zero_iff.mp
              have hp_ht : p.primeHeight = 0 :=
                primeHeight_zero_of_mem_associatedPrimes_of_isCohenMacaulayRing hp
              have hp_min : p ∈ minimalPrimes B :=
                Ideal.primeHeight_eq_zero_iff.mp hp_ht
              -- Derive q ≤ p.
              have hqp : q ≤ p := by
                have hcomap_le :
                    Q.comap Polynomial.C ≤ (Ideal.map Polynomial.C p).comap Polynomial.C :=
                  Ideal.comap_mono hle
                rw [hcomap_map_C] at hcomap_le
                exact hq_def ▸ hcomap_le
              -- Both q and p are minimal primes; q ≤ p forces q = p.
              have hqeq : q = p :=
                le_antisymm hqp (hp_min.2 ⟨‹q.IsPrime›, bot_le⟩ hqp)
              -- Q ≤ Ideal.map C q, and the reverse already holds via hker_le_Q.
              have hle' : Q ≤ Ideal.map Polynomial.C q := hqeq ▸ hle
              have hQ_eq : Q = Ideal.map Polynomial.C q := le_antisymm hle' hker_le_Q
              -- Show Q is a minimal prime of B[X]: any strictly smaller prime
              -- would contract to a prime strictly below q, contradicting
              -- minimality of q.
              have hQ_min : Q ∈ minimalPrimes (Polynomial B) := by
                refine ⟨⟨inferInstance, bot_le⟩, ?_⟩
                rintro P' ⟨hP'_prime, -⟩ hP'_le
                haveI := hP'_prime
                have hcomap_le' : P'.comap Polynomial.C ≤ q := by
                  have : P'.comap Polynomial.C ≤ Q.comap Polynomial.C :=
                    Ideal.comap_mono hP'_le
                  rwa [← hq_def] at this
                have hcomap_eq : P'.comap Polynomial.C = q :=
                  le_antisymm hcomap_le'
                    (hq_min.2 ⟨Ideal.IsPrime.comap Polynomial.C, bot_le⟩ hcomap_le')
                rw [hQ_eq, Ideal.map_le_iff_le_comap]
                exact hcomap_eq.ge
              have hQ_ht0' : Q.primeHeight = 0 :=
                Ideal.primeHeight_eq_zero_iff.mpr hQ_min
              exact absurd (hQ_ht1.symm.trans hQ_ht0') (by decide)
            -- Step 2: prime avoidance.
            have hfin := associatedPrimes.finite B B
            have hQ_not_sub :
                ¬ ((Q : Set (Polynomial B)) ⊆
                  ⋃ p ∈ associatedPrimes B B,
                    (Ideal.map Polynomial.C p : Set (Polynomial B))) := by
              intro hsub
              have himg_sub : (Q : Set (Polynomial B)) ⊆
                  ⋃ I ∈ (fun p => Ideal.map Polynomial.C p) '' associatedPrimes B B,
                    (I : Set (Polynomial B)) := by
                intro f hf
                obtain ⟨p, hp, hfp⟩ := Set.mem_iUnion₂.mp (hsub hf)
                exact Set.mem_iUnion₂.mpr
                  ⟨Ideal.map Polynomial.C p, ⟨p, hp, rfl⟩, hfp⟩
              have himg_fin : (Set.image
                  (fun p : Ideal B => Ideal.map Polynomial.C p)
                  (associatedPrimes B B)).Finite := hfin.image _
              rw [Ideal.subset_union_prime_finite himg_fin 0 0 (by
                rintro I ⟨p, hp, rfl⟩ _ _
                haveI : p.IsPrime := (show IsAssociatedPrime p B from hp).isPrime
                exact (Ideal.isPrime_map_C_iff_isPrime p).mpr ‹_›)] at himg_sub
              obtain ⟨I, ⟨p, hp, rfl⟩, hle⟩ := himg_sub
              exact hQ_not_le p hp hle
            obtain ⟨g, hgQ, hg_not_mem⟩ := Set.not_subset.mp hQ_not_sub
            refine ⟨g, ?_, hgQ⟩
            -- Step 3: regularity via McCoy.  If `b • g = 0` with `b ≠ 0`, then
            -- `Ann_B(b)` is contained in some associated prime, so all
            -- coefficients of `g` lie in that prime, contradicting prime
            -- avoidance.
            have h_nzd : g ∈ nonZeroDivisors (Polynomial B) := by
              rw [Polynomial.mem_nonZeroDivisors_iff]
              intro b hb
              by_contra hbne
              obtain ⟨p, hp_assoc, hAnn_le⟩ :=
                exists_le_isAssociatedPrime_of_isNoetherianRing B b hbne
              have hp_mem : p ∈ associatedPrimes B B := hp_assoc
              apply hg_not_mem
              refine Set.mem_iUnion₂.mpr ⟨p, hp_mem, ?_⟩
              show g ∈ Ideal.map Polynomial.C p
              rw [Ideal.mem_map_C_iff]
              intro n
              apply hAnn_le
              rw [Submodule.mem_colon_singleton]
              show Polynomial.coeff g n * b = 0
              have hcoeff : (b • g).coeff n = b * Polynomial.coeff g n := by
                rw [Polynomial.coeff_smul, smul_eq_mul]
              rw [mul_comm, ← hcoeff, hb, Polynomial.coeff_zero]
            exact (isRegular_iff_mem_nonZeroDivisors.mpr h_nzd).left.isSMulRegular
          -- Regular → regular on localization (flat base change)
          set gQ := algebraMap (Polynomial B) (Localization.AtPrime Q) g
          have hgQ_reg : IsSMulRegular (Localization.AtPrime Q) gQ := hg_reg.of_flat
          -- g ∈ Q → gQ ∈ maxIdeal
          have hgQ_mem : gQ ∈ maximalIdeal (Localization.AtPrime Q) := by
            rw [← Localization.AtPrime.map_eq_maximalIdeal]
            exact Ideal.mem_map_of_mem _ hg_mem
          -- 1-element WR sequence of length 1 = dim → CM
          have hreg1 : IsWeaklyRegular (Localization.AtPrime Q) [gQ] :=
            (isWeaklyRegular_cons_iff _ gQ []).mpr
              ⟨hgQ_reg, IsWeaklyRegular.nil _ _⟩
          have hmem1 : ∀ r ∈ [gQ], r ∈ maximalIdeal (Localization.AtPrime Q) := by
            intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; exact hgQ_mem
          exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim hreg1 hmem1 (by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q _, Ideal.height_eq_primeHeight,
                hQ_ht1]; rfl)

/-- **Polynomial CM extension for domains**: if `A` is a CM domain, then
`Polynomial A` is a CM ring. -/
theorem isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing_domain
    [IsCohenMacaulayRing A] :
    IsCohenMacaulayRing (Polynomial A) where
  CM_localize P _ := by
    haveI : IsDomain (Polynomial A) := inferInstance
    haveI : IsNoetherianRing (Polynomial A) := inferInstance
    haveI : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    by_cases hX : (Polynomial.X : Polynomial A) ∈ P
    · -- Case X ∈ P: use converse CM transfer with X
      -- X is regular (domain, X ≠ 0)
      set Rp := Localization.AtPrime P
      have hXreg : IsSMulRegular Rp (algebraMap _ Rp (X : Polynomial A)) := by
        haveI : IsDomain Rp :=
          IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
        have hne : algebraMap (Polynomial A) Rp X ≠ 0 :=
          fun h => Polynomial.X_ne_zero (IsLocalization.injective _
            P.primeCompl_le_nonZeroDivisors (by rw [h, map_zero]))
        intro a b hab; exact mul_left_cancel₀ hne hab
      set aX := algebraMap (Polynomial A) Rp X with haX_def
      have hXm : aX ∈ maximalIdeal Rp := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hX
      haveI := quotSMulTopLocalRing hXm
      -- QuotSMulTop X (A[X]_P) is CM because it's isomorphic to A_{P̄}
      -- where P̄ is the image of P in A[X]/(X) ≅ A, and A is CM
      have hCM_quot : @ringKrullDim (QuotSMulTop aX Rp) _ =
          ↑(@ringDepth (QuotSMulTop aX Rp) _ (quotSMulTopLocalRing hXm)) := by
        -- Use the ring equiv QuotSMulTop aX Rp ≃+* Localization.AtPrime (P.comap C)
        set p := P.comap (Polynomial.C : A →+* Polynomial A) with hp_def
        haveI : p.IsPrime := Ideal.IsPrime.comap Polynomial.C
        haveI : IsNoetherianRing (Localization.AtPrime p) :=
          IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
        -- A_{P∩A} is CM local
        haveI hCM_Ap : IsCohenMacaulayLocalRing (Localization.AtPrime p) :=
          IsCohenMacaulayRing.CM_localize p
        -- Transfer CM through ring equiv
        set e := quotSMulTopPolynomialLocalizationEquiv P hX
        haveI : IsCohenMacaulayLocalRing (QuotSMulTop aX Rp) :=
          isCohenMacaulayLocalRing_of_ringEquiv' hCM_Ap e.symm
        exact IsCohenMacaulayLocalRing.depth_eq_dim
      exact isCohenMacaulayLocalRing_of_regular_quotient hXreg hXm hCM_quot
    · -- Case X ∉ P: use converse CM transfer via induction on height(P).
      -- Base case: P = ⊥ → fraction field → dim 0 → CM.
      -- Inductive step: pick nonzero f ∈ P, which is regular (domain),
      -- and apply converse CM transfer.
      haveI : IsDomain (Localization.AtPrime P) :=
        IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
      -- Handle P = ⊥ (height 0): fraction field, dimension 0, CM.
      by_cases hP : P = ⊥
      · apply isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P),
            Ideal.height_eq_primeHeight]
        have : P.primeHeight = 0 := Ideal.primeHeight_eq_zero_iff.mpr (by
          rw [IsDomain.minimalPrimes_eq_singleton_bot, Set.mem_singleton_iff]; exact hP)
        simp [this]
      · -- P ≠ ⊥ and X ∉ P: further split on whether p = P ∩ A is ⊥.
        set p := P.comap (Polynomial.C : A →+* Polynomial A) with hp_def
        haveI : p.IsPrime := Ideal.IsPrime.comap Polynomial.C
        by_cases hp : p = ⊥
        · -- p = ⊥: P lies over (0), so height(P) = 1 (prime of height 1
          -- in Frac(A)[X]). A[X]_P is a 1-dimensional local domain, hence CM
          -- (any nonzero element in the maximal ideal is regular).
          -- Get a nonzero element of P
          have hPne : ∃ f ∈ P, f ≠ (0 : Polynomial A) := by
            by_contra h
            push_neg at h
            apply hP
            ext f; simp only [Ideal.mem_bot]
            exact ⟨fun hf => h f hf, fun hf => by rw [hf]; exact P.zero_mem⟩
          obtain ⟨f, hfP, hfne⟩ := hPne
          -- f maps to a nonzero element of maximalIdeal(A[X]_P)
          set af := algebraMap (Polynomial A) (Localization.AtPrime P) f
          have haf_ne : af ≠ 0 := by
            intro h
            exact hfne (IsLocalization.injective (Localization.AtPrime P)
              P.primeCompl_le_nonZeroDivisors (show algebraMap _ _ f = algebraMap _ _ 0 by
                rw [map_zero]; exact h))
          have haf_mem : af ∈ maximalIdeal (Localization.AtPrime P) := by
            rw [← Localization.AtPrime.map_eq_maximalIdeal]
            exact Ideal.mem_map_of_mem _ hfP
          -- In a domain, nonzero implies SMulRegular
          have haf_reg : IsSMulRegular (Localization.AtPrime P) af := by
            intro a b hab; exact mul_left_cancel₀ haf_ne hab
          -- [af] is a weakly regular sequence of length 1
          have hreg1 : IsWeaklyRegular (Localization.AtPrime P) [af] :=
            (isWeaklyRegular_cons_iff _ af []).mpr
              ⟨haf_reg, IsWeaklyRegular.nil _ _⟩
          have hmem1 : ∀ r ∈ [af], r ∈ maximalIdeal (Localization.AtPrime P) := by
            intro r hr; simp only [List.mem_singleton] at hr; rw [hr]; exact haf_mem
          -- height(P) = 1: P lies over ⊥ in A, so it corresponds to a
          -- nonzero prime of (FractionRing A)[X] (a PID), hence has height 1.
          have hP_ht : P.height = 1 :=
            height_eq_one_of_comap_C_eq_bot P hP (hp_def ▸ hp)
          exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim hreg1 hmem1 (by
            rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P),
                hP_ht]; rfl)
        · -- p ≠ ⊥ and X ∉ P: use the general CM polynomial localization lemma.
          -- Extract height(P) as a natural number for the induction.
          obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (Ideal.primeHeight_ne_top P)
          exact cm_localize_polynomial_of_cm_aux n A P (le_of_eq hn.symm)

end PolynomialExtension

/-! ### MvPolynomial over fields -/

section MvPolynomial

variable (K : Type u) [Field K]

set_option maxHeartbeats 400000 in
/-- **Multivariate polynomial rings over fields are Cohen-Macaulay.**

Proof by induction on the number of variables using `MvPolynomial.finSuccEquiv`. -/
theorem isCohenMacaulayRing_mvPolynomial_field (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) K) := by
  induction n with
  | zero =>
    -- MvPolynomial (Fin 0) K ≅ K, which is a CM field
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    let e := (MvPolynomial.isEmptyAlgEquiv K (Fin 0)).toRingEquiv
    -- Transfer the CM property from K through the ring equivalence
    constructor; intro p _
    haveI : IsNoetherianRing (MvPolynomial (Fin 0) K) :=
      MvPolynomial.isNoetherianRing
    haveI : IsNoetherianRing (Localization.AtPrime p) :=
      IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
    -- dim(MvPolynomial (Fin 0) K) = 0
    apply isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
    have hdim0 : ringKrullDim (MvPolynomial (Fin 0) K) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing (R := K),
          ringKrullDim_eq_zero_of_isField (Field.toIsField K)]; simp
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p _]
    apply le_antisymm
    · calc (p.height : WithBot ℕ∞) ≤ ringKrullDim _ := by
            rw [Ideal.height_eq_primeHeight]; exact Ideal.primeHeight_le_ringKrullDim
        _ = 0 := hdim0
    · rw [Ideal.height_eq_primeHeight]; exact_mod_cast zero_le _
  | succ n ih =>
    -- MvPolynomial (Fin (n+1)) K ≃ₐ Polynomial (MvPolynomial (Fin n) K)
    haveI := ih
    haveI : IsDomain (MvPolynomial (Fin n) K) := inferInstance
    haveI : IsNoetherianRing (MvPolynomial (Fin n) K) := MvPolynomial.isNoetherianRing
    -- The polynomial ring over a CM domain is CM
    haveI : IsCohenMacaulayRing (Polynomial (MvPolynomial (Fin n) K)) :=
      isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing_domain
    -- Transfer through the algebra equivalence finSuccEquiv
    exact isCohenMacaulayRing_of_ringEquiv (MvPolynomial.finSuccEquiv K n).toRingEquiv.symm

end MvPolynomial

/-! ### Polynomial ring over a general CM Noetherian ring is CM

This section proves the general (no IsDomain assumption) theorem that
`R[X]` is Cohen-Macaulay when `R` is a Noetherian CM ring. This backports
mathlib PR #28599 (Nailin Guan, Yongle Hu) to the v4.28.0 API of this project.

The key differences from upstream:
- Our `ringDepth` is defined directly as the sSup of regular sequence lengths,
  so we skip the `depth_eq_sSup_length_regular` rewrite.
- We use `isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim` (feeding it
  an explicit regular sequence of length `= dim`) instead of the upstream
  `isCohenMacaulayLocalRing_of_ringKrullDim_le_depth`. -/

section PolynomialGeneralCM

open IsLocalRing RingTheory.Sequence Polynomial Ideal

variable (R : Type u) [CommRing R]

/-- In a field polynomial ring, any nonzero ideal contains a monic element.
This is the translation of upstream `Polynomial.exist_monic_mem`. -/
private lemma polynomial_exist_monic_mem {F : Type u} [Field F] {I : Ideal F[X]} (ne : I ≠ ⊥) :
    ∃ f ∈ I, f.Monic := by
  obtain ⟨g, gmem, gne⟩ : ∃ g ∈ I, g ≠ 0 := by
    by_contra!
    exact ne ((Submodule.eq_bot_iff I).mpr this)
  refine ⟨C g.leadingCoeff⁻¹ * g, mul_mem_left I (C g.leadingCoeff⁻¹) gmem, ?_⟩
  simpa [Monic] using inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr gne)

/-- Extract a weakly regular sequence in the maximal ideal witnessing the depth,
for a CM Noetherian local ring. Returns `rs` with `rs.length = ringKrullDim R`
as a natural number. -/
private lemma exists_weaklyRegular_length_eq_ringKrullDim_of_isCohenMacaulayLocalRing
    [IsNoetherianRing R] [IsCohenMacaulayLocalRing R] :
    ∃ (rs : List R), IsWeaklyRegular R rs ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧
      ringKrullDim R = (rs.length : ℕ∞) := by
  -- ringDepth R = sSup of lengths of regular sequences in the maximal ideal.
  -- Claim: this sSup is attained.
  have hne : {(n : ℕ∞) | ∃ (rs : List R),
      (rs.length : ℕ∞) = n ∧ IsWeaklyRegular R rs ∧
      ∀ r ∈ rs, r ∈ maximalIdeal R}.Nonempty :=
    ⟨0, [], rfl, IsWeaklyRegular.nil R R, fun _ h => nomatch h⟩
  -- ringDepth R < ⊤ in ℕ∞ (from ringDepth ≤ ringKrullDim and ringKrullDim < ⊤)
  have hdim_lt : ringKrullDim R < (⊤ : WithBot ℕ∞) := ringKrullDim_lt_top
  have hdepth_le_dim : (ringDepth R : WithBot ℕ∞) ≤ ringKrullDim R :=
    ringDepth_le_ringKrullDim R
  have hdepth_lt_top : ringDepth R < (⊤ : ℕ∞) := by
    -- ringDepth R ≤ ringKrullDim R < ⊤, so ringDepth R < ⊤ in ℕ∞
    have h1 : (ringDepth R : WithBot ℕ∞) < ⊤ := lt_of_le_of_lt hdepth_le_dim hdim_lt
    -- h1 : (↑(ringDepth R) : WithBot ℕ∞) < ⊤
    -- Deduce ringDepth R < ⊤
    by_contra h
    push_neg at h
    have : ringDepth R = ⊤ := top_le_iff.mp h
    rw [this] at h1
    exact lt_irrefl _ (by exact_mod_cast h1)
  -- Now apply ENat.sSup_mem_of_nonempty_of_lt_top
  haveI : Nonempty _ := Set.Nonempty.to_subtype hne
  have hmem := @ENat.sSup_mem_of_nonempty_of_lt_top _ this hdepth_lt_top
  -- hmem : sSup _ ∈ _, i.e., ringDepth R is attained
  obtain ⟨rs, hlen, hreg, hmem'⟩ : ∃ rs : List R, (rs.length : ℕ∞) = ringDepth R ∧
      IsWeaklyRegular R rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal R := hmem
  refine ⟨rs, hreg, hmem', ?_⟩
  -- ringKrullDim R = ringDepth R (CM) = rs.length
  have hCMeq : ringKrullDim R = ringDepth R := IsCohenMacaulayLocalRing.depth_eq_dim
  rw [hCMeq, ← hlen]

-- Increased heartbeat limit: this proof case-splits on X ∈ p vs X ∉ p and
-- builds explicit regular sequences in each branch; each branch does substantial
-- simp/rewrite work on quotient-localization identifications.
set_option maxHeartbeats 800000 in
/-- **Core lemma**: if `R` is a CM Noetherian local ring and `p` is a prime of `R[X]`
whose contraction to `R` is the maximal ideal, then the localization `R[X]_p` is
Cohen-Macaulay local.

This is the translation of upstream `Polynomial.localization_at_comap_maximal_isCM_isCM`
to the v4.28.0 API. -/
private lemma localization_at_comap_maximal_isCM_isCM_local [IsNoetherianRing R]
    [IsCohenMacaulayLocalRing R] (p : Ideal R[X]) [p.IsPrime]
    (max : p.comap C = maximalIdeal R) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  set q := (maximalIdeal R).map C with q_def
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have ker : RingHom.ker (Polynomial.mapRingHom (IsLocalRing.residue R)) = q := by
    simpa only [residue, ker_mapRingHom, q] using congrArg (Ideal.map C) (Quotient.mkₐ_ker R _)
  -- Get a regular sequence witnessing the depth of R
  obtain ⟨rs, reg, mem, hlen⟩ :=
    exists_weaklyRegular_length_eq_ringKrullDim_of_isCohenMacaulayLocalRing R
  -- hlen : ringKrullDim R = ↑rs.length
  -- The elements of (rs.map algebraMap) are in maximalIdeal (Localization.AtPrime p)
  have mem' : ∀ a ∈ (rs.map (algebraMap R (Localization.AtPrime p))),
      a ∈ maximalIdeal (Localization.AtPrime p) := by
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro r hr
    rw [IsScalarTower.algebraMap_eq R R[X], RingHom.comp_apply]
    apply Ideal.mem_comap.mp
    rw [IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime p) p, ← Ideal.mem_comap,
      Polynomial.algebraMap_eq, max]
    exact mem r hr
  -- Module.Flat R (Localization.AtPrime p)
  haveI : Module.Flat R (Localization.AtPrime p) := Module.Flat.trans R R[X] _
  -- Krull dim equality: ringKrullDim (Loc.AtPrime p) = p.height
  haveI : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  have hdimeq : ringKrullDim (Localization.AtPrime p) = (p.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)
  -- Now case split: X ∈ P (upstream `eq0`) vs X ∉ P
  by_cases eq0 : p.map (Polynomial.mapRingHom (IsLocalRing.residue R)) = ⊥
  · -- Case X ∈ p: the regular sequence rs.map algebraMap works as-is
    have reg_loc : IsWeaklyRegular (Localization.AtPrime p)
        (rs.map (algebraMap R (Localization.AtPrime p))) :=
      IsWeaklyRegular.of_flat reg
    -- p = q
    have eq : p = q := le_antisymm (by simpa [← ker, ← Ideal.map_eq_bot_iff_le_ker]) qle
    -- p.height = (maximalIdeal R).height = rs.length
    have hpheight : p.height = (maximalIdeal R).height := by
      rw [eq, Polynomial.height_map_C (maximalIdeal R)]
    have hmaxht : (maximalIdeal R).height = (rs.length : ℕ∞) := by
      have h1 : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) = ringKrullDim R :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      rw [hlen] at h1
      exact_mod_cast h1
    have hdim : ringKrullDim (Localization.AtPrime p) =
        ((rs.map (algebraMap R (Localization.AtPrime p))).length : ℕ∞) := by
      rw [hdimeq, hpheight, hmaxht, List.length_map]
    exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim reg_loc mem' hdim
  · -- Case X ∉ p: append a lifted monic polynomial f to rs.map algebraMap
    rcases polynomial_exist_monic_mem eq0 with ⟨g, gmem, mong⟩
    have glift : g ∈ lifts (IsLocalRing.residue R) :=
      map_surjective _ IsLocalRing.residue_surjective _
    rcases Polynomial.lifts_and_natDegree_eq_and_monic glift mong with ⟨f, hf, _deg, monf⟩
    have fmem : f ∈ p := by
      simp only [← hf, ← coe_mapRingHom, ← mem_comap] at gmem
      rw [comap_map_of_surjective' _ (map_surjective _ IsLocalRing.residue_surjective),
        sup_of_le_left (by simpa [ker_mapRingHom, ker_residue] using qle)] at gmem
      exact gmem
    -- rs.map algebraMap to R[X] is weakly regular
    have reg'' : IsWeaklyRegular R[X] (rs.map (algebraMap R R[X])) :=
      IsWeaklyRegular.of_flat reg
    -- rs.map algebraMap ++ [f] is weakly regular in R[X]
    have reg' : IsWeaklyRegular R[X] ((rs.map (algebraMap R R[X])) ++ [f]) := by
      refine ⟨fun i hi => ?_⟩
      simp only [List.length_append, List.length_cons, List.length_nil, zero_add,
        Nat.lt_succ_iff] at hi
      rw [List.take_append_of_le_length hi]
      rcases lt_or_eq_of_le hi with lt|eq
      · simpa only [← List.getElem_append_left' lt [f]] using reg''.1 i lt
      · rw [List.getElem_concat_length eq, List.take_of_length_le (ge_of_eq eq), smul_eq_mul,
          mul_top, ← map_ofList, algebraMap_eq]
        let _inst : Algebra R[X] (R ⧸ Ideal.ofList rs)[X] := RingHom.toAlgebra
          (Polynomial.mapRingHom (Ideal.Quotient.mk _))
        apply (Equiv.isSMulRegular_congr (r := f) (s := f)
          (e := (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.ofList rs)).toEquiv)
          (fun x => by
            -- Goal: e (f • x) = f • e x, where
            -- LHS smul: f • x in (R/ofList rs)[X] via _inst = mapRingHom (Quotient.mk _) f * x
            -- RHS smul: f • e(x) in R[X] ⧸ map C (ofList rs) via default = Quotient.mk f * e(x)
            set e := Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.ofList rs)
            have heq : e.toEquiv (f • x) = e (f • x) := rfl
            have heq2 : e.toEquiv x = e x := rfl
            rw [heq, heq2]
            rw [show (f • x : (R ⧸ Ideal.ofList rs)[X]) =
              Polynomial.map (Ideal.Quotient.mk (Ideal.ofList rs)) f * x from rfl]
            rw [map_mul, Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk]
            change Ideal.Quotient.mk _ f * e x = f • e x
            rfl)).mp
        apply IsSMulRegular.of_right_eq_zero_of_smul
        simpa [Algebra.smul_def, algebraMap_def, Ideal.Quotient.algebraMap_eq, coe_mapRingHom]
          using (mem_nonZeroDivisors_iff.mp
            (monf.map (Ideal.Quotient.mk (Ideal.ofList rs))).mem_nonZeroDivisors).1
    -- All elements of ((rs.map algebraMap) ++ [f]).map algebraMap_toLoc
    -- are in maximalIdeal (Loc.AtPrime p)
    have mem'' : ∀ r ∈ (((rs.map (algebraMap R R[X])) ++ [f]).map
        (algebraMap R[X] (Localization.AtPrime p))),
        r ∈ maximalIdeal (Localization.AtPrime p) := by
      intro r hr
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.mem_append,
        List.mem_map, Function.comp_apply, List.mem_cons, List.not_mem_nil, or_false,
        ← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq] at hr
      rcases hr with isrs|isf
      · exact mem' _ (List.mem_map.mpr isrs)
      · simpa only [isf, ← mem_comap, IsLocalization.AtPrime.comap_maximalIdeal _ p]
    -- The extended sequence is weakly regular in Loc.AtPrime p
    have reg_loc : IsWeaklyRegular (Localization.AtPrime p)
        (((rs.map (algebraMap R R[X])) ++ [f]).map (algebraMap R[X] (Localization.AtPrime p))) :=
      IsWeaklyRegular.of_flat reg'
    -- Upper bound on p.height
    have ht2 : p.height ≤ (maximalIdeal R).height + 1 := by
      rw [← WithBot.coe_le_coe, WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim,
          Ideal.height_eq_primeHeight, WithBot.coe_one]
      -- Goal: (p.primeHeight : WithBot ℕ∞) ≤ ringKrullDim R[X]... wait, we need Loc.AtPrime p
      -- Actually the goal after the rewrites is:
      --   ↑p.primeHeight ≤ ringKrullDim R + ↑1
      -- Use: ringKrullDim R[X] = ringKrullDim R + 1 (for Noetherian) + p.primeHeight ≤ dim R[X]
      have h1 : (p.primeHeight : WithBot ℕ∞) ≤ ringKrullDim R[X] :=
        Ideal.primeHeight_le_ringKrullDim
      have h2 : ringKrullDim R[X] = ringKrullDim R + 1 := by
        rw [Polynomial.ringKrullDim_of_isNoetherianRing]
      exact h2 ▸ h1
    -- Length of extended sequence is rs.length + 1
    have hextlen : (((rs.map (algebraMap R R[X])) ++ [f]).map
        (algebraMap R[X] (Localization.AtPrime p))).length = rs.length + 1 := by
      simp [List.length_append, List.length_map]
    -- Get the dimension equality for Loc.AtPrime p
    have hmaxht : (maximalIdeal R).height = (rs.length : ℕ∞) := by
      have h1 : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) = ringKrullDim R :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      rw [hlen] at h1
      exact_mod_cast h1
    -- p.height ≤ rs.length + 1 (as ℕ∞)
    have ht2' : p.height ≤ (rs.length : ℕ∞) + 1 := by
      rw [hmaxht] at ht2; exact_mod_cast ht2
    -- Lower bound: length ≤ dim (via regular sequence)
    have hdimlb : ((rs.length + 1 : ℕ) : ℕ∞) ≤ p.height := by
      -- Regular sequence of length rs.length+1 in Loc.AtPrime p, all in maximalIdeal
      -- Length ≤ Krull dim of Loc.AtPrime p, and Krull dim of Loc.AtPrime p = p.height.
      have hreg_len : ((((rs.map (algebraMap R R[X])) ++ [f]).map
          (algebraMap R[X] (Localization.AtPrime p))).length : WithBot ℕ∞)
          ≤ ringKrullDim (Localization.AtPrime p) :=
        weaklyRegular_length_le_ringKrullDim _ reg_loc mem''
      rw [hextlen] at hreg_len
      rw [hdimeq] at hreg_len
      have hleq : ((rs.length + 1 : ℕ) : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞) := by
        push_cast; exact_mod_cast hreg_len
      exact_mod_cast hleq
    -- Combine: p.height = rs.length + 1
    have hpheight : p.height = ((rs.length + 1 : ℕ) : ℕ∞) := by
      apply le_antisymm
      · have : ((rs.length : ℕ∞) + 1) = ((rs.length + 1 : ℕ) : ℕ∞) := by push_cast; rfl
        rw [this] at ht2'; exact ht2'
      · exact hdimlb
    -- Now the dimension equality as needed by of_weaklyRegular_length_eq_dim
    have hdim : ringKrullDim (Localization.AtPrime p) =
        ((((rs.map (algebraMap R R[X])) ++ [f]).map
          (algebraMap R[X] (Localization.AtPrime p))).length : ℕ∞) := by
      rw [hdimeq, hpheight, hextlen]
    exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim reg_loc mem'' hdim

-- Increased heartbeat limit: constructs the pS prime and the pS.comap C = maxIdeal
-- equation through several IsLocalization comap/map identifications.
set_option maxHeartbeats 800000 in
/-- **Polynomial ring over a CM Noetherian ring is CM** (no IsDomain assumption).

This is the translation of upstream `Polynomial.isCM_of_isCM` (mathlib PR #28599)
to the v4.28.0 API of this project. -/
theorem isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing
    [IsNoetherianRing R] [IsCohenMacaulayRing R] :
    IsCohenMacaulayRing R[X] := by
  refine ⟨fun p _ => ?_⟩
  set q := p.comap (C : R →+* R[X]) with q_def
  haveI : q.IsPrime := Ideal.IsPrime.comap _
  -- Give Polynomial.algebra as local instance so subsequent typeclass synthesis works.
  letI algS : Algebra R[X] (Localization.AtPrime q)[X] :=
    Polynomial.algebra R (Localization.AtPrime q)
  set pc : Submonoid R[X] :=
    Submonoid.map (Polynomial.C : R →+* R[X]).toMonoidHom q.primeCompl with pc_def
  haveI : IsLocalization pc (Localization.AtPrime q)[X] :=
    Polynomial.isLocalization q.primeCompl _
  set pS : Ideal (Localization.AtPrime q)[X] :=
    p.map (algebraMap R[X] (Localization.AtPrime q)[X]) with pS_def
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a => a))
  haveI : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  haveI : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.comap_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  -- R_q is CM Noetherian local
  haveI hCMq : IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
    IsCohenMacaulayRing.CM_localize q
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    IsLocalization.isNoetherianRing q.primeCompl _ inferInstance
  -- The key hypothesis: pS.comap C = maximalIdeal (R_q)
  have hmax : Ideal.comap (Polynomial.C : (Localization.AtPrime q) →+*
        (Localization.AtPrime q)[X]) pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_comap q.primeCompl (Localization.AtPrime q)
          (Ideal.comap Polynomial.C pS),
      ← IsLocalization.map_comap q.primeCompl (Localization.AtPrime q)
          (maximalIdeal (Localization.AtPrime q))]
    simp only [Ideal.comap_comap, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← Ideal.comap_comap,
      IsLocalization.comap_map_of_isPrime_disjoint pc _ ‹_› disj,
      IsLocalization.AtPrime.comap_maximalIdeal (Localization.AtPrime q) q]
    rfl
  -- Apply the core lemma
  have hCM_pS := localization_at_comap_maximal_isCM_isCM_local
    (Localization.AtPrime q) pS hmax
  -- Transfer via IsLocalization.algEquiv to Localization.AtPrime p
  exact isCohenMacaulayLocalRing_of_ringEquiv' hCM_pS
    (IsLocalization.algEquiv p.primeCompl
      (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

/-- `MvPolynomial (Fin n) R` is Cohen-Macaulay when `R` is CM Noetherian.
Translation of upstream `MvPolynomial.fin_isCM_of_isCM`. -/
private lemma mvPolynomial_fin_isCM_of_isCM_local
    [IsNoetherianRing R] [IsCohenMacaulayRing R] (n : ℕ) :
    IsCohenMacaulayRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero =>
    exact isCohenMacaulayRing_of_ringEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm
  | succ n ih =>
    haveI := ih
    haveI : IsNoetherianRing (MvPolynomial (Fin n) R) := MvPolynomial.isNoetherianRing
    haveI : IsCohenMacaulayRing (Polynomial (MvPolynomial (Fin n) R)) :=
      isCohenMacaulayRing_polynomial_of_isCohenMacaulayRing (MvPolynomial (Fin n) R)
    exact isCohenMacaulayRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).toRingEquiv.symm

/-- **Multivariate polynomial ring over a CM Noetherian ring (finite variables) is CM**.

This is the translation of upstream `MvPolynomial.isCM_of_isCM_of_finite` (mathlib
PR #28599) to the v4.28.0 API of this project.

Universe restriction: the index type `ι` must share the universe `u` of `R`;
this is a local limitation of `isCohenMacaulayRing_of_ringEquiv` (which requires
both rings in the same universe) and is not present upstream. -/
theorem isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing
    [IsNoetherianRing R] [IsCohenMacaulayRing R] (ι : Type u) [Finite ι] :
    IsCohenMacaulayRing (MvPolynomial ι R) := by
  haveI := mvPolynomial_fin_isCM_of_isCM_local R (Nat.card ι)
  exact isCohenMacaulayRing_of_ringEquiv
    (MvPolynomial.renameEquiv R (Finite.equivFin ι)).toRingEquiv.symm

end PolynomialGeneralCM

end

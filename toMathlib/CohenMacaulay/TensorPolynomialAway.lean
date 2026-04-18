/-
The **L7 replacement** lemma for the HH global-CM route:

  (A ⊗_K K[τ][s⁻¹])_𝔓 is Cohen–Macaulay

for any Noetherian CM K-algebra A, any finite type τ, any s ∈ K[τ],
and any prime 𝔓 of A ⊗_K K[τ][s⁻¹].

Proof strategy:

  1. Construct a K-algebra iso  A ⊗_K K[τ][s⁻¹] ≃ₐ[A] Localization.Away s_A,
     where s_A := MvPolynomial.map (algebraMap K A) s ∈ A[τ].
  2. A[τ] is Cohen–Macaulay by the backported polynomial-over-CM theorem
     `isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing` (PR #28599).
  3. Localization.Away s_A is a localization of A[τ], hence globally CM.
  4. Transport CM through the iso.

This is the Q6 answer from the deep-model reply
(`guides/answers/ANSWER_HH_QUOTIENT_CM_AT_NON_AUGIDEAL.md`) and closes
the former F2 "L7" entry for the HH global-CM theorem.
-/

import toMathlib.CohenMacaulay.Polynomial
import toMathlib.PolynomialAwayTensor
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Tower

noncomputable section

open MvPolynomial TensorProduct

universe u

namespace TensorPolynomialAway

variable {K : Type u} [CommRing K]
variable {A : Type u} [CommRing A] [Algebra K A]
variable {τ : Type u} [DecidableEq τ]

/-- Image of `s : K[τ]` in `A[τ]` under the coefficient map `K → A`. -/
protected abbrev mapCoeff (s : MvPolynomial τ K) : MvPolynomial τ A :=
  MvPolynomial.map (algebraMap K A) s

/-! ### Step 1 — tensor-away iso

We construct an `A`-algebra isomorphism

    A ⊗_K K[τ][s⁻¹]  ≃ₐ[A]  Localization.Away (map s)

by bidirectional lifts, analogous to `polynomialAwayTensorEquiv`. -/

/-- **The tensor-away iso**: `A ⊗_K K[τ][s⁻¹] ≅ A[τ][s_A⁻¹]` as `A`-algebras. -/
def tensorAwayEquiv (s : MvPolynomial τ K) :
    TensorProduct K A (Localization.Away s)
      ≃ₐ[A] Localization.Away (TensorPolynomialAway.mapCoeff (A := A) s) := by
  set sA : MvPolynomial τ A := TensorPolynomialAway.mapCoeff (A := A) s
  set LA : Type u := Localization.Away sA
  -- A → LA via A → A[τ] → A[τ][s_A⁻¹]
  set mapA : A →ₐ[A] LA :=
    (IsScalarTower.toAlgHom A (MvPolynomial τ A) LA).comp
      (Algebra.ofId A (MvPolynomial τ A))
  -- K[τ] → LA sending s to a unit
  set mapKτ : MvPolynomial τ K →ₐ[K] LA :=
    (IsScalarTower.toAlgHom K (MvPolynomial τ A) LA).comp
      (MvPolynomial.mapAlgHom (Algebra.ofId K A))
  have hUnit : IsUnit (mapKτ s) := by
    change IsUnit (algebraMap (MvPolynomial τ A) LA sA)
    exact IsLocalization.Away.algebraMap_isUnit sA
  have hPowers : ∀ y : Submonoid.powers s, IsUnit (mapKτ y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hUnit.pow n
  set mapLs : Localization.Away s →ₐ[K] LA :=
    IsLocalization.liftAlgHom (M := Submonoid.powers s)
      (S := Localization.Away s) hPowers
  -- Forward: A ⊗_K Localization.Away s → LA
  set fwd : TensorProduct K A (Localization.Away s) →ₐ[A] LA :=
    Algebra.TensorProduct.lift mapA mapLs (fun _ _ => mul_comm _ _)
  -- Backward base: A[τ] → A ⊗_K Localization.Away s
  set bwdBase : MvPolynomial τ A →ₐ[A] TensorProduct K A (Localization.Away s) :=
    aeval fun t =>
      (1 : A) ⊗ₜ[K] (algebraMap (MvPolynomial τ K) (Localization.Away s) (X t))
  have hBwdUnit : IsUnit (bwdBase sA) := by
    have hcalc : bwdBase sA =
        (1 : A) ⊗ₜ[K] algebraMap (MvPolynomial τ K) (Localization.Away s) s := by
      change (aeval _) (MvPolynomial.map (algebraMap K A) s) = _
      rw [MvPolynomial.aeval_map_algebraMap]
      have hext :
          (aeval (fun t : τ =>
            (1 : A) ⊗ₜ[K]
              algebraMap (MvPolynomial τ K) (Localization.Away s) (X t)) :
          MvPolynomial τ K →ₐ[K] TensorProduct K A (Localization.Away s)) =
            (Algebra.TensorProduct.includeRight.restrictScalars K).comp
              (IsScalarTower.toAlgHom K (MvPolynomial τ K) (Localization.Away s)) := by
        apply algHom_ext
        intro t
        simp [Algebra.TensorProduct.includeRight_apply]
      exact congr_arg (fun φ : MvPolynomial τ K →ₐ[K] _ => φ s) hext
    rw [hcalc]
    have hu : IsUnit (algebraMap (MvPolynomial τ K) (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit s
    exact (Algebra.TensorProduct.includeRight
      (R := K) (A := A) (B := Localization.Away s)).isUnit_map hu
  have hPowersBwd : ∀ y : Submonoid.powers sA, IsUnit (bwdBase y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hBwdUnit.pow n
  set bwd : LA →ₐ[A] TensorProduct K A (Localization.Away s) :=
    IsLocalization.liftAlgHom (M := Submonoid.powers sA) (S := LA) hPowersBwd
  have hFwdBwdBase : fwd.comp bwdBase =
      (IsScalarTower.toAlgHom A (MvPolynomial τ A) LA) := by
    apply MvPolynomial.algHom_ext
    intro t
    simp [bwdBase, fwd, mapLs, mapA, mapKτ,
      Algebra.TensorProduct.lift_tmul,
      IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · refine Localization.algHom_ext (Submonoid.powers sA) ?_
    have h_bwd_comp : bwd.comp
        (IsScalarTower.toAlgHom A (MvPolynomial τ A) LA) = bwdBase := by
      apply AlgHom.ext
      intro x
      change bwd (algebraMap (MvPolynomial τ A) LA x) = bwdBase x
      simp [bwd, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    have hAlgHom : (Algebra.algHom A (MvPolynomial τ A) LA : _ →ₐ[A] _) =
        IsScalarTower.toAlgHom A (MvPolynomial τ A) LA := rfl
    rw [AlgHom.comp_assoc, hAlgHom, h_bwd_comp, hFwdBwdBase]
    rfl
  · apply Algebra.TensorProduct.ext
    · apply AlgHom.ext
      intro a
      change bwd (fwd (a ⊗ₜ[K] 1)) = a ⊗ₜ[K] 1
      simp [fwd, mapA, Algebra.TensorProduct.lift_tmul, bwd,
        IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq, bwdBase]
    · refine Localization.algHom_ext (Submonoid.powers s) ?_
      apply MvPolynomial.algHom_ext
      intro t
      change bwd (fwd ((1 : A) ⊗ₜ[K]
          algebraMap (MvPolynomial τ K) (Localization.Away s) (X t))) =
        (1 : A) ⊗ₜ[K]
          algebraMap (MvPolynomial τ K) (Localization.Away s) (X t)
      simp [fwd, mapKτ, mapLs, Algebra.TensorProduct.lift_tmul, bwd,
        IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq, bwdBase]

/-! ### Step 2 — localisation of a globally CM ring is globally CM -/

/-- **Localisation at a submonoid preserves global Cohen–Macaulay-ness.**

For prime `P` in `Localization M`, the contraction `Q := P.comap (algebraMap _ _)`
is prime in `R`, and the Mathlib `localizationLocalizationAtPrimeIsoLocalization`
gives a ring iso `R_Q ≅ (Localization M)_P`. Since `R` is globally CM, `R_Q` is
CM local, and we transport through the iso. -/
theorem isCohenMacaulayRing_localization
    (R : Type u) [CommRing R] [IsCohenMacaulayRing R]
    (M : Submonoid R) :
    IsCohenMacaulayRing (Localization M) := by
  refine ⟨fun P _ => ?_⟩
  set Q : Ideal R := P.comap (algebraMap R (Localization M))
  haveI : Q.IsPrime := Ideal.IsPrime.comap _
  haveI hCM_Q : IsCohenMacaulayLocalRing (Localization.AtPrime Q) :=
    IsCohenMacaulayRing.CM_localize Q
  exact isCohenMacaulayLocalRing_of_ringEquiv' hCM_Q
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P).toRingEquiv

/-! ### Step 3 — the L7 replacement -/

/-- **L7 replacement (global form)**: `A ⊗_K K[τ][s⁻¹]` is Cohen–Macaulay as
a ring, for any Noetherian CM K-algebra `A`, any finite index type `τ`, and
any `s ∈ K[τ]`. -/
theorem isCohenMacaulayRing_tensor_away
    [IsNoetherianRing A] [IsCohenMacaulayRing A]
    [Finite τ]
    (s : MvPolynomial τ K) :
    IsCohenMacaulayRing (TensorProduct K A (Localization.Away s)) := by
  haveI : IsNoetherianRing (MvPolynomial τ A) := MvPolynomial.isNoetherianRing
  haveI hCM_Aτ : IsCohenMacaulayRing (MvPolynomial τ A) :=
    isCohenMacaulayRing_mvPolynomial_of_isCohenMacaulayRing A τ
  set sA : MvPolynomial τ A := TensorPolynomialAway.mapCoeff (A := A) s
  haveI : IsCohenMacaulayRing (Localization.Away sA) :=
    isCohenMacaulayRing_localization (MvPolynomial τ A) (Submonoid.powers sA)
  exact isCohenMacaulayRing_of_ringEquiv (tensorAwayEquiv s).symm.toRingEquiv

/-- **L7 replacement (local form)**: for any prime `𝔓` of `A ⊗_K K[τ][s⁻¹]`,
its localisation is Cohen–Macaulay. -/
theorem isCohenMacaulayLocalRing_localization_tensor_away
    [IsNoetherianRing A] [IsCohenMacaulayRing A]
    [Finite τ]
    (s : MvPolynomial τ K)
    (𝔓 : Ideal (TensorProduct K A (Localization.Away s))) [𝔓.IsPrime] :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime 𝔓) := by
  haveI := isCohenMacaulayRing_tensor_away (A := A) s
  exact IsCohenMacaulayRing.CM_localize 𝔓

end TensorPolynomialAway

end

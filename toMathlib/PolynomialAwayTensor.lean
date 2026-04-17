/-
Lemma 6 from the F2 route to Proposition 1.6 CM at non-augmentation primes:

  K[α] ⊗_K K[β][m⁻¹] ≃ K[α ⊔ β][m'⁻¹]

where `m' = rename Sum.inr m` is the image of `m` under the Sum.inr embedding.

The strategy composes:
1. `TensorProduct.comm`: swap left and right factors.
2. `MvPolynomial.algebraTensorAlgEquiv`: tensor-with-polynomial over the
   coefficient ring of the polynomial.
3. A custom step identifying `MvPolynomial α L_β` with the localization of
   `MvPolynomial (α ⊕ β) K` at the image of `m`.
-/

import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section

open MvPolynomial TensorProduct

universe u

variable {K : Type u} [CommRing K] {α β : Type u} [DecidableEq α] [DecidableEq β]

/-- **Lemma 6**: polynomial factor merges with Laurent factor.

`K[α] ⊗_K K[β][m⁻¹] ≃ₐ[K] K[α ⊔ β][(rename Sum.inr m)⁻¹]`.

Constructed as an AlgEquiv via bidirectional lifts. -/
def polynomialAwayTensorEquiv (m : MvPolynomial β K) :
    TensorProduct K (MvPolynomial α K) (Localization.Away m)
      ≃ₐ[K] Localization.Away
        (rename (Sum.inr : β → α ⊕ β) m : MvPolynomial (α ⊕ β) K) := by
  set m' : MvPolynomial (α ⊕ β) K := rename Sum.inr m with hm'
  set Lαβ := Localization.Away m' with hLαβ
  set Lβ := Localization.Away m with hLβ
  -- Two K-algebra maps into Lαβ:
  set map_α : MvPolynomial α K →ₐ[K] Lαβ :=
    (IsScalarTower.toAlgHom K (MvPolynomial (α ⊕ β) K) Lαβ).comp
      (rename (Sum.inl : α → α ⊕ β))
  set map_β : MvPolynomial β K →ₐ[K] Lαβ :=
    (IsScalarTower.toAlgHom K (MvPolynomial (α ⊕ β) K) Lαβ).comp
      (rename (Sum.inr : β → α ⊕ β))
  -- map_β sends m to a unit (it equals algebraMap m' which is a unit).
  have hUnit : IsUnit (map_β m) := by
    change IsUnit (algebraMap (MvPolynomial (α ⊕ β) K) Lαβ (rename Sum.inr m))
    exact IsLocalization.Away.algebraMap_isUnit m'
  -- Lift to Localization.Away m via liftAlgHom over K
  have hPowers : ∀ y : Submonoid.powers m, IsUnit (map_β y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hUnit.pow n
  set map_Lβ : Lβ →ₐ[K] Lαβ :=
    IsLocalization.liftAlgHom (M := Submonoid.powers m) (S := Lβ) hPowers
  -- Forward: use Algebra.TensorProduct.lift
  set fwd : TensorProduct K (MvPolynomial α K) Lβ →ₐ[K] Lαβ :=
    Algebra.TensorProduct.lift map_α map_Lβ (fun _ _ => mul_comm _ _)
  -- Backward: K_αβ → TensorProduct K K_α Lβ sending vars appropriately
  set bwdBase : MvPolynomial (α ⊕ β) K →ₐ[K] TensorProduct K (MvPolynomial α K) Lβ :=
    aeval fun v => match v with
      | Sum.inl a => (X a : MvPolynomial α K) ⊗ₜ[K] (1 : Lβ)
      | Sum.inr b =>
          (1 : MvPolynomial α K) ⊗ₜ[K] (algebraMap (MvPolynomial β K) Lβ (X b))
  -- bwdBase sends m' to 1 ⊗ (algebraMap m), which is a unit since m is a unit in Lβ
  have hBwdUnit : IsUnit (bwdBase m') := by
    -- m' = rename Sum.inr m; bwdBase of rename Sum.inr m is 1 ⊗ algebraMap m
    have hcalc : bwdBase m' =
        (1 : MvPolynomial α K) ⊗ₜ[K] algebraMap (MvPolynomial β K) Lβ m := by
      change aeval _ (rename Sum.inr m) = _
      rw [aeval_rename]
      -- aeval (f ∘ Sum.inr) m = 1 ⊗ algebraMap m
      -- Both sides are images of m under a K-algebra hom K_β → K_α ⊗ L_β.
      -- LHS sends X b ↦ 1 ⊗ algebraMap (X b); RHS does the same.
      -- Use algHom_ext to equate the two algebra homs.
      have : (aeval (fun b : β =>
            (1 : MvPolynomial α K) ⊗ₜ[K]
              algebraMap (MvPolynomial β K) Lβ (X b)) :
            MvPolynomial β K →ₐ[K] TensorProduct K (MvPolynomial α K) Lβ) =
          (Algebra.TensorProduct.includeRight.comp
            (IsScalarTower.toAlgHom K (MvPolynomial β K) Lβ)) := by
        apply algHom_ext
        intro b
        simp [Algebra.TensorProduct.includeRight_apply]
      exact congr_arg (fun φ : MvPolynomial β K →ₐ[K] _ => φ m) this
    rw [hcalc]
    have hu : IsUnit (algebraMap (MvPolynomial β K) Lβ m) :=
      IsLocalization.Away.algebraMap_isUnit m
    exact (Algebra.TensorProduct.includeRight (R := K) (A := MvPolynomial α K)
      (B := Lβ)).isUnit_map hu
  -- Lift to Lαβ via liftAlgHom over K
  have hPowersBwd : ∀ y : Submonoid.powers m', IsUnit (bwdBase y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hBwdUnit.pow n
  set bwd : Lαβ →ₐ[K] TensorProduct K (MvPolynomial α K) Lβ :=
    IsLocalization.liftAlgHom (M := Submonoid.powers m') (S := Lαβ) hPowersBwd
  -- Key identity: fwd ∘ bwdBase = algebraMap K_αβ Lαβ (as K-algebra homs K_αβ → Lαβ)
  have hFwdBwdBase : fwd.comp bwdBase =
      (IsScalarTower.toAlgHom K (MvPolynomial (α ⊕ β) K) Lαβ) := by
    apply MvPolynomial.algHom_ext
    rintro (a | b)
    · -- X (inl a): bwdBase gives X a ⊗ 1, fwd gives map_α (X a) = algebraMap (X (inl a))
      simp [bwdBase, fwd, map_α, Algebra.TensorProduct.lift_tmul]
    · -- X (inr b): fwd(1 ⊗ algebraMap X b) = map_β (X b) = algebraMap (X (inr b))
      simp [bwdBase, fwd, map_β, map_Lβ, map_α,
        IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq,
        Algebra.TensorProduct.lift_tmul]
  -- Show compositions are identity
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · -- fwd ∘ bwd = AlgHom.id K Lαβ
    refine Localization.algHom_ext (Submonoid.powers m') ?_
    -- bwd.comp (algebraMap) = bwdBase (by liftAlgHom property)
    have h_bwd_comp : bwd.comp
        (IsScalarTower.toAlgHom K (MvPolynomial (α ⊕ β) K) Lαβ) = bwdBase := by
      apply AlgHom.ext
      intro x
      change bwd (algebraMap (MvPolynomial (α ⊕ β) K) Lαβ x) = bwdBase x
      simp [bwd, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    -- So (fwd ∘ bwd) ∘ algebraMap = fwd ∘ bwdBase = algebraMap (by hFwdBwdBase)
    have hAlgHom : (Algebra.algHom K (MvPolynomial (α ⊕ β) K) Lαβ : _ →ₐ[K] _) =
        IsScalarTower.toAlgHom K (MvPolynomial (α ⊕ β) K) Lαβ := rfl
    rw [AlgHom.comp_assoc, hAlgHom, h_bwd_comp, hFwdBwdBase]
    rfl
  · -- bwd ∘ fwd = AlgHom.id
    apply Algebra.TensorProduct.ext
    · -- agree on left factor (MvPolynomial α K)
      apply MvPolynomial.algHom_ext
      intro a
      change bwd (fwd (X a ⊗ₜ[K] 1)) = X a ⊗ₜ[K] 1
      simp [fwd, map_α, Algebra.TensorProduct.lift_tmul, bwd,
        IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq,
        bwdBase]
    · -- agree on right factor (Localization.Away m)
      refine Localization.algHom_ext (Submonoid.powers m) ?_
      apply MvPolynomial.algHom_ext
      intro b
      change bwd (fwd (1 ⊗ₜ[K] algebraMap (MvPolynomial β K) Lβ (X b))) =
        1 ⊗ₜ[K] algebraMap (MvPolynomial β K) Lβ (X b)
      simp [fwd, map_β, map_Lβ, Algebra.TensorProduct.lift_tmul, bwd,
        IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq, bwdBase]

end

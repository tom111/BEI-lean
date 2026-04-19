/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor-left-localisation bridge

Let `K` be a commutative ring, `A`, `B` two `K`-algebras, and `𝔓` a prime ideal of
`A ⊗[K] B` whose contraction to `A` (under `includeLeft : A →ₐ[K] A ⊗[K] B`) is a
prime ideal `m`. Then localising `A ⊗[K] B` at `𝔓` is the same as first base-changing
to `A_m ⊗[K] B` and then localising at the push-forward prime `𝔓'`.

This is the **tensor-left-localisation bridge** used in the BEI project (Session C2).
The concrete output is the ring equivalence

    Localization.AtPrime 𝔓 ≃+* Localization.AtPrime 𝔓'

## Proof strategy

1. Establish that `A_m ⊗[K] B` is an `(A ⊗[K] B)`-algebra via
   `Algebra.TensorProduct.map (IsScalarTower.toAlgHom K A A_m) (AlgHom.id K B)`.
2. Use `IsLocalization.tensorProduct_tensorProduct` to conclude that
   `A_m ⊗[K] B` is a localisation of `A ⊗[K] B` at
   `Algebra.algebraMapSubmonoid (A ⊗[K] B) m.primeCompl`.
3. Push `𝔓` forward along `A ⊗[K] B → A_m ⊗[K] B`, obtaining a prime `𝔓'`.
   Disjointness from the localisation submonoid follows from
   `𝔓.comap includeLeft = m`.
4. Conclude via `isLocalization_isLocalization_atPrime_isLocalization` plus
   `IsLocalization.algEquiv` that the two at-prime localisations agree.

## Main result

* `Algebra.tensorLeftLocalisationEquiv` — the ring equivalence.
* `Algebra.tensorLeftLocalisedPrime` — the push-forward prime in `A_m ⊗[K] B`.
* `Algebra.tensorLeftLocalisedPrime_isPrime` — it is prime.
-/

universe u

open TensorProduct

namespace Algebra

namespace TensorLeftLocalisation

/-- The canonical `K`-algebra map `A ⊗[K] B → A_m ⊗[K] B`. -/
noncomputable def toLocalizedHom (K : Type u) [CommRing K]
    {A : Type u} [CommRing A] [Algebra K A]
    (m : Ideal A) [m.IsPrime]
    (B : Type u) [CommRing B] [Algebra K B] :
    TensorProduct K A B →ₐ[K] TensorProduct K (Localization.AtPrime m) B :=
  Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom K A (Localization.AtPrime m))
    (AlgHom.id K B)

/-- `A_m ⊗[K] B` as an `(A ⊗[K] B)`-algebra via `toLocalizedHom`. -/
noncomputable def algebraStructure (K : Type u) [CommRing K]
    {A : Type u} [CommRing A] [Algebra K A]
    (m : Ideal A) [m.IsPrime]
    (B : Type u) [CommRing B] [Algebra K B] :
    Algebra (TensorProduct K A B) (TensorProduct K (Localization.AtPrime m) B) :=
  RingHom.toAlgebra (toLocalizedHom K m B).toRingHom

attribute [local instance] algebraStructure

section
variable {K : Type u} [CommRing K]
  {A : Type u} [CommRing A] [Algebra K A]
  (m : Ideal A) [m.IsPrime]
  (B : Type u) [CommRing B] [Algebra K B]

lemma algebraMap_eq :
    (algebraMap (TensorProduct K A B) (TensorProduct K (Localization.AtPrime m) B)) =
      (toLocalizedHom K m B).toRingHom :=
  rfl

/-- Scalar tower `A → A⊗B → A_m⊗B`. -/
lemma isScalarTower_A_tensor :
    IsScalarTower A (TensorProduct K A B) (TensorProduct K (Localization.AtPrime m) B) :=
  IsScalarTower.of_algebraMap_eq' <| by
    change algebraMap A (TensorProduct K (Localization.AtPrime m) B) =
        (toLocalizedHom K m B).toRingHom.comp (algebraMap A (TensorProduct K A B))
    ext a
    simp [toLocalizedHom, Algebra.TensorProduct.algebraMap_apply,
      IsScalarTower.toAlgHom_apply]

attribute [local instance] isScalarTower_A_tensor

/-- `A_m ⊗[K] B` is a localisation of `A ⊗[K] B` at the image of `m.primeCompl`. -/
lemma isLocalization_tensor :
    IsLocalization (Algebra.algebraMapSubmonoid (TensorProduct K A B) m.primeCompl)
      (TensorProduct K (Localization.AtPrime m) B) := by
  refine IsLocalization.tensorProduct_tensorProduct K B m.primeCompl _ ?_
  ext b
  simp [algebraMap_eq, toLocalizedHom]

end

end TensorLeftLocalisation

open TensorLeftLocalisation

/-- The push-forward prime `𝔓' = 𝔓.map (A⊗B → A_m⊗B)` of `𝔓 : Ideal (A ⊗[K] B)`
through the base change to `A_m`. -/
noncomputable def tensorLeftLocalisedPrime (K : Type u) [CommRing K]
    {A : Type u} [CommRing A] [Algebra K A]
    (m : Ideal A) [m.IsPrime]
    {B : Type u} [CommRing B] [Algebra K B]
    (𝔓 : Ideal (TensorProduct K A B)) :
    Ideal (TensorProduct K (Localization.AtPrime m) B) :=
  letI := algebraStructure K m B
  𝔓.map (algebraMap (TensorProduct K A B) (TensorProduct K (Localization.AtPrime m) B))

section Bridge

variable {K : Type u} [CommRing K]
  {A : Type u} [CommRing A] [Algebra K A]
  {B : Type u} [CommRing B] [Algebra K B]
  (m : Ideal A) [m.IsPrime]
  (𝔓 : Ideal (TensorProduct K A B)) [h𝔓 : 𝔓.IsPrime]

attribute [local instance] algebraStructure isScalarTower_A_tensor

variable (h : 𝔓.comap
  (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := B)).toRingHom = m)

omit h𝔓 in
include h in
lemma disjoint_algebraMapSubmonoid :
    Disjoint
      (Algebra.algebraMapSubmonoid (TensorProduct K A B) m.primeCompl : Set (TensorProduct K A B))
      (↑𝔓 : Set (TensorProduct K A B)) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨u, hu, rfl⟩ hmem
  have hcomap : u ∈ 𝔓.comap
      (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := B)).toRingHom := by
    rw [Ideal.mem_comap]
    -- `includeLeft u = u ⊗ₜ 1 = algebraMap A (A⊗B) u`
    have hrw : (Algebra.TensorProduct.includeLeft (R := K) (S := K) (A := A) (B := B)).toRingHom u =
        algebraMap A (TensorProduct K A B) u := rfl
    rw [hrw]; exact hmem
  rw [h] at hcomap
  exact hu hcomap

include h in
/-- The push-forward prime is indeed prime. -/
theorem tensorLeftLocalisedPrime_isPrime :
    (tensorLeftLocalisedPrime K m 𝔓).IsPrime := by
  haveI := isLocalization_tensor (K := K) m B
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (TensorProduct K A B) m.primeCompl) _ 𝔓 h𝔓
    (disjoint_algebraMapSubmonoid m 𝔓 h)

include h in
/-- **Tensor-left-localisation bridge**. If `𝔓` is a prime of `A ⊗[K] B` whose contraction
to `A` via `includeLeft` equals `m`, then localising at `𝔓` is the same as first base-changing
to `A_m ⊗[K] B` and localising at the push-forward prime. -/
noncomputable def tensorLeftLocalisationEquiv :
    letI := tensorLeftLocalisedPrime_isPrime m 𝔓 h
    Localization.AtPrime 𝔓 ≃+*
      Localization.AtPrime (tensorLeftLocalisedPrime K m 𝔓) := by
  haveI hLoc := isLocalization_tensor (K := K) m B
  haveI hPrime : (tensorLeftLocalisedPrime K m 𝔓).IsPrime :=
    tensorLeftLocalisedPrime_isPrime m 𝔓 h
  have hdisj := disjoint_algebraMapSubmonoid m 𝔓 h
  have hcomap :
      (tensorLeftLocalisedPrime K m 𝔓).comap
        (algebraMap (TensorProduct K A B)
          (TensorProduct K (Localization.AtPrime m) B)) = 𝔓 :=
    IsLocalization.comap_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid (TensorProduct K A B) m.primeCompl) _ h𝔓 hdisj
  -- The at-prime localization at `𝔓'` is also a localization of `A⊗B` at `𝔓.primeCompl`.
  haveI hAtPrime :
      IsLocalization.AtPrime (Localization.AtPrime (tensorLeftLocalisedPrime K m 𝔓)) 𝔓 := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (R := TensorProduct K A B)
      (S := TensorProduct K (Localization.AtPrime m) B)
      (Algebra.algebraMapSubmonoid (TensorProduct K A B) m.primeCompl)
      (T := Localization.AtPrime (tensorLeftLocalisedPrime K m 𝔓))
      (tensorLeftLocalisedPrime K m 𝔓)
    -- After rewriting the comap, the conclusion is precisely `IsLocalization.AtPrime ... 𝔓`.
    simpa [IsLocalization.AtPrime, hcomap] using this
  -- Both are at-prime localizations at `𝔓.primeCompl`; extract the canonical ring equiv.
  exact (IsLocalization.algEquiv (R := TensorProduct K A B) 𝔓.primeCompl
    (Localization.AtPrime 𝔓)
    (Localization.AtPrime (tensorLeftLocalisedPrime K m 𝔓))).toRingEquiv

end Bridge

end Algebra

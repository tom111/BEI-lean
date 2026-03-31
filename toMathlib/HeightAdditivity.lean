/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Height additivity for ideals in disjoint variable sets

For prime ideals I₁ ⊆ K[σ₁] and I₂ ⊆ K[σ₂] in disjoint variable sets,
the height of their combined extension in K[σ₁ ⊕ σ₂] satisfies:
  `height(I₁.map(rename inl) ⊔ I₂.map(rename inr)) = height(I₁) + height(I₂)`

## Proof strategy

We transfer the problem via `MvPolynomial.sumAlgEquiv` to
`MvPolynomial σ₁ (MvPolynomial σ₂ K)`, where the natural algebra structure
over `MvPolynomial σ₂ K` gives going-down (from freeness → flatness).
Then we apply `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` and
compute the residual height via `quotientEquivQuotientMvPolynomial`.

## Main results

- `MvPolynomial.height_sup_disjoint`: heights add for disjoint-variable primes
-/

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial Ideal

/-- The sup ideal in `K[σ₁ ⊕ σ₂]` transferred to the iterated polynomial ring
`MvPolynomial σ₁ (MvPolynomial σ₂ K)` via `sumAlgEquiv` has the form
`I₁.map(map C) ⊔ I₂.map C`.

Under `sumAlgEquiv K σ₁ σ₂ : K[σ₁ ⊕ σ₂] ≃ₐ K[σ₂][σ₁]`:
- `rename Sum.inl` maps to `MvPolynomial.map C` (by `sumAlgEquiv_comp_rename_inl`)
- `rename Sum.inr` maps to `C` (by `sumAlgEquiv_comp_rename_inr`)
-/
private lemma height_sup_eq_height_transferred
    {σ₁ σ₂ : Type*} [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K)) :
    (I₁.map (rename (Sum.inl : σ₁ → σ₁ ⊕ σ₂)).toRingHom ⊔
     I₂.map (rename (Sum.inr : σ₂ → σ₁ ⊕ σ₂)).toRingHom).height =
    (I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
     I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).height := by
  set e := (sumAlgEquiv K σ₁ σ₂).toRingEquiv
  -- sumAlgEquiv maps rename Sum.inl to map C, and rename Sum.inr to C
  have hinl : ∀ p : MvPolynomial σ₁ K,
      e (rename Sum.inl p) = MvPolynomial.map (C : K →+* MvPolynomial σ₂ K) p := by
    intro p
    have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inl K σ₁ σ₂) p
    simp only [AlgHom.comp_apply, mapAlgHom_apply] at h
    exact h
  have hinr : ∀ p : MvPolynomial σ₂ K,
      e (rename Sum.inr p) =
      (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K)) p := by
    intro p
    have h := AlgHom.congr_fun (sumAlgEquiv_comp_rename_inr K σ₁ σ₂) p
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, algebraMap_eq] at h
    exact h
  -- Transfer ideal maps: I.map(f) = I.map(e.symm ∘ (e ∘ f)) = (I.map(e ∘ f)).map(e.symm)
  -- I₁.map(rename inl) = (I₁.map(map C)).comap e
  -- because rename inl p = e⁻¹(map C p), i.e., e(rename inl p) = map C p
  -- So I₁.map(rename inl).map e = I₁.map(map C)
  have heq1 : e.toRingHom.comp (rename Sum.inl).toRingHom =
      MvPolynomial.map (C : K →+* MvPolynomial σ₂ K) :=
    RingHom.ext hinl
  have heq2 : e.toRingHom.comp (rename Sum.inr).toRingHom =
      (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K)) :=
    RingHom.ext hinr
  have h1 : (I₁.map (rename (Sum.inl : σ₁ → σ₁ ⊕ σ₂)).toRingHom).map e.toRingHom =
      I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) := by
    rw [Ideal.map_map, heq1]
  have h2 : (I₂.map (rename (Sum.inr : σ₂ → σ₁ ⊕ σ₂)).toRingHom).map e.toRingHom =
      I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K)) := by
    rw [Ideal.map_map, heq2]
  rw [show (I₁.map (rename (Sum.inl : σ₁ → σ₁ ⊕ σ₂)).toRingHom ⊔
    I₂.map (rename (Sum.inr : σ₂ → σ₁ ⊕ σ₂)).toRingHom).height =
    ((I₁.map (rename (Sum.inl : σ₁ → σ₁ ⊕ σ₂)).toRingHom ⊔
      I₂.map (rename (Sum.inr : σ₂ → σ₁ ⊕ σ₂)).toRingHom).map e.toRingHom).height from
    (RingEquiv.height_map e _).symm]
  rw [Ideal.map_sup, h1, h2]

/-- The transferred ideal is prime when I₁ and I₂ are prime.

**Proof sketch**: Via `quotientEquivQuotientMvPolynomial`, the quotient by `I₂.map C`
is `MvPolynomial σ₁ (MvPolynomial σ₂ K / I₂)`. In this ring, the residual ideal is
`I₁.map(MvPolynomial.map (algebraMap K L))` where `L = MvPolynomial σ₂ K / I₂` is a
domain. For any prime `Q` minimal over this residual, `Q` is prime. The original ideal
`P'` is the preimage of `Q` in the quotient, hence prime.

The main Mathlib gap is showing that `I₁.map(map f)` has at least one minimal prime
in a polynomial ring over a domain, which follows from Noetherianity. -/
private lemma isPrime_transferred
    {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K))
    [I₁.IsPrime] [I₂.IsPrime] :
    (I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
     I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).IsPrime := by
  sorry

/-- The transferred ideal lies over I₂ via the natural algebra structure.

**Proof sketch**: We need `P'.comap C = I₂` where `C` is the coefficient embedding.
The inclusion `I₂ ⊆ P'.comap C` follows from `le_comap_map` (since `I₂.map C ⊆ P'`).
For the reverse, since `P'` is prime and the algebra `MvPolynomial σ₁ R` over `R` is
faithfully flat, `P'.comap C` is a prime containing `I₂`. The equality follows from
applying `MvPolynomial.map constantCoeff` (a retraction of `map C`) to show any element
of `(I₁.map(map C)).comap C` lies in `⊥ ⊆ I₂`, using that `I₁` is proper prime in
`MvPolynomial σ₁ K` and hence `I₁ ∩ K = {0}`. -/
private lemma liesOver_transferred
    {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K))
    [I₁.IsPrime] [I₂.IsPrime] :
    letI := isPrime_transferred (K := K) I₁ I₂
    (I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
     I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).LiesOver I₂ := by
  sorry

/-- The residual height of the transferred ideal equals height(I₁).

**Proof sketch**: After quotienting by `I₂.map C`, the ring
`MvPolynomial σ₁ (MvPolynomial σ₂ K) / I₂.map C` is isomorphic to
`MvPolynomial σ₁ (MvPolynomial σ₂ K / I₂)` via `quotientEquivQuotientMvPolynomial`.
Under this isomorphism, the residual ideal corresponds to
`I₁.map(MvPolynomial.map (algebraMap K L))` where `L = MvPolynomial σ₂ K / I₂`.

Since `K` is a field and `L` is a nonzero `K`-algebra (a domain), `L` is free over `K`,
so `MvPolynomial σ₁ L` is free (hence faithfully flat) over `MvPolynomial σ₁ K` via
`MvPolynomial.map`. Going-down gives `height(Q) = height(I₁)` for any minimal prime `Q`
of `I₁.map(map f)` (since `Q` lies over `I₁` and the residual in
`MvPolynomial σ₁ L / I₁.map(map f)` is a minimal prime, hence has height 0). Thus:
  `height(I₁.map(map f)) = inf { height(Q) : Q minimal } = height(I₁)`. -/
private lemma residual_height_eq
    {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K))
    [I₁.IsPrime] [I₂.IsPrime] :
    letI := isPrime_transferred (K := K) I₁ I₂
    ((I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
      I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).map
      (Ideal.Quotient.mk (I₂.map (algebraMap (MvPolynomial σ₂ K)
        (MvPolynomial σ₁ (MvPolynomial σ₂ K)))))).height =
    I₁.height := by
  sorry

/-- Heights add for prime ideals in disjoint variable sets in a polynomial ring.

Given primes `I₁` in `K[σ₁]` and `I₂` in `K[σ₂]`, the combined ideal
`I₁.map(rename inl) ⊔ I₂.map(rename inr)` in `K[σ₁ ⊕ σ₂]` has
height equal to `height(I₁) + height(I₂)`. -/
theorem MvPolynomial.height_sup_disjoint
    {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K))
    [I₁.IsPrime] [I₂.IsPrime] :
    (I₁.map (MvPolynomial.rename (Sum.inl : σ₁ → σ₁ ⊕ σ₂)).toRingHom ⊔
     I₂.map (MvPolynomial.rename (Sum.inr : σ₂ → σ₁ ⊕ σ₂)).toRingHom).height =
    I₁.height + I₂.height := by
  -- Step 1: Transfer to iterated polynomial ring via sumAlgEquiv
  rw [height_sup_eq_height_transferred I₁ I₂]
  -- Step 2: Apply going-down height formula
  -- The iterated ring MvPolynomial σ₁ (MvPolynomial σ₂ K) is naturally an algebra
  -- over MvPolynomial σ₂ K (via C), and this algebra is free hence flat hence going-down.
  letI : (I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
    I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).IsPrime :=
    isPrime_transferred I₁ I₂
  letI : (I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
    I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).LiesOver I₂ :=
    liesOver_transferred I₁ I₂
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown I₂, add_comm]
  -- Step 3: Show residual height equals I₁.height
  congr 1
  exact residual_height_eq I₁ I₂

end

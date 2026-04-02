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

/-- If `I` is a proper ideal of `K[σ]` and `L` is a domain `K`-algebra, then the only
constant polynomial in the extension `I.map(map(algebraMap K L))` is zero. Equivalently,
`(I.map(map(algebraMap K L))).comap (algebraMap L (MvPolynomial σ L)) = ⊥`.

**Proof**: Choose a `K`-basis `{eⱼ}` of `L`. Then `MvPolynomial σ L ≅ ⊕ⱼ K[σ] · eⱼ`
as `K[σ]`-modules, and `I.map(map(algebraMap K L))` decomposes as `⊕ⱼ I · eⱼ`.
For `l = Σⱼ lⱼ eⱼ ∈ L`, `C_L(l)` has `j`-th component `C_K(lⱼ)`. If `C_L(l)` lies
in the extension ideal, then `C_K(lⱼ) ∈ I` for all `j`. Since `I` is proper and `K`
is a field, `I.comap C_K = ⊥` (the only constant in a proper ideal of `K[σ]` is `0`),
giving `lⱼ = 0` for all `j`, hence `l = 0`.

Alternatively, via tensor products: `MvPolynomial σ L / I^e ≅ (K[σ]/I) ⊗_K L`, and
the image of `C_L(l)` is `1̄ ⊗ l`. By `one_tmul_eq_zero_iff` (using that `K[σ]/I` is
a nonzero free `K`-module, hence faithfully flat), `1̄ ⊗ l = 0` iff `l = 0`. -/
private lemma comap_C_map_map_algebraMap_eq_bot
    {σ : Type*} [DecidableEq σ] {L : Type*} [CommRing L] [IsDomain L] [Algebra K L]
    (I : Ideal (MvPolynomial σ K)) (hI : I ≠ ⊤) :
    (I.map (MvPolynomial.map (algebraMap K L))).comap
      (algebraMap L (MvPolynomial σ L)) = ⊥ := by
  rw [eq_bot_iff]
  intro l hl
  simp only [Ideal.mem_comap, Ideal.mem_bot, algebraMap_eq] at hl ⊢
  -- hl : C l ∈ I.map (MvPolynomial.map (algebraMap K L))
  -- Goal : l = 0
  -- Strategy: Build ring hom ψ : L[σ] →+* (K[σ]/I) ⊗[K] L that kills I.map(map f) and
  -- sends C(l) to 1 ⊗ l, then apply faithful flatness of K[σ]/I over K.
  set Q := MvPolynomial σ K ⧸ I
  set π : MvPolynomial σ K →+* Q := Ideal.Quotient.mk I
  haveI : Nontrivial Q := Ideal.Quotient.nontrivial hI
  haveI : Module.Free K Q := Module.Free.of_divisionRing K Q
  haveI : Module.FaithfullyFlat K Q := inferInstance
  -- ψ evaluates coefficients via includeRight and variables via i ↦ π(Xᵢ) ⊗ 1
  let incR := (Algebra.TensorProduct.includeRight (R := K) (A := Q) (B := L)).toRingHom
  let incL := Algebra.TensorProduct.includeLeftRingHom (R := K) (A := Q) (B := L)
  let ψ := eval₂Hom incR (fun i => incL (π (X i)))
  -- (1) ψ(C l) = 1 ⊗ l
  have hψC : ψ (C l) = (1 : Q) ⊗ₜ[K] l := by
    simp [ψ, eval₂Hom_C, incR, Algebra.TensorProduct.includeRight_apply]
  -- (2) ψ ∘ (MvPolynomial.map (algebraMap K L)) = incL ∘ π
  have hψ_comp : ψ.comp (MvPolynomial.map (algebraMap K L)) = incL.comp π := by
    apply ringHom_ext
    · -- Constants: both reduce to algebraMap K (Q ⊗ L)
      intro k
      simp only [RingHom.comp_apply, map_C]
      show eval₂ incR (fun i => incL (π (X i))) (C (algebraMap K L k)) =
        incL (π (C k))
      -- Both sides equal algebraMap K (Q ⊗[K] L) k
      simp only [eval₂_C]
      change incR (algebraMap K L k) = incL (algebraMap K Q k)
      -- incR(algebraMap K L k) = 1 ⊗ algebraMap K L k = algebraMap K (Q ⊗ L) k
      -- incL(algebraMap K Q k) = algebraMap K Q k ⊗ 1 = algebraMap K (Q ⊗ L) k
      show Algebra.TensorProduct.includeRight (algebraMap K L k) =
        Algebra.TensorProduct.includeLeftRingHom (algebraMap K Q k)
      trans (algebraMap K (TensorProduct K Q L) k)
      · exact (Algebra.TensorProduct.includeRight (R := K) (A := Q) (B := L)).commutes k
      · exact ((Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := Q) (B := L)).commutes k).symm
    · -- Variables: both give incL(π(Xᵢ))
      intro i
      simp only [RingHom.comp_apply, map_X]
      show eval₂ incR (fun i => incL (π (X i))) (X i) = incL (π (X i))
      simp [eval₂_X]
  -- (3) ψ kills I.map(map f): the kernel of ψ contains I.map(map f)
  have hψ_kill : I.map (MvPolynomial.map (algebraMap K L)) ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    -- ψ(map(algebraMap K L)(g)) = (ψ.comp(map(algebraMap K L)))(g) = (incL.comp π)(g) = incL(π g)
    change (ψ.comp (MvPolynomial.map (algebraMap K L))) g = 0
    rw [hψ_comp, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero]
  -- (4) Combine: C l ∈ I.map(map f) gives ψ(C l) = 0, i.e. 1 ⊗ l = 0 in Q ⊗ L
  have h0 : (1 : Q) ⊗ₜ[K] l = 0 := hψC ▸ (hψ_kill hl)
  -- (5) Faithful flatness: (1 : Q) ⊗ l = 0 iff l = 0
  exact (Module.FaithfullyFlat.one_tmul_eq_zero_iff K L l).mp h0

/-- The transferred ideal lies over I₂ via the natural algebra structure.

**Proof sketch**: We need `P'.comap C = I₂` where `C` is the coefficient embedding.
The inclusion `I₂ ⊆ P'.comap C` follows from `le_comap_map` (since `I₂.map C ⊆ P'`).
For the reverse, apply `map(Quotient.mk I₂)` to transfer to `MvPolynomial σ₁ L` where
`L = MvPolynomial σ₂ K / I₂` is a domain. The image of `I₂.map C` vanishes, so
`C_L(π(f)) ∈ I₁.map(map(algebraMap K L))`. By `comap_C_map_map_algebraMap_eq_bot`
(no nonzero constant lies in the extension of a proper ideal from `K[σ]` to `L[σ]`),
`π(f) = 0`, hence `f ∈ I₂`. -/
private lemma liesOver_transferred
    {σ₁ σ₂ : Type*} [Fintype σ₁] [Fintype σ₂] [DecidableEq σ₁] [DecidableEq σ₂]
    (I₁ : Ideal (MvPolynomial σ₁ K)) (I₂ : Ideal (MvPolynomial σ₂ K))
    [I₁.IsPrime] [I₂.IsPrime] :
    letI := isPrime_transferred (K := K) I₁ I₂
    (I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
     I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))).LiesOver I₂ := by
  set P := I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
    I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))
  constructor
  show I₂ = P.comap (algebraMap (MvPolynomial σ₂ K) (MvPolynomial σ₁ (MvPolynomial σ₂ K)))
  rw [algebraMap_eq]
  apply le_antisymm
  · -- Easy direction: I₂ ≤ P.comap C
    intro f hf
    simp only [Ideal.mem_comap]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hf)
  · -- Hard direction: P.comap C ≤ I₂
    -- Apply map(Quotient.mk I₂) to transfer to MvPolynomial σ₁ L where L is a domain.
    -- Then use comap_C_map_map_algebraMap_eq_bot.
    intro f hf
    simp only [Ideal.mem_comap] at hf
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    set π : MvPolynomial σ₂ K →+* (MvPolynomial σ₂ K ⧸ I₂) := Ideal.Quotient.mk I₂
    set mapπ : MvPolynomial σ₁ (MvPolynomial σ₂ K) →+*
        MvPolynomial σ₁ (MvPolynomial σ₂ K ⧸ I₂) := MvPolynomial.map π
    -- (map π)(C(f)) ∈ (map π)(P)
    have hfP : mapπ ((C : MvPolynomial σ₂ K →+* _) f) ∈ P.map mapπ :=
      Ideal.mem_map_of_mem _ hf
    -- P.map(mapπ) = I₁.map(map C).map(mapπ) ⊔ I₂.map(C).map(mapπ)
    rw [show P = I₁.map (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) ⊔
        I₂.map (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K)) from rfl,
      Ideal.map_sup, Ideal.map_map, Ideal.map_map] at hfP
    -- The I₂ part maps to ⊥: π kills I₂, so (map π) ∘ C kills I₂
    have h_kill : I₂.map (mapπ.comp
        (C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K))) = ⊥ := by
      rw [Ideal.map_eq_bot_iff_le_ker]
      intro q hq
      rw [RingHom.mem_ker]
      show mapπ ((C : MvPolynomial σ₂ K →+* _) q) = 0
      simp only [mapπ, map_C, π]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero]
    rw [h_kill, sup_bot_eq] at hfP
    -- Now hfP : mapπ(C(f)) ∈ I₁.map(mapπ.comp (map C))
    -- mapπ.comp (map C) = map(π.comp C) = map(algebraMap K L)
    -- mapπ(C(f)) = C_L(π(f)) where C_L is the coeff embedding L → MvPolynomial σ₁ L
    -- So: C_L(π(f)) ∈ I₁.map(map(algebraMap K L))
    -- By comap_C_map_map_algebraMap_eq_bot: π(f) = 0
    have hne : I₁ ≠ ⊤ := IsPrime.ne_top inferInstance
    have key := comap_C_map_map_algebraMap_eq_bot (L := MvPolynomial σ₂ K ⧸ I₂) I₁ hne
    rw [eq_bot_iff] at key
    -- Show: π(f) ∈ (I₁.map(map(algebraMap K L))).comap C_L
    -- which by the key lemma gives π(f) ∈ ⊥, i.e., π(f) = 0
    suffices h : π f ∈ (I₁.map (MvPolynomial.map (algebraMap K (MvPolynomial σ₂ K ⧸ I₂)))).comap
        (algebraMap (MvPolynomial σ₂ K ⧸ I₂)
          (MvPolynomial σ₁ (MvPolynomial σ₂ K ⧸ I₂))) from
      Ideal.mem_bot.mp (key h)
    simp only [Ideal.mem_comap, algebraMap_eq]
    -- Goal: C(π(f)) ∈ I₁.map(map(algebraMap K L))
    -- Rewrite: C(π(f)) = (map π)(C(f)) and map(algebraMap K L) = (map π) ∘ (map C)
    have hmap_C : (C : MvPolynomial σ₂ K ⧸ I₂ →+*
        MvPolynomial σ₁ (MvPolynomial σ₂ K ⧸ I₂)) (π f) =
        mapπ ((C : MvPolynomial σ₂ K →+* MvPolynomial σ₁ (MvPolynomial σ₂ K)) f) := by
      simp [mapπ, map_C]
    have hmap_comp : MvPolynomial.map (algebraMap K (MvPolynomial σ₂ K ⧸ I₂)) =
        mapπ.comp (MvPolynomial.map (C : K →+* MvPolynomial σ₂ K)) := by
      have halg : algebraMap K (MvPolynomial σ₂ K ⧸ I₂) =
          π.comp (C : K →+* MvPolynomial σ₂ K) := by
        ext k
        show algebraMap K (MvPolynomial σ₂ K ⧸ I₂) k = π (C k)
        rw [IsScalarTower.algebraMap_apply K (MvPolynomial σ₂ K) (MvPolynomial σ₂ K ⧸ I₂)]
        simp [algebraMap_eq, π]
      rw [halg]
      -- map(π.comp C) = (map π).comp(map C) -- MvPolynomial.map_map as ring hom equality
      exact RingHom.ext (fun p => (MvPolynomial.map_map
        (C : K →+* MvPolynomial σ₂ K) π p).symm)
    rw [hmap_C, hmap_comp]
    -- Goal: mapπ(C(f)) ∈ I₁.map(mapπ.comp(map C))
    exact hfP

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

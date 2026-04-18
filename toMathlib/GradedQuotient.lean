/-
Copyright: BEI Lean project.

# Graded structure on a quotient by a homogeneous ideal

If `A` is a graded ring and `I : Ideal A` is homogeneous, then the quotient
`A ⧸ I` inherits a graded structure with graded pieces
`(𝒜 i).map (Ideal.Quotient.mk I)`.

This file builds `GradedRing` on the quotient as a reusable piece of
infrastructure for working with Stanley–Reisner-type rings.

## Status

- `SetLike.GradedMonoid` instance: proved.
- `DirectSum.Decomposition` (as a `def` under the homogeneity hypothesis): proved.
- `GradedRing` (assembled from the above): proved.
-/

import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

namespace GradedQuotient

open DirectSum

/-- The induced graded piece on `A ⧸ I`: the image of `𝒜 i` under the quotient map. -/
def gradedQuotientPiece {ι R A : Type*}
    [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
    [CommRing A] [Algebra R A]
    (𝒜 : ι → Submodule R A)
    (I : Ideal A) (i : ι) : Submodule R (A ⧸ I) :=
  (𝒜 i).map ((Ideal.Quotient.mkₐ R I).toLinearMap)

variable {ι R A : Type*}
variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R]
variable [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedRing 𝒜]
variable (I : Ideal A)

/-- `1 ∈ gradedQuotientPiece 0`. -/
instance : SetLike.GradedOne (gradedQuotientPiece 𝒜 I) where
  one_mem := ⟨1, SetLike.GradedOne.one_mem, by simp⟩

/-- Multiplication compatibility. -/
instance : SetLike.GradedMul (gradedQuotientPiece 𝒜 I) where
  mul_mem {_ _ _ _} hx hy := by
    simp only [gradedQuotientPiece, Submodule.mem_map] at hx hy ⊢
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    refine ⟨a * b, SetLike.GradedMul.mul_mem ha hb, ?_⟩
    simp

instance : SetLike.GradedMonoid (gradedQuotientPiece 𝒜 I) where

/-!
### Decomposition instance

We build a `DirectSum.Decomposition` on `gradedQuotientPiece 𝒜 I` under the
hypothesis that `I` is a homogeneous ideal.  Strategy:

* use the decomposition of `A` to define an additive hom
  `φ : A →+ ⨁ i, gradedQuotientPiece 𝒜 I i`;
* verify that `I ⊆ ker φ` using homogeneity;
* descend `φ` through `A ⧸ I` to obtain a candidate inverse to
  `DirectSum.coeAddMonoidHom` of the quotient pieces.
-/

section Decomposition

/-- The additive hom `𝒜 i →+ gradedQuotientPiece 𝒜 I i` given by applying the
quotient map `A →+* A ⧸ I`. -/
def pieceToQuotient (i : ι) :
    (𝒜 i : Submodule R A) →+ (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I)) where
  toFun a := ⟨Ideal.Quotient.mk I a, a.1, a.2, rfl⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp [map_add]

/-- The additive hom `A →+ ⨁ i, gradedQuotientPiece 𝒜 I i` built by decomposing
along `𝒜` and then applying the quotient map componentwise. -/
def forwardHom :
    A →+ (⨁ i, (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) :=
  (DirectSum.toAddMonoid
      (fun i => (DirectSum.of
        (fun i => (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) i).comp
        (pieceToQuotient 𝒜 I i))).comp
    (DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom

lemma forwardHom_apply_of_mem {i : ι} {a : A} (ha : a ∈ 𝒜 i) :
    forwardHom 𝒜 I a =
      DirectSum.of (fun i => (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) i
        ⟨Ideal.Quotient.mk I a, a, ha, rfl⟩ := by
  unfold forwardHom
  simp [DirectSum.decompose_of_mem _ ha, pieceToQuotient]

lemma forwardHom_vanishes_on_ideal (hI : I.IsHomogeneous 𝒜) {x : A} (hx : x ∈ I) :
    forwardHom 𝒜 I x = 0 := by
  classical
  -- write x as the sum of its homogeneous components and evaluate `forwardHom` termwise
  conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 x]
  rw [map_sum]
  refine Finset.sum_eq_zero ?_
  intro i _
  have hmem : (DirectSum.decompose 𝒜 x i : A) ∈ 𝒜 i := (DirectSum.decompose 𝒜 x i).2
  have hinI : (DirectSum.decompose 𝒜 x i : A) ∈ I := hI i hx
  rw [forwardHom_apply_of_mem 𝒜 I hmem]
  -- the element `⟨mk I (component), ...⟩` is the zero element of the quotient piece,
  -- since the component lies in I
  have h0 :
      (⟨Ideal.Quotient.mk I (DirectSum.decompose 𝒜 x i : A),
        (DirectSum.decompose 𝒜 x i : A),
        hmem, rfl⟩ :
        (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) = 0 := by
    apply Subtype.ext
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hinI]
  rw [h0, map_zero]

/-- The descent of `forwardHom` through `A ⧸ I`, using that `forwardHom` vanishes on `I`.
This is the candidate `decompose` map for the graded quotient. -/
def decomposeHom (hI : I.IsHomogeneous 𝒜) :
    A ⧸ I →+ (⨁ i, (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) where
  toFun := Quotient.lift (forwardHom 𝒜 I) (by
    intro a b hab
    have hdiff : a - b ∈ I := (Submodule.quotientRel_def I).mp hab
    have hvan : forwardHom 𝒜 I (a - b) = 0 :=
      forwardHom_vanishes_on_ideal 𝒜 I hI hdiff
    -- rewrite `a = b + (a - b)` to avoid needing subtraction on the codomain
    have heq : a = b + (a - b) := by ring
    calc forwardHom 𝒜 I a
        = forwardHom 𝒜 I (b + (a - b)) := by rw [← heq]
      _ = forwardHom 𝒜 I b + forwardHom 𝒜 I (a - b) := map_add _ _ _
      _ = forwardHom 𝒜 I b + 0 := by rw [hvan]
      _ = forwardHom 𝒜 I b := by rw [add_zero])
  map_zero' := by
    change Quotient.lift (forwardHom 𝒜 I) _ (Quotient.mk _ 0) = 0
    simp [map_zero]
  map_add' := by
    rintro ⟨a⟩ ⟨b⟩
    change Quotient.lift (forwardHom 𝒜 I) _ (Quotient.mk _ (a + b)) =
      Quotient.lift (forwardHom 𝒜 I) _ (Quotient.mk _ a) +
        Quotient.lift (forwardHom 𝒜 I) _ (Quotient.mk _ b)
    simp [map_add]

@[simp]
lemma decomposeHom_mk (hI : I.IsHomogeneous 𝒜) (a : A) :
    decomposeHom 𝒜 I hI (Ideal.Quotient.mk I a) = forwardHom 𝒜 I a := rfl

/-- Key computation: the composite `coeAddMonoidHom ∘ componentwiseToQuotient` equals
`Ideal.Quotient.mk I ∘ coeAddMonoidHom 𝒜`. -/
private lemma coe_comp_forward_aux (s : ⨁ i, ((𝒜 i : Submodule R A) : Submodule R A)) :
    DirectSum.coeAddMonoidHom (gradedQuotientPiece 𝒜 I)
        (DirectSum.toAddMonoid
          (fun i => (DirectSum.of
            (fun i => (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) i).comp
            (pieceToQuotient 𝒜 I i)) s) =
      Ideal.Quotient.mk I (DirectSum.coeAddMonoidHom 𝒜 s) := by
  refine DirectSum.induction_on s ?_ ?_ ?_
  · simp
  · intro i x
    simp [pieceToQuotient]
  · intro x y hx hy
    simp [map_add, hx, hy]

/-- The decomposition instance built via `ofAddHom`. -/
def decomposition (hI : I.IsHomogeneous 𝒜) :
    DirectSum.Decomposition (gradedQuotientPiece 𝒜 I) :=
  DirectSum.Decomposition.ofAddHom (M := A ⧸ I) (ℳ := gradedQuotientPiece 𝒜 I)
    (decomposeHom 𝒜 I hI)
    (by
      -- `coeAddMonoidHom ∘ decomposeHom = id` on `A ⧸ I`
      refine AddMonoidHom.ext ?_
      intro a
      refine Quotient.inductionOn' a ?_
      intro a
      change DirectSum.coeAddMonoidHom _ (decomposeHom 𝒜 I hI (Ideal.Quotient.mk I a)) =
        Ideal.Quotient.mk I a
      rw [decomposeHom_mk]
      -- compute `coeAddMonoidHom ∘ forwardHom a`
      change DirectSum.coeAddMonoidHom (gradedQuotientPiece 𝒜 I)
          (DirectSum.toAddMonoid
            (fun i => (DirectSum.of
              (fun i => (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) i).comp
              (pieceToQuotient 𝒜 I i))
            ((DirectSum.decomposeAddEquiv 𝒜).toAddMonoidHom a)) =
        Ideal.Quotient.mk I a
      rw [coe_comp_forward_aux]
      -- reduce `coeAddMonoidHom 𝒜 (decomposeAddEquiv 𝒜 a)` to `a`
      simp only [AddEquiv.toAddMonoidHom_eq_coe]
      have hcoe : DirectSum.coeAddMonoidHom 𝒜 =
          (DirectSum.decomposeAddEquiv 𝒜).symm.toAddMonoidHom := rfl
      rw [hcoe]
      simp)
    (by
      -- `decomposeHom ∘ coeAddMonoidHom = id` on `⨁ i, gradedQuotientPiece`
      refine DFinsupp.addHom_ext' ?_
      intro i
      refine AddMonoidHom.ext ?_
      rintro ⟨q, a, ha, rfl⟩
      change decomposeHom 𝒜 I hI
          (DirectSum.coeAddMonoidHom (gradedQuotientPiece 𝒜 I)
            (DirectSum.of (fun i => (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) i
              ⟨Ideal.Quotient.mk I a, a, ha, rfl⟩)) =
        DirectSum.of (fun i => (gradedQuotientPiece 𝒜 I i : Submodule R (A ⧸ I))) i
          ⟨Ideal.Quotient.mk I a, a, ha, rfl⟩
      rw [DirectSum.coeAddMonoidHom_of]
      change decomposeHom 𝒜 I hI (Ideal.Quotient.mk I a) = _
      rw [decomposeHom_mk, forwardHom_apply_of_mem 𝒜 I ha])

/-- The full `GradedRing` structure on `A ⧸ I` given a homogeneous ideal `I`. -/
def gradedRing (hI : I.IsHomogeneous 𝒜) :
    GradedRing (gradedQuotientPiece 𝒜 I) :=
  let _ : DirectSum.Decomposition (gradedQuotientPiece 𝒜 I) := decomposition 𝒜 I hI
  { (inferInstance : SetLike.GradedMonoid (gradedQuotientPiece 𝒜 I)) with
    decompose' := (decomposition 𝒜 I hI).decompose'
    left_inv := (decomposition 𝒜 I hI).left_inv
    right_inv := (decomposition 𝒜 I hI).right_inv }

end Decomposition

end GradedQuotient

end

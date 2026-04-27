import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import BEI.Equidim.Transport
import BEI.Equidim.ClosedGraphIntervals
import BEI.Equidim.IteratedRegularity
import BEI.Equidim.AugmentationLocalCM
import BEI.Equidim.GlobalCMSetup
import BEI.Equidim.F2Scaffolding
import BEI.Equidim.L4Iso
import BEI.Equidim.L1Iso
import BEI.Equidim.ReducedHHLocalCM
import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import BEI.ReducedHH
import toMathlib.Equidim.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Regular.RegularSequence
import toMathlib.QuotientDimension
import toMathlib.IdealQuotientHelpers
import toMathlib.MinimalPrimesRegular
import toMathlib.MvPolynomialHomogeneous
import toMathlib.CohenMacaulay.Defs
import toMathlib.CohenMacaulay.Basic
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.TensorPolynomialAway
import toMathlib.PolynomialAwayTensor
import toMathlib.TensorLocalisation
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.MvPolynomial

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

noncomputable section

open MvPolynomial SimpleGraph

/-!
# Equidimensional surrogate theorems for binomial edge ideals

Uses `IsEquidimRing` from `toMathlib/Equidim/Defs.lean`, the local
equidimensional surrogate currently used in the BEI project.

The surrogate API, the Herzog–Hibi bridge, and the monomial initial ideal
material live in `BEI/Equidim/MonomialInitial.lean` and are re-exported via
the import above. This file carries:

- the bipartite edge monomial ideal and its bridge to the variable-pair API;
- the closed-graph component-count lemmas;
- the regular-sequence and dimension-formula machinery;
- the global Cohen–Macaulay theorem
  `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` and its
  paper-facing wrapper `monomialInitialIdeal_isCohenMacaulay`.

## Reference: Herzog et al. (2010), Section 1
-/


/-! #### Session B: promote local CM at `augIdealReduced` to global CM. -/

/-- **Session B**: The localisation of the reduced HH ring at its augmentation
ideal is globally Cohen–Macaulay. Immediate from Session A′ and
`IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`. -/
private theorem isCohenMacaulayRing_at_augIdealReduced
    {r : ℕ} {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := by
  haveI := isCohenMacaulayLocalRing_at_augIdealReduced (K := K) hHH
  exact IsCohenMacaulayRing.of_isCohenMacaulayLocalRing

/-! #### Session C1: the bundled equiv `E_U`.

Composing `L1Iso`, `L4Iso`, the tensor associator, and `polynomialAwayTensorEquiv`,
we obtain a single K-algebra equivalence from the monomial localisation of the
HH quotient at `s_U` to
`reducedHHRing G' ⊗[K] Localization.Away (rename Sum.inr (hhUnitProductSub U))`,
where `G' = smallerHHGraph G (↑U)` and the `Sum.inr` embeds the `U`-index into
`↑(lambdaSet G (↑U)) ⊕ ↑(U : Set _)`. -/
/-- **Session C1: the bundled monomial-localisation equiv `E_U`** for an
independent finset `U`. Specialised to `K : Type` (universe 0) so that it can
be composed with `polynomialAwayTensorEquiv`, which requires all type arguments
in a single universe. All downstream callers instantiate `K` at universe 0. -/
private noncomputable def E_U {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    Localization.Away
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U))
      ≃ₐ[K]
      TensorProduct K
        (BEI.reducedHHRing (K := K) (smallerHHGraph G (U : Set _)))
        (Localization.Away
          (rename (R := K)
            (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
            (τ := ↑(lambdaSet G (U : Set _)) ⊕
              ↑((U : Set (BinomialEdgeVars (Fin n)))))
            Sum.inr
            (hhUnitProductSub (K := K) U))) := by
  classical
  -- Abbreviations for readability and to pin down types for typeclass search.
  let Uset : Set (BinomialEdgeVars (Fin n)) := ↑U
  let G' := smallerHHGraph G Uset
  let Λ : Set (BinomialEdgeVars (Fin n)) := lambdaSet G Uset
  let A := BEI.reducedHHRing (K := K) G'
  let P := MvPolynomial (↑Λ) K
  let Lsub := Localization.Away (hhUnitProductSub (K := K) U)
  -- Step 1: L1 iso.
  refine (L1Iso (K := K) G U hU).trans ?_
  -- Step 2: apply L4Iso to the left tensor factor.
  refine (Algebra.TensorProduct.congr
      (L4Iso (K := K) hHH Uset hU)
      (AlgEquiv.refl (R := K) (A₁ := Lsub))).trans ?_
  -- Step 3: reassociate the triple tensor.
  refine (Algebra.TensorProduct.assoc K K K A P Lsub).trans ?_
  -- Step 4: merge the polynomial factor with the localisation.
  exact Algebra.TensorProduct.congr
    (AlgEquiv.refl (R := K) (A₁ := A))
    (polynomialAwayTensorEquiv
      (K := K) (α := (Λ : Type _))
      (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
      (hhUnitProductSub (K := K) U))

set_option maxHeartbeats 400000 in
-- heartbeats needed: E_U is a 4-step AlgEquiv.trans; unfolding its action on a
-- specific element requires elaborating nested tensor/localization types.
/-- **E_U forward on a paired-left survivor variable**.

For `a : Fin (pairedCount G U)`, the embedded index `c_a := pairedSurvivorsVal G U a`
gives a paired-left survivor `v_emb = Sum.inl c_a ∈ hhSurvivors G U`. Applying `E_U` to
the algebraMap image of `mkI (X v_emb)` yields the pure tensor
`mkI_red (X (Sum.inl a)) ⊗ 1`.

Proof: trace the 4-step composition of `E_U`:
1. `L1Iso` sends it via `L1Forward` to `(mk_W (X ⟨v_emb, hW⟩)) ⊗ 1`.
2. `Algebra.TensorProduct.congr (L4Iso …) AlgEquiv.refl` applied to the pure tensor
   gives `(L4Iso (mk_W (X ⟨v_emb, hW⟩))) ⊗ 1`; by `L4Forward_mk_X` +
   `L4ForwardGen_inl` + `L4ForwardInl_of_paired` + `pairedSurvivorsIdx_val`, the
   inner image is `(mk_red (X (Sum.inl a))) ⊗ 1`, yielding
   `((mk_red (X (Sum.inl a))) ⊗ 1) ⊗ 1`.
3. The associator sends `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`, giving
   `(mk_red (X (Sum.inl a))) ⊗ (1 ⊗ 1)`.
4. `congr refl polynomialAwayTensorEquiv` applied to a pure tensor sends
   `x ⊗ w ↦ x ⊗ (polynomialAwayTensorEquiv w)`; `polynomialAwayTensorEquiv (1 ⊗ 1) = 1`
   by `map_one`. -/
private theorem E_U_algebraMap_mkI_X_pairedSurvivor_inl
    {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : Fin (pairedCount G (U : Set _))) :
    (E_U hHH U hU) (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl (pairedSurvivorsVal G (U : Set _) a))))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
        (smallerHHGraph G (U : Set _)))) (X (Sum.inl a)))
          ⊗ₜ[K] (1 : Localization.Away
            (rename (R := K)
              (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
              (τ := ↑(lambdaSet G (U : Set _)) ⊕
                ↑((U : Set (BinomialEdgeVars (Fin n)))))
              Sum.inr
              (hhUnitProductSub (K := K) U))) := by
  classical
  set i : Fin n := pairedSurvivorsVal G (U : Set _) a with hi_def
  have hi_mem : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
  have hW : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G (U : Set _) := pairedSurvivors_inl_mem G _ hi_mem
  -- Unfold E_U as a sequence of four AlgEquiv.trans applications.
  unfold E_U
  -- Step 1: L1Iso applied to algebraMap (mkI (X (Sum.inl i))) = (mk_W X ⟨_, hW⟩) ⊗ 1.
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hStep1 : L1Iso (K := K) G U hU (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl i)))) =
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inl i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1) := by
    simp only [L1Iso, AlgEquiv.ofAlgHom_apply]
    unfold L1Forward
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change L1ForwardQuot (K := K) G U hU
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl i))) = _
    rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W hW]
  rw [hStep1]
  -- Step 2: Algebra.TensorProduct.congr (L4Iso …) refl on a pure tensor.
  -- Compute L4Iso on (mk X ⟨Sum.inl i, hW⟩) first.
  have hi_ps : i ∈ pairedSurvivors G (U : Set _) := hi_mem
  have hidx : pairedSurvivorsIdx G (U : Set _) hi_ps = a :=
    pairedSurvivorsIdx_val G _ a
  have hStep2_inner :
      (L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inl i, hW⟩)) =
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
            (smallerHHGraph G (U : Set _))))
          (X (Sum.inl a))) ⊗ₜ[K]
          (1 : MvPolynomial (lambdaSet G (U : Set _)) K) := by
    simp only [L4Iso, AlgEquiv.ofAlgHom_apply]
    rw [L4Forward_mk_X]
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨Sum.inl i, hW⟩ rfl,
      L4ForwardInl_of_paired (K := K) G (U : Set _) hW hi_ps]
    rw [hidx]
  -- Step 2: congr (L4Iso …) refl on the pure tensor (mk ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (L4Iso (K := K) hHH (U : Set _) hU)
        (AlgEquiv.refl (R := K) (A₁ := Localization.Away
          (hhUnitProductSub (K := K) U))))
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inl i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      ((L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inl i, hW⟩))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  rw [hStep2_inner]
  -- Step 3: the associator maps (x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z).
  rw [Algebra.TensorProduct.assoc_tmul]
  -- Step 4: congr refl polynomialAwayTensorEquiv on pure tensor x ⊗ (1 ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K)
        (A₁ := BEI.reducedHHRing (K := K) (smallerHHGraph G (U : Set _))))
        (polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U)))
      (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inl a))) ⊗ₜ[K]
        ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
          (1 : Localization.Away (hhUnitProductSub (K := K) U)))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inl a))) ⊗ₜ[K]
        ((polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U))
          ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
            (1 : Localization.Away (hhUnitProductSub (K := K) U))))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  -- polynomialAwayTensorEquiv (1 ⊗ 1) = polynomialAwayTensorEquiv 1 = 1.
  have h11 : ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
      (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      (1 : TensorProduct K (MvPolynomial (lambdaSet G (U : Set _)) K)
        (Localization.Away (hhUnitProductSub (K := K) U))) := rfl
  rw [h11, map_one]

set_option maxHeartbeats 400000 in
-- heartbeats needed: E_U is a 4-step AlgEquiv.trans; unfolding its action on a
-- specific element requires elaborating nested tensor/localization types.
/-- **E_U forward on a paired-right survivor variable**.

Symmetric companion to `E_U_algebraMap_mkI_X_pairedSurvivor_inl`: for
`a : Fin (pairedCount G U)`, the embedded index `c_a := pairedSurvivorsVal G U a`
gives a paired-right survivor `v_emb = Sum.inr c_a ∈ hhSurvivors G U`. Applying `E_U`
to the algebraMap image of `mkI (X v_emb)` yields the pure tensor
`mkI_red (X (Sum.inr a)) ⊗ 1`. -/
private theorem E_U_algebraMap_mkI_X_pairedSurvivor_inr
    {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : Fin (pairedCount G (U : Set _))) :
    (E_U hHH U hU) (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr (pairedSurvivorsVal G (U : Set _) a))))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
        (smallerHHGraph G (U : Set _)))) (X (Sum.inr a)))
          ⊗ₜ[K] (1 : Localization.Away
            (rename (R := K)
              (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
              (τ := ↑(lambdaSet G (U : Set _)) ⊕
                ↑((U : Set (BinomialEdgeVars (Fin n)))))
              Sum.inr
              (hhUnitProductSub (K := K) U))) := by
  classical
  set i : Fin n := pairedSurvivorsVal G (U : Set _) a with hi_def
  have hi_mem : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
  have hW : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G (U : Set _) := pairedSurvivors_inr_mem G _ hi_mem
  -- Unfold E_U as a sequence of four AlgEquiv.trans applications.
  unfold E_U
  -- Step 1: L1Iso applied to algebraMap (mkI (X (Sum.inr i))) = (mk_W X ⟨_, hW⟩) ⊗ 1.
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hStep1 : L1Iso (K := K) G U hU (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr i)))) =
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inr i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1) := by
    simp only [L1Iso, AlgEquiv.ofAlgHom_apply]
    unfold L1Forward
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change L1ForwardQuot (K := K) G U hU
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr i))) = _
    rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W hW]
  rw [hStep1]
  -- Step 2: Algebra.TensorProduct.congr (L4Iso …) refl on a pure tensor.
  -- Compute L4Iso on (mk X ⟨Sum.inr i, hW⟩) first.
  have hi_ps : i ∈ pairedSurvivors G (U : Set _) := hi_mem
  have hidx : pairedSurvivorsIdx G (U : Set _) hi_ps = a :=
    pairedSurvivorsIdx_val G _ a
  have hStep2_inner :
      (L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inr i, hW⟩)) =
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
            (smallerHHGraph G (U : Set _))))
          (X (Sum.inr a))) ⊗ₜ[K]
          (1 : MvPolynomial (lambdaSet G (U : Set _)) K) := by
    simp only [L4Iso, AlgEquiv.ofAlgHom_apply]
    rw [L4Forward_mk_X]
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨Sum.inr i, hW⟩ rfl,
      L4ForwardInr_of_paired (K := K) G (U : Set _) hW hi_ps]
    rw [hidx]
  -- Step 2: congr (L4Iso …) refl on the pure tensor (mk ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (L4Iso (K := K) hHH (U : Set _) hU)
        (AlgEquiv.refl (R := K) (A₁ := Localization.Away
          (hhUnitProductSub (K := K) U))))
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inr i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      ((L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inr i, hW⟩))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  rw [hStep2_inner]
  -- Step 3: the associator maps (x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z).
  rw [Algebra.TensorProduct.assoc_tmul]
  -- Step 4: congr refl polynomialAwayTensorEquiv on pure tensor x ⊗ (1 ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K)
        (A₁ := BEI.reducedHHRing (K := K) (smallerHHGraph G (U : Set _))))
        (polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U)))
      (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inr a))) ⊗ₜ[K]
        ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
          (1 : Localization.Away (hhUnitProductSub (K := K) U)))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inr a))) ⊗ₜ[K]
        ((polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U))
          ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
            (1 : Localization.Away (hhUnitProductSub (K := K) U))))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  -- polynomialAwayTensorEquiv (1 ⊗ 1) = polynomialAwayTensorEquiv 1 = 1.
  have h11 : ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
      (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      (1 : TensorProduct K (MvPolynomial (lambdaSet G (U : Set _)) K)
        (Localization.Away (hhUnitProductSub (K := K) U))) := rfl
  rw [h11, map_one]

/-! #### Main theorem -/

set_option maxHeartbeats 800000 in
-- heartbeats + synth budget needed: main graded local-to-global assembly is heavy.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Graded local-to-global for the HH quotient**: Under HH conditions, the quotient
`S ⧸ bipartiteEdgeMonomialIdeal G` is a Cohen–Macaulay ring.

The proof splits into two cases by whether a prime `p` is contained in the
augmentation ideal `m⁺`:

- **Case `p ≤ m⁺`**: By localization transitivity,
  `R_p ≅ (R_{m⁺})_{p'}` where `p' = p · R_{m⁺}`. Since `R_{m⁺}` is CM and CM localizes.
- **Case `p ⊄ m⁺`**: F2 route. Pick `U := {v | mkI(X v) ∉ p}`. The independent-set
  hypothesis holds by primality (edge monomials are zero in `R = S/I`). Localize away
  from `s_U := mkI(∏_{u ∈ U} X u)`; the bundled equiv `E_U` identifies this with
  `reducedHHRing(G') ⊗[K] Localization.Away(...)`. Push `p_Lsu` through `E_U` to get
  a prime `𝔓`; generator-level forward traces (C3a-inl/inr) plus maximality of
  `augIdealReduced` give `𝔓.comap includeLeft = augIdealReduced G'`. Apply the
  tensor-left-localisation bridge (C2) and the L7 replacement
  (`isCohenMacaulayLocalRing_localization_tensor_away`), then transport back.

References: Bruns–Herzog, Theorem 2.1.3(b); Herzog–Hibi (2005). -/
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal
    {K : Type} [Field K]
    {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G) := by
  set R := MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set m := augIdeal (K := K) G
  constructor
  intro p _
  by_cases hp : p ≤ m
  · -- Case p ⊆ augIdeal: CM by localization transitivity.
    set Rm := Localization.AtPrime m
    have hdisj : Disjoint (↑m.primeCompl : Set R) (↑p) := by
      rw [Set.disjoint_left]; intro x hx hxp; exact hx (hp hxp)
    set p' := Ideal.map (algebraMap R Rm) p
    haveI hp' : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Rm p ‹_› hdisj
    haveI : IsCohenMacaulayLocalRing Rm :=
      isCohenMacaulayLocalRing_at_augIdeal (K := K) hn hHH
    set q := Ideal.comap (algebraMap R Rm) p' with hq_def
    have hqp : q = p := IsLocalization.comap_map_of_isPrime_disjoint _ Rm ‹_› hdisj
    haveI : q.IsPrime := hqp ▸ ‹p.IsPrime›
    haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p') :=
      isCohenMacaulayLocalRing_localization_atPrime p'
    have hCM_q : IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
      isCohenMacaulayLocalRing_of_ringEquiv' ‹_›
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          m.primeCompl p').symm.toRingEquiv
    have hpc : q.primeCompl = p.primeCompl := by
      ext x; exact not_congr (by rw [hqp])
    exact cast (show IsCohenMacaulayLocalRing (Localization.AtPrime q) =
      IsCohenMacaulayLocalRing (Localization.AtPrime p) by
        change IsCohenMacaulayLocalRing (Localization q.primeCompl) =
          IsCohenMacaulayLocalRing (Localization p.primeCompl)
        rw [hpc]) hCM_q
  · -- Case p ⊄ augIdeal: F2 decomposition via E_U, C2 bridge, and L7 replacement.
    classical
    -- Step 1: Pick U = "unit" variables (those whose mkI image is NOT in p).
    set U : Finset (BinomialEdgeVars (Fin n)) :=
      Finset.univ.filter (fun v => (Ideal.Quotient.mk I (X v) : R) ∉ p) with hU_def
    -- Step 2: U is HH-independent. HH edge ⇒ X u * X v ∈ I ⇒ product = 0 ∈ p ⇒ one of
    -- mkI(X u), mkI(X v) is in p, contradicting membership in U.
    have hU_indep : hhIndep G (U : Set _) := by
      intro u v hu hv hedge
      have huf : u ∈ U := by exact_mod_cast hu
      have hvf : v ∈ U := by exact_mod_cast hv
      have hu_nmem : Ideal.Quotient.mk I (X u) ∉ p := (Finset.mem_filter.mp huf).2
      have hv_nmem : Ideal.Quotient.mk I (X v) ∉ p := (Finset.mem_filter.mp hvf).2
      obtain ⟨i, j, hj, hadj, hle, heq⟩ := hedge
      rw [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hmem : X (Sum.inl i) * X (Sum.inr j) ∈ I :=
        Ideal.subset_span ⟨i, j, hj, hadj, hle, rfl⟩
      have h_mul_zero :
          (Ideal.Quotient.mk I (X (Sum.inl i))) * (Ideal.Quotient.mk I (X (Sum.inr j))) = 0 := by
        rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      have h_mul_mem :
          (Ideal.Quotient.mk I (X (Sum.inl i))) * (Ideal.Quotient.mk I (X (Sum.inr j))) ∈ p := by
        rw [h_mul_zero]; exact p.zero_mem
      rcases ‹p.IsPrime›.mem_or_mem h_mul_mem with hxu | hxv
      · exact hu_nmem hxu
      · exact hv_nmem hxv
    -- Step 3: sU := mkI(∏_{u ∈ U} X u) ∉ p.
    set sU : R := Ideal.Quotient.mk I (hhUnitProduct (K := K) U) with hsU_def
    have hsU_nmem : sU ∉ p := by
      rw [hsU_def]
      unfold hhUnitProduct
      rw [map_prod]
      intro hmem
      rcases Ideal.IsPrime.prod_mem_iff.mp hmem with ⟨u, hu, hu_in⟩
      exact (Finset.mem_filter.mp hu).2 hu_in
    -- Step 4: localize R away from sU.
    set Lsu := Localization.Away sU
    have hdisj : Disjoint (↑(Submonoid.powers sU) : Set R) (↑p : Set R) := by
      rw [Set.disjoint_left]
      rintro x ⟨k, rfl⟩ hx
      exact hsU_nmem (‹p.IsPrime›.mem_of_pow_mem _ hx)
    set p_Lsu : Ideal Lsu := Ideal.map (algebraMap R Lsu) p with p_Lsu_def
    haveI hp_Lsu : p_Lsu.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ Lsu p ‹_› hdisj
    have hcomap_p : p_Lsu.comap (algebraMap R Lsu) = p :=
      IsLocalization.comap_map_of_isPrime_disjoint _ Lsu ‹_› hdisj
    -- Step 5: apply E_U and pull p_Lsu back to 𝔓.
    set G' : SimpleGraph (Fin (pairedCount G (U : Set _) + 1)) :=
      smallerHHGraph G (U : Set _) with G'_def
    set A := BEI.reducedHHRing (K := K) G' with A_def
    set Lnew := Localization.Away (rename (R := K)
      (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
      (τ := ↑(lambdaSet G (U : Set _)) ⊕
        ↑((U : Set (BinomialEdgeVars (Fin n)))))
      Sum.inr (hhUnitProductSub (K := K) U)) with Lnew_def
    let e_U := E_U (K := K) hHH U hU_indep
    set 𝔓 : Ideal (TensorProduct K A Lnew) := p_Lsu.comap e_U.symm.toRingHom with 𝔓_def
    haveI h𝔓 : 𝔓.IsPrime := Ideal.IsPrime.comap e_U.symm.toRingHom
    -- Step 6: 𝔓.comap includeLeft = augIdealReduced G'.
    have h_contract : 𝔓.comap
        (Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := A) (B := Lnew)).toRingHom =
        BEI.augIdealReduced (K := K) G' := by
      -- Each reduced variable lies in 𝔓.comap includeLeft.
      have h_gen : ∀ (v : BinomialEdgeVars (Fin (pairedCount G (U : Set _)))),
          ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G')) (X v) : A) ∈
            𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
              (A := A) (B := Lnew)).toRingHom := by
        intro v
        rw [Ideal.mem_comap]
        change ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G')) (X v) ⊗ₜ[K]
          (1 : Lnew)) ∈ 𝔓
        rcases v with a | a
        · set i := pairedSurvivorsVal G (U : Set _) a
          have hi_ps : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
          have hi_surv : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈
              hhSurvivors G (U : Set _) := pairedSurvivors_inl_mem G _ hi_ps
          have hi_not_in_U : (Sum.inl i : BinomialEdgeVars (Fin n)) ∉ U := by
            intro h
            exact hi_surv (Or.inl (by exact_mod_cast h))
          have hmkI_in_p : Ideal.Quotient.mk I (X (Sum.inl i)) ∈ p := by
            by_contra h_notin
            exact hi_not_in_U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_notin⟩)
          have halg_in : algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inl i))) ∈ p_Lsu :=
            Ideal.mem_map_of_mem _ hmkI_in_p
          have hC3a := E_U_algebraMap_mkI_X_pairedSurvivor_inl (K := K) hHH U hU_indep a
          have halg_eq :
              algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inl i))) =
                e_U.symm
                  (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                    (X (Sum.inl a))) ⊗ₜ[K] (1 : Lnew)) := by
            rw [← hC3a]; exact (AlgEquiv.symm_apply_apply e_U _).symm
          have hsymm_in : e_U.symm
              (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                (X (Sum.inl a))) ⊗ₜ[K] (1 : Lnew)) ∈ p_Lsu :=
            halg_eq ▸ halg_in
          rw [𝔓_def, Ideal.mem_comap]
          exact hsymm_in
        · set i := pairedSurvivorsVal G (U : Set _) a
          have hi_ps : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
          have hi_surv : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈
              hhSurvivors G (U : Set _) := pairedSurvivors_inr_mem G _ hi_ps
          have hi_not_in_U : (Sum.inr i : BinomialEdgeVars (Fin n)) ∉ U := by
            intro h
            exact hi_surv (Or.inl (by exact_mod_cast h))
          have hmkI_in_p : Ideal.Quotient.mk I (X (Sum.inr i)) ∈ p := by
            by_contra h_notin
            exact hi_not_in_U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_notin⟩)
          have halg_in : algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inr i))) ∈ p_Lsu :=
            Ideal.mem_map_of_mem _ hmkI_in_p
          have hC3a := E_U_algebraMap_mkI_X_pairedSurvivor_inr (K := K) hHH U hU_indep a
          have halg_eq :
              algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inr i))) =
                e_U.symm
                  (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                    (X (Sum.inr a))) ⊗ₜ[K] (1 : Lnew)) := by
            rw [← hC3a]; exact (AlgEquiv.symm_apply_apply e_U _).symm
          have hsymm_in : e_U.symm
              (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                (X (Sum.inr a))) ⊗ₜ[K] (1 : Lnew)) ∈ p_Lsu :=
            halg_eq ▸ halg_in
          rw [𝔓_def, Ideal.mem_comap]
          exact hsymm_in
      -- augIdealReduced ≤ comap (via span of variables + zero constant coefficient).
      have h_le_comap : BEI.augIdealReduced (K := K) G' ≤
          𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
            (A := A) (B := Lnew)).toRingHom := by
        intro x hx
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [BEI.augIdealReduced, RingHom.mem_ker,
          BEI.quotConstCoeffReduced, Ideal.Quotient.lift_mk] at hx
        have hmem : f ∈ Ideal.span (Set.range
            (X : BinomialEdgeVars (Fin (pairedCount G (U : Set _))) →
              MvPolynomial (BinomialEdgeVars (Fin (pairedCount G (U : Set _)))) K)) := by
          rw [show Set.range X = X '' Set.univ from Set.image_univ.symm,
              MvPolynomial.mem_ideal_span_X_image]
          intro mono hm
          have hne : mono ≠ 0 := by
            intro hzero; subst hzero
            simp only [MvPolynomial.mem_support_iff] at hm; exact hm hx
          obtain ⟨idx, hidx⟩ := Finsupp.ne_iff.mp hne
          exact ⟨idx, Set.mem_univ _, hidx⟩
        have hmap :
            Ideal.map (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
              (Ideal.span (Set.range X)) ≤
            𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
              (A := A) (B := Lnew)).toRingHom := by
          rw [Ideal.map_span]
          apply Ideal.span_le.mpr
          rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
          exact h_gen v
        exact hmap (Ideal.mem_map_of_mem _ hmem)
      -- Comap is proper (𝔓 prime, so 1 ∉ 𝔓).
      have h_ne_top : 𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := A) (B := Lnew)).toRingHom ≠ ⊤ := by
        intro htop
        apply h𝔓.ne_top
        rw [Ideal.eq_top_iff_one]
        have h1 : (1 : A) ∈ 𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
            (A := A) (B := Lnew)).toRingHom := by rw [htop]; trivial
        rw [Ideal.mem_comap, map_one] at h1
        exact h1
      exact ((BEI.augIdealReduced_isMaximal G').eq_of_le h_ne_top h_le_comap).symm
    -- Step 7: apply C2 bridge.
    haveI h𝔓' : (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced G') 𝔓).IsPrime :=
      Algebra.tensorLeftLocalisedPrime_isPrime
        (B := Lnew) (BEI.augIdealReduced G') 𝔓 h_contract
    let e_C2 : Localization.AtPrime 𝔓 ≃+*
        Localization.AtPrime
          (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced (K := K) G') 𝔓) :=
      Algebra.tensorLeftLocalisationEquiv (BEI.augIdealReduced G') 𝔓 h_contract
    -- Step 8+9: L7 replacement gives CM-local at the tensor-pushed prime.
    haveI hCM_A : IsCohenMacaulayRing (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) :=
      isCohenMacaulayRing_at_augIdealReduced (K := K)
        (smallerHHGraph_herzogHibi hHH (U : Set _))
    haveI : IsNoetherianRing (BEI.reducedHHRing (K := K) G') :=
      Ideal.Quotient.isNoetherianRing _
    haveI : IsNoetherianRing (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) :=
      IsLocalization.isNoetherianRing (BEI.augIdealReduced (K := K) G').primeCompl
        (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) inferInstance
    haveI hCM_𝔓' : IsCohenMacaulayLocalRing
        (Localization.AtPrime
          (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced (K := K) G') 𝔓)) :=
      TensorPolynomialAway.isCohenMacaulayLocalRing_localization_tensor_away
        (A := Localization.AtPrime (BEI.augIdealReduced (K := K) G'))
        (rename (R := K)
          (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
          (τ := ↑(lambdaSet G (U : Set _)) ⊕
            ↑((U : Set (BinomialEdgeVars (Fin n)))))
          Sum.inr (hhUnitProductSub (K := K) U))
        (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced G') 𝔓)
    -- Step 10a: transport back through e_C2.
    have hCM_𝔓 : IsCohenMacaulayLocalRing (Localization.AtPrime 𝔓) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hCM_𝔓' e_C2.symm
    -- Step 10b: transport to Localization.AtPrime p_Lsu via e_U.
    have hH : p_Lsu.primeCompl.map e_U.toRingEquiv.toMonoidHom = 𝔓.primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        intro hmem
        apply hx
        rw [𝔓_def, Ideal.mem_comap] at hmem
        change e_U.symm.toRingHom (e_U.toRingEquiv x) ∈ p_Lsu at hmem
        rw [show e_U.toRingEquiv x = e_U x from rfl] at hmem
        change e_U.symm (e_U x) ∈ p_Lsu at hmem
        rwa [AlgEquiv.symm_apply_apply] at hmem
      · intro hy
        refine ⟨e_U.symm y, ?_, ?_⟩
        · intro hymem
          apply hy
          rw [𝔓_def, Ideal.mem_comap]
          exact hymem
        · change e_U.toRingEquiv (e_U.symm y) = y
          exact AlgEquiv.apply_symm_apply e_U y
    let e_locP : Localization.AtPrime p_Lsu ≃+* Localization.AtPrime 𝔓 :=
      IsLocalization.ringEquivOfRingEquiv
        (S := Localization.AtPrime p_Lsu)
        (Q := Localization.AtPrime 𝔓)
        (M := p_Lsu.primeCompl)
        (T := 𝔓.primeCompl)
        e_U.toRingEquiv hH
    have hCM_pLsu : IsCohenMacaulayLocalRing (Localization.AtPrime p_Lsu) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hCM_𝔓 e_locP.symm
    -- Step 10c: loc-of-loc to Localization.AtPrime p.
    set q₁ := Ideal.comap (algebraMap R Lsu) p_Lsu with q₁_def
    have hq₁p : q₁ = p := hcomap_p
    haveI : q₁.IsPrime := hq₁p ▸ ‹p.IsPrime›
    have hCM_q₁ : IsCohenMacaulayLocalRing (Localization.AtPrime q₁) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hCM_pLsu
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Submonoid.powers sU) p_Lsu).symm.toRingEquiv
    have hpc : q₁.primeCompl = p.primeCompl := by
      ext x; exact not_congr (by rw [hq₁p])
    exact cast (show IsCohenMacaulayLocalRing (Localization.AtPrime q₁) =
      IsCohenMacaulayLocalRing (Localization.AtPrime p) by
        change IsCohenMacaulayLocalRing (Localization q₁.primeCompl) =
          IsCohenMacaulayLocalRing (Localization p.primeCompl)
        rw [hpc]) hCM_q₁


/-- Under HH conditions, `S ⧸ monomialInitialIdeal G` is globally Cohen–Macaulay.

This is the `J_G`-side monomial CM statement: for a graph `G` satisfying the
Herzog–Hibi conditions (in particular, any closed graph satisfying the
Proposition 1.6 condition — see `prop_1_6_herzogHibi`), the quotient of the
polynomial ring by the monomial initial ideal of `J_G` is Cohen–Macaulay.

Proof: transport the HH bipartite CM theorem
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` along the
`y`-predecessor ring isomorphism built from `rename_yPredVar_monomialInitialIdeal`.

Restricted to `K : Type` because the underlying HH theorem is universe-monomorphic. -/
theorem monomialInitialIdeal_isCohenMacaulay
    {K : Type} [Field K]
    {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G) := by
  have hn0 : 0 < n := by omega
  set φ := (MvPolynomial.renameEquiv K (yPredEquiv n hn0)).toRingEquiv
  have hmap : bipartiteEdgeMonomialIdeal (K := K) G =
      Ideal.map φ (monomialInitialIdeal (K := K) G) := by
    have hfun : ⇑φ = ⇑(rename (yPredVar n hn0) : MvPolynomial _ K →ₐ[K] MvPolynomial _ K) := by
      funext p; exact (MvPolynomial.renameEquiv_apply K (yPredEquiv n hn0) p).symm
    change _ = Ideal.map φ.toRingHom _
    conv_rhs => rw [show φ.toRingHom = (rename (yPredVar n hn0) :
        MvPolynomial _ K →ₐ[K] MvPolynomial _ K).toRingHom from RingHom.ext (fun x => by
      change φ x = rename (yPredVar n hn0) x; exact congr_fun hfun x)]
    exact (rename_yPredVar_monomialInitialIdeal (K := K) hn0 G).symm
  have e : MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G ≃+*
      MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.quotientEquiv _ _ φ hmap
  haveI : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G) :=
    isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal hn hHH
  exact isCohenMacaulayRing_of_ringEquiv e.symm

end

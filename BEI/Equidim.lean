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


/-! ### Session A′: the reduced HH ring at its augmentation is CM local

The goal is

    IsCohenMacaulayLocalRing (Localization.AtPrime (augIdealReduced G))

for any HH graph `G` on `Fin (r + 1)`.

**Base case `r = 0`**: the reduced HH ring on no variables is `K` (a field),
`augIdealReduced = ⊥`, and `Localization.AtPrime ⊥ (field)` is CM local.

**Inductive case `r ≥ 1`**: bridge from L5 CM output to
`Localization.AtPrime (augIdealReduced G)` via the chain
  (L5) = (Rp ⧸ x_last) ⧸ y_last
       ≅ Rp ⧸ ⟨x_last, y_last⟩
       ≅ (R_G ⧸ ⟨x_last, y_last⟩)_{augIdeal / ...}
       ≅ Localization.AtPrime (augIdealReduced G)
where each step uses either `DoubleQuot`, quotient/localization commutation,
or the polynomial-level "kill last pair" ring equivalence.
-/

/-! #### Base case `r = 0`: reduced HH ring is the field `K` -/

/-- For `r = 0`, the index type `BinomialEdgeVars (Fin 0)` is empty. -/
private instance isEmpty_binomialEdgeVars_fin_zero :
    IsEmpty (BinomialEdgeVars (Fin 0)) :=
  inferInstanceAs (IsEmpty (Fin 0 ⊕ Fin 0))

/-- When the index type is empty, the reduced HH ideal has no generators, so it equals `⊥`. -/
private theorem reducedHHIdeal_eq_bot_of_r_zero {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) :
    BEI.reducedHHIdeal (K := K) G' = ⊥ := by
  unfold BEI.reducedHHIdeal MvPolynomial.variablePairIdeal
  rw [Ideal.span_eq_bot]
  rintro x ⟨a, _, _, _⟩
  exact (IsEmpty.false a).elim

/-- The reduced HH ring is isomorphic to `K` when `r = 0`. -/
private noncomputable def reducedHHRing_equiv_K_of_r_zero {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) : BEI.reducedHHRing (K := K) G' ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (reducedHHIdeal_eq_bot_of_r_zero G')).trans <|
    (AlgEquiv.quotientBot K _).trans
      (MvPolynomial.isEmptyAlgEquiv K (BinomialEdgeVars (Fin 0)))

/-- `augIdealReduced G' = ⊥` when `r = 0`: in a field, every proper ideal is `⊥`. -/
private theorem augIdealReduced_eq_bot_of_r_zero {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) :
    BEI.augIdealReduced (K := K) G' = ⊥ := by
  -- reducedHHRing G' is a field (via iso to K), hence every proper ideal is ⊥.
  have hfield : IsField (BEI.reducedHHRing (K := K) G') :=
    (reducedHHRing_equiv_K_of_r_zero G').toRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  letI : Field (BEI.reducedHHRing (K := K) G') := hfield.toField
  have hmax : (BEI.augIdealReduced (K := K) G').IsMaximal := BEI.augIdealReduced_isMaximal G'
  have hne_top : BEI.augIdealReduced (K := K) G' ≠ ⊤ := hmax.ne_top
  rcases Ideal.eq_bot_or_top (BEI.augIdealReduced (K := K) G') with heq | heq
  · exact heq
  · exact absurd heq hne_top

/-- **Base case** (`r = 0`): the localization of the reduced HH ring at its
augmentation ideal is CM local. Proof: `reducedHHRing G'` is a field, the
augmentation ideal is `⊥`, and the localization has Krull dimension 0. -/
private theorem isCohenMacaulayLocalRing_at_augIdealReduced_base {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) := by
  -- reducedHHRing G' is a field.
  have hfield : IsField (BEI.reducedHHRing (K := K) G') :=
    (reducedHHRing_equiv_K_of_r_zero G').toRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  letI : Field (BEI.reducedHHRing (K := K) G') := hfield.toField
  -- Krull dim of localization = height of augIdealReduced = 0 (since augIdealReduced = ⊥).
  apply isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (BEI.augIdealReduced (K := K) G')
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G')),
    Ideal.height_eq_primeHeight]
  have h : (BEI.augIdealReduced (K := K) G').primeHeight = 0 :=
    Ideal.primeHeight_eq_zero_iff.mpr (by
      rw [augIdealReduced_eq_bot_of_r_zero, IsDomain.minimalPrimes_eq_singleton_bot,
        Set.mem_singleton_iff])
  rw [h]; rfl

/-! #### Inductive case `r ≥ 1`: "kill last pair" bridge to `reducedHHRing`

We build a 4-step bridge from L5's CM output
`QuotSMulTop mkyL RpQ` (= `(Rp ⧸ xL) ⧸ yL`) to
`Localization.AtPrime (augIdealReduced G)`:

1. `QuotSMulTop mkyL RpQ ≃+* (Rp ⧸ xL) ⧸ span{mkyL}` (existing bridge).
2. `(Rp ⧸ xL) ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}` (DoubleQuot).
3. `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime (augIdeal.map mk_J) (R_G ⧸ J)`
   where `J = span{mkI X(inl r), mkI X(inr r)}` (localisation-quotient commutation).
4. `R_G ⧸ J ≃ₐ[K] reducedHHRing G` (the "kill last pair" polynomial iso).

Then transport L5's CM conclusion via `isCohenMacaulayLocalRing_of_ringEquiv'`.
-/

variable {r : ℕ}

/-- Forward variable map for the "kill last pair" iso: `inl i ↦ mkI X(inl i.castSucc)`
if `i.val < r`, else `0`. Similarly for `inr`. The "last" variables (index `r`)
are sent to `0`. -/
private noncomputable def killLastPairForwardVar
    {G : SimpleGraph (Fin (r + 1))} :
    BinomialEdgeVars (Fin (r + 1)) → BEI.reducedHHRing (K := K) G
  | Sum.inl ⟨i, _⟩ =>
      if h : i < r then
        Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inl ⟨i, h⟩))
      else 0
  | Sum.inr ⟨i, _⟩ =>
      if h : i < r then
        Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inr ⟨i, h⟩))
      else 0

/-- The forward polynomial-level algebra hom
`MvPolynomial (BinomialEdgeVars (Fin (r+1))) K →ₐ[K] reducedHHRing G`. -/
private noncomputable def killLastPairForwardPoly
    (G : SimpleGraph (Fin (r + 1))) :
    MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K →ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  aeval (killLastPairForwardVar (K := K) (G := G))

/-- `bipartiteEdgeMonomialIdeal G` is contained in the kernel of `killLastPairForwardPoly`.
Every generator `X(inl i) * X(inr j)` with `j.val + 1 < r + 1` has `j.val < r`, so
`j : Fin r`; additionally `i ≤ j` forces `i.val ≤ j.val < r`, so `i : Fin r`.
Hence the product maps to a reducedHH generator. -/
private lemma killLastPairForwardPoly_kills_bipartite
    (G : SimpleGraph (Fin (r + 1))) :
    bipartiteEdgeMonomialIdeal (K := K) G ≤
      RingHom.ker (killLastPairForwardPoly (K := K) G).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨i, j, hj, hadj, hle, rfl⟩
  -- `j.val + 1 < r + 1` ⟹ `j.val < r` ⟹ `i.val ≤ j.val < r`.
  have hjr : j.val < r := by omega
  have hir : i.val < r := lt_of_le_of_lt (by exact_mod_cast hle) hjr
  -- The map sends `X(inl i) * X(inr j)` to the corresponding reducedHH generator.
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  change (killLastPairForwardPoly (K := K) G) (X (Sum.inl i) * X (Sum.inr j)) = 0
  rw [map_mul]
  change (killLastPairForwardPoly (K := K) G) (X (Sum.inl i)) *
      (killLastPairForwardPoly (K := K) G) (X (Sum.inr j)) = 0
  unfold killLastPairForwardPoly
  rw [aeval_X, aeval_X]
  -- Now rewrite the variable map on the two elements.
  have hvar_inl : killLastPairForwardVar (K := K) (G := G) (Sum.inl i) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G)
        (X (Sum.inl ⟨i.val, hir⟩)) := by
    rcases i with ⟨iv, _⟩
    simp [killLastPairForwardVar, hir]
  have hvar_inr : killLastPairForwardVar (K := K) (G := G) (Sum.inr j) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G)
        (X (Sum.inr ⟨j.val, hjr⟩)) := by
    rcases j with ⟨jv, _⟩
    simp [killLastPairForwardVar, hjr]
  rw [hvar_inl, hvar_inr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  -- Show the product is in reducedHHIdeal.
  have hle' : (⟨i.val, hir⟩ : Fin r) ≤ ⟨j.val, hjr⟩ := by
    change i.val ≤ j.val; exact_mod_cast hle
  have hjsucc : (⟨j.val, hjr⟩ : Fin r).val + 1 < r + 1 := by simp; omega
  -- The adjacency condition.
  have hadj' : G.Adj (⟨i.val, hir⟩ : Fin r).castSucc
      ⟨(⟨j.val, hjr⟩ : Fin r).val + 1, hjsucc⟩ := by
    have heq1 : (⟨i.val, hir⟩ : Fin r).castSucc = i := Fin.ext rfl
    have heq2 : (⟨(⟨j.val, hjr⟩ : Fin r).val + 1, hjsucc⟩ : Fin (r + 1)) =
        ⟨j.val + 1, by omega⟩ := rfl
    rw [heq1, heq2]; exact hadj
  exact BEI.X_inl_mul_X_inr_mem_reducedHHIdeal hle' hjsucc hadj'

/-- The forward algebra hom `R_G →ₐ[K] reducedHHRing G`, obtained by descending
`killLastPairForwardPoly` through `bipartiteEdgeMonomialIdeal G`. -/
private noncomputable def killLastPairForwardRG
    (G : SimpleGraph (Fin (r + 1))) :
    (MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) →ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  Ideal.Quotient.liftₐ _ (killLastPairForwardPoly (K := K) G)
    (fun a ha => by
      have := killLastPairForwardPoly_kills_bipartite (K := K) G ha
      simpa [RingHom.mem_ker] using this)

/-- The "kill last pair" ideal in `R_G`: the span of the images of `X(inl r), X(inr r)`. -/
private noncomputable def killLastPairIdeal (G : SimpleGraph (Fin (r + 1))) :
    Ideal (MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
  Ideal.span
    { Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨r, lt_add_one r⟩)),
      Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨r, lt_add_one r⟩)) }

/-- `killLastPairForwardRG` kills `killLastPairIdeal G` — both last variables map to `0`. -/
private lemma killLastPairForwardRG_kills_lastPair
    (G : SimpleGraph (Fin (r + 1))) :
    killLastPairIdeal (K := K) G ≤
      RingHom.ker (killLastPairForwardRG (K := K) G).toRingHom := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  rcases hx with rfl | rfl
  · change killLastPairForwardRG (K := K) G
      (Ideal.Quotient.mk _ (X (Sum.inl ⟨r, lt_add_one r⟩))) = 0
    unfold killLastPairForwardRG
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    change killLastPairForwardPoly (K := K) G (X (Sum.inl ⟨r, lt_add_one r⟩)) = 0
    unfold killLastPairForwardPoly
    rw [aeval_X]
    simp [killLastPairForwardVar]
  · change killLastPairForwardRG (K := K) G
      (Ideal.Quotient.mk _ (X (Sum.inr ⟨r, lt_add_one r⟩))) = 0
    unfold killLastPairForwardRG
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    change killLastPairForwardPoly (K := K) G (X (Sum.inr ⟨r, lt_add_one r⟩)) = 0
    unfold killLastPairForwardPoly
    rw [aeval_X]
    simp [killLastPairForwardVar]

/-- The forward algebra hom `(R_G ⧸ J) →ₐ[K] reducedHHRing G` where `J = killLastPairIdeal G`. -/
private noncomputable def killLastPairForward
    (G : SimpleGraph (Fin (r + 1))) :
    ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸
        killLastPairIdeal (K := K) G) →ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  Ideal.Quotient.liftₐ _ (killLastPairForwardRG (K := K) G)
    (fun a ha => by
      have := killLastPairForwardRG_kills_lastPair (K := K) G ha
      simpa [RingHom.mem_ker] using this)

/-! ##### Backward direction: `reducedHHRing G →ₐ[K] R_G ⧸ killLastPairIdeal G` -/

/-- Backward variable map: `inl i ↦ mk_quot(mkI X(inl i.castSucc))`. -/
private noncomputable def killLastPairBackwardVar
    (G : SimpleGraph (Fin (r + 1))) :
    BinomialEdgeVars (Fin r) →
      ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G) ⧸
          killLastPairIdeal (K := K) G)
  | Sum.inl i =>
      Ideal.Quotient.mk _
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl i.castSucc)))
  | Sum.inr i =>
      Ideal.Quotient.mk _
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr i.castSucc)))

/-- The backward polynomial-level algebra hom
`MvPolynomial (BinomialEdgeVars (Fin r)) K →ₐ[K] (R_G ⧸ killLastPairIdeal G)`. -/
private noncomputable def killLastPairBackwardPoly
    (G : SimpleGraph (Fin (r + 1))) :
    MvPolynomial (BinomialEdgeVars (Fin r)) K →ₐ[K]
      ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G) ⧸
          killLastPairIdeal (K := K) G) :=
  aeval (killLastPairBackwardVar (K := K) G)

/-- `reducedHHIdeal G` is contained in the kernel of `killLastPairBackwardPoly`.
Each reducedHH generator `X(inl a) * X(inr b)` (with `a ≤ b < r` and edge
`{a, b+1}` in `G`) maps under `castSucc` embedding to a bipartite-edge generator
in `R_G`, which is zero in `R_G` (hence zero in the further quotient). -/
private lemma killLastPairBackwardPoly_kills_reducedHHIdeal
    (G : SimpleGraph (Fin (r + 1))) :
    BEI.reducedHHIdeal (K := K) G ≤
      RingHom.ker (killLastPairBackwardPoly (K := K) G).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨a, b, ⟨a', b', hb', hadj, hle, heq⟩, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.eq_iff_fst_eq_snd_eq.mp heq
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  change (killLastPairBackwardPoly (K := K) G) (X (Sum.inl a') * X (Sum.inr b')) = 0
  rw [map_mul]
  change (killLastPairBackwardPoly (K := K) G) (X (Sum.inl a')) *
      (killLastPairBackwardPoly (K := K) G) (X (Sum.inr b')) = 0
  unfold killLastPairBackwardPoly
  rw [aeval_X, aeval_X]
  show (killLastPairBackwardVar (K := K) G (Sum.inl a')) *
      (killLastPairBackwardVar (K := K) G (Sum.inr b')) = 0
  unfold killLastPairBackwardVar
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  -- The product lies in `killLastPairIdeal G`, since it is already 0 in `R_G`:
  -- `X(inl a'.castSucc) * X(inr b'.castSucc) ∈ bipartiteEdgeMonomialIdeal G`.
  have hj : (b'.castSucc : Fin (r + 1)).val + 1 < r + 1 := by
    have : (b'.castSucc : Fin (r + 1)).val = b'.val := rfl
    rw [this]; omega
  have hadj' : G.Adj (a'.castSucc : Fin (r + 1))
      ⟨(b'.castSucc : Fin (r + 1)).val + 1, hj⟩ := by
    have heq : (⟨(b'.castSucc : Fin (r + 1)).val + 1, hj⟩ : Fin (r + 1)) =
        ⟨b'.val + 1, hb'⟩ := rfl
    rw [heq]; exact hadj
  have hle' : (a'.castSucc : Fin (r + 1)) ≤ b'.castSucc := by
    change a'.val ≤ b'.val; exact_mod_cast hle
  have hmem_R : (X (Sum.inl a'.castSucc) * X (Sum.inr b'.castSucc) :
      MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K) ∈
      bipartiteEdgeMonomialIdeal (K := K) G := by
    refine Ideal.subset_span ?_
    exact ⟨a'.castSucc, b'.castSucc, hj, hadj', hle', rfl⟩
  have : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inl a'.castSucc) * X (Sum.inr b'.castSucc)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem_R
  rw [this]
  exact (killLastPairIdeal (K := K) G).zero_mem

/-- The backward algebra hom `reducedHHRing G →ₐ[K] (R_G ⧸ killLastPairIdeal G)`. -/
private noncomputable def killLastPairBackward
    (G : SimpleGraph (Fin (r + 1))) :
    BEI.reducedHHRing (K := K) G →ₐ[K]
      ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G) ⧸
          killLastPairIdeal (K := K) G) :=
  Ideal.Quotient.liftₐ _ (killLastPairBackwardPoly (K := K) G)
    (fun a ha => by
      have := killLastPairBackwardPoly_kills_reducedHHIdeal (K := K) G ha
      simpa [RingHom.mem_ker] using this)

/-! ##### Assembly: `killLastPairEquiv` -/

/-- Application lemma: `killLastPairForward` applied to the double-quotient of a polynomial
equals `killLastPairForwardPoly` applied to the polynomial. -/
private lemma killLastPairForward_apply_mk_mk
    (G : SimpleGraph (Fin (r + 1)))
    (p : MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K) :
    killLastPairForward (K := K) G
      (Ideal.Quotient.mk (killLastPairIdeal (K := K) G)
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) p)) =
    killLastPairForwardPoly (K := K) G p := rfl

/-- Application lemma: `killLastPairBackward` applied to the quotient of a polynomial
equals `killLastPairBackwardPoly` applied to the polynomial. -/
private lemma killLastPairBackward_apply_mk
    (G : SimpleGraph (Fin (r + 1)))
    (p : MvPolynomial (BinomialEdgeVars (Fin r)) K) :
    killLastPairBackward (K := K) G
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) p) =
    killLastPairBackwardPoly (K := K) G p := rfl

/-- Variable-level value of the forward map on `inl i.castSucc` (non-last). -/
private lemma killLastPairForwardVar_inl_castSucc
    (G : SimpleGraph (Fin (r + 1))) (i : Fin r) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inl i.castSucc) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inl i)) := by
  rcases i with ⟨iv, hiv⟩
  simp [killLastPairForwardVar, Fin.castSucc, hiv]

/-- Variable-level value of the forward map on `inr i.castSucc` (non-last). -/
private lemma killLastPairForwardVar_inr_castSucc
    (G : SimpleGraph (Fin (r + 1))) (i : Fin r) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inr i.castSucc) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inr i)) := by
  rcases i with ⟨iv, hiv⟩
  simp [killLastPairForwardVar, Fin.castSucc, hiv]

/-- Variable-level value of the forward map on `inl ⟨r, _⟩` (last). -/
private lemma killLastPairForwardVar_inl_last
    (G : SimpleGraph (Fin (r + 1))) (h : r < r + 1) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inl ⟨r, h⟩) = 0 := by
  simp [killLastPairForwardVar]

/-- Variable-level value of the forward map on `inr ⟨r, _⟩` (last). -/
private lemma killLastPairForwardVar_inr_last
    (G : SimpleGraph (Fin (r + 1))) (h : r < r + 1) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inr ⟨r, h⟩) = 0 := by
  simp [killLastPairForwardVar]

/-- Both compositions `forward ∘ backward` and `backward ∘ forward` are the identity,
so `killLastPairForward` and `killLastPairBackward` assemble into a ring equivalence. -/
private noncomputable def killLastPairEquiv
    (G : SimpleGraph (Fin (r + 1))) :
    ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸
        killLastPairIdeal (K := K) G) ≃ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  AlgEquiv.ofAlgHom (killLastPairForward (K := K) G)
    (killLastPairBackward (K := K) G)
    (by
      -- forward ∘ backward = id on `reducedHHRing G`. Use quotient + MvPolynomial
      -- algHom_ext: it suffices to check equality on variables (images of `X v`).
      refine Ideal.Quotient.algHom_ext _ ?_
      refine MvPolynomial.algHom_ext (fun v => ?_)
      -- Goal: ((F ∘ B) ∘ mk) (X v) = (id ∘ mk) (X v).
      change killLastPairForward (K := K) G
          (killLastPairBackward (K := K) G
            (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X v))) =
        Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X v)
      rw [killLastPairBackward_apply_mk]
      show killLastPairForward (K := K) G
          (killLastPairBackwardPoly (K := K) G (X v)) = _
      change killLastPairForward (K := K) G
          (aeval (killLastPairBackwardVar (K := K) G) (X v)) = _
      rw [aeval_X]
      cases v with
      | inl i =>
        change killLastPairForward (K := K) G
            (Ideal.Quotient.mk _
              (Ideal.Quotient.mk _ (X (Sum.inl i.castSucc)))) = _
        rw [killLastPairForward_apply_mk_mk]
        show killLastPairForwardPoly (K := K) G (X (Sum.inl i.castSucc)) = _
        change aeval (killLastPairForwardVar (K := K) (G := G)) (X (Sum.inl i.castSucc)) = _
        rw [aeval_X, killLastPairForwardVar_inl_castSucc]
      | inr i =>
        change killLastPairForward (K := K) G
            (Ideal.Quotient.mk _
              (Ideal.Quotient.mk _ (X (Sum.inr i.castSucc)))) = _
        rw [killLastPairForward_apply_mk_mk]
        show killLastPairForwardPoly (K := K) G (X (Sum.inr i.castSucc)) = _
        change aeval (killLastPairForwardVar (K := K) (G := G)) (X (Sum.inr i.castSucc)) = _
        rw [aeval_X, killLastPairForwardVar_inr_castSucc])
    (by
      -- backward ∘ forward = id on `(R_G ⧸ killLastPairIdeal)`.
      refine Ideal.Quotient.algHom_ext _ ?_
      refine Ideal.Quotient.algHom_ext _ ?_
      refine MvPolynomial.algHom_ext (fun v => ?_)
      -- Goal: ((B ∘ F) ∘ mk ∘ mk) (X v) = (id ∘ mk ∘ mk) (X v).
      change killLastPairBackward (K := K) G
          (killLastPairForward (K := K) G
            (Ideal.Quotient.mk _
              (Ideal.Quotient.mk _ (X v)))) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (X v))
      rw [killLastPairForward_apply_mk_mk]
      show killLastPairBackward (K := K) G
          (killLastPairForwardPoly (K := K) G (X v)) = _
      change killLastPairBackward (K := K) G
          (aeval (killLastPairForwardVar (K := K) (G := G)) (X v)) = _
      rw [aeval_X]
      cases v with
      | inl i =>
        rcases i with ⟨iv, hiv⟩
        by_cases h : iv < r
        · -- Non-last: iv < r. Write i = ⟨iv, hiv⟩ as (⟨iv, h⟩ : Fin r).castSucc.
          have heq : (⟨iv, hiv⟩ : Fin (r + 1)) = (⟨iv, h⟩ : Fin r).castSucc := rfl
          rw [heq, killLastPairForwardVar_inl_castSucc]
          rw [killLastPairBackward_apply_mk]
          change killLastPairBackwardPoly (K := K) G (X (Sum.inl ⟨iv, h⟩)) = _
          change aeval (killLastPairBackwardVar (K := K) G) (X (Sum.inl ⟨iv, h⟩)) = _
          rw [aeval_X]
          show killLastPairBackwardVar (K := K) G (Sum.inl ⟨iv, h⟩) = _
          rfl
        · -- Last: iv = r. Forward sends to 0; we need `0 = mk(mk(X(inl ⟨r, hiv⟩)))`.
          have hiv_eq : iv = r := by omega
          subst hiv_eq
          rw [killLastPairForwardVar_inl_last]
          rw [map_zero]
          -- Show `0 = mk(mk(X(inl ⟨r, hiv⟩)))` in `(R_G ⧸ killLastPairIdeal)`.
          symm
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (by left; rfl)
      | inr i =>
        rcases i with ⟨iv, hiv⟩
        by_cases h : iv < r
        · have heq : (⟨iv, hiv⟩ : Fin (r + 1)) = (⟨iv, h⟩ : Fin r).castSucc := rfl
          rw [heq, killLastPairForwardVar_inr_castSucc]
          rw [killLastPairBackward_apply_mk]
          change killLastPairBackwardPoly (K := K) G (X (Sum.inr ⟨iv, h⟩)) = _
          change aeval (killLastPairBackwardVar (K := K) G) (X (Sum.inr ⟨iv, h⟩)) = _
          rw [aeval_X]
          rfl
        · have hiv_eq : iv = r := by omega
          subst hiv_eq
          rw [killLastPairForwardVar_inr_last]
          rw [map_zero]
          symm
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (by right; rfl))

/-! ##### Localisation-quotient commutation (Step 3 of the bridge)

We build a ring equivalence
    `Rp ⧸ span{xL, yL}  ≃+*  Localization.AtPrime (augIdealQuot G) (R_G ⧸ killLastPairIdeal G)`
where `Rp = Localization.AtPrime (augIdeal G)`, xL, yL are the images of the last-pair
variables in Rp, and `augIdealQuot G = augIdeal G`-map to the quotient.

The bridge uses:
- forward: `Rp/J_Rp → Localization.AtPrime augIdealQuot`, defined by factoring
  `Localization.localRingHom` through the quotient.
- backward: `Localization.AtPrime augIdealQuot → Rp/J_Rp`, defined via the universal
  property (`IsLocalization.lift`).
-/

/-! ##### Image of `augIdeal G` under `killLastPairEquiv` is `augIdealReduced G` -/

/-- The image of `augIdeal G` under the double-quotient projection, as an ideal
in `R_G ⧸ killLastPairIdeal G`. -/
private noncomputable def augIdealQuot (G : SimpleGraph (Fin (r + 1))) :
    Ideal ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸
        killLastPairIdeal (K := K) G) :=
  (augIdeal (K := K) G).map (Ideal.Quotient.mk (killLastPairIdeal (K := K) G))

/-- `killLastPairIdeal G ⊆ augIdeal G`: both last-pair generators lie in the augmentation
ideal (they are variables with zero constant coefficient). -/
private lemma killLastPairIdeal_le_augIdeal (G : SimpleGraph (Fin (r + 1))) :
    killLastPairIdeal (K := K) G ≤ augIdeal (K := K) G := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact mkI_X_mem_augIdeal G _
  · exact mkI_X_mem_augIdeal G _

/-- `augIdealQuot G` is a maximal ideal (hence prime). Proof: use that
`(R_G ⧸ killLastPairIdeal) ⧸ augIdealQuot ≃ R_G ⧸ augIdeal = K`, a field. -/
private instance augIdealQuot_isMaximal (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).IsMaximal := by
  haveI : (augIdeal (K := K) G).IsMaximal := augIdeal_isMaximal G
  -- Use DoubleQuot.quotQuotEquivQuotOfLE to get the isomorphism.
  have hiso : ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) ⧸ killLastPairIdeal (K := K) G) ⧸
      augIdealQuot (K := K) G ≃+*
      (MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸ augIdeal (K := K) G :=
    DoubleQuot.quotQuotEquivQuotOfLE (killLastPairIdeal_le_augIdeal G)
  -- The target is a field (quotient by maximal), hence the source's quotient is too.
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  have hRHS_field : IsField ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸ augIdeal (K := K) G) :=
    Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.mp inferInstance
  exact MulEquiv.isField hRHS_field hiso.toMulEquiv

private instance augIdealQuot_isPrime (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).IsPrime := (augIdealQuot_isMaximal G).isPrime

/-- `augIdealQuot G` maps onto `augIdealReduced G` under `killLastPairEquiv`. -/
private lemma killLastPairEquiv_map_augIdealQuot
    (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).map
      (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom =
    BEI.augIdealReduced (K := K) G := by
  -- Show both inclusions.
  apply le_antisymm
  · -- `⊆`: every generator of augIdealQuot maps into augIdealReduced.
    -- augIdealQuot = map of augIdeal = map of (map of RingHom.ker constantCoeff).
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    -- x ∈ augIdealQuot G = (augIdeal G).map mk_J.
    -- First push into augIdeal, then factor through quotient.
    rw [augIdealQuot, Ideal.mem_comap] at *
    -- x ∈ (augIdeal G).map mk_J, i.e., there exist quotient representatives.
    -- Use constantCoeff factoring. Strategy: the forward algebra hom sends augIdeal
    -- (at the polynomial level) to augIdealReduced, because constant coefficients
    -- commute with the aeval.
    -- Prove augIdealQuot ≤ comap (mk_J ∘ mk_bipartite) of (polynomial augIdeal-like thing).
    -- Simpler: it suffices to show for x = mk_J (y) with y ∈ augIdeal G,
    -- that (killLastPairEquiv G) (mk_J y) ∈ augIdealReduced G.
    -- Use Ideal.map_mono-style induction via Submodule.span_induction.
    induction hx using Submodule.span_induction with
    | mem z hz =>
      -- z = mk_J y with y ∈ augIdeal G.
      obtain ⟨y, hy, rfl⟩ := hz
      -- killLastPairEquiv (mk_J y) = killLastPairForward (mk_J y) = killLastPairForwardRG y.
      change (killLastPairEquiv (K := K) G) (Ideal.Quotient.mk _ y) ∈
        BEI.augIdealReduced (K := K) G
      -- y ∈ augIdeal G = ker quotConstCoeff, in R_G.
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      -- Now use: killLastPairEquiv (mk_J (mk_I p)) = killLastPairForwardPoly p.
      change killLastPairForwardPoly (K := K) G p ∈ BEI.augIdealReduced (K := K) G
      -- The polynomial forward map applied to p: write p via induction.
      -- augIdealReduced = ker quotConstCoeffReduced, so it suffices to show
      -- quotConstCoeffReduced (killLastPairForwardPoly p) = constantCoeff p
      -- provided that the constant coefficient of p is 0 (since mk_I p ∈ augIdeal).
      -- Extract the constant coefficient condition.
      have hcc : constantCoeff p = 0 := by
        -- augIdeal G = RingHom.ker quotConstCoeff; check.
        change quotConstCoeff G
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) p) = 0 at hy
        simpa [quotConstCoeff] using hy
      -- Now show killLastPairForwardPoly p has zero reduced constant coefficient.
      have key : BEI.quotConstCoeffReduced G (killLastPairForwardPoly (K := K) G p) = 0 := by
        -- Both sides are ring homs applied to p; check they agree (and that composition
        -- equals constantCoeff on MvPolynomial side).
        -- Approach: show `(quotConstCoeffReduced G) ∘ killLastPairForwardPoly = constantCoeff`.
        suffices h : ((BEI.quotConstCoeffReduced G).comp
            (killLastPairForwardPoly (K := K) G).toRingHom) p = constantCoeff p by
          have : BEI.quotConstCoeffReduced G (killLastPairForwardPoly (K := K) G p) =
              constantCoeff p := h
          rw [this, hcc]
        -- This reduces to showing the compositions agree on generators.
        -- aeval_unique pattern: both are ring homs MvPol → K agreeing on all X v and C c.
        refine congrFun (congrArg DFunLike.coe
          (MvPolynomial.ringHom_ext (f := ((BEI.quotConstCoeffReduced G).comp
            (killLastPairForwardPoly (K := K) G).toRingHom))
            (g := (constantCoeff :
              MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K →+* K))
            ?_ ?_)) p
        · intro c
          -- Left: C c → killLastPairForwardPoly (C c) = C c in reducedHHRing → K.
          -- Both give c.
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
          rw [show killLastPairForwardPoly (K := K) G (C c) =
              algebraMap K _ c from (killLastPairForwardPoly (K := K) G).commutes c]
          change BEI.quotConstCoeffReduced G
              (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (C c)) = _
          unfold BEI.quotConstCoeffReduced
          rw [Ideal.Quotient.lift_mk]
          simp
        · intro v
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
          change BEI.quotConstCoeffReduced G
              (killLastPairForwardPoly (K := K) G (X v)) = constantCoeff (X v)
          change BEI.quotConstCoeffReduced G
              (aeval (killLastPairForwardVar (K := K) (G := G)) (X v)) = _
          rw [aeval_X, constantCoeff_X]
          -- Now compute: quotConstCoeffReduced (killLastPairForwardVar v) = 0.
          cases v with
          | inl i =>
            rcases i with ⟨iv, hiv⟩
            by_cases h : iv < r
            · simp only [killLastPairForwardVar, h, dif_pos]
              change BEI.quotConstCoeffReduced G
                (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X _)) = 0
              unfold BEI.quotConstCoeffReduced
              rw [Ideal.Quotient.lift_mk]
              simp
            · simp only [killLastPairForwardVar, h, dif_neg, not_false_eq_true]
              rfl
          | inr i =>
            rcases i with ⟨iv, hiv⟩
            by_cases h : iv < r
            · simp only [killLastPairForwardVar, h, dif_pos]
              change BEI.quotConstCoeffReduced G
                (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X _)) = 0
              unfold BEI.quotConstCoeffReduced
              rw [Ideal.Quotient.lift_mk]
              simp
            · simp only [killLastPairForwardVar, h, dif_neg, not_false_eq_true]
              rfl
      -- Conclude.
      change killLastPairForwardPoly (K := K) G p ∈
        RingHom.ker (BEI.quotConstCoeffReduced G)
      exact key
    | zero =>
      change (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom 0 ∈
        BEI.augIdealReduced (K := K) G
      rw [map_zero]; exact (BEI.augIdealReduced (K := K) G).zero_mem
    | add x y _ _ hxi hyi =>
      change (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom (x + y) ∈
        BEI.augIdealReduced (K := K) G
      rw [map_add]; exact (BEI.augIdealReduced (K := K) G).add_mem hxi hyi
    | smul a x _ hxi =>
      change (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom (a • x) ∈
        BEI.augIdealReduced (K := K) G
      rw [smul_eq_mul, map_mul]
      exact (BEI.augIdealReduced (K := K) G).mul_mem_left _ hxi
  · -- `⊇`: every generator of augIdealReduced comes from something in augIdealQuot.
    -- Simpler: since killLastPairEquiv is bijective, for any x ∈ augIdealReduced, let y :=
    -- (killLastPairEquiv G).symm x. Show y ∈ augIdealQuot G.
    intro x hx
    rw [Ideal.mem_map_iff_of_surjective
      (f := (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom)
      (hf := (killLastPairEquiv (K := K) G).surjective)]
    -- Take preimage under the iso.
    refine ⟨(killLastPairEquiv (K := K) G).symm x, ?_, by simp⟩
    -- Now show (killLastPairEquiv G).symm x ∈ augIdealQuot.
    -- It equals `killLastPairBackward (K := K) G x`. Use the backward version.
    -- Strategy: lift x ∈ augIdealReduced back through reducedHHRing G.
    -- Write x = mk_I q for some q : MvPol (BinomialEdgeVars (Fin r)) K with
    -- constantCoeff q = 0. Then backward sends this to mk_J (mk_I (aeval castSucc q)).
    -- Show constantCoeff of aeval castSucc q is 0 → the image lies in augIdealQuot.
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hcc : constantCoeff q = 0 := by
      simp only [BEI.augIdealReduced, RingHom.mem_ker] at hx
      unfold BEI.quotConstCoeffReduced at hx
      rw [Ideal.Quotient.lift_mk] at hx
      exact hx
    -- (killLastPairEquiv G).symm (mk_I q) = killLastPairBackward G (mk_I q) =
    -- killLastPairBackwardPoly q = mk_J (mk_I (aeval castSucc-eval q)).
    change (killLastPairEquiv (K := K) G).symm
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) q) ∈ augIdealQuot (K := K) G
    -- killLastPairEquiv.symm = killLastPairBackward (by AlgEquiv.ofAlgHom.symm).
    have hsymm : (killLastPairEquiv (K := K) G).symm
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) q) =
      killLastPairBackward (K := K) G
        (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) q) := rfl
    rw [hsymm, killLastPairBackward_apply_mk]
    change killLastPairBackwardPoly (K := K) G q ∈ augIdealQuot (K := K) G
    -- Now show this.
    -- augIdealQuot = map mk_J of augIdeal = map mk_J of (map mk_I of (ker constantCoeff)).
    -- So it suffices to show: there is some p : MvPol (Fin (r+1)) with constantCoeff p = 0
    -- and killLastPairBackwardPoly q = mk_J (mk_I p).
    -- Choose p = killLastPairInjPoly q — the polynomial obtained by applying castSucc to
    -- the variables of q. Then constantCoeff commutes with this renaming.
    -- Concretely: killLastPairBackwardPoly q is defined as aeval (killLastPairBackwardVar G) q.
    -- Its value on a basis element X v = mk_J (mk_I (X (inj v))).
    -- We can write killLastPairBackwardPoly q = mk_J (mk_I (rename inj q)) where
    -- inj = Sum.map castSucc castSucc. Then constantCoeff (rename inj q) = constantCoeff q = 0.
    -- Define the injection map.
    let inj : BinomialEdgeVars (Fin r) → BinomialEdgeVars (Fin (r + 1))
      | Sum.inl i => Sum.inl i.castSucc
      | Sum.inr i => Sum.inr i.castSucc
    -- Show killLastPairBackwardPoly q = mk_J (mk_I (rename inj q)).
    have hrename : killLastPairBackwardPoly (K := K) G q =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (rename inj q)) := by
      -- Both sides are ring homs from MvPol (BinomialEdgeVars (Fin r)) K.
      refine congrFun (congrArg DFunLike.coe
        (MvPolynomial.ringHom_ext
          (f := (killLastPairBackwardPoly (K := K) G).toRingHom)
          (g := ((Ideal.Quotient.mk _).comp
            ((Ideal.Quotient.mk _).comp (rename inj).toRingHom)))
          ?_ ?_)) q
      · intro c
        change killLastPairBackwardPoly (K := K) G (C c) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (rename inj (C c)))
        rw [rename_C]
        rw [show killLastPairBackwardPoly (K := K) G (C c) = algebraMap K _ c from
          (killLastPairBackwardPoly (K := K) G).commutes c]
        rfl
      · intro v
        change killLastPairBackwardPoly (K := K) G (X v) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (rename inj (X v)))
        rw [rename_X]
        change aeval (killLastPairBackwardVar (K := K) G) (X v) = _
        rw [aeval_X]
        cases v with
        | inl i => rfl
        | inr i => rfl
    rw [hrename]
    -- Show mk_J (mk_I (rename inj q)) ∈ augIdealQuot = map mk_J of augIdeal.
    unfold augIdealQuot
    refine Ideal.mem_map_of_mem _ ?_
    -- mk_I (rename inj q) ∈ augIdeal G.
    change quotConstCoeff G
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (rename inj q)) = 0
    simp [quotConstCoeff, constantCoeff_rename, hcc]

/-! ##### Step 3: Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot -/

/-- The map `augIdeal G = augIdealQuot.comap (Quotient.mk killLastPairIdeal)`.
This is the comap compatibility needed for `Localization.localRingHom`. -/
private lemma augIdeal_eq_comap_augIdealQuot
    (G : SimpleGraph (Fin (r + 1))) :
    augIdeal (K := K) G =
      (augIdealQuot (K := K) G).comap
        (Ideal.Quotient.mk (killLastPairIdeal (K := K) G)) := by
  unfold augIdealQuot
  -- augIdeal ⊆ augIdealQuot.comap mk_J follows from Ideal.le_comap_map.
  -- Reverse: augIdealQuot.comap mk_J ≤ augIdeal using killLastPairIdeal ⊆ augIdeal
  -- together with Ideal.comap_map_of_surjective.
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  -- Now goal: augIdeal = augIdeal ⊔ comap (Quotient.mk _) ⊥. comap(mk, ⊥) = killLastPairIdeal.
  have hcomap : Ideal.comap (Ideal.Quotient.mk (killLastPairIdeal (K := K) G)) ⊥
      = killLastPairIdeal (K := K) G := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hcomap]
  -- Need: augIdeal = augIdeal ⊔ killLastPairIdeal, i.e., killLastPairIdeal ≤ augIdeal.
  apply le_antisymm
  · exact le_sup_left
  · refine sup_le le_rfl ?_
    -- killLastPairIdeal = span {mk(X(inl r)), mk(X(inr r))} ⊆ augIdeal.
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mkI_X_mem_augIdeal G _
    · exact mkI_X_mem_augIdeal G _

/-- The `localRingHom` from `Rp = Localization.AtPrime (augIdeal G)` to
`Localization.AtPrime (augIdealQuot G)`, lifted from the quotient map
`R_G → R_G ⧸ killLastPairIdeal G`. -/
private noncomputable def quotLocalRingHom
    (G : SimpleGraph (Fin (r + 1))) :
    Localization.AtPrime (augIdeal (K := K) G) →+*
      Localization.AtPrime (augIdealQuot (K := K) G) :=
  Localization.localRingHom (augIdeal (K := K) G) (augIdealQuot (K := K) G)
    (Ideal.Quotient.mk (killLastPairIdeal (K := K) G))
    (augIdeal_eq_comap_augIdealQuot G)

/-- `quotLocalRingHom` applied to the image of a polynomial in `R_G` under `algebraMap R_G Rp`
factors as `algebraMap (R_G/J) (Localization.AtPrime augIdealQuot) ∘ (Quotient.mk J)`. -/
private lemma quotLocalRingHom_algebraMap
    (G : SimpleGraph (Fin (r + 1)))
    (x : MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :
    quotLocalRingHom (G := G) (algebraMap _ _ x) =
    algebraMap _ (Localization.AtPrime (augIdealQuot (K := K) G))
      (Ideal.Quotient.mk (killLastPairIdeal (K := K) G) x) := by
  simp [quotLocalRingHom, Localization.localRingHom_to_map]

/-- The `localRingHom` kills `span{xL, yL}`: both last-pair images map to 0
under `R_G → R_G ⧸ killLastPairIdeal → Localization.AtPrime augIdealQuot`. -/
private lemma quotLocalRingHom_kills_lastPair
    (G : SimpleGraph (Fin (r + 1))) :
    Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨r, lt_add_one r⟩))),
      algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
      Set (Localization.AtPrime (augIdeal (K := K) G))) ≤
      RingHom.ker (quotLocalRingHom (G := G)) := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  rcases hx with rfl | rfl
  · rw [quotLocalRingHom_algebraMap]
    have h0 : Ideal.Quotient.mk (killLastPairIdeal (K := K) G)
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨r, lt_add_one r⟩))) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by left; rfl)
    rw [h0, map_zero]
  · rw [quotLocalRingHom_algebraMap]
    have h0 : Ideal.Quotient.mk (killLastPairIdeal (K := K) G)
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨r, lt_add_one r⟩))) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by right; rfl)
    rw [h0, map_zero]

/-- The forward map `Rp ⧸ span{xL, yL} → Localization.AtPrime augIdealQuot`, obtained
by factoring `quotLocalRingHom` through the quotient. -/
private noncomputable def RpModLastPairToLoc
    (G : SimpleGraph (Fin (r + 1))) :
    ((Localization.AtPrime (augIdeal (K := K) G)) ⧸
        Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨r, lt_add_one r⟩))),
        algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inr ⟨r, lt_add_one r⟩)))})) →+*
      Localization.AtPrime (augIdealQuot (K := K) G) :=
  Ideal.Quotient.lift _ (quotLocalRingHom (G := G))
    (fun a ha => by
      have := quotLocalRingHom_kills_lastPair (G := G) ha
      simpa [RingHom.mem_ker] using this)

/-- Surjectivity of `RpModLastPairToLoc`: every element of the target is in the image. -/
private lemma RpModLastPairToLoc_surjective
    (G : SimpleGraph (Fin (r + 1))) :
    Function.Surjective (RpModLastPairToLoc (K := K) (G := G)) := by
  intro y
  -- y ∈ Localization.AtPrime augIdealQuot, write y = mk'(r_bar, s_bar) with
  -- r_bar ∈ R_G/J, s_bar ∈ augIdealQuot.primeCompl.
  -- Lift to R_G: r_bar = mk_J r, s_bar = mk_J s with s ∉ augIdeal G.
  obtain ⟨⟨r_bar, s_bar⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (augIdealQuot (K := K) G).primeCompl y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r_bar
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (s_bar : _ ⧸ killLastPairIdeal (K := K) G)
  -- Check s ∉ augIdeal G.
  have hs_ne : s ∉ augIdeal (K := K) G := by
    intro hmem
    -- s_bar.prop : s_bar ∉ augIdealQuot (i.e., s_bar ∈ primeCompl).
    -- But s ∈ augIdeal implies mk_J s ∈ augIdealQuot, and mk_J s = s_bar.
    have : (s_bar : _ ⧸ killLastPairIdeal (K := K) G) ∈ augIdealQuot (K := K) G := by
      rw [← hs]; exact Ideal.mem_map_of_mem _ hmem
    exact s_bar.prop this
  -- So s ∈ augIdeal.primeCompl; let s_Rp := mk'(1, s) as element ∈ Rp.
  -- Then s is a unit in Rp. Use mk'(r, s) ∈ Rp.
  let s' : (augIdeal (K := K) G).primeCompl := ⟨s, hs_ne⟩
  refine ⟨Ideal.Quotient.mk _ (IsLocalization.mk' _ r s'), ?_⟩
  -- Show this maps to the right element.
  change RpModLastPairToLoc (G := G)
    (Ideal.Quotient.mk _ (IsLocalization.mk' _ r s')) =
    IsLocalization.mk' _ _ s_bar
  unfold RpModLastPairToLoc
  rw [Ideal.Quotient.lift_mk]
  change quotLocalRingHom (G := G) (IsLocalization.mk' _ r s') = _
  rw [quotLocalRingHom, Localization.localRingHom_mk']
  -- Now the two sides should match up.
  congr 1
  exact Subtype.ext hs

/-- Injectivity of `RpModLastPairToLoc`. -/
private lemma RpModLastPairToLoc_injective
    (G : SimpleGraph (Fin (r + 1))) :
    Function.Injective (RpModLastPairToLoc (K := K) (G := G)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- x = mk_span y for some y : Rp.
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- y = mk'(p, s) with p : R_G, s ∈ augIdeal.primeCompl.
  obtain ⟨⟨p, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (augIdeal (K := K) G).primeCompl y
  -- hx says quotLocalRingHom (mk' p s) = 0, i.e., mk' (mk_J p) (mk_J s) = 0 in target.
  -- That means there's t ∈ augIdealQuot.primeCompl with t * (mk_J p) = 0, i.e.,
  -- t * (mk_J p) = 0 in R_G/J, i.e., t * p ∈ killLastPairIdeal.
  -- Then: in R_G, we have t * p ∈ killLastPairIdeal. Take preimage t0 of t with t0 ∉ augIdeal.
  -- Then mk'(p, s) is equivalent (in Rp) to something whose t0-multiple is in killLastPair
  -- map, which means it's in span{xL, yL}.
  have hx' : RpModLastPairToLoc (G := G)
    (Ideal.Quotient.mk _ (IsLocalization.mk' _ p s)) = 0 := hx
  unfold RpModLastPairToLoc at hx'
  rw [Ideal.Quotient.lift_mk] at hx'
  rw [quotLocalRingHom, Localization.localRingHom_mk'] at hx'
  -- Now hx' : mk' _ (mk_J p) (mk_J s) = 0. Use IsLocalization.mk'_eq_zero_iff.
  rw [IsLocalization.mk'_eq_zero_iff] at hx'
  obtain ⟨⟨t_bar, ht_bar⟩, ht⟩ := hx'
  simp only at ht
  -- t_bar ∈ augIdealQuot.primeCompl, t_bar * mk_J p = 0 in R_G/J.
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t_bar
  -- t ∉ augIdeal (since t_bar ∉ augIdealQuot via Ideal.mem_map comap compat).
  have ht_ne : t ∉ augIdeal (K := K) G := by
    intro hmem
    apply ht_bar
    exact Ideal.mem_map_of_mem _ hmem
  -- ht : mk_J t * mk_J p = 0, i.e., mk_J (t * p) = 0, i.e., t * p ∈ killLastPairIdeal.
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ht
  -- Now: mk_J (t*p) ∈ killLastPairIdeal means (t * p) ∈ killLastPairIdeal.
  -- Goal: mk_span (mk'(p, s)) = 0, i.e., mk'(p, s) ∈ span{xL, yL}.
  rw [Ideal.Quotient.eq_zero_iff_mem]
  -- mk'(p, s) = alg(p) * alg(s)⁻¹, and alg(p) * alg(t) ∈ span{xL, yL} (since t*p ∈ killLastPair).
  -- So: mk'(p, s) = alg(t)⁻¹ * alg(p) * alg(s)⁻¹ * alg(t) = alg(t*p) * (alg(s))⁻¹ * alg(t)⁻¹,
  -- and alg(t*p) ∈ span{xL, yL}.
  -- Since t ∉ augIdeal, alg(t) is a unit.
  have ht_unit : IsUnit (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G)) t) := by
    apply IsLocalization.map_units _ (⟨t, ht_ne⟩ : (augIdeal (K := K) G).primeCompl)
  -- Now: mk'(p, s) * alg(t) = mk'(p * t, s) = mk'(t * p, s) ∈ alg(killLastPairIdeal).span.
  have key : IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s *
      algebraMap _ _ t ∈
      Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨r, lt_add_one r⟩))),
      algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
      Set (Localization.AtPrime (augIdeal (K := K) G))) := by
    -- mk'(p, s) * alg(t) = alg(t) * mk'(p, s) = mk'(t*p, s) = alg(t*p) * alg(s)⁻¹.
    have h1 : IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s *
        algebraMap _ _ t =
        IsLocalization.mk' _ (t * p) s := by
      rw [mul_comm]
      exact IsLocalization.mul_mk'_eq_mk'_of_mul t p s
    rw [h1]
    -- Now show mk' (t*p) s ∈ span{xL, yL}.
    -- alg (t * p) ∈ span, and mk'(x, s) = alg(x) * alg(s)⁻¹. So mk'(t*p, s) is in span iff
    -- alg(t*p) is (since units preserve the span).
    have halg : algebraMap _ (Localization.AtPrime (augIdeal (K := K) G)) (t * p) ∈
        Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨r, lt_add_one r⟩))),
        algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
        Set (Localization.AtPrime (augIdeal (K := K) G))) := by
      -- (t * p) ∈ killLastPairIdeal. killLastPairIdeal = span{mk(X(inl r)), mk(X(inr r))}.
      -- So (t * p) is an R_G-linear combination of those. alg preserves this.
      have hmap : Ideal.map (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G)))
          (killLastPairIdeal (K := K) G) ≤
          Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
            (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
              (X (Sum.inl ⟨r, lt_add_one r⟩))),
          algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
            (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
              (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
          Set (Localization.AtPrime (augIdeal (K := K) G))) := by
        unfold killLastPairIdeal
        rw [Ideal.map_span]
        apply Ideal.span_le.mpr
        intro z hz
        simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Ideal.subset_span (by left; rfl)
        · exact Ideal.subset_span (by right; rfl)
      exact hmap (Ideal.mem_map_of_mem _ ht)
    -- Now mk'(t*p, s) = alg(t*p) * alg(s)⁻¹ (via mk'_eq_mul_mk'_one or similar).
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ halg
  -- Since alg(t) is a unit, mk'(p,s) ∈ span{xL,yL}.
  obtain ⟨u, hu⟩ := ht_unit
  change IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s ∈ _
  have hmk'_eq : IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s =
      (IsLocalization.mk' _ p s * algebraMap _ _ t) * ↑u⁻¹ := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hmk'_eq]
  exact Ideal.mul_mem_right _ _ key

/-- The ring equiv `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot`. -/
private noncomputable def RpModLastPairEquivLoc
    (G : SimpleGraph (Fin (r + 1))) :
    ((Localization.AtPrime (augIdeal (K := K) G)) ⧸
        Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨r, lt_add_one r⟩))),
        algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inr ⟨r, lt_add_one r⟩)))})) ≃+*
      Localization.AtPrime (augIdealQuot (K := K) G) :=
  RingEquiv.ofBijective (RpModLastPairToLoc (G := G))
    ⟨RpModLastPairToLoc_injective G, RpModLastPairToLoc_surjective G⟩

/-! ##### Step 4: `Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced` -/

/-- The image of `augIdealQuot.primeCompl` under `killLastPairEquiv` is
`augIdealReduced.primeCompl`. -/
private lemma killLastPairEquiv_map_primeCompl
    (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).primeCompl.map
        (killLastPairEquiv (K := K) G).toRingEquiv.toMonoidHom =
      (BEI.augIdealReduced (K := K) G).primeCompl := by
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro hxI
    apply hy
    have hmap := killLastPairEquiv_map_augIdealQuot (K := K) G
    -- hxI : killLastPairEquiv y ∈ augIdealReduced. Use hmap to convert.
    -- killLastPairEquiv y = (equiv).toMonoidHom y, which is the same as
    -- (equiv).toRingEquiv.toRingHom y.
    have hxI' : (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom y ∈
        (augIdealQuot (K := K) G).map
          (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom := by
      rw [hmap]; exact hxI
    rw [Ideal.mem_map_iff_of_surjective
        ((killLastPairEquiv (K := K) G).toRingEquiv.toRingHom)
        (killLastPairEquiv (K := K) G).surjective] at hxI'
    obtain ⟨z, hz, hyeq⟩ := hxI'
    have : z = y := (killLastPairEquiv (K := K) G).injective hyeq
    subst this
    exact hz
  · intro hx
    refine ⟨(killLastPairEquiv (K := K) G).symm x, ?_, ?_⟩
    · intro hyI
      apply hx
      have hmap := killLastPairEquiv_map_augIdealQuot (K := K) G
      -- From hyI : (equiv).symm x ∈ augIdealQuot, get (equiv) ((equiv).symm x) = x
      -- is in augIdealReduced.
      have hstep : (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom
          ((killLastPairEquiv (K := K) G).symm x) ∈ BEI.augIdealReduced (K := K) G := by
        rw [← hmap]; exact Ideal.mem_map_of_mem _ hyI
      -- (equiv).toRingEquiv.toRingHom v = (equiv) v by defn; then apply_symm_apply.
      have hcoe : (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom
          ((killLastPairEquiv (K := K) G).symm x) = x := by
        change (killLastPairEquiv (K := K) G) ((killLastPairEquiv (K := K) G).symm x) = x
        exact (killLastPairEquiv (K := K) G).apply_symm_apply x
      rwa [hcoe] at hstep
    · exact (killLastPairEquiv (K := K) G).apply_symm_apply x

/-- The ring equiv between localisations at corresponding primes, transported through
`killLastPairEquiv` via `IsLocalization.ringEquivOfRingEquiv`. -/
private noncomputable def locAugIdealQuotEquivLocAugIdealReduced
    (G : SimpleGraph (Fin (r + 1))) :
    Localization.AtPrime (augIdealQuot (K := K) G) ≃+*
      Localization.AtPrime (BEI.augIdealReduced (K := K) G) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := (augIdealQuot (K := K) G).primeCompl)
    (T := (BEI.augIdealReduced (K := K) G).primeCompl)
    (Localization.AtPrime (augIdealQuot (K := K) G))
    (Localization.AtPrime (BEI.augIdealReduced (K := K) G))
    (killLastPairEquiv (K := K) G).toRingEquiv
    (killLastPairEquiv_map_primeCompl G)

/-! ##### Assembly: `isCohenMacaulayLocalRing_at_augIdealReduced_step` -/

set_option maxHeartbeats 400000 in
-- heartbeats needed: assembly over iterated quotients + localizations.
/-- **Inductive case** (`r ≥ 1`): Bridge from L5's CM conclusion
`IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ)` to CM of
`Localization.AtPrime (augIdealReduced G)`. Uses the 4-step ring-iso chain:
1. `QuotSMulTop mkyL RpQ ≃+* RpQ ⧸ span{mkyL}` (existing bridge).
2. `RpQ ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}` (DoubleQuot).
3. `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot` (Step 3).
4. `Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced` (Step 4).
-/
private theorem isCohenMacaulayLocalRing_at_augIdealReduced_step
    {r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := by
  -- Introduce notations matching the L5 output.
  set Rp := Localization.AtPrime (augIdeal (K := K) G) with Rp_def
  -- L5's n = r + 1; hn : 2 ≤ r + 1 from hr : 1 ≤ r.
  have hn : 2 ≤ r + 1 := by omega
  -- The bipartite-edge ring element `X(inl ⟨r, _⟩)` is the last x.
  -- L5 uses `⟨(r + 1) - 1, _⟩ = ⟨r, _⟩`.
  have hrr1 : (r + 1) - 1 = r := by omega
  set xL : Rp := algebraMap _ Rp
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inl ⟨r, lt_add_one r⟩))) with xL_def
  set yL : Rp := algebraMap _ Rp
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inr ⟨r, lt_add_one r⟩))) with yL_def
  -- L5 notation uses ⟨(r+1)-1, _⟩, which is definitionally ⟨r, _⟩ after hrr1.
  -- We need to convert between the two forms to apply L5.
  have hbd : (r + 1) - 1 < r + 1 := by omega
  have hFin : (⟨r, lt_add_one r⟩ : Fin (r + 1)) = ⟨(r + 1) - 1, hbd⟩ :=
    Fin.ext hrr1.symm
  have hFin' : (⟨(r + 1) - 1, hbd⟩ : Fin (r + 1)) = ⟨r, lt_add_one r⟩ := Fin.ext hrr1
  have h_xL_eq : xL = algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨(r + 1) - 1, hbd⟩))) := by
    rw [hFin', xL_def]
  have h_yL_eq : yL = algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨(r + 1) - 1, hbd⟩))) := by
    rw [hFin', yL_def]
  -- Apply L5 to get CM of QuotSMulTop mkyL RpQ.
  have hL5 := isCohenMacaulayLocalRing_reducedHH_at_augIdeal (K' := K) hn hHH
  -- hL5's xL, yL, RpQ, mkyL definitions match ours modulo the (r+1)-1 = r issue.
  -- Transfer through the form match via `xL_eq, yL_eq`.
  set RpQ := Rp ⧸ Ideal.span {xL} with RpQ_def
  set mkyL : RpQ := Ideal.Quotient.mk (Ideal.span {xL}) yL with mkyL_def
  have hCM_L5 : IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ) := by
    -- L5 gives CM of QuotSMulTop (at (r+1)-1 form). Convert.
    convert hL5 using 3
  -- Hoisted membership / non-top facts used across Steps 1, 2, 2'.
  have hxLmem : xL ∈ IsLocalRing.maximalIdeal Rp :=
    X_inl_last_mem_maximalIdeal (K := K) (by omega) G
  have hyLmem : yL ∈ IsLocalRing.maximalIdeal Rp :=
    X_inr_last_mem_maximalIdeal (K := K) (by omega) G
  have hne_sup : Ideal.span {xL} ⊔ Ideal.span {yL} ≠ ⊤ := by
    intro htop
    have hle : Ideal.span {xL} ⊔ Ideal.span {yL} ≤ IsLocalRing.maximalIdeal Rp :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxLmem)
             ((Ideal.span_singleton_le_iff_mem _).mpr hyLmem)
    exact (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top (top_le_iff.mp (htop ▸ hle))
  haveI : IsLocalRing RpQ := by
    haveI : Nontrivial RpQ := Ideal.Quotient.nontrivial_iff.mpr
      (span_x_inl_last_ne_top (K := K) (by omega) G)
    exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmem_max : mkyL ∈ IsLocalRing.maximalIdeal RpQ := by
    haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {xL})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    apply (IsLocalRing.mem_maximalIdeal _).mp hyLmem
    exact (isUnit_map_iff (Ideal.Quotient.mk (Ideal.span {xL})) yL).mp hunit
  -- Step 1: QuotSMulTop mkyL RpQ ≃+* RpQ ⧸ span{mkyL}.
  have hstep1 : IsCohenMacaulayLocalRing (RpQ ⧸ Ideal.span {mkyL}) := by
    haveI := quotSMulTopLocalRing hmem_max
    haveI := hCM_L5
    haveI : Nontrivial (RpQ ⧸ Ideal.span {mkyL}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact (IsLocalRing.mem_maximalIdeal _).mp hmem_max)
    haveI : IsLocalRing (RpQ ⧸ Ideal.span {mkyL}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact isCohenMacaulayLocalRing_of_ringEquiv' hCM_L5
      (quotSMulTopRingEquivIdealQuotient mkyL)
  -- Step 2: RpQ ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}.
  have hstep2 : IsCohenMacaulayLocalRing
      (Rp ⧸ (Ideal.span {xL} ⊔ Ideal.span {yL})) := by
    -- span{mkyL} = span{yL}.map(Quotient.mk (span{xL})), so DoubleQuot.quotQuotEquivQuotSup
    -- gives (Rp ⧸ span{xL}) ⧸ span{mkyL} ≃+* Rp ⧸ (span{xL} ⊔ span{yL}).
    have hmap : (Ideal.span {yL}).map (Ideal.Quotient.mk (Ideal.span {xL})) =
        Ideal.span {mkyL} := by
      rw [Ideal.map_span, Set.image_singleton]
    haveI : Nontrivial (Rp ⧸ (Ideal.span {xL} ⊔ Ideal.span {yL})) :=
      Ideal.Quotient.nontrivial_iff.mpr hne_sup
    haveI : IsLocalRing (Rp ⧸ (Ideal.span {xL} ⊔ Ideal.span {yL})) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact isCohenMacaulayLocalRing_of_ringEquiv' hstep1
      ((Ideal.quotEquivOfEq hmap.symm).trans (DoubleQuot.quotQuotEquivQuotSup _ _))
  -- Step 2.5: span{xL} ⊔ span{yL} = span{xL, yL} (set equality).
  have hsup_eq : Ideal.span {xL} ⊔ Ideal.span {yL} =
      Ideal.span ({xL, yL} : Set Rp) := by
    rw [show ({xL, yL} : Set Rp) = {xL} ∪ {yL} from Set.insert_eq _ _,
      Ideal.span_union]
  have hstep2' : IsCohenMacaulayLocalRing
      (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) := by
    haveI : Nontrivial (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) :=
      Ideal.Quotient.nontrivial_iff.mpr (hsup_eq ▸ hne_sup)
    haveI : IsLocalRing (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact isCohenMacaulayLocalRing_of_ringEquiv' hstep2 (Ideal.quotEquivOfEq hsup_eq)
  -- Step 3: Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot.
  have hstep3 : IsCohenMacaulayLocalRing
      (Localization.AtPrime (augIdealQuot (K := K) G)) := by
    haveI : IsLocalRing (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalRing (Localization.AtPrime (augIdealQuot (K := K) G)) :=
      inferInstance
    exact isCohenMacaulayLocalRing_of_ringEquiv' hstep2' (RpModLastPairEquivLoc G)
  -- Step 4: Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced.
  haveI : IsLocalRing (Localization.AtPrime (augIdealQuot (K := K) G)) := inferInstance
  haveI : IsLocalRing (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := inferInstance
  exact isCohenMacaulayLocalRing_of_ringEquiv' hstep3
    (locAugIdealQuotEquivLocAugIdealReduced G)

/-- **Combined** inductive + base case: CM of `Localization.AtPrime (augIdealReduced G)`
for any HH graph `G` on `Fin (r + 1)`. -/
private theorem isCohenMacaulayLocalRing_at_augIdealReduced
    {r : ℕ} {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := by
  by_cases hr : r = 0
  · subst hr
    exact isCohenMacaulayLocalRing_at_augIdealReduced_base (K := K) G
  · exact isCohenMacaulayLocalRing_at_augIdealReduced_step (K := K)
      (by omega) hHH

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

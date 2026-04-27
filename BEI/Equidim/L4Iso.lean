import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import BEI.Equidim.Transport
import BEI.Equidim.ClosedGraphIntervals
import BEI.Equidim.IteratedRegularity
import BEI.Equidim.AugmentationLocalCM
import BEI.Equidim.GlobalCMSetup
import BEI.Equidim.F2Scaffolding
import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import BEI.ReducedHH
import toMathlib.Equidim.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
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
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.MvPolynomial

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial SimpleGraph IsLocalRing

/-!
# Equidimensional surrogate: L4 iso

This file isolates the construction of the L4 isomorphism

  `K[W] / I(Γ_G|_W) ≃ₐ[K] A^red_{G'} ⊗_K K[Λ]`

at the heart of the F2-route global Cohen-Macaulay proof: forward map,
backward map, bijectivity, and assembly steps.

## Reference: Herzog et al. (2010), proof of Proposition 1.6
-/

/-! #### Step 4/5/6: the L4 iso

The isomorphism `K[W] / I(Γ_G|_W) ≃ₐ[K] A^red_{G'} ⊗_K K[Λ]` on generators:

* `X ⟨Sum.inl c_a, _⟩ ↦ (mk X(inl a)) ⊗ 1` for paired-survivor `a`.
* `X ⟨Sum.inr c_a, _⟩ ↦ (mk X(inr a)) ⊗ 1` similarly.
* `X ⟨λ, _⟩ ↦ 1 ⊗ X ⟨λ, _⟩` for `λ ∈ lambdaSet G U`.
-/

/-- The inverse of `pairedSurvivorsEmb`: given `i ∈ pairedSurvivors G U`,
return the `Fin r` index. -/
noncomputable def pairedSurvivorsIdx {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) : Fin (pairedCount G U) :=
  ((pairedSurvivors G U).orderIsoOfFin rfl).symm ⟨i, hi⟩

private theorem pairedSurvivorsVal_idx {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    pairedSurvivorsVal G U (pairedSurvivorsIdx G U hi) = i := by
  have h : ((pairedSurvivors G U).orderIsoOfFin rfl)
      (((pairedSurvivors G U).orderIsoOfFin rfl).symm ⟨i, hi⟩) = ⟨i, hi⟩ :=
    ((pairedSurvivors G U).orderIsoOfFin rfl).apply_symm_apply _
  have h' : (((pairedSurvivors G U).orderIsoOfFin rfl)
      (((pairedSurvivors G U).orderIsoOfFin rfl).symm ⟨i, hi⟩) : Fin n) = i :=
    congrArg Subtype.val h
  -- The LHS unfolds to `(pairedSurvivors G U).orderEmbOfFin rfl (idx)`
  -- which is `pairedSurvivorsVal G U (pairedSurvivorsIdx G U hi)`.
  rw [Finset.coe_orderIsoOfFin_apply] at h'
  exact h'

theorem pairedSurvivorsIdx_val {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) :
    pairedSurvivorsIdx G U (pairedSurvivorsVal_mem G U a) = a := by
  unfold pairedSurvivorsIdx pairedSurvivorsVal pairedSurvivorsEmb
  have : ((pairedSurvivors G U).orderIsoOfFin rfl).symm
      (((pairedSurvivors G U).orderIsoOfFin rfl) a) = a :=
    ((pairedSurvivors G U).orderIsoOfFin rfl).symm_apply_apply _
  -- ⟨pairedSurvivorsVal G U a, pairedSurvivorsVal_mem G U a⟩ = orderIsoOfFin a
  have heq : ((pairedSurvivors G U).orderIsoOfFin rfl) a =
      ⟨pairedSurvivorsVal G U a, pairedSurvivorsVal_mem G U a⟩ := by
    apply Subtype.ext
    simp [Finset.coe_orderIsoOfFin_apply, pairedSurvivorsVal, pairedSurvivorsEmb]
  rw [heq] at this
  exact this

/-- `pairedSurvivorsIdx` preserves `<`. -/
theorem pairedSurvivorsIdx_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n)))
    {i j : Fin n} (hi : i ∈ pairedSurvivors G U) (hj : j ∈ pairedSurvivors G U)
    (hlt : i < j) :
    pairedSurvivorsIdx G U hi < pairedSurvivorsIdx G U hj := by
  -- Apply the order iso: it is order-preserving so `i < j` gives the indices as
  -- subtypes and then the strictMono of symm on the image gives `idx < idx`.
  have h1 : (⟨i, hi⟩ : { x // x ∈ pairedSurvivors G U }) <
      ⟨j, hj⟩ := hlt
  exact ((pairedSurvivors G U).orderIsoOfFin rfl).symm.strictMono h1

/-- `pairedSurvivorsIdx` preserves `≤`. -/
theorem pairedSurvivorsIdx_le {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n)))
    {i j : Fin n} (hi : i ∈ pairedSurvivors G U) (hj : j ∈ pairedSurvivors G U)
    (hle : i ≤ j) :
    pairedSurvivorsIdx G U hi ≤ pairedSurvivorsIdx G U hj := by
  have h1 : (⟨i, hi⟩ : { x // x ∈ pairedSurvivors G U }) ≤
      ⟨j, hj⟩ := hle
  exact ((pairedSurvivors G U).orderIsoOfFin rfl).symm.monotone h1

/-- A paired-survivor index `i` satisfies `i.val + 1 < n`. -/
private theorem pairedSurvivors_succ_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    i.val + 1 < n := by
  classical
  unfold pairedSurvivors at hi
  rw [Finset.mem_filter] at hi
  exact hi.2.1

/-- A paired-survivor index `i` has `inl i ∈ hhSurvivors G U`. -/
theorem pairedSurvivors_inl_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U := by
  classical
  unfold pairedSurvivors at hi
  rw [Finset.mem_filter] at hi
  exact hi.2.2.1

/-- A paired-survivor index `i` has `inr i ∈ hhSurvivors G U`. -/
theorem pairedSurvivors_inr_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U := by
  classical
  unfold pairedSurvivors at hi
  rw [Finset.mem_filter] at hi
  exact hi.2.2.2

/-- For `v ∈ hhSurvivors G U` with `v.val = Sum.inl i`, if `i ∉ pairedSurvivors G U`,
then `v.val ∈ lambdaSet G U`. -/
private theorem lambdaSet_mem_of_inl_not_paired {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ lambdaSet G U := by
  classical
  refine ⟨hmem, ?_⟩
  rintro (⟨j, hjmem, hj⟩ | ⟨j, hjmem, hj⟩)
  · -- Sum.inl j = Sum.inl i, so i = j, so j ∈ pairedSurvivors → contradiction.
    have hij : i = j := by
      have : Sum.inl (α := Fin n) (β := Fin n) j = Sum.inl i := hj
      exact (Sum.inl.inj this).symm
    subst hij
    exact hi hjmem
  · -- Sum.inr j = Sum.inl i: impossible.
    cases hj

/-- For `v ∈ hhSurvivors G U` with `v.val = Sum.inr i`, if `i ∉ pairedSurvivors G U`,
then `v.val ∈ lambdaSet G U`. -/
private theorem lambdaSet_mem_of_inr_not_paired {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ lambdaSet G U := by
  classical
  refine ⟨hmem, ?_⟩
  rintro (⟨j, hjmem, hj⟩ | ⟨j, hjmem, hj⟩)
  · cases hj
  · have hij : i = j := by
      have : Sum.inr (α := Fin n) (β := Fin n) j = Sum.inr i := hj
      exact (Sum.inr.inj this).symm
    subst hij
    exact hi hjmem

/-- Image of an `Sum.inl i` survivor in the tensor product. -/
private noncomputable def L4ForwardInl {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (i : Fin n) (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) := by
  classical
  by_cases hi : i ∈ pairedSurvivors G U
  · -- paired: map to (mk X(inl a)) ⊗ 1
    exact ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
      (X (Sum.inl (pairedSurvivorsIdx G U hi)))) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1
  · -- isolated: map to 1 ⊗ X ⟨inl i, _⟩
    exact (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
      (X ⟨(Sum.inl i : BinomialEdgeVars (Fin n)),
        lambdaSet_mem_of_inl_not_paired G U hmem hi⟩ :
          MvPolynomial (lambdaSet G U) K)

/-- Image of an `Sum.inr i` survivor in the tensor product. -/
private noncomputable def L4ForwardInr {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (i : Fin n) (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) := by
  classical
  by_cases hi : i ∈ pairedSurvivors G U
  · exact ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
      (X (Sum.inr (pairedSurvivorsIdx G U hi)))) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1
  · exact (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
      (X ⟨(Sum.inr i : BinomialEdgeVars (Fin n)),
        lambdaSet_mem_of_inr_not_paired G U hmem hi⟩ :
          MvPolynomial (lambdaSet G U) K)

/-- Paired case of `L4ForwardInl`. -/
theorem L4ForwardInl_of_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∈ pairedSurvivors G U) :
    L4ForwardInl (K := K) G U i hmem =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
        (X (Sum.inl (pairedSurvivorsIdx G U hi)))) :
          BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  unfold L4ForwardInl
  rw [dif_pos hi]

/-- Isolated case of `L4ForwardInl`. -/
private theorem L4ForwardInl_of_not_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    L4ForwardInl (K := K) G U i hmem =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X ⟨(Sum.inl i : BinomialEdgeVars (Fin n)),
          lambdaSet_mem_of_inl_not_paired G U hmem hi⟩ :
            MvPolynomial (lambdaSet G U) K) := by
  classical
  unfold L4ForwardInl
  rw [dif_neg hi]

/-- Paired case of `L4ForwardInr`. -/
theorem L4ForwardInr_of_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∈ pairedSurvivors G U) :
    L4ForwardInr (K := K) G U i hmem =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
        (X (Sum.inr (pairedSurvivorsIdx G U hi)))) :
          BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  unfold L4ForwardInr
  rw [dif_pos hi]

/-- Isolated case of `L4ForwardInr`. -/
private theorem L4ForwardInr_of_not_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    L4ForwardInr (K := K) G U i hmem =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X ⟨(Sum.inr i : BinomialEdgeVars (Fin n)),
          lambdaSet_mem_of_inr_not_paired G U hmem hi⟩ :
            MvPolynomial (lambdaSet G U) K) := by
  classical
  unfold L4ForwardInr
  rw [dif_neg hi]

/-- Step 4 forward on generators: send a survivor variable to its image in the
tensor product. -/
private noncomputable def L4ForwardGen {n : ℕ}
    {G : SimpleGraph (Fin n)} (_hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (_hU : hhIndep G U)
    (v : hhSurvivors G U) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) :=
  match hvc : (v.val : BinomialEdgeVars (Fin n)) with
  | Sum.inl i => L4ForwardInl (K := K) G U i (hvc ▸ v.property)
  | Sum.inr i => L4ForwardInr (K := K) G U i (hvc ▸ v.property)

/-- `L4ForwardGen` on an `Sum.inl` survivor. -/
theorem L4ForwardGen_inl {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) {i : Fin n} (hvc : v.val = Sum.inl i) :
    L4ForwardGen (K := K) hHH U hU v =
      L4ForwardInl (K := K) G U i (hvc ▸ v.property) := by
  -- Use Subtype.ext_iff pattern to unfold v.
  obtain ⟨vv, hvv⟩ := v
  change vv = Sum.inl i at hvc
  subst hvc
  rfl

/-- `L4ForwardGen` on an `Sum.inr` survivor. -/
theorem L4ForwardGen_inr {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) {i : Fin n} (hvc : v.val = Sum.inr i) :
    L4ForwardGen (K := K) hHH U hU v =
      L4ForwardInr (K := K) G U i (hvc ▸ v.property) := by
  obtain ⟨vv, hvv⟩ := v
  change vv = Sum.inr i at hvc
  subst hvc
  rfl

/-- The underlying polynomial algebra hom from `K[W]` extending `L4ForwardGen`. -/
private noncomputable def L4ForwardPoly {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    polyRestrict (K := K) (hhSurvivors G U) →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
  MvPolynomial.aeval (L4ForwardGen (K := K) hHH U hU)

@[simp]
private theorem L4ForwardPoly_X {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) :
    L4ForwardPoly (K := K) hHH U hU (X v) = L4ForwardGen (K := K) hHH U hU v := by
  unfold L4ForwardPoly
  simp [MvPolynomial.aeval_X]

/-- Each restricted edge generator `X p * X q` maps to zero under the polynomial
forward map. This is the key well-definedness fact for descending through
the restricted edge ideal. -/
private theorem L4ForwardPoly_vanishes_on_gens {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    {p q : hhSurvivors G U}
    (hedge : (p.val, q.val) ∈ hhEdgeSet G) :
    L4ForwardPoly (K := K) hHH U hU (X p * X q) = 0 := by
  classical
  -- Unpack the edge.
  obtain ⟨i, j, hj_succ, hadjG, hle_ij, heq⟩ := hedge
  have hpl : p.val = Sum.inl i := by
    have h := (Prod.mk.injEq _ _ _ _).mp heq
    exact h.1
  have hqr : q.val = Sum.inr j := by
    have h := (Prod.mk.injEq _ _ _ _).mp heq
    exact h.2
  -- Both `p` and `q` belong to `hhSurvivors G U`.
  have hp_mem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    hpl ▸ p.property
  have hq_mem : (Sum.inr j : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    hqr ▸ q.property
  -- Rewrite X p * X q to X (inl i) via Subtype ext.
  rw [map_mul, L4ForwardPoly_X, L4ForwardPoly_X,
    L4ForwardGen_inl (K := K) hHH hU p hpl,
    L4ForwardGen_inr (K := K) hHH hU q hqr]
  -- Case split on whether i and j are in pairedSurvivors.
  by_cases hi : i ∈ pairedSurvivors G U
  · by_cases hj : j ∈ pairedSurvivors G U
    · -- Both paired. Produce (mk X(inl a)) ⊗ 1 * (mk X(inr b)) ⊗ 1
      -- = (mk (X(inl a) * X(inr b))) ⊗ 1, and the product is in reducedHHIdeal.
      rw [L4ForwardInl_of_paired (K := K) G U hp_mem hi,
        L4ForwardInr_of_paired (K := K) G U hq_mem hj]
      -- Indices:
      set a : Fin (pairedCount G U) := pairedSurvivorsIdx G U hi with ha_def
      set b : Fin (pairedCount G U) := pairedSurvivorsIdx G U hj with hb_def
      -- a ≤ b from i ≤ j.
      have hab : a ≤ b := pairedSurvivorsIdx_le G U hi hj hle_ij
      -- The G' edge: need G'.Adj a.castSucc ⟨b.val+1, _⟩.
      -- b+1 < r+1 since b.val < r.
      have hbsucc : b.val + 1 < pairedCount G U + 1 := by
        have : b.val < pairedCount G U := b.isLt
        omega
      -- The underlying indices satisfy pairedSurvivorsVal G U a = i,
      -- pairedSurvivorsVal G U b = j.
      have ha_val : pairedSurvivorsVal G U a = i := pairedSurvivorsVal_idx G U hi
      have hb_val : pairedSurvivorsVal G U b = j := pairedSurvivorsVal_idx G U hj
      -- Rewrite hadjG.
      have hc_succ : (pairedSurvivorsVal G U b).val + 1 < n := by
        rw [hb_val]; exact hj_succ
      have hadjG' : G.Adj (pairedSurvivorsVal G U a)
          ⟨(pairedSurvivorsVal G U b).val + 1, hc_succ⟩ := by
        rw [ha_val]
        have : (⟨(pairedSurvivorsVal G U b).val + 1, hc_succ⟩ : Fin n) =
            ⟨j.val + 1, hj_succ⟩ := by apply Fin.ext; simp [hb_val]
        rw [this]; exact hadjG
      -- G'.Adj a.castSucc ⟨b.val+1, hbsucc⟩.
      have hadjGp : (smallerHHGraph G U).Adj a.castSucc ⟨b.val + 1, hbsucc⟩ := by
        rw [smallerHHGraph, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ⟨a, b, hab, rfl, ?_, hc_succ, hadjG'⟩⟩
        · intro heq
          have : a.val = b.val + 1 := by exact_mod_cast congrArg Fin.val heq
          have hab_val : a.val ≤ b.val := hab
          omega
        · simp
      -- Thus X(inl a) * X(inr b) ∈ reducedHHIdeal (smallerHHGraph G U).
      have hmem_red : (X (Sum.inl a) * X (Sum.inr b) :
          MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K) ∈
          BEI.reducedHHIdeal (K := K) (smallerHHGraph G U) :=
        BEI.X_inl_mul_X_inr_mem_reducedHHIdeal (K := K) hab hbsucc hadjGp
      -- Now compute the product in the tensor.
      -- (mk X(inl a) ⊗ 1) * (mk X(inr b) ⊗ 1) = mk (X(inl a) * X(inr b)) ⊗ 1 = 0 ⊗ 1 = 0.
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul,
        (Ideal.Quotient.eq_zero_iff_mem).mpr hmem_red, TensorProduct.zero_tmul]
    · -- i ∈ paired, j ∉ paired. Contradiction via L3 lemmas.
      -- Since j ∈ hhSurvivors via hq_mem : Sum.inr j ∈ hhSurvivors, and j ∉ paired,
      -- one of j+1 ≥ n, Sum.inl j ∉ hhSurvivors, Sum.inr j ∉ hhSurvivors.
      -- Since Sum.inr j ∈ hhSurvivors, and j+1 < n, we have Sum.inl j ∉ hhSurvivors.
      have hj_not_paired : ¬((j.val + 1 < n ∧
          (Sum.inl j : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U ∧
          (Sum.inr j : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)) := by
        intro hh
        apply hj
        unfold pairedSurvivors
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hh⟩
      -- Derive Sum.inl j ∉ hhSurvivors.
      have hxj_not : (Sum.inl j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
        intro hxj
        exact hj_not_paired ⟨hj_succ, hxj, hq_mem⟩
      -- Apply hhSurvivor_y_isolated: Sum.inl j isolates from neighbours.
      -- The neighbour is Sum.inr i with edge (inl i, inr j)? No — the statement:
      -- hhSurvivor_y_isolated says Sum.inr j ∈ hhSurvivors, Sum.inl j ∉, then
      -- every edge (Sum.inl k, Sum.inr j) has Sum.inl k ∉ hhSurvivors.
      -- Apply with k = i: we know hadj : G.Adj i ⟨j+1⟩ so (inl i, inr j) ∈ hhEdgeSet.
      have hedge_ij : (Sum.inl i, Sum.inr j) ∈ hhEdgeSet G :=
        ⟨i, j, hj_succ, hadjG, hle_ij, rfl⟩
      have hxi_not : (Sum.inl i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U :=
        hhSurvivor_y_isolated hHH hq_mem hxj_not hedge_ij
      exact absurd hp_mem hxi_not
  · -- i ∉ paired.
    -- By similar reasoning, Sum.inl i ∈ hhSurvivors (via hp_mem), so either
    -- i+1 ≥ n OR Sum.inr i ∉ hhSurvivors. First: i+1 < n since i ≤ j < n
    -- and j+1 < n, so i < j+1 ≤ n-1+1 = n. Wait, we need i.val + 1 < n.
    -- Actually from hle_ij : i ≤ j and hj_succ : j.val + 1 < n, we get
    -- i.val ≤ j.val, hence i.val + 1 ≤ j.val + 1 < n.
    have hi_succ : i.val + 1 < n := by
      have : i.val ≤ j.val := hle_ij
      omega
    have hi_not_paired : ¬((i.val + 1 < n ∧
        (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U ∧
        (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)) := by
      intro hh
      apply hi
      unfold pairedSurvivors
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hh⟩
    have hyi_not : (Sum.inr i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
      intro hyi
      exact hi_not_paired ⟨hi_succ, hp_mem, hyi⟩
    -- Apply hhSurvivor_x_isolated: Sum.inl i ∈ hhSurvivors, Sum.inr i ∉ hhSurvivors,
    -- then every edge (Sum.inl i, Sum.inr k) has Sum.inr k ∉ hhSurvivors.
    have hedge_ij : (Sum.inl i, Sum.inr j) ∈ hhEdgeSet G :=
      ⟨i, j, hj_succ, hadjG, hle_ij, rfl⟩
    have hyj_not : (Sum.inr j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U :=
      hhSurvivor_x_isolated hHH hp_mem hyi_not hedge_ij
    exact absurd hq_mem hyj_not

/-- The forward map vanishes on the entire restricted edge ideal. -/
private theorem L4ForwardPoly_vanishes {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (x : polyRestrict (K := K) (hhSurvivors G U)) :
    x ∈ restrictedEdgeIdeal (K := K) G (hhSurvivors G U) →
      L4ForwardPoly (K := K) hHH U hU x = 0 := by
  intro hx
  unfold restrictedEdgeIdeal MvPolynomial.variablePairIdeal at hx
  refine Submodule.span_induction (p := fun y _ =>
    L4ForwardPoly (K := K) hHH U hU y = 0) ?_ ?_ ?_ ?_ hx
  · -- Generators: y = X p * X q for an edge.
    rintro y ⟨p, q, hpq, rfl⟩
    -- Translate hpq : (p, q) ∈ restrictedEdgesSubtype, i.e. (p.val, q.val) ∈ hhEdgeSet G.
    exact L4ForwardPoly_vanishes_on_gens hHH hU hpq
  · simp
  · intros _ _ _ _ hx hy; simp [hx, hy]
  · intros r x _ hx; simp [hx]

/-- Step 4 forward: the descent to the quotient. -/
private noncomputable def L4Forward {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    restrictedHHRing (K := K) G (hhSurvivors G U) →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
  Ideal.Quotient.liftₐ (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
    (L4ForwardPoly (K := K) hHH U hU)
    (L4ForwardPoly_vanishes (K := K) hHH hU)

/-! #### Step 5 — backward map -/

/-- Backward on a reduced-HH generator `Sum.inl a` or `Sum.inr a`:
`x'_a ↦ mk X ⟨Sum.inl c_a, _⟩`, `y'_a ↦ mk X ⟨Sum.inr c_a, _⟩`. -/
private noncomputable def L4BackwardRedGen {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin (pairedCount G U))) :
    restrictedHHRing (K := K) G (hhSurvivors G U) :=
  match v with
  | Sum.inl a =>
      Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
        (X ⟨(Sum.inl (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)),
          pairedSurvivors_inl_mem G U (pairedSurvivorsVal_mem G U a)⟩)
  | Sum.inr a =>
      Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
        (X ⟨(Sum.inr (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)),
          pairedSurvivors_inr_mem G U (pairedSurvivorsVal_mem G U a)⟩)

/-- The polynomial hom extending `L4BackwardRedGen`. -/
private noncomputable def L4BackwardRedPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  MvPolynomial.aeval (L4BackwardRedGen (K := K) G U)

@[simp]
private theorem L4BackwardRedPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin (pairedCount G U))) :
    L4BackwardRedPoly (K := K) G U (X v) = L4BackwardRedGen (K := K) G U v := by
  unfold L4BackwardRedPoly
  simp [MvPolynomial.aeval_X]

/-- Unpacking of `smallerHHGraph` edges (forward direction only, with `a ≤ b` as a
required hypothesis): given the adjacency and the ordering constraint,
extract the underlying `G`-edge on paired-survivor indices. -/
private theorem smallerHHGraph_adj_imp {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Set (BinomialEdgeVars (Fin n))}
    {a : Fin (pairedCount G U)} {b : Fin (pairedCount G U)}
    (hab : a ≤ b) (hb : b.val + 1 < pairedCount G U + 1)
    (hadj : (smallerHHGraph G U).Adj a.castSucc ⟨b.val + 1, hb⟩) :
    ∃ hc : (pairedSurvivorsVal G U b).val + 1 < n,
      G.Adj (pairedSurvivorsVal G U a)
        ⟨(pairedSurvivorsVal G U b).val + 1, hc⟩ := by
  rw [smallerHHGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨_, h⟩ := hadj
  rcases h with h | h
  · obtain ⟨a', b', _, hu_eq, hv_eq, hc, hadj'⟩ := h
    have ha_eq : a = a' := by
      apply Fin.ext
      have := congrArg Fin.val hu_eq
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
      omega
    have hb_eq : b = b' := by
      apply Fin.ext
      have h1 : (⟨b.val + 1, hb⟩ : Fin (pairedCount G U + 1)).val = b'.val + 1 := hv_eq
      simp at h1
      omega
    subst ha_eq; subst hb_eq
    exact ⟨hc, hadj'⟩
  · -- reverse branch: impossible given a ≤ b.
    exfalso
    obtain ⟨a', b', hab', hu_eq, hv_eq, _, _⟩ := h
    -- u = ⟨b.val+1, hb⟩ = a'.castSucc, so a'.val = b.val+1
    -- v = a.castSucc, v.val = b'.val+1, so a.val = b'.val + 1
    have ha' : a'.val = b.val + 1 := by
      exact_mod_cast (congrArg Fin.val hu_eq).symm
    have hb' : a.val = b'.val + 1 := by exact_mod_cast hv_eq
    -- a' ≤ b' gives b.val + 1 ≤ b'.val, and a.val = b'.val + 1, so a.val ≥ b.val + 2.
    have h1 : a'.val ≤ b'.val := hab'
    have h2 : a.val ≤ b.val := hab
    omega

/-- The backward reduced-HH polynomial hom vanishes on reducedHH generators. -/
private theorem L4BackwardRedPoly_vanishes_on_gens {n : ℕ}
    {G : SimpleGraph (Fin n)} (U : Set (BinomialEdgeVars (Fin n)))
    {a b : BinomialEdgeVars (Fin (pairedCount G U))}
    (hab : (a, b) ∈ BEI.reducedHHEdgeSet (smallerHHGraph G U)) :
    L4BackwardRedPoly (K := K) G U (X a * X b) = 0 := by
  obtain ⟨a', b', hbsucc, hadjGp, hle, heq⟩ := hab
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _|>.mp heq
  -- Now a = Sum.inl a', b = Sum.inr b', with G'.Adj a'.castSucc ⟨b'.val+1, hbsucc⟩ and a' ≤ b'.
  obtain ⟨hc, hadjG⟩ := smallerHHGraph_adj_imp hle hbsucc hadjGp
  -- Use pairedSurvivorsVal_spec to get the underlying indices and the edge membership.
  set ia : Fin n := pairedSurvivorsVal G U a' with hia_def
  set ib : Fin n := pairedSurvivorsVal G U b' with hib_def
  -- Under the backward map, X(inl a') ↦ mk X ⟨Sum.inl ia, _⟩
  -- and X(inr b') ↦ mk X ⟨Sum.inr ib, _⟩.
  -- Their product in restrictedHHRing is mk (X ⟨inl ia, _⟩ * X ⟨inr ib, _⟩), which is in
  -- restrictedEdgeIdeal because (inl ia, inr ib) ∈ hhEdgeSet G.
  rw [map_mul]
  rw [L4BackwardRedPoly_X, L4BackwardRedPoly_X]
  simp only [L4BackwardRedGen]
  -- Get the indexed memberships.
  have hia_mem : (Sum.inl ia : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    pairedSurvivors_inl_mem G U (pairedSurvivorsVal_mem G U a')
  have hib_mem : (Sum.inr ib : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    pairedSurvivors_inr_mem G U (pairedSurvivorsVal_mem G U b')
  -- The strict monotonicity gives c_a' ≤ c_b' from a' ≤ b'.
  have hia_le_ib : ia ≤ ib := (pairedSurvivorsEmb G U).monotone hle
  -- The edge in hhEdgeSet G.
  have hedge : (Sum.inl ia, Sum.inr ib) ∈ hhEdgeSet G :=
    ⟨ia, ib, hc, hadjG, hia_le_ib, rfl⟩
  -- The edge in restrictedEdgesSubtype.
  have hedge_sub : (⟨(Sum.inl ia : BinomialEdgeVars (Fin n)), hia_mem⟩,
      ⟨(Sum.inr ib : BinomialEdgeVars (Fin n)), hib_mem⟩) ∈
      restrictedEdgesSubtype G (hhSurvivors G U) := hedge
  -- The product is in restrictedEdgeIdeal.
  have hmem_ideal : (X ⟨(Sum.inl ia : BinomialEdgeVars (Fin n)), hia_mem⟩ *
      X ⟨(Sum.inr ib : BinomialEdgeVars (Fin n)), hib_mem⟩ :
      polyRestrict (K := K) (hhSurvivors G U)) ∈
      restrictedEdgeIdeal (K := K) G (hhSurvivors G U) :=
    Ideal.subset_span ⟨_, _, hedge_sub, rfl⟩
  rw [← map_mul, (Ideal.Quotient.eq_zero_iff_mem).mpr hmem_ideal]

/-- Step 5 backward reduced: `A^red_{G'} →ₐ[K] K[W]/I(Γ_G|_W)`. -/
private noncomputable def L4BackwardRed {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    BEI.reducedHHRing (K := K) (smallerHHGraph G U) →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  Ideal.Quotient.liftₐ (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
    (L4BackwardRedPoly (K := K) G U) (by
      intro x hx
      unfold BEI.reducedHHIdeal MvPolynomial.variablePairIdeal at hx
      refine Submodule.span_induction (p := fun y _ =>
        L4BackwardRedPoly (K := K) G U y = 0) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨a, b, hab, rfl⟩
        exact L4BackwardRedPoly_vanishes_on_gens U hab
      · simp
      · intros _ _ _ _ hx hy; simp [hx, hy]
      · intros r x _ hx; simp [hx])

/-- Step 5 backward on `K[Λ]`: `X ⟨λ, _⟩ ↦ mk (X ⟨λ, _⟩)`. -/
private noncomputable def L4BackwardPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    MvPolynomial (lambdaSet G U) K →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  MvPolynomial.aeval (fun v =>
    Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
      (X ⟨v.val, v.property.1⟩))

@[simp]
private theorem L4BackwardPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (v : lambdaSet G U) :
    L4BackwardPoly (K := K) G U (X v) =
      Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
        (X ⟨v.val, v.property.1⟩) := by
  unfold L4BackwardPoly
  simp [MvPolynomial.aeval_X]

/-- Step 5 backward: full backward map via `Algebra.TensorProduct.lift`. -/
private noncomputable def L4Backward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  Algebra.TensorProduct.lift (L4BackwardRed (K := K) G U)
    (L4BackwardPoly (K := K) G U) (fun _ _ => mul_comm _ _)

/-! #### Step 6 — bijectivity and assembly -/

/-- The quotient map `aeval (L4ForwardGen) = (Ideal.Quotient.mk ∘ aeval) ...`.
-- Forward on `mk (X v)` equals `L4ForwardGen v`. -/
theorem L4Forward_mk_X {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) :
    L4Forward (K := K) hHH U hU
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U)) (X v)) =
    L4ForwardGen (K := K) hHH U hU v := by
  unfold L4Forward
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact L4ForwardPoly_X (K := K) hHH hU v

/-- Composition Backward ∘ Forward = id, generator-level (on `mk (X v)`). -/
private theorem L4Backward_Forward_mk_X {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) :
    (L4Backward (K := K) G U) (L4Forward (K := K) hHH U hU
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U)) (X v))) =
    Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U)) (X v) := by
  classical
  rw [L4Forward_mk_X]
  -- Case on v.val using match.
  obtain ⟨vv, hvv⟩ := v
  match hvc : vv, hvv with
  | Sum.inl i, hvv =>
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨Sum.inl i, hvv⟩ rfl]
    by_cases hi : i ∈ pairedSurvivors G U
    · rw [L4ForwardInl_of_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      unfold L4BackwardRed
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      change (L4BackwardRedPoly (K := K) G U) (X _) = _
      rw [L4BackwardRedPoly_X]
      simp only [L4BackwardRedGen]
      have h := pairedSurvivorsVal_idx G U hi
      -- Rewrite the target using the identity.
      congr 2
      apply Subtype.ext
      simp [h]
    · rw [L4ForwardInl_of_not_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [L4BackwardPoly_X]
  | Sum.inr i, hvv =>
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨Sum.inr i, hvv⟩ rfl]
    by_cases hi : i ∈ pairedSurvivors G U
    · rw [L4ForwardInr_of_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      unfold L4BackwardRed
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      change (L4BackwardRedPoly (K := K) G U) (X _) = _
      rw [L4BackwardRedPoly_X]
      simp only [L4BackwardRedGen]
      have h := pairedSurvivorsVal_idx G U hi
      congr 2
      apply Subtype.ext
      simp [h]
    · rw [L4ForwardInr_of_not_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [L4BackwardPoly_X]

/-- Composition Backward ∘ Forward = id, at the algHom level. -/
private theorem L4Backward_Forward {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    (L4Backward (K := K) G U).comp (L4Forward (K := K) hHH U hU) =
      AlgHom.id K (restrictedHHRing (K := K) G (hhSurvivors G U)) := by
  -- Use quotient-algHom extension: suffices to check on mk (X v) for v : hhSurvivors G U.
  apply Ideal.Quotient.algHom_ext
  -- Now we have: f.comp (Quotient.mkₐ) = g.comp (Quotient.mkₐ), on polynomials.
  apply MvPolynomial.algHom_ext
  intro v
  change (L4Backward (K := K) G U) (L4Forward (K := K) hHH U hU
    (Ideal.Quotient.mk _ (X v))) = _
  rw [L4Backward_Forward_mk_X]
  rfl

/-- Composition Forward ∘ Backward on pure tensors, left case `mk (X v) ⊗ 1`. -/
private theorem L4Forward_Backward_inl_tmul {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : BinomialEdgeVars (Fin (pairedCount G U))) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
          (X v) : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) (X v) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  -- Simplify L4Backward on the pure tensor.
  have h_inc : (L4Backward (K := K) G U)
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) (X v) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1) =
      (L4BackwardRed (K := K) G U)
        (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) (X v)) := by
    unfold L4Backward
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rw [h_inc]
  unfold L4BackwardRed
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change (L4Forward (K := K) hHH U hU)
    ((L4BackwardRedPoly (K := K) G U) (X v)) = _
  rw [L4BackwardRedPoly_X]
  -- L4BackwardRedGen v: case on v.
  rcases v with a | a
  · simp only [L4BackwardRedGen]
    rw [L4Forward_mk_X]
    have hi : pairedSurvivorsVal G U a ∈ pairedSurvivors G U :=
      pairedSurvivorsVal_mem G U a
    have hmem : (Sum.inl (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
        hhSurvivors G U := pairedSurvivors_inl_mem G U hi
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨_, hmem⟩ rfl]
    rw [L4ForwardInl_of_paired (K := K) G U hmem hi]
    rw [pairedSurvivorsIdx_val]
  · simp only [L4BackwardRedGen]
    rw [L4Forward_mk_X]
    have hi : pairedSurvivorsVal G U a ∈ pairedSurvivors G U :=
      pairedSurvivorsVal_mem G U a
    have hmem : (Sum.inr (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
        hhSurvivors G U := pairedSurvivors_inr_mem G U hi
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨_, hmem⟩ rfl]
    rw [L4ForwardInr_of_paired (K := K) G U hmem hi]
    rw [pairedSurvivorsIdx_val]

/-- Composition Forward ∘ Backward on pure tensors, right case `1 ⊗ X v`. -/
private theorem L4Forward_Backward_inr_tmul {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : lambdaSet G U) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
          (X v : MvPolynomial (lambdaSet G U) K))) =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X v : MvPolynomial (lambdaSet G U) K) := by
  classical
  have h_inc : (L4Backward (K := K) G U)
      ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X v : MvPolynomial (lambdaSet G U) K)) =
      (L4BackwardPoly (K := K) G U) (X v) := by
    unfold L4Backward
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rw [h_inc, L4BackwardPoly_X, L4Forward_mk_X]
  -- Case on v.val.
  have hvprop : v.val ∈ lambdaSet G U := v.property
  obtain ⟨vv, hvv⟩ := v
  match hvc : vv, hvv with
  | Sum.inl i, hvv =>
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨Sum.inl i, hvv.1⟩ rfl]
    have hi : i ∉ pairedSurvivors G U := by
      intro hi
      apply hvv.2
      exact Or.inl ⟨i, hi, rfl⟩
    rw [L4ForwardInl_of_not_paired (K := K) G U hvv.1 hi]
  | Sum.inr i, hvv =>
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨Sum.inr i, hvv.1⟩ rfl]
    have hi : i ∉ pairedSurvivors G U := by
      intro hi
      apply hvv.2
      exact Or.inr ⟨i, hi, rfl⟩
    rw [L4ForwardInr_of_not_paired (K := K) G U hvv.1 hi]

/-- Forward ∘ Backward on `a ⊗ 1` (left factor). Reduce to generators via an algHom
equality on `MvPolynomial`. -/
private theorem L4Forward_Backward_left {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (p : MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) p :
          BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) p :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  -- Think of both sides as K-algebra homs from `MvPoly` to the tensor product.
  -- φ_L : p ↦ forward (backward (mk p ⊗ 1))
  -- φ_R : p ↦ mk p ⊗ 1
  -- Both are K-algebra homs; they agree on X v (by L4Forward_Backward_inl_tmul),
  -- hence on all polynomials.
  set φL : MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    ((L4Forward (K := K) hHH U hU).comp (L4Backward (K := K) G U)).comp
      (((Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (B := MvPolynomial (lambdaSet G U) K))).comp
        (Ideal.Quotient.mkₐ K (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))))
  set φR : MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    ((Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (B := MvPolynomial (lambdaSet G U) K))).comp
      (Ideal.Quotient.mkₐ K (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)))
  have hφeq : φL = φR := by
    apply MvPolynomial.algHom_ext
    intro v
    -- Unfold both sides.
    change (L4Forward (K := K) hHH U hU) ((L4Backward (K := K) G U)
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
        (X v) : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1)) =
        (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
          (X v) : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1
    exact L4Forward_Backward_inl_tmul hHH hU v
  have := congrArg (fun φ => φ p) hφeq
  exact this

/-- Forward ∘ Backward on `1 ⊗ b` (right factor). -/
private theorem L4Forward_Backward_right {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (b : MvPolynomial (lambdaSet G U) K) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] b)) =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] b := by
  classical
  set φL : MvPolynomial (lambdaSet G U) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    ((L4Forward (K := K) hHH U hU).comp (L4Backward (K := K) G U)).comp
      (Algebra.TensorProduct.includeRight
        (R := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (B := MvPolynomial (lambdaSet G U) K))
  set φR : MvPolynomial (lambdaSet G U) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    Algebra.TensorProduct.includeRight
      (R := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (B := MvPolynomial (lambdaSet G U) K)
  have hφeq : φL = φR := by
    apply MvPolynomial.algHom_ext
    intro v
    change (L4Forward (K := K) hHH U hU) ((L4Backward (K := K) G U)
      ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] X v)) =
        (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] X v
    exact L4Forward_Backward_inr_tmul hHH hU v
  have := congrArg (fun φ => φ b) hφeq
  exact this

/-- Forward ∘ Backward on pure tensors. -/
private theorem L4Forward_Backward_tmul {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (a : BEI.reducedHHRing (K := K) (smallerHHGraph G U))
    (b : MvPolynomial (lambdaSet G U) K) :
    (L4Forward (K := K) hHH U hU) ((L4Backward (K := K) G U) (a ⊗ₜ[K] b)) =
      a ⊗ₜ[K] b := by
  classical
  -- Factor a ⊗ b = (a ⊗ 1) * (1 ⊗ b).
  have hsplit : a ⊗ₜ[K] b =
      ((a ⊗ₜ[K] (1 : MvPolynomial (lambdaSet G U) K)) *
        ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] b)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsplit, map_mul, map_mul]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [L4Forward_Backward_left hHH hU p, L4Forward_Backward_right hHH hU b]

/-- Composition Forward ∘ Backward = id, at the algHom level. -/
private theorem L4Forward_Backward {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    (L4Forward (K := K) hHH U hU).comp (L4Backward (K := K) G U) =
      AlgHom.id K (TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K)) := by
  classical
  apply Algebra.TensorProduct.ext'
  intro a b
  exact L4Forward_Backward_tmul hHH hU a b

/-- **Step 6: the L4 isomorphism.** -/
noncomputable def L4Iso {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    restrictedHHRing (K := K) G (hhSurvivors G U) ≃ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
  AlgEquiv.ofAlgHom (L4Forward (K := K) hHH U hU) (L4Backward (K := K) G U)
    (L4Forward_Backward (K := K) hHH U hU) (L4Backward_Forward (K := K) hHH U hU)


end

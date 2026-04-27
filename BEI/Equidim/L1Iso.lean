import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import BEI.Equidim.Transport
import BEI.Equidim.ClosedGraphIntervals
import BEI.Equidim.IteratedRegularity
import BEI.Equidim.AugmentationLocalCM
import BEI.Equidim.GlobalCMSetup
import BEI.Equidim.F2Scaffolding
import BEI.Equidim.L4Iso
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
# Equidimensional surrogate: L1 monomial-localisation iso

This file isolates the monomial-localisation ring isomorphism

  `Localization.Away (mkI s_U) ≃+* (target)`

used in the F2-route global Cohen-Macaulay proof: the well-definedness of
`L1ForwardPoly`, the extension of `L1ForwardQuot` over the away
localisation, the backward hom into the localisation, and the proofs that
the two compositions are the identity. Hosts both
`set_option maxHeartbeats 1300000 / 1100000` blocks
(`L1Forward_Backward_left`, `L1Forward_Backward_right`).

## Reference: Herzog et al. (2010), proof of Proposition 1.6
-/

/-! #### Step L1: monomial-localisation ring iso

For a Finset `U` of variables, independent in `Γ_G`, set
`s_U := ∏ u ∈ U, X u ∈ MvPolynomial σ K` and `W := σ \ (U ∪ N(U))`
(= `hhSurvivors G ↑U`). The L1 iso is a K-algebra isomorphism

  `R[s_U⁻¹] ≃ₐ[K] (restrictedHHRing G W) ⊗[K] Localization.Away s_U^U`

where `s_U^U` is the product of the variables `X ⟨u, _⟩` inside
`MvPolynomial {v // v ∈ U} K`, and `R := MvPolynomial σ K ⧸ I`
with `I = bipartiteEdgeMonomialIdeal G`. On generators:

* `mkI (X v) ↦ (mk X ⟨v, _⟩) ⊗ 1`          for `v ∈ W`;
* `mkI (X v) ↦ 0`                          for `v ∈ N(U)`;
* `mkI (X v) ↦ 1 ⊗ algebraMap (X ⟨v, _⟩)`  for `v ∈ U`.
-/

/-- The unit-variable product `s_U := ∏_{u ∈ U} X u` inside `MvPolynomial σ K`. -/
noncomputable def hhUnitProduct {n : ℕ}
    (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  ∏ u ∈ U, X (R := K) u

/-- The product of U-variables viewed in the subtype-indexed polynomial ring
`MvPolynomial {v // v ∈ (U : Set _)} K`. -/
noncomputable def hhUnitProductSub {n : ℕ}
    (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K :=
  ∏ u ∈ U.attach, X (R := K) ⟨u.val, by exact_mod_cast u.property⟩

/-- The target of the L1 forward hom. -/
private abbrev L1Target {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (BinomialEdgeVars (Fin n))) : Type _ :=
  TensorProduct K
    (restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
    (Localization.Away (hhUnitProductSub (K := K) U))

/-- Forward generator: send `v : BinomialEdgeVars (Fin n)` to its image in the
target, with a three-way case split on `W` / `U` / `N(U)` (other). The `N(U)`
case is not explicitly stated; we use the default value `0` when neither
`v ∈ W` nor `v ∈ U`, which is the correct image for `v ∈ N(U)`. -/
private noncomputable def L1ForwardGen {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin n)) : L1Target (K := K) G U := by
  classical
  by_cases hW : v ∈ hhSurvivors G (U : Set _)
  · exact ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
      (hhSurvivors G (U : Set _))) (X ⟨v, hW⟩) :
        restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1)
  · by_cases hU : v ∈ U
    · exact (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X (R := K) ⟨v, by exact_mod_cast hU⟩))
    · exact 0

/-- `L1ForwardGen` on a survivor (W) variable. -/
theorem L1ForwardGen_of_W {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {v : BinomialEdgeVars (Fin n)}
    (hW : v ∈ hhSurvivors G (U : Set _)) :
    L1ForwardGen (K := K) G U v =
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨v, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1) := by
  classical
  unfold L1ForwardGen
  rw [dif_pos hW]

/-- `L1ForwardGen` on a unit (U) variable (which cannot simultaneously be in W). -/
private theorem L1ForwardGen_of_U {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hU : v ∈ U) :
    L1ForwardGen (K := K) G U v =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X (R := K) ⟨v, by exact_mod_cast hU⟩)) := by
  classical
  unfold L1ForwardGen
  rw [dif_neg hnW, dif_pos hU]

/-- `L1ForwardGen` on a neighborhood (N(U)) variable, i.e. neither in `W` nor in `U`. -/
private theorem L1ForwardGen_of_N {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hnU : v ∉ U) :
    L1ForwardGen (K := K) G U v = 0 := by
  classical
  unfold L1ForwardGen
  rw [dif_neg hnW, dif_neg hnU]

/-- The polynomial-level L1 forward map. -/
private noncomputable def L1ForwardPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K →ₐ[K] L1Target (K := K) G U :=
  MvPolynomial.aeval (L1ForwardGen (K := K) G U)

@[simp]
theorem L1ForwardPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin n)) :
    L1ForwardPoly (K := K) G U (X v) = L1ForwardGen (K := K) G U v := by
  unfold L1ForwardPoly
  simp [MvPolynomial.aeval_X]

/-! ##### Well-definedness: `L1ForwardPoly` kills the bipartite edge ideal -/

/-- An HH edge `(p, q) = (Sum.inl i, Sum.inr j)` with `p, q` both in `W`:
then `X⟨p⟩ * X⟨q⟩` is a restricted-edge generator, hence killed in
`restrictedHHRing G W`. -/
private theorem L1Forward_vanishes_on_gen_W_W {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {p q : BinomialEdgeVars (Fin n)}
    (hedge : (p, q) ∈ hhEdgeSet G)
    (hpW : p ∈ hhSurvivors G (U : Set _))
    (hqW : q ∈ hhSurvivors G (U : Set _)) :
    L1ForwardPoly (K := K) G U (X p * X q) = 0 := by
  classical
  rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X,
    L1ForwardGen_of_W hpW, L1ForwardGen_of_W hqW]
  -- (mk X⟨p⟩ ⊗ 1) * (mk X⟨q⟩ ⊗ 1) = (mk (X⟨p⟩ * X⟨q⟩)) ⊗ 1 = 0 ⊗ 1 = 0.
  have hedge_sub : ((⟨p, hpW⟩ : (hhSurvivors G (U : Set _))),
      (⟨q, hqW⟩ : (hhSurvivors G (U : Set _)))) ∈
      restrictedEdgesSubtype G (hhSurvivors G (U : Set _)) := hedge
  have hmem_ideal : (X ⟨p, hpW⟩ * X ⟨q, hqW⟩ :
      polyRestrict (K := K) (hhSurvivors G (U : Set _))) ∈
      restrictedEdgeIdeal (K := K) G (hhSurvivors G (U : Set _)) :=
    Ideal.subset_span ⟨_, _, hedge_sub, rfl⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul,
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem_ideal, TensorProduct.zero_tmul]

/-- The forward hom kills the HH edge generator `X p * X q`. -/
private theorem L1Forward_vanishes_on_gens {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _))
    {p q : BinomialEdgeVars (Fin n)}
    (hedge : (p, q) ∈ hhEdgeSet G) :
    L1ForwardPoly (K := K) G U (X p * X q) = 0 := by
  classical
  -- Four-way case on whether p and q are in W.
  by_cases hpW : p ∈ hhSurvivors G (U : Set _)
  · by_cases hqW : q ∈ hhSurvivors G (U : Set _)
    · -- p, q both in W.
      exact L1Forward_vanishes_on_gen_W_W hedge hpW hqW
    · -- p ∈ W, q ∉ W. Is q ∈ U or q ∈ N(U)?
      rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X, L1ForwardGen_of_W hpW]
      by_cases hqU : q ∈ U
      · -- q ∈ U, then p (as other endpoint) ∈ N(U); but p ∈ W — contradiction.
        exfalso
        apply hpW
        -- p ∈ U ∪ hhNbhd G U because (p, q) ∈ hhEdgeSet and q ∈ U.
        refine Or.inr ⟨q, (by exact_mod_cast hqU : q ∈ (U : Set _)),
          Or.inr hedge⟩
      · rw [L1ForwardGen_of_N (show q ∉ hhSurvivors G (U : Set _) from hqW) hqU,
          mul_zero]
  · by_cases hqW : q ∈ hhSurvivors G (U : Set _)
    · -- p ∉ W, q ∈ W.
      rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X, L1ForwardGen_of_W hqW]
      by_cases hpU : p ∈ U
      · -- p ∈ U, q ∈ W. Then q ∈ N(U) via the edge — contradiction with hqW.
        exfalso
        apply hqW
        refine Or.inr ⟨p, (by exact_mod_cast hpU : p ∈ (U : Set _)),
          Or.inl hedge⟩
      · rw [L1ForwardGen_of_N hpW hpU, zero_mul]
    · -- Both p, q ∉ W. Case on whether they are in U.
      rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X]
      by_cases hpU : p ∈ U
      · by_cases hqU : q ∈ U
        · -- Both in U: independence forbids the edge.
          exfalso
          have hpU_set : p ∈ (U : Set (BinomialEdgeVars (Fin n))) := by
            exact_mod_cast hpU
          have hqU_set : q ∈ (U : Set (BinomialEdgeVars (Fin n))) := by
            exact_mod_cast hqU
          exact hU hpU_set hqU_set hedge
        · rw [L1ForwardGen_of_U hpW hpU, L1ForwardGen_of_N hqW hqU, mul_zero]
      · rw [L1ForwardGen_of_N hpW hpU, zero_mul]

/-- The forward polynomial hom vanishes on the entire bipartite edge ideal. -/
private theorem L1ForwardPoly_vanishes {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _))
    (x : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    x ∈ bipartiteEdgeMonomialIdeal (K := K) G →
      L1ForwardPoly (K := K) G U x = 0 := by
  classical
  rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
  intro hx
  unfold MvPolynomial.variablePairIdeal at hx
  refine Submodule.span_induction (p := fun y _ =>
    L1ForwardPoly (K := K) G U y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨p, q, hpq, rfl⟩
    exact L1Forward_vanishes_on_gens hU hpq
  · simp
  · intros _ _ _ _ hx hy; simp [hx, hy]
  · intros r x _ hx; simp [hx]

/-- Descent of `L1ForwardPoly` to the quotient ring `R`. -/
noncomputable def L1ForwardQuot {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) →ₐ[K] L1Target (K := K) G U :=
  Ideal.Quotient.liftₐ (bipartiteEdgeMonomialIdeal (K := K) G)
    (L1ForwardPoly (K := K) G U) (L1ForwardPoly_vanishes hU)

theorem L1ForwardQuot_mk {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (p : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    L1ForwardQuot (K := K) G U hU
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) p) =
      L1ForwardPoly (K := K) G U p := by
  unfold L1ForwardQuot
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

/-! ##### Extend `L1ForwardQuot` over `Localization.Away (mkI s_U)` -/

/-- The K-algebra hom sending `X u` for `u ∈ U` to
`1 ⊗ algebraMap (X ⟨u.val, u.property⟩)`. Used to prove that `L1ForwardPoly` on
`hhUnitProduct U` is `1 ⊗ algebraMap (hhUnitProductSub U)`, hence a unit. -/
private noncomputable def L1UnitRightHom {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K →ₐ[K]
      L1Target (K := K) G U :=
  Algebra.TensorProduct.includeRight.comp
    (IsScalarTower.toAlgHom K
      (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
      (Localization.Away (hhUnitProductSub (K := K) U)))

/-- `L1UnitRightHom` on `X v` equals `1 ⊗ algebraMap (X v)`. -/
private theorem L1UnitRightHom_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : (U : Set (BinomialEdgeVars (Fin n)))) :
    L1UnitRightHom (K := K) G U (X v) =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X v)) := by
  unfold L1UnitRightHom
  rw [AlgHom.comp_apply]
  change Algebra.TensorProduct.includeRight _ = _
  rw [Algebra.TensorProduct.includeRight_apply]
  rfl

/-- Key identity: on U-variables, `L1ForwardPoly` agrees with `L1UnitRightHom ∘ map`,
where `map : MvPolynomial σ K → MvPolynomial U K` sends `X u` to `X ⟨u, hu⟩` if
`u ∈ U` and to `0` otherwise. We phrase this cleanly via a direct calculation on
the product `hhUnitProduct`. -/
private theorem L1ForwardPoly_hhUnitProduct_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    L1ForwardPoly (K := K) G U (hhUnitProduct U) =
      L1UnitRightHom (K := K) G U (hhUnitProductSub (K := K) U) := by
  classical
  unfold hhUnitProduct hhUnitProductSub
  rw [map_prod, map_prod]
  -- Rewrite LHS via Finset.prod_attach.
  rw [← Finset.prod_attach U
    (f := fun u => L1ForwardPoly (K := K) G U (X (R := K) u))]
  apply Finset.prod_congr rfl
  intro u _
  -- For u ∈ U, L1ForwardPoly (X u) = 1 ⊗ algebraMap (X ⟨u, hu⟩) (via L1ForwardGen_of_U),
  -- and L1UnitRightHom (X ⟨u, hu⟩) = 1 ⊗ algebraMap (X ⟨u, hu⟩) (via L1UnitRightHom_X).
  have huU : u.val ∈ U := u.property
  have hnW : u.val ∉ hhSurvivors G (U : Set _) := by
    intro hW
    apply hW
    exact Or.inl (by exact_mod_cast huU)
  rw [L1ForwardPoly_X, L1ForwardGen_of_U hnW huU]
  rw [L1UnitRightHom_X]

/-- `L1UnitRightHom` factors as `includeRight ∘ algebraMap`. -/
private theorem L1UnitRightHom_eq_includeRight_algebraMap {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (p : MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K) :
    L1UnitRightHom (K := K) G U p =
      (Algebra.TensorProduct.includeRight
          (R := K)
          (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
          (B := Localization.Away (hhUnitProductSub (K := K) U)))
        (algebraMap
          (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
          (Localization.Away (hhUnitProductSub (K := K) U)) p) := by
  unfold L1UnitRightHom
  rfl

/-- Each U-variable `X u`, after forward L1, maps to a unit in the target. -/
private theorem L1ForwardPoly_X_U_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    {u : BinomialEdgeVars (Fin n)} (huU : u ∈ U) :
    IsUnit (L1ForwardPoly (K := K) G U (X u)) := by
  classical
  rw [L1ForwardPoly_X]
  have hnW : u ∉ hhSurvivors G (U : Set _) := by
    intro hW; apply hW; exact Or.inl (by exact_mod_cast huU)
  rw [L1ForwardGen_of_U hnW huU]
  -- algebraMap (X ⟨u, _⟩) divides hhUnitProductSub U, which is a unit.
  set uSub : (U : Set (BinomialEdgeVars (Fin n))) :=
    ⟨u, by exact_mod_cast huU⟩ with huSub_def
  have hprod_unit : IsUnit
      (algebraMap
        (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
        (Localization.Away (hhUnitProductSub (K := K) U))
        (hhUnitProductSub (K := K) U)) :=
    IsLocalization.Away.algebraMap_isUnit (hhUnitProductSub (K := K) U)
  have hmem : (⟨u, huU⟩ : {v // v ∈ U}) ∈ U.attach := Finset.mem_attach _ _
  -- Factor hhUnitProductSub U = X uSub * (∏ u' ∈ erase).
  have hsplit :
      (X (R := K) uSub :
        MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K) *
      (∏ u' ∈ U.attach.erase ⟨u, huU⟩,
        X (R := K) (⟨u'.val, by exact_mod_cast u'.property⟩ :
          (U : Set (BinomialEdgeVars (Fin n))))) =
      hhUnitProductSub (K := K) U := by
    unfold hhUnitProductSub
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]
  have hXunit : IsUnit
      ((algebraMap (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
          (Localization.Away (hhUnitProductSub (K := K) U)))
        (X (R := K) uSub)) := by
    apply isUnit_of_mul_isUnit_left (y := (algebraMap _
      (Localization.Away (hhUnitProductSub (K := K) U)))
      (∏ u' ∈ U.attach.erase ⟨u, huU⟩,
        X (R := K) (⟨u'.val, by exact_mod_cast u'.property⟩ :
          (U : Set (BinomialEdgeVars (Fin n))))))
    rw [← map_mul, hsplit]
    exact hprod_unit
  -- Now transport through includeRight.
  have hright : IsUnit
      ((Algebra.TensorProduct.includeRight
          (R := K)
          (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
          (B := Localization.Away (hhUnitProductSub (K := K) U))).toRingHom
      ((algebraMap _ (Localization.Away (hhUnitProductSub (K := K) U)))
        (X (R := K) uSub))) :=
    RingHom.isUnit_map _ hXunit
  exact hright

/-- The image of `s_U` in the target is a unit. We prove this by computing the
image as a product over `U` of factors of the form `1 ⊗ algebraMap (X u')`, each
of which is a unit. -/
private theorem L1ForwardPoly_hhUnitProduct_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    IsUnit (L1ForwardPoly (K := K) G U (hhUnitProduct U)) := by
  classical
  unfold hhUnitProduct
  rw [_root_.map_prod]
  -- Each factor L1ForwardPoly (X u) is a unit for u ∈ U. Iterate.
  have h : ∀ (s : Finset (BinomialEdgeVars (Fin n))) (_hs : s ⊆ U),
      IsUnit (∏ u ∈ s, L1ForwardPoly (K := K) G U (X u)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact isUnit_one
    | @insert a s hnotin ih =>
      rw [Finset.prod_insert hnotin]
      refine (L1ForwardPoly_X_U_isUnit G U (hs (Finset.mem_insert_self _ _))).mul ?_
      exact ih (fun x hxs => hs (Finset.mem_insert_of_mem hxs))
  exact h U (Finset.Subset.refl _)

/-- The image of `mkI s_U` in the target is a unit. -/
private theorem L1ForwardQuot_mkI_hhUnitProduct_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    IsUnit (L1ForwardQuot (K := K) G U hU
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U))) := by
  rw [L1ForwardQuot_mk]
  exact L1ForwardPoly_hhUnitProduct_isUnit (K := K) G U

/-- The L1 forward hom from `Localization.Away (mkI s_U)` into the target. -/
noncomputable def L1Forward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    Localization.Away
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U))
      →ₐ[K] L1Target (K := K) G U := by
  refine IsLocalization.liftAlgHom
    (M := Submonoid.powers
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U)))
    (f := L1ForwardQuot (K := K) G U hU)
    (S := Localization.Away
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U))) ?_
  rintro ⟨y, k, rfl⟩
  rw [map_pow]
  exact (L1ForwardQuot_mkI_hhUnitProduct_isUnit (K := K) G U hU).pow k

/-! ##### Backward hom: target → Localization.Away (mkI s_U) -/

/-- Abbreviation for `Localization.Away (mkI s_U)` as a `K`-algebra. -/
private abbrev L1Source {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (BinomialEdgeVars (Fin n))) : Type _ :=
  Localization.Away
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (hhUnitProduct U))

/-- The backward map on the restricted polynomial ring: `X ⟨v, _⟩ ↦ mkI (X v) / 1`. -/
private noncomputable def L1BackwardLeftPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    polyRestrict (K := K) (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Source (K := K) G U :=
  MvPolynomial.aeval fun v =>
    (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val))

@[simp]
private theorem L1BackwardLeftPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : hhSurvivors G (U : Set _)) :
    L1BackwardLeftPoly (K := K) G U (X v) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) := by
  unfold L1BackwardLeftPoly
  simp [MvPolynomial.aeval_X]

/-- `L1BackwardLeftPoly` kills the restricted edge ideal. -/
private theorem L1BackwardLeftPoly_vanishes {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (x : polyRestrict (K := K) (hhSurvivors G (U : Set _))) :
    x ∈ restrictedEdgeIdeal (K := K) G (hhSurvivors G (U : Set _)) →
      L1BackwardLeftPoly (K := K) G U x = 0 := by
  intro hx
  classical
  unfold restrictedEdgeIdeal MvPolynomial.variablePairIdeal at hx
  refine Submodule.span_induction (p := fun y _ =>
    L1BackwardLeftPoly (K := K) G U y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨p, q, hpq, rfl⟩
    -- hpq : (p.val, q.val) ∈ hhEdgeSet G. Then X p.val * X q.val ∈ I.
    have hedge : (p.val, q.val) ∈ hhEdgeSet G := hpq
    have hpoly : (X p.val * X q.val :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ∈
          bipartiteEdgeMonomialIdeal (K := K) G := by
      rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
      exact Ideal.subset_span ⟨p.val, q.val, hedge, rfl⟩
    rw [map_mul, L1BackwardLeftPoly_X, L1BackwardLeftPoly_X]
    rw [← map_mul, ← map_mul,
      (Ideal.Quotient.eq_zero_iff_mem).mpr hpoly, map_zero]
  · simp
  · intros _ _ _ _ hx hy; simp [hx, hy]
  · intros r x _ hx; simp [hx]

/-- Descent to `restrictedHHRing G W → L1Source`. -/
private noncomputable def L1BackwardLeft {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Source (K := K) G U :=
  Ideal.Quotient.liftₐ (restrictedEdgeIdeal (K := K) G (hhSurvivors G (U : Set _)))
    (L1BackwardLeftPoly (K := K) G U) (L1BackwardLeftPoly_vanishes G U)

/-- The backward map on the unit-subring polynomial `K[U]`: `X⟨u, hu⟩ ↦ mkI(X u) / 1`. -/
private noncomputable def L1BackwardRightPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K →ₐ[K]
      L1Source (K := K) G U :=
  MvPolynomial.aeval fun v =>
    (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val))

@[simp]
private theorem L1BackwardRightPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : (U : Set (BinomialEdgeVars (Fin n)))) :
    L1BackwardRightPoly (K := K) G U (X v) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) := by
  unfold L1BackwardRightPoly
  simp [MvPolynomial.aeval_X]

/-- The image of `hhUnitProductSub U` under `L1BackwardRightPoly` is the image of
`mkI s_U` in the source localisation, hence a unit. -/
private theorem L1BackwardRightPoly_hhUnitProductSub_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    IsUnit (L1BackwardRightPoly (K := K) G U (hhUnitProductSub (K := K) U)) := by
  classical
  -- Strategy: build three products over U.attach that coincide and glue them.
  -- Step 1: rewrite LHS via `L1BackwardRightPoly` `map_prod` and pointwise `_X`.
  have hLHS : L1BackwardRightPoly (K := K) G U (hhUnitProductSub (K := K) U) =
      ∏ u ∈ U.attach,
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)) (X u.val)) := by
    unfold hhUnitProductSub
    rw [_root_.map_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [L1BackwardRightPoly_X]
  -- Step 2: rewrite RHS `algebraMap (mk (∏ u ∈ U, X u))` via composition of the
  -- quotient ring hom and the algebraMap and two `map_prod` expansions.
  have hRHS : (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U)) =
      ∏ u ∈ U.attach,
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)) (X u.val)) := by
    -- First, `(algebraMap _ _ ∘ mk)` is a ring hom f : MvPoly σ K → L1Source.
    -- f(hhUnitProduct U) = f(∏ u ∈ U, X u) = ∏ u ∈ U, f(X u) = ∏ u ∈ U.attach, f(X u.val).
    have hfmap : ((algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U)).comp
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) :
          MvPolynomial _ K →+* _))) (hhUnitProduct U) =
        ∏ u ∈ U, ((algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U)).comp
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) :
          MvPolynomial _ K →+* _))) (X (R := K) u) := by
      unfold hhUnitProduct
      rw [_root_.map_prod]
    -- Simplify LHS-expression and apply Finset.prod_attach.
    simp only [RingHom.coe_comp, Function.comp_apply] at hfmap
    rw [hfmap]
    exact (Finset.prod_attach U (f := fun u =>
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)) (X u)))).symm
  rw [hLHS, ← hRHS]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Descent to `Localization.Away (hhUnitProductSub U) → L1Source`. -/
private noncomputable def L1BackwardRight {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    Localization.Away (hhUnitProductSub (K := K) U) →ₐ[K]
      L1Source (K := K) G U := by
  refine IsLocalization.liftAlgHom
    (M := Submonoid.powers (hhUnitProductSub (K := K) U))
    (f := L1BackwardRightPoly (K := K) G U)
    (S := Localization.Away (hhUnitProductSub (K := K) U)) ?_
  rintro ⟨y, k, rfl⟩
  rw [map_pow]
  exact (L1BackwardRightPoly_hhUnitProductSub_isUnit (K := K) G U).pow k

/-- The L1 backward hom: assembled via `Algebra.TensorProduct.lift`. -/
private noncomputable def L1Backward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    L1Target (K := K) G U →ₐ[K] L1Source (K := K) G U :=
  Algebra.TensorProduct.lift
    (L1BackwardLeft (K := K) G U) (L1BackwardRight (K := K) G U)
    (fun _ _ => mul_comm _ _)

/-! ##### Compositions are identity -/

/-- Forward then Backward on `algebraMap` of `mk X v` (with `v` a W-variable). -/
private theorem L1Backward_Forward_algebraMap_mk_X_of_W {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) {v : BinomialEdgeVars (Fin n)}
    (hW : v ∈ hhSurvivors G (U : Set _)) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W hW]
  -- Now L1Backward on (mk X⟨v, hW⟩) ⊗ 1 = L1BackwardLeft (mk X⟨v, hW⟩).
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  -- L1BackwardLeft (mk (X ⟨v, hW⟩)) = L1BackwardLeftPoly (X ⟨v, hW⟩).
  unfold L1BackwardLeft
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact L1BackwardLeftPoly_X G U ⟨v, hW⟩

/-- Forward then Backward on `algebraMap` of `mk X v` (with `v` a U-variable). -/
private theorem L1Backward_Forward_algebraMap_mk_X_of_U {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hvU : v ∈ U) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_U hnW hvU]
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  -- L1BackwardRight (algebraMap X ⟨v, hvU⟩) = L1BackwardRightPoly (X ⟨v, hvU⟩).
  unfold L1BackwardRight
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  exact L1BackwardRightPoly_X G U ⟨v, by exact_mod_cast hvU⟩

/-- Forward then Backward on `algebraMap` of `mk X v` (with `v` a N(U)-variable). -/
private theorem L1Backward_Forward_algebraMap_mk_X_of_N {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hnU : v ∉ U) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  -- v ∈ N(U): there is some u ∈ U with (u, v) ∈ hhEdgeSet G or (v, u) ∈ hhEdgeSet G.
  -- Then mkI(X u * X v) = 0, and mkI(X u) is a unit, so mkI(X v) = 0 in source.
  have hv_N : v ∈ hhNbhd G (U : Set _) := by
    -- v ∉ hhSurvivors means v ∈ U ∪ N(U). v ∉ U gives v ∈ N(U).
    by_contra hvN
    apply hnW
    intro h
    rcases h with hvU' | hvN'
    · exact hnU (by exact_mod_cast hvU')
    · exact hvN hvN'
  obtain ⟨u, huU, huadj⟩ := hv_N
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_N hnW hnU]
  rw [map_zero]
  -- Prove RHS = 0.
  -- There exists u ∈ U s.t. (u, v) or (v, u) in hhEdgeSet G. In both cases X u * X v ∈ I.
  have hpoly_zero : (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u) *
        Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) = 0 := by
    have hprod_mem : (X u * X v :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ∈
          bipartiteEdgeMonomialIdeal (K := K) G := by
      rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
      rcases huadj with h1 | h2
      · exact Ideal.subset_span ⟨u, v, h1, rfl⟩
      · -- (v, u) ∈ hhEdgeSet. Then X v * X u ∈ I, and X u * X v = X v * X u.
        have : (X v * X u : MvPolynomial (BinomialEdgeVars (Fin n)) K) ∈
            MvPolynomial.variablePairIdeal (R := K) (hhEdgeSet G) :=
          Ideal.subset_span ⟨v, u, h2, rfl⟩
        rw [mul_comm]; exact this
    have : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u * X v) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hprod_mem
    rw [map_mul] at this
    rw [this, map_zero]
  -- mkI (X u) is a unit in source, because it divides the unit `algebraMap (mkI s_U)`.
  have hu_unit : IsUnit ((algebraMap
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G)
      (L1Source (K := K) G U))
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u))) := by
    -- Use isUnit_of_mul_isUnit_left: if `x * y` is a unit, so is `x`.
    -- Take `y = algebraMap(mkI (∏_{w ∈ U \ {u}} X w))` so that
    -- `x * y = algebraMap(mkI s_U)` is a unit by construction.
    apply isUnit_of_mul_isUnit_left (y :=
      (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (∏ w ∈ U.erase u, X (R := K) w)))
    -- The product equals `algebraMap (mkI s_U)`, which is a unit.
    have hprod_eq :
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u)) *
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (∏ w ∈ U.erase u, X (R := K) w)) =
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U)) := by
      rw [← map_mul, ← map_mul]
      congr 1
      -- X u * ∏ w ∈ U.erase u, X w = ∏ v ∈ U, X v.
      unfold hhUnitProduct
      rw [mul_comm, Finset.prod_erase_mul _ _ huU]
    rw [hprod_eq]
    exact IsLocalization.Away.algebraMap_isUnit _
  -- From mkI(X u) * mkI(X v) = 0 in source and mkI(X u) unit, conclude mkI(X v) = 0.
  have : (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) = 0 := by
    have h_mul := hpoly_zero
    rw [map_mul] at h_mul
    exact (hu_unit.mul_right_eq_zero).mp h_mul
  rw [this]

/-- Backward ∘ Forward on the quotient level: on `mk X v` it equals
`algebraMap (mk X v)`. -/
private theorem L1Backward_Forward_quot_mk_X {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) (v : BinomialEdgeVars (Fin n)) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  classical
  by_cases hW : v ∈ hhSurvivors G (U : Set _)
  · exact L1Backward_Forward_algebraMap_mk_X_of_W hU hW
  · by_cases hvU : v ∈ U
    · exact L1Backward_Forward_algebraMap_mk_X_of_U hU hW hvU
    · exact L1Backward_Forward_algebraMap_mk_X_of_N hU hW hvU

/-- Backward ∘ Forward on the quotient level, stated as an algHom equality at the
`MvPolynomial` level. -/
private theorem L1Backward_Forward_quot_algHom {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    ((L1Backward (K := K) G U).comp
        (L1ForwardQuot (K := K) G U hU)).comp
      (Ideal.Quotient.mkₐ K (bipartiteEdgeMonomialIdeal (K := K) G)) =
    ((IsScalarTower.toAlgHom K
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))).comp
      (Ideal.Quotient.mkₐ K (bipartiteEdgeMonomialIdeal (K := K) G)) := by
  apply MvPolynomial.algHom_ext
  intro v
  change (L1Backward (K := K) G U) (L1ForwardQuot (K := K) G U hU
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
    (algebraMap _ (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))
  exact L1Backward_Forward_quot_mk_X hU v

/-- Backward ∘ Forward = id (Localization level). -/
private theorem L1Backward_Forward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    (L1Backward (K := K) G U).comp (L1Forward (K := K) G U hU) =
      AlgHom.id K (L1Source (K := K) G U) := by
  apply
    IsLocalization.algHom_ext (W := Submonoid.powers
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U)))
  -- Reduce to equality on algebraMap from R.
  have hBF : ((L1Backward (K := K) G U).comp
        (L1Forward (K := K) G U hU)).comp
      (IsScalarTower.toAlgHom K
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U)) =
      IsScalarTower.toAlgHom K _ (L1Source (K := K) G U) := by
    -- First: L1Forward ∘ algebraMap_R = L1ForwardQuot (by the `liftAlgHom` property).
    have hLF : (L1Forward (K := K) G U hU).comp
        (IsScalarTower.toAlgHom K
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U)) =
        L1ForwardQuot (K := K) G U hU := by
      apply AlgHom.ext
      intro x
      change L1Forward (K := K) G U hU
          (algebraMap _ (L1Source (K := K) G U) x) = L1ForwardQuot _ _ _ x
      unfold L1Forward
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      rfl
    -- Now combine: (Bwd ∘ Fwd) ∘ algebraMap = Bwd ∘ (Fwd ∘ algebraMap) = Bwd ∘ ForwardQuot,
    -- and we want it to equal algebraMap. Use algHom_ext on the quotient.
    rw [AlgHom.comp_assoc, hLF]
    -- Now goal: L1Backward ∘ L1ForwardQuot = algebraMap (as K-alg homs from R).
    apply Ideal.Quotient.algHom_ext
    -- Goal: (Bwd ∘ ForwardQuot) ∘ mkₐ = algebraMap ∘ mkₐ
    exact L1Backward_Forward_quot_algHom G U hU
  apply AlgHom.ext
  intro x
  change (L1Backward (K := K) G U) (L1Forward (K := K) G U hU
    ((algebraMap _ (L1Source (K := K) G U)) x)) =
      (AlgHom.id K _) ((algebraMap _ (L1Source (K := K) G U)) x)
  exact congrArg (fun φ : _ →ₐ[K] L1Source (K := K) G U => φ x) hBF

/-- Forward ∘ Backward on `(mk X⟨v, hW⟩) ⊗ 1` (left pure tensor, W case). -/
private theorem L1Forward_Backward_tmul_left_X {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) (v : hhSurvivors G (U : Set _)) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _))) (X v) :
              restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X v) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1 := by
  classical
  -- L1Backward on (mk X v) ⊗ 1 = L1BackwardLeft (mk X v).
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  unfold L1BackwardLeft
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change L1Forward (K := K) G U hU (L1BackwardLeftPoly (K := K) G U (X v)) = _
  rw [L1BackwardLeftPoly_X]
  -- L1Forward (algebraMap (mk X v.val)) = L1ForwardQuot (mk X v.val).
  unfold L1Forward
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change L1ForwardQuot (K := K) G U hU
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) = _
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W v.property]

/-- Forward ∘ Backward on `1 ⊗ algebraMap (X ⟨u, hu⟩)` (right pure tensor, U case). -/
private theorem L1Forward_Backward_tmul_right_X {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) (v : (U : Set (BinomialEdgeVars (Fin n)))) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
            (algebraMap
                (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
                (Localization.Away (hhUnitProductSub (K := K) U))
              (X v)))) =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X v)) := by
  classical
  -- L1Backward on 1 ⊗ (algebraMap X v) = L1BackwardRight (algebraMap X v).
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  unfold L1BackwardRight
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change L1Forward (K := K) G U hU (L1BackwardRightPoly (K := K) G U (X v)) = _
  rw [L1BackwardRightPoly_X]
  -- L1Forward (algebraMap (mk X v.val)) = L1ForwardQuot (mk X v.val).
  unfold L1Forward
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change L1ForwardQuot (K := K) G U hU
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) = _
  rw [L1ForwardQuot_mk, L1ForwardPoly_X]
  -- v ∈ U, v ∉ W (because U ⊆ Wᶜ).
  have hvU : v.val ∈ U := by exact_mod_cast v.property
  have hvU_set : v.val ∈ (U : Set (BinomialEdgeVars (Fin n))) := by
    exact_mod_cast hvU
  have hvnW : v.val ∉ hhSurvivors G (U : Set _) := by
    intro h
    exact h (Or.inl hvU_set)
  rw [L1ForwardGen_of_U hvnW hvU]

-- The `set φL, set φR` pattern plus MvPolynomial/Ideal.Quotient extensionality.
set_option maxHeartbeats 1300000 in
-- heartbeats needed: target type `L1Target` is a heavy tensor product of a quotient
-- and a localization; algHom extensionality on pure tensors is expensive.
/-- Forward ∘ Backward on left pure tensors (algHom equality): reduce to generators
via quotient + polynomial extensionality. -/
private theorem L1Forward_Backward_left {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U (a ⊗ₜ[K] 1)) = a ⊗ₜ[K] 1 := by
  classical
  set φL : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Target (K := K) G U :=
    ((L1Forward (K := K) G U hU).comp (L1Backward (K := K) G U)).comp
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
        (B := Localization.Away (hhUnitProductSub (K := K) U)))
  set φR : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Target (K := K) G U :=
    Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
      (B := Localization.Away (hhUnitProductSub (K := K) U))
  have hφ : φL = φR := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro v
    change L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _))) (X v) :
              restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X v) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1
    exact L1Forward_Backward_tmul_left_X hU v
  have := congrArg (fun φ => φ a) hφ
  exact this

set_option maxHeartbeats 1100000 in
-- heartbeats needed: heavy tensor-product extensionality; see L1Forward_Backward_left.
/-- Forward ∘ Backward on right pure tensors (algHom equality). -/
private theorem L1Forward_Backward_right {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (b : Localization.Away (hhUnitProductSub (K := K) U)) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U (1 ⊗ₜ[K] b)) = 1 ⊗ₜ[K] b := by
  classical
  set φL : Localization.Away (hhUnitProductSub (K := K) U) →ₐ[K]
      L1Target (K := K) G U :=
    ((L1Forward (K := K) G U hU).comp (L1Backward (K := K) G U)).comp
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
        (B := Localization.Away (hhUnitProductSub (K := K) U)))
  set φR : Localization.Away (hhUnitProductSub (K := K) U) →ₐ[K]
      L1Target (K := K) G U :=
    Algebra.TensorProduct.includeRight
      (R := K)
      (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
      (B := Localization.Away (hhUnitProductSub (K := K) U))
  have hφ : φL = φR := by
    refine IsLocalization.algHom_ext
      (W := Submonoid.powers (hhUnitProductSub (K := K) U)) ?_
    apply MvPolynomial.algHom_ext
    intro v
    change L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
            (algebraMap _
              (Localization.Away (hhUnitProductSub (K := K) U)) (X v)))) =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap _
          (Localization.Away (hhUnitProductSub (K := K) U)) (X v))
    exact L1Forward_Backward_tmul_right_X hU v
  have := congrArg (fun φ => φ b) hφ
  exact this

/-- Forward ∘ Backward = id. -/
private theorem L1Forward_Backward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    (L1Forward (K := K) G U hU).comp (L1Backward (K := K) G U) =
      AlgHom.id K (L1Target (K := K) G U) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  -- Factor a ⊗ b = (a ⊗ 1) * (1 ⊗ b).
  have hsplit : a ⊗ₜ[K] b =
      ((a ⊗ₜ[K] (1 : Localization.Away (hhUnitProductSub (K := K) U))) *
        ((1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] b)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change (L1Forward (K := K) G U hU) ((L1Backward (K := K) G U) (a ⊗ₜ[K] b)) =
    a ⊗ₜ[K] b
  rw [hsplit, map_mul, map_mul, L1Forward_Backward_left G U hU a,
    L1Forward_Backward_right G U hU b]

/-- **The L1 iso.** Monomial-localisation of the HH quotient at the independent
unit product `s_U` decomposes as a tensor of the restricted HH ring on `W` with
the Laurent polynomial ring on `U`:

  `R[s_U⁻¹] ≃ₐ[K] (restrictedHHRing G W) ⊗[K] Localization.Away s_U^U`. -/
noncomputable def L1Iso {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    Localization.Away
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U))
      ≃ₐ[K]
      TensorProduct K
        (restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
        (Localization.Away (hhUnitProductSub (K := K) U)) :=
  AlgEquiv.ofAlgHom (L1Forward (K := K) G U hU) (L1Backward (K := K) G U)
    (L1Forward_Backward G U hU) (L1Backward_Forward G U hU)


end

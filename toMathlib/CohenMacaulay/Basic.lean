/-
This file contains basic theorems about Cohen-Macaulay rings, adapted from
mathlib PR #26218, backported to the v4.28.0 environment used by BEI-lean.

The main result is the converse regular-quotient CM transfer:

  If `x ∈ maximalIdeal R` is `R`-regular and `R ⧸ (x)` is Cohen-Macaulay local,
  then `R` is Cohen-Macaulay local.

The long-term goal is to delete this local copy once the relevant CM infrastructure
is available upstream in Mathlib.
-/

import toMathlib.CohenMacaulay.Defs

/-!
# Cohen-Macaulay Rings — Basic Theorems

## Main results

- `quotSMulTopLocalRing`: the quotient `R ⧸ (x)` of a local ring by an element
  of the maximal ideal is again local.

- `ringDepth_quotSMulTop_succ_le`: if `x ∈ maximalIdeal R` is `R`-regular, then
  `ringDepth (R ⧸ (x)) + 1 ≤ ringDepth R` (the "easy" depth inequality).

- `isCohenMacaulayLocalRing_of_regular_quotient`: if `x ∈ maximalIdeal R` is
  `R`-regular and `R ⧸ (x)` is Cohen-Macaulay local, then `R` is Cohen-Macaulay
  local.

## Implementation notes

The forward direction (CM `R` and `x` regular implies CM `R/(x)`) requires the
full depth additivity theorem `depth(R/(x)) = depth(R) - 1`, which in turn
relies on the Rees theorem (all maximal regular sequences have the same length).
That infrastructure is not yet available and is recorded as the next blocker.
-/

noncomputable section

open IsLocalRing RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-! ### Quotient instances -/

/-- An element of the maximal ideal lies in the Jacobson radical of the
annihilator of `R` as a module over itself. -/
private lemma mem_annihilator_jacobson_of_mem_maximalIdeal {x : R}
    (hx : x ∈ maximalIdeal R) : x ∈ (Module.annihilator R R).jacobson := by
  have h0 : Module.annihilator R R = ⊥ := by
    ext r; simp only [Module.mem_annihilator, Submodule.mem_bot]
    exact ⟨fun h => by simpa using h 1, fun h => by subst h; simp⟩
  rw [h0, Ideal.mem_jacobson_bot]; intro y
  rw [show x * y + 1 = 1 - -(x * y) from by ring]
  exact isUnit_one_sub_self_of_mem_nonunits _
    ((mem_maximalIdeal _).mp (neg_mem ((maximalIdeal R).mul_mem_right y hx)))

/-- The quotient `R ⧸ xR` is nontrivial when `x` is in the maximal ideal. -/
lemma quotSMulTop_nontrivial {x : R} (hx : x ∈ maximalIdeal R) :
    Nontrivial (QuotSMulTop x R) :=
  (Submodule.Quotient.nontrivial_iff).mpr
    (Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator
      (mem_annihilator_jacobson_of_mem_maximalIdeal hx)).symm

/-- The quotient `R ⧸ xR` of a local ring by an element of the maximal ideal is
again a local ring. -/
lemma quotSMulTopLocalRing {x : R} (hx : x ∈ maximalIdeal R) :
    IsLocalRing (QuotSMulTop x R) :=
  haveI := quotSMulTop_nontrivial hx
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-! ### Depth lifting inequality -/

/-- Given a weakly regular sequence `ss` in `R ⧸ xR` (using the self-module
structure) with all elements in the maximal ideal, together with `x` regular in
the maximal ideal of `R`, the lifted sequence `x :: rs` is weakly regular in `R`
of length `|ss| + 1`. -/
private lemma ringDepth_le_of_lifted_cons {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R)
    {ss : List (QuotSMulTop x R)}
    (hreg_ss : IsWeaklyRegular (QuotSMulTop x R) ss)
    (hmem_ss : ∀ s ∈ ss,
      s ∈ @maximalIdeal (QuotSMulTop x R) _ (quotSMulTopLocalRing hx)) :
    (ss.length + 1 : ℕ∞) ≤ ringDepth R := by
  -- Lift ss to rs : List R via a section of the quotient map
  set lift := Function.surjInv
    (show Function.Surjective (algebraMap R (QuotSMulTop x R)) from
      Ideal.Quotient.mk_surjective) with lift_def
  set rs := ss.map lift with rs_def
  -- The lifted sequence maps back to ss
  have hmap : rs.map (algebraMap R (QuotSMulTop x R)) = ss := by
    simp only [rs_def, List.map_map, Function.comp_def]
    conv_rhs => rw [← List.map_id ss]
    congr 1; ext s
    exact Function.surjInv_eq Ideal.Quotient.mk_surjective s
  -- Regularity: ss weakly regular (self-module) → rs weakly regular (R-module)
  have hreg_rs : IsWeaklyRegular (QuotSMulTop x R) rs := by
    rw [← @isWeaklyRegular_map_algebraMap_iff R
      (QuotSMulTop x R) (QuotSMulTop x R) _ _ _ _ _ _ _ rs, hmap]
    exact hreg_ss
  -- x :: rs is weakly regular in R
  have hreg' : IsWeaklyRegular R (x :: rs) :=
    (isWeaklyRegular_cons_iff R x rs).mpr ⟨reg, hreg_rs⟩
  -- Maximal ideal membership for lifts
  have hmem_rs : ∀ r ∈ rs, r ∈ maximalIdeal R := by
    intro r hr
    rw [mem_maximalIdeal]
    intro hu
    obtain ⟨s, hs_mem, rfl⟩ := List.mem_map.mp hr
    have himage : algebraMap R (QuotSMulTop x R) (lift s) =
        s := Function.surjInv_eq Ideal.Quotient.mk_surjective s
    have hmem := hmem_ss s hs_mem
    rw [← himage] at hmem
    exact (@mem_maximalIdeal (QuotSMulTop x R) _
      (quotSMulTopLocalRing hx) _).mp hmem
      (hu.map (algebraMap R (QuotSMulTop x R)))
  -- All elements of x :: rs are in maximalIdeal R
  have hmem' : ∀ r ∈ (x :: rs), r ∈ maximalIdeal R := by
    simp only [List.mem_cons]
    rintro r (rfl | h)
    · exact hx
    · exact hmem_rs r h
  -- Use the existing depth lower bound
  have hlen : ((x :: rs).length : ℕ∞) ≤ ringDepth R :=
    ringDepth_le_of_isWeaklyRegular R hreg' hmem'
  simpa [rs_def] using hlen

/-- **Depth lifting inequality**: if `x ∈ maximalIdeal R` is `R`-regular, then
`depth(R ⧸ xR) + 1 ≤ depth(R)`.

This is the "easy" direction of the depth additivity formula. The proof lifts
each weakly regular sequence in `R ⧸ xR` (via a section of the quotient map)
and prepends `x` to obtain a longer weakly regular sequence in `R`. -/
theorem ringDepth_quotSMulTop_succ_le {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R) :
    @ringDepth (QuotSMulTop x R) _ (quotSMulTopLocalRing hx) + 1 ≤
      ringDepth R := by
  haveI := quotSMulTopLocalRing hx
  -- The depth set for the quotient is nonempty (empty sequence)
  have hne : {n : ℕ∞ | ∃ rs : List (QuotSMulTop x R),
      (rs.length : ℕ∞) = n ∧ IsWeaklyRegular (QuotSMulTop x R) rs ∧
      ∀ r ∈ rs, r ∈ maximalIdeal (QuotSMulTop x R)}.Nonempty :=
    ⟨0, [], rfl, IsWeaklyRegular.nil _ _, fun _ h => nomatch h⟩
  -- ringDepth unfolds to sSup of this set
  change sSup _ + 1 ≤ ringDepth R
  rw [ENat.sSup_add hne]
  apply iSup₂_le
  intro n ⟨ss, hlen, hreg_ss, hmem_ss⟩
  rw [← hlen]
  exact ringDepth_le_of_lifted_cons reg hx hreg_ss hmem_ss

/-! ### Converse CM transfer -/

variable [IsNoetherianRing R]

/-- **Converse regular-quotient CM transfer**: if `x ∈ maximalIdeal R` is
`R`-regular and `R ⧸ xR` is Cohen-Macaulay local, then `R` is Cohen-Macaulay
local.

The proof combines:
1. `ringDepth_quotSMulTop_succ_le`: `depth(R/xR) + 1 ≤ depth(R)`
2. CM of `R/xR`: `depth(R/xR) = dim(R/xR)`
3. `ringKrullDim_quotSMulTop_succ_eq_ringKrullDim`: `dim(R/xR) + 1 = dim(R)` -/
theorem isCohenMacaulayLocalRing_of_regular_quotient {x : R}
    (reg : IsSMulRegular R x) (hx : x ∈ maximalIdeal R)
    (hCM_depth : @ringKrullDim (QuotSMulTop x R) _ =
      ↑(@ringDepth (QuotSMulTop x R) _ (quotSMulTopLocalRing hx))) :
    IsCohenMacaulayLocalRing R where
  depth_eq_dim := by
    haveI := quotSMulTopLocalRing hx
    -- dim(R/xR) + 1 = dim(R)
    have hdim := ringKrullDim_quotSMulTop_succ_eq_ringKrullDim reg hx
    -- depth(R/xR) + 1 ≤ depth(R) in ℕ∞
    have hdepth_ineq := ringDepth_quotSMulTop_succ_le reg hx
    -- depth(R) ≤ dim(R) in WithBot ℕ∞
    have hdepth_le := ringDepth_le_ringKrullDim R
    apply le_antisymm
    · -- ringKrullDim R ≤ ↑(ringDepth R)
      calc ringKrullDim R
          = ringKrullDim (QuotSMulTop x R) + 1 := hdim.symm
        _ = ↑(ringDepth (QuotSMulTop x R)) + 1 := by rw [hCM_depth]
        _ ≤ ↑(ringDepth R) := by exact_mod_cast hdepth_ineq
    · -- ↑(ringDepth R) ≤ ringKrullDim R
      exact hdepth_le

/-- **CM from regular sequence of maximal length**: if there exists a weakly regular
sequence in the maximal ideal whose length equals the Krull dimension, then `R`
is Cohen-Macaulay local.

Proof: `length ≤ depth` (from `ringDepth_le_of_isWeaklyRegular`) and
`depth ≤ dim` (from `ringDepth_le_ringKrullDim`), so `length = dim` forces
`depth = dim`. -/
theorem isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim {rs : List R}
    (hreg : IsWeaklyRegular R rs) (hmem : ∀ r ∈ rs, r ∈ maximalIdeal R)
    (hdim : ringKrullDim R = (rs.length : ℕ∞)) :
    IsCohenMacaulayLocalRing R where
  depth_eq_dim := by
    have h_depth_lb : (rs.length : ℕ∞) ≤ ringDepth R :=
      ringDepth_le_of_isWeaklyRegular R hreg hmem
    have h_depth_ub : (ringDepth R : WithBot ℕ∞) ≤ ringKrullDim R :=
      ringDepth_le_ringKrullDim R
    apply le_antisymm
    · -- ringKrullDim R ≤ ↑(ringDepth R)
      rw [hdim]
      exact_mod_cast h_depth_lb
    · exact h_depth_ub

/-- A Noetherian local ring of Krull dimension zero is Cohen-Macaulay.

Every element of the maximal ideal is a zero-divisor (since the ring is
Artinian-like at dimension zero), so `depth = 0 = dim`. -/
theorem isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
    (hdim : ringKrullDim R = 0) :
    IsCohenMacaulayLocalRing R where
  depth_eq_dim := by
    have h_depth_ub : (ringDepth R : WithBot ℕ∞) ≤ ringKrullDim R :=
      ringDepth_le_ringKrullDim R
    rw [hdim] at h_depth_ub
    have h0 : ringDepth R = 0 :=
      nonpos_iff_eq_zero.mp (by exact_mod_cast h_depth_ub)
    rw [hdim, h0]; rfl

end

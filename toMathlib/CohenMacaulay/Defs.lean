/-
This file contains the Cohen-Macaulay ring definition, adapted from mathlib PR #26218
(by Nailin Guan, Yongle Hu), backported to the v4.28.0 environment used by BEI-lean.

The upstream PR defines depth via Ext groups (derived category infrastructure). Since the
Ext-based depth is not yet available in Mathlib v4.28.0, we define depth via the classical
regular sequence characterization, which is equivalent for Noetherian local rings
(Rees theorem / Auslander-Buchsbaum).

The long-term goal is to delete this local copy once the relevant CM infrastructure
is available upstream in Mathlib.
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular

/-!
# Cohen-Macaulay Rings (working definition for BEI)

## Definitions

- `ringDepth`: The depth of a local ring `R` (as a module over itself),
  defined as the supremum of lengths of `R`-regular sequences in the maximal ideal.

- `IsCohenMacaulayLocalRing`: A local ring is Cohen-Macaulay if
  `ringKrullDim R = ringDepth R`.

- `IsCohenMacaulayRing`: A commutative ring is Cohen-Macaulay if its
  localization at every prime ideal is `IsCohenMacaulayLocalRing`.

## Notes

The depth defined here via regular sequences coincides with the Ext-based definition
`inf { i | Ext^i(k, R) ≠ 0 }` for Noetherian local rings by the Rees theorem.
When the upstream Ext-based CM infrastructure (mathlib PR #26218) lands, these local
definitions should be replaced.
-/

noncomputable section

open IsLocalRing RingTheory.Sequence

variable (R : Type*) [CommRing R]

section Depth

variable [IsLocalRing R]

/-- The depth of a local ring `R`, defined as the supremum of lengths of
`R`-regular sequences contained in the maximal ideal.

For Noetherian local rings, this equals `inf { i | Ext^i(k, R) ≠ 0 }`
where `k` is the residue field (Rees theorem).

Adapted from mathlib PR #26218, where depth is defined via Ext groups. -/
noncomputable def ringDepth : ℕ∞ :=
  sSup {(n : ℕ∞) | ∃ (rs : List R),
    (rs.length : ℕ∞) = n ∧ IsWeaklyRegular R rs ∧ ∀ r ∈ rs, r ∈ maximalIdeal R}

lemma ringDepth_le_of_isWeaklyRegular {rs : List R}
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (rs.length : ℕ∞) ≤ ringDepth R :=
  le_sSup ⟨rs, rfl, reg, mem⟩

lemma zero_le_ringDepth : 0 ≤ ringDepth R :=
  le_sSup ⟨[], rfl, IsWeaklyRegular.nil R R, fun _ h => nomatch h⟩

end Depth

/-- A local ring `R` is **Cohen-Macaulay** if its Krull dimension equals its depth.

Adapted from mathlib PR #26218. The upstream definition uses Ext-based depth;
this local version uses the equivalent regular sequence depth. -/
class IsCohenMacaulayLocalRing extends IsLocalRing R where
  depth_eq_dim : ringKrullDim R = ringDepth R

/-- A commutative ring `R` is **Cohen-Macaulay** if its localization at every
prime ideal is `IsCohenMacaulayLocalRing`.

Adapted from mathlib PR #26218. -/
class IsCohenMacaulayRing : Prop where
  CM_localize : ∀ (p : Ideal R) [p.IsPrime],
    IsCohenMacaulayLocalRing (Localization.AtPrime p)

section Basic

variable [IsLocalRing R] [IsNoetherianRing R]

/-- In a Noetherian local ring, every weakly regular sequence in the maximal ideal
has length at most `ringKrullDim R`. -/
lemma weaklyRegular_length_le_ringKrullDim {rs : List R}
    (reg : IsWeaklyRegular R rs) (mem : ∀ r ∈ rs, r ∈ maximalIdeal R) :
    (rs.length : WithBot ℕ∞) ≤ ringKrullDim R := by
  have hreg : RingTheory.Sequence.IsRegular R rs :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal mem).mpr reg
  have heq := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  rw [← heq]
  have hne : ringKrullDim (R ⧸ Ideal.ofList rs) + ↑rs.length ≠ ⊥ := by
    rw [heq]; exact ringKrullDim_ne_bot
  have hne' : ringKrullDim (R ⧸ Ideal.ofList rs) ≠ ⊥ := by
    intro h; exact hne (by rw [h, WithBot.bot_add])
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne'
  rw [← hd]
  have : (↑d : WithBot ℕ∞) + ↑rs.length = ↑(d + ↑rs.length) := by norm_cast
  rw [this]
  exact_mod_cast (le_add_self : (↑rs.length : ℕ∞) ≤ d + ↑rs.length)

/-- In a Noetherian local ring, the depth is at most the Krull dimension. -/
lemma ringDepth_le_ringKrullDim : (ringDepth R : WithBot ℕ∞) ≤ ringKrullDim R := by
  have hne : ringKrullDim R ≠ ⊥ := ringKrullDim_ne_bot
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd, WithBot.coe_le_coe]
  exact sSup_le fun n ⟨rs, hlen, hreg, hmem⟩ => by
    have h := weaklyRegular_length_le_ringKrullDim R hreg hmem
    rw [← hd] at h
    exact hlen ▸ WithBot.coe_le_coe.mp h

end Basic

end

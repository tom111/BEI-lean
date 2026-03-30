/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BEI.Definitions
import BEI.PrimeIdeals
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Height of 2-minor ideals (determinantal ideals)

The ideal of 2×2 minors of a generic 2×m matrix has height m − 1. In the
language of binomial edge ideals, this is `height(J_{K_m}) = m − 1` where
K_m is the complete graph on m vertices.

## Main results

- `height_binomialEdgeIdeal_complete`: `height(J_{K_m}) = m − 1`

## Proof strategy

The ideal `J_{K_m}` is the kernel of the Segre-type map
  `φ : K[x₁,...,xₘ,y₁,...,yₘ] → K[t, u₁,...,uₘ]`
  `x_i ↦ t · u_i,  y_i ↦ u_i`

The image has Krull dimension m + 1 (it is a polynomial ring in m + 1
algebraically independent generators). Since the ambient ring has dimension 2m:
  `height(J_{K_m}) = 2m − (m + 1) = m − 1`

This uses the catenary property of polynomial rings:
  `height(P) + dim(R/P) = dim(R)`
which is NOT in Mathlib v4.28.0.

Alternatively, this is a special case of the **Eagon–Northcott theorem**:
the ideal of t-minors of a generic p × q matrix has height (p−t+1)(q−t+1).
For t = 2, p = 2, q = m: height = 1 · (m − 1) = m − 1.

## Mathlib prerequisites (available)
- `Ideal.height` (`Mathlib.RingTheory.Ideal.Height`)
- `MvPolynomial.ringKrullDim` (`Mathlib.RingTheory.KrullDimension.Polynomial`)
- `binomialEdgeIdeal` (`BEI.Definitions`)

## Mathlib gaps (blockers)
- Catenary property for polynomial rings
- Eagon–Northcott complex
- `height(P) + dim(R/P) = dim(R)` for `MvPolynomial`
-/

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial SimpleGraph

/-! ## Helpers for the height computation -/

/-- The complete graph on `Fin m` with `m ≥ 2` is connected. -/
private lemma complete_graph_connected (m : ℕ) (hm : 2 ≤ m) :
    (⊤ : SimpleGraph (Fin m)).Connected :=
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩; connected_top

/-- The binomial edge ideal of the complete graph is prime.
Uses `primeComponent_empty_connected` and `primeComponent_isPrime`. -/
private lemma binomialEdgeIdeal_complete_isPrime (m : ℕ) (hm : 2 ≤ m) :
    (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m))).IsPrime := by
  rw [← primeComponent_empty_connected (⊤ : SimpleGraph (Fin m)) (complete_graph_connected m hm)]
  exact primeComponent_isPrime (⊤ : SimpleGraph (Fin m)) ∅

/-- The column-0 minor `x_0 · y_{j+1} - x_{j+1} · y_0` as a polynomial. -/
private def col0Minor (m : ℕ) (j : Fin (m - 1)) :
    MvPolynomial (BinomialEdgeVars (Fin m)) K :=
  have hj := j.isLt
  x (⟨0, by omega⟩ : Fin m) * y (⟨j.val + 1, by omega⟩ : Fin m) -
  x (⟨j.val + 1, by omega⟩ : Fin m) * y (⟨0, by omega⟩ : Fin m)

/-- The set of column-0 minors `{x_0 y_j - x_j y_0 : j = 1,...,m-1}`. -/
private def col0Set (m : ℕ) : Set (MvPolynomial (BinomialEdgeVars (Fin m)) K) :=
  Set.range (col0Minor (K := K) m)

private lemma col0Set_finite (m : ℕ) : (col0Set (K := K) m).Finite :=
  Set.finite_range _

private lemma col0Set_ncard (m : ℕ) (_ : 2 ≤ m) :
    (col0Set (K := K) m).ncard ≤ m - 1 := by
  unfold col0Set
  rw [← Set.image_univ]
  calc (col0Minor (K := K) m '' Set.univ).ncard
      _ ≤ Set.univ.ncard := Set.ncard_image_le Set.univ.toFinite
      _ = Nat.card (Fin (m - 1)) := Set.ncard_univ _
      _ = m - 1 := Nat.card_fin _

/-- Each column-0 minor is in J_{K_m}. -/
private lemma col0Minor_mem_bei (m : ℕ) (_ : 2 ≤ m) (j : Fin (m - 1)) :
    col0Minor (K := K) m j ∈ binomialEdgeIdeal (⊤ : SimpleGraph (Fin m)) := by
  have hj := j.isLt
  apply Ideal.subset_span
  refine ⟨⟨0, by omega⟩, ⟨j.val + 1, by omega⟩, ?hadj, ?hlt, rfl⟩
  case hadj => exact (top_adj _ _).mpr (by simp only [ne_eq, Fin.mk.injEq]; omega)
  case hlt => exact Fin.mk_lt_mk.mpr (by omega)

/-- `span(column-0 minors) ≤ J_{K_m}`. -/
private lemma span_col0_le_bei (m : ℕ) (hm : 2 ≤ m) :
    Ideal.span (col0Set (K := K) m) ≤
      binomialEdgeIdeal (⊤ : SimpleGraph (Fin m)) := by
  apply Ideal.span_le.mpr
  intro f hf
  obtain ⟨j, rfl⟩ := hf
  exact col0Minor_mem_bei m hm j

/-- `J_{K_m}` is a minimal prime of `span(column-0 minors)`.

Key argument: for any prime `Q ⊇ span(col-0 minors)` with `Q ⊆ J_{K_m}`,
since `x_0 ∉ J_{K_m}` we have `x_0 ∉ Q`, so from
`x_0 · (x_i y_j - x_j y_i) = x_i · (x_0 y_j - x_j y_0) - x_j · (x_0 y_i - x_i y_0) ∈ Q`
and primality, `x_i y_j - x_j y_i ∈ Q` for all `i < j ≥ 1`, giving `J_{K_m} ⊆ Q`. -/
private lemma bei_complete_mem_minimalPrimes_col0 (m : ℕ) (hm : 2 ≤ m) :
    binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m)) ∈
      (Ideal.span (col0Set (K := K) m)).minimalPrimes := by
  haveI := binomialEdgeIdeal_complete_isPrime (K := K) m hm
  refine ⟨⟨‹_›, span_col0_le_bei m hm⟩, fun Q ⟨hQprime, hcol0Q⟩ hQJ => ?_⟩
  -- Suffices to show every generator x_i y_j - x_j y_i ∈ Q
  apply Ideal.span_le.mpr
  intro f hf
  obtain ⟨i, j, hadj, hij, rfl⟩ := hf
  -- x_0 ∉ J_{K_m}, hence x_0 ∉ Q
  have hx0_not_J : (x (K := K) (⟨0, by omega⟩ : Fin m) : MvPolynomial _ K) ∉
      binomialEdgeIdeal (⊤ : SimpleGraph (Fin m)) := by
    rw [← primeComponent_empty_connected (⊤ : SimpleGraph (Fin m))
      (complete_graph_connected m hm)]
    exact X_inl_not_mem_primeComponent (⊤ : SimpleGraph (Fin m)) ∅
      (Finset.notMem_empty _)
  have hx0_not_Q : (x (K := K) (⟨0, by omega⟩ : Fin m) : MvPolynomial _ K) ∉ Q :=
    fun h => hx0_not_J (hQJ h)
  -- For i < j: x_0 * (x_i y_j - x_j y_i) =
  --   x_i * (x_0 y_j - x_j y_0) - x_j * (x_0 y_i - x_i y_0) ∈ Q
  -- Therefore by primality of Q: x_i y_j - x_j y_i ∈ Q
  -- Helper: for v : Fin m with v ≠ 0, x_0 y_v - x_v y_0 ∈ Q (it's a col-0 minor)
  have col0_mem_Q : ∀ v : Fin m, v.val ≠ 0 →
      x (K := K) (⟨0, by omega⟩ : Fin m) * y v - x v * y (⟨0, by omega⟩ : Fin m) ∈ Q := by
    intro v hv
    apply hcol0Q; apply Ideal.subset_span
    refine ⟨⟨v.val - 1, by omega⟩, ?_⟩
    show col0Minor m ⟨v.val - 1, _⟩ =
      x (⟨0, _⟩ : Fin m) * y v - x v * y (⟨0, _⟩ : Fin m)
    unfold col0Minor x y
    have hval : (⟨v.val - 1 + 1, by omega⟩ : Fin m) = v := by
      ext; exact Nat.succ_pred_eq_of_ne_zero hv
    simp only [hval]
  -- x_0 * (x_i y_j - x_j y_i) ∈ Q via the Plücker-type identity
  have hx0_prod_mem : x (⟨0, by omega⟩ : Fin m) * (x (K := K) i * y j - x j * y i) ∈ Q := by
    have key : x (K := K) (⟨0, by omega⟩ : Fin m) * (x i * y j - x j * y i) =
        x i * (x ⟨0, by omega⟩ * y j - x j * y ⟨0, by omega⟩) -
        x j * (x ⟨0, by omega⟩ * y i - x i * y ⟨0, by omega⟩) := by ring
    rw [key]
    apply Q.sub_mem
    · apply Q.mul_mem_left
      exact col0_mem_Q j (by intro h; exact absurd hij (not_lt.mpr (by
        have : j = (⟨0, by omega⟩ : Fin m) := Fin.ext h
        rw [this]; exact @Fin.zero_le m ⟨by omega⟩ i)))
    · by_cases hi0 : i.val = 0
      · -- i = 0: the term x_j * (x_0 y_0 - x_0 y_0) = 0 ∈ Q
        have heq : i = (⟨0, by omega⟩ : Fin m) := Fin.ext hi0
        rw [heq]; simp only [sub_self, mul_zero]; exact Q.zero_mem
      · exact Q.mul_mem_left _ (col0_mem_Q i hi0)
  exact hQprime.mem_or_mem hx0_prod_mem |>.resolve_left hx0_not_Q

/-! ## Lower bound -/

/-- Lower bound: height(J_{K_m}) ≥ m − 1.

**Strategy** (not yet fully formalized): Define partial Segre maps
`φ_k : K[x,y] → K[x,y]` for k = 0,...,m−1 by `x_i ↦ x_i` and
`y_i ↦ x_i · y_0` for `i ≤ k`, `y_i ↦ y_i` otherwise.

Then `ker(φ_k)` is prime (the image is a domain) and the chain
`⊥ < ker(φ_0) < ker(φ_1) < ⋯ < ker(φ_{m-2}) < ker(φ_{m-1}) = J_{K_m}`
has length m − 1. The strict inclusions follow because `x_0 y_{k+1} − x_{k+1} y_0`
is in `ker(φ_{k+1})` but not in `ker(φ_k)` (the latter maps it to the nonzero
polynomial `x_0 · y_{k+1} − x_{k+1} · x_0 · y_0`). -/
private lemma height_bei_complete_ge (m : ℕ) (hm : 2 ≤ m) :
    (m - 1 : ℕ∞) ≤ Ideal.height (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m))) := by
  sorry

/-! ## Main theorem -/

/-- The binomial edge ideal of the complete graph K_m has height m − 1.
Equivalently, the ideal of 2×2 minors of a generic 2×m matrix has height m − 1. -/
theorem height_binomialEdgeIdeal_complete (m : ℕ) (hm : 2 ≤ m) :
    Ideal.height (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m))) = m - 1 := by
  apply le_antisymm
  · -- Upper bound: height ≤ m - 1, by Krull's height theorem
    calc Ideal.height (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m)))
        _ ≤ (col0Set (K := K) m).ncard :=
            Ideal.height_le_card_of_mem_minimalPrimes_span (col0Set_finite m)
              (bei_complete_mem_minimalPrimes_col0 m hm)
        _ ≤ m - 1 := by exact_mod_cast col0Set_ncard m hm
  · -- Lower bound: height ≥ m - 1
    exact height_bei_complete_ge m hm

end

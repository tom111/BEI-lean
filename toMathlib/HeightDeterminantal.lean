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

/-- Partial Segre map `ψ_k`: substitutes `y_i ↦ x_i · y_0` for `i.val ≤ k`,
keeps `y_i ↦ y_i` for `i.val > k`, and keeps all `x_i ↦ x_i`. -/
private noncomputable def partialSegreMap (m : ℕ) (k : ℕ) :
    MvPolynomial (BinomialEdgeVars (Fin m)) K →ₐ[K]
    MvPolynomial (BinomialEdgeVars (Fin m)) K :=
  MvPolynomial.aeval (fun v : BinomialEdgeVars (Fin m) =>
    match v with
    | Sum.inl i => X (Sum.inl i)
    | Sum.inr i =>
      if i.val ≤ k then
        X (Sum.inl i) * X (Sum.inr (⟨0, by have := i.isLt; omega⟩ : Fin m))
      else X (Sum.inr i))

/-- Single-step substitution `y_{k+1} ↦ x_{k+1} · y_0`, identity on all other variables.
Used to factor `ψ_{k+1} = σ_k ∘ ψ_k`. -/
private noncomputable def segreStep (m : ℕ) (k : ℕ) (hk : k + 1 < m) :
    MvPolynomial (BinomialEdgeVars (Fin m)) K →ₐ[K]
    MvPolynomial (BinomialEdgeVars (Fin m)) K :=
  MvPolynomial.aeval (fun v : BinomialEdgeVars (Fin m) =>
    match v with
    | Sum.inl i => X (Sum.inl i)
    | Sum.inr i =>
      if i = ⟨k + 1, hk⟩ then X (Sum.inl i) * X (Sum.inr (⟨0, by omega⟩ : Fin m))
      else X (Sum.inr i))

/-- `ψ_{k+1} = σ_k ∘ ψ_k`: the partial Segre map factors through the single step. -/
private lemma partialSegreMap_succ_eq_comp (m : ℕ) (k : ℕ) (hk : k + 1 < m) :
    partialSegreMap (K := K) m (k + 1) =
      (segreStep (K := K) m k hk).comp (partialSegreMap m k) := by
  apply MvPolynomial.algHom_ext; intro v
  simp only [AlgHom.comp_apply]
  cases v with
  | inl i =>
    simp only [partialSegreMap, segreStep, MvPolynomial.aeval_X]
  | inr i =>
    simp only [partialSegreMap, segreStep, MvPolynomial.aeval_X]
    by_cases hle : i.val ≤ k
    · -- i ≤ k: both ψ_k and ψ_{k+1} substitute y_i → x_i * y_0
      have hle' : i.val ≤ k + 1 := by omega
      simp only [hle, hle', ite_true]
      -- σ_k(x_i * y_0) = x_i * y_0 since y_0 ≠ y_{k+1} (0 ≠ k+1)
      simp only [map_mul, MvPolynomial.aeval_X]
      have h0ne : (⟨0, by omega⟩ : Fin m) ≠ ⟨k + 1, hk⟩ := by
        intro heq; simp [Fin.ext_iff] at heq
      simp [h0ne]
    · by_cases heq : i.val = k + 1
      · -- i = k+1: ψ_k leaves y_{k+1}, σ_k maps it to x_{k+1} * y_0
        have hle' : i.val ≤ k + 1 := by omega
        simp only [hle, hle', ite_true, ite_false]
        simp only [MvPolynomial.aeval_X]
        have : i = ⟨k + 1, hk⟩ := Fin.ext heq
        simp [this]
      · -- i > k+1: both ψ_k and ψ_{k+1} leave y_i alone
        have hle' : ¬(i.val ≤ k + 1) := by omega
        simp only [hle, hle', ite_false]
        simp only [MvPolynomial.aeval_X]
        have hne : i ≠ ⟨k + 1, hk⟩ := by intro h; exact heq (by rw [h])
        simp [hne]

/-- `ker(ψ_k) ⊆ ker(ψ_{k+1})`: follows from the factorization `ψ_{k+1} = σ_k ∘ ψ_k`. -/
private lemma ker_partialSegreMap_le (m : ℕ) (k : ℕ) (hk : k + 1 < m) :
    RingHom.ker (partialSegreMap (K := K) m k).toRingHom ≤
      RingHom.ker (partialSegreMap (K := K) m (k + 1)).toRingHom := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  have hcomp := partialSegreMap_succ_eq_comp (K := K) m k hk
  have : (partialSegreMap (K := K) m (k + 1)) f = 0 := by
    rw [hcomp, AlgHom.comp_apply, show (partialSegreMap (K := K) m k) f = 0 from hf]
    simp
  exact this

/-- `compRep ⊤ ∅ i = 0` for the complete graph: all vertices are in one component
and 0 is the minimum. -/
private lemma sameComponent_complete_empty (m : ℕ) (i j : Fin m) :
    SameComponent (⊤ : SimpleGraph (Fin m)) ∅ i j := by
  refine ⟨Finset.notMem_empty _, Finset.notMem_empty _, ?_⟩
  by_cases hij : i = j
  · subst hij; exact .refl
  · exact .single ⟨(top_adj i j).mpr hij, Finset.notMem_empty _, Finset.notMem_empty _⟩

private lemma compRep_complete_empty (m : ℕ) (_ : 1 ≤ m) (i : Fin m) :
    compRep (⊤ : SimpleGraph (Fin m)) ∅ i = ⟨0, by omega⟩ := by
  unfold compRep
  simp only [Finset.notMem_empty, ↓reduceDIte]
  apply le_antisymm
  · apply Finset.min'_le
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact sameComponent_complete_empty m i ⟨0, by omega⟩
  · exact Fin.mk_le_mk.mpr (Nat.zero_le _)

open Classical in
/-- `partialSegreMap m (m-1) = primeComponentMap ⊤ ∅` on `Fin m` when `m ≥ 1`. -/
private lemma partialSegreMap_eq_primeComponentMap (m : ℕ) (hm : 1 ≤ m) :
    partialSegreMap (K := K) m (m - 1) = primeComponentMap (⊤ : SimpleGraph (Fin m)) ∅ := by
  apply MvPolynomial.algHom_ext; intro v
  cases v with
  | inl i =>
    simp only [partialSegreMap, primeComponentMap, MvPolynomial.aeval_X,
      Finset.notMem_empty, ite_false]
  | inr i =>
    simp only [partialSegreMap, primeComponentMap, MvPolynomial.aeval_X,
      Finset.notMem_empty, ite_false]
    have : i.val ≤ m - 1 := by omega
    simp only [this, ↓reduceIte]
    congr 1
    rw [compRep_complete_empty m hm i]

/-- `ker(partialSegreMap m (m-1)) = J_{K_m}`. -/
private lemma ker_partialSegreMap_full (m : ℕ) (hm : 2 ≤ m) :
    RingHom.ker (partialSegreMap (K := K) m (m - 1)).toRingHom =
      binomialEdgeIdeal (⊤ : SimpleGraph (Fin m)) := by
  conv_lhs => rw [show (partialSegreMap (K := K) m (m - 1)) =
    primeComponentMap (⊤ : SimpleGraph (Fin m)) ∅ from
    partialSegreMap_eq_primeComponentMap m (by omega)]
  rw [← primeComponent_eq_ker (K := K) (⊤ : SimpleGraph (Fin m)) ∅]
  exact primeComponent_empty_connected (⊤ : SimpleGraph (Fin m))
    (complete_graph_connected m hm)

/-- `partialSegreMap` on `x_i` gives `x_i`. -/
private lemma partialSegreMap_x (m k : ℕ) (i : Fin m) :
    partialSegreMap (K := K) m k (X (Sum.inl i)) = X (Sum.inl i) := by
  simp [partialSegreMap]

/-- `partialSegreMap` on `y_i` when `i.val ≤ k`. -/
private lemma partialSegreMap_y_le (m k : ℕ) (i : Fin m) (h : i.val ≤ k) :
    partialSegreMap (K := K) m k (X (Sum.inr i)) =
      X (Sum.inl i) * X (Sum.inr (⟨0, by have := i.isLt; omega⟩ : Fin m)) := by
  simp [partialSegreMap, h]

/-- `partialSegreMap` on `y_i` when `i.val > k`. -/
private lemma partialSegreMap_y_gt (m k : ℕ) (i : Fin m) (h : ¬(i.val ≤ k)) :
    partialSegreMap (K := K) m k (X (Sum.inr i)) = X (Sum.inr i) := by
  simp [partialSegreMap, h]

/-- The witness `x_0 · y_{k+1} - x_{k+1} · y_0` is in `ker(ψ_{k+1})`. -/
private lemma witness_mem_ker (m : ℕ) (_ : 2 ≤ m) (k : Fin (m - 1)) :
    x (K := K) (⟨0, by omega⟩ : Fin m) * y (⟨k.val + 1, by omega⟩ : Fin m) -
       x (⟨k.val + 1, by omega⟩ : Fin m) * y (⟨0, by omega⟩ : Fin m) ∈
    RingHom.ker (partialSegreMap (K := K) m (k.val + 1)).toRingHom := by
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    x, y, x, y, map_sub, map_mul, map_mul, partialSegreMap_x, partialSegreMap_x]
  -- Now the goal has: partialSegreMap m (k+1) (X (Sum.inr ⟨k+1,_⟩))
  --                and partialSegreMap m (k+1) (X (Sum.inr ⟨0,_⟩))
  rw [partialSegreMap_y_le (K := K) _ _ (⟨k.val + 1, _⟩)
    (le_refl _ : (⟨k.val + 1, _⟩ : Fin m).val ≤ k.val + 1)]
  rw [partialSegreMap_y_le (K := K) _ _ (⟨0, _⟩)
    (Nat.zero_le _ : (⟨0, _⟩ : Fin m).val ≤ k.val + 1)]
  ring

/-- The witness `x_0 · y_{k+1} - x_{k+1} · y_0` is NOT in `ker(ψ_k)`. -/
private lemma witness_not_mem_ker (m : ℕ) (_ : 2 ≤ m) (k : Fin (m - 1)) :
    x (K := K) (⟨0, by omega⟩ : Fin m) * y (⟨k.val + 1, by omega⟩ : Fin m) -
       x (⟨k.val + 1, by omega⟩ : Fin m) * y (⟨0, by omega⟩ : Fin m) ∉
    RingHom.ker (partialSegreMap (K := K) m k.val).toRingHom := by
  rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]; push_neg
  rw [x, y, x, y, map_sub, map_mul, map_mul,
    partialSegreMap_x (K := K), partialSegreMap_x (K := K)]
  rw [partialSegreMap_y_gt (K := K) _ _ (⟨k.val + 1, _⟩)
    (show ¬((⟨k.val + 1, _⟩ : Fin m).val ≤ k.val) from Nat.not_succ_le_self k.val)]
  rw [partialSegreMap_y_le (K := K) _ _ (⟨0, _⟩)
    (Nat.zero_le _ : (⟨0, _⟩ : Fin m).val ≤ k.val)]
  -- Goal: X(inl ⟨0,_⟩) * X(inr ⟨k+1,_⟩) -
  --       X(inl ⟨k+1,_⟩) * (X(inl ⟨0,_⟩) * X(inr ⟨0,_⟩)) ≠ 0
  intro heq
  -- Show nonzero by extracting a coefficient where first term has coeff 1 and second has 0
  set d := Finsupp.single (Sum.inl (⟨0, by omega⟩ : Fin m) : BinomialEdgeVars (Fin m)) 1 +
    Finsupp.single (Sum.inr (⟨k.val + 1, by omega⟩ : Fin m) : BinomialEdgeVars (Fin m)) 1
  have h1 : MvPolynomial.coeff d
    (X (Sum.inl (⟨0, by omega⟩ : Fin m)) * X (Sum.inr (⟨k.val + 1, by omega⟩ : Fin m)) :
      MvPolynomial (BinomialEdgeVars (Fin m)) K) = 1 := by
    simp [d, MvPolynomial.coeff_single_X]
  have h2 : MvPolynomial.coeff d
    (X (Sum.inl (⟨k.val + 1, by omega⟩ : Fin m)) *
     (X (Sum.inl (⟨0, by omega⟩ : Fin m)) * X (Sum.inr (⟨0, by omega⟩ : Fin m))) :
      MvPolynomial (BinomialEdgeVars (Fin m)) K) = 0 := by
    simp only [d, MvPolynomial.coeff_X_mul']
    convert if_neg _
    simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finsupp.single_apply, not_not]
    simp
  have h3 : MvPolynomial.coeff d (0 : MvPolynomial (BinomialEdgeVars (Fin m)) K) = 0 :=
    MvPolynomial.coeff_zero d
  have h4 := congr_arg (MvPolynomial.coeff d) heq
  rw [MvPolynomial.coeff_sub, h1, h2, h3] at h4
  exact one_ne_zero (sub_zero (1 : K) ▸ h4)

/-- `ker(ψ_k) ⊂ ker(ψ_{k+1})` as ideals. -/
private lemma ker_partialSegreMap_lt (m : ℕ) (hm : 2 ≤ m) (k : Fin (m - 1)) :
    RingHom.ker (partialSegreMap (K := K) m k.val).toRingHom <
      RingHom.ker (partialSegreMap (K := K) m (k.val + 1)).toRingHom := by
  refine lt_of_le_of_ne (ker_partialSegreMap_le m k.val (by omega)) ?_
  intro heq
  exact witness_not_mem_ker (K := K) m hm k (heq ▸ witness_mem_ker (K := K) m hm k)

/-- Lower bound: height(J_{K_m}) ≥ m − 1.

Constructs a strictly increasing chain of prime ideals
`ker(ψ_0) < ker(ψ_1) < ⋯ < ker(ψ_{m-1}) = J_{K_m}` of length `m − 1`,
using partial Segre maps `ψ_k` that substitute `y_i ↦ x_i · y_0` for `i ≤ k`. -/
private lemma height_bei_complete_ge (m : ℕ) (hm : 2 ≤ m) :
    (m - 1 : ℕ∞) ≤ Ideal.height (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m))) := by
  haveI hprime := binomialEdgeIdeal_complete_isPrime (K := K) m hm
  rw [Ideal.height_eq_primeHeight]
  -- Build an LTSeries of PrimeSpectrum of length m-1
  -- The chain: ker(ψ_0) < ker(ψ_1) < ... < ker(ψ_{m-1}) = J_{K_m}
  let Q (i : ℕ) : PrimeSpectrum (MvPolynomial (BinomialEdgeVars (Fin m)) K) :=
    ⟨RingHom.ker (partialSegreMap (K := K) m i).toRingHom, RingHom.ker_isPrime _⟩
  let p : LTSeries (PrimeSpectrum (MvPolynomial (BinomialEdgeVars (Fin m)) K)) :=
    ⟨m - 1, fun i => Q i.val, fun ⟨i, hi⟩ => by
      show Q i < Q (i + 1)
      exact ker_partialSegreMap_lt (K := K) m hm ⟨i, by omega⟩⟩
  -- p.last = Q (m-1) has ideal ker(ψ_{m-1}) = J_{K_m}
  have hlast : p.last = ⟨binomialEdgeIdeal (⊤ : SimpleGraph (Fin m)), hprime⟩ := by
    apply PrimeSpectrum.ext
    show (Q (m - 1)).asIdeal = _
    exact ker_partialSegreMap_full m hm
  calc (m - 1 : ℕ∞) = ↑p.length := by norm_cast
    _ ≤ Ideal.primeHeight (binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin m))) := by
        rw [Ideal.primeHeight, ← hlast]; exact Order.length_le_height_last

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

import BEI.AdmissiblePaths
import BEI.MonomialOrder
import BEI.GroebnerAPI
import BEI.ClosedGraphs
import BEI.HerzogLemmas
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# The reduced Gröbner basis and the radical property (Theorems 2.1 and 2.2)

This file formalizes:
- **Theorem 2.1**: `{ u_π · f_{ij} }` is a reduced Gröbner basis of `J_G`.
- **Corollary 2.2**: `J_G` is a radical ideal.

## Reference: Herzog et al. (2010), Theorems 2.1 and Corollary 2.2
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## Theorem 2.1: Reduced Gröbner basis -/

/-- The Gröbner basis set spans `J_G`: every generator `f_{ij}` is in the span
(via trivial admissible paths), and every `u_π · f_{ij}` lies in `J_G`
(see `groebnerElement_mem` in `AdmissiblePaths.lean`). -/
theorem groebnerBasisSet_span (G : SimpleGraph V) :
    Ideal.span (groebnerBasisSet (K := K) G) = binomialEdgeIdeal (K := K) G := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨i, j, π, hπ, rfl⟩ := hf
    exact groebnerElement_mem G i j π hπ
  · apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨i, j, hAdj, hij, rfl⟩ := hf
    exact Ideal.subset_span (generator_in_groebnerBasisSet G i j hAdj hij)

/-! ## Leading coefficient of groebnerElement -/

/-- The leading coefficient of `groebnerElement i j π` is 1 (a unit).
Since `groebnerElement i j π = pathMonomial i j π * fij i j`, the leading coefficient
is `leadingCoeff(pathMonomial) * leadingCoeff(fij) = 1 * 1 = 1`. -/
theorem groebnerElement_leadingCoeff (i j : V) (π : List V) (hij : i < j) :
    binomialEdgeMonomialOrder.leadingCoeff (groebnerElement (K := K) i j π) = 1 := by
  change binomialEdgeMonomialOrder.leadingCoeff
      (pathMonomial (K := K) i j π * fij (K := K) i j) = 1
  rw [MonomialOrder.leadingCoeff_mul, fij_leadingCoeff i j hij, mul_one]
  simp only [pathMonomial, x, y, internalVertices]
  rw [MonomialOrder.leadingCoeff_mul]
  have : ∀ (l : List V) (f : V → BinomialEdgeVars V),
      binomialEdgeMonomialOrder.leadingCoeff
        ((l.map (fun v => (X (f v) : MvPolynomial (BinomialEdgeVars V) K))).prod) = 1 := by
    intro l f
    induction l with
    | nil => exact binomialEdgeMonomialOrder.leadingCoeff_one
    | cons a t ih =>
      simp only [List.map_cons, List.prod_cons, MonomialOrder.leadingCoeff_mul,
                 MonomialOrder.leadingCoeff_X, ih, one_mul]
  simp [this]

/-- The leading coefficient of each groebnerElement is a unit. -/
theorem groebnerElement_leadingCoeff_isUnit
    (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π) :
    IsUnit (binomialEdgeMonomialOrder.leadingCoeff (groebnerElement (K := K) i j π)) := by
  rw [groebnerElement_leadingCoeff i j π hπ.1]
  exact isUnit_one

/-! ## S-polynomial helpers for Buchberger's criterion -/

/-- A product of `X a` terms over a list equals a single monomial with coefficient 1. -/
private lemma prod_X_list_eq_monomial' {σ : Type*} {R : Type*} [CommSemiring R]
    (l : List σ) :
    ∃ (d : σ →₀ ℕ), (l.map (fun a => (X a : MvPolynomial σ R))).prod = monomial d 1 := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨Finsupp.single a 1 + d, ?_⟩
    simp only [List.map_cons, List.prod_cons, hd]
    change (monomial (Finsupp.single a 1) 1 : MvPolynomial σ R) * monomial d 1 = monomial _ 1
    rw [monomial_mul]; simp


/-- If `∏ X(l_k) = monomial d 1` and `t ∉ l`, then `d t = 0`. -/
private lemma prod_X_list_exponent_zero {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R]
    (l : List σ) (t : σ) (ht : t ∉ l)
    (d : σ →₀ ℕ) (hd : (l.map (fun a => (X a : MvPolynomial σ R))).prod = monomial d 1) :
    d t = 0 := by
  classical
  induction l generalizing d with
  | nil =>
    simp [List.map_nil, List.prod_nil] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    simp [← heq]
  | cons a l ih =>
    simp only [List.mem_cons, not_or] at ht
    obtain ⟨d', hd'⟩ := prod_X_list_eq_monomial' (R := R) l
    simp only [List.map_cons, List.prod_cons, hd'] at hd
    change monomial (Finsupp.single a 1) 1 * monomial d' 1 = monomial d 1 at hd
    rw [monomial_mul, one_mul] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    rw [← heq, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm ht.1), zero_add]
    exact ih ht.2 d' hd'

/-- If `∏ X(l_k) = monomial d 1`, `t ∈ l`, and `l.Nodup`, then `d t = 1`. -/
private lemma prod_X_list_exponent_one {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R]
    (l : List σ) (t : σ) (ht : t ∈ l) (hnd : l.Nodup)
    (d : σ →₀ ℕ) (hd : (l.map (fun a => (X a : MvPolynomial σ R))).prod = monomial d 1) :
    d t = 1 := by
  classical
  induction l generalizing d with
  | nil => simp at ht
  | cons a l ih =>
    obtain ⟨d', hd'⟩ := prod_X_list_eq_monomial' (R := R) l
    simp only [List.map_cons, List.prod_cons, hd'] at hd
    change monomial (Finsupp.single a 1) 1 * monomial d' 1 = monomial d 1 at hd
    rw [monomial_mul, one_mul] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    rw [← heq, Finsupp.add_apply, Finsupp.single_apply]
    rcases List.mem_cons.mp ht with rfl | ht'
    · rw [if_pos rfl]
      have : d' t = 0 := by
        apply prod_X_list_exponent_zero l t _ d' hd'
        exact (List.nodup_cons.mp hnd).1
      omega
    · have hnd' := List.Nodup.of_cons hnd
      have hat : a ≠ t := fun h => (List.nodup_cons.mp hnd).1 (h ▸ ht')
      rw [if_neg hat, zero_add]
      exact ih ht' hnd' d' hd'

/-- The pathMonomial exponent at `Sum.inl v` is 0 when `v ∉ internalVertices π` or `¬(j < v)`. -/
private lemma pathMonomial_exponent_inl_zero
    (i j : V) (π : List V) (v : V)
    (hv : v ∉ (internalVertices π).filter (fun w => j < w))
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inl v) = 0 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  have hdx_zero : dx (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    intro hmem
    apply hv
    simp only [List.mem_map] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    rw [← Sum.inl.inj hweq]
    exact hw
  have hdy_zero : dy (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, not_exists, not_and]; intro w _ hweq; exact absurd hweq (by simp)
  omega

/-- The pathMonomial exponent at `Sum.inr v` is 0 when `v ∉ internalVertices π` or `¬(v < i)`. -/
private lemma pathMonomial_exponent_inr_zero
    (i j : V) (π : List V) (v : V)
    (hv : v ∉ (internalVertices π).filter (fun w => w < i))
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inr v) = 0 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  have hdx_zero : dx (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    simp only [List.mem_map, not_exists, not_and]; intro w _ hweq; exact absurd hweq (by simp)
  have hdy_zero : dy (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    intro hmem
    apply hv
    simp only [List.mem_map] at hmem
    obtain ⟨w, hw, hweq⟩ := hmem
    rw [← Sum.inr.inj hweq]
    exact hw
  omega

/-- The pathMonomial exponent at `Sum.inl v` is 1 when `v ∈ internalVertices π` and `j < v`. -/
private lemma pathMonomial_exponent_inl_one
    (i j : V) (π : List V) (v : V)
    (hv_int : v ∈ internalVertices π) (hjv : j < v)
    (hnd : (internalVertices π).Nodup)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inl v) = 1 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  -- dy(inl v) = 0
  have hdy_zero : dy (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, not_exists, not_and]; intro w _ hweq; exact absurd hweq (by simp)
  -- dx(inl v) = 1: Sum.inl v ∈ the x-list
  have hdx_one : dx (Sum.inl v) = 1 := by
    apply prod_X_list_exponent_one _ _ _ _ _ hdx
    · exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv_int, decide_eq_true hjv⟩, rfl⟩
    · exact (hnd.filter _).map Sum.inl_injective
  omega

/-- The pathMonomial exponent at `Sum.inr v` is 1 when `v ∈ internalVertices π` and `v < i`. -/
private lemma pathMonomial_exponent_inr_one
    (i j : V) (π : List V) (v : V)
    (hv_int : v ∈ internalVertices π) (hvi : v < i)
    (hnd : (internalVertices π).Nodup)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inr v) = 1 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  -- dx(inr v) = 0
  have hdx_zero : dx (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    simp only [List.mem_map, not_exists, not_and]; intro w _ hweq; exact absurd hweq (by simp)
  -- dy(inr v) = 1: Sum.inr v ∈ the y-list
  have hdy_one : dy (Sum.inr v) = 1 := by
    apply prod_X_list_exponent_one _ _ _ _ _ hdy
    · exact List.mem_map.mpr ⟨v, List.mem_filter.mpr ⟨hv_int, decide_eq_true hvi⟩, rfl⟩
    · exact (hnd.filter _).map Sum.inr_injective
  omega

/-- The pathMonomial exponent at `Sum.inl v` is 0 when `v ≤ j`. -/
private lemma pathMonomial_exponent_inl_of_le
    (i j : V) (π : List V) (v : V) (hv : ¬(j < v))
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inl v) = 0 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  -- dx(inl v) = 0: v is not in the x-list because v ≤ j
  have hdx_zero : dx (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    simp only [List.mem_map, List.mem_filter, not_exists, not_and]
    intro w hmem hweq
    exact hv (by have := Sum.inl.inj hweq; subst this; exact of_decide_eq_true hmem.2)
  -- dy(inl v) = 0: dy only has inr entries
  have hdy_zero : dy (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, not_exists, not_and]
    intro w _ hweq
    exact absurd hweq (by simp)
  omega

/-- The pathMonomial exponent at `Sum.inr v` is 0 when `i ≤ v`. -/
private lemma pathMonomial_exponent_inr_of_ge
    (i j : V) (π : List V) (v : V) (hv : ¬(v < i))
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inr v) = 0 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  -- dx(inr v) = 0: dx only has inl entries
  have hdx_zero : dx (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    simp only [List.mem_map, not_exists, not_and]
    intro w _ hweq
    exact absurd hweq (by simp)
  -- dy(inr v) = 0: v is not in the y-list because v ≥ i
  have hdy_zero : dy (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, List.mem_filter, not_exists, not_and]
    intro w hmem hweq
    exact hv (by have := Sum.inr.inj hweq; subst this; exact of_decide_eq_true hmem.2)
  omega

/-- At a position `w` where both `f₁` and `f₂` vanish, the S-polynomial monomial factor
`D = (d₁ + f₁) ⊔ (d₂ + f₂) - f₁ ⊔ f₂` satisfies `D(w) ≥ d₁(w)` and `D(w) ≥ d₂(w)`. -/
private lemma sPolyD_ge_of_zero {ι : Type*} (d₁ d₂ f₁ f₂ : ι →₀ ℕ) (w : ι)
    (hf₁ : f₁ w = 0) (hf₂ : f₂ w = 0) :
    ((d₁ + f₁) ⊔ (d₂ + f₂) - f₁ ⊔ f₂) w ≥ d₁ w ∧
    ((d₁ + f₁) ⊔ (d₂ + f₂) - f₁ ⊔ f₂) w ≥ d₂ w := by
  simp only [Finsupp.sup_apply, Finsupp.add_apply, Finsupp.tsub_apply, hf₁, hf₂,
    add_zero, Nat.zero_max, Nat.sub_zero]
  omega

/-- `IsRemainder 0 G 0` holds trivially for any set G. -/
private lemma isRemainder_zero_zero'
    (G : Set (MvPolynomial (BinomialEdgeVars V) K)) :
    binomialEdgeMonomialOrder.IsRemainder (0 : MvPolynomial (BinomialEdgeVars V) K) G 0 :=
  ⟨⟨0, by simp, by simp [degree_zero, le_refl]⟩, by simp⟩

/-- Multiplying an `IsRemainder`-zero witness by a nonzero monomial preserves the property.
Key helper for factoring S-polynomials of groebnerElements via `sPolynomial_monomial_mul`. -/
private lemma isRemainder_monomial_mul'
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (G : Set (MvPolynomial (BinomialEdgeVars V) K))
    (d : BinomialEdgeVars V →₀ ℕ) (c : K) (hc : c ≠ 0)
    (hf : f ≠ 0)
    (h : binomialEdgeMonomialOrder.IsRemainder f G 0) :
    binomialEdgeMonomialOrder.IsRemainder (monomial d c * f) G 0 := by
  obtain ⟨⟨coeff, hsum, hdeg⟩, hrem⟩ := h
  simp only [add_zero] at hsum
  have hm_ne : (monomial d c : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 :=
    monomial_eq_zero.not.mpr hc
  constructor
  · classical
    refine ⟨coeff.mapRange (monomial d c * ·) (by simp), ?_, ?_⟩
    · simp only [add_zero, Finsupp.linearCombination_apply]
      rw [hsum, Finsupp.linearCombination_apply,
          Finsupp.sum_mapRange_index (by simp)]
      rw [Finsupp.mul_sum]
      congr 1; ext ⟨b, hb⟩ x; simp [smul_eq_mul, mul_assoc]
    · intro b
      simp only [Finsupp.mapRange_apply]
      by_cases hcb : b.val * coeff b = 0
      · have : b.val * (monomial d c * coeff b) = monomial d c * (b.val * coeff b) := by ring
        rw [this, hcb, mul_zero, degree_zero]; exact bot_le
      · have key : b.val * (monomial d c * coeff b) = monomial d c * (b.val * coeff b) := by ring
        rw [key, degree_mul hm_ne hcb, degree_mul hm_ne hf,
            binomialEdgeMonomialOrder.toSyn.map_add,
            binomialEdgeMonomialOrder.toSyn.map_add]
        exact add_le_add_right (hdeg b) _
  · intro c' hc'; simp at hc'

/-- `IsRemainder (-f) G 0` follows from `IsRemainder f G 0`. -/
private lemma isRemainder_neg'
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (G : Set (MvPolynomial (BinomialEdgeVars V) K))
    (h : binomialEdgeMonomialOrder.IsRemainder f G 0) :
    binomialEdgeMonomialOrder.IsRemainder (-f) G 0 := by
  by_cases hf : f = 0
  · rw [hf, neg_zero]; exact isRemainder_zero_zero' G
  · have heq : -f = monomial (0 : BinomialEdgeVars V →₀ ℕ) (-1 : K) * f := by
      simp [monomial_zero']
    rw [heq]
    exact isRemainder_monomial_mul' f G 0 (-1) (by norm_num) hf h

/-! ## Admissible path existence from walks -/

/-- The set of "candidate walks" from `a` to `b` in G with the vertex condition. -/
private def walkCandidates (G : SimpleGraph V) (a b : V) : Set (List V) :=
  { π | π.head? = some a ∧ π.getLast? = some b ∧ π.Nodup ∧
        (∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v) ∧
        π.Chain' (fun u v => G.Adj u v) }

/-- Given a nodup walk from `a` to `b` (with `a < b`) satisfying the vertex condition,
there exists an admissible path from `a` to `b` in G that is a sublist of the walk. -/
private theorem exists_admissible_path_of_walk (G : SimpleGraph V)
    (a b : V) (hab : a < b)
    (π : List V) (hHead : π.head? = some a) (hLast : π.getLast? = some b)
    (hND : π.Nodup) (hVtx : ∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v)
    (hWalk : π.Chain' (fun u v => G.Adj u v)) :
    ∃ σ : List V, IsAdmissiblePath G a b σ ∧ σ.Sublist π := by
  -- By strong induction on π.length.
  -- Either π satisfies the minimality condition (7) and is admissible,
  -- or there exists a proper sublist satisfying 1-6, which is shorter.
  suffices ∀ (n : ℕ) (π : List V), π.length ≤ n →
      π.head? = some a → π.getLast? = some b → π.Nodup →
      (∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v) →
      π.Chain' (fun u v => G.Adj u v) →
      ∃ σ, IsAdmissiblePath G a b σ ∧ σ.Sublist π from
    this π.length π le_rfl hHead hLast hND hVtx hWalk
  intro n
  induction n with
  | zero =>
    intro π hlen hHead _ _ _ _
    have : π.length = 0 := Nat.le_zero.mp hlen
    have : π = [] := List.eq_nil_of_length_eq_zero this
    simp [this] at hHead
  | succ n ih =>
    intro π hlen hHead hLast hND hVtx hWalk
    by_cases hMin : ∀ (π' : List V), π'.Sublist π → π' ≠ π →
        π'.head? = some a → π'.getLast? = some b →
        π'.Chain' (fun u v => G.Adj u v) →
        ¬(∀ v ∈ π', v = a ∨ v = b ∨ v < a ∨ b < v)
    · exact ⟨π, ⟨hab, hHead, hLast, hND, hVtx, hWalk, hMin⟩, List.Sublist.refl π⟩
    · push_neg at hMin
      obtain ⟨π', hSub, hNe, hHead', hLast', hWalk', hVtx'⟩ := hMin
      have hND' : π'.Nodup := hND.sublist hSub
      have hlen_lt : π'.length < π.length :=
        lt_of_le_of_ne hSub.length_le (fun h => hNe (hSub.length_eq.mp h))
      obtain ⟨σ, hσ, hσ_sub⟩ := ih π' (by omega) hHead' hLast' hND' hVtx' hWalk'
      exact ⟨σ, hσ, hσ_sub.trans hSub⟩



/-- The pathMonomial is a monomial with coefficient 1. -/
private lemma pathMonomial_is_monomial (i j : V) (π : List V) :
    ∃ d : BinomialEdgeVars V →₀ ℕ, pathMonomial (K := K) i j π = monomial d 1 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun v => j < v) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun v => v < i) |>.map Sum.inr)
  exact ⟨dx + dy, by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun v => j < v)).map
        (fun v => (X (Sum.inl v) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun v => j < v)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun v => v < i)).map
        (fun v => (X (Sum.inr v) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun v => v < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring⟩

/-! ## Sub-walk internal vertex helpers -/

private lemma getLast_not_mem_dropLast_nd (l : List V) (hnd : l.Nodup) (hne : l ≠ []) :
    l.getLast hne ∉ l.dropLast := by
  intro h
  rw [← List.dropLast_append_getLast hne] at hnd
  exact (List.nodup_append.mp hnd).2.2 _ h _ (List.mem_singleton.mpr rfl) rfl

private lemma ne_getLast_of_mem_tdl (l : List V) (hnd : l.Nodup) (hne : l ≠ [])
    (u : V) (hu : u ∈ l.tail.dropLast) : u ≠ l.getLast hne := by
  intro heq; rw [heq] at hu
  apply getLast_not_mem_dropLast_nd l hnd hne
  cases l with
  | nil => exact absurd rfl hne
  | cons x rest =>
    simp only [List.tail_cons] at hu
    cases rest with
    | nil => simp at hu
    | cons y rest' =>
      rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil y rest')]
      exact List.mem_cons_of_mem x hu

/-- Internal vertices of `τ.drop k` are internal vertices of `τ`. -/
private lemma internal_of_drop (τ : List V) (k : ℕ) (a b : V)
    (hne : τ ≠ []) (hND : τ.Nodup) (hHead : τ.head? = some a) (hLast : τ.getLast? = some b)
    (hk_pos : 0 < k) (hk_lt : k < τ.length)
    (u : V) (hu : u ∈ internalVertices (τ.drop k)) : u ∈ internalVertices τ := by
  have hu_mem : u ∈ τ := (List.drop_sublist k τ).mem
    ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hu))
  have hne_drop : τ.drop k ≠ [] := by simp [List.drop_eq_nil_iff]; omega
  have hu_ne_a : u ≠ a := by
    have htail : u ∈ (τ.drop k).tail := (List.dropLast_sublist _).mem hu
    rw [List.tail_drop] at htail
    intro heq
    apply (List.disjoint_take_drop hND (show 1 ≤ k + 1 by omega)) _ htail
    rw [heq]
    cases τ with
    | nil => exact absurd rfl hne
    | cons w rest => simp at hHead; subst hHead; simp
  have hu_ne_b : u ≠ b := by
    intro heq
    have hlast : (τ.drop k).getLast hne_drop = b := by
      rw [List.getLast_drop hne_drop]
      exact Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hLast)
    exact ne_getLast_of_mem_tdl _ ((List.drop_sublist k τ).nodup hND) hne_drop u hu
      (heq ▸ hlast.symm)
  show u ∈ τ.tail.dropLast
  cases τ with
  | nil => exact absurd rfl hne
  | cons w rest =>
    simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
    simp only [List.tail_cons]
    have hu_rest : u ∈ rest := (List.mem_cons.mp hu_mem).resolve_left hu_ne_a
    have hrest_ne : rest ≠ [] := List.ne_nil_of_mem hu_rest
    refine List.mem_dropLast_of_mem_of_ne_getLast hu_rest (fun heq => hu_ne_b ?_)
    rw [heq, ← List.getLast_cons hrest_ne (a := w)]
    exact Option.some.inj ((List.getLast?_eq_some_getLast (List.cons_ne_nil w rest)).symm.trans hLast)

/-- Internal vertices of `τ.take (k+1)` are internal vertices of `τ`. -/
private lemma internal_of_take (τ : List V) (k : ℕ) (a b : V)
    (hne : τ ≠ []) (hND : τ.Nodup) (hHead : τ.head? = some a) (hLast : τ.getLast? = some b)
    (hk_lt_pred : k < τ.length - 1)
    (u : V) (hu : u ∈ internalVertices (τ.take (k + 1))) : u ∈ internalVertices τ := by
  have hu_mem : u ∈ τ := (List.take_sublist (k + 1) τ).mem
    ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hu))
  have hu_ne_a : u ≠ a := by
    intro heq; rw [heq] at hu
    simp only [internalVertices] at hu
    cases ht : τ.take (k + 1) with
    | nil => simp [ht] at hu
    | cons w rest =>
      rw [ht] at hu; simp only [List.tail_cons] at hu
      have hwa : w = a := by
        have := congr_arg List.head? ht.symm
        rw [List.head?_take, if_neg (by omega), hHead] at this; simp at this; exact this
      subst hwa
      exact ((List.nodup_cons.mp (ht ▸ (List.take_sublist (k + 1) τ).nodup hND)).1)
        ((List.dropLast_sublist _).mem hu)
  have hu_ne_b : u ≠ b := by
    intro heq
    have hu_take : u ∈ τ.take (k + 1) :=
      (List.tail_sublist _).mem ((List.dropLast_sublist _).mem hu)
    rw [heq] at hu_take
    have hb_in_dl : b ∈ τ.dropLast := by
      rw [List.dropLast_eq_take]
      exact (List.take_sublist_take_left (show k + 1 ≤ τ.length - 1 by omega)).mem hu_take
    rw [← List.dropLast_append_getLast hne,
        Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hLast)] at hND
    exact (List.nodup_append.mp hND).2.2 b hb_in_dl b (List.mem_singleton.mpr rfl) rfl
  show u ∈ τ.tail.dropLast
  cases τ with
  | nil => exact absurd rfl hne
  | cons w rest =>
    simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
    simp only [List.tail_cons]
    have hu_rest : u ∈ rest := (List.mem_cons.mp hu_mem).resolve_left hu_ne_a
    have hrest_ne : rest ≠ [] := List.ne_nil_of_mem hu_rest
    refine List.mem_dropLast_of_mem_of_ne_getLast hu_rest (fun heq => hu_ne_b ?_)
    rw [heq, ← List.getLast_cons hrest_ne (a := w)]
    exact Option.some.inj ((List.getLast?_eq_some_getLast (List.cons_ne_nil w rest)).symm.trans hLast)

/-! ## General IsRemainder lemma for fij via walk decomposition -/

/-- **Core lemma**: If there is a nodup walk `τ` from `a` to `b` in `G`, and the monomial
`q = monomial d_q 1` "covers" every internal vertex of `τ` (i.e., `d_q` has `y_v` for `v < a`,
`x_v` for `v > b`, and `x_v` for "bad" vertices `a < v < b`), then `q * f_{ab}` has
`IsRemainder 0` modulo the Gröbner basis set.

This generalizes `isRemainder_fij_via_groebnerElement` to walks that may have internal
vertices in the range `(a, b)` (which would violate the admissible path vertex condition).
Such vertices are handled by the `fij_x_telescope` identity. -/
private theorem isRemainder_fij_of_covered_walk (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b : V) (τ : List V) (d_q : BinomialEdgeVars V →₀ ℕ),
    τ.length ≤ n →
    a < b →
    τ.head? = some a →
    τ.getLast? = some b →
    τ.Nodup →
    τ.Chain' (fun u v => G.Adj u v) →
    (∀ v ∈ internalVertices τ,
       (v < a → d_q (Sum.inr v) ≥ 1) ∧
       (b < v → d_q (Sum.inl v) ≥ 1) ∧
       (a < v → v < b → d_q (Sum.inl v) ≥ 1)) →
    binomialEdgeMonomialOrder.IsRemainder
      (monomial d_q 1 * fij (K := K) a b) (groebnerBasisSet G) 0 := by
  intro n
  induction n with
  | zero =>
    intro a b τ _ hlen _ hHead _ _ _ _
    have : τ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    simp [this] at hHead
  | succ n ih =>
    intro a b τ d_q hlen hab hHead hLast hND hWalk hCov
    by_cases hBad : ∃ v ∈ internalVertices τ, a < v ∧ v < b
    · -- Bad vertex case: telescope split at minimum v₀ ∈ (a, b)
      -- Choose v₀ as the minimum bad vertex for coverage transfer
      obtain ⟨v₀_raw, hv₀_raw_int, hav₀_raw, hv₀_rawb⟩ := hBad
      have hBadSet : ((internalVertices τ).filter (fun v => decide (a < v) && decide (v < b))).toFinset.Nonempty := by
        refine ⟨v₀_raw, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hv₀_raw_int, by simp [hav₀_raw, hv₀_rawb]⟩)⟩
      set v₀ := ((internalVertices τ).filter (fun v => decide (a < v) && decide (v < b))).toFinset.min' hBadSet
      have hv₀_filt : v₀ ∈ (internalVertices τ).filter (fun v => decide (a < v) && decide (v < b)) := by
        exact List.mem_toFinset.mp (Finset.min'_mem _ _)
      have hv₀_int : v₀ ∈ internalVertices τ := (List.mem_filter.mp hv₀_filt).1
      have hav₀ : a < v₀ := by have := (List.mem_filter.mp hv₀_filt).2; simp at this; exact this.1
      have hv₀b : v₀ < b := by have := (List.mem_filter.mp hv₀_filt).2; simp at this; exact this.2
      have hv₀_min : ∀ w ∈ internalVertices τ, a < w → w < b → v₀ ≤ w := by
        intro w hw haw hwb
        have hw_filt : w ∈ (internalVertices τ).filter (fun v => decide (a < v) && decide (v < b)) :=
          List.mem_filter.mpr ⟨hw, by simp [haw, hwb]⟩
        exact Finset.min'_le _ _ (List.mem_toFinset.mpr hw_filt)
      -- x_{v₀} divides monomial d_q (from coverage, third clause)
      have hcov_v₀ := (hCov v₀ hv₀_int).2.2 hav₀ hv₀b
      -- Use x-telescope: x_{v₀} * fij a b = x_a * fij v₀ b + x_b * fij a v₀
      -- Factor: monomial d_q 1 * fij a b = monomial d₁ 1 * fij v₀ b + monomial d₂ 1 * fij a v₀
      set ev₀ : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inl v₀) 1 with hev₀_def
      set ea : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inl a) 1 with hea_def
      set eb : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inl b) 1 with heb_def
      set d₁ := d_q - ev₀ + ea with hd₁_def
      set d₂ := d_q - ev₀ + eb with hd₂_def
      -- Sub-walk from v₀ to b (via τ.drop)
      have ⟨τ₂, hτ₂_len, hτ₂_head, hτ₂_last, hτ₂_nd, hτ₂_walk, hτ₂_int⟩ :
          ∃ τ₂ : List V,
          τ₂.length ≤ n ∧
          τ₂.head? = some v₀ ∧ τ₂.getLast? = some b ∧ τ₂.Nodup ∧
          τ₂.Chain' (fun u v => G.Adj u v) ∧
          ∀ u ∈ internalVertices τ₂, u ∈ internalVertices τ := by
        have hne : τ ≠ [] := by intro h; simp [h, internalVertices] at hv₀_int
        have hv₀_mem : v₀ ∈ τ :=
          (List.tail_sublist τ).mem ((List.dropLast_sublist _).mem hv₀_int)
        set k := τ.idxOf v₀
        have hk_lt : k < τ.length := List.idxOf_lt_length_of_mem hv₀_mem
        have hπk : τ[k]'hk_lt = v₀ := List.getElem_idxOf hk_lt
        have hk_pos : 0 < k := by
          by_contra h; push_neg at h
          have h0 : τ.idxOf v₀ = 0 := Nat.le_zero.mp h
          cases τ with
          | nil => exact absurd rfl hne
          | cons w rest =>
            simp only [List.head?_cons, Option.some.injEq] at hHead
            have : w = v₀ := by
              have hlt : (w :: rest).idxOf v₀ < (w :: rest).length :=
                List.idxOf_lt_length_of_mem hv₀_mem
              have := List.getElem_idxOf hlt
              simp [h0] at this; exact this
            exact absurd (this.symm.trans hHead) (ne_of_gt hav₀)
        refine ⟨τ.drop k, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [List.length_drop]; omega
        · rw [List.head?_drop, List.getElem?_eq_getElem hk_lt, hπk]
        · rw [List.getLast?_drop, if_neg (by omega), hLast]
        · exact (List.drop_sublist k τ).nodup hND
        · exact List.IsChain.drop hWalk k
        · exact fun u hu => internal_of_drop τ k a b hne hND hHead hLast hk_pos hk_lt u hu
      -- Sub-walk from a to v₀ (via τ.take)
      have ⟨τ₁, hτ₁_len, hτ₁_head, hτ₁_last, hτ₁_nd, hτ₁_walk, hτ₁_int⟩ :
          ∃ τ₁ : List V,
          τ₁.length ≤ n ∧
          τ₁.head? = some a ∧ τ₁.getLast? = some v₀ ∧ τ₁.Nodup ∧
          τ₁.Chain' (fun u v => G.Adj u v) ∧
          ∀ u ∈ internalVertices τ₁, u ∈ internalVertices τ := by
        have hne : τ ≠ [] := by intro h; simp [h, internalVertices] at hv₀_int
        have hv₀_mem : v₀ ∈ τ :=
          (List.tail_sublist τ).mem ((List.dropLast_sublist _).mem hv₀_int)
        set k := τ.idxOf v₀
        have hk_lt : k < τ.length := List.idxOf_lt_length_of_mem hv₀_mem
        have hπk : τ[k]'hk_lt = v₀ := List.getElem_idxOf hk_lt
        have hk_lt_pred : k < τ.length - 1 := by
          rcases Nat.lt_or_ge k (τ.length - 1) with h | h
          · exact h
          · exfalso
            have hk_eq : k = τ.length - 1 := Nat.le_antisymm (by omega) h
            have hv₀_last : v₀ = τ.getLast hne := by
              rw [List.getLast_eq_getElem]
              exact (show τ[τ.length - 1] = τ[k] from by congr 1; omega).trans hπk |>.symm
            exact (ne_of_lt hv₀b) (hv₀_last.trans
              (Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hLast)))
        refine ⟨τ.take (k + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [List.length_take]; omega
        · rw [List.head?_take, if_neg (by omega), hHead]
        · -- getLast? of take (k+1)
          have : (τ.take (k + 1)).getLast? = some v₀ := by
            rw [List.getLast?_take, if_neg (by omega)]
            have : τ[k]? = some v₀ := by
              rw [List.getElem?_eq_getElem (show k < τ.length by omega)]; exact congrArg some hπk
            simp [this]
          exact this
        · exact (List.take_sublist (k + 1) τ).nodup hND
        · exact List.IsChain.take hWalk (k + 1)
        · exact fun u hu => internal_of_take τ k a b hne hND hHead hLast hk_lt_pred u hu
      -- Coverage for sub-walks
      have hCov₂ : ∀ v ∈ internalVertices τ₂,
          (v < v₀ → d₁ (Sum.inr v) ≥ 1) ∧
          (b < v → d₁ (Sum.inl v) ≥ 1) ∧
          (v₀ < v → v < b → d₁ (Sum.inl v) ≥ 1) := by
        intro v hv
        have hv_τ := hτ₂_int v hv
        have ⟨hc1, hc2, hc3⟩ := hCov v hv_τ
        have hv_ne_a : v ≠ a := by
          intro heq; subst heq
          have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
          cases τ with | nil => exact absurd rfl hne_τ | cons w rest =>
            simp at hHead; subst hHead
            simp only [internalVertices, List.tail_cons] at hv_τ
            exact ((List.nodup_cons.mp hND).1) ((List.dropLast_sublist _).mem hv_τ)
        -- d₁(inr v) = d_q(inr v) since ev₀, ea only affect inl
        have hinr : d₁ (Sum.inr v) = d_q (Sum.inr v) := by
          simp only [hd₁_def, hev₀_def, hea_def, Finsupp.add_apply, Finsupp.tsub_apply]
          simp [Finsupp.single_apply]
        -- d₁(inl v) = d_q(inl v) when v ≠ v₀ and v ≠ a
        have hinl (hv₀' : v ≠ v₀) : d₁ (Sum.inl v) = d_q (Sum.inl v) := by
          simp only [hd₁_def, hev₀_def, hea_def]
          unfold BinomialEdgeVars at *
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inl.injEq]
          rw [if_neg (Ne.symm hv₀'), if_neg (Ne.symm hv_ne_a)]; omega
        refine ⟨fun hvv₀ => ?_, fun hvb => ?_, fun hvv₀ hvb => ?_⟩
        · -- v < v₀: by minimality, v is not bad, so v < a
          rw [hinr]
          have hva : v < a := by
            by_contra h; push_neg at h
            have hav : a < v := lt_of_le_of_ne h (Ne.symm hv_ne_a)
            have hvb' : v < b := lt_trans hvv₀ hv₀b
            exact absurd (hv₀_min v hv_τ hav hvb') (not_le.mpr hvv₀)
          exact hc1 hva
        · -- b < v
          rw [hinl (ne_of_gt (lt_trans hv₀b hvb))]
          exact hc2 hvb
        · -- v₀ < v < b
          rw [hinl (ne_of_gt hvv₀)]
          exact hc3 (lt_trans hav₀ hvv₀) hvb
      have hCov₁ : ∀ v ∈ internalVertices τ₁,
          (v < a → d₂ (Sum.inr v) ≥ 1) ∧
          (v₀ < v → d₂ (Sum.inl v) ≥ 1) ∧
          (a < v → v < v₀ → d₂ (Sum.inl v) ≥ 1) := by
        intro v hv
        have hv_τ := hτ₁_int v hv
        have ⟨hc1, hc2, hc3⟩ := hCov v hv_τ
        have hv_ne_b : v ≠ b := by
          intro heq; subst heq
          have hne_τ : τ ≠ [] := by
            intro h; simp [h, internalVertices] at hv_τ
          exact (ne_getLast_of_mem_tdl τ hND hne_τ v hv_τ)
            (Option.some.inj (hLast.symm.trans (List.getLast?_eq_some_getLast hne_τ)))
        -- d₂(inr v) = d_q(inr v)
        have hinr : d₂ (Sum.inr v) = d_q (Sum.inr v) := by
          simp only [hd₂_def, hev₀_def, heb_def, Finsupp.add_apply, Finsupp.tsub_apply]
          simp [Finsupp.single_apply]
        -- d₂(inl v) = d_q(inl v) when v ≠ v₀ and v ≠ b
        have hinl (hv₀' : v ≠ v₀) : d₂ (Sum.inl v) = d_q (Sum.inl v) := by
          simp only [hd₂_def, hev₀_def, heb_def]
          unfold BinomialEdgeVars at *
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inl.injEq]
          rw [if_neg (Ne.symm hv₀'), if_neg (Ne.symm hv_ne_b)]; omega
        refine ⟨fun hva => ?_, fun hvv₀ => ?_, fun hav hvv₀ => ?_⟩
        · -- v < a
          rw [hinr]; exact hc1 hva
        · -- v₀ < v: v is internal to τ, and v > v₀ > a, so a < v
          rw [hinl (ne_of_gt hvv₀)]
          rcases lt_or_ge v b with hvb | hvb
          · exact hc3 (lt_trans hav₀ hvv₀) hvb
          · exact hc2 (lt_of_le_of_ne hvb (Ne.symm hv_ne_b))
        · -- a < v < v₀: vacuous by minimality of v₀
          exfalso
          exact absurd (hv₀_min v hv_τ hav (lt_trans hvv₀ hv₀b)) (not_le.mpr hvv₀)
      -- Apply IH to both sub-walks
      have h₁ : binomialEdgeMonomialOrder.IsRemainder
          (monomial d₁ 1 * fij (K := K) v₀ b) (groebnerBasisSet G) 0 :=
        ih v₀ b τ₂ d₁ hτ₂_len hv₀b hτ₂_head hτ₂_last hτ₂_nd hτ₂_walk hCov₂
      have h₂ : binomialEdgeMonomialOrder.IsRemainder
          (monomial d₂ 1 * fij (K := K) a v₀) (groebnerBasisSet G) 0 :=
        ih a v₀ τ₁ d₂ hτ₁_len hav₀ hτ₁_head hτ₁_last hτ₁_nd hτ₁_walk hCov₁
      -- Algebraic identity
      have halg : monomial d_q (1 : K) * fij a b =
          monomial d₁ 1 * fij (K := K) v₀ b + monomial d₂ 1 * fij (K := K) a v₀ := by
        -- Factor: monomial d_q 1 = monomial (d_q - ev₀) 1 * monomial ev₀ 1
        have hle : ev₀ ≤ d_q := by
          unfold BinomialEdgeVars at *; exact Finsupp.single_le_iff.mpr hcov_v₀
        have hfactor : (monomial d_q (1:K) : MvPolynomial (BinomialEdgeVars V) K) =
            monomial (d_q - ev₀) (1:K) * monomial ev₀ (1:K) := by
          rw [monomial_mul, one_mul, tsub_add_cancel_of_le hle]
        -- monomial ev₀ 1 = x v₀
        have hxv₀ : (monomial ev₀ (1:K) : MvPolynomial (BinomialEdgeVars V) K) = x v₀ := rfl
        -- Apply fij_x_telescope: x v₀ * fij a b = x a * fij v₀ b + x b * fij a v₀
        rw [hfactor, mul_assoc,
            show monomial ev₀ (1:K) * fij (K := K) a b = x v₀ * fij a b from by rw [← hxv₀],
            fij_x_telescope (K := K) a v₀ b, mul_add, ← mul_assoc, ← mul_assoc]
        -- Recombine monomials
        congr 1
        · congr 1
          show monomial (d_q - ev₀) (1:K) * x (K := K) a = monomial d₁ 1
          change monomial (d_q - ev₀) (1:K) * monomial ea (1:K) = monomial d₁ 1
          rw [monomial_mul, one_mul]
        · congr 1
          show monomial (d_q - ev₀) (1:K) * x (K := K) b = monomial d₂ 1
          change monomial (d_q - ev₀) (1:K) * monomial eb (1:K) = monomial d₂ 1
          rw [monomial_mul, one_mul]
      -- Degree bounds for isRemainder_add
      -- The two terms have different degrees (discriminator at inl v₀).
      have hne_deg : binomialEdgeMonomialOrder.degree (monomial d₁ (1:K) * fij v₀ b) ≠
                     binomialEdgeMonomialOrder.degree (monomial d₂ (1:K) * fij a v₀) := by
        classical
        have hdeg1 : binomialEdgeMonomialOrder.degree (monomial d₁ (1:K) * fij v₀ b) =
            d₁ + (Finsupp.single (Sum.inl v₀ : BinomialEdgeVars V) 1 +
                   Finsupp.single (Sum.inr b : BinomialEdgeVars V) 1) := by
          rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero) (fij_ne_zero v₀ b hv₀b),
              degree_monomial, if_neg one_ne_zero, fij_degree v₀ b hv₀b]
        have hdeg2 : binomialEdgeMonomialOrder.degree (monomial d₂ (1:K) * fij a v₀) =
            d₂ + (Finsupp.single (Sum.inl a : BinomialEdgeVars V) 1 +
                   Finsupp.single (Sum.inr v₀ : BinomialEdgeVars V) 1) := by
          rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero) (fij_ne_zero a v₀ hav₀),
              degree_monomial, if_neg one_ne_zero, fij_degree a v₀ hav₀]
        -- Show the degree Finsupps differ at Sum.inl v₀:
        -- M1(inl v₀) = d_q(inl v₀), M2(inl v₀) = d_q(inl v₀) - 1
        -- Helper: evaluate inner Finsupp sums at inl v₀
        -- Finsupp.single_eq_of_ne takes (query ≠ key)
        rw [hdeg1, hdeg2]
        intro heq
        have hv := Finsupp.ext_iff.mp heq (Sum.inl v₀ : BinomialEdgeVars V)
        simp only [d₁, d₂, ev₀, ea, eb] at hv
        unfold BinomialEdgeVars at hv
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
          Sum.inl.injEq, reduceCtorEq, ite_true, ite_false,
          if_neg (ne_of_lt hav₀), if_neg (ne_of_lt hv₀b).symm] at hv
        omega
      obtain ⟨hdeg₁, hdeg₂⟩ := degree_bounds_of_ne _ _ hne_deg
      rw [halg]
      exact isRemainder_add _ _ _ h₁ h₂ hdeg₁ hdeg₂
    · -- No bad vertices: extract admissible path directly
      push_neg at hBad
      have hne_τ : τ ≠ [] := fun h => by simp [h] at hHead
      -- Helper: v ∈ τ, v ≠ head, v ≠ last → v ∈ internalVertices τ
      have mem_internal : ∀ v ∈ τ, v ≠ a → v ≠ b → v ∈ internalVertices τ := by
        intro v hv hva hvb
        simp only [internalVertices]
        match τ, hHead, hLast, hND, hv, hne_τ with
        | a' :: rest, hH, hL, hN, hv', _ =>
          simp only [List.head?_cons, Option.some.injEq] at hH; subst hH
          simp only [List.tail_cons]
          have hv_rest : v ∈ rest := (List.mem_cons.mp hv').resolve_left hva
          have hrest_ne : rest ≠ [] := List.ne_nil_of_mem hv_rest
          refine List.mem_dropLast_of_mem_of_ne_getLast hv_rest (fun heq => hvb ?_)
          have hlast_eq := List.getLast_cons hrest_ne (a := a')
          have hb : (a' :: rest).getLast (List.cons_ne_nil a' rest) = b :=
            Option.some.inj ((List.getLast?_eq_some_getLast (List.cons_ne_nil a' rest)).symm.trans hL)
          rw [heq, ← hlast_eq, hb]
      have hVtx : ∀ v ∈ τ, v = a ∨ v = b ∨ v < a ∨ b < v := by
        intro v hv
        rcases eq_or_ne v a with rfl | hva
        · exact Or.inl rfl
        · rcases eq_or_ne v b with rfl | hvb
          · exact Or.inr (Or.inl rfl)
          · -- v is internal, use hBad to conclude v < a or v > b
            have hv_int := mem_internal v hv hva hvb
            rcases lt_or_ge v a with hlt | hge
            · exact Or.inr (Or.inr (Or.inl hlt))
            · have hva' : a < v := lt_of_le_of_ne hge (Ne.symm hva)
              have hbv := hBad v hv_int hva'
              exact Or.inr (Or.inr (Or.inr (lt_of_le_of_ne hbv (Ne.symm hvb))))
      obtain ⟨σ, hσ, hσ_sub⟩ := exists_admissible_path_of_walk G a b hab τ
        hHead hLast hND hVtx hWalk
      obtain ⟨d_σ, hd_σ⟩ := pathMonomial_is_monomial (K := K) a b σ
      have hσ_nd : σ.Nodup := hσ.2.2.2.1
      have hσ_int_nd : (internalVertices σ).Nodup :=
        (hσ_nd.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
      have hσ_vtx := hσ.2.2.2.2.1  -- ∀ v ∈ σ, v = a ∨ v = b ∨ v < a ∨ b < v
      -- Internal vertices of σ are internal to τ (same endpoints, sublist)
      have hσ_head := hσ.2.1
      have hσ_last := hσ.2.2.1
      have hσ_ne : σ ≠ [] := by intro h; simp [h] at hσ_head
      have hint_σ_τ : ∀ v ∈ internalVertices σ, v ∈ internalVertices τ := by
        intro v hv_int_σ
        have hv_σ : v ∈ σ := (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_int_σ)
        have hv_τ : v ∈ τ := hσ_sub.mem hv_σ
        -- Use the admissibility vertex condition to show v ≠ a and v ≠ b
        have hva : v ≠ a := by
          intro heq
          -- v = a: a ∈ internalVertices σ contradicts nodup (a is head of σ)
          -- internalVertices σ ⊆ σ.tail, and a is the head.
          -- If a ∈ tail, then a appears twice, contradicting nodup.
          have hv_tail : v ∈ σ.tail := (List.dropLast_sublist _).mem hv_int_σ
          rw [heq] at hv_tail
          have : σ.head? = some a := hσ_head
          match σ, this, hσ_nd with
          | x :: rest, hh, hnd =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            rw [hh] at hnd; exact (List.nodup_cons.mp hnd).1 hv_tail
        have hvb : v ≠ b := by
          intro heq
          -- v = b: b ∈ internalVertices σ contradicts σ.Nodup (b is the last element)
          -- internalVertices σ = σ.tail.dropLast, so b ∈ σ.tail.dropLast
          -- But b = σ.getLast, and nodup prevents this.
          rw [heq] at hv_int_σ
          match σ, hσ_head, hσ_last, hσ_nd with
          | x :: rest, hh, hl, hnd =>
            simp only [internalVertices, List.tail_cons] at hv_int_σ
            match rest, hv_int_σ with
            | y :: rest', hv_dp =>
              have hnd_rest := (List.nodup_cons.mp hnd).2
              -- getLast (y :: rest') = b
              have hb_last : (y :: rest').getLast (List.cons_ne_nil y rest') = b := by
                simp only [List.getLast?_cons_cons] at hl
                rw [List.getLast?_eq_some_getLast (List.cons_ne_nil y rest')] at hl
                exact Option.some.inj hl
              -- b ∈ dropLast contradicts nodup since b = getLast
              have : (y :: rest').dropLast ++ [(y :: rest').getLast (List.cons_ne_nil y rest')] =
                  y :: rest' := List.dropLast_append_getLast (List.cons_ne_nil y rest')
              rw [← this] at hnd_rest
              have hb_in_dp := hb_last ▸ hv_dp
              exact (List.nodup_append.mp hnd_rest).2.2 _ hb_in_dp _ (List.Mem.head _) rfl
        exact mem_internal v hv_τ hva hvb
      have hdiv : d_σ ≤ d_q := by
        intro w
        rcases w with ⟨v⟩ | ⟨v⟩
        · -- w = Sum.inl v
          by_cases hv_filt : v ∈ (internalVertices σ).filter (fun w => b < w)
          · -- v is internal to σ and b < v: d_σ(inl v) = 1
            have hv_int_σ : v ∈ internalVertices σ := (List.mem_filter.mp hv_filt).1
            have hjv : b < v := of_decide_eq_true (List.mem_filter.mp hv_filt).2
            rw [pathMonomial_exponent_inl_one (K := K) a b σ v hv_int_σ hjv hσ_int_nd d_σ hd_σ]
            exact (hCov v (hint_σ_τ v hv_int_σ)).2.1 hjv
          · -- v not in filtered list: d_σ(inl v) = 0
            rw [pathMonomial_exponent_inl_zero (K := K) a b σ v hv_filt d_σ hd_σ]
            exact Nat.zero_le _
        · -- w = Sum.inr v
          by_cases hv_filt : v ∈ (internalVertices σ).filter (fun w => w < a)
          · have hv_int_σ : v ∈ internalVertices σ := (List.mem_filter.mp hv_filt).1
            have hvi : v < a := of_decide_eq_true (List.mem_filter.mp hv_filt).2
            rw [pathMonomial_exponent_inr_one (K := K) a b σ v hv_int_σ hvi hσ_int_nd d_σ hd_σ]
            exact (hCov v (hint_σ_τ v hv_int_σ)).1 hvi
          · rw [pathMonomial_exponent_inr_zero (K := K) a b σ v hv_filt d_σ hd_σ]
            exact Nat.zero_le _
      exact isRemainder_fij_via_groebnerElement G a b σ hσ
        (monomial d_q 1) d_q rfl d_σ hd_σ hdiv

/-- **Dual variant (y-telescope)**: same as `isRemainder_fij_of_covered_walk` but the
coverage for "bad" vertices `a < v < b` uses `Sum.inr v` (y-variable) instead of
`Sum.inl v` (x-variable). The proof uses `fij_telescope` instead of `fij_x_telescope`.
Needed for the shared-last-endpoint case (Case 5 of Theorem 2.1). -/
private theorem isRemainder_fij_of_covered_walk_y (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b : V) (τ : List V) (d_q : BinomialEdgeVars V →₀ ℕ),
    τ.length ≤ n →
    a < b →
    τ.head? = some a →
    τ.getLast? = some b →
    τ.Nodup →
    τ.Chain' (fun u v => G.Adj u v) →
    (∀ v ∈ internalVertices τ,
       (v < a → d_q (Sum.inr v) ≥ 1) ∧
       (b < v → d_q (Sum.inl v) ≥ 1) ∧
       (a < v → v < b → d_q (Sum.inr v) ≥ 1)) →
    binomialEdgeMonomialOrder.IsRemainder
      (monomial d_q 1 * fij (K := K) a b) (groebnerBasisSet G) 0 := by
  intro n
  induction n with
  | zero =>
    intro a b τ _ hlen _ hHead _ _ _ _
    have : τ = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    simp [this] at hHead
  | succ n ih =>
    intro a b τ d_q hlen hab hHead hLast hND hWalk hCov
    by_cases hBad : ∃ v ∈ internalVertices τ, a < v ∧ v < b
    · -- Bad vertex case: y-telescope split at maximum v₀ ∈ (a, b)
      obtain ⟨v₀_raw, hv₀_raw_int, hav₀_raw, hv₀_rawb⟩ := hBad
      have hBadSet : ((internalVertices τ).filter (fun v => decide (a < v) && decide (v < b))).toFinset.Nonempty := by
        refine ⟨v₀_raw, List.mem_toFinset.mpr (List.mem_filter.mpr ⟨hv₀_raw_int, by simp [hav₀_raw, hv₀_rawb]⟩)⟩
      set v₀ := ((internalVertices τ).filter (fun v => decide (a < v) && decide (v < b))).toFinset.max' hBadSet
      have hv₀_filt : v₀ ∈ (internalVertices τ).filter (fun v => decide (a < v) && decide (v < b)) := by
        exact List.mem_toFinset.mp (Finset.max'_mem _ _)
      have hv₀_int : v₀ ∈ internalVertices τ := (List.mem_filter.mp hv₀_filt).1
      have hav₀ : a < v₀ := by have := (List.mem_filter.mp hv₀_filt).2; simp at this; exact this.1
      have hv₀b : v₀ < b := by have := (List.mem_filter.mp hv₀_filt).2; simp at this; exact this.2
      have hv₀_max : ∀ w ∈ internalVertices τ, a < w → w < b → w ≤ v₀ := by
        intro w hw haw hwb
        have hw_filt : w ∈ (internalVertices τ).filter (fun v => decide (a < v) && decide (v < b)) :=
          List.mem_filter.mpr ⟨hw, by simp [haw, hwb]⟩
        exact Finset.le_max' _ _ (List.mem_toFinset.mpr hw_filt)
      -- y_{v₀} divides monomial d_q (from coverage, third clause)
      have hcov_v₀ := (hCov v₀ hv₀_int).2.2 hav₀ hv₀b
      -- Use y-telescope: y v₀ * fij a b = y b * fij a v₀ + y a * fij v₀ b
      -- monomial d_q 1 * fij a b
      --   = monomial (d_q - single(inr v₀)) 1 * y_{v₀} * fij a b
      --   = monomial (d_q - single(inr v₀)) 1 * (y_b * fij a v₀ + y_a * fij v₀ b)
      --   = monomial d₁ 1 * fij a v₀ + monomial d₂ 1 * fij v₀ b
      -- where d₁ = d_q - single(inr v₀) + single(inr b)
      --       d₂ = d_q - single(inr v₀) + single(inr a)
      set eyv₀ : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inr v₀) 1 with heyv₀_def
      set eyb : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inr b) 1 with heyb_def
      set eya : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inr a) 1 with heya_def
      set d₁ := d_q - eyv₀ + eyb with hd₁_def
      set d₂ := d_q - eyv₀ + eya with hd₂_def
      -- Sub-walk from v₀ to b
      have ⟨τ₂, hτ₂_len, hτ₂_head, hτ₂_last, hτ₂_nd, hτ₂_walk, hτ₂_int⟩ :
          ∃ τ₂ : List V,
          τ₂.length ≤ n ∧
          τ₂.head? = some v₀ ∧ τ₂.getLast? = some b ∧ τ₂.Nodup ∧
          τ₂.Chain' (fun u v => G.Adj u v) ∧
          ∀ u ∈ internalVertices τ₂, u ∈ internalVertices τ := by
        have hne : τ ≠ [] := by intro h; simp [h, internalVertices] at hv₀_int
        have hv₀_mem : v₀ ∈ τ :=
          (List.tail_sublist τ).mem ((List.dropLast_sublist _).mem hv₀_int)
        set k := τ.idxOf v₀
        have hk_lt : k < τ.length := List.idxOf_lt_length_of_mem hv₀_mem
        have hπk : τ[k]'hk_lt = v₀ := List.getElem_idxOf hk_lt
        have hk_pos : 0 < k := by
          by_contra h; push_neg at h
          have h0 : τ.idxOf v₀ = 0 := Nat.le_zero.mp h
          cases τ with
          | nil => exact absurd rfl hne
          | cons w rest =>
            simp only [List.head?_cons, Option.some.injEq] at hHead
            have : w = v₀ := by
              have hlt : (w :: rest).idxOf v₀ < (w :: rest).length :=
                List.idxOf_lt_length_of_mem hv₀_mem
              have := List.getElem_idxOf hlt
              simp [h0] at this; exact this
            exact absurd (this.symm.trans hHead) (ne_of_gt hav₀)
        refine ⟨τ.drop k, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [List.length_drop]; omega
        · rw [List.head?_drop, List.getElem?_eq_getElem hk_lt, hπk]
        · rw [List.getLast?_drop, if_neg (by omega), hLast]
        · exact (List.drop_sublist k τ).nodup hND
        · exact List.IsChain.drop hWalk k
        · exact fun u hu => internal_of_drop τ k a b hne hND hHead hLast hk_pos hk_lt u hu
      -- Sub-walk from a to v₀
      have ⟨τ₁, hτ₁_len, hτ₁_head, hτ₁_last, hτ₁_nd, hτ₁_walk, hτ₁_int⟩ :
          ∃ τ₁ : List V,
          τ₁.length ≤ n ∧
          τ₁.head? = some a ∧ τ₁.getLast? = some v₀ ∧ τ₁.Nodup ∧
          τ₁.Chain' (fun u v => G.Adj u v) ∧
          ∀ u ∈ internalVertices τ₁, u ∈ internalVertices τ := by
        have hne : τ ≠ [] := by intro h; simp [h, internalVertices] at hv₀_int
        have hv₀_mem : v₀ ∈ τ :=
          (List.tail_sublist τ).mem ((List.dropLast_sublist _).mem hv₀_int)
        set k := τ.idxOf v₀
        have hk_lt : k < τ.length := List.idxOf_lt_length_of_mem hv₀_mem
        have hπk : τ[k]'hk_lt = v₀ := List.getElem_idxOf hk_lt
        have hk_lt_pred : k < τ.length - 1 := by
          rcases Nat.lt_or_ge k (τ.length - 1) with h | h
          · exact h
          · exfalso
            have hk_eq : k = τ.length - 1 := Nat.le_antisymm (by omega) h
            have hv₀_last : v₀ = τ.getLast hne := by
              rw [List.getLast_eq_getElem]
              exact (show τ[τ.length - 1] = τ[k] from by congr 1; omega).trans hπk |>.symm
            exact (ne_of_lt hv₀b) (hv₀_last.trans
              (Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hLast)))
        refine ⟨τ.take (k + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [List.length_take]; omega
        · rw [List.head?_take, if_neg (by omega), hHead]
        · have : (τ.take (k + 1)).getLast? = some v₀ := by
            rw [List.getLast?_take, if_neg (by omega)]
            have : τ[k]? = some v₀ := by
              rw [List.getElem?_eq_getElem (show k < τ.length by omega)]; exact congrArg some hπk
            simp [this]
          exact this
        · exact (List.take_sublist (k + 1) τ).nodup hND
        · exact List.IsChain.take hWalk (k + 1)
        · exact fun u hu => internal_of_take τ k a b hne hND hHead hLast hk_lt_pred u hu
      -- Coverage for sub-walks (y-variant: bad vertices tracked by Sum.inr)
      have hCov₁ : ∀ v ∈ internalVertices τ₁,
          (v < a → d₁ (Sum.inr v) ≥ 1) ∧
          (v₀ < v → d₁ (Sum.inl v) ≥ 1) ∧
          (a < v → v < v₀ → d₁ (Sum.inr v) ≥ 1) := by
        intro v hv
        have hv_τ := hτ₁_int v hv
        have ⟨hc1, hc2, hc3⟩ := hCov v hv_τ
        have hv_ne_b : v ≠ b := by
          intro heq; subst heq
          have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
          exact (ne_getLast_of_mem_tdl τ hND hne_τ v hv_τ)
            (Option.some.inj (hLast.symm.trans (List.getLast?_eq_some_getLast hne_τ)))
        -- d₁(inl v) = d_q(inl v) since eyv₀, eyb are inr
        have hinl : d₁ (Sum.inl v) = d_q (Sum.inl v) := by
          simp only [hd₁_def, heyv₀_def, heyb_def]
          simp [Finsupp.add_apply, Finsupp.tsub_apply]
        -- d₁(inr v) = d_q(inr v) when v ≠ v₀ and v ≠ b
        have hinr (hv₀' : v ≠ v₀) : d₁ (Sum.inr v) = d_q (Sum.inr v) := by
          simp only [hd₁_def, heyv₀_def, heyb_def]
          unfold BinomialEdgeVars at *
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inr.injEq]
          rw [if_neg (Ne.symm hv₀'), if_neg (Ne.symm hv_ne_b)]; omega
        refine ⟨fun hva => ?_, fun hvv₀ => ?_, fun hav hvv₀ => ?_⟩
        · -- v < a: v ≠ v₀ and v ≠ b
          rw [hinr (ne_of_lt (lt_trans hva hav₀))]; exact hc1 hva
        · -- v₀ < v: by maximality, v is not bad, so b < v
          rw [hinl]
          have hvb : b < v := by
            by_contra h; push_neg at h
            have hvb' : v < b := lt_of_le_of_ne h hv_ne_b
            exact absurd hvv₀ (not_lt.mpr (hv₀_max v hv_τ (lt_trans hav₀ hvv₀) hvb'))
          exact hc2 hvb
        · -- a < v < v₀
          rw [hinr (ne_of_lt hvv₀)]
          exact hc3 hav (lt_trans hvv₀ hv₀b)
      have hCov₂ : ∀ v ∈ internalVertices τ₂,
          (v < v₀ → d₂ (Sum.inr v) ≥ 1) ∧
          (b < v → d₂ (Sum.inl v) ≥ 1) ∧
          (v₀ < v → v < b → d₂ (Sum.inr v) ≥ 1) := by
        intro v hv
        have hv_τ := hτ₂_int v hv
        have ⟨hc1, hc2, hc3⟩ := hCov v hv_τ
        have hv_ne_a : v ≠ a := by
          intro heq; subst heq
          have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
          cases τ with | nil => exact absurd rfl hne_τ | cons w rest =>
            simp at hHead; subst hHead
            simp only [internalVertices, List.tail_cons] at hv_τ
            exact ((List.nodup_cons.mp hND).1) ((List.dropLast_sublist _).mem hv_τ)
        -- d₂(inl v) = d_q(inl v) since eyv₀, eya are inr
        have hinl : d₂ (Sum.inl v) = d_q (Sum.inl v) := by
          simp only [hd₂_def, heyv₀_def, heya_def]
          simp [Finsupp.add_apply, Finsupp.tsub_apply]
        -- d₂(inr v) = d_q(inr v) when v ≠ v₀ and v ≠ a
        have hinr (hv₀' : v ≠ v₀) : d₂ (Sum.inr v) = d_q (Sum.inr v) := by
          simp only [hd₂_def, heyv₀_def, heya_def]
          unfold BinomialEdgeVars at *
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inr.injEq]
          rw [if_neg (Ne.symm hv₀'), if_neg (Ne.symm hv_ne_a)]; omega
        refine ⟨fun hvv₀ => ?_, fun hvb => ?_, fun hvv₀ hvb => ?_⟩
        · -- v < v₀: v ≠ v₀, and a < v (since v internal, v ≠ a) or v < a
          rw [hinr (ne_of_lt hvv₀)]
          rcases lt_or_ge v a with hva | hva
          · exact hc1 hva
          · exact hc3 (lt_of_le_of_ne hva (Ne.symm hv_ne_a)) (lt_trans hvv₀ hv₀b)
        · -- b < v
          rw [hinl]; exact hc2 hvb
        · -- v₀ < v < b
          rw [hinr (ne_of_gt hvv₀)]
          exact hc3 (lt_trans hav₀ hvv₀) hvb
      -- Apply IH (using y-variant for both sub-walks)
      have h₁ : binomialEdgeMonomialOrder.IsRemainder
          (monomial d₁ 1 * fij (K := K) a v₀) (groebnerBasisSet G) 0 :=
        ih a v₀ τ₁ d₁ hτ₁_len hav₀ hτ₁_head hτ₁_last hτ₁_nd hτ₁_walk hCov₁
      have h₂ : binomialEdgeMonomialOrder.IsRemainder
          (monomial d₂ 1 * fij (K := K) v₀ b) (groebnerBasisSet G) 0 :=
        ih v₀ b τ₂ d₂ hτ₂_len hv₀b hτ₂_head hτ₂_last hτ₂_nd hτ₂_walk hCov₂
      -- Algebraic identity and degree bounds
      have halg : monomial d_q (1 : K) * fij a b =
          monomial d₁ 1 * fij (K := K) a v₀ + monomial d₂ 1 * fij (K := K) v₀ b := by
        -- Factor: monomial d_q 1 = monomial (d_q - eyv₀) 1 * monomial eyv₀ 1
        have hle : eyv₀ ≤ d_q := by
          unfold BinomialEdgeVars at *; exact Finsupp.single_le_iff.mpr hcov_v₀
        have hfactor : (monomial d_q (1:K) : MvPolynomial (BinomialEdgeVars V) K) =
            monomial (d_q - eyv₀) (1:K) * monomial eyv₀ (1:K) := by
          rw [monomial_mul, one_mul, tsub_add_cancel_of_le hle]
        -- monomial eyv₀ 1 = y v₀
        have hyv₀ : (monomial eyv₀ (1:K) : MvPolynomial (BinomialEdgeVars V) K) = y v₀ := rfl
        -- Apply fij_telescope: y v₀ * fij a b = y b * fij a v₀ + y a * fij v₀ b
        rw [hfactor, mul_assoc,
            show monomial eyv₀ (1:K) * fij (K := K) a b = y v₀ * fij a b from by rw [← hyv₀],
            fij_telescope (K := K) a v₀ b, mul_add, ← mul_assoc, ← mul_assoc]
        -- Recombine monomials
        congr 1
        · congr 1
          show monomial (d_q - eyv₀) (1:K) * y (K := K) b = monomial d₁ 1
          change monomial (d_q - eyv₀) (1:K) * monomial eyb (1:K) = monomial d₁ 1
          rw [monomial_mul, one_mul]
        · congr 1
          show monomial (d_q - eyv₀) (1:K) * y (K := K) a = monomial d₂ 1
          change monomial (d_q - eyv₀) (1:K) * monomial eya (1:K) = monomial d₂ 1
          rw [monomial_mul, one_mul]
      -- Degree bounds for isRemainder_add (y-variant)
      -- The two terms have different degrees (discriminator at inr v₀).
      have hne_deg : binomialEdgeMonomialOrder.degree (monomial d₁ (1:K) * fij a v₀) ≠
                     binomialEdgeMonomialOrder.degree (monomial d₂ (1:K) * fij v₀ b) := by
        classical
        have hdeg1 : binomialEdgeMonomialOrder.degree (monomial d₁ (1:K) * fij a v₀) =
            d₁ + (Finsupp.single (Sum.inl a : BinomialEdgeVars V) 1 +
                   Finsupp.single (Sum.inr v₀ : BinomialEdgeVars V) 1) := by
          rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero) (fij_ne_zero a v₀ hav₀),
              degree_monomial, if_neg one_ne_zero, fij_degree a v₀ hav₀]
        have hdeg2 : binomialEdgeMonomialOrder.degree (monomial d₂ (1:K) * fij v₀ b) =
            d₂ + (Finsupp.single (Sum.inl v₀ : BinomialEdgeVars V) 1 +
                   Finsupp.single (Sum.inr b : BinomialEdgeVars V) 1) := by
          rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero) (fij_ne_zero v₀ b hv₀b),
              degree_monomial, if_neg one_ne_zero, fij_degree v₀ b hv₀b]
        -- Show the degree Finsupps differ at Sum.inr v₀:
        -- M1(inr v₀) = d_q(inr v₀), M2(inr v₀) = d_q(inr v₀) - 1
        rw [hdeg1, hdeg2]
        intro heq
        have hv := Finsupp.ext_iff.mp heq (Sum.inr v₀ : BinomialEdgeVars V)
        simp only [d₁, d₂, eyv₀, eyb, eya] at hv
        unfold BinomialEdgeVars at hv
        simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
          Sum.inr.injEq, reduceCtorEq, ite_true, ite_false,
          if_neg (ne_of_lt hav₀).symm, if_neg (ne_of_lt hv₀b),
          if_neg (ne_of_gt hv₀b), if_neg (ne_of_gt hav₀),
          if_neg (ne_of_lt hav₀), if_neg (ne_of_lt hv₀b)] at hv
        omega
      obtain ⟨hdeg₁, hdeg₂⟩ := degree_bounds_of_ne _ _ hne_deg
      rw [halg]
      exact isRemainder_add _ _ _ h₁ h₂ hdeg₁ hdeg₂
    · -- No bad vertices: extract admissible path directly
      push_neg at hBad
      have hne_τ : τ ≠ [] := fun h => by simp [h] at hHead
      have mem_internal : ∀ v ∈ τ, v ≠ a → v ≠ b → v ∈ internalVertices τ := by
        intro v hv hva hvb
        simp only [internalVertices]
        match τ, hHead, hLast, hND, hv, hne_τ with
        | a' :: rest, hH, hL, hN, hv', _ =>
          simp only [List.head?_cons, Option.some.injEq] at hH; subst hH
          simp only [List.tail_cons]
          have hv_rest : v ∈ rest := (List.mem_cons.mp hv').resolve_left hva
          have hrest_ne : rest ≠ [] := List.ne_nil_of_mem hv_rest
          refine List.mem_dropLast_of_mem_of_ne_getLast hv_rest (fun heq => hvb ?_)
          have hlast_eq := List.getLast_cons hrest_ne (a := a')
          have hb : (a' :: rest).getLast (List.cons_ne_nil a' rest) = b :=
            Option.some.inj ((List.getLast?_eq_some_getLast (List.cons_ne_nil a' rest)).symm.trans hL)
          rw [heq, ← hlast_eq, hb]
      have hVtx : ∀ v ∈ τ, v = a ∨ v = b ∨ v < a ∨ b < v := by
        intro v hv
        rcases eq_or_ne v a with rfl | hva
        · exact Or.inl rfl
        · rcases eq_or_ne v b with rfl | hvb
          · exact Or.inr (Or.inl rfl)
          · have hv_int := mem_internal v hv hva hvb
            rcases lt_or_ge v a with hlt | hge
            · exact Or.inr (Or.inr (Or.inl hlt))
            · have hva' : a < v := lt_of_le_of_ne hge (Ne.symm hva)
              have hbv := hBad v hv_int hva'
              exact Or.inr (Or.inr (Or.inr (lt_of_le_of_ne hbv (Ne.symm hvb))))
      obtain ⟨σ, hσ, hσ_sub⟩ := exists_admissible_path_of_walk G a b hab τ
        hHead hLast hND hVtx hWalk
      obtain ⟨d_σ, hd_σ⟩ := pathMonomial_is_monomial (K := K) a b σ
      have hσ_nd : σ.Nodup := hσ.2.2.2.1
      have hσ_int_nd : (internalVertices σ).Nodup :=
        (hσ_nd.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
      have hσ_head := hσ.2.1
      have hσ_last := hσ.2.2.1
      have hσ_ne : σ ≠ [] := by intro h; simp [h] at hσ_head
      have hint_σ_τ : ∀ v ∈ internalVertices σ, v ∈ internalVertices τ := by
        intro v hv_int_σ
        have hv_σ : v ∈ σ := (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_int_σ)
        have hv_τ : v ∈ τ := hσ_sub.mem hv_σ
        have hva : v ≠ a := by
          intro heq
          have hv_tail : v ∈ σ.tail := (List.dropLast_sublist _).mem hv_int_σ
          rw [heq] at hv_tail
          have : σ.head? = some a := hσ_head
          match σ, this, hσ_nd with
          | x :: rest, hh, hnd =>
            simp only [List.head?_cons, Option.some.injEq] at hh
            rw [hh] at hnd; exact (List.nodup_cons.mp hnd).1 hv_tail
        have hvb : v ≠ b := by
          intro heq
          rw [heq] at hv_int_σ
          match σ, hσ_head, hσ_last, hσ_nd with
          | x :: rest, hh, hl, hnd =>
            simp only [internalVertices, List.tail_cons] at hv_int_σ
            match rest, hv_int_σ with
            | y :: rest', hv_dp =>
              have hnd_rest := (List.nodup_cons.mp hnd).2
              have hb_last : (y :: rest').getLast (List.cons_ne_nil y rest') = b := by
                simp only [List.getLast?_cons_cons] at hl
                rw [List.getLast?_eq_some_getLast (List.cons_ne_nil y rest')] at hl
                exact Option.some.inj hl
              have : (y :: rest').dropLast ++ [(y :: rest').getLast (List.cons_ne_nil y rest')] =
                  y :: rest' := List.dropLast_append_getLast (List.cons_ne_nil y rest')
              rw [← this] at hnd_rest
              have hb_in_dp := hb_last ▸ hv_dp
              exact (List.nodup_append.mp hnd_rest).2.2 _ hb_in_dp _ (List.Mem.head _) rfl
        exact mem_internal v hv_τ hva hvb
      have hdiv : d_σ ≤ d_q := by
        intro w
        rcases w with ⟨v⟩ | ⟨v⟩
        · by_cases hv_filt : v ∈ (internalVertices σ).filter (fun w => b < w)
          · have hv_int_σ : v ∈ internalVertices σ := (List.mem_filter.mp hv_filt).1
            have hjv : b < v := of_decide_eq_true (List.mem_filter.mp hv_filt).2
            rw [pathMonomial_exponent_inl_one (K := K) a b σ v hv_int_σ hjv hσ_int_nd d_σ hd_σ]
            exact (hCov v (hint_σ_τ v hv_int_σ)).2.1 hjv
          · rw [pathMonomial_exponent_inl_zero (K := K) a b σ v hv_filt d_σ hd_σ]
            exact Nat.zero_le _
        · by_cases hv_filt : v ∈ (internalVertices σ).filter (fun w => w < a)
          · have hv_int_σ : v ∈ internalVertices σ := (List.mem_filter.mp hv_filt).1
            have hvi : v < a := of_decide_eq_true (List.mem_filter.mp hv_filt).2
            rw [pathMonomial_exponent_inr_one (K := K) a b σ v hv_int_σ hvi hσ_int_nd d_σ hd_σ]
            exact (hCov v (hint_σ_τ v hv_int_σ)).1 hvi
          · rw [pathMonomial_exponent_inr_zero (K := K) a b σ v hv_filt d_σ hd_σ]
            exact Nat.zero_le _
      exact isRemainder_fij_via_groebnerElement G a b σ hσ
        (monomial d_q 1) d_q rfl d_σ hd_σ hdiv

/-! ## Walk construction from shared-endpoint admissible paths -/

/-- Reversed walk preserves adjacency (graph is undirected). -/
private lemma chain'_reverse' (G : SimpleGraph V) (π : List V)
    (hW : π.Chain' (fun a b => G.Adj a b)) :
    π.reverse.Chain' (fun a b => G.Adj a b) := by
  change List.IsChain (fun a b => G.Adj a b) π.reverse
  rw [List.isChain_reverse]
  exact List.IsChain.imp (fun _ _ h => G.symm h) (hW : List.IsChain _ π)

/-- Internal vertices of a reversed list have the same membership as the original.
Both are "all elements except first and last", which are swapped by reversal. -/
private lemma internalVertices_reverse (l : List V) :
    internalVertices l.reverse = (internalVertices l).reverse := by
  simp only [internalVertices, List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]

private lemma mem_internalVertices_reverse {l : List V} {v : V}
    (h : v ∈ internalVertices l.reverse) : v ∈ internalVertices l := by
  rw [internalVertices_reverse] at h
  exact List.mem_reverse.mp h

/-! ### Helpers for walk construction -/

private lemma idxOf_lt {l : List V} {v : V} (hv : v ∈ l) : l.idxOf v < l.length :=
  List.findIdx_lt_length_of_exists ⟨v, hv, by simp [BEq.beq]⟩

private lemma head?_drop_idxOf {l : List V} {v : V} (hv : v ∈ l) :
    (l.drop (l.idxOf v)).head? = some v := by
  rw [List.head?_eq_getElem?, List.getElem?_drop]
  simp [List.getElem?_eq_getElem (idxOf_lt hv), List.getElem_idxOf (idxOf_lt hv)]

private lemma getLast?_drop_idxOf {l : List V} {v : V} (hv : v ∈ l) :
    (l.drop (l.idxOf v)).getLast? = l.getLast? := by
  have hne : l.drop (l.idxOf v) ≠ [] := by
    simp [List.drop_eq_nil_iff]; exact idxOf_lt hv
  rw [List.getLast?_eq_some_getLast hne,
      List.getLast?_eq_some_getLast (List.ne_nil_of_mem hv)]
  exact congrArg _ (List.getLast_drop hne)

private lemma isChain_drop {r : V → V → Prop} {l : List V} (h : l.IsChain r) (i : ℕ) :
    (l.drop i).IsChain r := by
  induction i generalizing l with
  | zero => simpa
  | succ n ih =>
    cases l with
    | nil => simp
    | cons a rest =>
      simp only [List.drop_succ_cons]
      cases h with
      | singleton _ => exact ih .nil
      | cons_cons _ h2 => exact ih h2

private lemma isChain_append {r : V → V → Prop} {l₁ l₂ : List V}
    (h₁ : l₁.IsChain r) (h₂ : l₂.IsChain r)
    (h : ∀ x, x ∈ l₁.getLast? → ∀ y, y ∈ l₂.head? → r x y) :
    (l₁ ++ l₂).IsChain r := by
  induction l₁ with
  | nil => simpa
  | cons a rest ih =>
    simp only [List.cons_append]
    cases rest with
    | nil =>
      simp at h
      cases l₂ with
      | nil => exact .singleton a
      | cons b rest₂ => exact .cons_cons (h b (by simp)) h₂
    | cons b rest' =>
      have h₁' : (b :: rest').IsChain r := by cases h₁ with | cons_cons _ h => exact h
      have hab : r a b := by cases h₁ with | cons_cons h _ => exact h
      exact .cons_cons hab (ih h₁' (by
        intro x hx y hy; apply h x _ y hy
        simp only [List.getLast?_cons_cons]; exact hx))

private lemma isChain_tail {r : V → V → Prop} {l : List V}
    (h : l.IsChain r) : l.tail.IsChain r := by
  cases h with
  | nil => exact .nil
  | singleton _ => exact .nil
  | cons_cons _ h2 => exact h2

private lemma mem_of_mem_internalVertices {l : List V} {v : V}
    (h : v ∈ internalVertices l) : v ∈ l :=
  (List.tail_sublist l).mem ((List.dropLast_sublist _).mem h)

private lemma getLast_not_mem_dropLast (l : List V) (hnd : l.Nodup) (hne : l ≠ []) :
    l.getLast hne ∉ l.dropLast := by
  rw [← List.dropLast_append_getLast hne] at hnd
  rw [List.nodup_append] at hnd
  intro h; exact absurd rfl (hnd.2.2 _ h _ (List.Mem.head []))

private lemma internal_ne_head {l : List V} (hnd : l.Nodup)
    {v : V} (hv : v ∈ internalVertices l) (hne : l ≠ []) : v ≠ l.head hne := by
  simp only [internalVertices] at hv
  cases l with
  | nil => exact absurd rfl hne
  | cons a rest =>
    simp only [List.tail_cons, List.head_cons] at hv ⊢
    intro heq; subst heq
    rw [List.nodup_cons] at hnd
    exact hnd.1 (List.dropLast_subset rest hv)

private lemma internal_ne_getLast {l : List V} (hnd : l.Nodup)
    {v : V} (hv : v ∈ internalVertices l) (hne : l ≠ []) : v ≠ l.getLast hne := by
  simp only [internalVertices] at hv
  cases l with
  | nil => exact absurd rfl hne
  | cons a rest =>
    simp only [List.tail_cons] at hv
    cases rest with
    | nil => simp at hv
    | cons b rest' =>
      simp only [List.getLast_cons (List.cons_ne_nil b rest')]
      have hnd_rest : (b :: rest').Nodup := by rw [List.nodup_cons] at hnd; exact hnd.2
      exact fun heq => by subst heq
                          exact getLast_not_mem_dropLast _ hnd_rest _ hv

-- Head/last from head?/getLast? as plain equalities
private lemma head_of_head? {l : List V} {a : V} (h : l.head? = some a) :
    l.head (by intro h'; simp [h'] at h) = a := by
  cases l with | nil => simp at h | cons x _ => simp at h; exact h

private lemma getLast_of_getLast? {l : List V} {a : V} (h : l.getLast? = some a) :
    l.getLast (by intro h'; simp [h'] at h) = a := by
  have hne : l ≠ [] := by intro h'; simp [h'] at h
  rw [List.getLast?_eq_some_getLast hne] at h; exact Option.some.inj h

-- v ∈ l, v ≠ head, v ≠ getLast → v ∈ internalVertices l
private lemma mem_internalVertices_of_ne {l : List V} {v : V}
    (hnd : l.Nodup) (hv : v ∈ l) (hne : l ≠ [])
    (hnh : v ≠ l.head hne) (hnl : v ≠ l.getLast hne) :
    v ∈ internalVertices l := by
  simp only [internalVertices]
  cases l with
  | nil => exact absurd rfl hne
  | cons x rest =>
    simp only [List.head_cons] at hnh
    simp only [List.tail_cons]
    have hv_rest : v ∈ rest := (List.mem_cons.mp hv).resolve_left hnh
    cases rest with
    | nil => exact absurd hv_rest (List.not_mem_nil)
    | cons y rest' =>
      have := List.getLast_cons (List.cons_ne_nil y rest') (a := x)
      rw [this] at hnl
      exact List.mem_dropLast_of_mem_of_ne_getLast hv_rest hnl

/-! ### The walk construction -/

private lemma walk_from_shared_first_aux (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b c : V) (π σ : List V),
    π.length + σ.length ≤ n →
    π.head? = some a → π.getLast? = some b →
    π.Nodup → π.Chain' (fun u v => G.Adj u v) →
    σ.head? = some a → σ.getLast? = some c →
    σ.Nodup → σ.Chain' (fun u v => G.Adj u v) →
    b ≠ c →
    ∃ τ : List V, τ.head? = some b ∧ τ.getLast? = some c ∧ τ.Nodup ∧
    τ.Chain' (fun u v => G.Adj u v) ∧
    (∀ v ∈ internalVertices τ,
      v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = a) := by
  intro n
  induction n with
  | zero =>
    intro a b c π σ hlen hπh
    have : π ≠ [] := by intro h; simp [h] at hπh
    have : 0 < π.length := by cases π with | nil => exact absurd rfl this | cons _ _ => simp
    omega
  | succ n ih =>
    intro a b c π σ hlen hπh hπl hπnd hπw hσh hσl hσnd hσw hbc
    have hπ_ne : π ≠ [] := by intro h; simp [h] at hπh
    have hσ_ne : σ ≠ [] := by intro h; simp [h] at hσh
    by_cases hshare : ∃ v ∈ σ.tail, v ∈ π
    · -- Recursive case: ∃ v ∈ σ.tail ∩ π with v ≠ a
      obtain ⟨v, hv_σt, hv_π⟩ := hshare
      have hv_σ : v ∈ σ := List.mem_of_mem_tail hv_σt
      have hva : v ≠ a := by
        intro heq; subst heq
        cases σ with
        | nil => simp at hσh
        | cons x rest =>
          simp at hσh; subst hσh
          rw [List.nodup_cons] at hσnd; exact absurd hv_σt hσnd.1
      -- idxOf v > 0 in σ since v ≠ head σ = a
      have hidx_pos : 0 < σ.idxOf v := by
        cases σ with
        | nil => exact absurd rfl hσ_ne
        | cons x rest =>
          have hxa : x = a := by simp at hσh; exact hσh
          show 0 < List.findIdx (fun w => w == v) (x :: rest)
          simp only [List.findIdx_cons]
          have hxv : ¬(x = v) := by rw [hxa]; exact Ne.symm hva
          simp only [BEq.beq, beq_iff_eq, hxv, ite_false]
          exact Nat.succ_pos _
      -- Apply IH with drops
      obtain ⟨τ, hτh, hτl, hτnd, hτw, hτcov⟩ := ih v b c
        (π.drop (π.idxOf v)) (σ.drop (σ.idxOf v))
        (by simp only [List.length_drop]
            have := idxOf_lt hv_π; have := idxOf_lt hv_σ; omega)
        (head?_drop_idxOf hv_π) (by rw [getLast?_drop_idxOf hv_π, hπl])
        (hπnd.sublist (List.drop_sublist _ _)) (isChain_drop hπw _)
        (head?_drop_idxOf hv_σ) (by rw [getLast?_drop_idxOf hv_σ, hσl])
        (hσnd.sublist (List.drop_sublist _ _)) (isChain_drop hσw _) hbc
      -- Translate coverage
      refine ⟨τ, hτh, hτl, hτnd, hτw, fun w hw => ?_⟩
      rcases hτcov w hw with h | h | h
      · -- w ∈ internalVertices (π.drop ..)
        have hw_π : w ∈ π := (List.drop_sublist _ _).mem (mem_of_mem_internalVertices h)
        by_cases hwa : w = a; · exact Or.inr (Or.inr hwa)
        have hπ'_ne : π.drop (π.idxOf v) ≠ [] := by
          simp [List.drop_eq_nil_iff]; exact idxOf_lt hv_π
        have hw_ne_b : w ≠ b := by
          intro heq; rw [heq] at h
          have := internal_ne_getLast (hπnd.sublist (List.drop_sublist _ _)) h hπ'_ne
          rw [getLast_of_getLast? (by rw [getLast?_drop_idxOf hv_π, hπl])] at this
          exact this rfl
        left; exact mem_internalVertices_of_ne hπnd hw_π hπ_ne
          (by rw [head_of_head? hπh]; exact hwa)
          (by rw [getLast_of_getLast? hπl]; exact hw_ne_b)
      · -- w ∈ internalVertices (σ.drop ..)
        have hw_σ : w ∈ σ := (List.drop_sublist _ _).mem (mem_of_mem_internalVertices h)
        by_cases hwa : w = a; · exact Or.inr (Or.inr hwa)
        have hσ'_ne : σ.drop (σ.idxOf v) ≠ [] := by
          simp [List.drop_eq_nil_iff]; exact idxOf_lt hv_σ
        have hw_ne_c : w ≠ c := by
          intro heq; rw [heq] at h
          have := internal_ne_getLast (hσnd.sublist (List.drop_sublist _ _)) h hσ'_ne
          rw [getLast_of_getLast? (by rw [getLast?_drop_idxOf hv_σ, hσl])] at this
          exact this rfl
        right; left; exact mem_internalVertices_of_ne hσnd hw_σ hσ_ne
          (by rw [head_of_head? hσh]; exact hwa)
          (by rw [getLast_of_getLast? hσl]; exact hw_ne_c)
      · -- w = v
        rw [h]
        by_cases hvb : v = b
        · -- v = b → v internal in σ
          right; left; exact mem_internalVertices_of_ne hσnd hv_σ hσ_ne
            (by rw [head_of_head? hσh]; exact hva)
            (by rw [getLast_of_getLast? hσl]; exact fun heq => hbc (hvb ▸ heq))
        · -- v ≠ b → v internal in π
          left; exact mem_internalVertices_of_ne hπnd hv_π hπ_ne
            (by rw [head_of_head? hπh]; exact hva)
            (by rw [getLast_of_getLast? hπl]; exact hvb)
    · -- Base case: σ.tail ∩ π = ∅
      push_neg at hshare
      by_cases hσt : σ.tail = []
      · -- σ = [a], c = a, τ = π.reverse
        have hac : c = a := by
          cases σ with
          | nil => simp at hσh
          | cons x rest =>
            simp at hσh hσt; subst hσh; subst hσt; simp at hσl; exact hσl.symm
        subst hac
        exact ⟨π.reverse,
          by rw [List.head?_reverse]; exact hπl,
          by rw [List.getLast?_reverse]; exact hπh,
          List.nodup_reverse.mpr hπnd,
          chain'_reverse' G π hπw,
          fun w hw => Or.inl (mem_internalVertices_reverse hw)⟩
      · -- σ.tail nonempty, τ = π.reverse ++ σ.tail
        have hτ_nd : (π.reverse ++ σ.tail).Nodup := by
          apply List.Nodup.append (List.nodup_reverse.mpr hπnd) (hσnd.sublist (List.tail_sublist _))
          intro w hw1 hw2; exact absurd (List.mem_reverse.mp hw1) (hshare w hw2)
        have hτ_ne : π.reverse ++ σ.tail ≠ [] := by simp [hπ_ne]
        refine ⟨π.reverse ++ σ.tail, ?_, ?_, hτ_nd, ?_, ?_⟩
        · -- head
          rw [List.head?_append]
          simp [List.head?_reverse, hπl]
        · -- last
          rw [List.getLast?_append_of_ne_nil _ hσt]
          cases σ with
          | nil => simp at hσh
          | cons x rest =>
            simp at hσt ⊢
            cases rest with
            | nil => exact absurd rfl hσt
            | cons y rest' => simp only [List.getLast?_cons_cons] at hσl ⊢; exact hσl
        · -- chain: π.reverse chain, σ.tail chain, connected at a
          apply isChain_append (chain'_reverse' G π hπw) (isChain_tail hσw)
          intro x hx y hy
          -- The isChain_append connection: need G.Adj x y
          -- where x ∈ (π.reverse).getLast? and y ∈ σ.tail.head?
          -- π.reverse.getLast? = π.head? = some a, so x = a
          -- σ.tail.head? for σ = s :: t :: _ is some t
          -- G.Adj s t from σ chain, and s = a, so G.Adj a t
          have hx_eq : x = a := by
            have : (π.reverse).getLast? = some a := by
              rw [List.getLast?_reverse]; exact hπh
            rw [this, Option.mem_def, Option.some.injEq] at hx; exact hx.symm
          rw [hx_eq]
          cases σ with
          | nil => simp at hσh
          | cons s rest =>
            cases rest with
            | nil => simp at hσt
            | cons t rest' =>
              have hy_eq : y = t := by
                simp only [List.tail_cons, List.head?_cons,
                  Option.mem_def, Option.some.injEq] at hy; exact hy.symm
              rw [hy_eq]
              have hs_eq : s = a := by simp at hσh; exact hσh
              rw [hs_eq] at hσw
              cases hσw with | cons_cons hadj _ => exact hadj
        · -- coverage
          intro w hw
          have hw_mem := mem_of_mem_internalVertices hw
          rw [List.mem_append] at hw_mem
          rcases hw_mem with hw_πr | hw_σt'
          · -- w ∈ π.reverse → w ∈ π
            rw [List.mem_reverse] at hw_πr
            by_cases hwa : w = a; · exact Or.inr (Or.inr hwa)
            have hw_ne_b : w ≠ b := by
              intro heq; rw [heq] at hw
              have hhead_eq : (π.reverse ++ σ.tail).head hτ_ne = b := by
                have : (π.reverse ++ σ.tail).head? = some b := by
                  rw [List.head?_append]; simp [List.head?_reverse, hπl]
                exact head_of_head? this
              exact absurd hhead_eq.symm (internal_ne_head hτ_nd hw hτ_ne)
            left; exact mem_internalVertices_of_ne hπnd hw_πr hπ_ne
              (by rw [head_of_head? hπh]; exact hwa)
              (by rw [getLast_of_getLast? hπl]; exact hw_ne_b)
          · -- w ∈ σ.tail → w ∈ σ
            have hw_σ : w ∈ σ := (List.tail_sublist σ).mem hw_σt'
            by_cases hwa : w = a; · exact Or.inr (Or.inr hwa)
            have hw_ne_c : w ≠ c := by
              intro heq; rw [heq] at hw
              have hτ_last_eq : (π.reverse ++ σ.tail).getLast hτ_ne = c := by
                rw [List.getLast_append_of_ne_nil _ hσt]
                -- σ.tail.getLast hσt = c
                -- σ.tail.getLast? = σ.getLast? (for len ≥ 2)
                have : σ.tail.getLast? = some c := by
                  cases σ with
                  | nil => simp at hσh
                  | cons x rest =>
                    simp at hσt; cases rest with
                    | nil => exact absurd rfl hσt
                    | cons y rest' =>
                      simp only [List.tail_cons, List.getLast?_cons_cons] at hσl ⊢
                      exact hσl
                exact getLast_of_getLast? this
              exact absurd hτ_last_eq.symm (internal_ne_getLast hτ_nd hw hτ_ne)
            right; left; exact mem_internalVertices_of_ne hσnd hw_σ hσ_ne
              (by rw [head_of_head? hσh]; exact hwa)
              (by rw [getLast_of_getLast? hσl]; exact hw_ne_c)

private lemma walk_from_shared_first (G : SimpleGraph V)
    (a b c : V) (π σ : List V)
    (hπ_head : π.head? = some a) (hπ_last : π.getLast? = some b)
    (hπ_nd : π.Nodup) (hπ_walk : π.Chain' (fun u v => G.Adj u v))
    (hσ_head : σ.head? = some a) (hσ_last : σ.getLast? = some c)
    (hσ_nd : σ.Nodup) (hσ_walk : σ.Chain' (fun u v => G.Adj u v))
    (hbc : b ≠ c) :
    ∃ τ : List V, τ.head? = some b ∧ τ.getLast? = some c ∧ τ.Nodup ∧
    τ.Chain' (fun u v => G.Adj u v) ∧
    (∀ v ∈ internalVertices τ,
      v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = a) :=
  walk_from_shared_first_aux G _ a b c π σ le_rfl
    hπ_head hπ_last hπ_nd hπ_walk hσ_head hσ_last hσ_nd hσ_walk hbc

/-! ## Theorem 2.1: Gröbner basis (Herzog direct S-polynomial approach)

The proof follows Herzog et al. (2010), Theorem 2.1, Second Step:
For any two admissible path binomials f_π1, f_π2 in G, show S(f_π1, f_π2)
reduces to 0 modulo G via Buchberger's criterion.

The key case analysis: when two paths share an endpoint, the S-polynomial
decomposes into a telescoping sum along the τ-path (concatenation of the
two paths), which provides a standard expression with remainder 0.
-/

/--
**Theorem 2.1** (Herzog et al. 2010): The set
  `{ u_π · f_{ij} | i < j, π admissible path from i to j in G }`
is a Gröbner basis of `J_G` with respect to the lex monomial order
`x_1 > ⋯ > x_n > y_1 > ⋯ > y_n`.

The proof has three steps:
1. `groebnerBasisSet_span`: `Ideal.span groebnerBasisSet = J_G`.
2. **This theorem**: Buchberger's criterion — all S-polynomials reduce to 0.
3. `theorem_2_1_reduced`: No leading monomial divides another (reducedness).

Reference: Herzog et al. (2010), Theorem 2.1.
-/

private lemma not_head_of_internal' (ρ : List V) (a : V)
    (hh : ρ.head? = some a) (hnd : ρ.Nodup) (v : V)
    (hv : v ∈ internalVertices ρ) : v ≠ a := by
  intro heq; rw [heq] at hv
  have := (List.dropLast_sublist _).mem hv
  match ρ, hh, hnd with
  | x :: rest, hh, hnd =>
    simp only [List.head?_cons, Option.some.injEq] at hh
    rw [hh] at hnd; exact (List.nodup_cons.mp hnd).1 this

private lemma not_last_of_internal' (ρ : List V) (a b : V)
    (hh : ρ.head? = some a) (hl : ρ.getLast? = some b) (hnd : ρ.Nodup) (v : V)
    (hv : v ∈ internalVertices ρ) : v ≠ b := by
  intro heq; rw [heq] at hv
  match ρ, hh, hl, hnd with
  | x :: rest, hh, hl, hnd =>
    simp only [internalVertices, List.tail_cons] at hv
    match rest, hv with
    | y :: rest', hv_dp =>
      have hnd_rest := (List.nodup_cons.mp hnd).2
      have hb_last : (y :: rest').getLast (List.cons_ne_nil y rest') = b := by
        simp only [List.getLast?_cons_cons] at hl
        rw [List.getLast?_eq_some_getLast (List.cons_ne_nil y rest')] at hl
        exact Option.some.inj hl
      have := List.dropLast_append_getLast (List.cons_ne_nil y rest')
      rw [← this] at hnd_rest
      exact (List.nodup_append.mp hnd_rest).2.2 _ (hb_last ▸ hv_dp) _ (List.Mem.head _) rfl

theorem theorem_2_1 (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis
      (groebnerBasisSet (K := K) G) (binomialEdgeIdeal (K := K) G) := by
  -- All groebnerElements have unit leading coefficients
  have hUnit : ∀ g ∈ groebnerBasisSet (K := K) G,
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g hg; obtain ⟨i, j, π, hπ, rfl⟩ := hg
    exact groebnerElement_leadingCoeff_isUnit i j π hπ
  -- Apply Buchberger criterion
  rw [show binomialEdgeIdeal (K := K) G = Ideal.span (groebnerBasisSet (K := K) G) from
    (groebnerBasisSet_span G).symm]
  rw [isGroebnerBasis_iff_sPolynomial_isRemainder (hG := hUnit)]
  -- For each pair of basis elements, show S-polynomial reduces to 0
  intro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
  obtain ⟨i, j, π, hπ, rfl⟩ := hg₁
  obtain ⟨k, l, σ, hσ, rfl⟩ := hg₂
  -- Case analysis on shared endpoints
  by_cases heq_i : i = k <;> by_cases heq_j : j = l
  · -- Case 1: i = k, j = l (same endpoints)
    -- S(u_π · f_{ij}, u_σ · f_{ij}) = 0 (monomial multiples of same polynomial)
    subst heq_i; subst heq_j
    change binomialEdgeMonomialOrder.IsRemainder
      (binomialEdgeMonomialOrder.sPolynomial
        (pathMonomial (K := K) i j π * fij i j)
        (pathMonomial (K := K) i j σ * fij i j))
      (groebnerBasisSet G) 0
    obtain ⟨dπ, hdπ⟩ := pathMonomial_is_monomial (K := K) i j π
    obtain ⟨dσ, hdσ⟩ := pathMonomial_is_monomial (K := K) i j σ
    rw [hdπ, hdσ, sPolynomial_monomial_mul, sPolynomial_self, mul_zero]
    exact isRemainder_zero_zero' _
  · -- Case 4: i = k, j ≠ l (shared first endpoint) — the hard case
    -- S-poly decomposes along the τ-path (concatenation of π and σ)
    subst heq_i
    -- Factor S-polynomial
    change binomialEdgeMonomialOrder.IsRemainder
      (binomialEdgeMonomialOrder.sPolynomial
        (pathMonomial (K := K) i j π * fij i j)
        (pathMonomial (K := K) i l σ * fij i l))
      (groebnerBasisSet G) 0
    obtain ⟨dπ, hdπ⟩ := pathMonomial_is_monomial (K := K) i j π
    obtain ⟨dσ, hdσ⟩ := pathMonomial_is_monomial (K := K) i l σ
    rw [hdπ, hdσ, sPolynomial_monomial_mul]
    have hij : i < j := hπ.1
    have hil : i < l := hσ.1
    rw [sPolynomial_fij_shared_first i j l hij hil heq_j]
    -- Goal: IsRemainder (monomial D (1*1) * (-(y i) * fij j l)) groebnerBasisSet 0
    set D := (dπ + binomialEdgeMonomialOrder.degree (fij (K := K) i j)) ⊔
             (dσ + binomialEdgeMonomialOrder.degree (fij (K := K) i l)) -
             binomialEdgeMonomialOrder.degree (fij (K := K) i j) ⊔
             binomialEdgeMonomialOrder.degree (fij (K := K) i l) with hD_def
    -- The full expression is -(monomial (D + single(inr i)) 1 * fij a b) for a < b
    -- D ≥ dπ and D ≥ dσ at all "internal" variables
    set E := D + (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ) with hE_def
    -- Shared helpers for both subcases
    have hπ_nd : (internalVertices π).Nodup :=
      (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
    have hσ_nd : (internalVertices σ).Nodup :=
      (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
    have hdeg_ij := fij_degree (K := K) i j hij
    have hdeg_il := fij_degree (K := K) i l hil
    have hfij_inr : ∀ v, v ≠ j → binomialEdgeMonomialOrder.degree (fij (K := K) i j) (Sum.inr v) = 0 := by
      intro v hne; rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr v from fun h => hne.symm (Sum.inr_injective h)]
    have hfil_inr : ∀ v, v ≠ l → binomialEdgeMonomialOrder.degree (fij (K := K) i l) (Sum.inr v) = 0 := by
      intro v hne; rw [hdeg_il, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr v from fun h => hne.symm (Sum.inr_injective h)]
    have hfij_inl : ∀ v, v ≠ i → binomialEdgeMonomialOrder.degree (fij (K := K) i j) (Sum.inl v) = 0 := by
      intro v hne; rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl v from fun h => hne.symm (Sum.inl_injective h)]
    have hfil_inl : ∀ v, v ≠ i → binomialEdgeMonomialOrder.degree (fij (K := K) i l) (Sum.inl v) = 0 := by
      intro v hne; rw [hdeg_il, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl v from fun h => hne.symm (Sum.inl_injective h)]
    have hE_ge_D : ∀ w, E w ≥ D w := by
      intro w; simp only [hE_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
    -- (using module-level not_head_of_internal' and not_last_of_internal')
    -- Coverage building blocks (shared between j<l and l<j subcases)
    have cov_inr_of_lt_i_π : ∀ v, v ∈ internalVertices π → v < i → E (Sum.inr v) ≥ 1 := by
      intro v hv_π hvi
      have := pathMonomial_exponent_inr_one (K := K) i j π v hv_π hvi hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inr v (ne_of_lt (lt_trans hvi hij)))
        (hfil_inr v (ne_of_lt (lt_trans hvi hil)))).1 (hE_ge_D _))
    have cov_inr_of_lt_i_σ : ∀ v, v ∈ internalVertices σ → v < i → E (Sum.inr v) ≥ 1 := by
      intro v hv_σ hvi
      have := pathMonomial_exponent_inr_one (K := K) i l σ v hv_σ hvi hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inr v (ne_of_lt (lt_trans hvi hij)))
        (hfil_inr v (ne_of_lt (lt_trans hvi hil)))).2 (hE_ge_D _))
    have cov_inl_of_gt_j : ∀ v, v ∈ internalVertices π → j < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_π hjv
      have := pathMonomial_exponent_inl_one (K := K) i j π v hv_π hjv hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inl v (ne_of_gt (lt_trans hij hjv)))
        (hfil_inl v (ne_of_gt (lt_trans hij hjv)))).1 (hE_ge_D _))
    have cov_inl_of_gt_l : ∀ v, v ∈ internalVertices σ → l < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_σ hlv
      have := pathMonomial_exponent_inl_one (K := K) i l σ v hv_σ hlv hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inl v (ne_of_gt (lt_trans hil hlv)))
        (hfil_inl v (ne_of_gt (lt_trans hil hlv)))).2 (hE_ge_D _))
    have cov_eq_i : E (Sum.inr i) ≥ 1 := by
      show (D + (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ)) (Sum.inr i) ≥ 1
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]; omega
    -- Both subcases reduce to: IsRemainder (monomial E 1 * fij a b) groebnerBasisSet 0
    -- where a = min(j,l), b = max(j,l)
    rcases lt_or_gt_of_ne heq_j with hjl | hlj
    · -- j < l: reduce to IsRemainder (monomial E 1 * fij j l) groebnerBasisSet 0
      suffices h : binomialEdgeMonomialOrder.IsRemainder
          (monomial E 1 * fij (K := K) j l) (groebnerBasisSet G) 0 by
        have heq : (monomial D) ((1 : K) * 1) * (-(y (K := K) i) * fij j l) =
            -(monomial E 1 * fij (K := K) j l) := by
          unfold BinomialEdgeVars at E D ⊢
          simp only [hE_def, one_mul, y, neg_mul, mul_neg]
          congr 1; rw [← mul_assoc]; congr 1
          change monomial D (1 : K) * monomial (Finsupp.single (Sum.inr i) 1) 1 = _
          rw [monomial_mul, one_mul]
        rw [heq]; exact isRemainder_neg' _ _ h
      obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
          ∃ τ : List V, τ.head? = some j ∧ τ.getLast? = some l ∧ τ.Nodup ∧
          τ.Chain' (fun u v => G.Adj u v) ∧
          (∀ v ∈ internalVertices τ,
            v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = i) := by
        exact walk_from_shared_first G i j l π σ
          hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 hπ.2.2.2.2.2.1
          hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.2.1 (ne_of_lt hjl)
      have hCov : ∀ v ∈ internalVertices τ,
          (v < j → E (Sum.inr v) ≥ 1) ∧
          (l < v → E (Sum.inl v) ≥ 1) ∧
          (j < v → v < l → E (Sum.inl v) ≥ 1) := by
        intro v hv_int
        rcases hτ_verts v hv_int with hv_π | hv_σ | hv_eq_i
        · have hv_mem : v ∈ π := (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv_π)
          have hv_ne_i := not_head_of_internal' π i hπ.2.1 hπ.2.2.2.1 v hv_π
          have hv_ne_j := not_last_of_internal' π i j hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 v hv_π
          rcases hπ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hjv
          · exact absurd rfl hv_ne_i
          · exact absurd rfl hv_ne_j
          · exact ⟨fun _ => cov_inr_of_lt_i_π v hv_π hvi,
                    fun hlv => absurd (lt_trans hvi (lt_trans hij hjl)) (not_lt.mpr (le_of_lt hlv)),
                    fun hjv' => absurd (lt_trans hvi hij) (not_lt.mpr (le_of_lt hjv'))⟩
          · exact ⟨fun hvj => absurd hjv (not_lt.mpr (le_of_lt hvj)),
                    fun _ => cov_inl_of_gt_j v hv_π hjv,
                    fun _ _ => cov_inl_of_gt_j v hv_π hjv⟩
        · have hv_mem : v ∈ σ := (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_σ)
          have hv_ne_i := not_head_of_internal' σ i hσ.2.1 hσ.2.2.2.1 v hv_σ
          have hv_ne_l := not_last_of_internal' σ i l hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 v hv_σ
          rcases hσ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hlv
          · exact absurd rfl hv_ne_i
          · exact absurd rfl hv_ne_l
          · exact ⟨fun _ => cov_inr_of_lt_i_σ v hv_σ hvi,
                    fun hlv => absurd (lt_trans hvi (lt_trans hij hjl)) (not_lt.mpr (le_of_lt hlv)),
                    fun hjv' => absurd (lt_trans hvi hij) (not_lt.mpr (le_of_lt hjv'))⟩
          · exact ⟨fun hvj => absurd (lt_trans hjl hlv) (not_lt.mpr (le_of_lt hvj)),
                    fun _ => cov_inl_of_gt_l v hv_σ hlv,
                    fun _ _ => cov_inl_of_gt_l v hv_σ hlv⟩
        · exact ⟨fun _ => hv_eq_i ▸ cov_eq_i,
                  fun hlv => absurd (lt_trans hij hjl) (not_lt.mpr (le_of_lt (hv_eq_i ▸ hlv))),
                  fun hjv => absurd hij (not_lt.mpr (le_of_lt (hv_eq_i ▸ hjv)))⟩
      exact isRemainder_fij_of_covered_walk G τ.length j l τ E le_rfl hjl
        hτ_head hτ_last hτ_nd hτ_walk hCov
    · -- l < j: symmetric, need admissible path from l to j
      suffices h : binomialEdgeMonomialOrder.IsRemainder
          (monomial E 1 * fij (K := K) l j) (groebnerBasisSet G) 0 by
        have heq : (monomial D) ((1 : K) * 1) * (-(y (K := K) i) * fij j l) =
            monomial E 1 * fij (K := K) l j := by
          unfold BinomialEdgeVars at E D ⊢
          simp only [hE_def, one_mul, y, neg_mul, mul_neg, fij_antisymm j l,
                     neg_neg, ← mul_assoc]
          congr 1
          change monomial D (1 : K) * monomial (Finsupp.single (Sum.inr i) 1) 1 = _
          rw [monomial_mul, one_mul]
        rw [heq]; exact h
      -- Goal: IsRemainder (monomial E 1 * fij l j) groebnerBasisSet 0
      -- Symmetric: walk from l to j through shared vertex i
      obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
          ∃ τ : List V, τ.head? = some l ∧ τ.getLast? = some j ∧ τ.Nodup ∧
          τ.Chain' (fun u v => G.Adj u v) ∧
          (∀ v ∈ internalVertices τ,
            v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = i) := by
        obtain ⟨τ', h1, h2, h3, h4, h5⟩ := walk_from_shared_first G i l j σ π
          hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.2.1
          hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 hπ.2.2.2.2.2.1 (ne_of_lt hlj)
        exact ⟨τ', h1, h2, h3, h4, fun v hv => by
          rcases h5 v hv with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)⟩
      have hCov : ∀ v ∈ internalVertices τ,
          (v < l → E (Sum.inr v) ≥ 1) ∧
          (j < v → E (Sum.inl v) ≥ 1) ∧
          (l < v → v < j → E (Sum.inl v) ≥ 1) := by
        intro v hv_int
        rcases hτ_verts v hv_int with hv_π | hv_σ | hv_eq_i
        · have hv_mem : v ∈ π := (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv_π)
          have hv_ne_i := not_head_of_internal' π i hπ.2.1 hπ.2.2.2.1 v hv_π
          have hv_ne_j := not_last_of_internal' π i j hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 v hv_π
          rcases hπ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hjv
          · exact absurd rfl hv_ne_i
          · exact absurd rfl hv_ne_j
          · exact ⟨fun _ => cov_inr_of_lt_i_π v hv_π hvi,
                    fun hjv => absurd (lt_trans hvi hij) (not_lt.mpr (le_of_lt hjv)),
                    fun hlv => absurd (lt_trans hvi hil) (not_lt.mpr (le_of_lt hlv))⟩
          · exact ⟨fun hvl => absurd (lt_trans hlj hjv) (not_lt.mpr (le_of_lt hvl)),
                    fun _ => cov_inl_of_gt_j v hv_π hjv,
                    fun _ _ => cov_inl_of_gt_j v hv_π hjv⟩
        · have hv_mem : v ∈ σ := (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_σ)
          have hv_ne_i := not_head_of_internal' σ i hσ.2.1 hσ.2.2.2.1 v hv_σ
          have hv_ne_l := not_last_of_internal' σ i l hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 v hv_σ
          rcases hσ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hlv
          · exact absurd rfl hv_ne_i
          · exact absurd rfl hv_ne_l
          · exact ⟨fun _ => cov_inr_of_lt_i_σ v hv_σ hvi,
                    fun hjv => absurd (lt_trans hvi hij) (not_lt.mpr (le_of_lt hjv)),
                    fun hlv => absurd (lt_trans hvi hil) (not_lt.mpr (le_of_lt hlv))⟩
          · exact ⟨fun hvl => absurd hlv (not_lt.mpr (le_of_lt hvl)),
                    fun _ => cov_inl_of_gt_l v hv_σ hlv,
                    fun _ _ => cov_inl_of_gt_l v hv_σ hlv⟩
        · exact ⟨fun _ => hv_eq_i ▸ cov_eq_i,
                  fun hjv => absurd hij (not_lt.mpr (le_of_lt (hv_eq_i ▸ hjv))),
                  fun hlv => absurd hil (not_lt.mpr (le_of_lt (hv_eq_i ▸ hlv)))⟩
      exact isRemainder_fij_of_covered_walk G τ.length l j τ E le_rfl hlj
        hτ_head hτ_last hτ_nd hτ_walk hCov
  · -- Case 5: j = l, i ≠ k (shared last endpoint) — symmetric to case 4
    subst heq_j
    -- Factor S-polynomial using sPolynomial_fij_shared_last
    change binomialEdgeMonomialOrder.IsRemainder
      (binomialEdgeMonomialOrder.sPolynomial
        (pathMonomial (K := K) i j π * fij i j)
        (pathMonomial (K := K) k j σ * fij k j))
      (groebnerBasisSet G) 0
    obtain ⟨dπ, hdπ⟩ := pathMonomial_is_monomial (K := K) i j π
    obtain ⟨dσ, hdσ⟩ := pathMonomial_is_monomial (K := K) k j σ
    rw [hdπ, hdσ, sPolynomial_monomial_mul]
    have hij : i < j := hπ.1
    have hkj : k < j := hσ.1
    rw [sPolynomial_fij_shared_last i k j hij hkj heq_i]
    -- Goal: IsRemainder (monomial D (1*1) * (x j * fij i k)) groebnerBasisSet 0
    set D := (dπ + binomialEdgeMonomialOrder.degree (fij (K := K) i j)) ⊔
             (dσ + binomialEdgeMonomialOrder.degree (fij (K := K) k j)) -
             binomialEdgeMonomialOrder.degree (fij (K := K) i j) ⊔
             binomialEdgeMonomialOrder.degree (fij (K := K) k j) with hD_def
    set E := D + (Finsupp.single (Sum.inl j) 1 : BinomialEdgeVars V →₀ ℕ) with hE_def
    -- Shared helpers for Case 5
    have hπ_nd : (internalVertices π).Nodup :=
      (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
    have hσ_nd : (internalVertices σ).Nodup :=
      (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
    have hdeg_ij := fij_degree (K := K) i j hij
    have hdeg_kj := fij_degree (K := K) k j hkj
    have hfij_inr : ∀ v, v ≠ j → binomialEdgeMonomialOrder.degree (fij (K := K) i j) (Sum.inr v) = 0 := by
      intro v hne; rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr v from fun h => hne.symm (Sum.inr_injective h)]
    have hfkj_inr : ∀ v, v ≠ j → binomialEdgeMonomialOrder.degree (fij (K := K) k j) (Sum.inr v) = 0 := by
      intro v hne; rw [hdeg_kj, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr v from fun h => hne.symm (Sum.inr_injective h)]
    have hfij_inl : ∀ v, v ≠ i → binomialEdgeMonomialOrder.degree (fij (K := K) i j) (Sum.inl v) = 0 := by
      intro v hne; rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl v from fun h => hne.symm (Sum.inl_injective h)]
    have hfkj_inl : ∀ v, v ≠ k → binomialEdgeMonomialOrder.degree (fij (K := K) k j) (Sum.inl v) = 0 := by
      intro v hne; rw [hdeg_kj, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl v from fun h => hne.symm (Sum.inl_injective h)]
    have hE_ge_D : ∀ w, E w ≥ D w := by
      intro w; simp only [hE_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
    -- Coverage building blocks for Case 5
    have cov_inr_of_lt_i_π : ∀ v, v ∈ internalVertices π → v < i → E (Sum.inr v) ≥ 1 := by
      intro v hv_π hvi
      have := pathMonomial_exponent_inr_one (K := K) i j π v hv_π hvi hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inr v (ne_of_lt (lt_trans hvi hij)))
        (hfkj_inr v (ne_of_lt (lt_trans hvi hij)))).1 (hE_ge_D _))
    have cov_inr_of_lt_k_σ : ∀ v, v ∈ internalVertices σ → v < k → E (Sum.inr v) ≥ 1 := by
      intro v hv_σ hvk
      have := pathMonomial_exponent_inr_one (K := K) k j σ v hv_σ hvk hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inr v (ne_of_lt (lt_trans hvk hkj)))
        (hfkj_inr v (ne_of_lt (lt_trans hvk hkj)))).2 (hE_ge_D _))
    have cov_inl_of_gt_j_π : ∀ v, v ∈ internalVertices π → j < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_π hjv
      have := pathMonomial_exponent_inl_one (K := K) i j π v hv_π hjv hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inl v (ne_of_gt (lt_trans hij hjv)))
        (hfkj_inl v (ne_of_gt (lt_trans hkj hjv)))).1 (hE_ge_D _))
    have cov_inl_of_gt_j_σ : ∀ v, v ∈ internalVertices σ → j < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_σ hjv
      have := pathMonomial_exponent_inl_one (K := K) k j σ v hv_σ hjv hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (hfij_inl v (ne_of_gt (lt_trans hij hjv)))
        (hfkj_inl v (ne_of_gt (lt_trans hkj hjv)))).2 (hE_ge_D _))
    have cov_eq_j : E (Sum.inl j) ≥ 1 := by
      show (D + (Finsupp.single (Sum.inl j) 1 : BinomialEdgeVars V →₀ ℕ)) (Sum.inl j) ≥ 1
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]; omega
    rcases lt_or_gt_of_ne heq_i with hik | hki
    · -- i < k: reduce to IsRemainder (monomial E 1 * fij i k) groebnerBasisSet 0
      suffices h : binomialEdgeMonomialOrder.IsRemainder
          (monomial E 1 * fij (K := K) i k) (groebnerBasisSet G) 0 by
        have heq : (monomial D) ((1 : K) * 1) * (x (K := K) j * fij i k) =
            monomial E 1 * fij (K := K) i k := by
          unfold BinomialEdgeVars at E D ⊢
          simp only [hE_def, one_mul, x, ← mul_assoc]; congr 1
          change monomial D (1 : K) * monomial (Finsupp.single (Sum.inl j) 1) 1 = _
          rw [monomial_mul, one_mul]
        rw [heq]; exact h
      obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
          ∃ τ : List V, τ.head? = some i ∧ τ.getLast? = some k ∧ τ.Nodup ∧
          τ.Chain' (fun u v => G.Adj u v) ∧
          (∀ v ∈ internalVertices τ,
            v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = j) := by
        -- Reverse paths: π.reverse goes j→i, σ.reverse goes j→k
        -- Use walk_from_shared_first with shared vertex j
        obtain ⟨τ', hτ'_head, hτ'_last, hτ'_nd, hτ'_walk, hτ'_verts⟩ :=
          walk_from_shared_first G j i k π.reverse σ.reverse
            (List.head?_reverse ▸ hπ.2.2.1)
            (List.getLast?_reverse ▸ hπ.2.1)
            (List.nodup_reverse.mpr hπ.2.2.2.1)
            (chain'_reverse' G π hπ.2.2.2.2.2.1)
            (List.head?_reverse ▸ hσ.2.2.1)
            (List.getLast?_reverse ▸ hσ.2.1)
            (List.nodup_reverse.mpr hσ.2.2.2.1)
            (chain'_reverse' G σ hσ.2.2.2.2.2.1)
            (ne_of_lt hik)
        exact ⟨τ', hτ'_head, hτ'_last, hτ'_nd, hτ'_walk, fun v hv => by
          rcases hτ'_verts v hv with h | h | h
          · exact Or.inl (mem_internalVertices_reverse h)
          · exact Or.inr (Or.inl (mem_internalVertices_reverse h))
          · exact Or.inr (Or.inr h)⟩
      -- Use y-variant: bad vertices (i < v < k) from σ's internals have y_v, not x_v
      have hCov : ∀ v ∈ internalVertices τ,
          (v < i → E (Sum.inr v) ≥ 1) ∧
          (k < v → E (Sum.inl v) ≥ 1) ∧
          (i < v → v < k → E (Sum.inr v) ≥ 1) := by
        intro v hv_int
        rcases hτ_verts v hv_int with hv_π | hv_σ | hv_eq_j
        · have hv_mem : v ∈ π := (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv_π)
          have hv_ne_i := not_head_of_internal' π i hπ.2.1 hπ.2.2.2.1 v hv_π
          have hv_ne_j := not_last_of_internal' π i j hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 v hv_π
          rcases hπ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hjv
          · exact absurd rfl hv_ne_i
          · exact absurd rfl hv_ne_j
          · exact ⟨fun _ => cov_inr_of_lt_i_π v hv_π hvi,
                    fun hkv => absurd (lt_trans hvi (lt_trans hik hkv)) (lt_irrefl _),
                    fun hiv => absurd hvi (not_lt.mpr (le_of_lt hiv))⟩
          · exact ⟨fun hvi' => absurd hjv (not_lt.mpr (le_of_lt (lt_trans hvi' hij))),
                    fun _ => cov_inl_of_gt_j_π v hv_π hjv,
                    fun _ hvk => absurd (lt_trans hvk (lt_trans hkj hjv)) (lt_irrefl _)⟩
        · have hv_mem : v ∈ σ := (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_σ)
          have hv_ne_k := not_head_of_internal' σ k hσ.2.1 hσ.2.2.2.1 v hv_σ
          have hv_ne_j := not_last_of_internal' σ k j hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 v hv_σ
          rcases hσ.2.2.2.2.1 v hv_mem with rfl | rfl | hvk | hjv
          · exact absurd rfl hv_ne_k
          · exact absurd rfl hv_ne_j
          · exact ⟨fun _ => cov_inr_of_lt_k_σ v hv_σ hvk,
                    fun hkv => absurd hkv (not_lt.mpr (le_of_lt hvk)),
                    fun _ _ => cov_inr_of_lt_k_σ v hv_σ hvk⟩
          · exact ⟨fun hvi' => absurd hjv (not_lt.mpr (le_of_lt (lt_trans hvi' hij))),
                    fun _ => cov_inl_of_gt_j_σ v hv_σ hjv,
                    fun _ hvk => absurd (lt_trans hvk (lt_trans hkj hjv)) (lt_irrefl _)⟩
        · exact ⟨fun hvj => absurd hij (not_lt.mpr (le_of_lt (hv_eq_j ▸ hvj))),
                  fun _ => hv_eq_j ▸ cov_eq_j,
                  fun _ hvk => absurd (lt_trans hkj (hv_eq_j ▸ hvk)) (lt_irrefl _)⟩
      exact isRemainder_fij_of_covered_walk_y G τ.length i k τ E le_rfl hik
        hτ_head hτ_last hτ_nd hτ_walk hCov
    · -- k < i: reduce to IsRemainder (monomial E 1 * fij k i) groebnerBasisSet 0
      suffices h : binomialEdgeMonomialOrder.IsRemainder
          (monomial E 1 * fij (K := K) k i) (groebnerBasisSet G) 0 by
        have heq : (monomial D) ((1 : K) * 1) * (x (K := K) j * fij i k) =
            -(monomial E 1 * fij (K := K) k i) := by
          unfold BinomialEdgeVars at E D ⊢
          simp only [hE_def, one_mul, x, neg_mul, mul_neg, fij_antisymm i k,
                     neg_neg, ← mul_assoc]
          congr 2
          change monomial D (1 : K) * monomial (Finsupp.single (Sum.inl j) 1) 1 = _
          rw [monomial_mul, one_mul]
        rw [heq]; exact isRemainder_neg' _ _ h
      obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
          ∃ τ : List V, τ.head? = some k ∧ τ.getLast? = some i ∧ τ.Nodup ∧
          τ.Chain' (fun u v => G.Adj u v) ∧
          (∀ v ∈ internalVertices τ,
            v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = j) := by
        -- Reverse paths: π.reverse goes j→i, σ.reverse goes j→k
        obtain ⟨τ', hτ'_head, hτ'_last, hτ'_nd, hτ'_walk, hτ'_verts⟩ :=
          walk_from_shared_first G j k i σ.reverse π.reverse
            (List.head?_reverse ▸ hσ.2.2.1)
            (List.getLast?_reverse ▸ hσ.2.1)
            (List.nodup_reverse.mpr hσ.2.2.2.1)
            (chain'_reverse' G σ hσ.2.2.2.2.2.1)
            (List.head?_reverse ▸ hπ.2.2.1)
            (List.getLast?_reverse ▸ hπ.2.1)
            (List.nodup_reverse.mpr hπ.2.2.2.1)
            (chain'_reverse' G π hπ.2.2.2.2.2.1)
            (ne_of_lt hki)
        exact ⟨τ', hτ'_head, hτ'_last, hτ'_nd, hτ'_walk, fun v hv => by
          rcases hτ'_verts v hv with h | h | h
          · exact Or.inr (Or.inl (mem_internalVertices_reverse h))
          · exact Or.inl (mem_internalVertices_reverse h)
          · exact Or.inr (Or.inr h)⟩
      -- Use y-variant: bad vertices from π's internals have y_v
      have hCov : ∀ v ∈ internalVertices τ,
          (v < k → E (Sum.inr v) ≥ 1) ∧
          (i < v → E (Sum.inl v) ≥ 1) ∧
          (k < v → v < i → E (Sum.inr v) ≥ 1) := by
        intro v hv_int
        rcases hτ_verts v hv_int with hv_π | hv_σ | hv_eq_j
        · have hv_mem : v ∈ π := (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv_π)
          have hv_ne_i := not_head_of_internal' π i hπ.2.1 hπ.2.2.2.1 v hv_π
          have hv_ne_j := not_last_of_internal' π i j hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 v hv_π
          rcases hπ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hjv
          · exact absurd rfl hv_ne_i
          · exact absurd rfl hv_ne_j
          · exact ⟨fun _ => cov_inr_of_lt_i_π v hv_π hvi,
                    fun hiv => absurd hvi (not_lt.mpr (le_of_lt hiv)),
                    fun _ _ => cov_inr_of_lt_i_π v hv_π hvi⟩
          · exact ⟨fun hvk => absurd (lt_trans hkj hjv) (not_lt.mpr (le_of_lt hvk)),
                    fun _ => cov_inl_of_gt_j_π v hv_π hjv,
                    fun _ hvi => absurd (lt_trans hvi (lt_trans hij hjv)) (lt_irrefl _)⟩
        · have hv_mem : v ∈ σ := (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_σ)
          have hv_ne_k := not_head_of_internal' σ k hσ.2.1 hσ.2.2.2.1 v hv_σ
          have hv_ne_j := not_last_of_internal' σ k j hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 v hv_σ
          rcases hσ.2.2.2.2.1 v hv_mem with rfl | rfl | hvk | hjv
          · exact absurd rfl hv_ne_k
          · exact absurd rfl hv_ne_j
          · exact ⟨fun _ => cov_inr_of_lt_k_σ v hv_σ hvk,
                    fun hiv => absurd (lt_trans hvk hki) (not_lt.mpr (le_of_lt hiv)),
                    fun hkv => absurd hvk (not_lt.mpr (le_of_lt hkv))⟩
          · exact ⟨fun hvk => absurd (lt_trans hkj hjv) (not_lt.mpr (le_of_lt hvk)),
                    fun _ => cov_inl_of_gt_j_σ v hv_σ hjv,
                    fun _ hvi => absurd (lt_trans hvi (lt_trans hij hjv)) (lt_irrefl _)⟩
        · exact ⟨fun hvk => absurd hkj (not_lt.mpr (le_of_lt (hv_eq_j ▸ hvk))),
                  fun _ => hv_eq_j ▸ cov_eq_j,
                  fun _ hvi => absurd hij (not_lt.mpr (le_of_lt (hv_eq_j ▸ hvi)))⟩
      exact isRemainder_fij_of_covered_walk_y G τ.length k i τ E le_rfl hki
        hτ_head hτ_last hτ_nd hτ_walk hCov
  · -- Cases 2 & 3: disjoint or cross-matched endpoints — coprime leading terms
    -- Factor: S(ge1, ge2) = monomial * S(fij i j, fij k l)
    change binomialEdgeMonomialOrder.IsRemainder
      (binomialEdgeMonomialOrder.sPolynomial
        (pathMonomial (K := K) i j π * fij i j)
        (pathMonomial (K := K) k l σ * fij k l))
      (groebnerBasisSet G) 0
    obtain ⟨dπ, hdπ⟩ := pathMonomial_is_monomial (K := K) i j π
    obtain ⟨dσ, hdσ⟩ := pathMonomial_is_monomial (K := K) k l σ
    rw [hdπ, hdσ, sPolynomial_monomial_mul]
    have hij : i < j := hπ.1
    have hkl : k < l := hσ.1
    rw [sPolynomial_fij_coprime i k j l hij hkl heq_i heq_j]
    -- Goal: IsRemainder (monomial D (1*1) * (x l * y k * fij i j - x j * y i * fij k l)) G 0
    -- Use the coprime swap identity to rewrite using pairs (i,k) and (j,l)
    -- This avoids the divisibility failure that occurs when k ∈ internalVertices π
    rw [fij_coprime_swap]
    -- Goal: IsRemainder (monomial D (1*1) * (x l * y j * fij i k - x k * y i * fij j l)) G 0
    sorry


/-! ## Degree computation helpers -/

/-- Exact degree of `∏ X(f w)` at `v`: equals 1 if `v ∈ l.map f`, else 0.
Requires `f` injective and `l` nodup so that the variable does not repeat. -/
private lemma prod_X_image_degree_eq' {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    [Nontrivial R] [DecidableEq σ] (f : V → σ) (hf : Function.Injective f) (l : List V)
    (hnd : l.Nodup) (m : MonomialOrder σ) (v : σ) :
    m.degree ((l.map (fun w => (X (f w) : MvPolynomial σ R))).prod) v =
    if v ∈ l.map f then 1 else 0 := by
  induction l with
  | nil => simp [degree_one]
  | cons a t ih =>
    have hnd' := List.Nodup.of_cons hnd
    simp only [List.map_cons, List.prod_cons, List.mem_cons]
    rw [degree_mul (X_ne_zero _) (List.prod_ne_zero (by simp [X_ne_zero])),
        Finsupp.add_apply, degree_X, Finsupp.single_apply, ih hnd']
    by_cases h1 : f a = v
    · have hnotin : v ∉ t.map f := by
        intro hmem
        obtain ⟨b, hb, hb_eq⟩ := List.mem_map.mp hmem
        exact (List.nodup_cons.mp hnd).1 (hf (h1.trans hb_eq.symm) ▸ hb)
      simp [h1, hnotin]
    · have h1' : ¬ (v = f a) := fun h => h1 h.symm
      simp [h1, h1']

/-- If `v ∉ image of f over l`, then the product `∏ X(f w)` has degree 0 at `v`. -/
private lemma prod_X_image_degree_zero' {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    [Nontrivial R] [DecidableEq σ] (f : V → σ) (l : List V) (m : MonomialOrder σ)
    (v : σ) (hv : v ∉ l.map f) :
    m.degree ((l.map (fun w => (X (f w) : MvPolynomial σ R))).prod) v = 0 := by
  induction l with
  | nil => simp [degree_one]
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons, List.mem_cons] at hv ⊢
    have ha : f a ≠ v := fun h => hv (Or.inl h.symm)
    have ht : v ∉ t.map f := fun h => hv (Or.inr h)
    rw [degree_mul (X_ne_zero _) (List.prod_ne_zero (by simp [X_ne_zero]))]
    simp [degree_X, Finsupp.add_apply, ha.symm, ih ht]

/-- The leading monomial of `groebnerElement i j π` at `Sum.inl v` is exactly
`if v = i ∨ v ∈ (internalVertices π).filter (· > j) then 1 else 0`.

That is, `inl v` appears (with exponent 1) iff v = i (from fij component) or
v is an internal vertex strictly above j (from the x-part of pathMonomial). -/
private lemma groebnerElement_degree_inl (G : SimpleGraph V)
    (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π) (v : V) :
    binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) (Sum.inl v) =
    if v = i ∨ v ∈ (internalVertices π).filter (fun w => j < w) then 1 else 0 := by
  obtain ⟨hij, _, _, hNodup, _, _, _⟩ := hπ
  have hint_nd : (internalVertices π).Nodup :=
    (hNodup.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  let xl := (internalVertices π).filter (fun w => j < w)
  let yl := (internalVertices π).filter (fun w => w < i)
  have hxne : (xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod ≠ 0 :=
    List.prod_ne_zero (by simp [X_ne_zero])
  have hyne : (yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod ≠ 0 :=
    List.prod_ne_zero (by simp [X_ne_zero])
  have hpm_eq : pathMonomial (K := K) i j π =
      (xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod *
      (yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod :=
    by simp [pathMonomial, x, y, xl, yl]
  have hfij_ne : (x i * y j - x j * y i : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := by
    intro hzero
    have hfij_zero : fij (K := K) i j = 0 := hzero
    have h := fij_leadingCoeff (K := K) i j hij
    rw [hfij_zero, MonomialOrder.leadingCoeff_zero] at h
    exact one_ne_zero h.symm
  have hpm_ne : pathMonomial (K := K) i j π ≠ 0 := hpm_eq ▸ mul_ne_zero hxne hyne
  change binomialEdgeMonomialOrder.degree
    (pathMonomial (K := K) i j π * (x i * y j - x j * y i)) (Sum.inl v) = _
  rw [degree_mul hpm_ne hfij_ne, Finsupp.add_apply, hpm_eq,
      degree_mul hxne hyne, Finsupp.add_apply]
  -- degree of x-product at inl v: equals 1 if v ∈ xl, 0 otherwise
  have hdegx : binomialEdgeMonomialOrder.degree
      ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inl v) =
      if v ∈ xl then 1 else 0 := by
    have h := prod_X_image_degree_eq' (R := K) Sum.inl Sum.inl_injective xl (hint_nd.filter _)
        binomialEdgeMonomialOrder (Sum.inl v)
    simp only [List.mem_map, Sum.inl.injEq, exists_eq_right] at h
    exact h
  -- degree of y-product at inl v: 0 (cross-type)
  have hdegy : binomialEdgeMonomialOrder.degree
      ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inl v) = 0 :=
    prod_X_image_degree_zero' Sum.inr yl _ _ (by simp)
  -- degree of fij at inl v: 1 if v = i, 0 otherwise
  have hfij_at_v : binomialEdgeMonomialOrder.degree
      (x i * y j - x j * y i : MvPolynomial (BinomialEdgeVars V) K) (Sum.inl v) =
      if v = i then 1 else 0 := by
    change binomialEdgeMonomialOrder.degree (fij (K := K) i j) (Sum.inl v) = _
    rw [fij_degree (K := K) i j hij]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    rcases eq_or_ne v i with rfl | hvi
    · simp
    · have h1 : ¬ (Sum.inl i : BinomialEdgeVars V) = Sum.inl v := fun h => hvi (Sum.inl.inj h).symm
      have h2 : ¬ (Sum.inr j : BinomialEdgeVars V) = Sum.inl v := Sum.inl_ne_inr.symm
      simp [h1, h2, hvi]
  -- i ∉ xl (xl has vertices > j > i)
  have hi_not_xl : i ∉ xl := by
    simp only [xl, List.mem_filter]
    intro ⟨_, hlt⟩; exact lt_irrefl i (lt_trans hij (of_decide_eq_true hlt))
  rw [hdegx, hdegy, hfij_at_v]
  simp only [add_zero]
  by_cases hvi : v = i
  · subst hvi
    rw [if_neg hi_not_xl, if_pos rfl, if_pos (Or.inl rfl)]
  · by_cases hvxl : v ∈ xl
    · rw [if_pos hvxl, if_neg hvi, if_pos (Or.inr hvxl)]
    · rw [if_neg hvxl, if_neg hvi, if_neg (not_or.mpr ⟨hvi, hvxl⟩)]

/-- The leading monomial of `groebnerElement i j π` at `Sum.inr v` is exactly
`if v = j ∨ v ∈ (internalVertices π).filter (· < i) then 1 else 0`. -/
private lemma groebnerElement_degree_inr (G : SimpleGraph V)
    (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π) (v : V) :
    binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) (Sum.inr v) =
    if v = j ∨ v ∈ (internalVertices π).filter (fun w => w < i) then 1 else 0 := by
  obtain ⟨hij, _, _, hNodup, _, _, _⟩ := hπ
  have hint_nd : (internalVertices π).Nodup :=
    (hNodup.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  let xl := (internalVertices π).filter (fun w => j < w)
  let yl := (internalVertices π).filter (fun w => w < i)
  have hxne : (xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod ≠ 0 :=
    List.prod_ne_zero (by simp [X_ne_zero])
  have hyne : (yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod ≠ 0 :=
    List.prod_ne_zero (by simp [X_ne_zero])
  have hpm_eq : pathMonomial (K := K) i j π =
      (xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod *
      (yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod :=
    by simp [pathMonomial, x, y, xl, yl]
  have hfij_ne : (x i * y j - x j * y i : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := by
    intro hzero
    have hfij_zero : fij (K := K) i j = 0 := hzero
    have h := fij_leadingCoeff (K := K) i j hij
    rw [hfij_zero, MonomialOrder.leadingCoeff_zero] at h
    exact one_ne_zero h.symm
  have hpm_ne : pathMonomial (K := K) i j π ≠ 0 := hpm_eq ▸ mul_ne_zero hxne hyne
  change binomialEdgeMonomialOrder.degree
    (pathMonomial (K := K) i j π * (x i * y j - x j * y i)) (Sum.inr v) = _
  rw [degree_mul hpm_ne hfij_ne, Finsupp.add_apply, hpm_eq,
      degree_mul hxne hyne, Finsupp.add_apply]
  -- degree of x-product at inr v: 0 (cross-type)
  have hdegx : binomialEdgeMonomialOrder.degree
      ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inr v) = 0 :=
    prod_X_image_degree_zero' Sum.inl xl _ _ (by simp)
  -- degree of y-product at inr v: 1 if v ∈ yl, 0 otherwise
  have hdegy : binomialEdgeMonomialOrder.degree
      ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inr v) =
      if v ∈ yl then 1 else 0 := by
    have h := prod_X_image_degree_eq' (R := K) Sum.inr Sum.inr_injective yl (hint_nd.filter _)
        binomialEdgeMonomialOrder (Sum.inr v)
    simp only [List.mem_map, Sum.inr.injEq, exists_eq_right] at h
    exact h
  -- degree of fij at inr v: 1 if v = j, 0 otherwise
  have hfij_at_v : binomialEdgeMonomialOrder.degree
      (x i * y j - x j * y i : MvPolynomial (BinomialEdgeVars V) K) (Sum.inr v) =
      if v = j then 1 else 0 := by
    change binomialEdgeMonomialOrder.degree (fij (K := K) i j) (Sum.inr v) = _
    rw [fij_degree (K := K) i j hij]
    simp only [Finsupp.add_apply, Finsupp.single_apply]
    rcases eq_or_ne v j with rfl | hvj
    · simp
    · have h1 : ¬ (Sum.inl i : BinomialEdgeVars V) = Sum.inr v := Sum.inl_ne_inr
      have h2 : ¬ (Sum.inr j : BinomialEdgeVars V) = Sum.inr v := fun h => hvj (Sum.inr.inj h).symm
      simp [h1, h2, hvj]
  -- j ∉ yl (yl has vertices < i < j)
  have hj_not_yl : j ∉ yl := by
    simp only [yl, List.mem_filter]
    intro ⟨_, hlt⟩; exact lt_irrefl j (lt_trans (of_decide_eq_true hlt) hij)
  rw [hdegx, hdegy, hfij_at_v]
  simp only [zero_add]
  by_cases hvj : v = j
  · subst hvj
    rw [if_neg hj_not_yl, if_pos rfl, if_pos (Or.inl rfl)]
  · by_cases hvyl : v ∈ yl
    · rw [if_pos hvyl, if_neg hvj, if_pos (Or.inr hvyl)]
    · rw [if_neg hvyl, if_neg hvj, if_neg (not_or.mpr ⟨hvj, hvyl⟩)]

/-- The degree of `groebnerElement i j π` at `Sum.inl i` is exactly 1. -/
private lemma groebnerElement_degree_at_inl_i (G : SimpleGraph V)
    (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π) :
    binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) (Sum.inl i) = 1 := by
  rw [groebnerElement_degree_inl G i j π hπ]; simp

/-- The degree of `groebnerElement i j π` at `Sum.inr j` is exactly 1. -/
private lemma groebnerElement_degree_at_inr_j (G : SimpleGraph V)
    (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π) :
    binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) (Sum.inr j) = 1 := by
  rw [groebnerElement_degree_inr G i j π hπ]; simp

/-- If two groebnerElements with the same endpoints (i, j) but different paths have
the degree of the first ≤ degree of the second, we reach a contradiction.
(The leading monomials of distinct admissible paths from i to j are incomparable.)

This uses the admissibility condition: no proper admissible sub-walk exists,
so the internal vertex sets cannot be nested. -/
private lemma groebnerElement_reduced_same_endpoints (G : SimpleGraph V)
    (i j : V) (π₁ : List V) (hπ₁ : IsAdmissiblePath G i j π₁)
    (π₂ : List V) (hπ₂ : IsAdmissiblePath G i j π₂) (hπ_ne : π₁ ≠ π₂)
    (hle : binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π₁) ≤
           binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π₂)) :
    False := by
  obtain ⟨hij, hπ₁_head, hπ₁_last, hπ₁_nd, hπ₁_vert, hπ₁_chain, hπ₁_min⟩ := hπ₁
  obtain ⟨_, hπ₂_head, hπ₂_last, hπ₂_nd, hπ₂_vert, hπ₂_chain, hπ₂_min⟩ := hπ₂
  have hπ₁_ne : π₁ ≠ [] := fun h => by simp [h] at hπ₁_head
  have hπ₂_ne : π₂ ≠ [] := fun h => by simp [h] at hπ₂_head
  -- Helper: v ∈ l ∧ v ≠ head ∧ v ≠ getLast → v ∈ internalVertices l
  have mem_int : ∀ (l : List V) (v : V) (hhead : l.head? = some i)
      (hlast : l.getLast? = some j) (hnd : l.Nodup) (hmem : v ∈ l)
      (hvi : v ≠ i) (hvj : v ≠ j), v ∈ internalVertices l := by
    intro l v hhead hlast hnd hmem hvi hvj
    have hne : l ≠ [] := fun h => by simp [h] at hhead
    simp only [internalVertices]
    have htail_ne : l.tail ≠ [] := by
      cases l with
      | nil => exact absurd rfl hne
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
        intro h; simp only [List.tail_cons] at h
        cases rest with
        | nil => simp only [List.getLast?_singleton, Option.some.injEq] at hlast
                 exact absurd hlast (ne_of_lt hij)
        | cons _ _ => exact absurd h (List.cons_ne_nil _ _)
    have hv_in_tail : v ∈ l.tail := by
      cases l with
      | nil => exact absurd rfl hne
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
        exact List.mem_of_ne_of_mem hvi hmem
    have htail_last : l.tail.getLast? = some j := by
      rw [List.getLast?_tail]
      have hlen_ne : l.length ≠ 1 := by
        cases l with
        | nil => exact absurd rfl hne
        | cons a rest =>
          simp only [List.head?_cons, Option.some.injEq] at hhead; subst hhead
          simp only [List.tail_cons] at htail_ne
          cases rest with
          | nil => exact absurd rfl htail_ne
          | cons _ _ => simp only [List.length_cons]; omega
      simp [hlen_ne, hlast]
    have hv_ne_last : v ≠ l.tail.getLast htail_ne := fun h =>
      hvj (Option.some.inj (h ▸ (List.getLast?_eq_some_getLast htail_ne).symm.trans htail_last))
    exact List.mem_dropLast_of_mem_of_ne_getLast hv_in_tail hv_ne_last
  -- j ∉ internalVertices l for admissible l ending at j
  have j_not_int : ∀ (l : List V), l ≠ [] → l.Nodup → l.getLast? = some j →
      j ∉ internalVertices l := by
    intro l hne hnd hlast
    have hj_not_drop : j ∉ l.dropLast := by
      have hj_last : l.getLast hne = j :=
        Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hlast)
      rw [← List.dropLast_append_getLast hne, hj_last] at hnd
      exact fun hd => (List.nodup_append.mp hnd).2.2 j hd j (List.mem_singleton_self j) rfl
    have hsublist : (internalVertices l).Sublist l.dropLast := by
      simp only [internalVertices]
      cases l with
      | nil => exact absurd rfl hne
      | cons a rest =>
        simp only [List.tail_cons]
        cases rest with
        | nil => simp
        | cons b rest2 =>
          simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _)]
          exact List.sublist_cons_self _ _
    exact fun hmem => hj_not_drop (hsublist.subset hmem)
  -- Step 1: int(π₁) ⊆ int(π₂) using degree bound
  have hint_sub : ∀ v ∈ internalVertices π₁, v ∈ internalVertices π₂ := by
    intro v hv
    have hv_in_π₁ : v ∈ π₁ :=
      (List.tail_sublist π₁).subset ((List.dropLast_sublist π₁.tail).subset hv)
    have hv_ne_i : v ≠ i := by
      intro heq; subst heq
      cases π₁ with
      | nil => exact absurd rfl hπ₁_ne
      | cons a rest =>
        simp only [List.head?_cons, Option.some.injEq] at hπ₁_head; subst hπ₁_head
        exact (List.nodup_cons.mp hπ₁_nd).1 ((List.dropLast_sublist _).subset hv)
    have hv_ne_j : v ≠ j := fun heq => j_not_int π₁ hπ₁_ne hπ₁_nd hπ₁_last (heq ▸ hv)
    rcases hπ₁_vert v hv_in_π₁ with rfl | rfl | hlt | hgt
    · exact absurd rfl hv_ne_i
    · exact absurd rfl hv_ne_j
    · -- v < i: use groebnerElement_degree_inr
      have hv_in_yl₁ : v ∈ (internalVertices π₁).filter (fun w => w < i) :=
        List.mem_filter.mpr ⟨hv, by simp [hlt]⟩
      have h1 : binomialEdgeMonomialOrder.degree
          (groebnerElement (K := K) i j π₁) (Sum.inr v) = 1 := by
        rw [groebnerElement_degree_inr G i j π₁
            ⟨hij, hπ₁_head, hπ₁_last, hπ₁_nd, hπ₁_vert, hπ₁_chain, hπ₁_min⟩]
        simp [hv_in_yl₁]
      have h_deg : 1 ≤ binomialEdgeMonomialOrder.degree
          (groebnerElement (K := K) i j π₂) (Sum.inr v) := h1 ▸ hle (Sum.inr v)
      rw [groebnerElement_degree_inr G i j π₂
        ⟨hij, hπ₂_head, hπ₂_last, hπ₂_nd, hπ₂_vert, hπ₂_chain, hπ₂_min⟩] at h_deg
      split_ifs at h_deg with h
      · rcases h with rfl | hyl₂
        · exact absurd (lt_trans hlt hij) (lt_irrefl _)
        · exact (List.mem_filter.mp hyl₂).1
      · norm_num at h_deg
    · -- v > j: use groebnerElement_degree_inl
      have hv_in_xl₁ : v ∈ (internalVertices π₁).filter (fun w => j < w) :=
        List.mem_filter.mpr ⟨hv, by simp [hgt]⟩
      have h1 : binomialEdgeMonomialOrder.degree
          (groebnerElement (K := K) i j π₁) (Sum.inl v) = 1 := by
        rw [groebnerElement_degree_inl G i j π₁
            ⟨hij, hπ₁_head, hπ₁_last, hπ₁_nd, hπ₁_vert, hπ₁_chain, hπ₁_min⟩]
        simp [hv_in_xl₁]
      have h_deg : 1 ≤ binomialEdgeMonomialOrder.degree
          (groebnerElement (K := K) i j π₂) (Sum.inl v) := h1 ▸ hle (Sum.inl v)
      rw [groebnerElement_degree_inl G i j π₂
        ⟨hij, hπ₂_head, hπ₂_last, hπ₂_nd, hπ₂_vert, hπ₂_chain, hπ₂_min⟩] at h_deg
      split_ifs at h_deg with h
      · rcases h with rfl | hxl₂
        · exact absurd (lt_trans hij hgt) (lt_irrefl _)
        · exact (List.mem_filter.mp hxl₂).1
      · norm_num at h_deg
  -- Step 2: all vertices of π₁ appear in π₂
  have hv_in_π₂ : ∀ v ∈ π₁, v ∈ π₂ := by
    intro v hv
    rcases hπ₁_vert v hv with rfl | rfl | hlt | hgt
    · exact List.mem_of_head? hπ₂_head
    · exact List.mem_of_getLast? hπ₂_last
    · exact (List.tail_sublist π₂).subset ((List.dropLast_sublist π₂.tail).subset
        (hint_sub v (mem_int π₁ v hπ₁_head hπ₁_last hπ₁_nd hv
          (ne_of_lt hlt) (ne_of_lt (lt_trans hlt hij)))))
    · exact (List.tail_sublist π₂).subset ((List.dropLast_sublist π₂.tail).subset
        (hint_sub v (mem_int π₁ v hπ₁_head hπ₁_last hπ₁_nd hv
          (ne_of_gt (lt_trans hij hgt)) (ne_of_gt hgt))))
  -- Step 3: find first difference position k (using Nat.find)
  have hex : ∃ m, (π₁[m]? : Option V) ≠ π₂[m]? :=
    not_forall.mp (hπ_ne ∘ List.ext_getElem?)
  set k := Nat.find hex
  have hk_ne : (π₁[k]? : Option V) ≠ π₂[k]? := Nat.find_spec hex
  have hk_min : ∀ m < k, (π₁[m]? : Option V) = π₂[m]? := fun m hm =>
    by_contra fun hm_ne => absurd (Nat.find_min hex hm) (not_not.mpr hm_ne)
  -- k ≥ 1 (both paths start at i)
  have hk_pos : 0 < k := by
    by_contra hk0; push_neg at hk0
    apply hk_ne; rw [Nat.le_zero.mp hk0]
    have h1 : (π₁[0]? : Option V) = some i := by
      rw [← List.head?_eq_getElem?]; exact hπ₁_head
    have h2 : (π₂[0]? : Option V) = some i := by
      rw [← List.head?_eq_getElem?]; exact hπ₂_head
    exact h1.trans h2.symm
  -- k < |π₁|
  have hk_lt_π₁ : k < π₁.length := by
    by_contra hk_ge; push_neg at hk_ge
    have h1 : (π₁[k]? : Option V) = none := List.getElem?_eq_none hk_ge
    rw [h1] at hk_ne
    -- π₂[k]? ≠ none, so k < |π₂|; all m < |π₁|: π₁[m]? = π₂[m]?
    -- j appears at positions |π₁|-1 and |π₂|-1 in π₂ → same position → |π₁| = |π₂| → contradiction
    have hcommon : ∀ m < π₁.length, (π₁[m]? : Option V) = π₂[m]? :=
      fun m hm => hk_min m (Nat.lt_of_lt_of_le hm hk_ge)
    have hπ₁_len_pos : 0 < π₁.length := by
      cases π₁ with | nil => simp at hπ₁_head | cons _ _ => simp
    have hlast_eq : (π₁[π₁.length - 1]? : Option V) = π₂[π₁.length - 1]? :=
      hcommon _ (by omega)
    rw [← List.getLast?_eq_getElem?, hπ₁_last] at hlast_eq
    -- j appears at π₁.length-1 and |π₂|-1 in π₂
    have hπ₂_lastpos := List.getLast?_eq_getElem? (l := π₂)
    rw [hπ₂_last] at hπ₂_lastpos
    have hpos1_lt : π₁.length - 1 < π₂.length := by
      by_contra hge; push_neg at hge
      rw [List.getElem?_eq_none hge] at hlast_eq; exact absurd hlast_eq (by simp)
    have hpos2_lt : π₂.length - 1 < π₂.length := by
      by_contra hge; push_neg at hge
      rw [List.getElem?_eq_none hge] at hπ₂_lastpos; exact absurd hπ₂_lastpos (by simp)
    have hj1 : π₂[π₁.length - 1]'hpos1_lt = j :=
      Option.some.inj ((List.getElem?_eq_getElem hpos1_lt).symm.trans hlast_eq.symm)
    have hj2 : π₂[π₂.length - 1]'hpos2_lt = j :=
      Option.some.inj ((List.getElem?_eq_getElem hpos2_lt).symm.trans hπ₂_lastpos.symm)
    have heq_pos := (List.Nodup.getElem_inj_iff hπ₂_nd
        (hi := hpos1_lt) (hj := hpos2_lt)).mp (hj1.trans hj2.symm)
    -- |π₁|-1 = |π₂|-1 → |π₁| = |π₂| → k ≥ |π₂| → π₂[k]? = none → contradiction
    exact hk_ne (List.getElem?_eq_none (by omega)).symm
  -- Let b = π₁[k] and set up n = π₂.idxOf b
  let b := π₁[k]'hk_lt_π₁
  have hb_in_π₂ : b ∈ π₂ := hv_in_π₂ b (List.getElem_mem hk_lt_π₁)
  set n := π₂.idxOf b
  have hn_lt : n < π₂.length := List.idxOf_lt_length_of_mem hb_in_π₂
  have hπ₂_at_n : π₂[n]'hn_lt = b := List.getElem_idxOf hn_lt
  -- b ∉ π₂.take k (same prefix as π₁.take k which is nodup at position k)
  have hb_not_take : b ∉ π₂.take k := by
    have htake_eq : π₂.take k = π₁.take k := by
      apply List.ext_getElem?; intro m
      simp only [List.getElem?_take]
      split_ifs with hm
      · exact (hk_min m hm).symm
      · rfl
    rw [htake_eq]
    intro h
    rw [List.mem_iff_getElem] at h
    obtain ⟨m, hm, hmeq⟩ := h
    simp only [List.length_take] at hm
    have hmk : m < k := Nat.lt_of_lt_of_le hm (Nat.min_le_left k π₁.length)
    rw [List.getElem_take] at hmeq
    exact absurd ((List.Nodup.getElem_inj_iff hπ₁_nd
        (hi := Nat.lt_trans hmk hk_lt_π₁) (hj := hk_lt_π₁)).mp hmeq) (by omega)
  -- k < |π₂| (b ∉ π₂.take k but b ∈ π₂ implies k < |π₂|)
  have hk_lt_π₂ : k < π₂.length := by
    rcases Nat.lt_or_ge k π₂.length with h | h
    · exact h
    · exact absurd hb_in_π₂ (List.take_of_length_le h ▸ hb_not_take)
  -- n > k
  have hn_gt_k : k < n := by
    have hn_ge : k ≤ n := by
      have heq := @List.idxOf_append V _ _ (π₂.take k) (π₂.drop k) b
      rw [List.take_append_drop] at heq
      have hn_unfold : n = List.idxOf b π₂ := rfl
      rw [hn_unfold, heq, if_neg hb_not_take]
      simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk_lt_π₂)]
      omega
    have hn_ne : n ≠ k := by
      intro heq
      have h_bk : π₂[k]'hk_lt_π₂ = b := by
        have h : π₂[n]'hn_lt = π₂[k]'hk_lt_π₂ := by congr 1
        exact h ▸ hπ₂_at_n
      have hπ₁k : (π₁[k]? : Option V) = some b := List.getElem?_eq_getElem hk_lt_π₁
      exact hk_ne (hπ₁k.trans (congrArg some h_bk ▸
        (List.getElem?_eq_getElem hk_lt_π₂).symm))
    omega
  -- Construct π' = π₂.take k ++ π₂.drop n (a proper sublist of π₂)
  let π' := π₂.take k ++ π₂.drop n
  have hπ'_sub : π'.Sublist π₂ :=
    List.take_append_drop n π₂ ▸
      List.Sublist.append (List.take_sublist_take_left (Nat.le_of_lt hn_gt_k)) (List.Sublist.refl _)
  have hπ'_ne : π' ≠ π₂ := fun heq => by
    have h_len : (π₂.take k ++ π₂.drop n).length = π₂.length := congrArg List.length heq
    simp only [List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left (Nat.le_of_lt hk_lt_π₂)] at h_len
    omega
  have hπ'_head : π'.head? = some i := by
    change (π₂.take k ++ π₂.drop n).head? = some i
    have htake_ne : π₂.take k ≠ [] := by
      rw [ne_eq, List.take_eq_nil_iff]; push_neg
      exact ⟨Nat.pos_iff_ne_zero.mp hk_pos, hπ₂_ne⟩
    rw [List.head?_append_of_ne_nil (π₂.take k) htake_ne, List.head?_take,
        if_neg (Nat.pos_iff_ne_zero.mp hk_pos), hπ₂_head]
  have hπ'_last : π'.getLast? = some j := by
    have hdrop_ne : π₂.drop n ≠ [] := by rw [ne_eq, List.drop_eq_nil_iff]; omega
    rw [List.getLast?_append, List.getLast?_drop, if_neg (by omega), hπ₂_last]
    simp
  have hπ'_chain : π'.Chain' (fun a b => G.Adj a b) := by
    change (π₂.take k ++ π₂.drop n).IsChain (fun a b => G.Adj a b)
    rw [List.isChain_append]
    refine ⟨List.IsChain.take hπ₂_chain k,
            List.IsChain.drop hπ₂_chain n, ?_⟩
    intro x hx y hy
    rw [List.getLast?_take, if_neg (Nat.pos_iff_ne_zero.mp hk_pos)] at hx
    rw [List.head?_drop] at hy
    have hk1_lt_π₂ : k - 1 < π₂.length := by omega
    have hx_val : π₂[k - 1]'hk1_lt_π₂ = x := by
      rw [Option.mem_def, List.getElem?_eq_getElem hk1_lt_π₂] at hx
      exact Option.some.inj hx
    have hy_val : π₂[n]'hn_lt = y :=
      Option.some.inj ((List.getElem?_eq_getElem hn_lt).symm.trans hy)
    have hk1_lt_π₁ : k - 1 < π₁.length := by omega
    have hπ₁k1 : π₁[k - 1]'hk1_lt_π₁ = π₂[k - 1]'hk1_lt_π₂ :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hk1_lt_π₁, ← List.getElem?_eq_getElem hk1_lt_π₂]
        exact hk_min (k - 1) (by omega))
    have hadj : G.Adj (π₁[k - 1]'hk1_lt_π₁) b := by
      have h := List.IsChain.getElem hπ₁_chain (k - 1) (by omega)
      simp only [Nat.sub_add_cancel hk_pos] at h
      exact h
    rw [← hx_val, ← hy_val, ← hπ₁k1, hπ₂_at_n]
    exact hadj
  exact hπ₂_min π' hπ'_sub hπ'_ne hπ'_head hπ'_last hπ'_chain
    (fun v hv => hπ₂_vert v (hπ'_sub.subset hv))

theorem theorem_2_1_reduced (G : SimpleGraph V)
    (i₁ j₁ : V) (π₁ : List V) (hπ₁ : IsAdmissiblePath G i₁ j₁ π₁)
    (i₂ j₂ : V) (π₂ : List V) (hπ₂ : IsAdmissiblePath G i₂ j₂ π₂)
    (hne : (i₁, j₁, π₁) ≠ (i₂, j₂, π₂)) :
    -- No leading monomial divides another
    ¬ (binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₁ j₁ π₁) ≤
       binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₂ j₂ π₂)) := by
  intro hle
  -- **Same endpoints, different paths** — handled by groebnerElement_reduced_same_endpoints
  by_cases hij_eq : (i₁, j₁) = (i₂, j₂)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hij_eq
    exact groebnerElement_reduced_same_endpoints G i₁ j₁ π₁ hπ₁ π₂ hπ₂
            (fun h => hne (by simp [h])) hle
  -- **Different endpoints** — derive contradiction from ordering
  -- From hle at inl i₁: i₁ = i₂ ∨ i₁ is an internal vertex of π₂ above j₂
  have hA : i₁ = i₂ ∨ i₁ ∈ (internalVertices π₂).filter (fun w => j₂ < w) := by
    have h_bound : 1 ≤ binomialEdgeMonomialOrder.degree
        (groebnerElement (K := K) i₂ j₂ π₂) (Sum.inl i₁) := by
      have := hle (Sum.inl i₁)
      rwa [groebnerElement_degree_at_inl_i G i₁ j₁ π₁ hπ₁] at this
    rw [groebnerElement_degree_inl G i₂ j₂ π₂ hπ₂] at h_bound
    split_ifs at h_bound with h
    · exact h
    · exact absurd h_bound (by norm_num)
  -- From hle at inr j₁: j₁ = j₂ ∨ j₁ is an internal vertex of π₂ below i₂
  have hB : j₁ = j₂ ∨ j₁ ∈ (internalVertices π₂).filter (fun w => w < i₂) := by
    have h_bound : 1 ≤ binomialEdgeMonomialOrder.degree
        (groebnerElement (K := K) i₂ j₂ π₂) (Sum.inr j₁) := by
      have := hle (Sum.inr j₁)
      rwa [groebnerElement_degree_at_inr_j G i₁ j₁ π₁ hπ₁] at this
    rw [groebnerElement_degree_inr G i₂ j₂ π₂ hπ₂] at h_bound
    split_ifs at h_bound with h
    · exact h
    · exact absurd h_bound (by norm_num)
  -- Case analysis: all four combinations lead to a contradiction
  have hij₁ := hπ₁.1  -- i₁ < j₁
  have hij₂ := hπ₂.1  -- i₂ < j₂
  rcases hA with rfl | hA_xl
  · -- i₁ = i₂: must have j₁ ≠ j₂ (since hij_eq says (i₁,j₁) ≠ (i₂,j₂) = (i₁,j₂))
    rcases hB with rfl | hB_yl
    · -- i₁ = i₂ AND j₁ = j₂: contradicts hij_eq
      exact hij_eq rfl
    · -- i₁ = i₂ AND j₁ ∈ yl₂ (j₁ < i₂ = i₁ < j₁): contradiction
      have hj₁_lt_i₁ : j₁ < i₁ :=
        of_decide_eq_true (List.mem_filter.mp hB_yl).2
      exact lt_irrefl j₁ (lt_trans hj₁_lt_i₁ hij₁)
  · -- i₁ ∈ xl₂: j₂ < i₁
    have hj₂_lt_i₁ : j₂ < i₁ := of_decide_eq_true (List.mem_filter.mp hA_xl).2
    rcases hB with rfl | hB_yl
    · -- j₁ = j₂ < i₁ < j₁: contradiction
      exact lt_irrefl j₁ (lt_trans hj₂_lt_i₁ hij₁)
    · -- j₁ ∈ yl₂ (j₁ < i₂) AND j₂ < i₁ < j₁ AND i₂ < j₂: cycle contradiction
      have hj₁_lt_i₂ : j₁ < i₂ := of_decide_eq_true (List.mem_filter.mp hB_yl).2
      exact lt_irrefl j₁ (lt_trans hj₁_lt_i₂ (lt_trans hij₂ (lt_trans hj₂_lt_i₁ hij₁)))

/-! ## Squarefree leading monomials -/

-- Helper lemmas `prod_X_image_degree_eq'`, `prod_X_image_degree_zero'` are defined above
-- (in the "Degree computation helpers" section).

/-- For a Nodup list and injective `f`, the product `∏ X(f w)` has degree ≤ 1 at every `v`. -/
private lemma prod_X_image_squarefree {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    [Nontrivial R] [DecidableEq σ] (f : V → σ) (hf : Function.Injective f) (l : List V)
    (hnd : l.Nodup) (m : MonomialOrder σ) (v : σ) :
    m.degree ((l.map (fun w => (X (f w) : MvPolynomial σ R))).prod) v ≤ 1 := by
  induction l with
  | nil => simp [degree_one]
  | cons a t ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [degree_mul (X_ne_zero _) (List.prod_ne_zero (by simp [X_ne_zero]))]
    simp only [Finsupp.add_apply, degree_X, Finsupp.single_apply]
    split_ifs with h
    · have ha_not_t : a ∉ t := (List.nodup_cons.mp hnd).1
      have hv_not_t : v ∉ t.map f := by
        intro hmem
        obtain ⟨b, hb_t, hb_eq⟩ := List.mem_map.mp hmem
        exact ha_not_t ((hf (h.trans hb_eq.symm)) ▸ hb_t)
      simp [prod_X_image_degree_zero' f t m v hv_not_t]
    · simp [ih (List.Nodup.of_cons hnd)]

/-! ## Corollary 2.2: J_G is radical -/

/--
**Corollary 2.2** (Herzog et al. 2010): `J_G` is a radical ideal.

**Proof**: By Theorem 2.1 the initial ideal `in_<(J_G)` is squarefree
(each leading monomial `u_π · x_i · y_j` has distinct variables). A general
result states that if `in_<(I)` is squarefree then `I` is radical.

Reference: Herzog et al. (2010), Corollary 2.2.
-/
theorem corollary_2_2 (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).IsRadical := by
  sorry

/--
The leading monomials of the Gröbner basis elements are squarefree:
each variable appears at most once in `u_π · x_i · y_j`.
-/
theorem groebnerElement_leadingMonomial_squarefree
    (G : SimpleGraph V) (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π)
    (v : BinomialEdgeVars V) :
    binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) v ≤ 1 := by
  obtain ⟨hij, hHead, hLast, hNodup, hInt, _⟩ := hπ
  have hne : π ≠ [] := by intro h; simp [h] at hHead
  have hint_nd : (internalVertices π).Nodup :=
    (hNodup.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  have hi_not_int : i ∉ internalVertices π := by
    simp only [internalVertices]; intro h
    cases π with
    | nil => exact absurd rfl hne
    | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
      exact (List.nodup_cons.mp hNodup).1 ((List.dropLast_sublist _).subset h)
  have hj_not_int : j ∉ internalVertices π := by
    simp only [internalVertices]; intro h
    have hj_last : π.getLast hne = j :=
      Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hLast)
    have hmem_dl : j ∈ π.dropLast := by
      cases π with
      | nil => exact absurd rfl hne
      | cons a rest =>
        simp only [List.tail_cons] at h; cases rest with
        | nil => simp at h
        | cons b rest2 =>
          rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b rest2)]
          exact List.mem_cons_of_mem a h
    have hj_count : π.count j = 1 :=
      Nat.le_antisymm (List.nodup_iff_count_le_one.mp hNodup _)
        (List.count_pos_iff.mpr (hj_last ▸ List.getLast_mem hne))
    have hpos : 0 < π.dropLast.count j := List.count_pos_iff.mpr hmem_dl
    have heq := congrArg (List.count j) (List.dropLast_append_getLast hne)
    simp only [List.count_append, hj_last, List.count_singleton_self] at heq
    omega
  have hpm_ne : pathMonomial (K := K) i j π ≠ 0 := by
    simp only [pathMonomial]
    exact mul_ne_zero
      (List.prod_ne_zero (by simp [x, X_ne_zero]))
      (List.prod_ne_zero (by simp [y, X_ne_zero]))
  have hfij_ne : (x i * y j - x j * y i : MvPolynomial (BinomialEdgeVars V) K) ≠ 0 := by
    have h : fij (K := K) i j ≠ 0 := by
      intro hzero
      have := fij_leadingCoeff (K := K) i j hij
      rw [hzero, MonomialOrder.leadingCoeff_zero] at this
      exact one_ne_zero this.symm
    exact h
  -- Decompose degree of groebnerElement = degree(pathMonomial) + degree(fij)
  show binomialEdgeMonomialOrder.degree (pathMonomial i j π * (x i * y j - x j * y i)) v ≤ 1
  rw [degree_mul hpm_ne hfij_ne, Finsupp.add_apply]
  -- Degree of fij at v
  have hfij_deg : (binomialEdgeMonomialOrder.degree (x i * y j - x j * y i :
      MvPolynomial (BinomialEdgeVars V) K)) v =
      (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1 : BinomialEdgeVars V →₀ ℕ) v :=
    congrFun (congrArg _ (fij_degree (K := K) i j hij)) v
  rw [Finsupp.add_apply] at hfij_deg
  simp only [Finsupp.single_apply] at hfij_deg
  -- Decompose degree of pathMonomial = degree(xProd) + degree(yProd)
  let xl := (internalVertices π).filter (fun w => j < w)
  let yl := (internalVertices π).filter (fun w => w < i)
  have hxne : (xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod ≠ 0 :=
    List.prod_ne_zero (by simp [X_ne_zero])
  have hyne : (yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod ≠ 0 :=
    List.prod_ne_zero (by simp [X_ne_zero])
  have hpm_split : binomialEdgeMonomialOrder.degree (pathMonomial (K := K) i j π) v =
      binomialEdgeMonomialOrder.degree
        ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) v +
      binomialEdgeMonomialOrder.degree
        ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) v := by
    have hpm_eq : pathMonomial (K := K) i j π =
        (xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod *
        (yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod := by
      simp [pathMonomial, x, y, xl, yl]
    rw [hpm_eq, degree_mul hxne hyne, Finsupp.add_apply]
  rw [hpm_split]
  cases v with
  | inl a =>
    have hdegy : binomialEdgeMonomialOrder.degree
        ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inl a) = 0 :=
      prod_X_image_degree_zero' Sum.inr _ _ _ (by simp)
    -- eliminate cross-type term: Sum.inr j ≠ Sum.inl a always
    have h_cross : (if Sum.inr j = Sum.inl a then (1 : ℕ) else 0) = 0 := if_neg (by simp)
    rw [h_cross, add_zero] at hfij_deg
    by_cases hai : a = i
    · subst hai
      have hdegx : binomialEdgeMonomialOrder.degree
          ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inl a) = 0 :=
        prod_X_image_degree_zero' Sum.inl _ _ _ (by
          intro hmem
          obtain ⟨w, hw, hw_eq⟩ := List.mem_map.mp hmem
          exact hi_not_int (Sum.inl_injective hw_eq ▸ (List.mem_filter.mp hw).1))
      rw [if_pos rfl] at hfij_deg
      omega
    · have hdegx : binomialEdgeMonomialOrder.degree
          ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inl a) ≤ 1 :=
        prod_X_image_squarefree Sum.inl Sum.inl_injective _ (hint_nd.filter _) _ _
      rw [if_neg (fun h => hai (Sum.inl_injective h).symm)] at hfij_deg
      omega
  | inr a =>
    have hdegx : binomialEdgeMonomialOrder.degree
        ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inr a) = 0 :=
      prod_X_image_degree_zero' Sum.inl _ _ _ (by simp)
    -- eliminate cross-type term: Sum.inl i ≠ Sum.inr a always
    have h_cross : (if Sum.inl i = Sum.inr a then (1 : ℕ) else 0) = 0 := if_neg (by simp)
    rw [h_cross, zero_add] at hfij_deg
    by_cases haj : a = j
    · subst haj
      have hdegy : binomialEdgeMonomialOrder.degree
          ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inr a) = 0 :=
        prod_X_image_degree_zero' Sum.inr _ _ _ (by
          intro hmem
          obtain ⟨w, hw, hw_eq⟩ := List.mem_map.mp hmem
          exact hj_not_int (Sum.inr_injective hw_eq ▸ (List.mem_filter.mp hw).1))
      rw [if_pos rfl] at hfij_deg
      omega
    · have hdegy : binomialEdgeMonomialOrder.degree
          ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inr a) ≤ 1 :=
        prod_X_image_squarefree Sum.inr Sum.inr_injective _ (hint_nd.filter _) _ _
      rw [if_neg (fun h => haj (Sum.inr_injective h).symm)] at hfij_deg
      omega

end

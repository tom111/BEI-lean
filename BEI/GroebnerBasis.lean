import BEI.AdmissiblePaths
import BEI.MonomialOrder
import BEI.GroebnerAPI
import BEI.ClosedGraphs
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

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

/--
**Theorem 2.1** (Herzog et al. 2010): The set
  `{ u_π · f_{ij} | i < j, π admissible path from i to j in G }`
is a reduced Gröbner basis of `J_G` with respect to the lex monomial order.

The proof proceeds in three steps:
1. Each `u_π · f_{ij} ∈ J_G` (see `groebnerElement_mem` in `AdmissiblePaths.lean`).
2. Buchberger: all S-polynomials reduce to 0 modulo the set.
3. Reducedness: no leading monomial divides another.

Reference: Herzog et al. (2010), Theorem 2.1.
-/
theorem theorem_2_1 (G : SimpleGraph V) :
    -- Part 1: the Gröbner basis set spans J_G
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


/-! ## Rauh's approach: crossing lemma and iterative reduction

The proof of `isRemainder_sPolynomial_fij_of_admissible` follows Rauh (arxiv:1210.7960),
Theorem 2.3. The key idea: any nonzero S-polynomial of two `fij`s can be written as
a difference of monomial-times-fij terms. Each such term `M * fij(a,b)` has a leading
monomial `M * x_a * y_b`. If the "variable assignment" is not antitone (i.e., the
monomial `M` is not a valid pathMonomial for any admissible path from `a` to `b`),
then some groebnerElement's leading term divides `M * x_a * y_b`, allowing reduction.
By well-founded induction on the monomial order, this process terminates at 0.

### Specialization to d₀ = 2

In the BEI case (d₀ = 2), a "crossing" in a monomial degree `d` at position `(a, b)`
means `a < b` with `d(inl a) ≥ 1` (x_a divides) and `d(inr b) ≥ 1` (y_b divides).
The pathMonomial of an admissible path from `a` to `b` consists of:
- `x_v` for internal vertices `v > b` (these have κ(v) = 1, i.e., inl)
- `y_v` for internal vertices `v < a` (these have κ(v) = 2, i.e., inr)

The antitone condition forces: smaller vertices get higher κ values (y-variables)
and larger vertices get lower κ values (x-variables). A crossing violates this.
-/
/-- If `∏ X(l_k) = monomial d 1` and `l.Nodup`, then `d t ≤ 1` for all `t`. -/
private lemma prod_X_list_exponent_le_one {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R]
    [DecidableEq σ]
    (l : List σ) (hnd : l.Nodup) (t : σ)
    (d : σ →₀ ℕ) (hd : (l.map (fun a => (X a : MvPolynomial σ R))).prod = monomial d 1) :
    d t ≤ 1 := by
  classical
  induction l generalizing d with
  | nil =>
    simp [List.map_nil, List.prod_nil] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    simp [← heq]
  | cons a l ih =>
    obtain ⟨d', hd'⟩ := prod_X_list_eq_monomial' (R := R) l
    simp only [List.map_cons, List.prod_cons, hd'] at hd
    change monomial (Finsupp.single a 1) 1 * monomial d' 1 = monomial d 1 at hd
    rw [monomial_mul, one_mul] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    rw [← heq]
    have hnd' := (List.nodup_cons.mp hnd).2
    have ha_notin := (List.nodup_cons.mp hnd).1
    by_cases hat : t = a
    · -- t = a: single a 1 contributes 1, d'(a) = 0 since a ∉ l
      subst hat
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
      have := prod_X_list_exponent_zero l t ha_notin d' hd'
      omega
    · -- t ≠ a: single contributes 0, use IH
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hat), zero_add]
      exact ih hnd' d' hd'

/-- The pathMonomial exponent is at most 1 at every position. -/
private lemma pathMonomial_exponent_le_one (i j : V) (π : List V)
    (hσ : IsAdmissiblePath G i j π) (w : BinomialEdgeVars V)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d w ≤ 1 := by
  obtain ⟨_, _, _, hNodup, _, _, _⟩ := hσ
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun v => j < v) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun v => v < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun v => j < v)).map
        (fun v => (X (Sum.inl v) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun v => j < v)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun v => v < i)).map
        (fun v => (X (Sum.inr v) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun v => v < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  have hint_nd : (internalVertices π).Nodup :=
    (hNodup.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  have inl_inj : Function.Injective (Sum.inl : V → BinomialEdgeVars V) :=
    Sum.inl_injective
  have inr_inj : Function.Injective (Sum.inr : V → BinomialEdgeVars V) :=
    Sum.inr_injective
  have hxl_nd : ((internalVertices π).filter (fun v => j < v) |>.map Sum.inl).Nodup :=
    List.Nodup.map inl_inj (hint_nd.filter _)
  have hyl_nd : ((internalVertices π).filter (fun v => v < i) |>.map Sum.inr).Nodup :=
    List.Nodup.map inr_inj (hint_nd.filter _)
  cases w with
  | inl v =>
    -- dy has only inr entries, so dy(inl v) = 0
    have hdy_zero : dy (Sum.inl v) = 0 := by
      apply prod_X_list_exponent_zero _ _ _ _ hdy
      simp only [List.mem_map, not_exists, not_and]
      intro w _ hweq; exact absurd hweq (by simp)
    have hdx_le := prod_X_list_exponent_le_one _ hxl_nd (Sum.inl v) _ hdx
    omega
  | inr v =>
    -- dx has only inl entries, so dx(inr v) = 0
    have hdx_zero : dx (Sum.inr v) = 0 := by
      apply prod_X_list_exponent_zero _ _ _ _ hdx
      simp only [List.mem_map, not_exists, not_and]
      intro w _ hweq; exact absurd hweq (by simp)
    have hdy_le := prod_X_list_exponent_le_one _ hyl_nd (Sum.inr v) _ hdy
    omega

/-- The pathMonomial exponent at `Sum.inl v` is 0 when `v ∉ (internalVertices σ).filter (j < ·)`.
Strengthens `pathMonomial_exponent_inl_of_le` to also cover `v ∈ internals` with `v ≤ j`. -/
private lemma pathMonomial_exponent_inl_zero_of_not_mem
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
    simp only [List.mem_map, Sum.inl.injEq, not_exists, not_and]
    intro w hw hweq; exact hv (hweq ▸ hw)
  have hdy_zero : dy (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, not_exists, not_and]
    intro w _ hweq; exact absurd hweq (by simp)
  omega

/-- The pathMonomial exponent at `Sum.inr v` is 0 when `v ∉ (internalVertices σ).filter (· < i)`. -/
private lemma pathMonomial_exponent_inr_zero_of_not_mem
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
    simp only [List.mem_map, not_exists, not_and]
    intro w _ hweq; exact absurd hweq (by simp)
  have hdy_zero : dy (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, Sum.inr.injEq, not_exists, not_and]
    intro w hw hweq; exact hv (hweq ▸ hw)
  omega

private lemma pathMonomial_degree_le_of_supported (i j : V) (σ : List V)
    (hσ : IsAdmissiblePath G i j σ)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hx : ∀ v ∈ internalVertices σ, j < v → 1 ≤ d (Sum.inl v))
    (hy : ∀ v ∈ internalVertices σ, v < i → 1 ≤ d (Sum.inr v)) :
    ∀ (d_σ : BinomialEdgeVars V →₀ ℕ),
      pathMonomial (K := K) i j σ = monomial d_σ 1 → d_σ ≤ d := by
  intro d_σ hd_σ w
  rcases w with v | v
  · -- w = Sum.inl v
    by_cases hv_mem : v ∈ (internalVertices σ).filter (fun w => j < w)
    · -- v is an internal vertex with j < v: d_σ(inl v) = 1 and d(inl v) ≥ 1
      have h_le := pathMonomial_exponent_le_one (G := G) i j σ hσ (Sum.inl v) d_σ hd_σ
      have h_sup := hx v (List.mem_filter.mp hv_mem).1
        (of_decide_eq_true (List.mem_filter.mp hv_mem).2)
      omega
    · -- v is NOT in the filtered list: d_σ(inl v) = 0
      have := pathMonomial_exponent_inl_zero_of_not_mem (K := K) i j σ v hv_mem d_σ hd_σ
      omega
  · -- w = Sum.inr v: symmetric
    by_cases hv_mem : v ∈ (internalVertices σ).filter (fun w => w < i)
    · have h_le := pathMonomial_exponent_le_one (G := G) i j σ hσ (Sum.inr v) d_σ hd_σ
      have h_sup := hy v (List.mem_filter.mp hv_mem).1
        (of_decide_eq_true (List.mem_filter.mp hv_mem).2)
      omega
    · have := pathMonomial_exponent_inr_zero_of_not_mem (K := K) i j σ v hv_mem d_σ hd_σ
      omega

/-- Internal vertices of a list are members of the list. -/
private lemma internalVertices_mem (π : List V) (v : V)
    (hv : v ∈ internalVertices π) : v ∈ π := by
  simp only [internalVertices] at hv
  exact List.tail_subset _ (List.dropLast_subset _ hv)

/-! ## Rauh's core divisibility claim

The key to proving `groebnerBasisSet` is a Gröbner basis (Theorem 2.1) is showing that
every nonzero element of `J_G` has its leading monomial divisible by some groebnerElement's
leading monomial.

**Previous approach (ABANDONED)**: Factor S(ge₁,ge₂) = monomial D · S(fij₁,fij₂) and prove
IsRemainder for the inner S-polynomial. This is **WRONG** because S(fij₁,fij₂) need not be
in J_G (e.g., fij(3,5) ∉ J_G when 3-5 is not an edge, even if admissible paths exist for
the original pairs through a common vertex).

**Current approach (Rauh, arxiv:1210.7960, Theorem 2)**: Prove the leading-term divisibility
claim directly, then derive IsGroebnerBasis via `exists_isRemainder` + irredundancy.

For any nonzero f ∈ J_G, the leading monomial has a "crossing" (∃ a < b with x_a | LM
and y_b | LM), because J_G is Z^V-homogeneous and contains no monomials. The crossing
yields an admissible path a→b whose groebnerElement's LT divides LM(f). -/

/-! ### Assembly: Rauh's core divisibility claim -/

/-- **Core claim (Rauh, Theorem 2)**: For any nonzero `f ∈ J_G`, some groebnerElement's
leading monomial divides `f`'s leading monomial (componentwise ≤ on Finsupp).

**Proof**: TODO — Rauh's approach. See `BEI/HerzogLemmas.lean` for the archived false
approach. The correct proof needs `HasCrossing` + an admissible path extraction argument. -/
private lemma exists_groebnerElement_degree_le (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G) (hf_ne : f ≠ 0) :
    ∃ g ∈ groebnerBasisSet (K := K) G,
      binomialEdgeMonomialOrder.degree g ≤ binomialEdgeMonomialOrder.degree f := by
  sorry

/-- Any element of `J_G` reduces to remainder 0 modulo `groebnerBasisSet`.
Follows from `exists_groebnerElement_degree_le` (Rauh's core claim) +
`exists_isRemainder` + irredundancy. -/
private lemma isRemainder_of_mem_ideal (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ Ideal.span (groebnerBasisSet (K := K) G)) :
    binomialEdgeMonomialOrder.IsRemainder f (groebnerBasisSet (K := K) G) 0 := by
  have hUnit : ∀ g ∈ groebnerBasisSet (K := K) G,
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g hg; obtain ⟨i, j, π, hπ, rfl⟩ := hg
    exact groebnerElement_leadingCoeff_isUnit i j π hπ
  -- Get some remainder r via the division algorithm
  obtain ⟨r, ⟨⟨coeff, hsum, hdeg⟩, hirr⟩⟩ :=
    binomialEdgeMonomialOrder.exists_isRemainder hUnit f
  -- It suffices to show r = 0
  suffices hr_zero : r = 0 by
    subst hr_zero; exact ⟨⟨coeff, by simpa using hsum, hdeg⟩, by simpa using hirr⟩
  by_contra r_ne
  -- r ∈ J_G: since f ∈ span(G) and the linear combination is in span(G)
  have hlin_mem : Finsupp.linearCombination _ (fun (b : ↥(groebnerBasisSet (K := K) G)) ↦
      b.val) coeff ∈ Ideal.span (groebnerBasisSet (K := K) G) := by
    simp only [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun b _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span b.prop)
  have hr_sub : f - Finsupp.linearCombination _ (fun (b : ↥(groebnerBasisSet (K := K) G)) ↦
      b.val) coeff ∈ Ideal.span (groebnerBasisSet (K := K) G) :=
    (Ideal.span (groebnerBasisSet (K := K) G)).sub_mem hf_mem hlin_mem
  have hr_eq : f - Finsupp.linearCombination _ (fun (b : ↥(groebnerBasisSet (K := K) G)) ↦
      b.val) coeff = r := by rw [hsum]; ring
  have hr_mem : r ∈ Ideal.span (groebnerBasisSet (K := K) G) := hr_eq ▸ hr_sub
  -- Apply the core claim: some groebnerElement's LT divides r's LT
  rw [← show binomialEdgeIdeal (K := K) G = Ideal.span (groebnerBasisSet (K := K) G) from
    (theorem_2_1 G).symm] at hr_mem
  obtain ⟨ge, hge_mem, hge_div⟩ := exists_groebnerElement_degree_le G r hr_mem r_ne
  -- Contradiction: r's leading monomial is in its support but divisible by ge's LT
  exact hirr _ (binomialEdgeMonomialOrder.degree_mem_support r_ne) ge hge_mem hge_div

/-! ## Theorem 2.1: Gröbner basis -/

/--
**Theorem 2.1** (Herzog et al. 2010, main part): The set `groebnerBasisSet G` is a Gröbner basis
of `J_G` with respect to the lex monomial order.

**Proof**: By Buchberger's criterion, it suffices to show that all S-polynomials of
basis elements reduce to 0. Since each S-polynomial lies in `J_G = Ideal.span(groebnerBasisSet)`,
this follows from `isRemainder_of_mem_ideal`, which itself relies on
`exists_groebnerElement_degree_le` (Rauh's core claim).

Reference: Rauh (2013), Theorem 2; originally Herzog et al. (2010), Theorem 2.1.
-/
theorem theorem_2_1_groebner (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis
      (groebnerBasisSet (K := K) G) (binomialEdgeIdeal (K := K) G) := by
  rw [show binomialEdgeIdeal (K := K) G = Ideal.span (groebnerBasisSet (K := K) G) from
    (theorem_2_1 G).symm]
  rw [isGroebnerBasis_iff_sPolynomial_isRemainder (hG := fun g hg => by
    obtain ⟨i, j, π, hπ, rfl⟩ := hg
    exact groebnerElement_leadingCoeff_isUnit i j π hπ)]
  intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
  exact isRemainder_of_mem_ideal G _
    (sPolynomial_mem_ideal (Ideal.subset_span he₁) (Ideal.subset_span he₂))

theorem theorem_2_1_leading (G : SimpleGraph V) (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) (hf0 : f ≠ 0) :
    -- The leading term of f is divisible by some leading term in the basis set
    ∃ (i j : V) (π : List V) (_ : IsAdmissiblePath G i j π),
      binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) ≤
      binomialEdgeMonomialOrder.degree f := by
  -- Follows from theorem_2_1_groebner: the IsGroebnerBasis condition gives
  -- span(lt(I)) = span(lt(G)), so lt(f) ∈ span(lt(G)), and some basis element
  -- has leading monomial dividing lt(f).
  obtain ⟨_, hInitIdeal⟩ := theorem_2_1_groebner (K := K) G
  -- lt(f) ∈ span(lt(binomialEdgeIdeal G))
  have hlt_mem : binomialEdgeMonomialOrder.leadingTerm f ∈
      Ideal.span (binomialEdgeMonomialOrder.leadingTerm ''
        ↑(binomialEdgeIdeal (K := K) G)) :=
    Ideal.subset_span ⟨f, hf, rfl⟩
  -- Rewrite using hGB: span(lt(I)) = span(lt(G))
  rw [hInitIdeal] at hlt_mem
  -- All groebnerBasisSet elements have unit leading coefficients
  have hG_units : ∀ g ∈ (groebnerBasisSet (K := K) G),
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g ⟨i, j, π, hπ, hge⟩
    rw [hge]; exact groebnerElement_leadingCoeff_isUnit i j π hπ
  -- Rewrite span(lt(G)) = span({monomial(deg g) 1 : g ∈ G})
  rw [span_leadingTerm_eq_span_monomial hG_units,
      ← Set.image_image (fun s => monomial s (1 : K)) binomialEdgeMonomialOrder.degree,
      mem_ideal_span_monomial_image] at hlt_mem
  -- degree f ∈ (leadingTerm f).support (since f ≠ 0)
  have hdeg_supp : binomialEdgeMonomialOrder.degree f ∈
      (binomialEdgeMonomialOrder.leadingTerm f).support := by
    simp only [MonomialOrder.leadingTerm]
    classical
    rw [support_monomial, if_neg (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hf0)]
    exact Finset.mem_singleton_self _
  -- Extract: ∃ g ∈ groebnerBasisSet G, degree g ≤ degree f
  obtain ⟨si, ⟨g, hg_mem, rfl⟩, hle⟩ := hlt_mem _ hdeg_supp
  obtain ⟨i, j, π, hπ, rfl⟩ := hg_mem
  exact ⟨i, j, π, hπ, hle⟩

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

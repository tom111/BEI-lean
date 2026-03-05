import BEI.AdmissiblePaths
import BEI.MonomialOrder
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

theorem theorem_2_1_leading (G : SimpleGraph V) (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) :
    -- Part 2: the leading term of f is divisible by some leading term in the basis set
    ∃ (i j : V) (π : List V) (_ : IsAdmissiblePath G i j π),
      binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) ≤
      binomialEdgeMonomialOrder.degree f := by
  sorry

theorem theorem_2_1_reduced (G : SimpleGraph V)
    (i₁ j₁ : V) (π₁ : List V) (_ : IsAdmissiblePath G i₁ j₁ π₁)
    (i₂ j₂ : V) (π₂ : List V) (_ : IsAdmissiblePath G i₂ j₂ π₂)
    (hne : (i₁, j₁, π₁) ≠ (i₂, j₂, π₂)) :
    -- Part 3: no leading monomial divides another
    ¬ (binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₁ j₁ π₁) ≤
       binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₂ j₂ π₂)) := by
  sorry

/-! ## Squarefree leading monomials -/

/-- If `v ∉ image of f over l`, then the product `∏ X(f w)` has degree 0 at `v`. -/
private lemma prod_X_image_degree_zero {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
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
      simp [prod_X_image_degree_zero f t m v hv_not_t]
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
      prod_X_image_degree_zero Sum.inr _ _ _ (by simp)
    -- eliminate cross-type term: Sum.inr j ≠ Sum.inl a always
    have h_cross : (if Sum.inr j = Sum.inl a then (1 : ℕ) else 0) = 0 := if_neg (by simp)
    rw [h_cross, add_zero] at hfij_deg
    by_cases hai : a = i
    · subst hai
      have hdegx : binomialEdgeMonomialOrder.degree
          ((xl.map (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inl a) = 0 :=
        prod_X_image_degree_zero Sum.inl _ _ _ (by
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
      prod_X_image_degree_zero Sum.inl _ _ _ (by simp)
    -- eliminate cross-type term: Sum.inl i ≠ Sum.inr a always
    have h_cross : (if Sum.inl i = Sum.inr a then (1 : ℕ) else 0) = 0 := if_neg (by simp)
    rw [h_cross, zero_add] at hfij_deg
    by_cases haj : a = j
    · subst haj
      have hdegy : binomialEdgeMonomialOrder.degree
          ((yl.map (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K))).prod) (Sum.inr a) = 0 :=
        prod_X_image_degree_zero Sum.inr _ _ _ (by
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

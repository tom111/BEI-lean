import BEI.GroebnerBasisSPolynomial

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Reduced Groebner basis (Theorem 2.1) and squarefree leading monomials

This file contains:
- Degree computation helpers for `groebnerElement`.
- `theorem_2_1_reduced`: no leading monomial of one basis element divides another.
- `theorem_2_1_isReducedGroebnerBasis`: the paper-faithful wrapper combining
  `theorem_2_1` (from `BEI/GroebnerBasisSPolynomial.lean`) with reducedness.
- `groebnerElement_leadingMonomial_squarefree`: each variable appears at most once
  in the leading monomial.

## Reference: Herzog et al. (2010), Theorem 2.1
-/

noncomputable section

open MvPolynomial MonomialOrder

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
    -- j appears at positions |π₁|-1 and |π₂|-1 in π₂ �� same position → |π₁| = |π₂| → contradiction
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

/-! ## Paper-faithful wrapper: Theorem 2.1 (reduced Groebner basis)

The paper states Theorem 2.1 as a single result: the admissible-path family is
a **reduced** Groebner basis. We package the two separately-proved parts into one
combined statement. -/

/--
**Theorem 2.1** (paper-faithful wrapper): The admissible-path Groebner basis set is
a reduced Groebner basis of `J_G`. This combines:
- `theorem_2_1`: the set is a Groebner basis;
- `theorem_2_1_reduced`: no leading monomial divides another.

Reference: Herzog et al. (2010), Theorem 2.1.
-/
theorem theorem_2_1_isReducedGroebnerBasis (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis
      (groebnerBasisSet (K := K) G) (binomialEdgeIdeal (K := K) G) ∧
    ∀ (i₁ j₁ : V) (π₁ : List V) (_ : IsAdmissiblePath G i₁ j₁ π₁)
      (i₂ j₂ : V) (π₂ : List V) (_ : IsAdmissiblePath G i₂ j₂ π₂),
      (i₁, j₁, π₁) ≠ (i₂, j₂, π₂) →
      ¬ (binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₁ j₁ π₁) ≤
         binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i₂ j₂ π₂)) :=
  ⟨theorem_2_1 G, fun _ _ _ h₁ _ _ _ h₂ hne => theorem_2_1_reduced G _ _ _ h₁ _ _ _ h₂ hne⟩

/-! ## Corollary 2.2: J_G is radical -/

-- Corollary 2.2 is proved in BEI/Radical.lean via the squarefree Gröbner basis argument.

/--
The leading monomials of the Groebner basis elements are squarefree:
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
  change binomialEdgeMonomialOrder.degree (pathMonomial i j π * (x i * y j - x j * y i)) v ≤ 1
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

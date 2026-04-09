import BEI.AdmissiblePaths
import BEI.MonomialOrder
import BEI.GroebnerAPI
import BEI.HerzogLemmas
import Mathlib.RingTheory.MvPolynomial.MonomialOrder

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Walk-based IsRemainder infrastructure for Theorem 2.1

S-polynomial helpers, pathMonomial exponent analysis, covered walk lemmas
(x-variant, y-variant, mixed), and walk construction from shared-endpoint
admissible paths. Extracted from GroebnerBasis.lean for modularity.
-/

noncomputable section

open MvPolynomial MonomialOrder

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
    simp only [List.map_nil, List.prod_nil] at hd
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

omit [DecidableEq V] [Fintype V] in
/-- The pathMonomial exponent at `Sum.inl v` is 0 when `v ∉ internalVertices π` or `¬(j < v)`. -/
lemma pathMonomial_exponent_inl_zero
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

omit [DecidableEq V] [Fintype V] in
/-- The pathMonomial exponent at `Sum.inr v` is 0 when `v ∉ internalVertices π` or `¬(v < i)`. -/
lemma pathMonomial_exponent_inr_zero
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

omit [DecidableEq V] [Fintype V] in
/-- The pathMonomial exponent at `Sum.inl v` is 1 when `v ∈ internalVertices π` and `j < v`. -/
lemma pathMonomial_exponent_inl_one
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

omit [DecidableEq V] [Fintype V] in
/-- The pathMonomial exponent at `Sum.inr v` is 1 when `v ∈ internalVertices π` and `v < i`. -/
lemma pathMonomial_exponent_inr_one
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

/-- At a position `w` where both `f₁` and `f₂` vanish, the S-polynomial monomial factor
`D = (d₁ + f₁) ⊔ (d₂ + f₂) - f₁ ⊔ f₂` satisfies `D(w) ≥ d₁(w)` and `D(w) ≥ d₂(w)`. -/
lemma sPolyD_ge_of_zero {ι : Type*} (d₁ d₂ f₁ f₂ : ι →₀ ℕ) (w : ι)
    (hf₁ : f₁ w = 0) (hf₂ : f₂ w = 0) :
    ((d₁ + f₁) ⊔ (d₂ + f₂) - f₁ ⊔ f₂) w ≥ d₁ w ∧
    ((d₁ + f₁) ⊔ (d₂ + f₂) - f₁ ⊔ f₂) w ≥ d₂ w := by
  simp only [Finsupp.sup_apply, Finsupp.add_apply, Finsupp.tsub_apply, hf₁, hf₂,
    add_zero, Nat.zero_max, Nat.sub_zero]
  omega

omit [DecidableEq V] in
/-- `IsRemainder 0 G 0` holds trivially for any set G. -/
lemma isRemainder_zero_zero'
    (G : Set (MvPolynomial (BinomialEdgeVars V) K)) :
    binomialEdgeMonomialOrder.IsRemainder (0 : MvPolynomial (BinomialEdgeVars V) K) G 0 :=
  ⟨⟨0, by simp, by simp [degree_zero, le_refl]⟩, by simp⟩

omit [DecidableEq V] in
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

omit [DecidableEq V] in
/-- `IsRemainder (-f) G 0` follows from
`IsRemainder f G 0`. -/
lemma isRemainder_neg'
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

omit [DecidableEq V] [Fintype V] in
/-- Given a nodup walk from `a` to `b` (with `a < b`) satisfying the vertex condition,
there exists an admissible path from `a` to `b` in G that is a sublist of the walk. -/
theorem exists_admissible_path_of_walk (G : SimpleGraph V)
    (a b : V) (hab : a < b)
    (π : List V) (hHead : π.head? = some a) (hLast : π.getLast? = some b)
    (hND : π.Nodup) (hVtx : ∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v)
    (hWalk : π.IsChain (fun u v => G.Adj u v)) :
    ∃ σ : List V, IsAdmissiblePath G a b σ ∧ σ.Sublist π := by
  -- By strong induction on π.length.
  -- Either π satisfies the minimality condition (7) and is admissible,
  -- or there exists a proper sublist satisfying 1-6, which is shorter.
  suffices ∀ (n : ℕ) (π : List V), π.length ≤ n →
      π.head? = some a → π.getLast? = some b → π.Nodup →
      (∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v) →
      π.IsChain (fun u v => G.Adj u v) →
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
        π'.IsChain (fun u v => G.Adj u v) →
        ¬(∀ v ∈ π', v = a ∨ v = b ∨ v < a ∨ b < v)
    · exact ⟨π, ⟨hab, hHead, hLast, hND, hVtx, hWalk, hMin⟩, List.Sublist.refl π⟩
    · push_neg at hMin
      obtain ⟨π', hSub, hNe, hHead', hLast', hWalk', hVtx'⟩ := hMin
      have hND' : π'.Nodup := hND.sublist hSub
      have hlen_lt : π'.length < π.length :=
        lt_of_le_of_ne hSub.length_le (fun h => hNe (hSub.length_eq.mp h))
      obtain ⟨σ, hσ, hσ_sub⟩ := ih π' (by omega) hHead' hLast' hND' hVtx' hWalk'
      exact ⟨σ, hσ, hσ_sub.trans hSub⟩



omit [DecidableEq V] [Fintype V] in
/-- The pathMonomial is a monomial with coefficient 1. -/
lemma pathMonomial_is_monomial (i j : V) (π : List V) :
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

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma getLast_not_mem_dropLast_nd (l : List V) (hnd : l.Nodup) (hne : l ≠ []) :
    l.getLast hne ∉ l.dropLast := by
  intro h
  rw [← List.dropLast_append_getLast hne] at hnd
  exact (List.nodup_append.mp hnd).2.2 _ h _ (List.mem_singleton.mpr rfl) rfl

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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
    | cons w rest => simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead; simp
  have hu_ne_b : u ≠ b := by
    intro heq
    have hlast : (τ.drop k).getLast hne_drop = b := by
      rw [List.getLast_drop hne_drop]
      exact Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hLast)
    exact ne_getLast_of_mem_tdl _ ((List.drop_sublist k τ).nodup hND) hne_drop u hu
      (heq ▸ hlast.symm)
  change u ∈ τ.tail.dropLast
  cases τ with
  | nil => exact absurd rfl hne
  | cons w rest =>
    simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
    simp only [List.tail_cons]
    have hu_rest : u ∈ rest := (List.mem_cons.mp hu_mem).resolve_left hu_ne_a
    have hrest_ne : rest ≠ [] := List.ne_nil_of_mem hu_rest
    refine List.mem_dropLast_of_mem_of_ne_getLast hu_rest (fun heq => hu_ne_b ?_)
    rw [heq, ← List.getLast_cons hrest_ne (a := w)]
    exact Option.some.inj
      ((List.getLast?_eq_some_getLast (List.cons_ne_nil w rest)).symm.trans hLast)

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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
        rw [List.head?_take, if_neg (by omega), hHead] at this
        simp only [List.head?_cons, Option.some.injEq] at this; exact this
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
  change u ∈ τ.tail.dropLast
  cases τ with
  | nil => exact absurd rfl hne
  | cons w rest =>
    simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
    simp only [List.tail_cons]
    have hu_rest : u ∈ rest := (List.mem_cons.mp hu_mem).resolve_left hu_ne_a
    have hrest_ne : rest ≠ [] := List.ne_nil_of_mem hu_rest
    refine List.mem_dropLast_of_mem_of_ne_getLast hu_rest (fun heq => hu_ne_b ?_)
    rw [heq, ← List.getLast_cons hrest_ne (a := w)]
    exact Option.some.inj
      ((List.getLast?_eq_some_getLast (List.cons_ne_nil w rest)).symm.trans hLast)

/-! ## General IsRemainder lemma for fij via walk decomposition -/

omit [DecidableEq V] in
/-- **Core lemma**: If there is a nodup walk `τ` from `a` to `b` in `G`,
and the monomial `q = monomial d_q 1` "covers" every internal vertex of
`τ` (i.e., `d_q` has `y_v` for `v < a`,
`x_v` for `v > b`, and `x_v` for "bad" vertices `a < v < b`), then `q * f_{ab}` has
`IsRemainder 0` modulo the Gröbner basis set.

This generalizes `isRemainder_fij_via_groebnerElement` to walks that may have internal
vertices in the range `(a, b)` (which would violate the admissible path vertex condition).
Such vertices are handled by the `fij_x_telescope` identity. -/
theorem isRemainder_fij_of_covered_walk (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b : V) (τ : List V) (d_q : BinomialEdgeVars V →₀ ℕ),
    τ.length ≤ n →
    a < b →
    τ.head? = some a →
    τ.getLast? = some b →
    τ.Nodup →
    τ.IsChain (fun u v => G.Adj u v) →
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
      have hBadSet :
          ((internalVertices τ).filter
            (fun v => decide (a < v) && decide (v < b))).toFinset.Nonempty := by
        refine ⟨v₀_raw, List.mem_toFinset.mpr
          (List.mem_filter.mpr ⟨hv₀_raw_int, by simp [hav₀_raw, hv₀_rawb]⟩)⟩
      set v₀ := ((internalVertices τ).filter
        (fun v => decide (a < v) && decide (v < b))).toFinset.min' hBadSet
      have hv₀_filt : v₀ ∈ (internalVertices τ).filter
          (fun v => decide (a < v) && decide (v < b)) := by
        exact List.mem_toFinset.mp (Finset.min'_mem _ _)
      have hv₀_int : v₀ ∈ internalVertices τ :=
        (List.mem_filter.mp hv₀_filt).1
      have hav₀ : a < v₀ := by
        have := (List.mem_filter.mp hv₀_filt).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
      have hv₀b : v₀ < b := by
        have := (List.mem_filter.mp hv₀_filt).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
      have hv₀_min : ∀ w ∈ internalVertices τ, a < w → w < b → v₀ ≤ w := by
        intro w hw haw hwb
        have hw_filt : w ∈ (internalVertices τ).filter
            (fun v => decide (a < v) && decide (v < b)) :=
          List.mem_filter.mpr ⟨hw, by simp [haw, hwb]⟩
        exact Finset.min'_le _ _
          (List.mem_toFinset.mpr hw_filt)
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
          τ₂.IsChain (fun u v => G.Adj u v) ∧
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
              simp only [h0, List.getElem_cons_zero] at this; exact this
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
          τ₁.IsChain (fun u v => G.Adj u v) ∧
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
            simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
            simp only [internalVertices, List.tail_cons] at hv_τ
            exact ((List.nodup_cons.mp hND).1) ((List.dropLast_sublist _).mem hv_τ)
        -- d₁(inr v) = d_q(inr v) since ev₀, ea only affect inl
        have hinr : d₁ (Sum.inr v) = d_q (Sum.inr v) := by
          simp only [hd₁_def, hev₀_def, hea_def, Finsupp.add_apply, Finsupp.tsub_apply]
          simp
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
          simp
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
          change monomial (d_q - ev₀) (1:K) * x (K := K) a = monomial d₁ 1
          change monomial (d_q - ev₀) (1:K) * monomial ea (1:K) = monomial d₁ 1
          rw [monomial_mul, one_mul]
        · congr 1
          change monomial (d_q - ev₀) (1:K) * x (K := K) b = monomial d₂ 1
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
          refine List.mem_dropLast_of_mem_of_ne_getLast hv_rest
            (fun heq => hvb ?_)
          have hlast_eq := List.getLast_cons hrest_ne (a := a')
          have hb : (a' :: rest).getLast
              (List.cons_ne_nil a' rest) = b :=
            Option.some.inj ((List.getLast?_eq_some_getLast
              (List.cons_ne_nil a' rest)).symm.trans hL)
          rw [heq, ← hlast_eq, hb]
      have hVtx :
          ∀ v ∈ τ, v = a ∨ v = b ∨ v < a ∨ b < v := by
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

omit [DecidableEq V] in
/-- **Dual variant (y-telescope)**: same as
`isRemainder_fij_of_covered_walk` but the coverage for "bad"
vertices `a < v < b` uses `Sum.inr v` (y-variable) instead of
`Sum.inl v` (x-variable). The proof uses `fij_telescope` instead
of `fij_x_telescope`.
Needed for the shared-last-endpoint case (Case 5 of Thm 2.1). -/
theorem isRemainder_fij_of_covered_walk_y (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b : V) (τ : List V) (d_q : BinomialEdgeVars V →₀ ℕ),
    τ.length ≤ n →
    a < b →
    τ.head? = some a →
    τ.getLast? = some b →
    τ.Nodup →
    τ.IsChain (fun u v => G.Adj u v) →
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
      have hBadSet :
          ((internalVertices τ).filter
            (fun v => decide (a < v) && decide (v < b))).toFinset.Nonempty := by
        refine ⟨v₀_raw, List.mem_toFinset.mpr
          (List.mem_filter.mpr ⟨hv₀_raw_int, by simp [hav₀_raw, hv₀_rawb]⟩)⟩
      set v₀ := ((internalVertices τ).filter
        (fun v => decide (a < v) && decide (v < b))).toFinset.max' hBadSet
      have hv₀_filt : v₀ ∈ (internalVertices τ).filter
          (fun v => decide (a < v) && decide (v < b)) := by
        exact List.mem_toFinset.mp (Finset.max'_mem _ _)
      have hv₀_int : v₀ ∈ internalVertices τ :=
        (List.mem_filter.mp hv₀_filt).1
      have hav₀ : a < v₀ := by
        have := (List.mem_filter.mp hv₀_filt).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
      have hv₀b : v₀ < b := by
        have := (List.mem_filter.mp hv₀_filt).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
      have hv₀_max : ∀ w ∈ internalVertices τ, a < w → w < b → w ≤ v₀ := by
        intro w hw haw hwb
        have hw_filt : w ∈ (internalVertices τ).filter
            (fun v => decide (a < v) && decide (v < b)) :=
          List.mem_filter.mpr ⟨hw, by simp [haw, hwb]⟩
        exact Finset.le_max' _ _
          (List.mem_toFinset.mpr hw_filt)
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
          τ₂.IsChain (fun u v => G.Adj u v) ∧
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
              simp only [h0, List.getElem_cons_zero] at this; exact this
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
          τ₁.IsChain (fun u v => G.Adj u v) ∧
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
            simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
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
          change monomial (d_q - eyv₀) (1:K) * y (K := K) b = monomial d₁ 1
          change monomial (d_q - eyv₀) (1:K) * monomial eyb (1:K) = monomial d₁ 1
          rw [monomial_mul, one_mul]
        · congr 1
          change monomial (d_q - eyv₀) (1:K) * y (K := K) a = monomial d₂ 1
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
          if_neg (ne_of_gt hv₀b), if_neg (ne_of_lt hav₀)] at hv
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
          refine List.mem_dropLast_of_mem_of_ne_getLast hv_rest
            (fun heq => hvb ?_)
          have hlast_eq := List.getLast_cons hrest_ne (a := a')
          have hb : (a' :: rest).getLast
              (List.cons_ne_nil a' rest) = b :=
            Option.some.inj ((List.getLast?_eq_some_getLast
              (List.cons_ne_nil a' rest)).symm.trans hL)
          rw [heq, ← hlast_eq, hb]
      have hVtx :
          ∀ v ∈ τ, v = a ∨ v = b ∨ v < a ∨ b < v := by
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

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Reversed walk preserves adjacency (graph is undirected). -/
lemma chain'_reverse' (G : SimpleGraph V) (π : List V)
    (hW : π.IsChain (fun a b => G.Adj a b)) :
    π.reverse.IsChain (fun a b => G.Adj a b) := by
  rw [List.isChain_reverse]
  exact List.IsChain.imp (fun _ _ h => G.symm h) (hW : List.IsChain _ π)

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Internal vertices of a reversed list have the same membership as the original.
Both are "all elements except first and last", which are swapped by reversal. -/
private lemma internalVertices_reverse (l : List V) :
    internalVertices l.reverse = (internalVertices l).reverse := by
  simp only [internalVertices, List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
lemma mem_internalVertices_reverse {l : List V} {v : V}
    (h : v ∈ internalVertices l.reverse) : v ∈ internalVertices l := by
  rw [internalVertices_reverse] at h
  exact List.mem_reverse.mp h

/-! ### Helpers for walk construction -/

omit [LinearOrder V] [Fintype V] in
private lemma idxOf_lt {l : List V} {v : V} (hv : v ∈ l) : l.idxOf v < l.length :=
  List.findIdx_lt_length_of_exists ⟨v, hv, by simp [BEq.beq]⟩

omit [LinearOrder V] [Fintype V] in
lemma head?_drop_idxOf {l : List V} {v : V} (hv : v ∈ l) :
    (l.drop (l.idxOf v)).head? = some v := by
  rw [List.head?_eq_getElem?, List.getElem?_drop]
  simp [List.getElem?_eq_getElem (idxOf_lt hv), List.getElem_idxOf (idxOf_lt hv)]

omit [LinearOrder V] [Fintype V] in
lemma getLast?_drop_idxOf {l : List V} {v : V} (hv : v ∈ l) :
    (l.drop (l.idxOf v)).getLast? = l.getLast? := by
  have hne : l.drop (l.idxOf v) ≠ [] := by
    simp only [ne_eq, List.drop_eq_nil_iff, not_le]; exact idxOf_lt hv
  rw [List.getLast?_eq_some_getLast hne,
      List.getLast?_eq_some_getLast (List.ne_nil_of_mem hv)]
  exact congrArg _ (List.getLast_drop hne)

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
lemma isChain_drop {r : V → V → Prop} {l : List V} (h : l.IsChain r) (i : ℕ) :
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

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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
      simp only [List.getLast?_singleton, Option.mem_def, Option.some.injEq, forall_eq'] at h
      cases l₂ with
      | nil => exact .singleton a
      | cons b rest₂ => exact .cons_cons (h b (by simp)) h₂
    | cons b rest' =>
      have h₁' : (b :: rest').IsChain r := by cases h₁ with | cons_cons _ h => exact h
      have hab : r a b := by cases h₁ with | cons_cons h _ => exact h
      exact .cons_cons hab (ih h₁' (by
        intro x hx y hy; apply h x _ y hy
        simp only [List.getLast?_cons_cons]; exact hx))

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma isChain_tail {r : V → V → Prop} {l : List V}
    (h : l.IsChain r) : l.tail.IsChain r := by
  cases h with
  | nil => exact .nil
  | singleton _ => exact .nil
  | cons_cons _ h2 => exact h2

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma mem_of_mem_internalVertices {l : List V} {v : V}
    (h : v ∈ internalVertices l) : v ∈ l :=
  (List.tail_sublist l).mem ((List.dropLast_sublist _).mem h)

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma getLast_not_mem_dropLast (l : List V) (hnd : l.Nodup) (hne : l ≠ []) :
    l.getLast hne ∉ l.dropLast := by
  rw [← List.dropLast_append_getLast hne] at hnd
  rw [List.nodup_append] at hnd
  intro h; exact absurd rfl (hnd.2.2 _ h _ (List.Mem.head []))

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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
omit [LinearOrder V] [DecidableEq V] [Fintype V] in
lemma head_of_head? {l : List V} {a : V} (h : l.head? = some a) :
    l.head (by intro h'; simp [h'] at h) = a := by
  cases l with
  | nil => simp only [List.head?_nil, reduceCtorEq] at h
  | cons x _ => simp only [List.head?_cons, Option.some.injEq] at h; exact h

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
lemma getLast_of_getLast? {l : List V} {a : V} (h : l.getLast? = some a) :
    l.getLast (by intro h'; simp [h'] at h) = a := by
  have hne : l ≠ [] := by intro h'; simp [h'] at h
  rw [List.getLast?_eq_some_getLast hne] at h; exact Option.some.inj h

-- v ∈ l, v ≠ head, v ≠ getLast → v ∈ internalVertices l
omit [LinearOrder V] [DecidableEq V] [Fintype V] in
lemma mem_internalVertices_of_ne {l : List V} {v : V}
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


omit [DecidableEq V] in
theorem isRemainder_fij_of_mixed_walk (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b : V) (τ : List V) (d_q : BinomialEdgeVars V →₀ ℕ),
    τ.length ≤ n →
    a < b →
    τ.head? = some a →
    τ.getLast? = some b →
    τ.Nodup →
    τ.IsChain (fun u v => G.Adj u v) →
    (∀ w ∈ internalVertices τ, d_q (Sum.inl w) ≥ 1 ∨ d_q (Sum.inr w) ≥ 1) →
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
    -- Case split: is there a "bad" vertex v ∈ (a, b) among internal vertices?
    by_cases hBad : ∃ v ∈ internalVertices τ, a < v ∧ v < b
    · -- Bad vertex case: pick minimum bad vertex v₀
      obtain ⟨v₀_raw, hv₀_raw_int, hav₀_raw, hv₀_rawb⟩ := hBad
      have hBadSet : ((internalVertices τ).filter
          (fun v => decide (a < v) && decide (v < b))).toFinset.Nonempty := by
        refine ⟨v₀_raw, List.mem_toFinset.mpr
          (List.mem_filter.mpr ⟨hv₀_raw_int, by simp [hav₀_raw, hv₀_rawb]⟩)⟩
      set v₀ := ((internalVertices τ).filter
          (fun v => decide (a < v) && decide (v < b))).toFinset.min' hBadSet
      have hv₀_filt : v₀ ∈ (internalVertices τ).filter
          (fun v => decide (a < v) && decide (v < b)) := by
        exact List.mem_toFinset.mp (Finset.min'_mem _ _)
      have hv₀_int : v₀ ∈ internalVertices τ := (List.mem_filter.mp hv₀_filt).1
      have hav₀ : a < v₀ := by
        have := (List.mem_filter.mp hv₀_filt).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
      have hv₀b : v₀ < b := by
        have := (List.mem_filter.mp hv₀_filt).2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.2
      have hv₀_min : ∀ w ∈ internalVertices τ, a < w → w < b → v₀ ≤ w := by
        intro w hw haw hwb
        have hw_filt : w ∈ (internalVertices τ).filter
            (fun v => decide (a < v) && decide (v < b)) :=
          List.mem_filter.mpr ⟨hw, by simp [haw, hwb]⟩
        exact Finset.min'_le _ _ (List.mem_toFinset.mpr hw_filt)
      -- Coverage at v₀: d_q(inl v₀) ≥ 1 or d_q(inr v₀) ≥ 1
      have hcov_v₀ := hCov v₀ hv₀_int
      -- Sub-walk from v₀ to b (via τ.drop)
      have ⟨τ₂, hτ₂_len, hτ₂_head, hτ₂_last, hτ₂_nd, hτ₂_walk, hτ₂_int⟩ :
          ∃ τ₂ : List V,
          τ₂.length ≤ n ∧
          τ₂.head? = some v₀ ∧ τ₂.getLast? = some b ∧ τ₂.Nodup ∧
          τ₂.IsChain (fun u v => G.Adj u v) ∧
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
              simp only [h0, List.getElem_cons_zero] at this; exact this
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
          τ₁.IsChain (fun u v => G.Adj u v) ∧
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
              rw [List.getElem?_eq_getElem (show k < τ.length by omega)]
              exact congrArg some hπk
            simp [this]
          exact this
        · exact (List.take_sublist (k + 1) τ).nodup hND
        · exact List.IsChain.take hWalk (k + 1)
        · exact fun u hu => internal_of_take τ k a b hne hND hHead hLast hk_lt_pred u hu
      -- Case split on x vs y coverage at v₀
      rcases hcov_v₀ with hcov_x | hcov_y
      · -- x-telescope at v₀: x_{v₀} * fij a b = x_a * fij v₀ b + x_b * fij a v₀
        set ev₀ : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inl v₀) 1 with hev₀_def
        set ea : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inl a) 1 with hea_def
        set eb : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inl b) 1 with heb_def
        set d₁ := d_q - ev₀ + ea with hd₁_def
        set d₂ := d_q - ev₀ + eb with hd₂_def
        -- Coverage for sub-walk τ₂ (v₀ → b): disjunctive
        have hCov₂ : ∀ v ∈ internalVertices τ₂,
            d₁ (Sum.inl v) ≥ 1 ∨ d₁ (Sum.inr v) ≥ 1 := by
          intro v hv
          have hv_τ := hτ₂_int v hv
          have hv_ne_a : v ≠ a := by
            intro heq; subst heq
            have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
            cases τ with | nil => exact absurd rfl hne_τ | cons w rest =>
              simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
              simp only [internalVertices, List.tail_cons] at hv_τ
              exact ((List.nodup_cons.mp hND).1) ((List.dropLast_sublist _).mem hv_τ)
          have hv_ne_v₀ : v ≠ v₀ := by
            intro heq; subst heq
            -- v₀ is head of τ₂, so v₀ ∉ internalVertices τ₂
            have hne_τ₂ : τ₂ ≠ [] := by intro h; simp [h, internalVertices] at hv
            exact internal_ne_head hτ₂_nd hv hne_τ₂ (head_of_head? hτ₂_head).symm
          -- d₁(inl v) = d_q(inl v) since v ≠ v₀ and v ≠ a
          have hinl : d₁ (Sum.inl v) = d_q (Sum.inl v) := by
            simp only [hd₁_def, hev₀_def, hea_def]
            unfold BinomialEdgeVars at *
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inl.injEq]
            rw [if_neg (Ne.symm hv_ne_v₀), if_neg (Ne.symm hv_ne_a)]; omega
          -- d₁(inr v) = d_q(inr v) since ev₀, ea are at inl
          have hinr : d₁ (Sum.inr v) = d_q (Sum.inr v) := by
            simp only [hd₁_def, hev₀_def, hea_def, Finsupp.add_apply, Finsupp.tsub_apply,
              Finsupp.single_apply, reduceCtorEq, ↓reduceIte]; omega
          rw [hinl, hinr]; exact hCov v hv_τ
        -- Coverage for sub-walk τ₁ (a → v₀): disjunctive
        have hCov₁ : ∀ v ∈ internalVertices τ₁,
            d₂ (Sum.inl v) ≥ 1 ∨ d₂ (Sum.inr v) ≥ 1 := by
          intro v hv
          have hv_τ := hτ₁_int v hv
          have hv_ne_b : v ≠ b := by
            intro heq; subst heq
            have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
            exact (ne_getLast_of_mem_tdl τ hND hne_τ v hv_τ)
              (Option.some.inj (hLast.symm.trans (List.getLast?_eq_some_getLast hne_τ)))
          have hv_ne_v₀ : v ≠ v₀ := by
            intro heq; subst heq
            -- v₀ is last of τ₁, so v₀ ∉ internalVertices τ₁
            have hne_τ₁ : τ₁ ≠ [] := by intro h; simp [h, internalVertices] at hv
            exact internal_ne_getLast hτ₁_nd hv hne_τ₁ (getLast_of_getLast? hτ₁_last).symm
          -- d₂(inl v) = d_q(inl v) since v ≠ v₀ and v ≠ b
          have hinl : d₂ (Sum.inl v) = d_q (Sum.inl v) := by
            simp only [hd₂_def, hev₀_def, heb_def]
            unfold BinomialEdgeVars at *
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inl.injEq]
            rw [if_neg (Ne.symm hv_ne_v₀), if_neg (Ne.symm hv_ne_b)]; omega
          -- d₂(inr v) = d_q(inr v) since ev₀, eb are at inl
          have hinr : d₂ (Sum.inr v) = d_q (Sum.inr v) := by
            simp only [hd₂_def, hev₀_def, heb_def, Finsupp.add_apply, Finsupp.tsub_apply,
              Finsupp.single_apply, reduceCtorEq, ↓reduceIte]; omega
          rw [hinl, hinr]; exact hCov v hv_τ
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
          have hle : ev₀ ≤ d_q := by
            unfold BinomialEdgeVars at *; exact Finsupp.single_le_iff.mpr hcov_x
          have hfactor : (monomial d_q (1:K) : MvPolynomial (BinomialEdgeVars V) K) =
              monomial (d_q - ev₀) (1:K) * monomial ev₀ (1:K) := by
            rw [monomial_mul, one_mul, tsub_add_cancel_of_le hle]
          have hxv₀ : (monomial ev₀ (1:K) : MvPolynomial (BinomialEdgeVars V) K) = x v₀ := rfl
          rw [hfactor, mul_assoc,
              show monomial ev₀ (1:K) * fij (K := K) a b = x v₀ * fij a b from by rw [← hxv₀],
              fij_x_telescope (K := K) a v₀ b, mul_add, ← mul_assoc, ← mul_assoc]
          congr 1
          · congr 1
            change monomial (d_q - ev₀) (1:K) * monomial ea (1:K) = monomial d₁ 1
            rw [monomial_mul, one_mul]
          · congr 1
            change monomial (d_q - ev₀) (1:K) * monomial eb (1:K) = monomial d₂ 1
            rw [monomial_mul, one_mul]
        -- Degree bounds
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
      · -- y-telescope at v₀: y_{v₀} * fij a b = y_b * fij a v₀ + y_a * fij v₀ b
        set eyv₀ : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inr v₀) 1 with heyv₀_def
        set eyb : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inr b) 1 with heyb_def
        set eya : BinomialEdgeVars V →₀ ℕ := Finsupp.single (Sum.inr a) 1 with heya_def
        set d₁ := d_q - eyv₀ + eyb with hd₁_def
        set d₂ := d_q - eyv₀ + eya with hd₂_def
        -- Coverage for sub-walk τ₁ (a → v₀): disjunctive
        have hCov₁ : ∀ v ∈ internalVertices τ₁,
            d₁ (Sum.inl v) ≥ 1 ∨ d₁ (Sum.inr v) ≥ 1 := by
          intro v hv
          have hv_τ := hτ₁_int v hv
          have hv_ne_b : v ≠ b := by
            intro heq; subst heq
            have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
            exact (ne_getLast_of_mem_tdl τ hND hne_τ v hv_τ)
              (Option.some.inj (hLast.symm.trans (List.getLast?_eq_some_getLast hne_τ)))
          have hv_ne_v₀ : v ≠ v₀ := by
            intro heq; subst heq
            have hne_τ₁ : τ₁ ≠ [] := by intro h; simp [h, internalVertices] at hv
            exact internal_ne_getLast hτ₁_nd hv hne_τ₁ (getLast_of_getLast? hτ₁_last).symm
          -- d₁(inl v) = d_q(inl v) since eyv₀, eyb are at inr
          have hinl : d₁ (Sum.inl v) = d_q (Sum.inl v) := by
            simp only [hd₁_def, heyv₀_def, heyb_def, Finsupp.add_apply, Finsupp.tsub_apply,
              Finsupp.single_apply, reduceCtorEq, ↓reduceIte]; omega
          -- d₁(inr v) = d_q(inr v) since v ≠ v₀ and v ≠ b
          have hinr : d₁ (Sum.inr v) = d_q (Sum.inr v) := by
            simp only [hd₁_def, heyv₀_def, heyb_def]
            unfold BinomialEdgeVars at *
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inr.injEq]
            rw [if_neg (Ne.symm hv_ne_v₀), if_neg (Ne.symm hv_ne_b)]; omega
          rw [hinl, hinr]; exact hCov v hv_τ
        -- Coverage for sub-walk τ₂ (v₀ → b): disjunctive
        have hCov₂ : ∀ v ∈ internalVertices τ₂,
            d₂ (Sum.inl v) ≥ 1 ∨ d₂ (Sum.inr v) ≥ 1 := by
          intro v hv
          have hv_τ := hτ₂_int v hv
          have hv_ne_a : v ≠ a := by
            intro heq; subst heq
            have hne_τ : τ ≠ [] := by intro h; simp [h, internalVertices] at hv_τ
            cases τ with | nil => exact absurd rfl hne_τ | cons w rest =>
              simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
              simp only [internalVertices, List.tail_cons] at hv_τ
              exact ((List.nodup_cons.mp hND).1) ((List.dropLast_sublist _).mem hv_τ)
          have hv_ne_v₀ : v ≠ v₀ := by
            intro heq; subst heq
            have hne_τ₂ : τ₂ ≠ [] := by intro h; simp [h, internalVertices] at hv
            exact internal_ne_head hτ₂_nd hv hne_τ₂ (head_of_head? hτ₂_head).symm
          -- d₂(inl v) = d_q(inl v) since eyv₀, eya are at inr
          have hinl : d₂ (Sum.inl v) = d_q (Sum.inl v) := by
            simp only [hd₂_def, heyv₀_def, heya_def, Finsupp.add_apply, Finsupp.tsub_apply,
              Finsupp.single_apply, reduceCtorEq, ↓reduceIte]; omega
          -- d₂(inr v) = d_q(inr v) since v ≠ v₀ and v ≠ a
          have hinr : d₂ (Sum.inr v) = d_q (Sum.inr v) := by
            simp only [hd₂_def, heyv₀_def, heya_def]
            unfold BinomialEdgeVars at *
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, Sum.inr.injEq]
            rw [if_neg (Ne.symm hv_ne_v₀), if_neg (Ne.symm hv_ne_a)]; omega
          rw [hinl, hinr]; exact hCov v hv_τ
        -- Apply IH (fij_telescope: y v₀ * fij a b = y b * fij a v₀ + y a * fij v₀ b)
        have h₁ : binomialEdgeMonomialOrder.IsRemainder
            (monomial d₁ 1 * fij (K := K) a v₀) (groebnerBasisSet G) 0 :=
          ih a v₀ τ₁ d₁ hτ₁_len hav₀ hτ₁_head hτ₁_last hτ₁_nd hτ₁_walk hCov₁
        have h₂ : binomialEdgeMonomialOrder.IsRemainder
            (monomial d₂ 1 * fij (K := K) v₀ b) (groebnerBasisSet G) 0 :=
          ih v₀ b τ₂ d₂ hτ₂_len hv₀b hτ₂_head hτ₂_last hτ₂_nd hτ₂_walk hCov₂
        -- Algebraic identity
        have halg : monomial d_q (1 : K) * fij a b =
            monomial d₁ 1 * fij (K := K) a v₀ + monomial d₂ 1 * fij (K := K) v₀ b := by
          have hle : eyv₀ ≤ d_q := by
            unfold BinomialEdgeVars at *; exact Finsupp.single_le_iff.mpr hcov_y
          have hfactor : (monomial d_q (1:K) : MvPolynomial (BinomialEdgeVars V) K) =
              monomial (d_q - eyv₀) (1:K) * monomial eyv₀ (1:K) := by
            rw [monomial_mul, one_mul, tsub_add_cancel_of_le hle]
          have hyv₀ : (monomial eyv₀ (1:K) : MvPolynomial (BinomialEdgeVars V) K) = y v₀ := rfl
          rw [hfactor, mul_assoc,
              show monomial eyv₀ (1:K) * fij (K := K) a b = y v₀ * fij a b from by rw [← hyv₀],
              fij_telescope (K := K) a v₀ b, mul_add, ← mul_assoc, ← mul_assoc]
          congr 1
          · congr 1
            change monomial (d_q - eyv₀) (1:K) * monomial eyb (1:K) = monomial d₁ 1
            rw [monomial_mul, one_mul]
          · congr 1
            change monomial (d_q - eyv₀) (1:K) * monomial eya (1:K) = monomial d₂ 1
            rw [monomial_mul, one_mul]
        -- Degree bounds
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
          rw [hdeg1, hdeg2]
          intro heq
          have hv := Finsupp.ext_iff.mp heq (Sum.inr v₀ : BinomialEdgeVars V)
          simp only [d₁, d₂, eyv₀, eyb, eya] at hv
          unfold BinomialEdgeVars at hv
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
            Sum.inr.injEq, reduceCtorEq, ite_true, ite_false,
            if_neg (ne_of_gt hv₀b),
            if_neg (ne_of_lt hav₀)] at hv
          omega
        obtain ⟨hdeg₁, hdeg₂⟩ := degree_bounds_of_ne _ _ hne_deg
        rw [halg]
        exact isRemainder_add _ _ _ h₁ h₂ hdeg₁ hdeg₂
    · -- No bad vertices: all internal vertices satisfy v ≤ a or v ≥ b
      push_neg at hBad
      have hne_τ : τ ≠ [] := fun h => by simp [h] at hHead
      have mem_internal : ∀ v ∈ τ, v ≠ a → v ≠ b → v ∈ internalVertices τ := by
        intro v hv hva hvb
        exact mem_internalVertices_of_ne hND hv hne_τ
          (by rwa [head_of_head? hHead]) (by rwa [getLast_of_getLast? hLast])
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
      -- Divisibility: the path monomial needs x_v for v > b and y_v
      -- for v < a, but disjunctive coverage doesn't guarantee which
      -- side is covered. Split on "processable" vertices first.
      by_cases hProc : ∃ v ∈ internalVertices τ,
          (b < v ∧ d_q (Sum.inr v) ≥ 1) ∨
          (v < a ∧ d_q (Sum.inl v) ≥ 1)
      · -- Processable non-bad vertex: telescope at it
        obtain ⟨v₀, hv₀_int, hv₀_proc⟩ := hProc
        rcases hv₀_proc with ⟨hbv₀, hcov_yr⟩ | ⟨hv₀a, hcov_xl⟩
        · -- v₀ > b, d_q(inr v₀) ≥ 1: y-telescope at v₀
          -- y_{v₀} * fij(a,b) = y_b * fij(a,v₀) + y_a * fij(v₀,b)
          -- and fij(v₀,b) = -fij(b,v₀) since v₀ > b
          have hav₀ : a < v₀ := lt_trans hab hbv₀
          set eyv₀ : BinomialEdgeVars V →₀ ℕ :=
            Finsupp.single (Sum.inr v₀) 1 with heyv₀_def
          set eyb : BinomialEdgeVars V →₀ ℕ :=
            Finsupp.single (Sum.inr b) 1 with heyb_def
          set eya : BinomialEdgeVars V →₀ ℕ :=
            Finsupp.single (Sum.inr a) 1 with heya_def
          set d₁ := d_q - eyv₀ + eyb with hd₁_def
          set d₂ := d_q - eyv₀ + eya with hd₂_def
          -- Sub-walk from v₀ to b (suffix of τ)
          have ⟨τ₂, hτ₂_len, hτ₂_head, hτ₂_last, hτ₂_nd,
              hτ₂_walk, hτ₂_int⟩ :
              ∃ τ₂ : List V,
              τ₂.length ≤ n ∧
              τ₂.head? = some v₀ ∧ τ₂.getLast? = some b ∧
              τ₂.Nodup ∧
              τ₂.IsChain (fun u v => G.Adj u v) ∧
              ∀ u ∈ internalVertices τ₂,
                u ∈ internalVertices τ := by
            have hne : τ ≠ [] := by
              intro h; simp [h, internalVertices] at hv₀_int
            have hv₀_mem : v₀ ∈ τ :=
              mem_of_mem_internalVertices hv₀_int
            set k := τ.idxOf v₀
            have hk_lt : k < τ.length :=
              List.idxOf_lt_length_of_mem hv₀_mem
            have hπk : τ[k]'hk_lt = v₀ :=
              List.getElem_idxOf hk_lt
            have hk_pos : 0 < k := by
              by_contra h; push_neg at h
              have h0 : τ.idxOf v₀ = 0 := Nat.le_zero.mp h
              cases τ with
              | nil => exact absurd rfl hne
              | cons w rest =>
                simp only [List.head?_cons, Option.some.injEq]
                  at hHead
                have : w = v₀ := by
                  have hlt :
                    (w :: rest).idxOf v₀ <
                      (w :: rest).length :=
                    List.idxOf_lt_length_of_mem hv₀_mem
                  have := List.getElem_idxOf hlt
                  simp only [h0, List.getElem_cons_zero] at this; exact this
                exact absurd (this.symm.trans hHead)
                  (ne_of_gt (lt_trans hab hbv₀))
            refine ⟨τ.drop k, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [List.length_drop]; omega
            · rw [List.head?_drop,
                List.getElem?_eq_getElem hk_lt, hπk]
            · rw [List.getLast?_drop,
                if_neg (by omega), hLast]
            · exact (List.drop_sublist k τ).nodup hND
            · exact List.IsChain.drop hWalk k
            · exact fun u hu =>
                internal_of_drop τ k a b hne hND
                  hHead hLast hk_pos hk_lt u hu
          -- Sub-walk from a to v₀ (prefix of τ)
          have ⟨τ₁, hτ₁_len, hτ₁_head, hτ₁_last, hτ₁_nd,
              hτ₁_walk, hτ₁_int⟩ :
              ∃ τ₁ : List V,
              τ₁.length ≤ n ∧
              τ₁.head? = some a ∧ τ₁.getLast? = some v₀ ∧
              τ₁.Nodup ∧
              τ₁.IsChain (fun u v => G.Adj u v) ∧
              ∀ u ∈ internalVertices τ₁,
                u ∈ internalVertices τ := by
            have hne : τ ≠ [] := by
              intro h; simp [h, internalVertices] at hv₀_int
            have hv₀_mem : v₀ ∈ τ :=
              mem_of_mem_internalVertices hv₀_int
            set k := τ.idxOf v₀
            have hk_lt : k < τ.length :=
              List.idxOf_lt_length_of_mem hv₀_mem
            have hπk : τ[k]'hk_lt = v₀ :=
              List.getElem_idxOf hk_lt
            have hk_lt_pred : k < τ.length - 1 := by
              rcases Nat.lt_or_ge k (τ.length - 1) with h | h
              · exact h
              · exfalso
                have hk_eq : k = τ.length - 1 :=
                  Nat.le_antisymm (by omega) h
                have hv₀_last : v₀ = τ.getLast hne := by
                  rw [List.getLast_eq_getElem]
                  exact (show τ[τ.length - 1] = τ[k]
                    from by congr 1; omega).trans hπk
                    |>.symm
                exact (ne_of_gt hbv₀) (hv₀_last.trans
                  (Option.some.inj
                    ((List.getLast?_eq_some_getLast hne
                      ).symm.trans hLast)))
            refine ⟨τ.take (k + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [List.length_take]; omega
            · rw [List.head?_take,
                if_neg (by omega), hHead]
            · have : (τ.take (k + 1)).getLast? =
                  some v₀ := by
                rw [List.getLast?_take,
                  if_neg (by omega)]
                have : τ[k]? = some v₀ := by
                  rw [List.getElem?_eq_getElem
                    (show k < τ.length by omega)]
                  exact congrArg some hπk
                simp [this]
              exact this
            · exact (List.take_sublist (k + 1) τ).nodup
                hND
            · exact List.IsChain.take hWalk (k + 1)
            · exact fun u hu =>
                internal_of_take τ k a b hne hND
                  hHead hLast hk_lt_pred u hu
          -- Coverage for τ₁ (a → v₀): disjunctive
          have hCov₁ : ∀ v ∈ internalVertices τ₁,
              d₁ (Sum.inl v) ≥ 1 ∨ d₁ (Sum.inr v) ≥ 1 := by
            intro v hv
            have hv_τ := hτ₁_int v hv
            have hv_ne_b : v ≠ b := by
              intro heq; subst heq
              have hne_τ : τ ≠ [] := by
                intro h; simp [h, internalVertices] at hv_τ
              exact (ne_getLast_of_mem_tdl τ hND hne_τ v
                hv_τ) (Option.some.inj (hLast.symm.trans
                  (List.getLast?_eq_some_getLast hne_τ)))
            have hv_ne_v₀ : v ≠ v₀ := by
              intro heq; subst heq
              have hne : τ₁ ≠ [] := by
                intro h; simp [h, internalVertices] at hv
              exact internal_ne_getLast hτ₁_nd hv hne
                (getLast_of_getLast? hτ₁_last).symm
            have hinl : d₁ (Sum.inl v) =
                d_q (Sum.inl v) := by
              simp only [hd₁_def, heyv₀_def, heyb_def,
                Finsupp.add_apply, Finsupp.tsub_apply,
                Finsupp.single_apply, reduceCtorEq,
                ↓reduceIte]; omega
            have hinr : d₁ (Sum.inr v) =
                d_q (Sum.inr v) := by
              simp only [hd₁_def, heyv₀_def, heyb_def]
              unfold BinomialEdgeVars at *
              simp only [Finsupp.add_apply,
                Finsupp.tsub_apply, Finsupp.single_apply,
                Sum.inr.injEq]
              rw [if_neg (Ne.symm hv_ne_v₀),
                if_neg (Ne.symm hv_ne_b)]; omega
            rw [hinl, hinr]; exact hCov v hv_τ
          -- Coverage for τ₂.reverse (b → v₀): disjunctive
          -- Internal vertices of τ₂.reverse = internal of τ₂
          have hCov₂ : ∀ v ∈ internalVertices τ₂.reverse,
              d₂ (Sum.inl v) ≥ 1 ∨ d₂ (Sum.inr v) ≥ 1 := by
            intro v hv
            have hv_int := mem_internalVertices_reverse hv
            have hv_τ := hτ₂_int v hv_int
            have hv_ne_a : v ≠ a := by
              intro heq; subst heq
              have hne_τ : τ ≠ [] := by
                intro h; simp [h, internalVertices] at hv_τ
              cases τ with
              | nil => exact absurd rfl hne_τ
              | cons w rest =>
                simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
                simp only [internalVertices,
                  List.tail_cons] at hv_τ
                exact ((List.nodup_cons.mp hND).1)
                  ((List.dropLast_sublist _).mem hv_τ)
            have hv_ne_v₀ : v ≠ v₀ := by
              intro heq; subst heq
              have hne : τ₂ ≠ [] := by
                intro h; simp [h, internalVertices] at hv_int
              exact internal_ne_head hτ₂_nd hv_int hne
                (head_of_head? hτ₂_head).symm
            have hinl : d₂ (Sum.inl v) =
                d_q (Sum.inl v) := by
              simp only [hd₂_def, heyv₀_def, heya_def,
                Finsupp.add_apply, Finsupp.tsub_apply,
                Finsupp.single_apply, reduceCtorEq,
                ↓reduceIte]; omega
            have hinr : d₂ (Sum.inr v) =
                d_q (Sum.inr v) := by
              simp only [hd₂_def, heyv₀_def, heya_def]
              unfold BinomialEdgeVars at *
              simp only [Finsupp.add_apply,
                Finsupp.tsub_apply, Finsupp.single_apply,
                Sum.inr.injEq]
              rw [if_neg (Ne.symm hv_ne_v₀),
                if_neg (Ne.symm hv_ne_a)]; omega
            rw [hinl, hinr]; exact hCov v hv_τ
          -- Apply IH
          have h₁ : binomialEdgeMonomialOrder.IsRemainder
              (monomial d₁ 1 * fij (K := K) a v₀)
              (groebnerBasisSet G) 0 :=
            ih a v₀ τ₁ d₁ hτ₁_len hav₀ hτ₁_head
              hτ₁_last hτ₁_nd hτ₁_walk hCov₁
          -- For fij(b, v₀) via reversed τ₂
          have hτ₂_rev_len : τ₂.reverse.length ≤ n := by
            simp only [List.length_reverse]; exact hτ₂_len
          have hτ₂_rev_head : τ₂.reverse.head? =
              some b := by
            rw [List.head?_reverse]; exact hτ₂_last
          have hτ₂_rev_last : τ₂.reverse.getLast? =
              some v₀ := by
            rw [List.getLast?_reverse]; exact hτ₂_head
          have hτ₂_rev_nd : τ₂.reverse.Nodup :=
            List.nodup_reverse.mpr hτ₂_nd
          have hτ₂_rev_walk : τ₂.reverse.IsChain
              (fun u v => G.Adj u v) :=
            chain'_reverse' G τ₂ hτ₂_walk
          have h₂_pre :
              binomialEdgeMonomialOrder.IsRemainder
              (monomial d₂ 1 * fij (K := K) b v₀)
              (groebnerBasisSet G) 0 :=
            ih b v₀ τ₂.reverse d₂ hτ₂_rev_len hbv₀
              hτ₂_rev_head hτ₂_rev_last hτ₂_rev_nd
              hτ₂_rev_walk hCov₂
          -- fij(v₀, b) = -fij(b, v₀)
          have h₂ :
              binomialEdgeMonomialOrder.IsRemainder
              (monomial d₂ 1 * fij (K := K) v₀ b)
              (groebnerBasisSet G) 0 := by
            have : monomial d₂ (1:K) * fij (K := K) v₀ b
                = -(monomial d₂ 1 * fij (K := K) b v₀) := by
              rw [fij_antisymm (K := K) v₀ b, mul_neg]
            rw [this]; exact isRemainder_neg' _ _ h₂_pre
          -- Algebraic identity
          have halg : monomial d_q (1 : K) * fij a b =
              monomial d₁ 1 * fij (K := K) a v₀ +
              monomial d₂ 1 * fij (K := K) v₀ b := by
            have hle : eyv₀ ≤ d_q := by
              unfold BinomialEdgeVars at *
              exact Finsupp.single_le_iff.mpr hcov_yr
            have hfactor :
                (monomial d_q (1:K) :
                  MvPolynomial (BinomialEdgeVars V) K) =
                monomial (d_q - eyv₀) (1:K) *
                monomial eyv₀ (1:K) := by
              rw [monomial_mul, one_mul,
                tsub_add_cancel_of_le hle]
            have hyv₀ :
                (monomial eyv₀ (1:K) :
                  MvPolynomial (BinomialEdgeVars V) K) =
                y v₀ := rfl
            rw [hfactor, mul_assoc,
                show monomial eyv₀ (1:K) *
                  fij (K := K) a b = y v₀ * fij a b
                  from by rw [← hyv₀],
                fij_telescope (K := K) a v₀ b,
                mul_add, ← mul_assoc, ← mul_assoc]
            congr 1
            · congr 1
              change monomial (d_q - eyv₀) (1:K) *
                monomial eyb (1:K) = monomial d₁ 1
              rw [monomial_mul, one_mul]
            · congr 1
              change monomial (d_q - eyv₀) (1:K) *
                monomial eya (1:K) = monomial d₂ 1
              rw [monomial_mul, one_mul]
          -- Degree bounds
          have hne_deg :
              binomialEdgeMonomialOrder.degree
                (monomial d₁ (1:K) * fij a v₀) ≠
              binomialEdgeMonomialOrder.degree
                (monomial d₂ (1:K) * fij v₀ b) := by
            classical
            have hdeg1 :
                binomialEdgeMonomialOrder.degree
                  (monomial d₁ (1:K) * fij a v₀) =
                d₁ + (Finsupp.single
                  (Sum.inl a : BinomialEdgeVars V) 1 +
                  Finsupp.single
                  (Sum.inr v₀ : BinomialEdgeVars V) 1)
                := by
              rw [degree_mul
                (monomial_eq_zero.not.mpr one_ne_zero)
                (fij_ne_zero a v₀ hav₀),
                degree_monomial, if_neg one_ne_zero,
                fij_degree a v₀ hav₀]
            have fij_v₀b_ne : fij (K := K) v₀ b ≠ 0 := by
              rw [fij_antisymm]
              exact neg_ne_zero.mpr (fij_ne_zero b v₀ hbv₀)
            have hdeg2 :
                binomialEdgeMonomialOrder.degree
                  (monomial d₂ (1:K) * fij v₀ b) =
                d₂ + (Finsupp.single
                  (Sum.inl b : BinomialEdgeVars V) 1 +
                  Finsupp.single
                  (Sum.inr v₀ : BinomialEdgeVars V) 1)
                := by
              rw [degree_mul
                (monomial_eq_zero.not.mpr one_ne_zero)
                fij_v₀b_ne,
                degree_monomial, if_neg one_ne_zero,
                fij_antisymm (K := K) v₀ b,
                MonomialOrder.degree_neg,
                fij_degree b v₀ hbv₀]
            rw [hdeg1, hdeg2]
            intro heq
            have hv := Finsupp.ext_iff.mp heq
              (Sum.inl a : BinomialEdgeVars V)
            -- Fully unfold and simplify at Sum.inl a
            simp only [d₁, d₂, eyv₀, eyb, eya] at hv
            unfold BinomialEdgeVars at hv
            simp only [Finsupp.add_apply,
              Finsupp.tsub_apply, Finsupp.single_apply,
              Sum.inl.injEq, reduceCtorEq, ite_true,
              ite_false,
              if_neg (ne_of_lt hab).symm] at hv
            omega
          obtain ⟨hdeg₁, hdeg₂⟩ :=
            degree_bounds_of_ne _ _ hne_deg
          rw [halg]
          exact isRemainder_add _ _ _ h₁ h₂ hdeg₁ hdeg₂
        · -- v₀ < a, d_q(inl v₀) ≥ 1: x-telescope at v₀
          -- x_{v₀} * fij(a,b) = x_a * fij(v₀,b) + x_b * fij(a,v₀)
          -- fij(v₀,a) comes into play since v₀ < a
          -- fij_x_telescope(v₀, a, b) gives:
          --   x_a * fij(v₀, b) = x_{v₀} * fij(a,b) + x_b * fij(v₀,a)
          -- Rearranging doesn't help directly. Better:
          -- fij_x_telescope(a, v₀, b):
          --   x_{v₀} * fij(a,b) = x_a * fij(v₀,b) + x_b * fij(a,v₀)
          -- fij(v₀, b): v₀ < a < b, so v₀ < b (good order)
          -- fij(a, v₀): a > v₀, so fij(v₀, a) with v₀ < a
          -- fij(a, v₀) = -fij(v₀, a)
          have hv₀b : v₀ < b := lt_trans hv₀a hab
          set ev₀ : BinomialEdgeVars V →₀ ℕ :=
            Finsupp.single (Sum.inl v₀) 1 with hev₀_def
          set ea : BinomialEdgeVars V →₀ ℕ :=
            Finsupp.single (Sum.inl a) 1 with hea_def
          set eb : BinomialEdgeVars V →₀ ℕ :=
            Finsupp.single (Sum.inl b) 1 with heb_def
          set d₁ := d_q - ev₀ + ea with hd₁_def
          set d₂ := d_q - ev₀ + eb with hd₂_def
          -- Sub-walk from v₀ to b (suffix)
          have ⟨τ₂, hτ₂_len, hτ₂_head, hτ₂_last,
              hτ₂_nd, hτ₂_walk, hτ₂_int⟩ :
              ∃ τ₂ : List V,
              τ₂.length ≤ n ∧
              τ₂.head? = some v₀ ∧ τ₂.getLast? = some b ∧
              τ₂.Nodup ∧
              τ₂.IsChain (fun u v => G.Adj u v) ∧
              ∀ u ∈ internalVertices τ₂,
                u ∈ internalVertices τ := by
            have hne : τ ≠ [] := by
              intro h; simp [h, internalVertices] at hv₀_int
            have hv₀_mem : v₀ ∈ τ :=
              mem_of_mem_internalVertices hv₀_int
            set k := τ.idxOf v₀
            have hk_lt : k < τ.length :=
              List.idxOf_lt_length_of_mem hv₀_mem
            have hπk : τ[k]'hk_lt = v₀ :=
              List.getElem_idxOf hk_lt
            have hk_pos : 0 < k := by
              by_contra h; push_neg at h
              have h0 : τ.idxOf v₀ = 0 := Nat.le_zero.mp h
              cases τ with
              | nil => exact absurd rfl hne
              | cons w rest =>
                simp only [List.head?_cons, Option.some.injEq]
                  at hHead
                have : w = v₀ := by
                  have hlt :
                    (w :: rest).idxOf v₀ <
                      (w :: rest).length :=
                    List.idxOf_lt_length_of_mem hv₀_mem
                  have := List.getElem_idxOf hlt
                  simp only [h0, List.getElem_cons_zero] at this; exact this
                exact absurd (this.symm.trans hHead)
                  (ne_of_gt hv₀a).symm
            refine ⟨τ.drop k, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [List.length_drop]; omega
            · rw [List.head?_drop,
                List.getElem?_eq_getElem hk_lt, hπk]
            · rw [List.getLast?_drop,
                if_neg (by omega), hLast]
            · exact (List.drop_sublist k τ).nodup hND
            · exact List.IsChain.drop hWalk k
            · exact fun u hu =>
                internal_of_drop τ k a b hne hND
                  hHead hLast hk_pos hk_lt u hu
          -- Sub-walk from a to v₀ (prefix): reverse to v₀ → a
          have ⟨τ₁, hτ₁_len, hτ₁_head, hτ₁_last,
              hτ₁_nd, hτ₁_walk, hτ₁_int⟩ :
              ∃ τ₁ : List V,
              τ₁.length ≤ n ∧
              τ₁.head? = some a ∧ τ₁.getLast? = some v₀ ∧
              τ₁.Nodup ∧
              τ₁.IsChain (fun u v => G.Adj u v) ∧
              ∀ u ∈ internalVertices τ₁,
                u ∈ internalVertices τ := by
            have hne : τ ≠ [] := by
              intro h; simp [h, internalVertices] at hv₀_int
            have hv₀_mem : v₀ ∈ τ :=
              mem_of_mem_internalVertices hv₀_int
            set k := τ.idxOf v₀
            have hk_lt : k < τ.length :=
              List.idxOf_lt_length_of_mem hv₀_mem
            have hπk : τ[k]'hk_lt = v₀ :=
              List.getElem_idxOf hk_lt
            have hk_lt_pred : k < τ.length - 1 := by
              rcases Nat.lt_or_ge k (τ.length - 1) with
                h | h
              · exact h
              · exfalso
                have hk_eq : k = τ.length - 1 :=
                  Nat.le_antisymm (by omega) h
                have hv₀_last : v₀ = τ.getLast hne := by
                  rw [List.getLast_eq_getElem]
                  exact (show τ[τ.length - 1] = τ[k]
                    from by congr 1; omega).trans hπk
                    |>.symm
                exact (ne_of_gt hv₀b).symm
                  (hv₀_last.trans (Option.some.inj
                    ((List.getLast?_eq_some_getLast hne
                      ).symm.trans hLast)))
            refine ⟨τ.take (k + 1), ?_, ?_, ?_, ?_, ?_, ?_⟩
            · simp [List.length_take]; omega
            · rw [List.head?_take,
                if_neg (by omega), hHead]
            · have : (τ.take (k + 1)).getLast? =
                  some v₀ := by
                rw [List.getLast?_take,
                  if_neg (by omega)]
                have : τ[k]? = some v₀ := by
                  rw [List.getElem?_eq_getElem
                    (show k < τ.length by omega)]
                  exact congrArg some hπk
                simp [this]
              exact this
            · exact (List.take_sublist (k + 1) τ).nodup
                hND
            · exact List.IsChain.take hWalk (k + 1)
            · exact fun u hu =>
                internal_of_take τ k a b hne hND
                  hHead hLast hk_lt_pred u hu
          -- Coverage for τ₂ (v₀ → b): disjunctive
          have hCov₂ : ∀ v ∈ internalVertices τ₂,
              d₁ (Sum.inl v) ≥ 1 ∨ d₁ (Sum.inr v) ≥ 1 := by
            intro v hv
            have hv_τ := hτ₂_int v hv
            have hv_ne_a : v ≠ a := by
              intro heq; subst heq
              have hne_τ : τ ≠ [] := by
                intro h; simp [h, internalVertices] at hv_τ
              cases τ with
              | nil => exact absurd rfl hne_τ
              | cons w rest =>
                simp only [List.head?_cons, Option.some.injEq] at hHead; subst hHead
                simp only [internalVertices,
                  List.tail_cons] at hv_τ
                exact ((List.nodup_cons.mp hND).1)
                  ((List.dropLast_sublist _).mem hv_τ)
            have hv_ne_v₀ : v ≠ v₀ := by
              intro heq; subst heq
              have hne : τ₂ ≠ [] := by
                intro h; simp [h, internalVertices] at hv
              exact internal_ne_head hτ₂_nd hv hne
                (head_of_head? hτ₂_head).symm
            have hinl : d₁ (Sum.inl v) =
                d_q (Sum.inl v) := by
              simp only [hd₁_def, hev₀_def, hea_def]
              unfold BinomialEdgeVars at *
              simp only [Finsupp.add_apply,
                Finsupp.tsub_apply, Finsupp.single_apply,
                Sum.inl.injEq]
              rw [if_neg (Ne.symm hv_ne_v₀),
                if_neg (Ne.symm hv_ne_a)]; omega
            have hinr : d₁ (Sum.inr v) =
                d_q (Sum.inr v) := by
              simp only [hd₁_def, hev₀_def, hea_def,
                Finsupp.add_apply, Finsupp.tsub_apply,
                Finsupp.single_apply, reduceCtorEq,
                ↓reduceIte]; omega
            rw [hinl, hinr]; exact hCov v hv_τ
          -- Coverage for τ₁.reverse (v₀ → a): disjunctive
          have hCov₁ : ∀ v ∈ internalVertices τ₁.reverse,
              d₂ (Sum.inl v) ≥ 1 ∨ d₂ (Sum.inr v) ≥ 1 := by
            intro v hv
            have hv_int := mem_internalVertices_reverse hv
            have hv_τ := hτ₁_int v hv_int
            have hv_ne_b : v ≠ b := by
              intro heq; subst heq
              have hne_τ : τ ≠ [] := by
                intro h; simp [h, internalVertices] at hv_τ
              exact (ne_getLast_of_mem_tdl τ hND hne_τ v
                hv_τ) (Option.some.inj (hLast.symm.trans
                  (List.getLast?_eq_some_getLast hne_τ)))
            have hv_ne_v₀ : v ≠ v₀ := by
              intro heq; subst heq
              have hne : τ₁ ≠ [] := by
                intro h; simp [h, internalVertices] at hv_int
              exact internal_ne_getLast hτ₁_nd hv_int hne
                (getLast_of_getLast? hτ₁_last).symm
            have hinl : d₂ (Sum.inl v) =
                d_q (Sum.inl v) := by
              simp only [hd₂_def, hev₀_def, heb_def]
              unfold BinomialEdgeVars at *
              simp only [Finsupp.add_apply,
                Finsupp.tsub_apply, Finsupp.single_apply,
                Sum.inl.injEq]
              rw [if_neg (Ne.symm hv_ne_v₀),
                if_neg (Ne.symm hv_ne_b)]; omega
            have hinr : d₂ (Sum.inr v) =
                d_q (Sum.inr v) := by
              simp only [hd₂_def, hev₀_def, heb_def,
                Finsupp.add_apply, Finsupp.tsub_apply,
                Finsupp.single_apply, reduceCtorEq,
                ↓reduceIte]; omega
            rw [hinl, hinr]; exact hCov v hv_τ
          -- IH for fij(v₀, b) via τ₂
          have h₁ : binomialEdgeMonomialOrder.IsRemainder
              (monomial d₁ 1 * fij (K := K) v₀ b)
              (groebnerBasisSet G) 0 :=
            ih v₀ b τ₂ d₁ hτ₂_len hv₀b hτ₂_head
              hτ₂_last hτ₂_nd hτ₂_walk hCov₂
          -- IH for fij(v₀, a) via τ₁.reverse
          have hτ₁_rev_len : τ₁.reverse.length ≤ n := by
            simp only [List.length_reverse]; exact hτ₁_len
          have hτ₁_rev_head : τ₁.reverse.head? =
              some v₀ := by
            rw [List.head?_reverse]; exact hτ₁_last
          have hτ₁_rev_last : τ₁.reverse.getLast? =
              some a := by
            rw [List.getLast?_reverse]; exact hτ₁_head
          have hτ₁_rev_nd : τ₁.reverse.Nodup :=
            List.nodup_reverse.mpr hτ₁_nd
          have hτ₁_rev_walk : τ₁.reverse.IsChain
              (fun u v => G.Adj u v) :=
            chain'_reverse' G τ₁ hτ₁_walk
          -- fij(v₀, a): v₀ < a, good order
          have h₂_pre :
              binomialEdgeMonomialOrder.IsRemainder
              (monomial d₂ 1 * fij (K := K) v₀ a)
              (groebnerBasisSet G) 0 :=
            ih v₀ a τ₁.reverse d₂ hτ₁_rev_len hv₀a
              hτ₁_rev_head hτ₁_rev_last hτ₁_rev_nd
              hτ₁_rev_walk hCov₁
          -- fij(a, v₀) = -fij(v₀, a)
          have h₂ :
              binomialEdgeMonomialOrder.IsRemainder
              (monomial d₂ 1 * fij (K := K) a v₀)
              (groebnerBasisSet G) 0 := by
            have : monomial d₂ (1:K) * fij (K := K) a v₀
                = -(monomial d₂ 1 * fij (K := K) v₀ a)
                := by
              rw [fij_antisymm (K := K) a v₀, mul_neg]
            rw [this]; exact isRemainder_neg' _ _ h₂_pre
          -- Algebraic identity:
          -- x_{v₀} * fij(a,b) = x_a * fij(v₀,b) + x_b * fij(a,v₀)
          have halg : monomial d_q (1 : K) * fij a b =
              monomial d₁ 1 * fij (K := K) v₀ b +
              monomial d₂ 1 * fij (K := K) a v₀ := by
            have hle : ev₀ ≤ d_q := by
              unfold BinomialEdgeVars at *
              exact Finsupp.single_le_iff.mpr hcov_xl
            have hfactor :
                (monomial d_q (1:K) :
                  MvPolynomial (BinomialEdgeVars V) K) =
                monomial (d_q - ev₀) (1:K) *
                monomial ev₀ (1:K) := by
              rw [monomial_mul, one_mul,
                tsub_add_cancel_of_le hle]
            have hxv₀ :
                (monomial ev₀ (1:K) :
                  MvPolynomial (BinomialEdgeVars V) K) =
                x v₀ := rfl
            rw [hfactor, mul_assoc,
                show monomial ev₀ (1:K) *
                  fij (K := K) a b = x v₀ * fij a b
                  from by rw [← hxv₀],
                fij_x_telescope (K := K) a v₀ b,
                mul_add, ← mul_assoc, ← mul_assoc]
            congr 1
            · congr 1
              change monomial (d_q - ev₀) (1:K) *
                monomial ea (1:K) = monomial d₁ 1
              rw [monomial_mul, one_mul]
            · congr 1
              change monomial (d_q - ev₀) (1:K) *
                monomial eb (1:K) = monomial d₂ 1
              rw [monomial_mul, one_mul]
          -- Degree bounds: discriminate at Sum.inl v₀
          have hne_deg :
              binomialEdgeMonomialOrder.degree
                (monomial d₁ (1:K) * fij v₀ b) ≠
              binomialEdgeMonomialOrder.degree
                (monomial d₂ (1:K) * fij a v₀) := by
            classical
            have hdeg1 :
                binomialEdgeMonomialOrder.degree
                  (monomial d₁ (1:K) * fij v₀ b) =
                d₁ + (Finsupp.single
                  (Sum.inl v₀ : BinomialEdgeVars V) 1 +
                  Finsupp.single
                  (Sum.inr b : BinomialEdgeVars V) 1)
                := by
              rw [degree_mul
                (monomial_eq_zero.not.mpr one_ne_zero)
                (fij_ne_zero v₀ b hv₀b),
                degree_monomial, if_neg one_ne_zero,
                fij_degree v₀ b hv₀b]
            have fij_av₀_ne : fij (K := K) a v₀ ≠ 0 := by
              rw [fij_antisymm]
              exact neg_ne_zero.mpr (fij_ne_zero v₀ a hv₀a)
            have hdeg2 :
                binomialEdgeMonomialOrder.degree
                  (monomial d₂ (1:K) * fij a v₀) =
                d₂ + (Finsupp.single
                  (Sum.inl v₀ : BinomialEdgeVars V) 1 +
                  Finsupp.single
                  (Sum.inr a : BinomialEdgeVars V) 1)
                := by
              rw [degree_mul
                (monomial_eq_zero.not.mpr one_ne_zero)
                fij_av₀_ne,
                degree_monomial, if_neg one_ne_zero,
                fij_antisymm (K := K) a v₀,
                MonomialOrder.degree_neg,
                fij_degree v₀ a hv₀a]
            rw [hdeg1, hdeg2]
            intro heq
            -- Discriminate at Sum.inr b
            -- LHS at inr b: d₁(inr b) + 0 + 1 = d_q(inr b) + 1
            -- RHS at inr b: d₂(inr b) + 0 + 0 = d_q(inr b)
            have hv := Finsupp.ext_iff.mp heq
              (Sum.inr b : BinomialEdgeVars V)
            simp only [d₁, d₂, ev₀, ea, eb] at hv
            unfold BinomialEdgeVars at hv
            simp only [Finsupp.add_apply,
              Finsupp.tsub_apply, Finsupp.single_apply,
              Sum.inr.injEq, reduceCtorEq, ite_true,
              ite_false,
              if_neg (ne_of_lt hab)] at hv
            omega
          obtain ⟨hdeg₁, hdeg₂⟩ :=
            degree_bounds_of_ne _ _ hne_deg
          rw [halg]
          exact isRemainder_add _ _ _ h₁ h₂ hdeg₁ hdeg₂
      · -- No processable vertices: deterministic coverage
        -- For every internal v:
        --   v > b → d_q(inr v) = 0 (by ¬processable). Combined with hCov: d_q(inl v) ≥ 1.
        --   v < a → d_q(inl v) = 0 (by ¬processable). Combined with hCov: d_q(inr v) ≥ 1.
        -- This gives deterministic coverage matching the admissible path!
        -- Helper: extract the not-processable consequence
        have hNP : ∀ v ∈ internalVertices τ,
            ¬((b < v ∧ d_q (Sum.inr v) ≥ 1) ∨ (v < a ∧ d_q (Sum.inl v) ≥ 1)) := by
          intro v hv habs; exact hProc ⟨v, hv, habs⟩
        have hdiv : d_σ ≤ d_q := by
          intro w
          rcases w with ⟨v⟩ | ⟨v⟩
          · -- w = Sum.inl v
            by_cases hv_filt : v ∈ (internalVertices σ).filter (fun w => b < w)
            · have hv_int_σ : v ∈ internalVertices σ := (List.mem_filter.mp hv_filt).1
              have hjv : b < v := of_decide_eq_true (List.mem_filter.mp hv_filt).2
              rw [pathMonomial_exponent_inl_one (K := K) a b σ v hv_int_σ hjv hσ_int_nd d_σ hd_σ]
              have hv_int_τ := hint_σ_τ v hv_int_σ
              rcases hCov v hv_int_τ with h | h
              · exact h
              · exfalso; exact hNP v hv_int_τ (Or.inl ⟨hjv, h⟩)
            · rw [pathMonomial_exponent_inl_zero (K := K) a b σ v hv_filt d_σ hd_σ]
              exact Nat.zero_le _
          · -- w = Sum.inr v
            by_cases hv_filt : v ∈ (internalVertices σ).filter (fun w => w < a)
            · have hv_int_σ : v ∈ internalVertices σ := (List.mem_filter.mp hv_filt).1
              have hvi : v < a := of_decide_eq_true (List.mem_filter.mp hv_filt).2
              rw [pathMonomial_exponent_inr_one (K := K) a b σ v hv_int_σ hvi hσ_int_nd d_σ hd_σ]
              have hv_int_τ := hint_σ_τ v hv_int_σ
              rcases hCov v hv_int_τ with h | h
              · exfalso; exact hNP v hv_int_τ (Or.inr ⟨hvi, h⟩)
              · exact h
            · rw [pathMonomial_exponent_inr_zero (K := K) a b σ v hv_filt d_σ hd_σ]
              exact Nat.zero_le _
        exact isRemainder_fij_via_groebnerElement G a b σ hσ
          (monomial d_q 1) d_q rfl d_σ hd_σ hdiv

/-! ### The walk construction -/

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma walk_from_shared_first_aux (G : SimpleGraph V) :
    ∀ (n : ℕ) (a b c : V) (π σ : List V),
    π.length + σ.length ≤ n →
    π.head? = some a → π.getLast? = some b →
    π.Nodup → π.IsChain (fun u v => G.Adj u v) →
    σ.head? = some a → σ.getLast? = some c →
    σ.Nodup → σ.IsChain (fun u v => G.Adj u v) →
    b ≠ c →
    ∃ τ : List V, τ.head? = some b ∧ τ.getLast? = some c ∧ τ.Nodup ∧
    τ.IsChain (fun u v => G.Adj u v) ∧
    (∀ v ∈ internalVertices τ,
      v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = a) := by
  classical
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
        | nil => simp only [List.head?_nil, reduceCtorEq] at hσh
        | cons x rest =>
          simp only [List.head?_cons, Option.some.injEq] at hσh; subst hσh
          rw [List.nodup_cons] at hσnd; exact absurd hv_σt hσnd.1
      -- idxOf v > 0 in σ since v ≠ head σ = a
      have hidx_pos : 0 < σ.idxOf v := by
        cases σ with
        | nil => exact absurd rfl hσ_ne
        | cons x rest =>
          have hxa : x = a := by
            simp only [List.head?_cons, Option.some.injEq] at hσh; exact hσh
          change 0 < List.findIdx (fun w => w == v) (x :: rest)
          simp only [List.findIdx_cons]
          have hxv : ¬(x = v) := by rw [hxa]; exact Ne.symm hva
          simp only [BEq.beq, hxv]
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
          simp only [ne_eq, List.drop_eq_nil_iff, not_le]; exact idxOf_lt hv_π
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
          simp only [ne_eq, List.drop_eq_nil_iff, not_le]; exact idxOf_lt hv_σ
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
            simp only [List.head?_cons, Option.some.injEq] at hσh hσt
            subst hσh; subst hσt
            simp only [List.getLast?_singleton, Option.some.injEq] at hσl
            exact hσl.symm
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
            simp only [List.tail_cons] at hσt ⊢
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
              have hs_eq : s = a := by
                simp only [List.head?_cons, Option.some.injEq] at hσh; exact hσh
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
                    simp only [List.tail_cons] at hσt; cases rest with
                    | nil => exact absurd rfl hσt
                    | cons y rest' =>
                      simp only [List.tail_cons, List.getLast?_cons_cons] at hσl ⊢
                      exact hσl
                exact getLast_of_getLast? this
              exact absurd hτ_last_eq.symm (internal_ne_getLast hτ_nd hw hτ_ne)
            right; left; exact mem_internalVertices_of_ne hσnd hw_σ hσ_ne
              (by rw [head_of_head? hσh]; exact hwa)
              (by rw [getLast_of_getLast? hσl]; exact hw_ne_c)

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
lemma walk_from_shared_first (G : SimpleGraph V)
    (a b c : V) (π σ : List V)
    (hπ_head : π.head? = some a) (hπ_last : π.getLast? = some b)
    (hπ_nd : π.Nodup) (hπ_walk : π.IsChain (fun u v => G.Adj u v))
    (hσ_head : σ.head? = some a) (hσ_last : σ.getLast? = some c)
    (hσ_nd : σ.Nodup) (hσ_walk : σ.IsChain (fun u v => G.Adj u v))
    (hbc : b ≠ c) :
    ∃ τ : List V, τ.head? = some b ∧ τ.getLast? = some c ∧ τ.Nodup ∧
    τ.IsChain (fun u v => G.Adj u v) ∧
    (∀ v ∈ internalVertices τ,
      v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = a) :=
  walk_from_shared_first_aux G _ a b c π σ le_rfl
    hπ_head hπ_last hπ_nd hπ_walk hσ_head hσ_last hσ_nd hσ_walk hbc


end

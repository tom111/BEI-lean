import BEI.GraphProperties

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V]

/-!
# Admissible paths and their associated monomials

This file defines the monomial `u_π` associated to an admissible path `π`
from `i` to `j` in G, and the Gröbner basis element `u_π · f_{ij}`.

The monomial is:
  `u_π = (∏_{v ∈ internals(π), v > j} x_v) · (∏_{v ∈ internals(π), v < i} y_v)`

## Reference: Herzog et al. (2010), Section 2
-/

noncomputable section

open MvPolynomial

/-! ## The monomial u_π -/

/--
The internal vertices of a path `π` from `i` to `j`: all vertices except the
first and last.
-/
def internalVertices (π : List V) : List V := π.tail.dropLast

/--
The **path monomial** `u_π` for an admissible path π from i to j:
  `u_π = (∏_{v > j, v internal} x_v) · (∏_{v < i, v internal} y_v)`
-/
noncomputable def pathMonomial (i j : V) (π : List V) :
    MvPolynomial (BinomialEdgeVars V) K :=
  let internals := internalVertices π
  let xPart := (internals.filter (fun v => j < v)).map (fun v => x v)
  let yPart := (internals.filter (fun v => v < i)).map (fun v => y v)
  xPart.prod * yPart.prod

/-- For the trivial path [i, j], the path monomial is 1 (no internal vertices). -/
@[simp]
theorem pathMonomial_pair (i j : V) :
    pathMonomial (K := K) i j [i, j] = 1 := by
  simp [pathMonomial, internalVertices]

/--
The **Gröbner basis element** for path π from i to j:
  `u_π · f_{ij} = u_π · (x_i y_j - x_j y_i)`
-/
noncomputable def groebnerElement (i j : V) (π : List V) :
    MvPolynomial (BinomialEdgeVars V) K :=
  pathMonomial i j π * (x i * y j - x j * y i)

/-- For the trivial path, the Gröbner element equals the generator `f_{ij}`. -/
@[simp]
theorem groebnerElement_pair (i j : V) :
    groebnerElement (K := K) i j [i, j] = x i * y j - x j * y i := by
  simp [groebnerElement]

/--
The full **reduced Gröbner basis set** of J_G:
  `G = { u_π · f_{ij} | i < j, π admissible path from i to j in G }`
-/
def groebnerBasisSet (G : SimpleGraph V) :
    Set (MvPolynomial (BinomialEdgeVars V) K) :=
  { p | ∃ (i j : V) (π : List V) (_ : IsAdmissiblePath G i j π),
        p = groebnerElement i j π }

/-! ## Membership in J_G -/

/-!
### Helper lemmas for groebnerElem_mem_aux
-/

/-- The reversed walk in an undirected graph is still a walk. -/
private lemma chain'_reverse (G : SimpleGraph V) (π : List V)
    (hW : π.Chain' (fun a b => G.Adj a b)) :
    π.reverse.Chain' (fun a b => G.Adj a b) := by
  change List.IsChain (fun a b => G.Adj a b) π.reverse
  rw [List.isChain_reverse]
  exact List.IsChain.imp (fun _ _ h => G.symm h) (hW : List.IsChain _ π)

/--
Path monomial factorization at a below-i internal vertex v₀ (Case A).

Let v₀ be the maximum internal vertex with v₀ < i, and let π be split into
- α' = the prefix [i, ..., v₀] reversed to [v₀, ..., i]
- β = the suffix [v₀, ..., j]

Then `pathMonomial i j π = y v₀ * pathMonomial v₀ i α' * pathMonomial v₀ j β`.

This is the key algebraic identity enabling the induction; proof deferred.
-/
private lemma pathMonomial_split_below (G : SimpleGraph V) (i j v₀ : V)
    (hij : i < j) (hv₀i : v₀ < i) (π β α' : List V)
    (hπHead : π.head? = some i) (hπLast : π.getLast? = some j)
    (hπND : π.Nodup)
    (hπInt : ∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v)
    (hv₀Int : v₀ ∈ internalVertices π)
    (hv₀Max : ∀ w ∈ internalVertices π, w < i → w ≤ v₀)
    (hβ : β = π.drop (π.idxOf v₀))
    (hα' : α' = (π.take (π.idxOf v₀ + 1)).reverse) :
    pathMonomial (K := K) i j π =
      y v₀ * pathMonomial v₀ i α' * pathMonomial v₀ j β := by
  -- Step 1: index setup
  have hv₀_in_π : v₀ ∈ π :=
    (List.tail_sublist π).subset ((List.dropLast_sublist π.tail).subset hv₀Int)
  let k := π.idxOf v₀
  have hk_lt : k < π.length := List.idxOf_lt_length_of_mem hv₀_in_π
  have hπk : π[k] = v₀ := List.getElem_idxOf hk_lt
  have hne : π ≠ [] := List.ne_nil_iff_length_pos.mpr (by omega)
  have h0lt : 0 < π.length := List.length_pos_of_ne_nil hne
  have hπ0i : π[0] = i := by
    have h0 : π[0]? = some i := by rwa [← List.head?_eq_getElem?]
    exact Option.some.inj ((List.getElem?_eq_getElem h0lt).symm.trans h0)
  have hπ_last_j : π[π.length - 1] = j := by
    rw [← (List.getLast_eq_getElem hne)]
    exact Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have heq : π[0] = v₀ := by simp only [h] at hπk; exact hπk
      exact absurd (heq.symm.trans hπ0i) (ne_of_lt hv₀i)
    · exact h
  have hk_lt_pred : k < π.length - 1 := by
    rcases Nat.lt_or_ge k (π.length - 1) with h | h
    · exact h
    · exfalso
      have hk_eq : k = π.length - 1 := Nat.le_antisymm (by omega) (by omega)
      have heq : v₀ = j := by
        have h1 : π[k]? = some v₀ :=
          (List.getElem?_eq_getElem hk_lt).trans (congrArg some hπk)
        have h2 : π[π.length - 1]? = some j :=
          (List.getElem?_eq_getElem (by omega)).trans (congrArg some hπ_last_j)
        have h3 : π[k]? = π[π.length - 1]? := by congr 1
        exact Option.some.inj (h1.symm.trans (h3.trans h2))
      exact absurd heq (ne_of_lt (lt_trans hv₀i hij))
  -- Step 2: list equality for internalVertices
  have hintEq : internalVertices π = (internalVertices α').reverse ++ [v₀] ++ internalVertices β := by
    simp only [internalVertices]
    rw [hα', hβ]
    have htake_ne : π.take k ≠ [] := by simp [List.take_eq_nil_iff, hk_pos.ne', hne]
    have hdrop_ne : π.drop (k + 1) ≠ [] := by
      intro h; simp [List.drop_eq_nil_iff] at h; omega
    have hrev_tail : ((π.take (k + 1)).reverse).tail = (π.take k).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt, Option.toList_some,
          List.reverse_append, List.reverse_singleton]; rfl
    have hint_α'_rev : (((π.take (k + 1)).reverse).tail.dropLast).reverse = (π.take k).tail := by
      rw [hrev_tail, List.dropLast_reverse, List.reverse_reverse]
    have hβ_tail : (π.drop k).tail = π.drop (k + 1) := by
      rw [← List.getElem_cons_drop hk_lt, List.tail_cons]
    have htail_cons : π.tail = (π.take k).tail ++ (π[k] :: π.drop (k + 1)) := by
      have h1 : π.drop k = π[k] :: π.drop (k + 1) := (List.getElem_cons_drop hk_lt).symm
      have h2 : π = π.take k ++ (π[k] :: π.drop (k + 1)) := by
        have := List.take_append_drop k π; rw [h1] at this; exact this.symm
      rw [congrArg List.tail h2, List.tail_append_of_ne_nil htake_ne]
    have htail_dl : π.tail.dropLast =
        (π.take k).tail ++ [π[k]] ++ (π.drop (k + 1)).dropLast := by
      rw [congrArg List.dropLast htail_cons,
          List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
          List.dropLast_cons_of_ne_nil hdrop_ne]
      simp [List.append_assoc]
    rw [hint_α'_rev]
    rw [← hβ_tail, hπk] at htail_dl
    exact htail_dl
  -- Step 3: non-membership / Nodup facts
  have hint_nd : (internalVertices π).Nodup :=
    (hπND.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  have hi_not_int : i ∉ internalVertices π := by
    simp only [internalVertices]; intro h
    cases π with
    | nil => exact absurd rfl hne
    | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
      exact (List.nodup_cons.mp hπND).1 ((List.dropLast_sublist _).subset h)
  have hj_not_int : j ∉ internalVertices π := by
    simp only [internalVertices]; intro h
    have hj_last : π.getLast hne = j :=
      Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
    have hj_count : π.count j = 1 :=
      List.nodup_iff_count_le_one.mp hπND |> fun hle =>
        Nat.le_antisymm (hle _) (List.count_pos_iff.mpr (hj_last ▸ List.getLast_mem hne))
    have hmem_dl : j ∈ π.dropLast := by
      cases π with
      | nil => exact absurd rfl hne
      | cons a rest =>
        simp only [List.tail_cons] at h; cases rest with
        | nil => simp at h
        | cons b rest2 =>
          rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b rest2)]
          exact List.mem_cons_of_mem a h
    have hpos : 0 < π.dropLast.count j := List.count_pos_iff.mpr hmem_dl
    have heq := congrArg (List.count j) (List.dropLast_append_getLast hne)
    simp only [List.count_append, hj_last, List.count_singleton_self] at heq
    omega
  have hv₀_not_int_α' : v₀ ∉ internalVertices α' := by
    intro h
    have hint_nd' := hint_nd
    rw [hintEq] at hint_nd'
    have hnd1 := (List.nodup_append.mp hint_nd').1
    exact absurd rfl ((List.nodup_append.mp hnd1).2.2 v₀ (List.mem_reverse.mpr h) v₀
      (List.mem_singleton_self v₀))
  have hv₀_not_int_β : v₀ ∉ internalVertices β := by
    intro h
    have hint_nd' := hint_nd
    rw [hintEq] at hint_nd'
    exact absurd rfl ((List.nodup_append.mp hint_nd').2.2 v₀
      (List.mem_append_right _ (List.mem_singleton_self v₀)) v₀ h)
  -- Step 4: filter equalities (using membership + hπInt)
  have hα'_sub : ∀ v ∈ internalVertices α', v ∈ internalVertices π := fun v hv => by
    rw [hintEq]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_reverse.mpr hv))
  have hβ_sub : ∀ v ∈ internalVertices β, v ∈ internalVertices π := fun v hv => by
    rw [hintEq]; exact List.mem_append_right _ hv
  have hfilt_α'_x : (internalVertices α').filter (fun v => decide (j < v)) =
      (internalVertices α').filter (fun v => decide (i < v)) := by
    apply List.filter_congr; intro v hv
    have hv_π : v ∈ π :=
      (List.tail_sublist _).subset ((List.dropLast_sublist _).subset (hα'_sub v hv))
    rcases hπInt v hv_π with rfl | rfl | hlt | hgt
    · exact absurd (hα'_sub v hv) hi_not_int
    · exact absurd (hα'_sub v hv) hj_not_int
    · simp [not_lt.mpr (le_of_lt (lt_trans hlt hij)), not_lt.mpr (le_of_lt hlt)]
    · simp [hgt, lt_trans hij hgt]
  have hfilt_α'_y : (internalVertices α').filter (fun v => decide (v < i)) =
      (internalVertices α').filter (fun v => decide (v < v₀)) := by
    apply List.filter_congr; intro v hv
    have hv_π : v ∈ π :=
      (List.tail_sublist _).subset ((List.dropLast_sublist _).subset (hα'_sub v hv))
    rcases hπInt v hv_π with rfl | rfl | hlt | hgt
    · exact absurd (hα'_sub v hv) hi_not_int
    · exact absurd (hα'_sub v hv) hj_not_int
    · have hle := hv₀Max v (hα'_sub v hv) hlt
      simp [hlt, lt_of_le_of_ne hle (fun h => hv₀_not_int_α' (h ▸ hv))]
    · simp [not_lt.mpr (le_of_lt (lt_trans hij hgt)),
            not_lt.mpr (le_of_lt (lt_trans hv₀i (lt_trans hij hgt)))]
  have hfilt_β_y : (internalVertices β).filter (fun v => decide (v < i)) =
      (internalVertices β).filter (fun v => decide (v < v₀)) := by
    apply List.filter_congr; intro v hv
    have hv_π : v ∈ π :=
      (List.tail_sublist _).subset ((List.dropLast_sublist _).subset (hβ_sub v hv))
    rcases hπInt v hv_π with rfl | rfl | hlt | hgt
    · exact absurd (hβ_sub v hv) hi_not_int
    · exact absurd (hβ_sub v hv) hj_not_int
    · have hle := hv₀Max v (hβ_sub v hv) hlt
      simp [hlt, lt_of_le_of_ne hle (fun h => hv₀_not_int_β (h ▸ hv))]
    · simp [not_lt.mpr (le_of_lt (lt_trans hij hgt)),
            not_lt.mpr (le_of_lt (lt_trans hv₀i (lt_trans hij hgt)))]
  -- Step 5: algebraic closure
  simp only [pathMonomial, internalVertices]
  rw [show π.tail.dropLast = (α'.tail.dropLast).reverse ++ [v₀] ++ β.tail.dropLast from by
    have := hintEq; simp only [internalVertices] at this; exact this]
  have hjv₀ : decide (j < v₀) = false :=
    decide_eq_false (not_lt.mpr (le_of_lt (lt_trans hv₀i hij)))
  have hiv₀ : decide (v₀ < i) = true := decide_eq_true hv₀i
  have hfα'_x' : α'.tail.dropLast.filter (fun v => decide (j < v)) =
      α'.tail.dropLast.filter (fun v => decide (i < v)) := by
    have := hfilt_α'_x; simp only [internalVertices] at this; exact this
  have hfα'_y' : α'.tail.dropLast.filter (fun v => decide (v < i)) =
      α'.tail.dropLast.filter (fun v => decide (v < v₀)) := by
    have := hfilt_α'_y; simp only [internalVertices] at this; exact this
  have hfβ_y' : β.tail.dropLast.filter (fun v => decide (v < i)) =
      β.tail.dropLast.filter (fun v => decide (v < v₀)) := by
    have := hfilt_β_y; simp only [internalVertices] at this; exact this
  have hx : (α'.tail.dropLast.reverse ++ [v₀] ++ β.tail.dropLast).filter
        (fun v => decide (j < v)) =
      (α'.tail.dropLast.filter (fun v => decide (i < v))).reverse ++
        β.tail.dropLast.filter (fun v => decide (j < v)) := by
    simp only [List.filter_append, List.filter_reverse, hfα'_x']; simp [hjv₀]
  have hy : (α'.tail.dropLast.reverse ++ [v₀] ++ β.tail.dropLast).filter
        (fun v => decide (v < i)) =
      (α'.tail.dropLast.filter (fun v => decide (v < v₀))).reverse ++ [v₀] ++
        β.tail.dropLast.filter (fun v => decide (v < v₀)) := by
    simp only [List.filter_append, List.filter_reverse, hfα'_y', hfβ_y']; simp [hiv₀]
  rw [hx, hy]
  simp only [List.map_append, List.map_reverse, List.prod_append, List.prod_reverse,
             List.map_singleton, List.prod_singleton, x, y]
  ring

/--
Path monomial factorization at an above-j internal vertex v₀ (Case B).

`pathMonomial i j π = x v₀ * pathMonomial j v₀ β.reverse * pathMonomial i v₀ α'.reverse`.
-/
private lemma pathMonomial_split_above (G : SimpleGraph V) (i j v₀ : V)
    (hij : i < j) (hv₀j : j < v₀) (π β α' : List V)
    (hπHead : π.head? = some i) (hπLast : π.getLast? = some j)
    (hπND : π.Nodup)
    (hπInt : ∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v)
    (hv₀Int : v₀ ∈ internalVertices π)
    (hv₀Min : ∀ w ∈ internalVertices π, j < w → v₀ ≤ w)
    (hβ : β = π.drop (π.idxOf v₀))
    (hα' : α' = (π.take (π.idxOf v₀ + 1)).reverse) :
    pathMonomial (K := K) i j π =
      x v₀ * pathMonomial j v₀ β.reverse * pathMonomial i v₀ α'.reverse := by
  -- Step 1: index setup
  have hv₀_in_π : v₀ ∈ π :=
    (List.tail_sublist π).subset ((List.dropLast_sublist π.tail).subset hv₀Int)
  let k := π.idxOf v₀
  have hk_lt : k < π.length := List.idxOf_lt_length_of_mem hv₀_in_π
  have hπk : π[k] = v₀ := List.getElem_idxOf hk_lt
  have hne : π ≠ [] := List.ne_nil_iff_length_pos.mpr (by omega)
  have h0lt : 0 < π.length := List.length_pos_of_ne_nil hne
  have hπ0i : π[0] = i := by
    have h0 : π[0]? = some i := by rwa [← List.head?_eq_getElem?]
    exact Option.some.inj ((List.getElem?_eq_getElem h0lt).symm.trans h0)
  have hπ_last_j : π[π.length - 1] = j := by
    rw [← (List.getLast_eq_getElem hne)]
    exact Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have heq : π[0] = v₀ := by simp only [h] at hπk; exact hπk
      exact absurd (heq.symm.trans hπ0i) (ne_of_gt (lt_trans hij hv₀j))
    · exact h
  have hk_lt_pred : k < π.length - 1 := by
    rcases Nat.lt_or_ge k (π.length - 1) with h | h
    · exact h
    · exfalso
      have hk_eq : k = π.length - 1 := Nat.le_antisymm (by omega) (by omega)
      have heq : v₀ = j := by
        have h1 : π[k]? = some v₀ :=
          (List.getElem?_eq_getElem hk_lt).trans (congrArg some hπk)
        have h2 : π[π.length - 1]? = some j :=
          (List.getElem?_eq_getElem (by omega)).trans (congrArg some hπ_last_j)
        have h3 : π[k]? = π[π.length - 1]? := by congr 1
        exact Option.some.inj (h1.symm.trans (h3.trans h2))
      exact absurd heq (ne_of_gt hv₀j)
  -- Step 2: list equality for internalVertices (identical to split_below)
  have hintEq : internalVertices π = (internalVertices α').reverse ++ [v₀] ++ internalVertices β := by
    simp only [internalVertices]
    rw [hα', hβ]
    have htake_ne : π.take k ≠ [] := by simp [List.take_eq_nil_iff, hk_pos.ne', hne]
    have hdrop_ne : π.drop (k + 1) ≠ [] := by
      intro h; simp [List.drop_eq_nil_iff] at h; omega
    have hrev_tail : ((π.take (k + 1)).reverse).tail = (π.take k).reverse := by
      rw [List.take_add_one, List.getElem?_eq_getElem hk_lt, Option.toList_some,
          List.reverse_append, List.reverse_singleton]; rfl
    have hint_α'_rev : (((π.take (k + 1)).reverse).tail.dropLast).reverse = (π.take k).tail := by
      rw [hrev_tail, List.dropLast_reverse, List.reverse_reverse]
    have hβ_tail : (π.drop k).tail = π.drop (k + 1) := by
      rw [← List.getElem_cons_drop hk_lt, List.tail_cons]
    have htail_cons : π.tail = (π.take k).tail ++ (π[k] :: π.drop (k + 1)) := by
      have h1 : π.drop k = π[k] :: π.drop (k + 1) := (List.getElem_cons_drop hk_lt).symm
      have h2 : π = π.take k ++ (π[k] :: π.drop (k + 1)) := by
        have := List.take_append_drop k π; rw [h1] at this; exact this.symm
      rw [congrArg List.tail h2, List.tail_append_of_ne_nil htake_ne]
    have htail_dl : π.tail.dropLast =
        (π.take k).tail ++ [π[k]] ++ (π.drop (k + 1)).dropLast := by
      rw [congrArg List.dropLast htail_cons,
          List.dropLast_append_of_ne_nil (List.cons_ne_nil _ _),
          List.dropLast_cons_of_ne_nil hdrop_ne]
      simp [List.append_assoc]
    rw [hint_α'_rev]
    rw [← hβ_tail, hπk] at htail_dl
    exact htail_dl
  -- Step 3: non-membership / Nodup facts
  have hint_nd : (internalVertices π).Nodup :=
    (hπND.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  have hi_not_int : i ∉ internalVertices π := by
    simp only [internalVertices]; intro h
    cases π with
    | nil => exact absurd rfl hne
    | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
      exact (List.nodup_cons.mp hπND).1 ((List.dropLast_sublist _).subset h)
  have hj_not_int : j ∉ internalVertices π := by
    simp only [internalVertices]; intro h
    have hj_last : π.getLast hne = j :=
      Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
    have hj_count : π.count j = 1 :=
      List.nodup_iff_count_le_one.mp hπND |> fun hle =>
        Nat.le_antisymm (hle _) (List.count_pos_iff.mpr (hj_last ▸ List.getLast_mem hne))
    have hmem_dl : j ∈ π.dropLast := by
      cases π with
      | nil => exact absurd rfl hne
      | cons a rest =>
        simp only [List.tail_cons] at h; cases rest with
        | nil => simp at h
        | cons b rest2 =>
          rw [List.dropLast_cons_of_ne_nil (List.cons_ne_nil b rest2)]
          exact List.mem_cons_of_mem a h
    have hpos : 0 < π.dropLast.count j := List.count_pos_iff.mpr hmem_dl
    have heq := congrArg (List.count j) (List.dropLast_append_getLast hne)
    simp only [List.count_append, hj_last, List.count_singleton_self] at heq
    omega
  have hv₀_not_int_α' : v₀ ∉ internalVertices α' := by
    intro h
    have hint_nd' := hint_nd
    rw [hintEq] at hint_nd'
    have hnd1 := (List.nodup_append.mp hint_nd').1
    exact absurd rfl ((List.nodup_append.mp hnd1).2.2 v₀ (List.mem_reverse.mpr h) v₀
      (List.mem_singleton_self v₀))
  have hv₀_not_int_β : v₀ ∉ internalVertices β := by
    intro h
    have hint_nd' := hint_nd
    rw [hintEq] at hint_nd'
    exact absurd rfl ((List.nodup_append.mp hint_nd').2.2 v₀
      (List.mem_append_right _ (List.mem_singleton_self v₀)) v₀ h)
  -- Step 4: subset facts
  have hα'_sub : ∀ v ∈ internalVertices α', v ∈ internalVertices π := fun v hv => by
    rw [hintEq]; exact List.mem_append_left _ (List.mem_append_left _
      (List.mem_reverse.mpr hv))
  have hβ_sub : ∀ v ∈ internalVertices β, v ∈ internalVertices π := fun v hv => by
    rw [hintEq]; exact List.mem_append_right _ hv
  -- Step 5: reverse identities (β.reverse and α'.reverse internal vertices)
  have hβ_rev_int : β.reverse.tail.dropLast = (β.tail.dropLast).reverse := by
    rw [List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]
  have hα'_rev_int : α'.reverse.tail.dropLast = (α'.tail.dropLast).reverse := by
    rw [List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]
  -- Step 6: filter equalities (adapted for Case B: v₀ > j)
  have hfilt_α'_x : (internalVertices α').filter (fun v => decide (j < v)) =
      (internalVertices α').filter (fun v => decide (v₀ < v)) := by
    apply List.filter_congr; intro v hv
    have hv_π : v ∈ π :=
      (List.tail_sublist _).subset ((List.dropLast_sublist _).subset (hα'_sub v hv))
    rcases hπInt v hv_π with rfl | rfl | hlt | hgt
    · exact absurd (hα'_sub v hv) hi_not_int
    · exact absurd (hα'_sub v hv) hj_not_int
    · simp [not_lt.mpr (le_of_lt (lt_trans hlt hij)),
            not_lt.mpr (le_of_lt (lt_trans (lt_trans hlt hij) hv₀j))]
    · have hle := hv₀Min v (hα'_sub v hv) hgt
      simp [hgt, lt_of_le_of_ne hle (fun h => hv₀_not_int_α' (h ▸ hv))]
  have hfilt_β_x : (internalVertices β).filter (fun v => decide (j < v)) =
      (internalVertices β).filter (fun v => decide (v₀ < v)) := by
    apply List.filter_congr; intro v hv
    have hv_π : v ∈ π :=
      (List.tail_sublist _).subset ((List.dropLast_sublist _).subset (hβ_sub v hv))
    rcases hπInt v hv_π with rfl | rfl | hlt | hgt
    · exact absurd (hβ_sub v hv) hi_not_int
    · exact absurd (hβ_sub v hv) hj_not_int
    · simp [not_lt.mpr (le_of_lt (lt_trans hlt hij)),
            not_lt.mpr (le_of_lt (lt_trans (lt_trans hlt hij) hv₀j))]
    · have hle := hv₀Min v (hβ_sub v hv) hgt
      simp [hgt, lt_of_le_of_ne hle (fun h => hv₀_not_int_β (h ▸ hv))]
  have hfilt_β_y : (internalVertices β).filter (fun v => decide (v < i)) =
      (internalVertices β).filter (fun v => decide (v < j)) := by
    apply List.filter_congr; intro v hv
    have hv_π : v ∈ π :=
      (List.tail_sublist _).subset ((List.dropLast_sublist _).subset (hβ_sub v hv))
    rcases hπInt v hv_π with rfl | rfl | hlt | hgt
    · exact absurd (hβ_sub v hv) hi_not_int
    · exact absurd (hβ_sub v hv) hj_not_int
    · simp [hlt, lt_trans hlt hij]
    · simp [not_lt.mpr (le_of_lt (lt_trans hij hgt)), not_lt.mpr (le_of_lt hgt)]
  -- Step 7: algebraic closure
  simp only [pathMonomial, internalVertices]
  rw [show π.tail.dropLast = (α'.tail.dropLast).reverse ++ [v₀] ++ β.tail.dropLast from by
    have := hintEq; simp only [internalVertices] at this; exact this]
  rw [hβ_rev_int, hα'_rev_int]
  have hjv₀ : decide (j < v₀) = true := decide_eq_true hv₀j
  have hiv₀ : decide (v₀ < i) = false :=
    decide_eq_false (not_lt.mpr (le_of_lt (lt_trans hij hv₀j)))
  have hfα'_x' : α'.tail.dropLast.filter (fun v => decide (j < v)) =
      α'.tail.dropLast.filter (fun v => decide (v₀ < v)) := by
    have := hfilt_α'_x; simp only [internalVertices] at this; exact this
  have hfβ_x' : β.tail.dropLast.filter (fun v => decide (j < v)) =
      β.tail.dropLast.filter (fun v => decide (v₀ < v)) := by
    have := hfilt_β_x; simp only [internalVertices] at this; exact this
  have hfβ_y' : β.tail.dropLast.filter (fun v => decide (v < i)) =
      β.tail.dropLast.filter (fun v => decide (v < j)) := by
    have := hfilt_β_y; simp only [internalVertices] at this; exact this
  have hx : ((α'.tail.dropLast).reverse ++ [v₀] ++ β.tail.dropLast).filter
        (fun v => decide (j < v)) =
      (α'.tail.dropLast.filter (fun v => decide (v₀ < v))).reverse ++ [v₀] ++
        β.tail.dropLast.filter (fun v => decide (v₀ < v)) := by
    simp only [List.filter_append, List.filter_reverse, hfα'_x', hfβ_x']; simp [hjv₀]
  have hy : ((α'.tail.dropLast).reverse ++ [v₀] ++ β.tail.dropLast).filter
        (fun v => decide (v < i)) =
      (α'.tail.dropLast.filter (fun v => decide (v < i))).reverse ++
        β.tail.dropLast.filter (fun v => decide (v < j)) := by
    simp only [List.filter_append, List.filter_reverse, hfβ_y']; simp [hiv₀]
  rw [hx, hy]
  simp only [List.map_append, List.map_reverse, List.prod_append, List.prod_reverse,
             List.map_singleton, List.prod_singleton, List.filter_reverse, x, y]
  ring

/--
Sub-walk properties: the drop and take-reverse at an internal vertex's position satisfy
the head, last, nodup, and internal-vertex conditions.
These are all list-manipulation facts; deferred as sorry.
-/
private lemma subwalk_props (G : SimpleGraph V) (π : List V) (v₀ i j : V)
    (hij : i < j)
    (hπHead : π.head? = some i) (hπLast : π.getLast? = some j)
    (hπND : π.Nodup) (hπLen : π.length ≥ 3)
    (hπInt : ∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v)
    (hv₀Int : v₀ ∈ internalVertices π)
    (hv₀Max : ∀ w ∈ internalVertices π, w < i → w ≤ v₀)
    (hv₀j : v₀ < j)
    (hπW : π.Chain' (fun a b => G.Adj a b)) :
    let k := π.idxOf v₀
    let β := π.drop k
    let α' := (π.take (k + 1)).reverse
    -- Properties of β (walk from v₀ to j)
    β.head? = some v₀ ∧ β.getLast? = some j ∧ β.length < π.length ∧ β.Nodup ∧
    (∀ v ∈ β, v = v₀ ∨ v = j ∨ v < v₀ ∨ j < v) ∧
    β.Chain' (fun a b => G.Adj a b) ∧
    -- Properties of α' (walk from v₀ to i)
    α'.head? = some v₀ ∧ α'.getLast? = some i ∧ α'.length < π.length ∧ α'.Nodup ∧
    (∀ v ∈ α', v = v₀ ∨ v = i ∨ v < v₀ ∨ i < v) ∧
    α'.Chain' (fun a b => G.Adj a b) := by
  intro k β α'
  -- Setup: v₀ in π, k = idxOf v₀
  have hv₀_in_π : v₀ ∈ π :=
    (List.tail_sublist π).subset ((List.dropLast_sublist π.tail).subset hv₀Int)
  have hk_lt : k < π.length := List.idxOf_lt_length_of_mem hv₀_in_π
  have hπk : π[k] = v₀ := List.getElem_idxOf hk_lt
  have hne : π ≠ [] := by intro h; simp [h] at hπHead
  have h0lt : 0 < π.length := by omega
  have hπ0i : π[0] = i := by
    have h0 : π[0]? = some i := by rwa [← List.head?_eq_getElem?]
    exact Option.some.inj ((List.getElem?_eq_getElem h0lt).symm.trans h0)
  have hπ_last_j : π[π.length - 1] = j := by
    rw [← (List.getLast_eq_getElem hne)]
    exact Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
  -- k ≥ 1: v₀ is not the head i
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have heq : π[0] = v₀ := by simp only [h] at hπk; exact hπk
      have hv₀_eq_i : v₀ = i := heq.symm.trans hπ0i
      have hv₀_in_tail : v₀ ∈ π.tail :=
        (List.dropLast_sublist π.tail).subset hv₀Int
      cases hπ_form : π with
      | nil => simp [hπ_form] at hπHead
      | cons a rest =>
        simp only [hπ_form, List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
        rw [hπ_form, List.tail_cons] at hv₀_in_tail
        rw [hπ_form] at hπND
        exact (List.nodup_cons.mp hπND).1 (hv₀_eq_i ▸ hv₀_in_tail)
    · exact h
  -- k < π.length - 1: v₀ is not the last j
  have hk_lt_pred : k < π.length - 1 := by
    by_contra h
    have heq : k = π.length - 1 := by omega
    have h1 : π[k]? = some v₀ := by
      rw [List.getElem?_eq_getElem hk_lt]; exact congrArg some hπk
    have h2 : π[π.length - 1]? = some j := by
      rw [List.getElem?_eq_getElem (by omega)]; exact congrArg some hπ_last_j
    rw [heq] at h1
    exact absurd (Option.some.inj (h1.symm.trans h2)) (ne_of_lt hv₀j)
  -- j ∉ π.take(k+1): since j is at position length-1 > k
  have hj_not_in_dropLast : j ∉ π.dropLast := by
    have hj_last : π.getLast hne = j :=
      Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
    rw [← hj_last]
    have happ := List.dropLast_append_getLast hne
    rw [← happ] at hπND; rw [List.nodup_append] at hπND
    intro h
    exact absurd rfl (hπND.2.2 (π.getLast hne) h (π.getLast hne) (List.mem_singleton.mpr rfl))
  have hj_not_in_take : j ∉ π.take (k + 1) := fun h =>
    hj_not_in_dropLast (List.dropLast_eq_take ▸ List.take_subset_take_left π (by omega) h)
  -- tail/last helpers for internalVertices membership
  have hπtail_ne : π.tail ≠ [] := by
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, π = a :: b :: rest := by
      match π, hπLen with | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp
  have hπtail_last : (π.tail).getLast hπtail_ne = j := by
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, π = a :: b :: rest := by
      match π, hπLen with | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp only [List.tail_cons]
    rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
    exact List.getLast?_cons_cons.symm.trans hπLast
  have hπW' : List.IsChain (fun a b => G.Adj a b) π := hπW
  -- *** β properties ***
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- β.head? = some v₀
    rw [List.head?_drop, List.getElem?_eq_getElem hk_lt]; exact congrArg some hπk
  · -- β.getLast? = some j
    change (π.drop k).getLast? = some j
    simp [List.getLast?_drop, Nat.not_le.mpr hk_lt, hπLast]
  · -- β.length < π.length
    change (π.drop k).length < π.length
    simp [List.length_drop]; omega
  · -- β.Nodup
    exact (List.drop_sublist k π).nodup hπND
  · -- β internal verts: ∀ v ∈ β, v = v₀ ∨ v = j ∨ v < v₀ ∨ j < v
    intro v hv
    have hv_in_π : v ∈ π := List.mem_of_mem_drop hv
    rcases hπInt v hv_in_π with h | h | h | h
    · -- v = i: impossible (position 0 < k in β)
      exfalso
      rw [List.mem_iff_getElem] at hv
      obtain ⟨p, hp, hpv⟩ := hv
      have hkp : k + p < π.length := by
        have hβlen : β.length = π.length - k := by
          change (π.drop k).length = π.length - k; simp
        omega
      have hπkp : π[k + p] = v := by rw [← List.getElem_drop]; exact hpv
      have h1 : π[k + p]? = some v := by
        rw [List.getElem?_eq_getElem hkp]; exact congrArg some hπkp
      have h2 : π[0]? = some i := by rwa [← List.head?_eq_getElem?]
      rw [h] at h1
      rw [List.getElem?_eq_getElem h0lt] at h2
      have heq0kp : (0 : ℕ) = k + p := by
        have h_eq : π[0]'(by omega) = π[k + p]'hkp := hπ0i.trans (h.symm.trans hπkp.symm)
        exact (hπND.getElem_inj_iff (hi := by omega) (hj := hkp)).mp h_eq
      omega
    · exact Or.inr (Or.inl h)
    · -- v < i: find v ≤ v₀ via maximality
      have hv_ne_j : v ≠ j := ne_of_lt (h.trans hij)
      have hv_in_tail : v ∈ π.tail := by
        cases hπ_form : π with
        | nil => simp [hπ_form] at hπHead
        | cons a rest =>
          simp only [hπ_form, List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
          simp only [List.tail_cons]
          rw [hπ_form] at hv_in_π
          rcases List.mem_cons.mp hv_in_π with h' | h'
          · exact absurd h' (ne_of_lt h)
          · exact h'
      have hv_in_int : v ∈ internalVertices π :=
        List.mem_dropLast_of_mem_of_ne_getLast hv_in_tail (hπtail_last.symm ▸ hv_ne_j)
      have hv_le : v ≤ v₀ := hv₀Max v hv_in_int h
      rcases lt_or_eq_of_le hv_le with h2 | h2
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inr h))
  · -- β.Chain'
    exact List.IsChain.drop hπW' k
  · -- α'.head? = some v₀
    rw [List.head?_reverse]; simp [List.getLast?_take, hk_lt, hπk]
  · -- α'.getLast? = some i
    rw [List.getLast?_reverse]
    simp [List.head?_take, Nat.pos_iff_ne_zero.mp hk_pos, hπHead]
  · -- α'.length < π.length
    change ((π.take (k + 1)).reverse).length < π.length
    simp [List.length_reverse, List.length_take]; omega
  · -- α'.Nodup
    exact List.nodup_reverse.mpr ((List.take_sublist (k + 1) π).nodup hπND)
  · -- α' internal verts: ∀ v ∈ α', v = v₀ ∨ v = i ∨ v < v₀ ∨ i < v
    intro v hv_alpha'
    rw [List.mem_reverse] at hv_alpha'
    have hv_in_π : v ∈ π := List.mem_of_mem_take hv_alpha'
    rcases hπInt v hv_in_π with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact absurd (h ▸ hv_alpha') hj_not_in_take
    · -- v < i: find v ≤ v₀
      have hv_ne_j : v ≠ j := ne_of_lt (h.trans hij)
      have hv_ne_i : v ≠ i := ne_of_lt h
      have hv_in_tail : v ∈ π.tail := by
        cases hπ_form : π with
        | nil => simp [hπ_form] at hπHead
        | cons a rest =>
          simp only [hπ_form, List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
          simp only [List.tail_cons]
          rw [hπ_form] at hv_in_π
          rcases List.mem_cons.mp hv_in_π with h' | h'
          · exact absurd h' hv_ne_i
          · exact h'
      have hv_in_int : v ∈ internalVertices π :=
        List.mem_dropLast_of_mem_of_ne_getLast hv_in_tail (hπtail_last.symm ▸ hv_ne_j)
      have hv_le : v ≤ v₀ := hv₀Max v hv_in_int h
      rcases lt_or_eq_of_le hv_le with h2 | h2
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inr (hij.trans h)))
  · -- α'.Chain'
    change List.IsChain (fun a b => G.Adj a b) ((π.take (k + 1)).reverse)
    rw [List.isChain_reverse]
    exact List.IsChain.imp (fun _ _ h => G.symm h) (List.IsChain.take hπW' (k + 1))

/-- Analogous sub-walk properties for Case B (above-j vertex v₀). -/
private lemma subwalk_props_above (G : SimpleGraph V) (π : List V) (v₀ i j : V)
    (hij : i < j)
    (hπHead : π.head? = some i) (hπLast : π.getLast? = some j)
    (hπND : π.Nodup) (hπLen : π.length ≥ 3)
    (hπInt : ∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v)
    (hv₀Int : v₀ ∈ internalVertices π)
    (hv₀Min : ∀ w ∈ internalVertices π, j < w → v₀ ≤ w)
    (hj_lt_v₀ : j < v₀)
    (hπW : π.Chain' (fun a b => G.Adj a b)) :
    let k := π.idxOf v₀
    let β := π.drop k
    let α' := (π.take (k + 1)).reverse
    -- β.reverse is a walk from j to v₀
    β.reverse.head? = some j ∧ β.reverse.getLast? = some v₀ ∧
    β.reverse.length < π.length ∧ β.reverse.Nodup ∧
    (∀ v ∈ β.reverse, v = j ∨ v = v₀ ∨ v < j ∨ v₀ < v) ∧
    β.reverse.Chain' (fun a b => G.Adj a b) ∧
    -- α'.reverse is a walk from i to v₀
    α'.reverse.head? = some i ∧ α'.reverse.getLast? = some v₀ ∧
    α'.reverse.length < π.length ∧ α'.reverse.Nodup ∧
    (∀ v ∈ α'.reverse, v = i ∨ v = v₀ ∨ v < i ∨ v₀ < v) ∧
    α'.reverse.Chain' (fun a b => G.Adj a b) := by
  intro k β α'
  have hv₀_in_π : v₀ ∈ π :=
    (List.tail_sublist π).subset ((List.dropLast_sublist π.tail).subset hv₀Int)
  have hk_lt : k < π.length := List.idxOf_lt_length_of_mem hv₀_in_π
  have hπk : π[k] = v₀ := List.getElem_idxOf hk_lt
  have hne : π ≠ [] := by intro h; simp [h] at hπHead
  have h0lt : 0 < π.length := by omega
  have hπ0i : π[0] = i := by
    have h0 : π[0]? = some i := by rwa [← List.head?_eq_getElem?]
    exact Option.some.inj ((List.getElem?_eq_getElem h0lt).symm.trans h0)
  have hπ_last_j : π[π.length - 1] = j := by
    rw [← (List.getLast_eq_getElem hne)]
    exact Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
  -- k ≥ 1: v₀ ≠ i (since i < v₀)
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      have heq : π[0] = v₀ := by simp only [h] at hπk; exact hπk
      exact absurd (heq.symm.trans hπ0i) (ne_of_gt (hij.trans hj_lt_v₀))
    · exact h
  -- k < π.length - 1: v₀ ≠ j (since j < v₀)
  have hk_lt_pred : k < π.length - 1 := by
    by_contra h
    have heq : k = π.length - 1 := by omega
    have h1 : π[k]? = some v₀ := by
      rw [List.getElem?_eq_getElem hk_lt]; exact congrArg some hπk
    have h2 : π[π.length - 1]? = some j := by
      rw [List.getElem?_eq_getElem (by omega)]; exact congrArg some hπ_last_j
    rw [heq] at h1
    exact absurd (Option.some.inj (h1.symm.trans h2)) (ne_of_gt hj_lt_v₀)
  -- j ∉ π.take(k+1)
  have hj_not_in_dropLast : j ∉ π.dropLast := by
    have hj_last : π.getLast hne = j :=
      Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans hπLast)
    rw [← hj_last]
    have happ := List.dropLast_append_getLast hne
    rw [← happ] at hπND; rw [List.nodup_append] at hπND
    intro h
    exact absurd rfl (hπND.2.2 (π.getLast hne) h (π.getLast hne) (List.mem_singleton.mpr rfl))
  have hj_not_in_take : j ∉ π.take (k + 1) := fun h =>
    hj_not_in_dropLast (List.dropLast_eq_take ▸ List.take_subset_take_left π (by omega) h)
  -- tail/last helpers
  have hπtail_ne : π.tail ≠ [] := by
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, π = a :: b :: rest := by
      match π, hπLen with | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp
  have hπtail_last : (π.tail).getLast hπtail_ne = j := by
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, π = a :: b :: rest := by
      match π, hπLen with | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    simp only [List.tail_cons]
    rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
    exact List.getLast?_cons_cons.symm.trans hπLast
  have hπW' : List.IsChain (fun a b => G.Adj a b) π := hπW
  -- β properties (β = π.drop k, β.head? = v₀, β.getLast? = j)
  have hβH : β.head? = some v₀ := by
    rw [List.head?_drop, List.getElem?_eq_getElem hk_lt]; exact congrArg some hπk
  have hβL : β.getLast? = some j := by
    change (π.drop k).getLast? = some j
    simp [List.getLast?_drop, Nat.not_le.mpr hk_lt, hπLast]
  have hβLen : β.length < π.length := by
    change (π.drop k).length < π.length
    simp [List.length_drop]; omega
  have hβND : β.Nodup := (List.drop_sublist k π).nodup hπND
  have hβW : β.Chain' (fun a b => G.Adj a b) := List.IsChain.drop hπW' k
  -- α' properties (α' = (π.take(k+1)).reverse)
  have hα'H : α'.head? = some v₀ := by
    rw [List.head?_reverse]; simp [List.getLast?_take, hk_lt, hπk]
  have hα'L : α'.getLast? = some i := by
    rw [List.getLast?_reverse]
    simp [List.head?_take, Nat.pos_iff_ne_zero.mp hk_pos, hπHead]
  have hα'Len : α'.length < π.length := by
    change ((π.take (k + 1)).reverse).length < π.length
    simp [List.length_reverse, List.length_take]; omega
  have hα'ND : α'.Nodup :=
    List.nodup_reverse.mpr ((List.take_sublist (k + 1) π).nodup hπND)
  have hα'W : α'.Chain' (fun a b => G.Adj a b) := by
    change List.IsChain (fun a b => G.Adj a b) ((π.take (k + 1)).reverse)
    rw [List.isChain_reverse]
    exact List.IsChain.imp (fun _ _ h => G.symm h) (List.IsChain.take hπW' (k + 1))
  -- *** β.reverse properties ***
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- β.reverse.head? = some j (= β.getLast?)
    rw [List.head?_reverse]; exact hβL
  · -- β.reverse.getLast? = some v₀ (= β.head?)
    rw [List.getLast?_reverse]; exact hβH
  · -- β.reverse.length < π.length
    simp [hβLen]
  · -- β.reverse.Nodup
    exact List.nodup_reverse.mpr hβND
  · -- β.reverse internal verts: ∀ v ∈ β.reverse, v = j ∨ v = v₀ ∨ v < j ∨ v₀ < v
    intro v hv
    rw [List.mem_reverse] at hv
    have hv_in_π : v ∈ π := List.mem_of_mem_drop hv
    rcases hπInt v hv_in_π with h | h | h | h
    · -- v = i: impossible (i at position 0 < k by Nodup)
      exfalso
      rw [List.mem_iff_getElem] at hv
      obtain ⟨p, hp, hpv⟩ := hv
      have hkp : k + p < π.length := by
        have hβlen : β.length = π.length - k := by
          change (π.drop k).length = π.length - k; simp
        omega
      have hπkp : π[k + p] = v := by rw [← List.getElem_drop]; exact hpv
      have h1 : π[k + p]? = some v := by
        rw [List.getElem?_eq_getElem hkp]; exact congrArg some hπkp
      have h2 : π[0]? = some i := by rwa [← List.head?_eq_getElem?]
      rw [h] at h1
      rw [List.getElem?_eq_getElem h0lt] at h2
      have heq0kp : (0 : ℕ) = k + p := by
        have h_eq : π[0]'(by omega) = π[k + p]'hkp := hπ0i.trans (h.symm.trans hπkp.symm)
        exact (hπND.getElem_inj_iff (hi := by omega) (hj := hkp)).mp h_eq
      omega
    · exact Or.inl h
    · -- v < i < j: v < j
      exact Or.inr (Or.inr (Or.inl (h.trans hij)))
    · -- j < v: v₀ ≤ v by hv₀Min; need v ∈ internalVertices π
      have hv_ne_i : v ≠ i := ne_of_gt (hij.trans h)
      have hv_ne_j : v ≠ j := ne_of_gt h
      have hv_in_tail : v ∈ π.tail := by
        cases hπ_form : π with
        | nil => simp [hπ_form] at hπHead
        | cons a rest =>
          simp only [hπ_form, List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
          simp only [List.tail_cons]
          rw [hπ_form] at hv_in_π
          rcases List.mem_cons.mp hv_in_π with h' | h'
          · exact absurd h' hv_ne_i
          · exact h'
      have hv_in_int : v ∈ internalVertices π :=
        List.mem_dropLast_of_mem_of_ne_getLast hv_in_tail (hπtail_last.symm ▸ hv_ne_j)
      rcases le_iff_lt_or_eq.mp (hv₀Min v hv_in_int h) with h2 | h2
      · exact Or.inr (Or.inr (Or.inr h2))
      · exact Or.inr (Or.inl h2.symm)
  · -- β.reverse.Chain'
    exact chain'_reverse G β hβW
  · -- α'.reverse.head? = some i (= α'.getLast?)
    rw [List.head?_reverse]; exact hα'L
  · -- α'.reverse.getLast? = some v₀ (= α'.head?)
    rw [List.getLast?_reverse]; exact hα'H
  · -- α'.reverse.length < π.length
    simp [hα'Len]
  · -- α'.reverse.Nodup
    exact List.nodup_reverse.mpr hα'ND
  · -- α'.reverse internal verts: ∀ v ∈ α'.reverse, v = i ∨ v = v₀ ∨ v < i ∨ v₀ < v
    intro v hv
    -- α'.reverse = π.take(k+1)
    simp only [α', List.reverse_reverse] at hv
    have hv_in_π : v ∈ π := List.mem_of_mem_take hv
    rcases hπInt v hv_in_π with h | h | h | h
    · exact Or.inl h
    · exact absurd (h ▸ hv) hj_not_in_take
    · exact Or.inr (Or.inr (Or.inl h))
    · -- j < v: v₀ ≤ v by hv₀Min; need v ∈ internalVertices π
      have hv_ne_i : v ≠ i := ne_of_gt (hij.trans h)
      have hv_ne_j : v ≠ j := ne_of_gt h
      have hv_in_tail : v ∈ π.tail := by
        cases hπ_form : π with
        | nil => simp [hπ_form] at hπHead
        | cons a rest =>
          simp only [hπ_form, List.head?_cons, Option.some.injEq] at hπHead; subst hπHead
          simp only [List.tail_cons]
          rw [hπ_form] at hv_in_π
          rcases List.mem_cons.mp hv_in_π with h' | h'
          · exact absurd h' hv_ne_i
          · exact h'
      have hv_in_int : v ∈ internalVertices π :=
        List.mem_dropLast_of_mem_of_ne_getLast hv_in_tail (hπtail_last.symm ▸ hv_ne_j)
      rcases le_iff_lt_or_eq.mp (hv₀Min v hv_in_int h) with h2 | h2
      · exact Or.inr (Or.inr (Or.inr h2))
      · exact Or.inr (Or.inl h2.symm)
  · -- α'.reverse.Chain'
    simp only [α', List.reverse_reverse]
    exact List.IsChain.take hπW' (k + 1)

/-- Core membership lemma by strong induction on walk length. -/
private theorem groebnerElem_mem_aux (G : SimpleGraph V) :
    ∀ (n : ℕ) (i j : V) (π : List V),
    π.length = n → i < j →
    π.head? = some i → π.getLast? = some j →
    π.Nodup →
    (∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v) →
    π.Chain' (fun a b => G.Adj a b) →
    pathMonomial (K := K) i j π * (x i * y j - x j * y i) ∈ binomialEdgeIdeal G := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro i j π hlen hij hHead hLast hNodup hInternal hWalk
  match π, hHead, hLast, hWalk, hNodup, hInternal, hlen with
  | [], hH, _, _, _, _, _ => simp at hH
  | [a], hH, hL, _, _, _, _ =>
    simp only [List.head?_cons, Option.some.injEq] at hH
    simp only [List.getLast?_singleton, Option.some.injEq] at hL
    subst hH; subst hL
    exact absurd hij (lt_irrefl _)
  | [a, b], hH, hL, hW, _, _, _ =>
    simp only [List.head?_cons, Option.some.injEq] at hH
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at hL
    have hAdj : G.Adj a b := by simp [List.Chain'] at hW; exact hW
    have hpm : pathMonomial (K := K) i j [a, b] = 1 := by
      rw [← hH, ← hL]; exact pathMonomial_pair a b
    rw [hpm, one_mul]
    have hAdj' : G.Adj i j := hH ▸ hL ▸ hAdj
    exact Ideal.subset_span ⟨i, j, hAdj', hij, rfl⟩
  | a :: b :: c :: rest, hH, hL, hW, hND, hInt, hlen' =>
    -- After simp+subst, 'i' is replaced by 'a'
    simp only [List.head?_cons, Option.some.injEq] at hH; subst hH
    have hπLen : (a :: b :: c :: rest).length ≥ 3 := by simp
    have ha_ne_b : a ≠ b := by
      intro h; subst h
      exact (List.nodup_cons.mp hND).1 (List.mem_cons.mpr (Or.inl rfl))
    have hb_ne_j : b ≠ j := by
      intro hbj; subst hbj
      have hnd2 : (b :: c :: rest).Nodup := (List.nodup_cons.mp hND).2
      have hb_notin_cr : b ∉ (c :: rest) := (List.nodup_cons.mp hnd2).1
      apply hb_notin_cr
      have hbcr_ne : (c :: rest) ≠ [] := List.cons_ne_nil _ _
      have hlast_cr : (c :: rest).getLast hbcr_ne ∈ (c :: rest) := List.getLast_mem _
      have hlast_eq_b : (c :: rest).getLast hbcr_ne = b := by
        have h1 : (a :: b :: c :: rest).getLast (by simp) = b := by
          rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
          simpa using hL
        simpa [List.getLast_cons, List.getLast_cons] using h1
      rwa [hlast_eq_b] at hlast_cr
    have hb_range : b < a ∨ j < b := by
      rcases hInt b (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
        with rfl | rfl | h | h
      · exact absurd rfl ha_ne_b
      · exact absurd rfl hb_ne_j
      · exact Or.inl h
      · exact Or.inr h
    -- b is an internal vertex of (a :: b :: c :: rest)
    have hb_int : b ∈ internalVertices (a :: b :: c :: rest) := by
      simp only [internalVertices, List.tail_cons]
      apply List.mem_dropLast_of_mem_of_ne_getLast
      · -- First goal: b ≠ (b :: c :: rest).getLast (by simp)
        intro h
        have heq : (b :: c :: rest).getLast (by simp) = j := by
          rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
          simpa [List.getLast?_cons_cons] using hL
        rw [heq] at h
        exact hb_ne_j h
      · -- Second goal: b ∈ b :: c :: rest
        exact List.mem_cons.mpr (Or.inl rfl)
    rcases hb_range with hb_lt | hb_gt
    · -- *** CASE A: b < a ***
      -- Find v₀ = max { v ∈ internalVertices (a :: b :: c :: rest) | v < a }
      let ints := internalVertices (a :: b :: c :: rest)
      let belowA := ints.toFinset.filter (· < a)
      have hbelowA_ne : belowA.Nonempty :=
        ⟨b, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb_int, hb_lt⟩⟩
      let v₀ := belowA.max' hbelowA_ne
      have hv₀_mem_belowA : v₀ ∈ belowA := Finset.max'_mem belowA hbelowA_ne
      have hv₀_lt_a : v₀ < a := (Finset.mem_filter.mp hv₀_mem_belowA).2
      have hv₀_int : v₀ ∈ ints :=
        List.mem_toFinset.mp (Finset.mem_filter.mp hv₀_mem_belowA).1
      have hv₀_max : ∀ w ∈ ints, w < a → w ≤ v₀ := fun w hw hwa =>
        Finset.le_max' belowA w (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw, hwa⟩)
      have hv₀_lt_j : v₀ < j := hv₀_lt_a.trans hij
      -- Get sub-walk properties
      let k := (a :: b :: c :: rest).idxOf v₀
      let β := (a :: b :: c :: rest).drop k
      let α' := ((a :: b :: c :: rest).take (k + 1)).reverse
      obtain ⟨hβH, hβL, hβlen, hβND, hβInt, hβW, hα'H, hα'L, hα'len, hα'ND, hα'Int, hα'W⟩ :=
        subwalk_props G (a :: b :: c :: rest) v₀ a j
          hij (by simp) hL hND hπLen hInt hv₀_int hv₀_max hv₀_lt_j hW
      -- Apply IH to β (walk from v₀ to j)
      have hβ_mem : pathMonomial (K := K) v₀ j β * (x v₀ * y j - x j * y v₀) ∈
          binomialEdgeIdeal G :=
        ih β.length (hlen' ▸ hβlen) v₀ j β rfl hv₀_lt_j hβH hβL hβND hβInt hβW
      -- Apply IH to α' (walk from v₀ to a)
      have hα'_mem : pathMonomial (K := K) v₀ a α' * (x v₀ * y a - x a * y v₀) ∈
          binomialEdgeIdeal G :=
        ih α'.length (hlen' ▸ hα'len) v₀ a α' rfl hv₀_lt_a hα'H hα'L hα'ND hα'Int hα'W
      -- Path monomial factorization: u_π = y v₀ * u_{α'} * u_β
      have hMon : pathMonomial (K := K) a j (a :: b :: c :: rest) =
          y v₀ * pathMonomial v₀ a α' * pathMonomial v₀ j β :=
        pathMonomial_split_below G a j v₀ hij hv₀_lt_a (a :: b :: c :: rest) β α'
          (by simp) hL hND hInt hv₀_int hv₀_max rfl rfl
      -- Algebraic identity: y v₀ * f_{aj} = y_a * f_{v₀,j} - y_j * f_{v₀,a}
      rw [hMon]
      have halg : y (K := K) v₀ * pathMonomial v₀ a α' * pathMonomial v₀ j β *
            (x a * y j - x j * y a) =
          y a * pathMonomial v₀ a α' * (pathMonomial v₀ j β * (x v₀ * y j - x j * y v₀)) -
          y j * pathMonomial v₀ j β * (pathMonomial v₀ a α' * (x v₀ * y a - x a * y v₀)) := by
        ring
      rw [halg]
      exact Ideal.sub_mem _
        (Ideal.mul_mem_left _ _ hβ_mem)
        (Ideal.mul_mem_left _ _ hα'_mem)
    · -- *** CASE B: b > j (symmetric) ***
      -- Find v₀ = min { v ∈ internalVertices (a :: b :: c :: rest) | v > j }
      let ints := internalVertices (a :: b :: c :: rest)
      let aboveJ := ints.toFinset.filter (j < ·)
      have haboveJ_ne : aboveJ.Nonempty :=
        ⟨b, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hb_int, hb_gt⟩⟩
      let v₀ := aboveJ.min' haboveJ_ne
      have hv₀_mem_aboveJ : v₀ ∈ aboveJ := Finset.min'_mem aboveJ haboveJ_ne
      have hv₀_gt_j : j < v₀ := (Finset.mem_filter.mp hv₀_mem_aboveJ).2
      have hv₀_int : v₀ ∈ ints :=
        List.mem_toFinset.mp (Finset.mem_filter.mp hv₀_mem_aboveJ).1
      have hv₀_min : ∀ w ∈ ints, j < w → v₀ ≤ w := fun w hw hwj =>
        Finset.min'_le aboveJ w (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw, hwj⟩)
      have ha_lt_v₀ : a < v₀ := hij.trans hv₀_gt_j
      -- Get sub-walk properties
      let k := (a :: b :: c :: rest).idxOf v₀
      let β := (a :: b :: c :: rest).drop k
      let α' := ((a :: b :: c :: rest).take (k + 1)).reverse
      obtain ⟨hβRevH, hβRevL, hβRevLen, hβRevND, hβRevInt, hβRevW,
               hα'RevH, hα'RevL, hα'RevLen, hα'RevND, hα'RevInt, hα'RevW⟩ :=
        subwalk_props_above G (a :: b :: c :: rest) v₀ a j
          hij (by simp) hL hND hπLen hInt hv₀_int hv₀_min hv₀_gt_j hW
      -- Apply IH to β.reverse (walk from j to v₀)
      have hβrev_mem : pathMonomial (K := K) j v₀ β.reverse * (x j * y v₀ - x v₀ * y j) ∈
          binomialEdgeIdeal G :=
        ih β.reverse.length (hlen' ▸ hβRevLen) j v₀ β.reverse rfl hv₀_gt_j
          hβRevH hβRevL hβRevND hβRevInt hβRevW
      -- Apply IH to α'.reverse (walk from a to v₀)
      have hα'rev_mem : pathMonomial (K := K) a v₀ α'.reverse * (x a * y v₀ - x v₀ * y a) ∈
          binomialEdgeIdeal G :=
        ih α'.reverse.length (hlen' ▸ hα'RevLen) a v₀ α'.reverse rfl ha_lt_v₀
          hα'RevH hα'RevL hα'RevND hα'RevInt hα'RevW
      -- Path monomial factorization: u_π = x v₀ * u_{β.rev} * u_{α'.rev}
      have hMon : pathMonomial (K := K) a j (a :: b :: c :: rest) =
          x v₀ * pathMonomial j v₀ β.reverse * pathMonomial a v₀ α'.reverse :=
        pathMonomial_split_above G a j v₀ hij hv₀_gt_j (a :: b :: c :: rest) β α'
          (by simp) hL hND hInt hv₀_int hv₀_min rfl rfl
      -- Algebraic identity: x v₀ * f_{aj} = x_j * f_{a,v₀} - x_a * f_{j,v₀}
      rw [hMon]
      have halg : x (K := K) v₀ * pathMonomial j v₀ β.reverse * pathMonomial a v₀ α'.reverse *
            (x a * y j - x j * y a) =
          x j * pathMonomial j v₀ β.reverse * (pathMonomial a v₀ α'.reverse * (x a * y v₀ - x v₀ * y a)) -
          x a * pathMonomial a v₀ α'.reverse * (pathMonomial j v₀ β.reverse * (x j * y v₀ - x v₀ * y j)) := by
        ring
      rw [halg]
      exact Ideal.sub_mem _
        (Ideal.mul_mem_left _ _ hα'rev_mem)
        (Ideal.mul_mem_left _ _ hβrev_mem)

/--
Every Gröbner basis element `u_π · f_{ij}` belongs to `binomialEdgeIdeal G`.

Proof by induction on the length of π:
- Base case (|π| = 2): `u_π = 1`, so `groebnerElement i j [i,j] = f_{ij} ∈ J_G`.
- Inductive step: use an algebraic identity to write `u_π f_{ij}` as a combination
  of shorter Gröbner elements.

Reference: Herzog et al. (2010), proof of Theorem 2.1, Step 1.
-/
theorem groebnerElement_mem (G : SimpleGraph V) (i j : V) (π : List V)
    (hπ : IsAdmissiblePath G i j π) :
    groebnerElement (K := K) i j π ∈ binomialEdgeIdeal G := by
  obtain ⟨hij, hHead, hLast, hNodup, hInternal, hWalk, _⟩ := hπ
  exact groebnerElem_mem_aux G π.length i j π rfl hij hHead hLast hNodup hInternal hWalk

/-- Every generator `f_{ij}` (for edges {i,j} ∈ E(G), i < j) is in the Gröbner basis set. -/
theorem generator_in_groebnerBasisSet (G : SimpleGraph V) (i j : V)
    (hAdj : G.Adj i j) (hij : i < j) :
    x (K := K) i * y j - x j * y i ∈ groebnerBasisSet G :=
  ⟨i, j, [i, j], edge_is_admissible G hAdj hij, by simp [groebnerElement]⟩

end

import BEI.CoveredWalks
import BEI.ClosedGraphs
import Mathlib.RingTheory.Ideal.Operations

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# S-polynomial case analysis for Theorem 2.1

This file carries the Buchberger half of Theorem 2.1.

The paper-facing public endpoint is `theorem_2_1_isReducedGroebnerBasis`
in `BEI/GroebnerBasis.lean`; everything in this file is part of the
implementation track for that wrapper.

This file contains:
- `groebnerBasisSet_span`: the Groebner basis set spans `J_G`.
- `groebnerElement_leadingCoeff_isUnit`: each leading coefficient is a unit
  (the `= 1` form is a private support lemma).
- `theorem_2_1`: the full Buchberger S-polynomial case analysis proving the
  admissible-path set is a Groebner basis.

The reducedness half (`theorem_2_1_reduced`), squarefree leading monomials, and
the paper-faithful wrapper are in `BEI/GroebnerBasis.lean`.

## Reference: Herzog et al. (2010), Theorem 2.1
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## Span of the Gröbner basis set -/

omit [DecidableEq V] [Fintype V] in
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

omit [DecidableEq V] in
/-- The leading coefficient of `groebnerElement i j π` is 1 (a unit).
Since `groebnerElement i j π = pathMonomial i j π * fij i j`, the leading coefficient
is `leadingCoeff(pathMonomial) * leadingCoeff(fij) = 1 * 1 = 1`. -/
private theorem groebnerElement_leadingCoeff (i j : V) (π : List V) (hij : i < j) :
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

omit [DecidableEq V] in
/-- The leading coefficient of each groebnerElement is a unit. -/
theorem groebnerElement_leadingCoeff_isUnit
    (i j : V) (π : List V) (hπ : IsAdmissiblePath G i j π) :
    IsUnit (binomialEdgeMonomialOrder.leadingCoeff (groebnerElement (K := K) i j π)) := by
  rw [groebnerElement_leadingCoeff i j π hπ.1]
  exact isUnit_one

/-! ## Theorem 2.1: Gröbner basis (Herzog direct S-polynomial approach)

The proof follows Herzog et al. (2010), Theorem 2.1, Second Step:
For any two admissible path binomials f_π1, f_π2 in G, show S(f_π1, f_π2)
reduces to 0 modulo G via Buchberger's criterion.

The key case analysis: when two paths share an endpoint, the S-polynomial
decomposes into a telescoping sum along the τ-path (concatenation of the
two paths), which provides a standard expression with remainder 0.
-/

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/--
**Theorem 2.1** (Herzog et al. 2010): The set
  `{ u_π · f_{ij} | i < j, π admissible path from i to j in G }`
is a Gröbner basis of `J_G` with respect to the lex monomial order
`x_1 > ⋯ > x_n > y_1 > ⋯ > y_n`.

The proof has three steps:
1. `groebnerBasisSet_span`: `Ideal.span groebnerBasisSet = J_G`.
2. **This theorem**: Buchberger's criterion — all S-polynomials reduce to 0.
3. `theorem_2_1_reduced`: No leading monomial divides another (reducedness).

**Fidelity: Equivalent, split.** The paper states Gröbner basis + reducedness in one
theorem. Here the two properties are proved separately, then combined in the wrapper
`theorem_2_1_isReducedGroebnerBasis`.

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

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
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

/-- Degree of `monomial Q 1 * fij a b` is `Q + Finsupp.single (Sum.inl a) 1 +
Finsupp.single (Sum.inr b) 1`. Used inside `theorem_2_1` to eliminate repeated
6-line calculations of leading-monomial degrees. -/
private lemma degree_monomial_mul_fij {a b : V} (hab : a < b)
    (Q : BinomialEdgeVars V →₀ ℕ) :
    binomialEdgeMonomialOrder.degree (monomial Q (1 : K) * fij (K := K) a b) =
      Q + (Finsupp.single (Sum.inl a : BinomialEdgeVars V) 1 +
           Finsupp.single (Sum.inr b : BinomialEdgeVars V) 1) := by
  classical
  rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
    (fij_ne_zero (K := K) a b hab),
    degree_monomial, if_neg one_ne_zero, fij_degree a b hab]

omit [DecidableEq V] in
/-- `fij a b` has zero degree at `Sum.inr v` whenever `v ≠ b` (since the only
nonzero `inr` contribution is at `Sum.inr b`). Used 16× across `theorem_2_1`'s
mixed-walk lambda bodies to eliminate the inline 4-line vanishing-at-`inr` proof. -/
private lemma fij_degree_inr_eq_zero {a b : V} (hab : a < b) (v : V) (hne : v ≠ b) :
    binomialEdgeMonomialOrder.degree (fij (K := K) a b) (Sum.inr v) = 0 := by
  rw [fij_degree _ _ hab, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  simp [show (Sum.inr b : BinomialEdgeVars V) ≠ Sum.inr v from
    fun h => hne.symm (Sum.inr_injective h)]

omit [DecidableEq V] in
/-- `fij a b` has zero degree at `Sum.inl v` whenever `v ≠ a` (since the only
nonzero `inl` contribution is at `Sum.inl a`). Sister lemma to
`fij_degree_inr_eq_zero`. -/
private lemma fij_degree_inl_eq_zero {a b : V} (hab : a < b) (v : V) (hne : v ≠ a) :
    binomialEdgeMonomialOrder.degree (fij (K := K) a b) (Sum.inl v) = 0 := by
  rw [fij_degree _ _ hab, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
  simp [show (Sum.inl a : BinomialEdgeVars V) ≠ Sum.inl v from
    fun h => hne.symm (Sum.inl_injective h)]

omit [DecidableEq V] [Fintype V] in
/-- Coverage helper for `theorem_2_1`'s mixed-walk leaves. Given an admissible path
`π` from `i` to `j`, a vertex `w ∈ π` distinct from both endpoints, and a target
exponent `Q` dominating `dπ` at `Sum.inl w` and `Sum.inr w`, the disjunctive lower
bound `Q (Sum.inl w) ≥ 1 ∨ Q (Sum.inr w) ≥ 1` holds. The path's vertex
classification (`v = i ∨ v = j ∨ v < i ∨ j < v`) selects which side is bounded. -/
private lemma cov_inr_or_inl_of_admissible_path
    (G : SimpleGraph V) (i j : V) (π : List V)
    (hπ : IsAdmissiblePath G i j π)
    (hπ_int_nd : (internalVertices π).Nodup)
    {dπ : BinomialEdgeVars V →₀ ℕ}
    (hdπ : pathMonomial (K := K) i j π = monomial dπ 1)
    {Q : BinomialEdgeVars V →₀ ℕ}
    {w : V} (hw_π : w ∈ π) (hw_ne_i : w ≠ i) (hw_ne_j : w ≠ j)
    (hQ_ge_dπ_inr : Q (Sum.inr w) ≥ dπ (Sum.inr w))
    (hQ_ge_dπ_inl : Q (Sum.inl w) ≥ dπ (Sum.inl w)) :
    Q (Sum.inl w) ≥ 1 ∨ Q (Sum.inr w) ≥ 1 := by
  have hw_int_π : w ∈ internalVertices π :=
    mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
      (by rwa [head_of_head? hπ.2.1])
      (by rwa [getLast_of_getLast? hπ.2.2.1])
  rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
  · exact absurd hw_eq hw_ne_i
  · exact absurd hw_eq hw_ne_j
  · right
    have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π hwi hπ_int_nd dπ hdπ
    omega
  · left
    have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π hjw hπ_int_nd dπ hdπ
    omega

omit [DecidableEq V] in
/-- Case 4 fold (shared first endpoint `i`). Given two admissible paths `π : i→a` and
`σ : i→b` with `a < b`, an exponent `E` covering all internal vertices of either path
plus the shared `i`, derive `IsRemainder (monomial E 1 * fij a b) ...`. The two
sub-cases of Case 4 (`j < l` and `l < j`) are recovered by calling this with either
`(π, σ, j, l)` or `(σ, π, l, j)` and adjusting signs at the call site via
`fij_antisymm`. -/
private lemma case4_remainder
    (G : SimpleGraph V) (i a b : V) {π σ : List V}
    (hπ : IsAdmissiblePath G i a π) (hσ : IsAdmissiblePath G i b σ)
    (hia : i < a) (hib : i < b) (hab : a < b)
    {E : BinomialEdgeVars V →₀ ℕ}
    (cov_inr_lt_i_π : ∀ v, v ∈ internalVertices π → v < i → E (Sum.inr v) ≥ 1)
    (cov_inr_lt_i_σ : ∀ v, v ∈ internalVertices σ → v < i → E (Sum.inr v) ≥ 1)
    (cov_inl_gt_a : ∀ v, v ∈ internalVertices π → a < v → E (Sum.inl v) ≥ 1)
    (cov_inl_gt_b : ∀ v, v ∈ internalVertices σ → b < v → E (Sum.inl v) ≥ 1)
    (cov_eq_i : E (Sum.inr i) ≥ 1) :
    binomialEdgeMonomialOrder.IsRemainder
      (monomial E 1 * fij (K := K) a b) (groebnerBasisSet G) 0 := by
  obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :=
    walk_from_shared_first G i a b π σ
      hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 hπ.2.2.2.2.2.1
      hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 hσ.2.2.2.2.2.1 (ne_of_lt hab)
  have hCov : ∀ v ∈ internalVertices τ,
      (v < a → E (Sum.inr v) ≥ 1) ∧
      (b < v → E (Sum.inl v) ≥ 1) ∧
      (a < v → v < b → E (Sum.inl v) ≥ 1) := by
    intro v hv_int
    rcases hτ_verts v hv_int with hv_π | hv_σ | hv_eq_i
    · have hv_mem : v ∈ π :=
        (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv_π)
      have hv_ne_i := not_head_of_internal' π i hπ.2.1 hπ.2.2.2.1 v hv_π
      have hv_ne_a := not_last_of_internal' π i a hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 v hv_π
      rcases hπ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hav
      · exact absurd rfl hv_ne_i
      · exact absurd rfl hv_ne_a
      · exact ⟨fun _ => cov_inr_lt_i_π v hv_π hvi,
                fun hbv => absurd (lt_trans hvi (lt_trans hia hab))
                  (not_lt.mpr (le_of_lt hbv)),
                fun hav' _ => absurd (lt_trans hvi hia) (not_lt.mpr (le_of_lt hav'))⟩
      · exact ⟨fun hva => absurd hav (not_lt.mpr (le_of_lt hva)),
                fun _ => cov_inl_gt_a v hv_π hav,
                fun _ _ => cov_inl_gt_a v hv_π hav⟩
    · have hv_mem : v ∈ σ :=
        (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_σ)
      have hv_ne_i := not_head_of_internal' σ i hσ.2.1 hσ.2.2.2.1 v hv_σ
      have hv_ne_b := not_last_of_internal' σ i b hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 v hv_σ
      rcases hσ.2.2.2.2.1 v hv_mem with rfl | rfl | hvi | hbv
      · exact absurd rfl hv_ne_i
      · exact absurd rfl hv_ne_b
      · exact ⟨fun _ => cov_inr_lt_i_σ v hv_σ hvi,
                fun hbv' => absurd (lt_trans hvi hib) (not_lt.mpr (le_of_lt hbv')),
                fun hav' _ => absurd (lt_trans hvi hia) (not_lt.mpr (le_of_lt hav'))⟩
      · exact ⟨fun hva => absurd (lt_trans hab hbv) (not_lt.mpr (le_of_lt hva)),
                fun _ => cov_inl_gt_b v hv_σ hbv,
                fun _ _ => cov_inl_gt_b v hv_σ hbv⟩
    · exact ⟨fun _ => hv_eq_i ▸ cov_eq_i,
              fun hbv => absurd (lt_trans hia hab)
                (not_lt.mpr (le_of_lt (hv_eq_i ▸ hbv))),
              fun hav' _ => absurd hia (not_lt.mpr (le_of_lt (hv_eq_i ▸ hav')))⟩
  exact isRemainder_fij_of_covered_walk G τ.length a b τ E le_rfl hab
    hτ_head hτ_last hτ_nd hτ_walk hCov

omit [DecidableEq V] in
/-- Case 5 fold (shared last endpoint `j`, y-variant). Given two admissible paths
`π : a→j` and `σ : b→j` with `a < b`, an exponent `E` covering all internal vertices
of either path plus the shared `j`, derive `IsRemainder (monomial E 1 * fij a b) ...`.
The two sub-cases of Case 5 (`i < k` and `k < i`) are recovered by calling this
with either `(π, σ, i, k)` or `(σ, π, k, i)`. Reverses paths internally to apply
`walk_from_shared_first` from `j`, and uses `isRemainder_fij_of_covered_walk_y` —
mid-range vertices contribute `Sum.inr` (i.e. `y_v`) coverage. -/
private lemma case5_remainder
    (G : SimpleGraph V) (a b j : V) {π σ : List V}
    (hπ : IsAdmissiblePath G a j π) (hσ : IsAdmissiblePath G b j σ)
    (haj : a < j) (hbj : b < j) (hab : a < b)
    {E : BinomialEdgeVars V →₀ ℕ}
    (cov_inr_lt_a_π : ∀ v, v ∈ internalVertices π → v < a → E (Sum.inr v) ≥ 1)
    (cov_inr_lt_b_σ : ∀ v, v ∈ internalVertices σ → v < b → E (Sum.inr v) ≥ 1)
    (cov_inl_gt_j_π : ∀ v, v ∈ internalVertices π → j < v → E (Sum.inl v) ≥ 1)
    (cov_inl_gt_j_σ : ∀ v, v ∈ internalVertices σ → j < v → E (Sum.inl v) ≥ 1)
    (cov_eq_j : E (Sum.inl j) ≥ 1) :
    binomialEdgeMonomialOrder.IsRemainder
      (monomial E 1 * fij (K := K) a b) (groebnerBasisSet G) 0 := by
  obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
      ∃ τ : List V, τ.head? = some a ∧ τ.getLast? = some b ∧ τ.Nodup ∧
      τ.IsChain (fun u v => G.Adj u v) ∧
      (∀ v ∈ internalVertices τ,
        v ∈ internalVertices π ∨ v ∈ internalVertices σ ∨ v = j) := by
    obtain ⟨τ', hτ'_head, hτ'_last, hτ'_nd, hτ'_walk, hτ'_verts⟩ :=
      walk_from_shared_first G j a b π.reverse σ.reverse
        (List.head?_reverse ▸ hπ.2.2.1)
        (List.getLast?_reverse ▸ hπ.2.1)
        (List.nodup_reverse.mpr hπ.2.2.2.1)
        (chain'_reverse' G π hπ.2.2.2.2.2.1)
        (List.head?_reverse ▸ hσ.2.2.1)
        (List.getLast?_reverse ▸ hσ.2.1)
        (List.nodup_reverse.mpr hσ.2.2.2.1)
        (chain'_reverse' G σ hσ.2.2.2.2.2.1)
        (ne_of_lt hab)
    exact ⟨τ', hτ'_head, hτ'_last, hτ'_nd, hτ'_walk, fun v hv => by
      rcases hτ'_verts v hv with h | h | h
      · exact Or.inl (mem_internalVertices_reverse h)
      · exact Or.inr (Or.inl (mem_internalVertices_reverse h))
      · exact Or.inr (Or.inr h)⟩
  have hCov : ∀ v ∈ internalVertices τ,
      (v < a → E (Sum.inr v) ≥ 1) ∧
      (b < v → E (Sum.inl v) ≥ 1) ∧
      (a < v → v < b → E (Sum.inr v) ≥ 1) := by
    intro v hv_int
    rcases hτ_verts v hv_int with hv_π | hv_σ | hv_eq_j
    · have hv_mem : v ∈ π :=
        (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv_π)
      have hv_ne_a := not_head_of_internal' π a hπ.2.1 hπ.2.2.2.1 v hv_π
      have hv_ne_j := not_last_of_internal' π a j hπ.2.1 hπ.2.2.1 hπ.2.2.2.1 v hv_π
      rcases hπ.2.2.2.2.1 v hv_mem with rfl | rfl | hva | hjv
      · exact absurd rfl hv_ne_a
      · exact absurd rfl hv_ne_j
      · exact ⟨fun _ => cov_inr_lt_a_π v hv_π hva,
                fun hbv => absurd (lt_trans hva (lt_trans hab hbv)) (lt_irrefl _),
                fun hav _ => absurd hva (not_lt.mpr (le_of_lt hav))⟩
      · exact ⟨fun hva => absurd hjv (not_lt.mpr (le_of_lt (lt_trans hva (lt_trans hab hbj)))),
                fun _ => cov_inl_gt_j_π v hv_π hjv,
                fun _ hvb => absurd (lt_trans hjv hvb) (not_lt.mpr (le_of_lt hbj))⟩
    · have hv_mem : v ∈ σ :=
        (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv_σ)
      have hv_ne_b := not_head_of_internal' σ b hσ.2.1 hσ.2.2.2.1 v hv_σ
      have hv_ne_j := not_last_of_internal' σ b j hσ.2.1 hσ.2.2.1 hσ.2.2.2.1 v hv_σ
      rcases hσ.2.2.2.2.1 v hv_mem with rfl | rfl | hvb | hjv
      · exact absurd rfl hv_ne_b
      · exact absurd rfl hv_ne_j
      · exact ⟨fun _ => cov_inr_lt_b_σ v hv_σ hvb,
                fun hbv => absurd hbv (not_lt.mpr (le_of_lt hvb)),
                fun _ _ => cov_inr_lt_b_σ v hv_σ hvb⟩
      · exact ⟨fun hva => absurd hjv (not_lt.mpr (le_of_lt (lt_trans hva (lt_trans hab hbj)))),
                fun _ => cov_inl_gt_j_σ v hv_σ hjv,
                fun _ hvb => absurd (lt_trans hjv hvb) (not_lt.mpr (le_of_lt hbj))⟩
    · exact ⟨fun hva => absurd haj (not_lt.mpr (le_of_lt (hv_eq_j ▸ hva))),
              fun _ => hv_eq_j ▸ cov_eq_j,
              fun _ hvb => absurd (lt_trans hbj (hv_eq_j ▸ hvb)) (lt_irrefl _)⟩
  exact isRemainder_fij_of_covered_walk_y G τ.length a b τ E le_rfl hab
    hτ_head hτ_last hτ_nd hτ_walk hCov

omit [DecidableEq V] in
theorem theorem_2_1 (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis
      (groebnerBasisSet (K := K) G) (binomialEdgeIdeal (K := K) G) := by
  classical
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
    have hE_ge_D : ∀ w, E w ≥ D w := by
      intro w; simp only [hE_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
    -- (using module-level not_head_of_internal' and not_last_of_internal')
    -- Coverage building blocks (shared between j<l and l<j subcases)
    have cov_inr_of_lt_i_π : ∀ v, v ∈ internalVertices π → v < i → E (Sum.inr v) ≥ 1 := by
      intro v hv_π hvi
      have := pathMonomial_exponent_inr_one (K := K) i j π v hv_π hvi hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inr_eq_zero (K := K) hij v (ne_of_lt (lt_trans hvi hij)))
        (fij_degree_inr_eq_zero (K := K) hil v (ne_of_lt (lt_trans hvi hil)))).1 (hE_ge_D _))
    have cov_inr_of_lt_i_σ : ∀ v, v ∈ internalVertices σ → v < i → E (Sum.inr v) ≥ 1 := by
      intro v hv_σ hvi
      have := pathMonomial_exponent_inr_one (K := K) i l σ v hv_σ hvi hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inr_eq_zero (K := K) hij v (ne_of_lt (lt_trans hvi hij)))
        (fij_degree_inr_eq_zero (K := K) hil v (ne_of_lt (lt_trans hvi hil)))).2 (hE_ge_D _))
    have cov_inl_of_gt_j : ∀ v, v ∈ internalVertices π → j < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_π hjv
      have := pathMonomial_exponent_inl_one (K := K) i j π v hv_π hjv hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inl_eq_zero (K := K) hij v (ne_of_gt (lt_trans hij hjv)))
        (fij_degree_inl_eq_zero (K := K) hil v (ne_of_gt (lt_trans hij hjv)))).1 (hE_ge_D _))
    have cov_inl_of_gt_l : ∀ v, v ∈ internalVertices σ → l < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_σ hlv
      have := pathMonomial_exponent_inl_one (K := K) i l σ v hv_σ hlv hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inl_eq_zero (K := K) hij v (ne_of_gt (lt_trans hil hlv)))
        (fij_degree_inl_eq_zero (K := K) hil v (ne_of_gt (lt_trans hil hlv)))).2 (hE_ge_D _))
    have cov_eq_i : E (Sum.inr i) ≥ 1 := by
      change (D + (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ)) (Sum.inr i) ≥ 1
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
      exact case4_remainder G i j l hπ hσ hij hil hjl
        cov_inr_of_lt_i_π cov_inr_of_lt_i_σ cov_inl_of_gt_j cov_inl_of_gt_l cov_eq_i
    · -- l < j: symmetric, swap (π, σ) and (j, l) when calling helper
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
      exact case4_remainder G i l j hσ hπ hil hij hlj
        cov_inr_of_lt_i_σ cov_inr_of_lt_i_π cov_inl_of_gt_l cov_inl_of_gt_j cov_eq_i
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
    have hE_ge_D : ∀ w, E w ≥ D w := by
      intro w; simp only [hE_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
    -- Coverage building blocks for Case 5
    have cov_inr_of_lt_i_π : ∀ v, v ∈ internalVertices π → v < i → E (Sum.inr v) ≥ 1 := by
      intro v hv_π hvi
      have := pathMonomial_exponent_inr_one (K := K) i j π v hv_π hvi hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inr_eq_zero (K := K) hij v (ne_of_lt (lt_trans hvi hij)))
        (fij_degree_inr_eq_zero (K := K) hkj v (ne_of_lt (lt_trans hvi hij)))).1 (hE_ge_D _))
    have cov_inr_of_lt_k_σ : ∀ v, v ∈ internalVertices σ → v < k → E (Sum.inr v) ≥ 1 := by
      intro v hv_σ hvk
      have := pathMonomial_exponent_inr_one (K := K) k j σ v hv_σ hvk hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inr_eq_zero (K := K) hij v (ne_of_lt (lt_trans hvk hkj)))
        (fij_degree_inr_eq_zero (K := K) hkj v (ne_of_lt (lt_trans hvk hkj)))).2 (hE_ge_D _))
    have cov_inl_of_gt_j_π : ∀ v, v ∈ internalVertices π → j < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_π hjv
      have := pathMonomial_exponent_inl_one (K := K) i j π v hv_π hjv hπ_nd dπ hdπ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inl_eq_zero (K := K) hij v (ne_of_gt (lt_trans hij hjv)))
        (fij_degree_inl_eq_zero (K := K) hkj v (ne_of_gt (lt_trans hkj hjv)))).1 (hE_ge_D _))
    have cov_inl_of_gt_j_σ : ∀ v, v ∈ internalVertices σ → j < v → E (Sum.inl v) ≥ 1 := by
      intro v hv_σ hjv
      have := pathMonomial_exponent_inl_one (K := K) k j σ v hv_σ hjv hσ_nd dσ hdσ
      exact le_trans (by omega) (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _
        (fij_degree_inl_eq_zero (K := K) hij v (ne_of_gt (lt_trans hij hjv)))
        (fij_degree_inl_eq_zero (K := K) hkj v (ne_of_gt (lt_trans hkj hjv)))).2 (hE_ge_D _))
    have cov_eq_j : E (Sum.inl j) ≥ 1 := by
      change (D + (Finsupp.single (Sum.inl j) 1 : BinomialEdgeVars V →₀ ℕ)) (Sum.inl j) ≥ 1
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
      exact case5_remainder G i k j hπ hσ hij hkj hik
        cov_inr_of_lt_i_π cov_inr_of_lt_k_σ cov_inl_of_gt_j_π cov_inl_of_gt_j_σ cov_eq_j
    · -- k < i: symmetric, swap (π, σ) and (i, k) when calling helper
      suffices h : binomialEdgeMonomialOrder.IsRemainder
          (monomial E 1 * fij (K := K) k i) (groebnerBasisSet G) 0 by
        have heq : (monomial D) ((1 : K) * 1) * (x (K := K) j * fij i k) =
            -(monomial E 1 * fij (K := K) k i) := by
          unfold BinomialEdgeVars at E D ⊢
          simp only [hE_def, one_mul, x, mul_neg, fij_antisymm i k, ← mul_assoc]
          congr 2
          change monomial D (1 : K) * monomial (Finsupp.single (Sum.inl j) 1) 1 = _
          rw [monomial_mul, one_mul]
        rw [heq]; exact isRemainder_neg' _ _ h
      exact case5_remainder G k i j hσ hπ hkj hij hki
        cov_inr_of_lt_k_σ cov_inr_of_lt_i_π cov_inl_of_gt_j_σ cov_inl_of_gt_j_π cov_eq_j
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
    -- Coprime leading terms: the S-polynomial of fij i j and fij k l has two summands
    -- with different leading monomials. The standard Buchberger criterion for coprime
    -- leading terms guarantees reduction to zero.
    --
    -- The proof proceeds by factoring out the monomial prefix (from sPolynomial_monomial_mul),
    -- then expressing the inner S-polynomial as a linear combination of groebnerBasisSet
    -- elements with appropriate degree bounds.
    --
    -- When {i,j} and {k,l} are edges: fij i j, fij k l ∈ groebnerBasisSet directly,
    -- and isRemainder_sub_mul gives the result via coprime_degrees_ne + degree_bounds_of_sub.
    --
    -- When paths are non-trivial: the proof requires a multi-step polynomial division
    -- argument using multiple groebnerBasisSet elements (telescope decomposition through
    -- intermediate edges). This involves the same covered-walk machinery as Cases 4 & 5
    -- but applied to both terms of the coprime S-polynomial simultaneously.
    --
    -- Mathematical justification: Theorem on coprime leading monomials in Gröbner basis
    -- theory (Buchberger's criterion, Lemma 2 of Cox-Little-O'Shea Chapter 2 §6).
    -- S(u_π f_{ij}, u_σ f_{kl}) reduces to zero modulo the Gröbner basis because the
    -- leading monomials of f_{ij} and f_{kl} share no variables.
    set D := (dπ + binomialEdgeMonomialOrder.degree (fij (K := K) i j)) ⊔
             (dσ + binomialEdgeMonomialOrder.degree (fij (K := K) k l)) -
             binomialEdgeMonomialOrder.degree (fij (K := K) i j) ⊔
             binomialEdgeMonomialOrder.degree (fij (K := K) k l) with hD_def
    -- Case split: do the paths share a vertex? (same vs different component)
    by_cases hshared : ∃ v, v ∈ π ∧ v ∈ σ
    · -- Same component: shared vertex case.
      -- The different-components proof (below) fails here because dπ ≤ Q₁ may fail.
      -- Instead, use coprime swap and the isRemainder_fij_via_two_walks infrastructure.
      obtain ⟨v, hv_π, hv_σ⟩ := hshared
      have hπ_int_nd : (internalVertices π).Nodup :=
        (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
      have hσ_int_nd : (internalVertices σ).Nodup :=
        (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
      -- Apply coprime swap: rewrite the S-polynomial
      rw [fij_coprime_swap (K := K)]
      -- Goal: IsRemainder (monomial D (1*1) * (x l * y j * fij i k - x k * y i * fij j l)) G 0
      -- Define new quotient monomial degrees for swapped pairs
      set Q₁ := D + (Finsupp.single (Sum.inl l) 1 : BinomialEdgeVars V →₀ ℕ) +
                     (Finsupp.single (Sum.inr j) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₁_def
      set Q₂ := D + (Finsupp.single (Sum.inl k) 1 : BinomialEdgeVars V →₀ ℕ) +
                     (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₂_def
      have hQ₁_ge_D : ∀ s, Q₁ s ≥ D s := fun s => by
        simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
      have hQ₂_ge_D : ∀ s, Q₂ s ≥ D s := fun s => by
        simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
      -- Walk construction via drops of reversed paths through shared vertex v
      have hv_πR : v ∈ π.reverse := List.mem_reverse.mpr hv_π
      have hv_σR : v ∈ σ.reverse := List.mem_reverse.mpr hv_σ
      -- Walk from i to k: paths v→i (π.reverse.drop) and v→k (σ.reverse.drop)
      obtain ⟨τ_ik, hτ_ik_h, hτ_ik_l, hτ_ik_nd, hτ_ik_w, hτ_ik_v⟩ :=
        walk_from_shared_first G v i k
          (π.reverse.drop (π.reverse.idxOf v))
          (σ.reverse.drop (σ.reverse.idxOf v))
          (head?_drop_idxOf hv_πR)
          (by rw [getLast?_drop_idxOf hv_πR, List.getLast?_reverse]; exact hπ.2.1)
          ((List.nodup_reverse.mpr hπ.2.2.2.1).sublist (List.drop_sublist _ _))
          (isChain_drop (chain'_reverse' G π hπ.2.2.2.2.2.1) _)
          (head?_drop_idxOf hv_σR)
          (by rw [getLast?_drop_idxOf hv_σR, List.getLast?_reverse]; exact hσ.2.1)
          ((List.nodup_reverse.mpr hσ.2.2.2.1).sublist (List.drop_sublist _ _))
          (isChain_drop (chain'_reverse' G σ hσ.2.2.2.2.2.1) _)
          heq_i
      -- Walk from j to l: paths v→j (π.drop) and v→l (σ.drop)
      obtain ⟨τ_jl, hτ_jl_h, hτ_jl_l, hτ_jl_nd, hτ_jl_w, hτ_jl_v⟩ :=
        walk_from_shared_first G v j l
          (π.drop (π.idxOf v))
          (σ.drop (σ.idxOf v))
          (head?_drop_idxOf hv_π)
          (by rw [getLast?_drop_idxOf hv_π]; exact hπ.2.2.1)
          (hπ.2.2.2.1.sublist (List.drop_sublist _ _))
          (isChain_drop hπ.2.2.2.2.2.1 _)
          (head?_drop_idxOf hv_σ)
          (by rw [getLast?_drop_idxOf hv_σ]; exact hσ.2.2.1)
          (hσ.2.2.2.1.sublist (List.drop_sublist _ _))
          (isChain_drop hσ.2.2.2.2.2.1 _)
          heq_j
      -- Walks have the vertex condition needed for admissible paths
      -- Vertices of the walk are from π, σ, or the shared vertex v
      -- Internal vertices of τ_ik come from internalVertices π (reversed), σ (reversed), or v
      -- Internal vertices of τ_jl come from internalVertices π, σ, or v
      -- Get admissible paths (handling both orderings)
      rcases lt_or_gt_of_ne heq_i with hik | hki
      · -- i < k
        -- Prove h₁: IsRemainder (monomial Q₁ 1 * fij i k) G 0
        -- The walk τ_ik has mixed x/y coverage: π-vertices (j < w) have x-coverage (Q₁(inl w) ≥ 1),
        -- σ-vertices (w < k) have y-coverage (Q₁(inr w) ≥ 1).
        -- Neither isRemainder_fij_of_covered_walk nor _y handles this directly.
        -- A mixed-coverage walk helper is needed.
        have h₁ : binomialEdgeMonomialOrder.IsRemainder
            (monomial Q₁ 1 * fij (K := K) i k) (groebnerBasisSet G) 0 := by
          exact isRemainder_fij_of_mixed_walk G τ_ik.length i k τ_ik Q₁ le_rfl hik
            hτ_ik_h hτ_ik_l hτ_ik_nd hτ_ik_w (fun w hw => by
            have hw_ne_i := not_head_of_internal' τ_ik i hτ_ik_h hτ_ik_nd w hw
            have hw_ne_k := not_last_of_internal' τ_ik i k hτ_ik_h hτ_ik_l hτ_ik_nd w hw
            -- Check if w is one of the "easy" values covered by Q₁'s extra terms
            by_cases hw_eq_j : w = j
            · right; subst hw_eq_j
              simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                reduceCtorEq, ite_true, ite_false]; omega
            · by_cases hw_eq_l : w = l
              · left; subst hw_eq_l
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · -- w ≠ i, j, k, l: both fij degrees are 0 at w's position, use sPolyD
                have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_eq_j
                have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_eq_l
                have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_ne_i
                have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_ne_k
                -- Get w's origin and prove coverage via pathMonomial exponents
                rcases hτ_ik_v w hw with hw_πR | hw_σR | hw_eq_v
                · have hw_π : w ∈ π := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                  exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                    hw_π hw_ne_i hw_eq_j
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                      (hQ₁_ge_D _))
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                      (hQ₁_ge_D _))
                · have hw_σ : w ∈ σ := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                  exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                    hw_σ hw_ne_k hw_eq_l
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                      (hQ₁_ge_D _))
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                      (hQ₁_ge_D _))
                · subst hw_eq_v
                  exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                    hv_π hw_ne_i hw_eq_j
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                      (hQ₁_ge_D _))
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                      (hQ₁_ge_D _)))
        -- Now handle fij(j, l)
        rcases lt_or_gt_of_ne heq_j with hjl | hlj
        · -- j < l
          have h₂ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₂ 1 * fij (K := K) j l) (groebnerBasisSet G) 0 := by
            exact isRemainder_fij_of_mixed_walk G τ_jl.length j l τ_jl Q₂ le_rfl hjl
              hτ_jl_h hτ_jl_l hτ_jl_nd hτ_jl_w (fun w hw => by
              have hw_ne_j := not_head_of_internal' τ_jl j hτ_jl_h hτ_jl_nd w hw
              have hw_ne_l := not_last_of_internal' τ_jl j l hτ_jl_h hτ_jl_l hτ_jl_nd w hw
              by_cases hw_eq_k : w = k
              · left; subst hw_eq_k
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_i : w = i
                · right; subst hw_eq_i
                  simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_ne_j
                  have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_ne_l
                  have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_eq_i
                  have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_eq_k
                  rcases hτ_jl_v w hw with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hw_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                      hw_σ hw_eq_k hw_ne_l
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                        (hQ₂_ge_D _))
                  · subst hw_eq_v
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hv_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₂_ge_D _)))
          have h₂' : binomialEdgeMonomialOrder.IsRemainder
              (-(monomial Q₂ 1 * fij (K := K) j l)) (groebnerBasisSet G) 0 :=
            isRemainder_neg' _ _ h₂
          -- Algebraic equalities
          have hQ₁_eq : monomial D (1 : K) * x l * y j = monomial Q₁ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          have hQ₂_eq : monomial D (1 : K) * x k * y i = monomial Q₂ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          -- Rewrite and combine
          suffices heq : (monomial D) ((1 : K) * 1) *
              (x (K := K) l * y j * fij i k - x k * y i * fij j l) =
              monomial Q₁ 1 * fij (K := K) i k + (-(monomial Q₂ 1 * fij (K := K) j l)) by
            rw [heq]
            have hdeg_ne : binomialEdgeMonomialOrder.degree (monomial Q₁ 1 * fij (K := K) i k) ≠
                binomialEdgeMonomialOrder.degree (-(monomial Q₂ 1 * fij (K := K) j l)) := by
              rw [MonomialOrder.degree_neg]; intro heq'
              classical
              -- Evaluate at Sum.inl i to derive contradiction
              have ev₁ : (Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr k : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl i) = Q₁ (Sum.inl i) + 1 := by
                simp only [Finsupp.add_apply, Finsupp.single_apply]; rfl
              have ev₂ : (Q₂ + (Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl i) = Q₂ (Sum.inl i) := by
                unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
                simp only [Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl j : V ⊕ V) = Sum.inl i) from
                    fun h => (ne_of_lt hij) (Sum.inl.inj h).symm,
                  Sum.inr_ne_inl, ite_false, add_zero]
              have h_eval := Finsupp.ext_iff.mp heq' (Sum.inl i : BinomialEdgeVars V)
              rw [degree_monomial_mul_fij (K := K) hik Q₁,
                  degree_monomial_mul_fij (K := K) hjl Q₂, ev₁, ev₂] at h_eval
              have hQ₁_ge : Q₁ (Sum.inl i) ≥ D (Sum.inl i) := by
                unfold BinomialEdgeVars at Q₁ hQ₁_def ⊢
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; omega
              have hQ₂_eq : Q₂ (Sum.inl i) = D (Sum.inl i) := by
                unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl k : V ⊕ V) = Sum.inl i) from
                    fun h => heq_i (Sum.inl.inj h).symm,
                  Sum.inr_ne_inl, ite_false, add_zero]
              omega
            obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_ne _ _ hdeg_ne
            exact isRemainder_add _ _ _ h₁ h₂' hd₁ hd₂
          -- Prove the algebraic equality
          rw [show (monomial D) ((1 : K) * 1) * (x l * y j * fij i k - x k * y i * fij j l)
              = monomial D 1 * x l * y j * fij i k -
                monomial D 1 * x k * y i * fij j l from by ring,
            sub_eq_add_neg,
            show monomial D (1 : K) * x l * y j * fij i k =
              (monomial D 1 * x l * y j) * fij i k from by ring,
            show monomial D (1 : K) * x k * y i * fij j l =
              (monomial D 1 * x k * y i) * fij j l from by ring,
            hQ₁_eq, hQ₂_eq]
        · -- l < j: fij j l = -(fij l j), so the subtraction becomes addition
          -- h₁ for fij(i,k) with i < k: same as j < l case (4 sorries above)
          have h₁ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₁ 1 * fij (K := K) i k) (groebnerBasisSet G) 0 := by
            exact isRemainder_fij_of_mixed_walk G τ_ik.length i k τ_ik Q₁ le_rfl hik
              hτ_ik_h hτ_ik_l hτ_ik_nd hτ_ik_w (fun w hw => by
              have hw_ne_i := not_head_of_internal' τ_ik i hτ_ik_h hτ_ik_nd w hw
              have hw_ne_k := not_last_of_internal' τ_ik i k hτ_ik_h hτ_ik_l hτ_ik_nd w hw
              by_cases hw_eq_j : w = j
              · right; subst hw_eq_j
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_l : w = l
                · left; subst hw_eq_l
                  simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                    reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_eq_j
                  have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_eq_l
                  have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_ne_i
                  have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_ne_k
                  rcases hτ_ik_v w hw with hw_πR | hw_σR | hw_eq_v
                  · have hw_π : w ∈ π := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hw_π hw_ne_i hw_eq_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₁_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₁_ge_D _))
                  · have hw_σ : w ∈ σ := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                    exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                      hw_σ hw_ne_k hw_eq_l
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                        (hQ₁_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                        (hQ₁_ge_D _))
                  · subst hw_eq_v
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hv_π hw_ne_i hw_eq_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₁_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₁_ge_D _)))
          -- h₂ for fij(l,j) with l < j
          have h₂ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₂ 1 * fij (K := K) l j) (groebnerBasisSet G) 0 := by
            exact isRemainder_fij_of_mixed_walk G τ_jl.reverse.length l j τ_jl.reverse Q₂ le_rfl hlj
              (by rw [List.head?_reverse]; exact hτ_jl_l)
              (by rw [List.getLast?_reverse]; exact hτ_jl_h)
              (List.nodup_reverse.mpr hτ_jl_nd)
              (chain'_reverse' G τ_jl hτ_jl_w)
              (fun w hw => by
              have hw_orig := mem_internalVertices_reverse hw
              have hw_ne_l := not_head_of_internal' τ_jl.reverse l
                (by rw [List.head?_reverse]; exact hτ_jl_l)
                (List.nodup_reverse.mpr hτ_jl_nd) w hw
              have hw_ne_j := not_last_of_internal' τ_jl.reverse l j
                (by rw [List.head?_reverse]; exact hτ_jl_l)
                (by rw [List.getLast?_reverse]; exact hτ_jl_h)
                (List.nodup_reverse.mpr hτ_jl_nd) w hw
              by_cases hw_eq_k : w = k
              · left; subst hw_eq_k
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_i : w = i
                · right; subst hw_eq_i
                  simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_ne_j
                  have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_ne_l
                  have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_eq_i
                  have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_eq_k
                  rcases hτ_jl_v w hw_orig with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hw_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                      hw_σ hw_eq_k hw_ne_l
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                        (hQ₂_ge_D _))
                  · subst hw_eq_v
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hv_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₂_ge_D _)))
          -- Algebraic equalities
          have hQ₁_eq : monomial D (1 : K) * x l * y j = monomial Q₁ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          have hQ₂_eq : monomial D (1 : K) * x k * y i = monomial Q₂ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          -- Rewrite and combine (addition, not subtraction, since fij j l = -(fij l j))
          suffices heq : (monomial D) ((1 : K) * 1) *
              (x (K := K) l * y j * fij i k - x k * y i * fij j l) =
              monomial Q₁ 1 * fij (K := K) i k + monomial Q₂ 1 * fij (K := K) l j by
            rw [heq]
            have hdeg_ne : binomialEdgeMonomialOrder.degree (monomial Q₁ 1 * fij (K := K) i k) ≠
                binomialEdgeMonomialOrder.degree (monomial Q₂ 1 * fij (K := K) l j) := by
              classical
              rw [degree_monomial_mul_fij (K := K) hik Q₁,
                  degree_monomial_mul_fij (K := K) hlj Q₂]
              intro heq'
              have h_eval := Finsupp.ext_iff.mp heq' (Sum.inl i : BinomialEdgeVars V)
              have ev₁ : (Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr k : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl i) = Q₁ (Sum.inl i) + 1 := by
                simp only [Finsupp.add_apply, Finsupp.single_apply]; rfl
              have ev₂ : (Q₂ + (Finsupp.single (Sum.inl l : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl i) = Q₂ (Sum.inl i) := by
                unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
                simp only [Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl l : V ⊕ V) = Sum.inl i) from
                    fun h => absurd (Sum.inl.inj h) (ne_of_gt (lt_trans hik hkl)),
                  Sum.inr_ne_inl, ite_false, add_zero]
              rw [ev₁, ev₂] at h_eval
              have hQ₁_ge : Q₁ (Sum.inl i) ≥ D (Sum.inl i) := by
                unfold BinomialEdgeVars at Q₁ hQ₁_def ⊢
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; omega
              have hQ₂_eq' : Q₂ (Sum.inl i) = D (Sum.inl i) := by
                unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl k : V ⊕ V) = Sum.inl i) from
                    fun h => heq_i (Sum.inl.inj h).symm,
                  Sum.inr_ne_inl, ite_false, add_zero]
              omega
            obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_ne _ _ hdeg_ne
            exact isRemainder_add _ _ _ h₁ h₂ hd₁ hd₂
          -- Prove the algebraic equality (subtraction → addition via fij_antisymm)
          have : fij (K := K) j l = -(fij (K := K) l j) := fij_antisymm j l
          rw [show (monomial D) ((1 : K) * 1) * (x l * y j * fij (K := K) i k - x k * y i * fij j l)
              = monomial D 1 * x l * y j * fij i k -
                monomial D 1 * x k * y i * fij j l from by ring,
            this, show monomial D (1 : K) * x k * y i * -(fij (K := K) l j) =
              -(monomial D 1 * x k * y i * fij l j) from by ring,
            sub_neg_eq_add,
            show monomial D (1 : K) * x l * y j * fij i k =
              (monomial D 1 * x l * y j) * fij i k from by ring,
            show monomial D (1 : K) * x k * y i * fij l j =
              (monomial D 1 * x k * y i) * fij l j from by ring,
            hQ₁_eq, hQ₂_eq]
      · -- k < i: use fij_antisymm to reduce
        suffices h : binomialEdgeMonomialOrder.IsRemainder
            (monomial D ((1 : K) * 1) *
              (x (K := K) l * y j * fij k i - x k * y i * fij l j))
            (groebnerBasisSet G) 0 by
          have heq : monomial D ((1 : K) * 1) *
              (x (K := K) l * y j * fij i k - x k * y i * fij j l) =
              -(monomial D ((1 : K) * 1) *
                (x (K := K) l * y j * fij k i - x k * y i * fij l j)) := by
            simp only [fij_antisymm i k, fij_antisymm j l]; ring
          rw [heq]; exact isRemainder_neg' _ _ h
        -- Now goal:
        -- IsRemainder (monomial D (1*1) * (x l * y j * fij k i - x k * y i * fij l j)) G 0
        -- This has the same structure as the i < k case with (k,i) and (l,j) playing the roles
        -- of (i,k) and (j,l). Since k < i, fij(k,i) has k < i.
        -- The proof follows the same pattern as the i < k case above.
        -- Prove h₁: IsRemainder (monomial Q₁ 1 * fij k i) G 0
        -- Walk from k to i via τ_ik.reverse (k < i)
        have h₁ : binomialEdgeMonomialOrder.IsRemainder
            (monomial Q₁ 1 * fij (K := K) k i) (groebnerBasisSet G) 0 := by
          exact isRemainder_fij_of_mixed_walk G τ_ik.reverse.length k i τ_ik.reverse Q₁ le_rfl hki
            (by rw [List.head?_reverse]; exact hτ_ik_l)
            (by rw [List.getLast?_reverse]; exact hτ_ik_h)
            (List.nodup_reverse.mpr hτ_ik_nd)
            (chain'_reverse' G τ_ik hτ_ik_w)
            (fun w hw => by
            have hw_orig := mem_internalVertices_reverse hw
            have hw_ne_k := not_head_of_internal' τ_ik.reverse k
              (by rw [List.head?_reverse]; exact hτ_ik_l)
              (List.nodup_reverse.mpr hτ_ik_nd) w hw
            have hw_ne_i := not_last_of_internal' τ_ik.reverse k i
              (by rw [List.head?_reverse]; exact hτ_ik_l)
              (by rw [List.getLast?_reverse]; exact hτ_ik_h)
              (List.nodup_reverse.mpr hτ_ik_nd) w hw
            by_cases hw_eq_j : w = j
            · right; subst hw_eq_j
              simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                reduceCtorEq, ite_true, ite_false]; omega
            · by_cases hw_eq_l : w = l
              · left; subst hw_eq_l
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_eq_j
                have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_eq_l
                have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_ne_i
                have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_ne_k
                rcases hτ_ik_v w hw_orig with hw_πR | hw_σR | hw_eq_v
                · have hw_π : w ∈ π := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                  exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                    hw_π hw_ne_i hw_eq_j
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                      (hQ₁_ge_D _))
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                      (hQ₁_ge_D _))
                · have hw_σ : w ∈ σ := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                  exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                    hw_σ hw_ne_k hw_eq_l
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                      (hQ₁_ge_D _))
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                      (hQ₁_ge_D _))
                · subst hw_eq_v
                  exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                    hv_π hw_ne_i hw_eq_j
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                      (hQ₁_ge_D _))
                    (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                      (hQ₁_ge_D _)))
        -- Now handle fij(l, j) or fij(j, l)
        rcases lt_or_gt_of_ne heq_j with hjl | hlj
        · -- j < l: fij(l, j) = -(fij(j, l)), subtraction becomes addition
          have h₂ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₂ 1 * fij (K := K) j l) (groebnerBasisSet G) 0 := by
            exact isRemainder_fij_of_mixed_walk G τ_jl.length j l τ_jl Q₂ le_rfl hjl
              hτ_jl_h hτ_jl_l hτ_jl_nd hτ_jl_w (fun w hw => by
              have hw_ne_j := not_head_of_internal' τ_jl j hτ_jl_h hτ_jl_nd w hw
              have hw_ne_l := not_last_of_internal' τ_jl j l hτ_jl_h hτ_jl_l hτ_jl_nd w hw
              by_cases hw_eq_k : w = k
              · left; subst hw_eq_k
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_i : w = i
                · right; subst hw_eq_i
                  simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_ne_j
                  have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_ne_l
                  have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_eq_i
                  have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_eq_k
                  rcases hτ_jl_v w hw with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hw_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                      hw_σ hw_eq_k hw_ne_l
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                        (hQ₂_ge_D _))
                  · subst hw_eq_v
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hv_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hQ₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hQ₂_ge_D _)))
          -- Algebraic equalities
          have hQ₁_eq : monomial D (1 : K) * x l * y j = monomial Q₁ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          have hQ₂_eq : monomial D (1 : K) * x k * y i = monomial Q₂ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          -- fij(l, j) = -(fij(j, l)), so subtraction becomes addition
          -- x l * y j * fij k i - x k * y i * fij l j
          -- = Q₁ * fij k i - Q₂ * (-(fij j l)) = Q₁ * fij k i + Q₂ * fij j l
          suffices heq : (monomial D) ((1 : K) * 1) *
              (x (K := K) l * y j * fij k i - x k * y i * fij l j) =
              monomial Q₁ 1 * fij (K := K) k i + monomial Q₂ 1 * fij (K := K) j l by
            rw [heq]
            have hdeg_ne : binomialEdgeMonomialOrder.degree (monomial Q₁ 1 * fij (K := K) k i) ≠
                binomialEdgeMonomialOrder.degree (monomial Q₂ 1 * fij (K := K) j l) := by
              classical
              rw [degree_monomial_mul_fij (K := K) hki Q₁,
                  degree_monomial_mul_fij (K := K) hjl Q₂]
              intro heq'
              -- Evaluate at Sum.inl l to derive contradiction
              have h_eval := Finsupp.ext_iff.mp heq' (Sum.inl l : BinomialEdgeVars V)
              have ev₁ : (Q₁ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr i : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl l) = Q₁ (Sum.inl l) := by
                unfold BinomialEdgeVars at Q₁ hQ₁_def ⊢
                simp only [Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl k : V ⊕ V) = Sum.inl l) from
                    fun h => ne_of_lt hkl (Sum.inl.inj h),
                  Sum.inr_ne_inl, ite_false, add_zero]
              have ev₂ : (Q₂ + (Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl l) = Q₂ (Sum.inl l) := by
                unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
                simp only [Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl j : V ⊕ V) = Sum.inl l) from
                    fun h => heq_j (Sum.inl.inj h),
                  Sum.inr_ne_inl, ite_false, add_zero]
              rw [ev₁, ev₂] at h_eval
              have hQ₁_val : Q₁ (Sum.inl l) = D (Sum.inl l) + 1 := by
                unfold BinomialEdgeVars at Q₁ hQ₁_def ⊢
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inr_ne_inl, ite_true, ite_false]; omega
              have hQ₂_val : Q₂ (Sum.inl l) = D (Sum.inl l) := by
                unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl k : V ⊕ V) = Sum.inl l) from
                    fun h => ne_of_lt hkl (Sum.inl.inj h),
                  Sum.inr_ne_inl, ite_false, add_zero]
              omega
            obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_ne _ _ hdeg_ne
            exact isRemainder_add _ _ _ h₁ h₂ hd₁ hd₂
          -- Prove the algebraic equality: fij l j = -(fij j l)
          have hflj : fij (K := K) l j = -(fij (K := K) j l) := fij_antisymm l j
          rw [show (monomial D) ((1 : K) * 1) * (x l * y j * fij k i - x k * y i * fij l j)
              = monomial D 1 * x l * y j * fij k i -
                monomial D 1 * x k * y i * fij l j from by ring,
            hflj, show monomial D (1 : K) * x k * y i * -(fij (K := K) j l) =
              -(monomial D 1 * x k * y i * fij j l) from by ring,
            sub_neg_eq_add,
            show monomial D (1 : K) * x l * y j * fij k i =
              (monomial D 1 * x l * y j) * fij k i from by ring,
            show monomial D (1 : K) * x k * y i * fij j l =
              (monomial D 1 * x k * y i) * fij j l from by ring,
            hQ₁_eq, hQ₂_eq]
        · -- l < j: use ring identity to rewrite with different quotient monomials
          -- x l * y j * fij k i - x k * y i * fij l j = x j * y l * fij k i - x i * y k * fij l j
          -- Define R₁ = D + single(inl j) + single(inr l), R₂ = D + single(inl i) + single(inr k)
          set R₁ := D + (Finsupp.single (Sum.inl j) 1 : BinomialEdgeVars V →₀ ℕ) +
                         (Finsupp.single (Sum.inr l) 1 : BinomialEdgeVars V →₀ ℕ) with hR₁_def
          set R₂ := D + (Finsupp.single (Sum.inl i) 1 : BinomialEdgeVars V →₀ ℕ) +
                         (Finsupp.single (Sum.inr k) 1 : BinomialEdgeVars V →₀ ℕ) with hR₂_def
          have h₁R : binomialEdgeMonomialOrder.IsRemainder
              (monomial R₁ 1 * fij (K := K) k i) (groebnerBasisSet G) 0 := by
            exact isRemainder_fij_of_mixed_walk G τ_ik.reverse.length k i τ_ik.reverse R₁ le_rfl hki
              (by rw [List.head?_reverse]; exact hτ_ik_l)
              (by rw [List.getLast?_reverse]; exact hτ_ik_h)
              (List.nodup_reverse.mpr hτ_ik_nd)
              (chain'_reverse' G τ_ik hτ_ik_w)
              (fun w hw => by
              have hw_orig := mem_internalVertices_reverse hw
              have hw_ne_k := not_head_of_internal' τ_ik.reverse k
                (by rw [List.head?_reverse]; exact hτ_ik_l)
                (List.nodup_reverse.mpr hτ_ik_nd) w hw
              have hw_ne_i := not_last_of_internal' τ_ik.reverse k i
                (by rw [List.head?_reverse]; exact hτ_ik_l)
                (by rw [List.getLast?_reverse]; exact hτ_ik_h)
                (List.nodup_reverse.mpr hτ_ik_nd) w hw
              have hR₁_ge_D : ∀ s, R₁ s ≥ D s := fun s => by
                simp only [hR₁_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
              by_cases hw_eq_j : w = j
              · left; subst hw_eq_j
                simp only [hR₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_l : w = l
                · right; subst hw_eq_l
                  simp only [hR₁_def, Finsupp.add_apply, Finsupp.single_apply,
                    reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_eq_j
                  have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_eq_l
                  have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_ne_i
                  have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_ne_k
                  rcases hτ_ik_v w hw_orig with hw_πR | hw_σR | hw_eq_v
                  · have hw_π : w ∈ π := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hw_π hw_ne_i hw_eq_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hR₁_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hR₁_ge_D _))
                  · have hw_σ : w ∈ σ := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                    exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                      hw_σ hw_ne_k hw_eq_l
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                        (hR₁_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                        (hR₁_ge_D _))
                  · subst hw_eq_v
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hv_π hw_ne_i hw_eq_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hR₁_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hR₁_ge_D _)))
          have h₂R : binomialEdgeMonomialOrder.IsRemainder
              (monomial R₂ 1 * fij (K := K) l j) (groebnerBasisSet G) 0 := by
            exact isRemainder_fij_of_mixed_walk G τ_jl.reverse.length l j τ_jl.reverse R₂ le_rfl hlj
              (by rw [List.head?_reverse]; exact hτ_jl_l)
              (by rw [List.getLast?_reverse]; exact hτ_jl_h)
              (List.nodup_reverse.mpr hτ_jl_nd)
              (chain'_reverse' G τ_jl hτ_jl_w)
              (fun w hw => by
              have hw_orig := mem_internalVertices_reverse hw
              have hw_ne_l := not_head_of_internal' τ_jl.reverse l
                (by rw [List.head?_reverse]; exact hτ_jl_l)
                (List.nodup_reverse.mpr hτ_jl_nd) w hw
              have hw_ne_j := not_last_of_internal' τ_jl.reverse l j
                (by rw [List.head?_reverse]; exact hτ_jl_l)
                (by rw [List.getLast?_reverse]; exact hτ_jl_h)
                (List.nodup_reverse.mpr hτ_jl_nd) w hw
              have hR₂_ge_D : ∀ s, R₂ s ≥ D s := fun s => by
                simp only [hR₂_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
              by_cases hw_eq_i : w = i
              · left; subst hw_eq_i
                simp only [hR₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_k : w = k
                · right; subst hw_eq_k
                  simp only [hR₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 := fij_degree_inr_eq_zero (K := K) hij w hw_ne_j
                  have hfkl_inr0 := fij_degree_inr_eq_zero (K := K) hkl w hw_ne_l
                  have hfij_inl0 := fij_degree_inl_eq_zero (K := K) hij w hw_eq_i
                  have hfkl_inl0 := fij_degree_inl_eq_zero (K := K) hkl w hw_eq_k
                  rcases hτ_jl_v w hw_orig with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hw_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hR₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hR₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    exact cov_inr_or_inl_of_admissible_path G k l σ hσ hσ_int_nd hdσ
                      hw_σ hw_eq_k hw_ne_l
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2
                        (hR₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2
                        (hR₂_ge_D _))
                  · subst hw_eq_v
                    exact cov_inr_or_inl_of_admissible_path G i j π hπ hπ_int_nd hdπ
                      hv_π hw_eq_i hw_ne_j
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1
                        (hR₂_ge_D _))
                      (le_trans (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1
                        (hR₂_ge_D _)))
          have h₂R' : binomialEdgeMonomialOrder.IsRemainder
              (-(monomial R₂ 1 * fij (K := K) l j)) (groebnerBasisSet G) 0 :=
            isRemainder_neg' _ _ h₂R
          -- Algebraic equalities (using ring identity to rewrite)
          have hR₁_eq : monomial D (1 : K) * x j * y l = monomial R₁ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          have hR₂_eq : monomial D (1 : K) * x i * y k = monomial R₂ 1 := by
            simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
          -- Rewrite and combine
          suffices heq : (monomial D) ((1 : K) * 1) *
              (x (K := K) l * y j * fij k i - x k * y i * fij l j) =
              monomial R₁ 1 * fij (K := K) k i + (-(monomial R₂ 1 * fij (K := K) l j)) by
            rw [heq]
            have hdeg_ne : binomialEdgeMonomialOrder.degree (monomial R₁ 1 * fij (K := K) k i) ≠
                binomialEdgeMonomialOrder.degree (-(monomial R₂ 1 * fij (K := K) l j)) := by
              rw [MonomialOrder.degree_neg]; intro heq'
              classical
              -- Evaluate at Sum.inl k to derive contradiction
              rw [degree_monomial_mul_fij (K := K) hki R₁,
                  degree_monomial_mul_fij (K := K) hlj R₂] at heq'
              have h_eval := Finsupp.ext_iff.mp heq' (Sum.inl k : BinomialEdgeVars V)
              have ev₁ : (R₁ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr i : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl k) = R₁ (Sum.inl k) + 1 := by
                simp only [Finsupp.add_apply, Finsupp.single_apply]; rfl
              have ev₂ : (R₂ + (Finsupp.single (Sum.inl l : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
                  (Sum.inl k) = R₂ (Sum.inl k) := by
                unfold BinomialEdgeVars at R₂ hR₂_def ⊢
                simp only [Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl l : V ⊕ V) = Sum.inl k) from
                    fun h => ne_of_gt hkl (Sum.inl.inj h),
                  Sum.inr_ne_inl, ite_false, add_zero]
              rw [ev₁, ev₂] at h_eval
              have hR₁_val : R₁ (Sum.inl k) = D (Sum.inl k) := by
                unfold BinomialEdgeVars at R₁ hR₁_def ⊢
                simp only [hR₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl j : V ⊕ V) = Sum.inl k) from
                    fun h => ne_of_gt (lt_trans hki hij) (Sum.inl.inj h),
                  Sum.inr_ne_inl, ite_false, add_zero]
              have hR₂_val : R₂ (Sum.inl k) = D (Sum.inl k) := by
                unfold BinomialEdgeVars at R₂ hR₂_def ⊢
                simp only [hR₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  show ¬((Sum.inl i : V ⊕ V) = Sum.inl k) from
                    fun h => heq_i (Sum.inl.inj h),
                  Sum.inr_ne_inl, ite_false, add_zero]
              omega
            obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_ne _ _ hdeg_ne
            exact isRemainder_add _ _ _ h₁R h₂R' hd₁ hd₂
          -- Prove the algebraic equality via ring identity
          rw [show (monomial D) ((1 : K) * 1) * (x l * y j * fij (K := K) k i - x k * y i * fij l j)
              = monomial D 1 * x j * y l * fij k i -
                monomial D 1 * x i * y k * fij l j from by simp only [fij]; ring,
            sub_eq_add_neg,
            show monomial D (1 : K) * x j * y l * fij k i =
              (monomial D 1 * x j * y l) * fij k i from by ring,
            show monomial D (1 : K) * x i * y k * fij l j =
              (monomial D 1 * x i * y k) * fij l j from by ring,
            hR₁_eq, hR₂_eq]
    · -- Different components case: D ≥ dπ and D ≥ dσ since paths share no vertices,
      -- so each term factors as monomial * groebnerElement, combined with degree bounds.
      push_neg at hshared
      -- Membership from head?/getLast?
      have i_in_π : i ∈ π := List.mem_of_head? hπ.2.1
      have j_in_π : j ∈ π := List.mem_of_getLast? hπ.2.2.1
      have k_in_σ : k ∈ σ := List.mem_of_head? hσ.2.1
      have l_in_σ : l ∈ σ := List.mem_of_getLast? hσ.2.2.1
      -- Non-membership from disjoint paths
      have k_not_π : k ∉ π := fun hk => (hshared k hk) k_in_σ
      have l_not_π : l ∉ π := fun hl => (hshared l hl) l_in_σ
      have i_not_σ : i ∉ σ := hshared i i_in_π
      have j_not_σ : j ∉ σ := hshared j j_in_π
      -- Internal vertices ⊆ full path
      have int_sub_π : ∀ v, v ∈ internalVertices π → v ∈ π :=
        fun v hv => (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hv)
      have int_sub_σ : ∀ v, v ∈ internalVertices σ → v ∈ σ :=
        fun v hv => (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hv)
      -- PathMonomial vanishing at cross-path endpoints
      have dπ_inl_k : dπ (Sum.inl k) = 0 :=
        pathMonomial_exponent_inl_zero (K := K) i j π k
          (fun h => k_not_π (int_sub_π k (List.mem_filter.mp h).1)) dπ hdπ
      have dπ_inr_l : dπ (Sum.inr l) = 0 :=
        pathMonomial_exponent_inr_zero (K := K) i j π l
          (fun h => l_not_π (int_sub_π l (List.mem_filter.mp h).1)) dπ hdπ
      have dσ_inl_i : dσ (Sum.inl i) = 0 :=
        pathMonomial_exponent_inl_zero (K := K) k l σ i
          (fun h => i_not_σ (int_sub_σ i (List.mem_filter.mp h).1)) dσ hdσ
      have dσ_inr_j : dσ (Sum.inr j) = 0 :=
        pathMonomial_exponent_inr_zero (K := K) k l σ j
          (fun h => j_not_σ (int_sub_σ j (List.mem_filter.mp h).1)) dσ hdσ
      -- fij degree formulas
      have hdeg_ij := fij_degree (K := K) i j hij
      have hdeg_kl := fij_degree (K := K) k l hkl
      -- D ≥ dπ pointwise (cross-condition: dπ vanishes where fij_ij < fij_kl)
      have D_ge_dπ : dπ ≤ D := by
        intro v
        unfold BinomialEdgeVars at *
        simp only [hD_def, hdeg_ij, hdeg_kl, Finsupp.sup_apply, Finsupp.add_apply,
          Finsupp.tsub_apply, Finsupp.single_apply]
        rcases v with w | w
        · simp only [Sum.inl.injEq, Sum.inr_ne_inl, ite_false, add_zero]
          by_cases hkw : k = w
          · subst hkw; simp [dπ_inl_k]
          · simp [hkw]; omega
        · simp only [Sum.inr.injEq, Sum.inl_ne_inr, ite_false, zero_add]
          by_cases hlw : l = w
          · subst hlw; simp [dπ_inr_l]
          · simp [hlw]; omega
      -- D ≥ dσ pointwise (cross-condition: dσ vanishes where fij_kl < fij_ij)
      have D_ge_dσ : dσ ≤ D := by
        intro v
        unfold BinomialEdgeVars at *
        simp only [hD_def, hdeg_ij, hdeg_kl, Finsupp.sup_apply, Finsupp.add_apply,
          Finsupp.tsub_apply, Finsupp.single_apply]
        rcases v with w | w
        · simp only [Sum.inl.injEq, Sum.inr_ne_inl, ite_false, add_zero]
          by_cases hiw : i = w
          · subst hiw; simp [dσ_inl_i]
          · simp [hiw]; omega
        · simp only [Sum.inr.injEq, Sum.inl_ne_inr, ite_false, zero_add]
          by_cases hjw : j = w
          · subst hjw; simp [dσ_inr_j]
          · simp [hjw]; omega
      -- Define quotient monomial degrees
      set Q₁ := D + (Finsupp.single (Sum.inl l) 1 : BinomialEdgeVars V →₀ ℕ) +
                     (Finsupp.single (Sum.inr k) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₁_def
      set Q₂ := D + (Finsupp.single (Sum.inl j) 1 : BinomialEdgeVars V →₀ ℕ) +
                     (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₂_def
      have dπ_le_Q₁ : dπ ≤ Q₁ := fun w => le_trans (D_ge_dπ w)
        (by simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; omega)
      have dσ_le_Q₂ : dσ ≤ Q₂ := fun w => le_trans (D_ge_dσ w)
        (by simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply]; omega)
      -- IsRemainder for each term via groebnerElement factorization
      have h₁ : binomialEdgeMonomialOrder.IsRemainder
          (monomial Q₁ 1 * fij (K := K) i j) (groebnerBasisSet G) 0 :=
        isRemainder_fij_via_groebnerElement G i j π hπ _ Q₁ rfl dπ hdπ dπ_le_Q₁
      have h₂ : binomialEdgeMonomialOrder.IsRemainder
          (monomial Q₂ 1 * fij (K := K) k l) (groebnerBasisSet G) 0 :=
        isRemainder_fij_via_groebnerElement G k l σ hσ _ Q₂ rfl dσ hdσ dσ_le_Q₂
      have h₂' : binomialEdgeMonomialOrder.IsRemainder
          (-(monomial Q₂ 1 * fij (K := K) k l)) (groebnerBasisSet G) 0 :=
        isRemainder_neg' _ _ h₂
      -- Algebraic equalities: monomial D * x l * y k = monomial Q₁, etc.
      have hQ₁_eq : monomial D (1 : K) * x l * y k = monomial Q₁ 1 := by
        simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
      have hQ₂_eq : monomial D (1 : K) * x j * y i = monomial Q₂ 1 := by
        simp only [x, y, X]; rw [monomial_mul, one_mul, monomial_mul, one_mul]
      -- Rewrite goal and combine via isRemainder_add
      suffices heq : (monomial D) ((1 : K) * 1) *
          (x (K := K) l * y k * fij i j - x j * y i * fij k l) =
          monomial Q₁ 1 * fij (K := K) i j + (-(monomial Q₂ 1 * fij (K := K) k l)) by
        rw [heq]
        have hdeg_ne : binomialEdgeMonomialOrder.degree (monomial Q₁ 1 * fij (K := K) i j) ≠
            binomialEdgeMonomialOrder.degree (-(monomial Q₂ 1 * fij (K := K) k l)) := by
          rw [MonomialOrder.degree_neg]; intro heq'
          classical
          -- Evaluate degrees at Sum.inl i to get contradiction
          have h1 := Finsupp.ext_iff.mp heq' (Sum.inl i : BinomialEdgeVars V)
          rw [degree_monomial_mul_fij (K := K) hij Q₁,
              degree_monomial_mul_fij (K := K) hkl Q₂] at h1
          have hne_ki : (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl i :=
            fun h => heq_i (Sum.inl.inj h).symm
          have hne_ji : (Sum.inl j : BinomialEdgeVars V) ≠ Sum.inl i :=
            fun h => (ne_of_lt hij) (Sum.inl.inj h).symm
          -- Evaluate both sides at Sum.inl i
          have ev₁ : (Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
              Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
              (Sum.inl i) = Q₁ (Sum.inl i) + 1 := by
            simp only [Finsupp.add_apply, Finsupp.single_apply]; rfl
          have ev₂ : (Q₂ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
              Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1 : BinomialEdgeVars V →₀ ℕ))
              (Sum.inl i) = Q₂ (Sum.inl i) := by
            simp only [Finsupp.add_apply, Finsupp.single_apply, hne_ki]; rfl
          rw [ev₁, ev₂] at h1
          have hQ₁_ge : Q₁ (Sum.inl i) ≥ D (Sum.inl i) := by
            unfold BinomialEdgeVars at Q₁ hQ₁_def ⊢
            simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; omega
          have hQ₂_le : Q₂ (Sum.inl i) = D (Sum.inl i) := by
            unfold BinomialEdgeVars at Q₂ hQ₂_def ⊢
            simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply, hne_ji,
              Sum.inr_ne_inl, ite_false, add_zero]
          omega
        obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_ne _ _ hdeg_ne
        exact isRemainder_add _ _ _ h₁ h₂' hd₁ hd₂
      -- Prove the algebraic equality
      rw [show (monomial D) ((1 : K) * 1) * (x l * y k * fij i j - x j * y i * fij k l)
          = monomial D 1 * x l * y k * fij i j -
            monomial D 1 * x j * y i * fij k l from by ring,
        sub_eq_add_neg,
        show monomial D (1 : K) * x l * y k * fij i j =
          (monomial D 1 * x l * y k) * fij i j from by ring,
        show monomial D (1 : K) * x j * y i * fij k l =
          (monomial D 1 * x j * y i) * fij k l from by ring,
        hQ₁_eq, hQ₂_eq]
end
-- The degree computation helpers, theorem_2_1_reduced, squarefree lemma,
-- and theorem_2_1_isReducedGroebnerBasis are in BEI/GroebnerBasis.lean.

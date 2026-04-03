import BEI.CoveredWalks
import BEI.ClosedGraphs
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

set_option maxHeartbeats 800000 in
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
      -- Membership from head?/getLast?
      have i_in_π : i ∈ π := List.mem_of_head? hπ.2.1
      have j_in_π : j ∈ π := List.mem_of_getLast? hπ.2.2.1
      have k_in_σ : k ∈ σ := List.mem_of_head? hσ.2.1
      have l_in_σ : l ∈ σ := List.mem_of_getLast? hσ.2.2.1
      -- Internal vertices ⊆ full path
      have int_sub_π : ∀ w, w ∈ internalVertices π → w ∈ π :=
        fun w hw => (List.tail_sublist π).mem ((List.dropLast_sublist _).mem hw)
      have int_sub_σ : ∀ w, w ∈ internalVertices σ → w ∈ σ :=
        fun w hw => (List.tail_sublist σ).mem ((List.dropLast_sublist _).mem hw)
      -- fij degree formulas
      have hdeg_ij := fij_degree (K := K) i j hij
      have hdeg_kl := fij_degree (K := K) k l hkl
      -- D ≥ dπ at positions where both fij degrees vanish
      -- D ≥ dσ at positions where both fij degrees vanish
      -- Apply coprime swap: rewrite the S-polynomial
      rw [fij_coprime_swap (K := K)]
      -- Goal: IsRemainder (monomial D (1*1) * (x l * y j * fij i k - x k * y i * fij j l)) G 0
      -- Define new quotient monomial degrees for swapped pairs
      set Q₁ := D + (Finsupp.single (Sum.inl l) 1 : BinomialEdgeVars V →₀ ℕ) +
                     (Finsupp.single (Sum.inr j) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₁_def
      set Q₂ := D + (Finsupp.single (Sum.inl k) 1 : BinomialEdgeVars V →₀ ℕ) +
                     (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₂_def
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
        -- σ-vertices (w < k) have y-coverage (Q₁(inr w) ≥ 1). Neither isRemainder_fij_of_covered_walk
        -- nor _y handles this directly. A mixed-coverage walk helper is needed.
        have h₁ : binomialEdgeMonomialOrder.IsRemainder
            (monomial Q₁ 1 * fij (K := K) i k) (groebnerBasisSet G) 0 := by
          have hπ_int_nd : (internalVertices π).Nodup :=
            (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
          have hσ_int_nd : (internalVertices σ).Nodup :=
            (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
          exact isRemainder_fij_of_mixed_walk G τ_ik.length i k τ_ik Q₁ le_rfl hik
            hτ_ik_h hτ_ik_l hτ_ik_nd hτ_ik_w (fun w hw => by
            have hw_ne_i := not_head_of_internal' τ_ik i hτ_ik_h hτ_ik_nd w hw
            have hw_ne_k := not_last_of_internal' τ_ik i k hτ_ik_h hτ_ik_l hτ_ik_nd w hw
            have hQ₁_ge_D : ∀ s, Q₁ s ≥ D s := fun s => by
              simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
            -- Check if w is one of the "easy" values covered by Q₁'s extra terms
            by_cases hw_eq_j : w = j
            · right; subst hw_eq_j
              simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
            · by_cases hw_eq_l : w = l
              · left; subst hw_eq_l
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · -- w ≠ i, j, k, l: both fij degrees are 0 at w's position, use sPolyD
                have hfij_inr0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) i j) (Sum.inr w) = 0 := by
                  rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                    fun h => hw_eq_j (Sum.inr_injective h).symm]
                have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) k l) (Sum.inr w) = 0 := by
                  rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                    fun h => hw_eq_l (Sum.inr_injective h).symm]
                have hfij_inl0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) i j) (Sum.inl w) = 0 := by
                  rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                    fun h => hw_ne_i (Sum.inl_injective h).symm]
                have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) k l) (Sum.inl w) = 0 := by
                  rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                    fun h => hw_ne_k (Sum.inl_injective h).symm]
                -- Get w's origin and prove coverage via pathMonomial exponents
                rcases hτ_ik_v w hw with hw_πR | hw_σR | hw_eq_v
                · have hw_π : w ∈ π := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                  have hw_int_π : w ∈ internalVertices π :=
                    mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                      (by rwa [head_of_head? hπ.2.1])
                      (by rwa [getLast_of_getLast? hπ.2.2.1])
                  rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                  · exact absurd hw_eq hw_ne_i
                  · exact absurd hw_eq hw_eq_j
                  · right
                    have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                      hwi hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₁_ge_D _))
                  · left
                    have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                      hjw hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₁_ge_D _))
                · have hw_σ : w ∈ σ := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                  have hw_int_σ : w ∈ internalVertices σ :=
                    mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                      (by rwa [head_of_head? hσ.2.1])
                      (by rwa [getLast_of_getLast? hσ.2.2.1])
                  rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                  · exact absurd hw_eq hw_ne_k
                  · exact absurd hw_eq hw_eq_l
                  · right
                    have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                      hwk hσ_int_nd dσ hdσ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hQ₁_ge_D _))
                  · left
                    have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                      hlw hσ_int_nd dσ hdσ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hQ₁_ge_D _))
                · subst hw_eq_v
                  have hv_int_π : w ∈ internalVertices π :=
                    mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                      (by rwa [head_of_head? hπ.2.1])
                      (by rwa [getLast_of_getLast? hπ.2.2.1])
                  rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                  · exact absurd hw_eq hw_ne_i
                  · exact absurd hw_eq hw_eq_j
                  · right
                    have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                      hwi hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₁_ge_D _))
                  · left
                    have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                      hjw hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₁_ge_D _)))
        -- Now handle fij(j, l)
        rcases lt_or_gt_of_ne heq_j with hjl | hlj
        · -- j < l
          have h₂ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₂ 1 * fij (K := K) j l) (groebnerBasisSet G) 0 := by
            have hπ_int_nd : (internalVertices π).Nodup :=
              (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
            have hσ_int_nd : (internalVertices σ).Nodup :=
              (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
            exact isRemainder_fij_of_mixed_walk G τ_jl.length j l τ_jl Q₂ le_rfl hjl
              hτ_jl_h hτ_jl_l hτ_jl_nd hτ_jl_w (fun w hw => by
              have hw_ne_j := not_head_of_internal' τ_jl j hτ_jl_h hτ_jl_nd w hw
              have hw_ne_l := not_last_of_internal' τ_jl j l hτ_jl_h hτ_jl_l hτ_jl_nd w hw
              have hQ₂_ge_D : ∀ s, Q₂ s ≥ D s := fun s => by
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
              by_cases hw_eq_k : w = k
              · left; subst hw_eq_k
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_i : w = i
                · right; subst hw_eq_i
                  simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inr w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_j (Sum.inr_injective h).symm]
                  have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inr w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_l (Sum.inr_injective h).symm]
                  have hfij_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inl w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_i (Sum.inl_injective h).symm]
                  have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inl w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_k (Sum.inl_injective h).symm]
                  rcases hτ_jl_v w hw with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    have hw_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    have hw_int_σ : w ∈ internalVertices σ :=
                      mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                        (by rwa [head_of_head? hσ.2.1])
                        (by rwa [getLast_of_getLast? hσ.2.2.1])
                    rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                    · exact absurd hw_eq hw_eq_k
                    · exact absurd hw_eq hw_ne_l
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                        hwk hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                        hlw hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hQ₂_ge_D _))
                  · subst hw_eq_v
                    have hv_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₂_ge_D _)))
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
              have hdeg₁ : binomialEdgeMonomialOrder.degree (monomial Q₁ (1 : K) * fij i k) =
                  Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr k : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) i k hik),
                  degree_monomial, if_neg one_ne_zero, fij_degree i k hik]
              have hdeg₂ : binomialEdgeMonomialOrder.degree (monomial Q₂ (1 : K) * fij j l) =
                  Q₂ + (Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) j l hjl),
                  degree_monomial, if_neg one_ne_zero, fij_degree j l hjl]
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
              rw [hdeg₁, hdeg₂, ev₁, ev₂] at h_eval
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
            have hπ_int_nd : (internalVertices π).Nodup :=
              (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
            have hσ_int_nd : (internalVertices σ).Nodup :=
              (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
            exact isRemainder_fij_of_mixed_walk G τ_ik.length i k τ_ik Q₁ le_rfl hik
              hτ_ik_h hτ_ik_l hτ_ik_nd hτ_ik_w (fun w hw => by
              have hw_ne_i := not_head_of_internal' τ_ik i hτ_ik_h hτ_ik_nd w hw
              have hw_ne_k := not_last_of_internal' τ_ik i k hτ_ik_h hτ_ik_l hτ_ik_nd w hw
              have hQ₁_ge_D : ∀ s, Q₁ s ≥ D s := fun s => by
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
              by_cases hw_eq_j : w = j
              · right; subst hw_eq_j
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_l : w = l
                · left; subst hw_eq_l
                  simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inr w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_eq_j (Sum.inr_injective h).symm]
                  have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inr w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_eq_l (Sum.inr_injective h).symm]
                  have hfij_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inl w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_ne_i (Sum.inl_injective h).symm]
                  have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inl w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_ne_k (Sum.inl_injective h).symm]
                  rcases hτ_ik_v w hw with hw_πR | hw_σR | hw_eq_v
                  · have hw_π : w ∈ π := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                    have hw_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_ne_i
                    · exact absurd hw_eq hw_eq_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₁_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₁_ge_D _))
                  · have hw_σ : w ∈ σ := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                    have hw_int_σ : w ∈ internalVertices σ :=
                      mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                        (by rwa [head_of_head? hσ.2.1])
                        (by rwa [getLast_of_getLast? hσ.2.2.1])
                    rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                    · exact absurd hw_eq hw_ne_k
                    · exact absurd hw_eq hw_eq_l
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                        hwk hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hQ₁_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                        hlw hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hQ₁_ge_D _))
                  · subst hw_eq_v
                    have hv_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_ne_i
                    · exact absurd hw_eq hw_eq_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₁_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₁_ge_D _)))
          -- h₂ for fij(l,j) with l < j
          have h₂ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₂ 1 * fij (K := K) l j) (groebnerBasisSet G) 0 := by
            have hπ_int_nd : (internalVertices π).Nodup :=
              (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
            have hσ_int_nd : (internalVertices σ).Nodup :=
              (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
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
              have hQ₂_ge_D : ∀ s, Q₂ s ≥ D s := fun s => by
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
              by_cases hw_eq_k : w = k
              · left; subst hw_eq_k
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_i : w = i
                · right; subst hw_eq_i
                  simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inr w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_j (Sum.inr_injective h).symm]
                  have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inr w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_l (Sum.inr_injective h).symm]
                  have hfij_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inl w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_i (Sum.inl_injective h).symm]
                  have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inl w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_k (Sum.inl_injective h).symm]
                  rcases hτ_jl_v w hw_orig with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    have hw_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    have hw_int_σ : w ∈ internalVertices σ :=
                      mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                        (by rwa [head_of_head? hσ.2.1])
                        (by rwa [getLast_of_getLast? hσ.2.2.1])
                    rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                    · exact absurd hw_eq hw_eq_k
                    · exact absurd hw_eq hw_ne_l
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                        hwk hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                        hlw hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hQ₂_ge_D _))
                  · subst hw_eq_v
                    have hv_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₂_ge_D _)))
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
              have hdeg₁ : binomialEdgeMonomialOrder.degree (monomial Q₁ (1 : K) * fij i k) =
                  Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr k : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) i k hik),
                  degree_monomial, if_neg one_ne_zero, fij_degree i k hik]
              have hdeg₂ : binomialEdgeMonomialOrder.degree (monomial Q₂ (1 : K) * fij l j) =
                  Q₂ + (Finsupp.single (Sum.inl l : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) l j hlj),
                  degree_monomial, if_neg one_ne_zero, fij_degree l j hlj]
              rw [hdeg₁, hdeg₂]; intro heq'
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
        -- Now goal: IsRemainder (monomial D (1*1) * (x l * y j * fij k i - x k * y i * fij l j)) G 0
        -- This has the same structure as the i < k case with (k,i) and (l,j) playing the roles
        -- of (i,k) and (j,l). Since k < i, fij(k,i) has k < i.
        -- The proof follows the same pattern as the i < k case above.
        -- Prove h₁: IsRemainder (monomial Q₁ 1 * fij k i) G 0
        -- Walk from k to i via τ_ik.reverse (k < i)
        have h₁ : binomialEdgeMonomialOrder.IsRemainder
            (monomial Q₁ 1 * fij (K := K) k i) (groebnerBasisSet G) 0 := by
          have hπ_int_nd : (internalVertices π).Nodup :=
            (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
          have hσ_int_nd : (internalVertices σ).Nodup :=
            (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
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
            have hQ₁_ge_D : ∀ s, Q₁ s ≥ D s := fun s => by
              simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
            by_cases hw_eq_j : w = j
            · right; subst hw_eq_j
              simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
            · by_cases hw_eq_l : w = l
              · left; subst hw_eq_l
                simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) i j) (Sum.inr w) = 0 := by
                  rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                    fun h => hw_eq_j (Sum.inr_injective h).symm]
                have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) k l) (Sum.inr w) = 0 := by
                  rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                    fun h => hw_eq_l (Sum.inr_injective h).symm]
                have hfij_inl0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) i j) (Sum.inl w) = 0 := by
                  rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                    fun h => hw_ne_i (Sum.inl_injective h).symm]
                have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                    (fij (K := K) k l) (Sum.inl w) = 0 := by
                  rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                  simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                    fun h => hw_ne_k (Sum.inl_injective h).symm]
                rcases hτ_ik_v w hw_orig with hw_πR | hw_σR | hw_eq_v
                · have hw_π : w ∈ π := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                  have hw_int_π : w ∈ internalVertices π :=
                    mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                      (by rwa [head_of_head? hπ.2.1])
                      (by rwa [getLast_of_getLast? hπ.2.2.1])
                  rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                  · exact absurd hw_eq hw_ne_i
                  · exact absurd hw_eq hw_eq_j
                  · right
                    have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                      hwi hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₁_ge_D _))
                  · left
                    have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                      hjw hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₁_ge_D _))
                · have hw_σ : w ∈ σ := List.mem_reverse.mp
                    ((List.drop_sublist _ _).mem
                      ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                  have hw_int_σ : w ∈ internalVertices σ :=
                    mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                      (by rwa [head_of_head? hσ.2.1])
                      (by rwa [getLast_of_getLast? hσ.2.2.1])
                  rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                  · exact absurd hw_eq hw_ne_k
                  · exact absurd hw_eq hw_eq_l
                  · right
                    have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                      hwk hσ_int_nd dσ hdσ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hQ₁_ge_D _))
                  · left
                    have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                      hlw hσ_int_nd dσ hdσ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hQ₁_ge_D _))
                · subst hw_eq_v
                  have hv_int_π : w ∈ internalVertices π :=
                    mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                      (by rwa [head_of_head? hπ.2.1])
                      (by rwa [getLast_of_getLast? hπ.2.2.1])
                  rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                  · exact absurd hw_eq hw_ne_i
                  · exact absurd hw_eq hw_eq_j
                  · right
                    have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                      hwi hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₁_ge_D _))
                  · left
                    have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                      hjw hπ_int_nd dπ hdπ
                    exact le_trans (by omega) (le_trans
                      (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₁_ge_D _)))
        -- Now handle fij(l, j) or fij(j, l)
        rcases lt_or_gt_of_ne heq_j with hjl | hlj
        · -- j < l: fij(l, j) = -(fij(j, l)), subtraction becomes addition
          have h₂ : binomialEdgeMonomialOrder.IsRemainder
              (monomial Q₂ 1 * fij (K := K) j l) (groebnerBasisSet G) 0 := by
            have hπ_int_nd : (internalVertices π).Nodup :=
              (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
            have hσ_int_nd : (internalVertices σ).Nodup :=
              (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
            exact isRemainder_fij_of_mixed_walk G τ_jl.length j l τ_jl Q₂ le_rfl hjl
              hτ_jl_h hτ_jl_l hτ_jl_nd hτ_jl_w (fun w hw => by
              have hw_ne_j := not_head_of_internal' τ_jl j hτ_jl_h hτ_jl_nd w hw
              have hw_ne_l := not_last_of_internal' τ_jl j l hτ_jl_h hτ_jl_l hτ_jl_nd w hw
              have hQ₂_ge_D : ∀ s, Q₂ s ≥ D s := fun s => by
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply]; split_ifs <;> omega
              by_cases hw_eq_k : w = k
              · left; subst hw_eq_k
                simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_i : w = i
                · right; subst hw_eq_i
                  simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inr w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_j (Sum.inr_injective h).symm]
                  have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inr w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_l (Sum.inr_injective h).symm]
                  have hfij_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inl w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_i (Sum.inl_injective h).symm]
                  have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inl w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_k (Sum.inl_injective h).symm]
                  rcases hτ_jl_v w hw with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    have hw_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    have hw_int_σ : w ∈ internalVertices σ :=
                      mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                        (by rwa [head_of_head? hσ.2.1])
                        (by rwa [getLast_of_getLast? hσ.2.2.1])
                    rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                    · exact absurd hw_eq hw_eq_k
                    · exact absurd hw_eq hw_ne_l
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                        hwk hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                        hlw hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hQ₂_ge_D _))
                  · subst hw_eq_v
                    have hv_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hQ₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hQ₂_ge_D _)))
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
              have hdeg₁ : binomialEdgeMonomialOrder.degree (monomial Q₁ (1 : K) * fij k i) =
                  Q₁ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr i : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) k i hki),
                  degree_monomial, if_neg one_ne_zero, fij_degree k i hki]
              have hdeg₂ : binomialEdgeMonomialOrder.degree (monomial Q₂ (1 : K) * fij j l) =
                  Q₂ + (Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) j l hjl),
                  degree_monomial, if_neg one_ne_zero, fij_degree j l hjl]
              rw [hdeg₁, hdeg₂]; intro heq'
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
                  show ((Sum.inl l : V ⊕ V) = Sum.inl l) from rfl,
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
            have hπ_int_nd : (internalVertices π).Nodup :=
              (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
            have hσ_int_nd : (internalVertices σ).Nodup :=
              (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
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
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_l : w = l
                · right; subst hw_eq_l
                  simp only [hR₁_def, Finsupp.add_apply, Finsupp.single_apply,
                    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inr w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_eq_j (Sum.inr_injective h).symm]
                  have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inr w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_eq_l (Sum.inr_injective h).symm]
                  have hfij_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inl w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_ne_i (Sum.inl_injective h).symm]
                  have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inl w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_ne_k (Sum.inl_injective h).symm]
                  rcases hτ_ik_v w hw_orig with hw_πR | hw_σR | hw_eq_v
                  · have hw_π : w ∈ π := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πR)))
                    have hw_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_ne_i
                    · exact absurd hw_eq hw_eq_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hR₁_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hR₁_ge_D _))
                  · have hw_σ : w ∈ σ := List.mem_reverse.mp
                      ((List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σR)))
                    have hw_int_σ : w ∈ internalVertices σ :=
                      mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                        (by rwa [head_of_head? hσ.2.1])
                        (by rwa [getLast_of_getLast? hσ.2.2.1])
                    rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                    · exact absurd hw_eq hw_ne_k
                    · exact absurd hw_eq hw_eq_l
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                        hwk hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hR₁_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                        hlw hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hR₁_ge_D _))
                  · subst hw_eq_v
                    have hv_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_ne_i
                    · exact absurd hw_eq hw_eq_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hR₁_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hR₁_ge_D _)))
          have h₂R : binomialEdgeMonomialOrder.IsRemainder
              (monomial R₂ 1 * fij (K := K) l j) (groebnerBasisSet G) 0 := by
            have hπ_int_nd : (internalVertices π).Nodup :=
              (hπ.2.2.2.1.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
            have hσ_int_nd : (internalVertices σ).Nodup :=
              (hσ.2.2.2.1.sublist (List.tail_sublist σ)).sublist (List.dropLast_sublist _)
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
                  Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
              · by_cases hw_eq_k : w = k
                · right; subst hw_eq_k
                  simp only [hR₂_def, Finsupp.add_apply, Finsupp.single_apply,
                    Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_true, ite_false]; omega
                · have hfij_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inr w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_j (Sum.inr_injective h).symm]
                  have hfkl_inr0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inr w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inr l : BinomialEdgeVars V) ≠ Sum.inr w from
                      fun h => hw_ne_l (Sum.inr_injective h).symm]
                  have hfij_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) i j) (Sum.inl w) = 0 := by
                    rw [hdeg_ij, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_i (Sum.inl_injective h).symm]
                  have hfkl_inl0 : binomialEdgeMonomialOrder.degree
                      (fij (K := K) k l) (Sum.inl w) = 0 := by
                    rw [hdeg_kl, Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
                    simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl w from
                      fun h => hw_eq_k (Sum.inl_injective h).symm]
                  rcases hτ_jl_v w hw_orig with hw_πD | hw_σD | hw_eq_v
                  · have hw_π : w ∈ π :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_πD))
                    have hw_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hw_π (List.ne_nil_of_mem hw_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hw_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hw_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hR₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hw_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hR₂_ge_D _))
                  · have hw_σ : w ∈ σ :=
                      (List.drop_sublist _ _).mem
                        ((List.tail_sublist _).mem ((List.dropLast_sublist _).mem hw_σD))
                    have hw_int_σ : w ∈ internalVertices σ :=
                      mem_internalVertices_of_ne hσ.2.2.2.1 hw_σ (List.ne_nil_of_mem hw_σ)
                        (by rwa [head_of_head? hσ.2.1])
                        (by rwa [getLast_of_getLast? hσ.2.2.1])
                    rcases hσ.2.2.2.2.1 w hw_σ with hw_eq | hw_eq | hwk | hlw
                    · exact absurd hw_eq hw_eq_k
                    · exact absurd hw_eq hw_ne_l
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) k l σ w hw_int_σ
                        hwk hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).2 (hR₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) k l σ w hw_int_σ
                        hlw hσ_int_nd dσ hdσ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).2 (hR₂_ge_D _))
                  · subst hw_eq_v
                    have hv_int_π : w ∈ internalVertices π :=
                      mem_internalVertices_of_ne hπ.2.2.2.1 hv_π (List.ne_nil_of_mem hv_π)
                        (by rwa [head_of_head? hπ.2.1])
                        (by rwa [getLast_of_getLast? hπ.2.2.1])
                    rcases hπ.2.2.2.2.1 w hv_π with hw_eq | hw_eq | hwi | hjw
                    · exact absurd hw_eq hw_eq_i
                    · exact absurd hw_eq hw_ne_j
                    · right
                      have := pathMonomial_exponent_inr_one (K := K) i j π w hv_int_π
                        hwi hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inr0 hfkl_inr0).1 (hR₂_ge_D _))
                    · left
                      have := pathMonomial_exponent_inl_one (K := K) i j π w hv_int_π
                        hjw hπ_int_nd dπ hdπ
                      exact le_trans (by omega) (le_trans
                        (sPolyD_ge_of_zero dπ dσ _ _ _ hfij_inl0 hfkl_inl0).1 (hR₂_ge_D _)))
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
              have hdeg₁ : binomialEdgeMonomialOrder.degree (monomial R₁ (1 : K) * fij k i) =
                  R₁ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr i : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) k i hki),
                  degree_monomial, if_neg one_ne_zero, fij_degree k i hki]
              have hdeg₂ : binomialEdgeMonomialOrder.degree (monomial R₂ (1 : K) * fij l j) =
                  R₂ + (Finsupp.single (Sum.inl l : BinomialEdgeVars V) 1 +
                        Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1) := by
                rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
                  (fij_ne_zero (K := K) l j hlj),
                  degree_monomial, if_neg one_ne_zero, fij_degree l j hlj]
              -- Evaluate at Sum.inl k to derive contradiction
              rw [hdeg₁, hdeg₂] at heq'
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
          have hdeg₁ : binomialEdgeMonomialOrder.degree (monomial Q₁ (1 : K) * fij i j) =
              Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
                    Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1) := by
            rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
              (fij_ne_zero (K := K) i j hij),
              degree_monomial, if_neg one_ne_zero, fij_degree i j hij]
          have hdeg₂ : binomialEdgeMonomialOrder.degree (monomial Q₂ (1 : K) * fij k l) =
              Q₂ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
                    Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1) := by
            rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
              (fij_ne_zero (K := K) k l hkl),
              degree_monomial, if_neg one_ne_zero, fij_degree k l hkl]
          -- Evaluate degrees at Sum.inl i to get contradiction
          have h1 := Finsupp.ext_iff.mp heq' (Sum.inl i : BinomialEdgeVars V)
          rw [hdeg₁, hdeg₂] at h1
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


/- DEAD CODE START (to be removed)
        w = Sum.inl i ∨ w = Sum.inr j := by
      intro w; rw [hdeg_ij]
      rcases w with v | v
      · -- w = inl v: degree = (if inl i = inl v then 1 else 0)
        simp only [Finsupp.add_apply, Finsupp.single_apply, Sum.inl_ne_inr, ite_false, add_zero]
        by_cases h : v = i
        · subst h; right; left; rfl
        · left; exact if_neg (fun heq => h (Sum.inl.inj heq).symm)
      · -- w = inr v: degree = (if inr j = inr v then 1 else 0)
        rw [Finsupp.add_apply, Finsupp.single_apply,
            if_neg (show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inr v from Sum.inl_ne_inr),
            Finsupp.single_apply, zero_add]
        by_cases h : v = j
        · subst h; right; right; rfl
        · left; exact if_neg (fun heq => h (Sum.inr.inj heq).symm)
    have deg_kl_zero_or : ∀ w, binomialEdgeMonomialOrder.degree (fij (K := K) k l) w = 0 ∨
        w = Sum.inl k ∨ w = Sum.inr l := by
      intro w; rw [hdeg_kl]
      rcases w with v | v
      · simp only [Finsupp.add_apply, Finsupp.single_apply, Sum.inl_ne_inr, ite_false, add_zero]
        by_cases h : v = k
        · subst h; right; left; rfl
        · left; exact if_neg (fun heq => h (Sum.inl.inj heq).symm)
      · rw [Finsupp.add_apply, Finsupp.single_apply,
            if_neg (show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inr v from Sum.inl_ne_inr),
            Finsupp.single_apply, zero_add]
        by_cases h : v = l
        · subst h; right; right; rfl
        · left; exact if_neg (fun heq => h (Sum.inr.inj heq).symm)
    -- dπ vanishes at endpoints of π (i,j) from the admissible path conditions
    have dπ_inl_i : dπ (Sum.inl i) = 0 := pathMonomial_exponent_inl_zero (K := K) i j π i
      (fun h => not_lt.mpr (le_of_lt hij) (of_decide_eq_true (List.mem_filter.mp h).2)) dπ hdπ
    have dπ_inr_j : dπ (Sum.inr j) = 0 := pathMonomial_exponent_inr_zero (K := K) i j π j
      (fun h => not_lt.mpr (le_of_lt hij) (of_decide_eq_true (List.mem_filter.mp h).2)) dπ hdπ
    have dσ_inl_k : dσ (Sum.inl k) = 0 := pathMonomial_exponent_inl_zero (K := K) k l σ k
      (fun h => not_lt.mpr (le_of_lt hkl) (of_decide_eq_true (List.mem_filter.mp h).2)) dσ hdσ
    have dσ_inr_l : dσ (Sum.inr l) = 0 := pathMonomial_exponent_inr_zero (K := K) k l σ l
      (fun h => not_lt.mpr (le_of_lt hkl) (of_decide_eq_true (List.mem_filter.mp h).2)) dσ hdσ
    -- D ≥ dπ and D ≥ dσ pointwise: at positions where both fij degrees are 0,
    -- use sPolyD_ge_of_zero. At positions where only one is nonzero, D dominates
    -- via the max-sub structure. At endpoints of the SAME path, dπ/dσ = 0.
    -- D ≥ dπ: use Finsupp-level inequalities (avoids pointwise case analysis)
    -- dπ ≤ dπ+fij ≤ sup(dπ+fij, dσ+fkl), and sup - fij ≥ (dπ+fij) - fij = dπ,
    -- then sup-fij ⊔ fkl ≥ sup-fij ≥ dπ.
    -- D ≥ dπ ⊔ dσ: at each v, if fij(v) < fkl(v) then dπ(v) = 0, and vice versa.
    -- This is the cross-condition for finsupp_sup_le_D.
    have D_ge_sup : dπ ⊔ dσ ≤ D := by
      intro v
      simp only [hD_def, Finsupp.sup_apply, Finsupp.add_apply, Finsupp.tsub_apply]
      -- Need: max(dπ v, dσ v) ≤ max(max(dπ v + fij v, dσ v + fkl v) - fij v, fkl v)
      -- If fij v < fkl v: dπ v = 0 (cross-condition)
      -- If fij v > fkl v: dσ v = 0 (cross-condition)
      -- If fij v = fkl v: direct
      have h_cross₁ : binomialEdgeMonomialOrder.degree (fij (K := K) i j) v <
          binomialEdgeMonomialOrder.degree (fij (K := K) k l) v → dπ v = 0 := by
        intro hlt
        rcases deg_ij_zero_or v with h | rfl | rfl
        · -- fij(v) = 0, so v must be inl k or inr l (from deg_kl > 0)
          rcases deg_kl_zero_or v with h' | rfl | rfl
          · simp [h, h'] at hlt
          · -- v = inl k: dπ(inl k) = 0 since k ∉ π
            exact pathMonomial_exponent_inl_zero (K := K) i j π k
              (fun h => hk_not_in_π (int_sub_π k (List.mem_filter.mp h).1)) dπ hdπ
          · -- v = inr l: dπ(inr l) = 0 since l ∉ π
            exact pathMonomial_exponent_inr_zero (K := K) i j π l
              (fun h => hl_not_in_π (int_sub_π l (List.mem_filter.mp h).1)) dπ hdπ
        · exact dπ_inl_i
        · exact dπ_inr_j
      have h_cross₂ : binomialEdgeMonomialOrder.degree (fij (K := K) k l) v <
          binomialEdgeMonomialOrder.degree (fij (K := K) i j) v → dσ v = 0 := by
        intro hlt
        rcases deg_kl_zero_or v with h | rfl | rfl
        · rcases deg_ij_zero_or v with h' | rfl | rfl
          · simp [h, h'] at hlt
          · -- v = inl i: dσ(inl i) = 0 since i ∉ σ
            exact pathMonomial_exponent_inl_zero (K := K) k l σ i
              (fun h => hi_not_in_σ (int_sub_σ i (List.mem_filter.mp h).1)) dσ hdσ
          · -- v = inr j: dσ(inr j) = 0 since j ∉ σ
            exact pathMonomial_exponent_inr_zero (K := K) k l σ j
              (fun h => hj_not_in_σ (int_sub_σ j (List.mem_filter.mp h).1)) dσ hdσ
        · exact dσ_inl_k
        · exact dσ_inr_l
      have := h_cross₁; have := h_cross₂; omega
    have D_ge_dπ : dπ ≤ D := le_trans le_sup_left D_ge_sup
    have D_ge_dσ : dσ ≤ D := le_trans le_sup_right D_ge_sup
    -- Monomial degrees for each term
    set Q₁ := D + (Finsupp.single (Sum.inl l) 1 : BinomialEdgeVars V →₀ ℕ) +
                   (Finsupp.single (Sum.inr k) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₁_def
    set Q₂ := D + (Finsupp.single (Sum.inl j) 1 : BinomialEdgeVars V →₀ ℕ) +
                   (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars V →₀ ℕ) with hQ₂_def
    have dπ_le_Q₁ : dπ ≤ Q₁ := fun w => le_trans (D_ge_dπ w)
      (by simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; omega)
    have dσ_le_Q₂ : dσ ≤ Q₂ := fun w => le_trans (D_ge_dσ w)
      (by simp only [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply]; omega)
    -- Each term reduces to 0
    have h₁ : binomialEdgeMonomialOrder.IsRemainder
        (monomial Q₁ 1 * fij (K := K) i j) (groebnerBasisSet G) 0 :=
      isRemainder_fij_via_groebnerElement G i j π hπ _ Q₁ rfl dπ hdπ dπ_le_Q₁
    have h₂ : binomialEdgeMonomialOrder.IsRemainder
        (monomial Q₂ 1 * fij (K := K) k l) (groebnerBasisSet G) 0 :=
      isRemainder_fij_via_groebnerElement G k l σ hσ _ Q₂ rfl dσ hdσ dσ_le_Q₂
    have h₂' : binomialEdgeMonomialOrder.IsRemainder
        (-(monomial Q₂ 1 * fij (K := K) k l)) (groebnerBasisSet G) 0 :=
      isRemainder_neg' _ _ h₂
    -- Algebraic equalities: monomial D 1 * x l * y k = monomial Q₁ 1, etc.
    have hQ₁_eq : monomial D (1 : K) * x l * y k = monomial Q₁ 1 := by
      simp only [x, y, X]
      rw [monomial_mul, one_mul, monomial_mul, one_mul]
    have hQ₂_eq : monomial D (1 : K) * x j * y i = monomial Q₂ 1 := by
      simp only [x, y, X]
      rw [monomial_mul, one_mul, monomial_mul, one_mul]
    -- Rewrite goal
    suffices heq : (monomial D) ((1 : K) * 1) *
        (x (K := K) l * y k * fij i j - x j * y i * fij k l) =
        monomial Q₁ 1 * fij (K := K) i j + (-(monomial Q₂ 1 * fij (K := K) k l)) by
      rw [heq]
      have hdeg_ne : binomialEdgeMonomialOrder.degree (monomial Q₁ 1 * fij (K := K) i j) ≠
          binomialEdgeMonomialOrder.degree (-(monomial Q₂ 1 * fij (K := K) k l)) := by
        rw [MonomialOrder.degree_neg]; intro heq'
        -- Degree of q₁*fij(i,j) at inl i = Q₁(inl i) + 1 (because fij has x_i)
        -- Degree of q₂*fij(k,l) at inl i = Q₂(inl i) (because k ≠ i)
        classical
        have hdeg₁ : binomialEdgeMonomialOrder.degree (monomial Q₁ (1 : K) * fij i j) =
            Q₁ + (Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1) := by
          rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
            (fij_ne_zero (K := K) i j hij),
            degree_monomial, if_neg one_ne_zero, fij_degree i j hij]
        have hdeg₂ : binomialEdgeMonomialOrder.degree (monomial Q₂ (1 : K) * fij k l) =
            Q₂ + (Finsupp.single (Sum.inl k : BinomialEdgeVars V) 1 +
                  Finsupp.single (Sum.inr l : BinomialEdgeVars V) 1) := by
          rw [degree_mul (monomial_eq_zero.not.mpr one_ne_zero)
            (fij_ne_zero (K := K) k l hkl),
            degree_monomial, if_neg one_ne_zero, fij_degree k l hkl]
        have h1 : (binomialEdgeMonomialOrder.degree (monomial Q₁ (1 : K) * fij i j))
            (Sum.inl i) = Q₁ (Sum.inl i) + 1 := by
          rw [hdeg₁]; simp [Finsupp.add_apply, Finsupp.single_apply, Sum.inr_ne_inl]
        have h2 : (binomialEdgeMonomialOrder.degree (monomial Q₂ (1 : K) * fij k l))
            (Sum.inl i) = Q₂ (Sum.inl i) := by
          rw [hdeg₂]; simp [Finsupp.add_apply, Finsupp.single_apply, Sum.inr_ne_inl,
            show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl i from
              fun h => heq_i (Sum.inl.inj h).symm]
        have h3 := Finsupp.ext_iff.mp heq' (Sum.inl i)
        -- h1: degree₁(inl i) = Q₁(inl i) + 1
        -- h2: degree₂(inl i) = Q₂(inl i)
        -- h3: degree₁(inl i) = degree₂(inl i)
        -- Q₂(inl i) = D(inl i) (since j ≠ i and inr i ≠ inl i)
        -- Q₁(inl i) ≥ D(inl i) (since Q₁ = D + single_l + single_k)
        -- So Q₁(inl i) + 1 > D(inl i) = Q₂(inl i) → contradiction
        have hQ₂_at_i : Q₂ (Sum.inl i) = D (Sum.inl i) := by
          simp [hQ₂_def, Finsupp.add_apply, Finsupp.single_apply, Sum.inr_ne_inl,
            show (Sum.inl j : BinomialEdgeVars V) ≠ Sum.inl i from
              fun h => (ne_of_lt hij) (Sum.inl.inj h).symm]
        have hQ₁_ge : Q₁ (Sum.inl i) ≥ D (Sum.inl i) := by
          simp only [hQ₁_def, Finsupp.add_apply, Finsupp.single_apply]; omega
        linarith
      obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_ne _ _ hdeg_ne
      exact isRemainder_add _ _ _ h₁ h₂' hd₁ hd₂
    -- Prove the algebraic equality
    have key : (monomial D) ((1 : K) * 1) * (x l * y k * fij i j - x j * y i * fij k l)
        = monomial D 1 * x l * y k * fij i j - monomial D 1 * x j * y i * fij k l := by
      ring
    rw [key, sub_eq_add_neg,
        show monomial D (1 : K) * x l * y k * fij i j =
          (monomial D 1 * x l * y k) * fij i j from by ring,
        show monomial D (1 : K) * x j * y i * fij k l =
          (monomial D 1 * x j * y i) * fij k l from by ring,
        hQ₁_eq, hQ₂_eq]
DEAD CODE END -/


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

/-! ## Paper-faithful wrapper: Theorem 2.1 (reduced Gröbner basis)

The paper states Theorem 2.1 as a single result: the admissible-path family is
a **reduced** Gröbner basis. We package the two separately-proved parts into one
combined statement. -/

/--
**Theorem 2.1** (paper-faithful wrapper): The admissible-path Gröbner basis set is
a reduced Gröbner basis of `J_G`. This combines:
- `theorem_2_1`: the set is a Gröbner basis;
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

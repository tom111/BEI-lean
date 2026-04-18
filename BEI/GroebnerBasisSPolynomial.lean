import BEI.CoveredWalks
import BEI.ClosedGraphs
import Mathlib.RingTheory.Ideal.Operations

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# S-polynomial case analysis for Theorem 2.1

This file contains:
- `groebnerBasisSet_span`: the Groebner basis set spans `J_G`.
- `groebnerElement_leadingCoeff` / `groebnerElement_leadingCoeff_isUnit`: leading coefficients.
- `theorem_2_1`: the full Buchberger S-polynomial case analysis proving the
  admissible-path set is a Groebner basis.

The reducedness half (`theorem_2_1_reduced`), squarefree leading monomials, and
the paper-faithful wrapper are in `BEI/GroebnerBasis.lean`.

## Reference: Herzog et al. (2010), Theorem 2.1
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
      obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
          ∃ τ : List V, τ.head? = some j ∧ τ.getLast? = some l ∧ τ.Nodup ∧
          τ.IsChain (fun u v => G.Adj u v) ∧
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
          τ.IsChain (fun u v => G.Adj u v) ∧
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
      obtain ⟨τ, hτ_head, hτ_last, hτ_nd, hτ_walk, hτ_verts⟩ :
          ∃ τ : List V, τ.head? = some i ∧ τ.getLast? = some k ∧ τ.Nodup ∧
          τ.IsChain (fun u v => G.Adj u v) ∧
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
          τ.IsChain (fun u v => G.Adj u v) ∧
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
end
-- The degree computation helpers, theorem_2_1_reduced, squarefree lemma,
-- and theorem_2_1_isReducedGroebnerBasis are in BEI/GroebnerBasis.lean.

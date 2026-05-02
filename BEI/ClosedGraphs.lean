import BEI.MonomialOrder
import BEI.GraphProperties
import BEI.GroebnerAPI
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Ideal

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Closed graphs and the Gröbner basis condition (Theorem 1.1)

This file formalizes Theorem 1.1 of Herzog et al. (2010): the quadratic generators
`f_{ij} = x_i y_j - x_j y_i` of the binomial edge ideal `J_G` form a Gröbner basis
with respect to the lex order if and only if G is a closed graph.

## Key definitions
- `generatorSet G`: the set of quadratic generators of `J_G`

## Reference: Herzog et al. (2010), Theorem 1.1
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## The generator set -/

/--
The set of quadratic generators of `binomialEdgeIdeal G`:
  `{f_{ij} = x_i y_j - x_j y_i | {i,j} ∈ E(G), i < j}`
-/
def generatorSet (G : SimpleGraph V) :
    Set (MvPolynomial (BinomialEdgeVars V) K) :=
  { f | ∃ i j : V, G.Adj i j ∧ i < j ∧ f = x i * y j - x j * y i }

omit [DecidableEq V] [Fintype V] in
/-- The generator set spans `binomialEdgeIdeal G`. -/
theorem generatorSet_span (G : SimpleGraph V) :
    Ideal.span (generatorSet (K := K) G) = binomialEdgeIdeal (K := K) G := rfl

omit [DecidableEq V] [Fintype V] in
private lemma fij_mem (G : SimpleGraph V) {a b : V}
    (hadj : G.Adj a b) (hab : a < b) :
    fij (K := K) a b ∈ generatorSet (K := K) G :=
  ⟨a, b, hadj, hab, rfl⟩

omit [DecidableEq V] [Fintype V] in
private lemma mul_fij_mem
    (G : SimpleGraph V) (q : MvPolynomial (BinomialEdgeVars V) K) {a b : V}
    (hadj : G.Adj a b) (hab : a < b) :
    q * fij (K := K) a b ∈ binomialEdgeIdeal (K := K) G :=
  Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a, b, hadj, hab, rfl⟩)

/-! ## Helper lemmas for the Buchberger case analysis -/

omit [DecidableEq V] in
private lemma zero_le_syn (d : BinomialEdgeVars V →₀ ℕ) :
    binomialEdgeMonomialOrder.toSyn 0 ≤ binomialEdgeMonomialOrder.toSyn d := by
  simp only [binomialEdgeMonomialOrder, MonomialOrder.lex, map_zero]
  exact bot_le

omit [DecidableEq V] in
/-- If `f ∈ G`, then `q * f` has remainder `0` modulo `G`. -/
lemma isRemainder_single_mul
    (f q : MvPolynomial (BinomialEdgeVars V) K)
    (G : Set (MvPolynomial (BinomialEdgeVars V) K))
    (h_mem : f ∈ G) :
    binomialEdgeMonomialOrder.IsRemainder (q * f) G 0 := by
  constructor
  · classical
    set b₀ : G := ⟨f, h_mem⟩
    refine ⟨Finsupp.single b₀ q, ?_, ?_⟩
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero, b₀]
    · intro b
      simp only [Finsupp.single_apply]
      split_ifs with heq
      · cases heq; simp only [b₀]; rw [mul_comm]
      · simp only [mul_zero, MonomialOrder.degree_zero]; exact zero_le_syn _
  · intro c hc; simp at hc

/-! ### Finsupp sup/tsub helpers -/

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Sup of two finsupps sharing `inl i`: the `inr` components are disjoint. -/
private lemma finsupp_ext_shared_inl (i j₁ j₂ : V) (hj : j₁ ≠ j₂) :
    let d₁ := Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr j₁) 1
    let d₂ := Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr j₂) 1
    (d₁ ⊔ d₂ = d₁ + Finsupp.single (Sum.inr j₂ : BinomialEdgeVars V) 1) ∧
    (d₁ + Finsupp.single (Sum.inr j₂ : BinomialEdgeVars V) 1 - d₁ =
      Finsupp.single (Sum.inr j₂ : BinomialEdgeVars V) 1) ∧
    (d₁ + Finsupp.single (Sum.inr j₂ : BinomialEdgeVars V) 1 - d₂ =
      Finsupp.single (Sum.inr j₁ : BinomialEdgeVars V) 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> {
    ext v; simp only [Finsupp.sup_apply, Finsupp.tsub_apply,
      Finsupp.add_apply]
    rcases v with u | u
    · have : (Sum.inr j₁ : BinomialEdgeVars V) ≠ Sum.inl u := Sum.inr_ne_inl
      have : (Sum.inr j₂ : BinomialEdgeVars V) ≠ Sum.inl u := Sum.inr_ne_inl
      simp_all
    · have : (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inr u := Sum.inl_ne_inr
      simp_all only [ne_eq]
      by_cases h1 : j₁ = u <;> by_cases h2 : j₂ = u
      · exact absurd (h1.trans h2.symm) hj
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
  }

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Sup of two finsupps sharing `inr j`: the `inl` components are disjoint. -/
private lemma finsupp_ext_shared_inr (i₁ i₂ j : V) (hi : i₁ ≠ i₂) :
    let d₁ := Finsupp.single (Sum.inl i₁ : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr j) 1
    let d₂ := Finsupp.single (Sum.inl i₂ : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr j) 1
    (d₁ ⊔ d₂ = d₁ + Finsupp.single (Sum.inl i₂ : BinomialEdgeVars V) 1) ∧
    (d₁ + Finsupp.single (Sum.inl i₂ : BinomialEdgeVars V) 1 - d₁ =
      Finsupp.single (Sum.inl i₂ : BinomialEdgeVars V) 1) ∧
    (d₁ + Finsupp.single (Sum.inl i₂ : BinomialEdgeVars V) 1 - d₂ =
      Finsupp.single (Sum.inl i₁ : BinomialEdgeVars V) 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> {
    ext v; simp only [Finsupp.sup_apply, Finsupp.tsub_apply,
      Finsupp.add_apply]
    rcases v with u | u
    · have : (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inl u := Sum.inr_ne_inl
      simp_all only [ne_eq]
      by_cases h1 : i₁ = u <;> by_cases h2 : i₂ = u
      · exact absurd (h1.trans h2.symm) hi
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    · have : (Sum.inl i₁ : BinomialEdgeVars V) ≠ Sum.inr u := Sum.inl_ne_inr
      have : (Sum.inl i₂ : BinomialEdgeVars V) ≠ Sum.inr u := Sum.inl_ne_inr
      simp_all
  }

/-! ### S-polynomial identities -/

omit [DecidableEq V] in
/-- S-polynomial of generators sharing first endpoint:
`S(f_{i,j₁}, f_{i,j₂}) = -(y_i) * f_{j₁,j₂}`. -/
lemma sPolynomial_fij_shared_first (i j₁ j₂ : V) (hij₁ : i < j₁)
    (hij₂ : i < j₂) (hj : j₁ ≠ j₂) :
    binomialEdgeMonomialOrder.sPolynomial (fij (K := K) i j₁)
      (fij (K := K) i j₂) = -(y i) * fij j₁ j₂ := by
  rw [sPolynomial_def, fij_degree i j₁ hij₁, fij_degree i j₂ hij₂,
      fij_leadingCoeff (K := K) i j₁ hij₁,
      fij_leadingCoeff (K := K) i j₂ hij₂]
  obtain ⟨hsup, htsub1, htsub2⟩ := finsupp_ext_shared_inl i j₁ j₂ hj
  rw [hsup, htsub1, htsub2]
  change (y j₂ : MvPolynomial (BinomialEdgeVars V) K) * fij i j₁ -
    (y j₁ : MvPolynomial (BinomialEdgeVars V) K) * fij i j₂ =
    -(y i) * fij j₁ j₂
  unfold fij x y; ring

omit [DecidableEq V] in
/-- S-polynomial of generators sharing last endpoint:
`S(f_{i₁,j}, f_{i₂,j}) = x_j * f_{i₁,i₂}`. -/
lemma sPolynomial_fij_shared_last (i₁ i₂ j : V) (hi₁j : i₁ < j)
    (hi₂j : i₂ < j) (hi : i₁ ≠ i₂) :
    binomialEdgeMonomialOrder.sPolynomial (fij (K := K) i₁ j)
      (fij (K := K) i₂ j) = x j * fij i₁ i₂ := by
  rw [sPolynomial_def, fij_degree i₁ j hi₁j, fij_degree i₂ j hi₂j,
      fij_leadingCoeff (K := K) i₁ j hi₁j,
      fij_leadingCoeff (K := K) i₂ j hi₂j]
  obtain ⟨hsup, htsub1, htsub2⟩ := finsupp_ext_shared_inr i₁ i₂ j hi
  rw [hsup, htsub1, htsub2]
  change (x i₂ : MvPolynomial (BinomialEdgeVars V) K) * fij i₁ j -
    (x i₁ : MvPolynomial (BinomialEdgeVars V) K) * fij i₂ j =
    x j * fij i₁ i₂
  unfold fij x y; ring

/-! ### Coprime case helpers -/

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Sup/tsub for coprime finsupps (no shared inl or inr components). -/
private lemma finsupp_ext_coprime (i₁ i₂ j₁ j₂ : V) (hi : i₁ ≠ i₂)
    (hj : j₁ ≠ j₂) :
    let d₁ := Finsupp.single (Sum.inl i₁ : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr j₁) 1
    let d₂ := Finsupp.single (Sum.inl i₂ : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr j₂) 1
    (d₁ ⊔ d₂ = d₁ + d₂) ∧ (d₁ + d₂ - d₁ = d₂) ∧
    (d₁ + d₂ - d₂ = d₁) := by
  refine ⟨?_, ?_, ?_⟩ <;> {
    ext v; simp only [Finsupp.sup_apply, Finsupp.tsub_apply,
      Finsupp.add_apply]
    rcases v with u | u
    · have : (Sum.inr j₁ : BinomialEdgeVars V) ≠ Sum.inl u :=
        Sum.inr_ne_inl
      have : (Sum.inr j₂ : BinomialEdgeVars V) ≠ Sum.inl u :=
        Sum.inr_ne_inl
      simp_all only [ne_eq]
      by_cases h1 : i₁ = u <;> by_cases h2 : i₂ = u
      · exact absurd (h1.trans h2.symm) hi
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
    · have : (Sum.inl i₁ : BinomialEdgeVars V) ≠ Sum.inr u :=
        Sum.inl_ne_inr
      have : (Sum.inl i₂ : BinomialEdgeVars V) ≠ Sum.inr u :=
        Sum.inl_ne_inr
      simp_all only [ne_eq]
      by_cases h1 : j₁ = u <;> by_cases h2 : j₂ = u
      · exact absurd (h1.trans h2.symm) hj
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
  }

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma monomial_sum_eq_mul (a b : BinomialEdgeVars V) :
    (monomial (Finsupp.single a 1 + Finsupp.single b 1)) (1 : K) =
    X a * X b := by
  rw [show (1 : K) = 1 * 1 from (mul_one 1).symm, ← monomial_mul]
  rfl

omit [DecidableEq V] in
/-- S-polynomial of generators with coprime leading monomials. -/
lemma sPolynomial_fij_coprime (i₁ i₂ j₁ j₂ : V) (hi₁j₁ : i₁ < j₁)
    (hi₂j₂ : i₂ < j₂) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂) :
    binomialEdgeMonomialOrder.sPolynomial (fij (K := K) i₁ j₁)
      (fij (K := K) i₂ j₂) =
    x j₂ * y i₂ * fij i₁ j₁ - x j₁ * y i₁ * fij i₂ j₂ := by
  rw [sPolynomial_def, fij_degree i₁ j₁ hi₁j₁, fij_degree i₂ j₂ hi₂j₂,
      fij_leadingCoeff (K := K) i₁ j₁ hi₁j₁,
      fij_leadingCoeff (K := K) i₂ j₂ hi₂j₂]
  obtain ⟨hsup, htsub1, htsub2⟩ :=
    finsupp_ext_coprime i₁ i₂ j₁ j₂ hi hj
  rw [hsup, htsub1, htsub2, monomial_sum_eq_mul,
    monomial_sum_eq_mul]
  unfold fij x y; ring

omit [DecidableEq V] in
/-- `IsRemainder` for `q₁ * f₁ - q₂ * f₂` when `f₁, f₂ ∈ G`, `f₁ ≠ f₂`,
and the degree bounds hold. -/
lemma isRemainder_sub_mul
    (f₁ f₂ q₁ q₂ : MvPolynomial (BinomialEdgeVars V) K)
    (G : Set (MvPolynomial (BinomialEdgeVars V) K))
    (h₁ : f₁ ∈ G) (h₂ : f₂ ∈ G) (hne : f₁ ≠ f₂)
    (hdeg₁ : binomialEdgeMonomialOrder.degree (q₁ * f₁)
      ≼[binomialEdgeMonomialOrder]
      binomialEdgeMonomialOrder.degree (q₁ * f₁ - q₂ * f₂))
    (hdeg₂ : binomialEdgeMonomialOrder.degree (q₂ * f₂)
      ≼[binomialEdgeMonomialOrder]
      binomialEdgeMonomialOrder.degree (q₁ * f₁ - q₂ * f₂)) :
    binomialEdgeMonomialOrder.IsRemainder
      (q₁ * f₁ - q₂ * f₂) G 0 := by
  constructor
  · classical
    set b₁ : G := ⟨f₁, h₁⟩
    set b₂ : G := ⟨f₂, h₂⟩
    have hb_ne : b₁ ≠ b₂ :=
      fun h => hne (congr_arg Subtype.val h)
    refine ⟨Finsupp.single b₁ q₁ + Finsupp.single b₂ (-q₂),
      ?_, ?_⟩
    · simp only [map_add, Finsupp.linearCombination_single,
        smul_eq_mul, add_zero, b₁, b₂]; ring
    · intro b
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      by_cases hb1 : b₁ = b
      · have hb2 : ¬(b₂ = b) :=
          fun h => hb_ne (hb1.trans h.symm)
        simp only [if_pos hb1, if_neg hb2, add_zero]
        rw [show b.val = f₁ from
          congr_arg Subtype.val hb1.symm, mul_comm]
        exact hdeg₁
      · by_cases hb2 : b₂ = b
        · simp only [if_neg hb1, if_pos hb2, zero_add]
          rw [show b.val = f₂ from
            congr_arg Subtype.val hb2.symm,
            mul_neg, MonomialOrder.degree_neg, mul_comm]
          exact hdeg₂
        · simp only [if_neg hb1, if_neg hb2, add_zero,
            mul_zero, MonomialOrder.degree_zero]
          exact zero_le_syn _
  · intro c hc; simp at hc

/-! ### Coprime degree bound helpers -/

omit [DecidableEq V] [Fintype V] in
lemma fij_ne_zero [Finite V] (a b : V) (hab : a < b) :
    fij (K := K) a b ≠ 0 := by
  intro h
  have := fij_leadingCoeff_isUnit (K := K) a b hab
  rw [h, MonomialOrder.leadingCoeff_zero] at this
  exact not_isUnit_zero this

omit [DecidableEq V] in
/-- The degree of `x j * y i * fij a b` splits as sum of degrees. -/
lemma degree_xy_mul_fij (i j a b : V) (hab : a < b) :
    binomialEdgeMonomialOrder.degree
      (x j * y i * fij (K := K) a b) =
    Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
      Finsupp.single (Sum.inr i) 1 +
      (Finsupp.single (Sum.inl a : BinomialEdgeVars V) 1 +
       Finsupp.single (Sum.inr b) 1) := by
  simp only [x, y]
  rw [MonomialOrder.degree_mul
    (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
    (fij_ne_zero a b hab),
    MonomialOrder.degree_mul (X_ne_zero _) (X_ne_zero _),
    MonomialOrder.degree_X, MonomialOrder.degree_X,
    fij_degree a b hab]

omit [DecidableEq V] in
/-- The degrees of the two terms in the coprime S-polynomial are distinct.
Discriminator: evaluate at `Sum.inl i₁` — one side has 1, the other has 0. -/
lemma coprime_degrees_ne (i₁ i₂ j₁ j₂ : V)
    (hi₁j₁ : i₁ < j₁) (hi₂j₂ : i₂ < j₂) (hi : i₁ ≠ i₂) :
    binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree
        (x j₂ * y i₂ * fij (K := K) i₁ j₁)) ≠
    binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree
        (x j₁ * y i₁ * fij (K := K) i₂ j₂)) := by
  rw [degree_xy_mul_fij i₂ j₂ i₁ j₁ hi₁j₁,
      degree_xy_mul_fij i₁ j₁ i₂ j₂ hi₂j₂]
  intro h
  have heq := binomialEdgeMonomialOrder.toSyn.injective h
  have h1 := Finsupp.ext_iff.mp heq (Sum.inl i₁ : BinomialEdgeVars V)
  simp only [Finsupp.add_apply, Finsupp.single_apply] at h1
  have : (Sum.inr i₂ : BinomialEdgeVars V) ≠ Sum.inl i₁ := Sum.inr_ne_inl
  have : (Sum.inr j₁ : BinomialEdgeVars V) ≠ Sum.inl i₁ := Sum.inr_ne_inl
  have : (Sum.inr i₁ : BinomialEdgeVars V) ≠ Sum.inl i₁ := Sum.inr_ne_inl
  have : (Sum.inr j₂ : BinomialEdgeVars V) ≠ Sum.inl i₁ := Sum.inr_ne_inl
  have : ¬((Sum.inl j₁ : BinomialEdgeVars V) = Sum.inl i₁) :=
    fun h => hi₁j₁.ne' (Sum.inl.inj h)
  have : ¬((Sum.inl i₂ : BinomialEdgeVars V) = Sum.inl i₁) :=
    fun h => hi (Sum.inl.inj h).symm
  simp_all

omit [DecidableEq V] in
/-- If `toSyn(deg f) ≠ toSyn(deg g)`, both degree bounds hold for `f - g`. -/
lemma degree_bounds_of_sub
    (f g : MvPolynomial (BinomialEdgeVars V) K)
    (hne : binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree f) ≠
      binomialEdgeMonomialOrder.toSyn
      (binomialEdgeMonomialOrder.degree g)) :
    (binomialEdgeMonomialOrder.degree f
      ≼[binomialEdgeMonomialOrder]
      binomialEdgeMonomialOrder.degree (f - g)) ∧
    (binomialEdgeMonomialOrder.degree g
      ≼[binomialEdgeMonomialOrder]
      binomialEdgeMonomialOrder.degree (f - g)) := by
  show binomialEdgeMonomialOrder.toSyn _ ≤ _ ∧
    binomialEdgeMonomialOrder.toSyn _ ≤ _
  rcases lt_or_gt_of_ne hne with h | h
  · have hfg : f - g = -(g - f) := by ring
    rw [hfg, MonomialOrder.degree_neg,
      MonomialOrder.degree_sub_of_lt h]
    exact ⟨le_of_lt h, le_refl _⟩
  · rw [MonomialOrder.degree_sub_of_lt h]
    exact ⟨le_refl _, le_of_lt h⟩

/-! ## Theorem 1.1 -/

omit [DecidableEq V] in
/-- Forward direction of Theorem 1.1: closed graph → Gröbner basis.

Applies the Buchberger criterion and performs case analysis on the four possible
configurations of two generators `f_{i₁,j₁}` and `f_{i₂,j₂}`:
1. Same pair (trivial)
2. Shared first endpoint `i₁ = i₂` (uses closedness condition 1)
3. Shared last endpoint `j₁ = j₂` (uses closedness condition 2)
4. Coprime (pure algebra, no closedness needed) -/
theorem closed_implies_groebner (G : SimpleGraph V) (h : IsClosedGraph G) :
    binomialEdgeMonomialOrder.IsGroebnerBasis (generatorSet (K := K) G)
      (binomialEdgeIdeal (K := K) G) := by
  classical
  -- All generators have unit leading coefficients
  have hGenUnit : ∀ g ∈ generatorSet (K := K) G,
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g hg
    obtain ⟨i, j, _, hij, rfl⟩ := hg
    exact fij_leadingCoeff_isUnit i j hij
  -- Apply Buchberger criterion
  rw [show binomialEdgeIdeal (K := K) G =
    Ideal.span (generatorSet (K := K) G)
    from (generatorSet_span G).symm]
  rw [binomialEdgeMonomialOrder.isGroebnerBasis_iff_sPolynomial_isRemainder
    hGenUnit]
  -- For each pair of generators, show S-polynomial reduces to 0
  intro ⟨g₁, hg₁⟩ ⟨g₂, hg₂⟩
  obtain ⟨i₁, j₁, hadj₁, hij₁, hg₁_eq⟩ := hg₁
  obtain ⟨i₂, j₂, hadj₂, hij₂, hg₂_eq⟩ := hg₂
  -- Normalize to fij notation (fij is a def, not abbrev)
  have hg₁_fij : g₁ = fij (K := K) i₁ j₁ := hg₁_eq
  have hg₂_fij : g₂ = fij (K := K) i₂ j₂ := hg₂_eq
  simp only [hg₁_fij, hg₂_fij]
  -- Case analysis on shared endpoints
  by_cases heq_i : i₁ = i₂ <;> by_cases heq_j : j₁ = j₂
  · -- Case 1: same pair (i₁ = i₂, j₁ = j₂)
    subst heq_i; subst heq_j
    rw [sPolynomial_self]
    simpa using isRemainder_single_mul (fij (K := K) i₁ j₁) 0
      (generatorSet (K := K) G) (fij_mem G hadj₁ hij₁)
  · -- Case 2: shared first endpoint (i₁ = i₂, j₁ ≠ j₂)
    subst heq_i
    rw [sPolynomial_fij_shared_first i₁ j₁ j₂ hij₁ hij₂ heq_j]
    -- Closedness gives G.Adj j₁ j₂
    have hadj_jj : G.Adj j₁ j₂ := h.1 hij₁ hij₂ heq_j hadj₁ hadj₂
    rcases lt_or_gt_of_ne heq_j with hjlt | hjgt
    · -- j₁ < j₂: -(y i₁) * fij j₁ j₂, and fij j₁ j₂ ∈ generatorSet
      exact isRemainder_single_mul (fij j₁ j₂) (-(y i₁)) _ (fij_mem G hadj_jj hjlt)
    · -- j₁ > j₂: fij j₁ j₂ = -(fij j₂ j₁)
      have : -(y (K := K) i₁) * fij j₁ j₂ = y i₁ * fij j₂ j₁ := by
        unfold fij; ring
      rw [this]
      exact isRemainder_single_mul (fij j₂ j₁) (y i₁) _ (fij_mem G hadj_jj.symm hjgt)
  · -- Case 3: shared last endpoint (j₁ = j₂, i₁ ≠ i₂)
    subst heq_j
    rw [sPolynomial_fij_shared_last i₁ i₂ j₁ hij₁ hij₂ heq_i]
    -- Closedness gives G.Adj i₁ i₂
    have hadj_ii : G.Adj i₁ i₂ := h.2 hij₁ hij₂ heq_i hadj₁ hadj₂
    rcases lt_or_gt_of_ne heq_i with hilt | higt
    · -- i₁ < i₂: x j₁ * fij i₁ i₂, and fij i₁ i₂ ∈ generatorSet
      exact isRemainder_single_mul (fij i₁ i₂) (x j₁) _ (fij_mem G hadj_ii hilt)
    · -- i₁ > i₂: fij i₁ i₂ = -(fij i₂ i₁)
      have : (x (K := K) j₁) * fij i₁ i₂ = -(x j₁) * fij i₂ i₁ := by
        unfold fij; ring
      rw [this]
      exact isRemainder_single_mul (fij i₂ i₁) (-(x j₁)) _ (fij_mem G hadj_ii.symm higt)
  · -- Case 4: coprime (i₁ ≠ i₂, j₁ ≠ j₂) — pure algebra
    rw [sPolynomial_fij_coprime i₁ i₂ j₁ j₂ hij₁ hij₂ heq_i heq_j]
    -- fij i₁ j₁ ≠ fij i₂ j₂ (they differ since i₁ ≠ i₂)
    have hfij_ne : fij (K := K) i₁ j₁ ≠ fij (K := K) i₂ j₂ := by
      intro heq
      have h1 := congr_arg binomialEdgeMonomialOrder.degree heq
      rw [fij_degree i₁ j₁ hij₁, fij_degree i₂ j₂ hij₂] at h1
      have h2 := Finsupp.ext_iff.mp h1
        (Sum.inl i₁ : BinomialEdgeVars V)
      simp only [Finsupp.add_apply, Finsupp.single_apply] at h2
      have : ¬((Sum.inl i₂ : BinomialEdgeVars V) = Sum.inl i₁) :=
        fun h => heq_i (Sum.inl.inj h).symm
      simp_all
    -- Degree bounds from coprime_degrees_ne + degree_bounds_of_sub
    have hne := coprime_degrees_ne (K := K) i₁ i₂ j₁ j₂ hij₁ hij₂ heq_i
    obtain ⟨hd₁, hd₂⟩ := degree_bounds_of_sub
      (x j₂ * y i₂ * fij (K := K) i₁ j₁)
      (x j₁ * y i₁ * fij (K := K) i₂ j₂) hne
    exact isRemainder_sub_mul (fij i₁ j₁) (fij i₂ j₂)
      (x j₂ * y i₂) (x j₁ * y i₁) _
      (fij_mem G hadj₁ hij₁) (fij_mem G hadj₂ hij₂) hfij_ne hd₁ hd₂

omit [DecidableEq V] in
/-- Lex degree of a cubic monomial `X u * X v * X w`. Each of the four branches
of `groebner_implies_closed` builds two such cubics whose degrees control the
lex comparison. -/
private lemma cubic_degree (u v w : BinomialEdgeVars V) :
    binomialEdgeMonomialOrder.degree
      (X u * X v * X w : MvPolynomial (BinomialEdgeVars V) K) =
    Finsupp.single u 1 + Finsupp.single v 1 + Finsupp.single w 1 := by
  rw [MonomialOrder.degree_mul
        (mul_ne_zero (X_ne_zero _) (X_ne_zero _)) (X_ne_zero _),
      MonomialOrder.degree_mul (X_ne_zero _) (X_ne_zero _),
      MonomialOrder.degree_X, MonomialOrder.degree_X, MonomialOrder.degree_X]

omit [DecidableEq V] [Fintype V] in
/-- Epilogue of the two Condition 1 branches in `groebner_implies_closed`:
from a Finsupp inequality whose RHS has a single `inl` slot at `μ` and two
`inr` slots at `α, β`, with `α < μ` and `a < b`, deduce `a = μ ∧ b = β`. -/
private lemma extract_cond1 (μ α β a b : V) (hαμ : α < μ) (hab : a < b)
    (h : Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1 ≤
        (Finsupp.single (Sum.inl μ) 1 + Finsupp.single (Sum.inr α) 1 +
          Finsupp.single (Sum.inr β) 1 : BinomialEdgeVars V →₀ ℕ)) :
    a = μ ∧ b = β := by
  classical
  have ha : a = μ := by
    have hle_inl := h (Sum.inl a)
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hle_inl
    by_contra haμ
    have hne_μa : (Sum.inl μ : BinomialEdgeVars V) ≠ Sum.inl a :=
      fun heq => haμ (Sum.inl.inj (α := V) (β := V) heq).symm
    simp [hne_μa] at hle_inl
  refine ⟨ha, ?_⟩
  subst ha
  have hle_inr := h (Sum.inr b)
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hle_inr
  by_contra hbβ
  have hne_βb : (Sum.inr β : BinomialEdgeVars V) ≠ Sum.inr b :=
    fun heq => hbβ (Sum.inr.inj (α := V) heq).symm
  by_cases hbα : b = α
  · subst hbα
    exact absurd (lt_trans hab hαμ) (lt_irrefl a)
  · have hne_αb : (Sum.inr α : BinomialEdgeVars V) ≠ Sum.inr b :=
      fun heq => hbα (Sum.inr.inj (α := V) heq).symm
    simp [hne_αb, hne_βb] at hle_inr

omit [DecidableEq V] [Fintype V] in
/-- Epilogue of the two Condition 2 branches in `groebner_implies_closed`:
from a Finsupp inequality whose RHS has two `inl` slots at `α, β` and a single
`inr` slot at `μ`, deduce `b = μ ∧ (a = α ∨ a = β)`. The disjunction is left
to the call site, which rules out the wrong disjunct from `hab : a < b` and
the remaining order data. -/
private lemma extract_cond2 (μ α β a b : V)
    (h : Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1 ≤
        (Finsupp.single (Sum.inl α) 1 + Finsupp.single (Sum.inl β) 1 +
          Finsupp.single (Sum.inr μ) 1 : BinomialEdgeVars V →₀ ℕ)) :
    b = μ ∧ (a = α ∨ a = β) := by
  classical
  have hb : b = μ := by
    have hle_inr := h (Sum.inr b)
    simp only [Finsupp.add_apply, Finsupp.single_apply] at hle_inr
    by_contra hbμ
    have hne_μb : (Sum.inr μ : BinomialEdgeVars V) ≠ Sum.inr b :=
      fun heq => hbμ (Sum.inr.inj (α := V) heq).symm
    simp [hne_μb] at hle_inr
  refine ⟨hb, ?_⟩
  have hle_inl := h (Sum.inl a)
  simp only [Finsupp.add_apply, Finsupp.single_apply] at hle_inl
  by_contra hh
  push_neg at hh
  have hne_αa : (Sum.inl α : BinomialEdgeVars V) ≠ Sum.inl a :=
    fun heq => hh.1 (Sum.inl.inj (α := V) (β := V) heq).symm
  have hne_βa : (Sum.inl β : BinomialEdgeVars V) ≠ Sum.inl a :=
    fun heq => hh.2 (Sum.inl.inj (α := V) (β := V) heq).symm
  simp [hne_αa, hne_βa] at hle_inl

omit [DecidableEq V] in
/-- Backward direction of Theorem 1.1: Gröbner basis → closed graph. -/
theorem groebner_implies_closed (G : SimpleGraph V)
    (h : binomialEdgeMonomialOrder.IsGroebnerBasis (generatorSet (K := K) G)
      (binomialEdgeIdeal (K := K) G)) :
    IsClosedGraph G := by
  classical
  -- All generators of generatorSet G have unit leading coefficients
  have hGenUnit : ∀ g ∈ generatorSet (K := K) G,
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g hg
    obtain ⟨i, j, _, hij, rfl⟩ := hg
    exact fij_leadingCoeff_isUnit i j hij
  -- Private lex helper: show that (M2 <lex M1) when M2 is missing inr d and M1 has it,
  -- and both are 0 at all inr v with v > d.
  -- Note: the inl-case in the Lex proof is vacuous (inl u < inr d is impossible).
  have lex_lt : ∀ (d : V) (M2 M1 : BinomialEdgeVars V →₀ ℕ),
      M2 (Sum.inr d) = 0 → M1 (Sum.inr d) = 1 →
      (∀ v : V, d < v → M2 (Sum.inr v) = M1 (Sum.inr v)) →
      binomialEdgeMonomialOrder.toSyn M2 < binomialEdgeMonomialOrder.toSyn M1 := by
    intro d M2 M1 hM2 hM1 hagree_inr
    rw [Finsupp.Lex.lt_iff]
    refine ⟨Sum.inr d, fun l hl => ?_, ?_⟩
    · simp only [binomialEdgeMonomialOrder, MonomialOrder.lex, AddEquiv.coe_mk, ofLex_toLex]
      cases l with
      | inl u => exact absurd hl.1 (by simp [binomialEdgeLE])
      | inr v =>
        have hvd : d < v := by
          obtain ⟨h1, h2⟩ := hl; simp only [binomialEdgeLE] at h1 h2
          exact lt_of_le_not_ge h1 h2
        exact hagree_inr v hvd
    · simp only [binomialEdgeMonomialOrder, MonomialOrder.lex, AddEquiv.coe_mk, ofLex_toLex]
      rw [hM2, hM1]; exact Nat.lt_succ_self 0
  -- Core contradiction helper
  have contra : ∀ (p : MvPolynomial (BinomialEdgeVars V) K)
      (D : BinomialEdgeVars V →₀ ℕ),
      p ∈ binomialEdgeIdeal (K := K) G →
      binomialEdgeMonomialOrder.degree p = D →
      D ≠ 0 →
      (∀ a b : V, G.Adj a b → a < b →
        ¬ (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1 ≤ D)) →
      False := fun p D hp_mem hp_deg hD_ne hno_gen => by
    have hp_ne : p ≠ 0 := fun heq => hD_ne (by rw [← hp_deg, heq, MonomialOrder.degree_zero])
    have hlt_in : binomialEdgeMonomialOrder.leadingTerm p ∈
        Ideal.span (binomialEdgeMonomialOrder.leadingTerm '' ↑(binomialEdgeIdeal (K := K) G)) :=
      Ideal.subset_span ⟨p, hp_mem, rfl⟩
    rw [h.2, span_leadingTerm_eq_span_monomial hGenUnit] at hlt_in
    have hsupp : binomialEdgeMonomialOrder.degree p ∈
        (binomialEdgeMonomialOrder.leadingTerm p).support := by
      simp only [MonomialOrder.leadingTerm]; classical
      rw [support_monomial, if_neg (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hp_ne)]
      exact Finset.mem_singleton_self _
    -- Convert hlt_in to use (fun s ↦ monomial s 1) '' (degree '' G) form
    have himg : (fun p ↦ (monomial (binomialEdgeMonomialOrder.degree p)) (1 : K)) ''
          generatorSet (K := K) G =
        (fun s : BinomialEdgeVars V →₀ ℕ ↦ (monomial s) (1 : K)) ''
            (binomialEdgeMonomialOrder.degree '' generatorSet (K := K) G) := by
      ext; simp [Set.mem_image]
    rw [himg, mem_ideal_span_monomial_image] at hlt_in
    obtain ⟨si, hsi_mem, hs_le⟩ := hlt_in (binomialEdgeMonomialOrder.degree p) hsupp
    obtain ⟨g, hg_mem, rfl⟩ := hsi_mem
    obtain ⟨a, b, hadj_ab, hab, rfl⟩ := hg_mem
    rw [show (x a * y b - x b * y a : MvPolynomial (BinomialEdgeVars V) K) =
        fij (K := K) a b from rfl, fij_degree a b hab, hp_deg] at hs_le
    exact hno_gen a b hadj_ab hab hs_le
  constructor
  · -- Condition 1: ∀ i j k, i<j → i<k → j≠k → adj(i,j) → adj(i,k) → adj(j,k)
    intro i j k hij hik hjk hadj_ij hadj_ik
    by_contra hnotadj
    rcases lt_or_gt_of_ne hjk with hjlt | hklt
    · -- Case j < k (so i < j < k): p = y j * fij i k - y k * fij i j = y i * fij j k
      -- p ∈ J_G; degree p = e_{inl j} + e_{inr i} + e_{inr k}
      have hp_mem : y j * (x i * y k - x k * y i) - y k * (x i * y j - x j * y i) ∈
          binomialEdgeIdeal (K := K) G := by
        exact Ideal.sub_mem (binomialEdgeIdeal (K := K) G)
          (by simpa [fij] using mul_fij_mem G (y j) hadj_ik (lt_trans hij hjlt))
          (by simpa [fij] using mul_fij_mem G (y k) hadj_ij hij)
      have hp_eq : y j * (x i * y k - x k * y i) - y k * (x i * y j - x j * y i) =
          (x j * y i * y k - x k * y i * y j : MvPolynomial (BinomialEdgeVars V) K) := by ring
      -- Degree of x j * y i * y k
      have hdeg1 : binomialEdgeMonomialOrder.degree
          (x j * y i * y k :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr k) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      have hdeg2 : binomialEdgeMonomialOrder.degree
          (x k * y i * y j :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr j) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      -- M2 <lex M1: discriminator = Sum.inr k (since k > j > i, inr k is lowest-ranked)
      have hne_ik : ¬(Sum.inr i = Sum.inr k) :=
        fun h => (lt_trans hij hjlt).ne (Sum.inr.inj (α := V) h)
      have hne_jk : ¬(Sum.inr j = Sum.inr k) :=
        fun h => hjlt.ne (Sum.inr.inj (α := V) h)
      have hlex_ineq := lex_lt k
          (Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr j) 1)
          (Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr k) 1)
          (by simp [Finsupp.add_apply, hne_ik, hne_jk])
          (by simp [Finsupp.add_apply, hne_ik])
          (fun v hv => by
            have hne_iv : ¬(Sum.inr i = Sum.inr v) :=
              fun h => (lt_trans (lt_trans hij hjlt) hv).ne
                (Sum.inr.inj (α := V) h)
            have hne_jv : ¬(Sum.inr j = Sum.inr v) :=
              fun h => (lt_trans hjlt hv).ne
                (Sum.inr.inj (α := V) h)
            have hne_kv : ¬(Sum.inr k = Sum.inr v) :=
              fun h => hv.ne (Sum.inr.inj (α := V) h)
            simp [Finsupp.add_apply, hne_iv, hne_jv, hne_kv])
      have hp_deg : binomialEdgeMonomialOrder.degree
          (y j * (x i * y k - x k * y i) -
            y k * (x i * y j - x j * y i) :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr k) 1 := by
        rw [hp_eq, MonomialOrder.degree_sub_of_lt
          (by rw [hdeg1, hdeg2]; exact hlex_ineq), hdeg1]
      apply contra _ _ hp_mem hp_deg
      · intro heq
        have := Finsupp.ext_iff.mp heq (Sum.inl j)
        simp [Finsupp.add_apply] at this
      · intro a b hadj_ab hab hs_le
        obtain ⟨rfl, rfl⟩ := extract_cond1 j i k a b hij hab hs_le
        exact hnotadj hadj_ab
    · -- Case k < j (so i < k < j):
      -- degree p = e_{inl k} + e_{inr i} + e_{inr j}
      have hp_mem : y k * (x i * y j - x j * y i) - y j * (x i * y k - x k * y i) ∈
          binomialEdgeIdeal (K := K) G := by
        exact Ideal.sub_mem (binomialEdgeIdeal (K := K) G)
          (by simpa [fij] using mul_fij_mem G (y k) hadj_ij hij)
          (by simpa [fij] using mul_fij_mem G (y j) hadj_ik hik)
      have hp_eq : y k * (x i * y j - x j * y i) - y j * (x i * y k - x k * y i) =
          (x k * y i * y j - x j * y i * y k : MvPolynomial (BinomialEdgeVars V) K) := by ring
      have hdeg1 : binomialEdgeMonomialOrder.degree
          (x k * y i * y j :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr j) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      have hdeg2 : binomialEdgeMonomialOrder.degree
          (x j * y i * y k :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr k) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      -- Discriminator = Sum.inr j
      -- (j > k, so inr j has lower rank than inr k)
      have hne_ij : ¬(Sum.inr i = Sum.inr j) :=
        fun h => hij.ne (Sum.inr.inj (α := V) h)
      have hne_kj : ¬(Sum.inr k = Sum.inr j) :=
        fun h => hklt.ne (Sum.inr.inj (α := V) h)
      have hlex_ineq := lex_lt j
          (Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr k) 1)
          (Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr j) 1)
          (by simp [Finsupp.add_apply, hne_ij, hne_kj])
          (by simp [Finsupp.add_apply, hne_ij])
          (fun v hv => by
            have hne_iv : ¬(Sum.inr i = Sum.inr v) :=
              fun h => (lt_trans hij hv).ne
                (Sum.inr.inj (α := V) h)
            have hne_kv : ¬(Sum.inr k = Sum.inr v) :=
              fun h => (lt_trans hklt hv).ne
                (Sum.inr.inj (α := V) h)
            have hne_jv : ¬(Sum.inr j = Sum.inr v) :=
              fun h => hv.ne (Sum.inr.inj (α := V) h)
            simp [Finsupp.add_apply, hne_iv, hne_kv, hne_jv])
      have hp_deg : binomialEdgeMonomialOrder.degree
          (y k * (x i * y j - x j * y i) -
            y j * (x i * y k - x k * y i) :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 +
            Finsupp.single (Sum.inr j) 1 := by
        rw [hp_eq, MonomialOrder.degree_sub_of_lt
          (by rw [hdeg1, hdeg2]; exact hlex_ineq), hdeg1]
      apply contra _ _ hp_mem hp_deg
      · intro heq
        have := Finsupp.ext_iff.mp heq (Sum.inl k)
        simp [Finsupp.add_apply] at this
      · intro a b hadj_ab hab hs_le
        obtain ⟨rfl, rfl⟩ := extract_cond1 k i j a b hik hab hs_le
        exact hnotadj hadj_ab.symm
  · -- Condition 2:
    intro i j k hik hjk hij hadj_ik hadj_jk
    by_contra hnotadj
    rcases lt_or_gt_of_ne hij with hilt | hjlt
    · -- Case i < j (so i < j < k): p = x j * fij i k - x i * fij j k = x k * fij i j
      -- degree p = e_{inl i} + e_{inl k} + e_{inr j}
      have hp_mem : x j * (x i * y k - x k * y i) - x i * (x j * y k - x k * y j) ∈
          binomialEdgeIdeal (K := K) G := by
        exact Ideal.sub_mem (binomialEdgeIdeal (K := K) G)
          (by simpa [fij] using mul_fij_mem G (x j) hadj_ik (lt_trans hilt hjk))
          (by simpa [fij] using mul_fij_mem G (x i) hadj_jk hjk)
      have hp_eq : x j * (x i * y k - x k * y i) - x i * (x j * y k - x k * y j) =
          (x i * x k * y j - x j * x k * y i : MvPolynomial (BinomialEdgeVars V) K) := by ring
      have hdeg1 : binomialEdgeMonomialOrder.degree
          (x i * x k * y j :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl i) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr j) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      have hdeg2 : binomialEdgeMonomialOrder.degree
          (x j * x k * y i :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      -- Discriminator = Sum.inr j;
      -- M2 = e_{inl j}+e_{inl k}+e_{inr i},
      -- M1 = e_{inl i}+e_{inl k}+e_{inr j}
      have hne_ij3 : ¬(Sum.inr i = Sum.inr j) :=
        fun h => hilt.ne (Sum.inr.inj (α := V) h)
      have hlex_ineq := lex_lt j
          (Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1)
          (Finsupp.single (Sum.inl i) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr j) 1)
          (by simp [Finsupp.add_apply, hne_ij3])
          (by simp [Finsupp.add_apply])
          (fun v hv => by
            have hne_iv : ¬(Sum.inr i = Sum.inr v) :=
              fun h => (lt_trans hilt hv).ne
                (Sum.inr.inj (α := V) h)
            have hne_jv : ¬(Sum.inr j = Sum.inr v) :=
              fun h => hv.ne (Sum.inr.inj (α := V) h)
            simp [Finsupp.add_apply, hne_iv, hne_jv])
      have hp_deg : binomialEdgeMonomialOrder.degree
          (x j * (x i * y k - x k * y i) -
            x i * (x j * y k - x k * y j) :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl i) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr j) 1 := by
        rw [hp_eq, MonomialOrder.degree_sub_of_lt
          (by rw [hdeg1, hdeg2]; exact hlex_ineq), hdeg1]
      apply contra _ _ hp_mem hp_deg
      · intro heq
        have := Finsupp.ext_iff.mp heq (Sum.inl i)
        simp [Finsupp.add_apply] at this
      · intro a b hadj_ab hab hs_le
        obtain ⟨rfl, rfl | rfl⟩ := extract_cond2 j i k a b hs_le
        · exact hnotadj hadj_ab
        · exact absurd hab (not_lt.mpr hjk.le)
    · -- Case j < i (so j < i < k): p = x i * fij j k - x j * fij i k = x k * fij j i
      -- degree p = e_{inl j} + e_{inl k} + e_{inr i}
      have hp_mem : x i * (x j * y k - x k * y j) - x j * (x i * y k - x k * y i) ∈
          binomialEdgeIdeal (K := K) G := by
        exact Ideal.sub_mem (binomialEdgeIdeal (K := K) G)
          (by simpa [fij] using mul_fij_mem G (x i) hadj_jk (lt_trans hjlt hik))
          (by simpa [fij] using mul_fij_mem G (x j) hadj_ik hik)
      have hp_eq : x i * (x j * y k - x k * y j) - x j * (x i * y k - x k * y i) =
          (x j * x k * y i - x i * x k * y j : MvPolynomial (BinomialEdgeVars V) K) := by ring
      have hdeg1 : binomialEdgeMonomialOrder.degree
          (x j * x k * y i :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      have hdeg2 : binomialEdgeMonomialOrder.degree
          (x i * x k * y j :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl i) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr j) 1 := by
        simp only [x, y]; exact cubic_degree _ _ _
      -- Discriminator = Sum.inr i;
      -- M2 = e_{inl i}+e_{inl k}+e_{inr j},
      -- M1 = e_{inl j}+e_{inl k}+e_{inr i}
      have hne_ij4 : ¬(Sum.inr i = Sum.inr j) :=
        fun h => hjlt.ne' (Sum.inr.inj (α := V) h)
      have hlex_ineq := lex_lt i
          (Finsupp.single (Sum.inl i) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr j) 1)
          (Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1)
          (by simp [Finsupp.add_apply, hne_ij4])
          (by simp [Finsupp.add_apply])
          (fun v hv => by
            have hne_jv : ¬(Sum.inr j = Sum.inr v) :=
              fun h => (lt_trans hjlt hv).ne
                (Sum.inr.inj (α := V) h)
            have hne_iv : ¬(Sum.inr i = Sum.inr v) :=
              fun h => hv.ne (Sum.inr.inj (α := V) h)
            simp [Finsupp.add_apply, hne_jv, hne_iv])
      have hp_deg : binomialEdgeMonomialOrder.degree
          (x i * (x j * y k - x k * y j) -
            x j * (x i * y k - x k * y i) :
            MvPolynomial (BinomialEdgeVars V) K) =
          Finsupp.single (Sum.inl j) 1 +
            Finsupp.single (Sum.inl k) 1 +
            Finsupp.single (Sum.inr i) 1 := by
        rw [hp_eq, MonomialOrder.degree_sub_of_lt
          (by rw [hdeg1, hdeg2]; exact hlex_ineq), hdeg1]
      apply contra _ _ hp_mem hp_deg
      · intro heq
        have := Finsupp.ext_iff.mp heq (Sum.inl j)
        simp [Finsupp.add_apply] at this
      · intro a b hadj_ab hab hs_le
        obtain ⟨rfl, rfl | rfl⟩ := extract_cond2 i j k a b hs_le
        · exact hnotadj hadj_ab.symm
        · exact absurd hab (not_lt.mpr hik.le)

omit [DecidableEq V] in
/--
**Theorem 1.1** (Herzog et al. 2010): The quadratic generators of `J_G` form a
Gröbner basis with respect to the lex order iff G is a closed graph.

Reference: Herzog et al. (2010), Theorem 1.1.
-/
theorem theorem_1_1 (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis (generatorSet (K := K) G)
      (binomialEdgeIdeal (K := K) G) ↔
    IsClosedGraph G :=
  ⟨groebner_implies_closed G, closed_implies_groebner G⟩

end

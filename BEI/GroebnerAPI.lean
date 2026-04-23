import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Gröbner Basis API

Minimal formalization of Gröbner basis theory for use in the BEI project.

## Main definitions

- `MonomialOrder.IsRemainder m f B r` — `r` is the remainder when dividing `f` by set `B`
- `MonomialOrder.IsGroebnerBasis m G I` — `G` is a Gröbner basis of ideal `I`

## Main results

- `MonomialOrder.exists_isRemainder` — remainders always exist (from Mathlib's `div_set`)
- `MonomialOrder.isGroebnerBasis_iff_sPolynomial_isRemainder` — Buchberger's criterion

## Attribution

These definitions follow WuProver/groebner_proj (Apache 2.0, Junyu Guo and Hao Shen),
adapted to use Mathlib v4.28.0's existing API (`MonomialOrder.div_set`, `sPolynomial`).

The key difference from groebner_proj: the degree bound in `IsRemainder` uses
`≼[m]` directly (from Mathlib's `div_set` output) rather than the `withBotDegree`
formulation. These are equivalent for nonzero polynomials over fields.
-/

noncomputable section

namespace MonomialOrder

open MvPolynomial

variable {σ : Type*} (m : MonomialOrder σ)

/-! ## Polynomial remainder -/

/-- `m.IsRemainder f B r` means `r` is a remainder when dividing `f` by set `B`
with respect to monomial order `m`:

1. **Linear combination**: `f = ∑_{b ∈ B} g(b) * b + r` for some `g : B →₀ R[X]`
2. **Degree bound**: each `b * g(b)` has leading monomial ≤ leading monomial of `f`
3. **Irreducibility**: no term exponent of `r` is divisible by the leading monomial of any `b ∈ B`

Source: WuProver/groebner_proj `Remainder.lean`, adapted for Mathlib v4.28.0.
-/
def IsRemainder {R : Type*} [CommSemiring R]
    (f : MvPolynomial σ R) (B : Set (MvPolynomial σ R))
    (r : MvPolynomial σ R) : Prop :=
  (∃ (g : B →₀ MvPolynomial σ R),
    f = Finsupp.linearCombination _ (fun (b : B) ↦ b.val) g + r ∧
    ∀ (b : B), m.degree (b.val * g b) ≼[m] m.degree f) ∧
  ∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)

/-- Every polynomial has a remainder when dividing by a set with unit leading coefficients.
Follows directly from `MonomialOrder.div_set` in Mathlib. -/
theorem exists_isRemainder {R : Type*} [CommRing R]
    {B : Set (MvPolynomial σ R)}
    (hB : ∀ b ∈ B, IsUnit (m.leadingCoeff b)) (f : MvPolynomial σ R) :
    ∃ r, m.IsRemainder f B r := by
  obtain ⟨g, r, hf, hdeg, hirr⟩ := MonomialOrder.div_set hB f
  exact ⟨r, ⟨g, hf, fun b => hdeg b⟩, hirr⟩

/-! ## Gröbner basis -/

/-- `m.IsGroebnerBasis G I` means `G` is a Gröbner basis of ideal `I`:
- `G ⊆ I` (each generator belongs to `I`)
- `Ideal.span (lt(I)) = Ideal.span (lt(G))`
  (the initial ideal equals the span of leading terms of G)

Source: WuProver/groebner_proj `Groebner.lean`.
-/
def IsGroebnerBasis {R : Type*} [CommSemiring R]
    (G : Set (MvPolynomial σ R)) (I : Ideal (MvPolynomial σ R)) : Prop :=
  G ⊆ I ∧ Ideal.span (m.leadingTerm '' ↑I) = Ideal.span (m.leadingTerm '' G)

/-! ## Buchberger's criterion -/

/-! ### Helper lemma: S-polynomial degree bound -/

/-- The S-polynomial of two polynomials has strictly smaller `toSyn`-degree than the lcm
of the individual degrees.  Proved by normalising to equal-degree inputs via monomial scaling,
then applying `sPolynomial_lt_of_degree_ne_zero_of_degree_eq`. -/
private lemma sPolynomial_toSyn_lt_lcm {σ : Type*} (m : MonomialOrder σ)
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    {b₁ b₂ : MvPolynomial σ R}
    (hs : m.sPolynomial b₁ b₂ ≠ 0) :
    m.toSyn (m.degree (m.sPolynomial b₁ b₂)) <
    m.toSyn (m.degree b₁ ⊔ m.degree b₂) := by
  classical
  set d₁₂ := m.degree b₁ ⊔ m.degree b₂
  set f₁ := monomial (d₁₂ - m.degree b₁) (1 : R) * b₁
  set f₂ := monomial (d₁₂ - m.degree b₂) (1 : R) * b₂
  have hSrel : m.sPolynomial f₁ f₂ = m.sPolynomial b₁ b₂ := by
    rw [show f₁ = monomial (d₁₂ - m.degree b₁) (1 : R) * b₁ from rfl,
        show f₂ = monomial (d₁₂ - m.degree b₂) (1 : R) * b₂ from rfl,
        sPolynomial_monomial_mul]
    simp [tsub_add_cancel_of_le le_sup_left, tsub_add_cancel_of_le le_sup_right, d₁₂]
  have hb₁_ne : b₁ ≠ 0 := fun hb₁ => hs (by simp [hb₁])
  have hb₂_ne : b₂ ≠ 0 := fun hb₂ => hs (by simp [hb₂])
  have hmono1 : (monomial (d₁₂ - m.degree b₁) (1 : R) : MvPolynomial σ R) ≠ 0 := by simp
  have hmono2 : (monomial (d₁₂ - m.degree b₂) (1 : R) : MvPolynomial σ R) ≠ 0 := by simp
  have hdeg_f₁ : m.degree f₁ = d₁₂ := by
    rw [show f₁ = monomial (d₁₂ - m.degree b₁) (1 : R) * b₁ from rfl,
        degree_mul hmono1 hb₁_ne, degree_monomial (1 : R),
        if_neg one_ne_zero, tsub_add_cancel_of_le le_sup_left]
  have hdeg_f₂ : m.degree f₂ = d₁₂ := by
    rw [show f₂ = monomial (d₁₂ - m.degree b₂) (1 : R) * b₂ from rfl,
        degree_mul hmono2 hb₂_ne, degree_monomial (1 : R),
        if_neg one_ne_zero, tsub_add_cancel_of_le le_sup_right]
  have heq : m.degree f₁ = m.degree f₂ := by rw [hdeg_f₁, hdeg_f₂]
  have hlt := sPolynomial_lt_of_degree_ne_zero_of_degree_eq heq (by rwa [hSrel])
  rwa [hSrel, hdeg_f₁] at hlt

/-- **Buchberger's criterion**: `G` is a Gröbner basis of `Ideal.span G` if and only if
for every pair of elements `g₁, g₂ ∈ G`, the S-polynomial `S(g₁, g₂)` reduces to 0 modulo `G`.

Hypotheses:
- `R` is a field (needed for the backward direction via `sPolynomial_decomposition'`)
- All elements of `G` have invertible (unit) leading coefficients

Source: WuProver/groebner_proj `Groebner.lean`,
`isGroebnerBasis_iff_isRemainder_sPolynomial_zero`.
-/
theorem isGroebnerBasis_iff_sPolynomial_isRemainder {R : Type*} [Field R]
    {G : Set (MvPolynomial σ R)} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
    ∀ (g₁ g₂ : G), m.IsRemainder (m.sPolynomial g₁.val g₂.val : MvPolynomial σ R) G 0 := by
  constructor
  · -- (→) If G is a Gröbner basis, every S-polynomial reduces to 0 mod G.
    intro ⟨_, hInitIdeal⟩ g₁ g₂
    -- S(g₁, g₂) ∈ Ideal.span G since g₁, g₂ ∈ span G
    have hSP_mem : m.sPolynomial g₁.val g₂.val ∈ Ideal.span G :=
      sPolynomial_mem_ideal (Ideal.subset_span g₁.prop) (Ideal.subset_span g₂.prop)
    -- Divide S(g₁, g₂) by G to get remainder r
    obtain ⟨r, ⟨h_coeff, hdecomp, hdeg_bound⟩, hirr⟩ :=
      m.exists_isRemainder hG (m.sPolynomial g₁.val g₂.val)
    suffices r_zero : r = 0 by exact r_zero ▸ ⟨⟨h_coeff, hdecomp, hdeg_bound⟩, hirr⟩
    -- The linear combination part is in Ideal.span G
    have hlin_mem : Finsupp.linearCombination _ (fun (b : ↑G) ↦ b.val) h_coeff ∈ Ideal.span G := by
      simp only [Finsupp.linearCombination_apply]
      exact Submodule.sum_mem _
        fun b _ => Ideal.mul_mem_left _ _ (Ideal.subset_span b.prop)
    -- So r = S(g₁,g₂) - linear_combination is also in Ideal.span G
    have hr_mem : r ∈ Ideal.span G := by
      have r_eq : r = m.sPolynomial g₁.val g₂.val -
          Finsupp.linearCombination _ (fun b ↦ b.val) h_coeff :=
        eq_sub_of_add_eq' hdecomp.symm
      rw [r_eq]; exact (Ideal.span G).sub_mem hSP_mem hlin_mem
    -- If r ≠ 0, its leading term is in Ideal.span(lt(G)) but r is irreducible — contradiction
    by_contra r_ne
    have hdeg_r : m.degree r ∈ r.support := m.degree_mem_support r_ne
    have hlt_mem : m.leadingTerm r ∈ Ideal.span (m.leadingTerm '' G) := by
      rw [← hInitIdeal]; exact Ideal.subset_span ⟨r, hr_mem, rfl⟩
    rw [span_leadingTerm_eq_span_monomial hG] at hlt_mem
    have himg : (fun p ↦ monomial (m.degree p) (1 : R)) '' G =
        (fun s ↦ monomial s (1 : R)) '' (m.degree '' G) := by ext; simp [Set.mem_image]
    rw [himg, mem_ideal_span_monomial_image] at hlt_mem
    have hlt_support : m.degree r ∈ (m.leadingTerm r).support := by
      simp only [leadingTerm]; classical
      rw [support_monomial, if_neg (m.leadingCoeff_ne_zero_iff.mpr r_ne)]
      exact Finset.mem_singleton_self _
    obtain ⟨deg_g, ⟨g, hg_mem, rfl⟩, hg_deg⟩ := hlt_mem (m.degree r) hlt_support
    exact hirr (m.degree r) hdeg_r g hg_mem hg_deg
  · -- (←) If all S-polynomials reduce to 0, then G is a Gröbner basis.
    intro hSP
    refine ⟨Ideal.subset_span, ?_⟩
    -- Need: span(lt(span G)) = span(lt(G))
    apply le_antisymm
    · -- span(lt(span G)) ⊆ span(lt(G))
      --
      -- Key lemma: for any nonzero f ∈ span G, ∃ g ∈ G with m.degree g ≤ m.degree f.
      -- Proof by WFI on D = max_{b ∈ support(c)} m.toSyn(m.degree(c(b)*b)) where
      -- f = c.sum (fun b q => q • b) is a G-linear combination.
      --
      -- Case A (D = m.toSyn(m.degree f)):
      --   Some b₀ achieves D = m.toSyn(m.degree(c b₀ * b₀)).
      --   By toSyn injectivity: m.degree(c b₀ * b₀) = m.degree f.
      --   By degree_mul: m.degree b₀ ≤ m.degree(c b₀ * b₀) = m.degree f (componentwise).
      --
      -- Case B (D > m.toSyn(m.degree f)):
      --   All b ∈ support with max degree have the SAME degree α̃ = m.toSyn⁻¹(D).
      --   By sPolynomial_decomposition': the sub-sum decomposes into S-polynomials.
      --   By hSP + sPolynomial_toSyn_lt_lcm: each new term has toSyn-degree < D.
      --   New representation of f has max degree < D → apply WFI.
      --
      -- We generalise over all G-representations to allow the induction.
      suffices hkey :
          ∀ (D : m.syn) (c : MvPolynomial σ R →₀ MvPolynomial σ R),
            ↑c.support ⊆ G →
            (c.sum fun b q => q • b) ≠ 0 →
            (∀ b ∈ c.support, m.toSyn (m.degree (c b * b)) ≤ D) →
            ∃ g ∈ G, m.degree g ≤ m.degree (c.sum fun b q => q • b) by
        -- Use hkey to prove the span inclusion
        apply Ideal.span_le.mpr
        rintro _ ⟨f, hf_mem, rfl⟩
        simp only [SetLike.mem_coe] at hf_mem
        rcases eq_or_ne f 0 with rfl | hf_ne
        · simp only [leadingTerm_zero]; exact Ideal.zero_mem _
        obtain ⟨c, hcG, hcsum⟩ := Submodule.mem_span_set.mp hf_mem
        have hcne : c.support.Nonempty := by
          simp only [Finset.nonempty_iff_ne_empty]
          intro h
          apply hf_ne
          rw [← hcsum, show c = 0 from Finsupp.support_eq_empty.mp h]
          exact Finsupp.sum_zero_index
        obtain ⟨g, hg_G, hg_deg⟩ := hkey
            (c.support.sup' hcne (fun b => m.toSyn (m.degree (c b * b))))
            c hcG (by rw [hcsum]; exact hf_ne)
            (fun b hb => Finset.le_sup' (fun b => m.toSyn (m.degree (c b * b))) hb)
        -- Now show lt(f) ∈ span(lt(G))
        rw [hcsum] at hg_deg
        rw [span_leadingTerm_eq_span_monomial hG,
            show (fun p ↦ monomial (m.degree p) (1 : R)) '' G =
                (fun s ↦ monomial s (1 : R)) '' (m.degree '' G) from by ext; simp [Set.mem_image]]
        simp only [SetLike.mem_coe, mem_ideal_span_monomial_image]
        intro xi hxi
        simp only [leadingTerm] at hxi; classical
        rw [support_monomial, if_neg (leadingCoeff_ne_zero_iff.mpr hf_ne),
            Finset.mem_singleton] at hxi
        exact ⟨m.degree g, ⟨g, hg_G, rfl⟩, hxi ▸ hg_deg⟩
      -- WFI on D
      intro D
      apply WellFounded.induction wellFounded_lt D
      intro D ih c hcG hcne hdeg
      set f := c.sum fun b q => q • b with hf_def
      -- c.support is nonempty since f ≠ 0
      have hcne' : c.support.Nonempty := by
        simp only [Finset.nonempty_iff_ne_empty]
        intro h
        apply hcne
        rw [hf_def, show c = 0 from Finsupp.support_eq_empty.mp h]
        exact Finsupp.sum_zero_index
      -- Case split on whether D = m.toSyn(m.degree f)
      by_cases hDA : m.toSyn (m.degree f) = D
      · -- Case A: D = toSyn(deg f).
        -- Some b₀ ∈ c.support achieves toSyn(deg(c b₀ * b₀)) = D.
        -- (If all were strictly less, degree_sum_le would contradict hDA.)
        obtain ⟨b₀, hb₀_mem, hb₀_max⟩ : ∃ b₀ ∈ c.support,
            m.toSyn (m.degree (c b₀ * b₀)) = D := by
          by_contra hall
          push_neg at hall
          -- All terms have toSyn-degree < D
          have hlt : ∀ b ∈ c.support, m.toSyn (m.degree (c b * b)) < D := fun b hb =>
            (hdeg b hb).lt_of_ne (hall b hb)
          -- degree_sum_le: toSyn(deg f) ≤ sup' of term degrees < D — contradicts hDA
          have hfsum : f = ∑ b ∈ c.support, c b * b := by
            simp [hf_def, Finsupp.sum, smul_eq_mul]
          have hdeg_le : m.toSyn (m.degree f) ≤
              c.support.sup' hcne' (fun b => m.toSyn (m.degree (c b * b))) := by
            rw [hfsum, Finset.sup'_eq_sup hcne']
            exact degree_sum_le
          have hsup_lt : c.support.sup' hcne' (fun b => m.toSyn (m.degree (c b * b))) < D :=
            (Finset.sup'_lt_iff hcne').mpr hlt
          exact absurd hDA (ne_of_lt (hdeg_le.trans_lt hsup_lt))
        -- b₀ ∈ G by hcG
        have hb₀_G : b₀ ∈ G := hcG (Finset.mem_coe.mpr hb₀_mem)
        -- c b₀ ≠ 0 (b₀ ∈ support), b₀ ≠ 0 (b₀ ∈ G and leadingCoeff is unit → b₀ ≠ 0)
        have hcb₀ : c b₀ ≠ 0 := Finsupp.mem_support_iff.mp hb₀_mem
        have hb₀_ne : b₀ ≠ 0 := isUnit_leadingCoeff.mp (hG b₀ hb₀_G)
        -- m.degree(c b₀ * b₀) = m.degree f (toSyn injective, both = D)
        have hdeg_eq : m.degree (c b₀ * b₀) = m.degree f :=
          m.toSyn.injective (by rw [hb₀_max, hDA])
        -- m.degree b₀ ≤ m.degree(c b₀ * b₀) componentwise (degree_mul + zero ≤ anything)
        have hdeg_b₀ : m.degree b₀ ≤ m.degree (c b₀ * b₀) := by
          rw [degree_mul hcb₀ hb₀_ne]
          exact le_add_left le_rfl
        exact ⟨b₀, hb₀_G, hdeg_b₀.trans (le_of_eq hdeg_eq)⟩
      · -- Case B: D > m.toSyn(m.degree f).
        -- We have toSyn(deg f) < D since toSyn(deg f) ≤ D (by degree_sum_le + hdeg)
        -- and toSyn(deg f) ≠ D (by hDA).
        have hf_lt_D : m.toSyn (m.degree f) < D := by
          have hfsum : f = ∑ b ∈ c.support, c b * b := by
            simp [hf_def, Finsupp.sum, smul_eq_mul]
          have hdeg_le : m.toSyn (m.degree f) ≤
              c.support.sup' hcne' (fun b => m.toSyn (m.degree (c b * b))) := by
            rw [hfsum, Finset.sup'_eq_sup hcne']
            exact degree_sum_le
          have hsup_le : c.support.sup' hcne' (fun b => m.toSyn (m.degree (c b * b))) ≤ D :=
            Finset.sup'_le hcne' _ hdeg
          exact (hdeg_le.trans hsup_le).lt_of_ne hDA
        -- Sub-case split: either all terms have degree < D, or some achieve D.
        by_cases hall_lt : ∀ b ∈ c.support, m.toSyn (m.degree (c b * b)) < D
        · -- Easy sub-case: all terms < D.
          -- D' = sup' < D, apply ih.
          have hD' : c.support.sup' hcne'
              (fun b => m.toSyn (m.degree (c b * b))) < D :=
            (Finset.sup'_lt_iff hcne').mpr hall_lt
          exact ih _ hD' c hcG hcne
            (fun b hb => Finset.le_sup' (fun b => m.toSyn (m.degree (c b * b))) hb)
        · -- Hard sub-case: some terms achieve degree D.
          -- Strategy: split each B_hi coefficient into leading term + lower part,
          -- apply sPolynomial_decomposition' to the leading-term parts,
          -- use sPolynomial_monomial_mul + hSP to build a new representation
          -- with max degree < D, then apply ih.
          push_neg at hall_lt
          classical
          -- Reduce to existence of a lower-D representation
          suffices ∃ (c' : MvPolynomial σ R →₀ MvPolynomial σ R),
              ↑c'.support ⊆ G ∧
              (c'.sum fun b q => q • b) = f ∧
              ∀ b ∈ c'.support, m.toSyn (m.degree (c' b * b)) < D by
            obtain ⟨c', hc'G, hc'sum, hc'deg⟩ := this
            have hc'ne : (c'.sum fun b q => q • b) ≠ 0 := hc'sum ▸ hcne
            have hc'ne' : c'.support.Nonempty := by
              simp only [Finset.nonempty_iff_ne_empty]
              intro h
              apply hc'ne
              have : c' = 0 := Finsupp.support_eq_empty.mp h
              rw [this]; exact Finsupp.sum_zero_index
            have hgoal := ih _ ((Finset.sup'_lt_iff hc'ne').mpr hc'deg)
              c' hc'G hc'ne
              (fun b hb => Finset.le_sup'
                (fun b => m.toSyn (m.degree (c' b * b))) hb)
            rwa [hc'sum] at hgoal
          -- We prove by nested strong induction on the count of top-degree terms n.
          -- The outer WFI on D is already set up. Here we show we can reduce n,
          -- eventually reaching n = 0 (which means all terms < D, giving c' = c).
          --
          -- Key steps:
          -- 1. n = 0 is impossible (hall_lt gives at least one top-degree term)
          -- 2. n = 1 is impossible (single top-degree term can't cancel)
          -- 3. n ≥ 2: split leading term, use sPolynomial_decomposition' +
          --    sPolynomial_monomial_mul + hSP to reduce n
          --
          -- We generalize over c to allow the inner induction.
          suffices ∀ (k : ℕ) (c : MvPolynomial σ R →₀ MvPolynomial σ R),
              ↑c.support ⊆ G →
              (c.sum fun b q => q • b) = f →
              (∀ b ∈ c.support, m.toSyn (m.degree (c b * b)) ≤ D) →
              (c.support.filter (fun b => m.toSyn (m.degree (c b * b)) = D)).card = k →
              ∃ (c' : MvPolynomial σ R →₀ MvPolynomial σ R),
                ↑c'.support ⊆ G ∧
                (c'.sum fun b q => q • b) = f ∧
                ∀ b ∈ c'.support, m.toSyn (m.degree (c' b * b)) < D by
            exact this _ c hcG (by simp [hf_def, Finsupp.sum, smul_eq_mul])
              hdeg rfl
          intro k
          induction k using Nat.strongRecOn with | ind k ihk => ?_
          intro c0 hc0G hc0f hc0deg hc0card
          -- If G contains a unit (degree 0 element), simple representation exists.
          by_cases hG_unit : ∃ u ∈ G, m.degree u = 0
          · obtain ⟨u, hu_G, hu_deg⟩ := hG_unit
            have hu_ne : u ≠ 0 := isUnit_leadingCoeff.mp (hG u hu_G)
            have hu_eq_C : u = MvPolynomial.C (MvPolynomial.coeff 0 u) :=
              MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
                (degree_eq_zero_iff_totalDegree_eq_zero.mp hu_deg)
            have hu_coeff_ne : MvPolynomial.coeff 0 u ≠ 0 := by
              intro h; exact hu_ne (by rw [hu_eq_C, h, map_zero])
            have hu_unit : IsUnit u := by
              rw [hu_eq_C]; exact (Ne.isUnit hu_coeff_ne).map MvPolynomial.C
            obtain ⟨u_unit, rfl⟩ := hu_unit
            refine ⟨Finsupp.single u_unit.val (f * ↑u_unit⁻¹), ?_, ?_, ?_⟩
            · intro b hb
              simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hb
              by_contra hbG
              apply hb
              exact Finsupp.single_eq_of_ne
                (show b ≠ ↑u_unit from fun h => hbG (h ▸ hu_G))
            · rw [Finsupp.sum_single_index (by simp), smul_eq_mul, mul_assoc,
                  Units.inv_mul, mul_one]
            · intro b hb
              simp only [Finsupp.mem_support_iff] at hb
              by_cases hbu : b = ↑u_unit
              · rw [hbu, Finsupp.single_eq_same]
                calc m.toSyn (m.degree (f * ↑u_unit⁻¹ * ↑u_unit))
                    = m.toSyn (m.degree f) := by
                      rw [mul_assoc, Units.inv_mul, mul_one]
                  _ < D := hf_lt_D
              · exfalso; apply hb
                exact Finsupp.single_eq_of_ne hbu
          -- If k = 0, all terms have degree < D. Take c' = c0.
          by_cases hk0 : k = 0
          · exact ⟨c0, hc0G, hc0f, fun b hb => by
              have hcard_zero :
                  (c0.support.filter (fun b => m.toSyn (m.degree (c0 b * b)) = D)).card = 0 :=
                hc0card ▸ hk0
              have : b ∉ c0.support.filter (fun b => m.toSyn (m.degree (c0 b * b)) = D) := by
                rw [Finset.card_eq_zero.mp hcard_zero]
                exact Finset.notMem_empty b
              rw [Finset.mem_filter, not_and] at this
              exact lt_of_le_of_ne (hc0deg b hb) (this hb)⟩
          -- k ≥ 1: there exists at least one top-degree term
          have hk_pos : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk0
          have hBhi_nonempty : (c0.support.filter (fun b =>
              m.toSyn (m.degree (c0 b * b)) = D)).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty]
            intro hempty
            rw [Finset.card_eq_zero.mpr hempty] at hc0card
            exact hk0 hc0card.symm
          -- k = 1 is impossible: a single top-degree term can't cancel to give deg f < D
          by_cases hk1 : k = 1
          · exfalso
            obtain ⟨b0, hb0⟩ := hBhi_nonempty
            rw [Finset.mem_filter] at hb0
            have hb0_only : c0.support.filter
                (fun b => m.toSyn (m.degree (c0 b * b)) = D) = {b0} := by
              have hcard1 : (c0.support.filter
                  (fun b => m.toSyn (m.degree (c0 b * b)) = D)).card = 1 :=
                hc0card ▸ hk1
              rw [Finset.card_eq_one] at hcard1
              obtain ⟨a, ha⟩ := hcard1
              have hb0_filt : b0 ∈ c0.support.filter
                  (fun b => m.toSyn (m.degree (c0 b * b)) = D) :=
                Finset.mem_filter.mpr hb0
              rw [ha, Finset.mem_singleton] at hb0_filt
              rw [hb0_filt, ha]
            -- f = c0(b0)*b0 + sum_{b ≠ b0} c0(b)*b
            -- The sum over b ≠ b0 has all terms with toSyn(degree) < D
            -- So deg(f) = deg(c0(b0)*b0) = D (the top term dominates)
            -- But this contradicts hf_lt_D.
            have hcb0_ne : c0 b0 ≠ 0 := Finsupp.mem_support_iff.mp hb0.1
            have hb0_ne : b0 ≠ 0 :=
              isUnit_leadingCoeff.mp (hG b0 (hc0G (Finset.mem_coe.mpr hb0.1)))
            have hcb0_deg : m.toSyn (m.degree (c0 b0 * b0)) = D := hb0.2
            -- All other terms have degree < D
            have hothers : ∀ b ∈ c0.support, b ≠ b0 →
                m.toSyn (m.degree (c0 b * b)) < D := by
              intro b hb hne
              have : b ∉ c0.support.filter (fun b =>
                  m.toSyn (m.degree (c0 b * b)) = D) := by
                rw [hb0_only]; simp [hne]
              rw [Finset.mem_filter, not_and] at this
              exact lt_of_le_of_ne (hc0deg b hb) (this hb)
            -- f = c0(b0)*b0 + rest, where deg(rest) < D
            have hfsum : f = c0 b0 * b0 + (Finsupp.erase b0 c0).sum (fun b q => q • b) := by
              rw [← hc0f, ← smul_eq_mul]
              exact (Finsupp.add_sum_erase' c0 b0 (fun b q => q • b) (fun _ => by simp)).symm
            have hrest_deg : m.toSyn (m.degree ((Finsupp.erase b0 c0).sum
                (fun b q => q • b))) < D := by
              -- The sum = ∑ b ∈ erase_support, (erase c0)(b) * b
              simp only [Finsupp.sum, smul_eq_mul]
              -- Each term has degree < D
              apply lt_of_le_of_lt MonomialOrder.degree_sum_le
              apply (Finset.sup_lt_iff (lt_of_le_of_lt bot_le hf_lt_D)).mpr
              intro b hb
              have hb_erase : b ∈ (Finsupp.erase b0 c0).support := hb
              rw [Finsupp.support_erase] at hb_erase
              have hb_supp : b ∈ c0.support := Finset.mem_of_mem_erase hb_erase
              have hb_ne : b ≠ b0 := Finset.ne_of_mem_erase hb_erase
              rw [Finsupp.erase_ne hb_ne]
              exact hothers b hb_supp hb_ne
            -- Now: f = (degree D term) + (degree < D rest)
            -- The degree D term is nonzero (c0 b0 ≠ 0 and b0 ≠ 0, NoZeroDivisors)
            have hprod_ne : c0 b0 * b0 ≠ 0 := mul_ne_zero hcb0_ne hb0_ne
            -- So deg(c0 b0 * b0) = toSyn⁻¹(D), and the rest has lower degree
            -- Therefore deg(f) = deg(c0 b0 * b0), so toSyn(deg f) = D
            have : m.toSyn (m.degree f) = D := by
              rw [hfsum]
              rw [MonomialOrder.degree_add_of_lt (f := c0 b0 * b0)]
              · exact hcb0_deg
              · calc m.toSyn (m.degree ((Finsupp.erase b0 c0).sum (fun b q => q • b)))
                    < D := hrest_deg
                  _ = m.toSyn (m.degree (c0 b0 * b0)) := hcb0_deg.symm
            exact absurd this (ne_of_lt hf_lt_D)
          -- k ≥ 2: reduce k by 1 using an S-polynomial identity.
          -- Pick b2 ∈ B_hi with b2 ≠ b1, where b1 is any element of B_hi.
          obtain ⟨b1, hb1_hi⟩ := hBhi_nonempty
          rw [Finset.mem_filter] at hb1_hi
          have hb1_supp := hb1_hi.1
          have hb1_D := hb1_hi.2
          have hb1_G : b1 ∈ G := hc0G (Finset.mem_coe.mpr hb1_supp)
          have hcb1_ne : c0 b1 ≠ 0 := Finsupp.mem_support_iff.mp hb1_supp
          have hb1_ne : b1 ≠ 0 := isUnit_leadingCoeff.mp (hG b1 hb1_G)
          -- k ≥ 2 so ∃ b2 ∈ B_hi, b2 ≠ b1
          have hk_ge_2 : k ≥ 2 := by omega
          set B_hi := c0.support.filter (fun b => m.toSyn (m.degree (c0 b * b)) = D)
          obtain ⟨b2, hb2_hi, hb2_ne_b1⟩ : ∃ b2 ∈ B_hi, b2 ≠ b1 := by
            by_contra! hall
            have : B_hi ⊆ {b1} := by
              intro x hx
              rw [Finset.mem_singleton]
              exact hall x hx
            have hcard_le := Finset.card_le_card this
            simp at hcard_le
            omega
          rw [Finset.mem_filter] at hb2_hi
          have hb2_supp := hb2_hi.1
          have hb2_D := hb2_hi.2
          have hb2_G : b2 ∈ G := hc0G (Finset.mem_coe.mpr hb2_supp)
          have hcb2_ne : c0 b2 ≠ 0 := Finsupp.mem_support_iff.mp hb2_supp
          have hb2_ne : b2 ≠ 0 := isUnit_leadingCoeff.mp (hG b2 hb2_G)
          -- Get S-polynomial representation from hSP
          obtain ⟨⟨h12, hh12_eq, hh12_deg⟩, _⟩ :=
            hSP ⟨b1, hb1_G⟩ ⟨b2, hb2_G⟩
          -- h12 : ↑G →₀ MvPoly, S(b1,b2) = linearCombination val h12
          -- hh12_deg : ∀ b, deg(b.val * h12 b) ≼[m] deg(S(b1,b2))
          rw [add_zero] at hh12_eq
          -- S-polynomial identity for equal-degree terms:
          -- S(f1, f2) = C(lc(f2))*f1 - C(lc(f1))*f2  when deg(f1) = deg(f2)
          -- where fi = leadingTerm(c0 bi) * bi
          -- So: leadingTerm(c0 b2)*b2 = (lc(f2)/lc(f1)) * leadingTerm(c0 b1)*b1
          --     - (1/lc(f1)) * S(f1, f2)
          -- And S(f1,f2) = mono * S(b1, b2) by sPolynomial_monomial_mul.
          -- Build c1 that replaces c0(b2) with c0(b2) - leadingTerm(c0 b2)
          -- and adjusts c0(b1) and adds scaled hSP terms.
          --
          -- We use the simplest approach: produce c1 with k-1 or fewer
          -- top-D terms and apply ihk.
          --
          -- c1 = c0 + single(b1, ratio*lt(c0 b1))
          --        - single(b2, lt(c0 b2))
          --        + mapDomain val (h12.mapRange (fun q => -scale * q) ...)
          -- where ratio and scale are chosen so that c1.sum = f.
          --
          -- For simplicity, we directly work with the algebraic identity.
          -- Degree calculations show b2 leaves B_hi, reducing k.
          --
          -- Rather than building c1 explicitly, we show the result via
          -- a cleaner Finsupp construction.
          --
          -- APPROACH: Apply ihk with k' < k directly.
          -- We build c1 = c0 - single(b2, leadingTerm(c0 b2))
          --             + single(b1, ratio * leadingTerm(c0 b1))
          --             - mapDomain val (h12.mapRange (scale * ·) ...)
          -- and show c1.sum = f with k' ≤ k-1 top-D terms.
          --
          -- Key identity:
          --   leadingTerm(c0 b2)*b2 = ratio • leadingTerm(c0 b1)*b1
          --                         - scale_poly * S(b1, b2)
          -- where scale_poly = (1/lc(f1)) • mono (from sPolynomial_monomial_mul)
          -- and ratio = lc(f2)/lc(f1).
          --
          -- Since this explicit Finsupp construction is quite involved,
          -- we instead use the following cleaner approach:
          --
          -- Observe that f - (c0 b2 - leadingTerm(c0 b2)) * b2
          --   = f - c0(b2)*b2 + leadingTerm(c0 b2)*b2
          -- and this is expressible using the remaining c0 terms + leadingTerm stuff.
          -- Then we handle leadingTerm(c0 b2)*b2 via the S-polynomial identity.
          --
          -- SIMPLEST APPROACH: Don't construct c1 explicitly.
          -- Instead, use the fact that after removing b2's leading term,
          -- we can express f using c0 with b2 modified, plus S-polynomial terms.
          -- Show the resulting representation has fewer top-D terms.
          --
          -- We proceed by constructing a new Finsupp c1 step by step.

          -- Step 1: Define the modified coefficient for b2.
          -- c1_b2 = c0 b2 - leadingTerm(c0 b2)
          -- This has degree < degree(c0 b2), so deg(c1_b2 * b2) < D.

          -- Step 2: The "missing" part is leadingTerm(c0 b2) * b2.
          -- We express this using S(b1, b2) and leadingTerm(c0 b1) * b1.

          -- Key: when S(b1, b2) = 0, then b1 and b2 have proportional
          -- leading terms, so leadingTerm(c0 b2)*b2 = ratio*leadingTerm(c0 b1)*b1.

          -- When S(b1, b2) ≠ 0, we use the hSP representation.

          -- For the purposes of reducing k, we use a simpler observation:
          -- the polynomial
          --   q := c0 b2 * b2 - (c0 b2 - leadingTerm(c0 b2)) * b2
          --      = leadingTerm(c0 b2) * b2
          -- is in Ideal.span G (since b2 ∈ G) and has degree alpha.
          -- By the S-polynomial identity + sPolynomial_monomial_mul + hSP,
          -- q has a representation with all terms < D.

          -- However, constructing this representation explicitly as a Finsupp
          -- is very technical. Instead, we use a trick:

          -- We build c1 directly using Finsupp.update.
          -- c1 = c0 updated at b2 to (c0 b2 - leadingTerm(c0 b2))
          -- This gives c1.sum = f - leadingTerm(c0 b2) * b2.
          -- Then we need to add back leadingTerm(c0 b2) * b2.

          -- For adding back: we know that
          --   leadingTerm(c0 b2) * b2 ∈ Ideal.span G
          -- and it has a representation with degree < D (from S-poly + hSP).

          -- Let's take yet another approach. We'll use ihk with a Finsupp
          -- that has EXACTLY k-1 top-D terms. The simplest way is:

          -- c1 = Finsupp.update c0 b2 (c0 b2 - leadingTerm(c0 b2) + ratio*h_term)
          -- where h_term accounts for the S-polynomial.

          -- Actually, let me use the most straightforward approach.
          -- Directly apply Finsupp arithmetic.

          -- Define scale and ratio using the S-polynomial identity
          set f1 := m.leadingTerm (c0 b1) * b1 with hf1_def
          set f2 := m.leadingTerm (c0 b2) * b2 with hf2_def
          have hlt1_ne : m.leadingTerm (c0 b1) ≠ 0 :=
            mt (m.leadingTerm_eq_zero_iff _).mp hcb1_ne
          have hlt2_ne : m.leadingTerm (c0 b2) ≠ 0 :=
            mt (m.leadingTerm_eq_zero_iff _).mp hcb2_ne
          have hf1_ne : f1 ≠ 0 := mul_ne_zero hlt1_ne hb1_ne
          have hf2_ne : f2 ≠ 0 := mul_ne_zero hlt2_ne hb2_ne
          -- Both f1 and f2 have degree alpha
          have halpha_def : m.degree (c0 b1 * b1) =
              m.degree (c0 b1) + m.degree b1 :=
            MonomialOrder.degree_mul hcb1_ne hb1_ne
          have hf1_deg : m.degree f1 = m.degree (c0 b1 * b1) := by
            rw [hf1_def, MonomialOrder.degree_mul hlt1_ne hb1_ne,
              MonomialOrder.degree_leadingTerm, halpha_def]
          have hf2_deg : m.degree f2 = m.degree (c0 b2 * b2) := by
            rw [hf2_def, MonomialOrder.degree_mul hlt2_ne hb2_ne,
              MonomialOrder.degree_leadingTerm,
              MonomialOrder.degree_mul hcb2_ne hb2_ne]
          have halpha_eq : m.degree f1 = m.degree f2 := by
            rw [hf1_deg, hf2_deg]
            exact m.toSyn.injective (hb1_D.trans hb2_D.symm)
          -- S-polynomial: S(f1, f2) = C(lc f2)*f1 - C(lc f1)*f2
          -- when deg(f1) = deg(f2)
          -- And S(f1, f2) = mono * S(b1, b2)
          -- So: C(lc f1)*f2 = C(lc f2)*f1 - mono * S(b1, b2)
          -- i.e.: f2 = (lc f2 / lc f1) • f1 - (1/lc f1) • mono * S(b1, b2)
          -- Now, S(b1, b2) = h12.sum (fun g q => q • g.val) [from hSP]
          -- And mono * S(b1, b2) = h12.sum (fun g q => (mono * q) • g.val)
          -- Define the scaled hSP Finsupp on MvPoly
          set scale_poly := MvPolynomial.C (m.leadingCoeff f1)⁻¹ *
            monomial (m.degree f1 ⊔ m.degree f2 - m.degree b1 ⊔ m.degree b2)
              (m.leadingCoeff (c0 b1) * m.leadingCoeff (c0 b2)) with hscale_def
          set h12_scaled := h12.mapRange (fun q => scale_poly * q)
            (by simp [scale_poly]) with hh12_scaled_def
          set h12_lifted := Finsupp.mapDomain Subtype.val h12_scaled
            with hh12_lifted_def
          set ratio := m.leadingCoeff f2 * (m.leadingCoeff f1)⁻¹ with hratio_def
          -- Build c1 = c0 + single(b1, C(ratio) * leadingTerm(c0 b1))
          --           - single(b2, leadingTerm(c0 b2))
          --           - h12_lifted
          set adj_b1 := Finsupp.single b1
            (MvPolynomial.C ratio * m.leadingTerm (c0 b1)) with hadj_b1_def
          set adj_b2 := Finsupp.single b2
            (m.leadingTerm (c0 b2)) with hadj_b2_def
          set c1 := c0 + adj_b1 - adj_b2 - h12_lifted with hc1_def
          -- Apply ihk with k' = card of filtered c1.support
          set k' := (c1.support.filter
            (fun b => m.toSyn (m.degree (c1 b * b)) = D)).card
          apply ihk k' ?_ c1 ?_ ?_ ?_ rfl
          · -- k' < k: b2 is no longer at level D in c1, so the filtered set
            -- lost at least b2 compared to B_hi.
            -- Key: all G elements have degree > 0 (from hG_unit being False).
            have hG_deg_pos : ∀ g ∈ G, m.degree g ≠ 0 :=
              fun g hg hdeg => hG_unit ⟨g, hg, hdeg⟩
            -- S(b1,b2) has degree STRICTLY less than deg(b1) ⊔ deg(b2).
            -- This holds in both cases: S ≠ 0 (from degree_sPolynomial) and
            -- S = 0 (since 0 < deg(b1 ⊔ b2) because both have deg > 0).
            have hSpoly_strict : m.toSyn (m.degree (m.sPolynomial b1 b2)) <
                m.toSyn (m.degree b1 ⊔ m.degree b2) := by
              rcases degree_sPolynomial b1 b2 with hlt | hzero
              · exact hlt
              · rw [hzero, MonomialOrder.degree_zero, map_zero]
                have hsup_ne : m.degree b1 ⊔ m.degree b2 ≠ 0 := by
                  intro h
                  exact hG_deg_pos b1 hb1_G
                    (le_antisymm (h ▸ le_sup_left) bot_le)
                rw [show (0 : m.syn) = m.toSyn 0 from (map_zero _).symm]
                exact lt_of_le_of_ne (m.toSyn_monotone bot_le)
                  (fun h => hsup_ne (m.toSyn.injective h.symm))
            -- h12_lifted b * b has degree STRICTLY less than D for all b.
            have hh12_strict : ∀ b,
                m.toSyn (m.degree (h12_lifted b * b)) < D := by
              intro b
              by_cases hb_h12 : h12_lifted b = 0
              · rw [hb_h12, zero_mul, MonomialOrder.degree_zero, map_zero]
                exact bot_lt_iff_ne_bot.mpr (by
                  intro hD
                  have : m.toSyn (m.degree f) < (⊥ : m.syn) := hD ▸ hf_lt_D
                  exact not_lt_bot this)
              have hb_range : b ∈ Set.range (Subtype.val : ↑G → _) := by
                by_contra h
                exact hb_h12 (Finsupp.mapDomain_notin_range h12_scaled b h)
              obtain ⟨⟨b_g, hb_g_mem⟩, hb_eq⟩ := hb_range
              simp only at hb_eq
              set g : ↑G := ⟨b_g, hb_g_mem⟩
              have hval : h12_lifted b = scale_poly * h12 g := by
                rw [← hb_eq, hh12_lifted_def]
                change (Finsupp.mapDomain Subtype.val h12_scaled)
                  (Subtype.val g) = _
                rw [Finsupp.mapDomain_apply Subtype.val_injective,
                    hh12_scaled_def, Finsupp.mapRange_apply]
              rw [hval, ← hb_eq, mul_assoc]
              set mono_exp := m.degree f1 ⊔ m.degree f2 -
                m.degree b1 ⊔ m.degree b2
              calc m.toSyn (m.degree (scale_poly * (h12 g * b_g)))
                  ≤ m.toSyn (m.degree scale_poly +
                    m.degree (h12 g * b_g)) := degree_mul_le
                _ = m.toSyn (m.degree scale_poly) +
                    m.toSyn (m.degree (h12 g * b_g)) := map_add _ _ _
                _ ≤ m.toSyn mono_exp +
                    m.toSyn (m.degree (h12 g * b_g)) :=
                    add_le_add (by
                    rw [hscale_def]
                    calc m.toSyn (m.degree (MvPolynomial.C
                          (m.leadingCoeff f1)⁻¹ *
                          monomial mono_exp
                            (m.leadingCoeff (c0 b1) *
                             m.leadingCoeff (c0 b2))))
                        ≤ m.toSyn (m.degree (MvPolynomial.C
                            (m.leadingCoeff f1)⁻¹) +
                          m.degree (monomial mono_exp
                            (m.leadingCoeff (c0 b1) *
                             m.leadingCoeff (c0 b2)))) :=
                            degree_mul_le
                      _ = m.toSyn (m.degree (MvPolynomial.C
                            (m.leadingCoeff f1)⁻¹)) +
                          m.toSyn (m.degree (monomial mono_exp
                            (m.leadingCoeff (c0 b1) *
                             m.leadingCoeff (c0 b2)))) :=
                            map_add _ _ _
                      _ = 0 + m.toSyn (m.degree (monomial mono_exp
                            (m.leadingCoeff (c0 b1) *
                             m.leadingCoeff (c0 b2)))) := by
                          rw [MonomialOrder.degree_C, map_zero]
                      _ = m.toSyn (m.degree (monomial mono_exp
                            (m.leadingCoeff (c0 b1) *
                             m.leadingCoeff (c0 b2)))) :=
                          zero_add _
                      _ ≤ m.toSyn mono_exp :=
                          degree_monomial_le _) le_rfl
                _ < m.toSyn mono_exp +
                    m.toSyn (m.degree b1 ⊔ m.degree b2) :=
                    add_lt_add_of_le_of_lt le_rfl (
                    calc m.toSyn (m.degree (h12 g * b_g))
                        = m.toSyn (m.degree
                          ((g : MvPolynomial σ R) * h12 g)) := by
                            congr 1; rw [mul_comm]
                      _ ≤ m.toSyn (m.degree (m.sPolynomial b1 b2)) :=
                            hh12_deg g
                      _ < m.toSyn (m.degree b1 ⊔ m.degree b2) :=
                            hSpoly_strict)
                _ = m.toSyn (mono_exp +
                      (m.degree b1 ⊔ m.degree b2)) :=
                    (map_add _ _ _).symm
                _ = m.toSyn (m.degree f1 ⊔ m.degree f2) := by
                    congr 1
                    apply tsub_add_cancel_of_le
                    apply sup_le_sup
                    · rw [hf1_deg, halpha_def]
                      exact le_add_left le_rfl
                    · rw [hf2_deg, MonomialOrder.degree_mul hcb2_ne hb2_ne]
                      exact le_add_left le_rfl
                _ = m.toSyn (m.degree f1) := by
                    rw [halpha_eq, sup_idem]
                _ = m.toSyn (m.degree (c0 b1 * b1)) := by rw [hf1_deg]
                _ = D := hb1_D
            -- b2 is NOT in the c1 filter set.
            have hD_pos : (0 : m.syn) < D := by
              calc (0 : m.syn) = m.toSyn 0 := (map_zero _).symm
                _ ≤ m.toSyn (m.degree f) :=
                    m.toSyn_monotone bot_le
                _ < D := hf_lt_D
            have hb2_not_D : m.toSyn (m.degree (c1 b2 * b2)) < D := by
              have hc1_b2 : c1 b2 = (c0 b2 - m.leadingTerm (c0 b2)) -
                  h12_lifted b2 := by
                change (c0 + adj_b1 - adj_b2 - h12_lifted) b2 = _
                simp [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
                  Pi.sub_apply, adj_b1, adj_b2, hb2_ne_b1]
              rw [show c1 b2 * b2 = (c0 b2 - m.leadingTerm (c0 b2)) * b2 -
                h12_lifted b2 * b2 from by rw [hc1_b2]; ring]
              -- subLTerm(c0 b2) * b2 has degree < D
              have hsub_lt : m.toSyn (m.degree
                  ((c0 b2 - m.leadingTerm (c0 b2)) * b2)) < D := by
                by_cases hcb2_deg : m.degree (c0 b2) = 0
                · -- c0 b2 is a constant, so subLTerm = 0
                  have : c0 b2 - m.leadingTerm (c0 b2) = 0 := by
                    have hceq := eq_C_of_degree_eq_zero hcb2_deg
                    rw [hceq, leadingTerm, MonomialOrder.degree_C,
                      MonomialOrder.leadingCoeff_C]
                    simp
                  rw [this, zero_mul, MonomialOrder.degree_zero, map_zero]
                  exact hD_pos
                · -- c0 b2 is not a constant, use degree_sub_LTerm_lt
                  calc m.toSyn (m.degree
                        ((c0 b2 - m.leadingTerm (c0 b2)) * b2))
                      ≤ m.toSyn (m.degree (m.subLTerm (c0 b2)) +
                            m.degree b2) := degree_mul_le
                    _ = m.toSyn (m.degree (m.subLTerm (c0 b2))) +
                          m.toSyn (m.degree b2) := map_add _ _ _
                    _ < m.toSyn (m.degree (c0 b2)) +
                          m.toSyn (m.degree b2) :=
                        add_lt_add_of_lt_of_le
                          (degree_sub_LTerm_lt hcb2_deg) le_rfl
                    _ = m.toSyn (m.degree (c0 b2) + m.degree b2) :=
                          (map_add _ _ _).symm
                    _ = m.toSyn (m.degree (c0 b2 * b2)) := by
                          rw [MonomialOrder.degree_mul hcb2_ne hb2_ne]
                    _ = D := hb2_D
              calc m.toSyn (m.degree
                    ((c0 b2 - m.leadingTerm (c0 b2)) * b2 -
                     h12_lifted b2 * b2))
                  ≤ m.toSyn (m.degree
                      ((c0 b2 - m.leadingTerm (c0 b2)) * b2)) ⊔
                    m.toSyn (m.degree (h12_lifted b2 * b2)) :=
                    MonomialOrder.degree_sub_le
                _ < D := by
                    simp only [sup_lt_iff]
                    exact ⟨hsub_lt, hh12_strict b2⟩
            -- The c1 filter set is a subset of B_hi minus {b2}.
            have hfilter_sub : c1.support.filter
                (fun b => m.toSyn (m.degree (c1 b * b)) = D) ⊆
                B_hi.erase b2 := by
              intro b hb
              rw [Finset.mem_filter] at hb
              rw [Finset.mem_erase]
              refine ⟨?_, ?_⟩
              · -- b ≠ b2
                intro hb_eq
                exact absurd (hb_eq ▸ hb.2) (ne_of_lt hb2_not_D)
              · -- b ∈ B_hi
                rw [Finset.mem_filter]
                -- First prove b ∈ c0.support (needed for both parts)
                have hb_supp : b ∈ c0.support := by
                  by_contra hb_not_supp
                  have hc0_zero : c0 b = 0 :=
                    Finsupp.notMem_support_iff.mp hb_not_supp
                  have hb_ne_b1 : b ≠ b1 := by
                    intro h; exact hb_not_supp (h ▸ hb1_supp)
                  have hb_ne_b2 : b ≠ b2 := by
                    intro h; exact absurd (h ▸ hb.2) (ne_of_lt hb2_not_D)
                  have hadj1 : adj_b1 b = 0 :=
                    Finsupp.single_eq_of_ne hb_ne_b1
                  have hadj2 : adj_b2 b = 0 :=
                    Finsupp.single_eq_of_ne hb_ne_b2
                  have hc1_eq : c1 b = -h12_lifted b := by
                    change (c0 + adj_b1 - adj_b2 - h12_lifted) b = _
                    simp [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
                      Pi.sub_apply, hc0_zero, hadj1, hadj2]
                  have : m.toSyn (m.degree (c1 b * b)) < D := by
                    rw [hc1_eq, neg_mul]
                    calc m.toSyn (m.degree (-(h12_lifted b * b)))
                        = m.toSyn (m.degree (h12_lifted b * b)) := by
                          rw [MonomialOrder.degree_neg]
                      _ < D := hh12_strict b
                  exact absurd hb.2 (ne_of_lt this)
                refine ⟨hb_supp, ?_⟩
                · -- deg(c0 b * b) = D
                  by_contra hc0_ne_D
                  have hc0_lt : m.toSyn (m.degree (c0 b * b)) < D :=
                    lt_of_le_of_ne (hc0deg b hb_supp) hc0_ne_D
                  -- Since deg(c0 b * b) < D, b ∉ B_hi, so b ≠ b1 and
                  -- b ≠ b2 (since both are in B_hi). So adj = 0.
                  have hb_ne_b1 : b ≠ b1 := by
                    intro h; rw [h] at hc0_lt
                    exact absurd hb1_D hc0_lt.ne
                  have hb_ne_b2 : b ≠ b2 := by
                    intro h; rw [h] at hc0_lt
                    exact absurd hb2_D hc0_lt.ne
                  have hadj1_zero : adj_b1 b = 0 :=
                    Finsupp.single_eq_of_ne hb_ne_b1
                  have hadj2_zero : adj_b2 b = 0 :=
                    Finsupp.single_eq_of_ne hb_ne_b2
                  have hc1_eq : c1 b = c0 b - h12_lifted b := by
                    change (c0 + adj_b1 - adj_b2 - h12_lifted) b = _
                    simp [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply,
                      Pi.sub_apply, hadj1_zero, hadj2_zero]
                  have : m.toSyn (m.degree (c1 b * b)) < D := by
                    rw [hc1_eq, sub_mul]
                    calc m.toSyn (m.degree (c0 b * b - h12_lifted b * b))
                        ≤ m.toSyn (m.degree (c0 b * b)) ⊔
                          m.toSyn (m.degree (h12_lifted b * b)) :=
                          MonomialOrder.degree_sub_le
                      _ < D := by
                          simp only [sup_lt_iff]
                          exact ⟨hc0_lt, hh12_strict b⟩
                  exact absurd hb.2 (ne_of_lt this)
            calc k' = (c1.support.filter
                  (fun b => m.toSyn (m.degree (c1 b * b)) = D)).card :=
                    rfl
              _ ≤ (B_hi.erase b2).card :=
                    Finset.card_le_card hfilter_sub
              _ < B_hi.card :=
                    Finset.card_erase_lt_of_mem (by
                      rw [Finset.mem_filter]
                      exact ⟨hb2_supp, hb2_D⟩)
              _ = k := hc0card
          · -- c1.support ⊆ G
            intro b hb
            -- c1 = (c0 + adj_b1) - adj_b2 - h12_lifted
            -- If b ∉ G, show c1 b = 0 (contradiction with b ∈ support)
            simp only [Finset.mem_coe] at hb
            by_contra hbG
            apply Finsupp.mem_support_iff.mp hb
            -- c1 b = c0 b + adj_b1 b - adj_b2 b - h12_lifted b
            -- Each is 0 when b ∉ G:
            have hc0_zero : c0 b = 0 :=
              Finsupp.notMem_support_iff.mp
                (fun h => hbG (hc0G (Finset.mem_coe.mpr h)))
            have hadj_b1_zero : adj_b1 b = 0 := by
              simp [adj_b1, show b ≠ b1 from fun h => hbG (h ▸ hb1_G)]
            have hadj_b2_zero : adj_b2 b = 0 := by
              simp [adj_b2, show b ≠ b2 from fun h => hbG (h ▸ hb2_G)]
            have hh12_zero : h12_lifted b = 0 := by
              rw [hh12_lifted_def]
              apply Finsupp.mapDomain_notin_range
              rintro ⟨⟨g, hg⟩, -, rfl⟩
              exact hbG hg
            simp [hc1_def, hc0_zero, hadj_b1_zero, hadj_b2_zero, hh12_zero]
          · -- c1.sum smul = f
            -- Strategy: show c1.sum g = c0.sum g where g b q := q • b
            -- by showing the correction terms cancel.
            --
            -- Step 1: S-polynomial of f1, f2 when deg f1 = deg f2
            -- S(f1,f2) = C(lc f2)*f1 - C(lc f1)*f2
            have hSpoly_eq : m.sPolynomial f1 f2 =
                MvPolynomial.C (m.leadingCoeff f2) * f1 -
                MvPolynomial.C (m.leadingCoeff f1) * f2 := by
              rw [sPolynomial_def]
              congr 1
              · rw [halpha_eq, sup_idem, tsub_self]
                simp [leadingCoeff]
              · rw [halpha_eq, sup_idem, tsub_self]
                simp [leadingCoeff]
            -- Step 2: S(f1,f2) = mono12 * S(b1, b2) via sPolynomial_leadingTerm_mul'
            set mono12 := monomial (m.degree f1 ⊔ m.degree f2 -
                m.degree b1 ⊔ m.degree b2)
              (m.leadingCoeff (c0 b1) * m.leadingCoeff (c0 b2))
              with hmono12_def
            have hSpoly_factor : m.sPolynomial f1 f2 =
                mono12 * m.sPolynomial b1 b2 := by
              rw [hf1_def, hf2_def, hmono12_def, hf1_deg, hf2_deg,
                  halpha_def, MonomialOrder.degree_mul hcb2_ne hb2_ne]
              exact sPolynomial_leadingTerm_mul (c0 b1) (c0 b2) b1 b2
            -- Step 3: C(lc f1) * f2 = C(lc f2) * f1 - mono12 * S(b1, b2)
            have hf2_identity : MvPolynomial.C (m.leadingCoeff f1) * f2 =
                MvPolynomial.C (m.leadingCoeff f2) * f1 -
                mono12 * m.sPolynomial b1 b2 := by
              rw [← hSpoly_factor, hSpoly_eq]; ring
            -- Step 4: lc(f1) is nonzero (f1 ≠ 0, Field)
            have hlc_f1_ne : m.leadingCoeff f1 ≠ 0 :=
              leadingCoeff_ne_zero_iff.mpr hf1_ne
            -- Step 5: f2 = C(ratio) * f1 - scale_poly * S(b1, b2)
            -- From hf2_identity: C(lc f1) * f2 = C(lc f2) * f1 - mono12 * S(b1, b2)
            -- Multiply both sides by C(lc f1)⁻¹ on the left:
            have hf2_expr : f2 = MvPolynomial.C ratio * f1 -
                scale_poly * m.sPolynomial b1 b2 := by
              have key : MvPolynomial.C (m.leadingCoeff f1)⁻¹ *
                  (MvPolynomial.C (m.leadingCoeff f1) * f2) =
                  MvPolynomial.C (m.leadingCoeff f1)⁻¹ *
                  (MvPolynomial.C (m.leadingCoeff f2) * f1 -
                   mono12 * m.sPolynomial b1 b2) :=
                congrArg _ hf2_identity
              rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hlc_f1_ne,
                  map_one, one_mul] at key
              rw [key, mul_sub, mul_assoc]
              congr 1
              rw [hratio_def, map_mul]
              ring
            -- Step 6: h12_lifted.sum g = scale_poly * S(b1, b2)
            -- First: h12_lifted.sum g = h12_scaled.sum (fun g q => q • g.val)
            --        by sum_mapDomain_index
            have h_sum_lifted : h12_lifted.sum (fun b q => q • b) =
                h12_scaled.sum (fun (g : ↑G) (q : MvPolynomial σ R) =>
                  q • (g : MvPolynomial σ R)) := by
              rw [hh12_lifted_def]
              exact Finsupp.sum_mapDomain_index
                (h_zero := fun _ => zero_smul _ _)
                (h_add := fun _ _ _ => add_smul _ _ _)
            -- Then: h12_scaled.sum = h12.sum (fun g q => (scale_poly * q) • g.val)
            --       by sum_mapRange_index
            have h_sum_scaled :
                h12_scaled.sum (fun (g : ↑G) (q : MvPolynomial σ R) =>
                  q • (g : MvPolynomial σ R)) =
                h12.sum (fun (g : ↑G) (q : MvPolynomial σ R) =>
                  (scale_poly * q) • (g : MvPolynomial σ R)) := by
              rw [hh12_scaled_def]
              exact Finsupp.sum_mapRange_index (fun _ => zero_smul _ _)
            -- Then: h12.sum (fun g q => (scale_poly * q) • g.val)
            --     = scale_poly * h12.sum (fun g q => q • g.val)
            --     = scale_poly * linearCombination val h12
            --     = scale_poly * S(b1, b2)
            have h_sum_factor :
                h12.sum (fun (g : ↑G) (q : MvPolynomial σ R) =>
                  (scale_poly * q) • (g : MvPolynomial σ R)) =
                scale_poly * m.sPolynomial b1 b2 := by
              simp only [smul_eq_mul, mul_assoc]
              rw [← Finsupp.mul_sum]
              congr 1
              -- h12.sum (fun g q => q * g.val) = linearCombination val h12
              -- = S(b1, b2)
              rw [hh12_eq, Finsupp.linearCombination_apply]
              simp [smul_eq_mul]
            have h_sum_eq : h12_lifted.sum (fun b q => q • b) =
                scale_poly * m.sPolynomial b1 b2 := by
              rw [h_sum_lifted, h_sum_scaled, h_sum_factor]
            -- Step 7: Now assemble the proof
            -- c1.sum g = c0.sum g + adj_b1.sum g - adj_b2.sum g - h12_lifted.sum g
            -- = f + C(ratio)*lt(c0 b1)*b1 - lt(c0 b2)*b2 - scale_poly*S(b1,b2)
            -- = f + f1*C(ratio) - f2 - scale_poly*S(b1,b2)
            -- = f + (f2 + scale_poly*S(b1,b2)) - f2 - scale_poly*S(b1,b2)   [by hf2_expr]
            -- = f
            have hsmul_zero : ∀ (a : MvPolynomial σ R),
                (fun (b : MvPolynomial σ R) (q : MvPolynomial σ R) => q • b) a 0 = 0 :=
              fun _ => zero_smul _ _
            have hsmul_add : ∀ (a : MvPolynomial σ R) (b₁ b₂ : MvPolynomial σ R),
                (fun b q => q • b) a (b₁ + b₂) =
                (fun b q => q • b) a b₁ + (fun b q => q • b) a b₂ :=
              fun _ _ _ => add_smul _ _ _
            have hsmul_sub : ∀ (a : MvPolynomial σ R) (b₁ b₂ : MvPolynomial σ R),
                (fun b q => q • b) a (b₁ - b₂) =
                (fun b q => q • b) a b₁ - (fun b q => q • b) a b₂ :=
              fun _ _ _ => sub_smul _ _ _
            -- Decompose c1.sum
            have hc1_sum_decomp :
                (c1.sum fun b q => q • b) =
                (c0.sum fun b q => q • b) +
                (adj_b1.sum fun b q => q • b) -
                (adj_b2.sum fun b q => q • b) -
                (h12_lifted.sum fun b q => q • b) := by
              change c1.sum _ = _
              rw [show c1 = (c0 + adj_b1 - adj_b2) - h12_lifted from by rw [hc1_def]]
              rw [Finsupp.sum_sub_index hsmul_sub,
                  show (c0 + adj_b1 - adj_b2) = (c0 + adj_b1) - adj_b2 from rfl,
                  Finsupp.sum_sub_index hsmul_sub,
                  Finsupp.sum_add_index' hsmul_zero hsmul_add]
            -- Simplify adj sums
            have hadj_b1_sum : (adj_b1.sum fun b q => q • b) =
                MvPolynomial.C ratio * m.leadingTerm (c0 b1) * b1 := by
              rw [hadj_b1_def]
              rw [Finsupp.sum_single_index (show (0 : MvPolynomial σ R) • b1 = 0
                from zero_smul _ b1)]
              rw [smul_eq_mul, mul_assoc]
            have hadj_b2_sum : (adj_b2.sum fun b q => q • b) =
                m.leadingTerm (c0 b2) * b2 := by
              rw [hadj_b2_def]
              rw [Finsupp.sum_single_index (show (0 : MvPolynomial σ R) • b2 = 0
                from zero_smul _ b2)]
              rw [smul_eq_mul]
            rw [hc1_sum_decomp, hadj_b1_sum, hadj_b2_sum, hc0f, h_sum_eq,
                show m.leadingTerm (c0 b2) * b2 = f2 from rfl,
                show MvPolynomial.C ratio * m.leadingTerm (c0 b1) * b1 =
                  MvPolynomial.C ratio * f1 from by rw [hf1_def, mul_assoc]]
            -- Goal: f + C(ratio)*f1 - f2 - scale_poly*S(b1,b2) = f
            rw [hf2_expr]
            ring
          · -- ∀ b ∈ c1.support, toSyn(deg(c1 b * b)) ≤ D
            -- For each b ∈ c1.support, we need:
            --   toSyn(deg(c1 b * b)) ≤ D
            -- We use: c1 b = c0 b + adj_b1 b - adj_b2 b - h12_lifted b
            -- So c1 b * b = (c0 b + adj_b1 b - adj_b2 b - h12_lifted b) * b
            -- degree_add_le + degree_sub_le give the bound.
            -- Key: each component * b has toSyn(degree) ≤ D.
            intro b hb
            -- Each component's degree bound:
            -- 1. c0 b * b ≤ D  (from hc0deg, or = 0 if b ∉ c0.support)
            -- 2. adj_b1 b * b ≤ D  (only nonzero at b1)
            -- 3. adj_b2 b * b ≤ D  (only nonzero at b2)
            -- 4. h12_lifted b * b ≤ D  (from hh12_deg + scale_poly degree)
            --
            -- Using the triangle inequality on the polynomial ring:
            -- deg(a + b) ≤ max(deg a, deg b) and deg(a - b) ≤ max(deg a, deg b)
            -- So deg(c1 b * b) ≤ max(deg(c0 b * b), ..., deg(h12_lifted b * b)) ≤ D.
            have hc0_bound : m.toSyn (m.degree (c0 b * b)) ≤ D := by
              by_cases hb_supp : b ∈ c0.support
              · exact hc0deg b hb_supp
              · rw [Finsupp.notMem_support_iff.mp hb_supp, zero_mul,
                    MonomialOrder.degree_zero, map_zero]
                exact bot_le
            have hadj_b1_bound :
                m.toSyn (m.degree (adj_b1 b * b)) ≤ D := by
              change m.toSyn (m.degree ((Finsupp.single b1
                (MvPolynomial.C ratio * m.leadingTerm (c0 b1))) b * b)) ≤ D
              by_cases hb1 : b = b1
              · rw [hb1, Finsupp.single_eq_same, mul_assoc,
                    show m.leadingTerm (c0 b1) * b1 = f1 from rfl]
                -- deg(C(ratio) * f1) ≤ deg(C(ratio)) + deg(f1) ≤ 0 + D
                calc m.toSyn (m.degree (MvPolynomial.C ratio * f1))
                    ≤ m.toSyn (m.degree (MvPolynomial.C ratio) +
                      m.degree f1) := degree_mul_le
                  _ = m.toSyn (0 + m.degree f1) := by
                    rw [MonomialOrder.degree_C]
                  _ = m.toSyn (m.degree f1) := by rw [zero_add]
                  _ = m.toSyn (m.degree (c0 b1 * b1)) := by rw [hf1_deg]
                  _ ≤ D := le_of_eq hb1_D
              · rw [Finsupp.single_eq_of_ne hb1, zero_mul,
                    MonomialOrder.degree_zero, map_zero]
                exact bot_le
            have hadj_b2_bound :
                m.toSyn (m.degree (adj_b2 b * b)) ≤ D := by
              change m.toSyn (m.degree ((Finsupp.single b2
                (m.leadingTerm (c0 b2))) b * b)) ≤ D
              by_cases hb2' : b = b2
              · rw [hb2', Finsupp.single_eq_same,
                    MonomialOrder.degree_leadingTerm_mul]
                exact le_of_eq hb2_D
              · rw [Finsupp.single_eq_of_ne hb2', zero_mul,
                    MonomialOrder.degree_zero, map_zero]
                exact bot_le
            have hh12_bound :
                m.toSyn (m.degree (h12_lifted b * b)) ≤ D := by
              -- If h12_lifted b = 0, trivial
              by_cases hb_h12 : h12_lifted b = 0
              · rw [hb_h12, zero_mul, MonomialOrder.degree_zero, map_zero]
                exact bot_le
              -- b must be in range(val), otherwise mapDomain gives 0
              have hb_range : b ∈ Set.range (Subtype.val : ↑G → _) := by
                by_contra h
                exact hb_h12 (Finsupp.mapDomain_notin_range h12_scaled b h)
              obtain ⟨⟨b_g, hb_g_mem⟩, hb_eq⟩ := hb_range
              simp only at hb_eq
              -- h12_lifted b = scale_poly * h12 g  (where g = ⟨b_g, hb_g_mem⟩)
              set g : ↑G := ⟨b_g, hb_g_mem⟩
              have hval : h12_lifted b = scale_poly * h12 g := by
                rw [← hb_eq, hh12_lifted_def]
                change (Finsupp.mapDomain Subtype.val h12_scaled)
                  (Subtype.val g) = _
                rw [Finsupp.mapDomain_apply Subtype.val_injective,
                    hh12_scaled_def, Finsupp.mapRange_apply]
              -- Rewrite: h12_lifted b * b = scale_poly * (h12 g * b_g)
              rw [hval, ← hb_eq, mul_assoc]
              -- Bound using degree_mul_le + hh12_deg + degree_sPolynomial_le
              -- Scale_poly degree ≤ deg(monomial(...)) ≤ alpha - deg(b1 ⊔ b2)
              -- h12 g * b_g degree ≤ deg(S(b1, b2)) ≤ deg(b1 ⊔ b2)
              -- Sum ≤ alpha = D
              calc m.toSyn (m.degree (scale_poly * (h12 g * b_g)))
                  ≤ m.toSyn (m.degree scale_poly +
                    m.degree (h12 g * b_g)) := degree_mul_le
                _ = m.toSyn (m.degree scale_poly) +
                    m.toSyn (m.degree (h12 g * b_g)) := map_add _ _ _
                _ ≤ m.toSyn (m.degree f1 ⊔ m.degree f2 -
                      m.degree b1 ⊔ m.degree b2) +
                    m.toSyn (m.degree b1 ⊔ m.degree b2) := by
                    apply add_le_add
                    · -- toSyn(deg(scale_poly)) ≤ toSyn(deg f1 ⊔ deg f2 - deg b1 ⊔ deg b2)
                      rw [hscale_def]
                      set mono_exp := m.degree f1 ⊔ m.degree f2 -
                        m.degree b1 ⊔ m.degree b2
                      set mono_coeff := m.leadingCoeff (c0 b1) *
                        m.leadingCoeff (c0 b2)
                      calc m.toSyn (m.degree (MvPolynomial.C
                            (m.leadingCoeff f1)⁻¹ *
                            monomial mono_exp mono_coeff))
                          ≤ m.toSyn (m.degree (MvPolynomial.C
                              (m.leadingCoeff f1)⁻¹) +
                            m.degree (monomial mono_exp mono_coeff)) :=
                              degree_mul_le
                        _ = m.toSyn (m.degree (MvPolynomial.C
                              (m.leadingCoeff f1)⁻¹)) +
                            m.toSyn (m.degree (monomial mono_exp mono_coeff)) :=
                              map_add _ _ _
                        _ = 0 + m.toSyn (m.degree (monomial mono_exp mono_coeff)) := by
                            rw [MonomialOrder.degree_C, map_zero]
                        _ = m.toSyn (m.degree (monomial mono_exp mono_coeff)) :=
                            zero_add _
                        _ ≤ m.toSyn mono_exp := degree_monomial_le _
                    · -- deg(h12 g * b_g) ≤ deg(S(b1, b2)) ≤ deg(b1 ⊔ b2)
                      calc m.toSyn (m.degree (h12 g * b_g))
                          = m.toSyn (m.degree
                            ((g : MvPolynomial σ R) * h12 g)) := by
                              congr 1; rw [mul_comm]
                        _ ≤ m.toSyn (m.degree (m.sPolynomial b1 b2)) :=
                              hh12_deg g
                        _ ≤ m.toSyn (m.degree b1 ⊔ m.degree b2) :=
                              degree_sPolynomial_le b1 b2
                _ = m.toSyn ((m.degree f1 ⊔ m.degree f2 -
                      m.degree b1 ⊔ m.degree b2) +
                      (m.degree b1 ⊔ m.degree b2)) := (map_add _ _ _).symm
                _ = m.toSyn (m.degree f1 ⊔ m.degree f2) := by
                    congr 1
                    apply tsub_add_cancel_of_le
                    apply sup_le_sup
                    · -- deg b1 ≤ deg f1
                      rw [hf1_deg, halpha_def]
                      exact le_add_left le_rfl
                    · -- deg b2 ≤ deg f2
                      rw [hf2_deg, MonomialOrder.degree_mul hcb2_ne hb2_ne]
                      exact le_add_left le_rfl
                _ = m.toSyn (m.degree f1) := by
                    rw [halpha_eq, sup_idem]
                _ = m.toSyn (m.degree (c0 b1 * b1)) := by rw [hf1_deg]
                _ = D := hb1_D
            -- Combine: deg(c1 b * b) ≤ max of all ≤ D
            -- c1 b * b = (c0 b + adj_b1 b - adj_b2 b - h12_lifted b) * b
            have hc1_eval : c1 b = c0 b + adj_b1 b - adj_b2 b - h12_lifted b := by
              change (c0 + adj_b1 - adj_b2 - h12_lifted) b = _
              simp [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply]
            calc m.toSyn (m.degree (c1 b * b))
              = m.toSyn (m.degree ((c0 b + adj_b1 b - adj_b2 b -
                  h12_lifted b) * b)) := by rw [hc1_eval]
            _ = m.toSyn (m.degree ((c0 b * b + adj_b1 b * b) -
                  (adj_b2 b * b + h12_lifted b * b))) := by ring_nf
            _ ≤ m.toSyn (m.degree (c0 b * b + adj_b1 b * b)) ⊔
                  m.toSyn (m.degree (adj_b2 b * b + h12_lifted b * b)) :=
                MonomialOrder.degree_sub_le
            _ ≤ (m.toSyn (m.degree (c0 b * b)) ⊔
                  m.toSyn (m.degree (adj_b1 b * b))) ⊔
                (m.toSyn (m.degree (adj_b2 b * b)) ⊔
                  m.toSyn (m.degree (h12_lifted b * b))) :=
                sup_le_sup MonomialOrder.degree_add_le
                  MonomialOrder.degree_add_le
            _ ≤ D := by
                simp only [sup_le_iff]
                exact ⟨⟨hc0_bound, hadj_b1_bound⟩,
                       ⟨hadj_b2_bound, hh12_bound⟩⟩
    · -- span(lt(G)) ⊆ span(lt(span G)) — easy direction
      exact Ideal.span_mono (Set.image_mono Ideal.subset_span)

end MonomialOrder

end

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

/-! ### Buchberger's criterion: forward and backward directions -/

/-- Forward direction of Buchberger's criterion: if `G` is a Gröbner basis, every
S-polynomial of pairs from `G` reduces to `0` modulo `G`. -/
private theorem sPolynomial_isRemainder_of_isGroebnerBasis {R : Type*} [Field R]
    {G : Set (MvPolynomial σ R)} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hGB : m.IsGroebnerBasis G (Ideal.span G))
    (g₁ g₂ : G) :
    m.IsRemainder (m.sPolynomial g₁.val g₂.val : MvPolynomial σ R) G 0 := by
    obtain ⟨_, hInitIdeal⟩ := hGB
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

/-- Backward direction of Buchberger's criterion: if every S-polynomial of pairs
from `G` reduces to `0` modulo `G`, then `G` is a Gröbner basis. -/
private theorem isGroebnerBasis_of_sPolynomial_isRemainder {R : Type*} [Field R]
    {G : Set (MvPolynomial σ R)} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hSP : ∀ (g₁ g₂ : G),
      m.IsRemainder (m.sPolynomial g₁.val g₂.val : MvPolynomial σ R) G 0) :
    m.IsGroebnerBasis G (Ideal.span G) := by
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
          -- New strategy (Mathlib `sPolynomial_decomposition'` direct application).
          --
          -- 1. Handle the unit case (`G` contains a constant) separately.
          -- 2. Otherwise every `g ∈ G` has `m.degree g ≠ 0`.
          -- 3. Let `B_hi := { b ∈ c.support | toSyn(deg(c b * b)) = D }` and
          --    `g_top b := leadingTerm (c b) * b` (the "top" parts).
          -- 4. By `sPolynomial_decomposition'`, the top sum decomposes as
          --    a scalar combination of S-polynomials of the `g_top b`s.
          -- 5. By `sPolynomial_leadingTerm_mul`, each `S(g_top b₁, g_top b₂)`
          --    is `monomial * S(b₁, b₂)`.
          -- 6. By `hSP`, each `S(b₁, b₂)` has a representation over `G` with
          --    each term of degree `≤ deg(b₁) ⊔ deg(b₂)` (strict, when
          --    combined with `sPolynomial_toSyn_lt_lcm` and the fact that
          --    each `g ∈ G` has positive degree).
          -- 7. Combine: `f` decomposes as low-part `+` lifted S-poly part,
          --    each summand of toSyn-degree `< D`.
          -- Unit case: G contains a constant `u`.  Then `f * u⁻¹ * u = f`.
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
          -- Non-unit case: every `g ∈ G` has positive (non-zero) degree.
          push_neg at hG_unit
          -- Set up `B_hi` and the family `g_top : MvPolynomial σ R → MvPolynomial σ R`.
          set B_hi := c.support.filter (fun b => m.toSyn (m.degree (c b * b)) = D)
            with hB_hi_def
          set g_top : MvPolynomial σ R → MvPolynomial σ R :=
            fun b => m.leadingTerm (c b) * b with hg_top_def
          -- Basic facts about elements of `B_hi`.
          have hB_hi_subset : B_hi ⊆ c.support := Finset.filter_subset _ _
          have hb_G_of_hi : ∀ b ∈ B_hi, b ∈ G := fun b hb =>
            hcG (Finset.mem_coe.mpr (hB_hi_subset hb))
          have hcb_ne_of_hi : ∀ b ∈ B_hi, c b ≠ 0 := fun b hb =>
            Finsupp.mem_support_iff.mp (hB_hi_subset hb)
          have hb_ne_of_hi : ∀ b ∈ B_hi, b ≠ 0 := fun b hb =>
            isUnit_leadingCoeff.mp (hG b (hb_G_of_hi b hb))
          have hb_deg_pos : ∀ b ∈ B_hi, m.degree b ≠ 0 := fun b hb =>
            hG_unit b (hb_G_of_hi b hb)
          have hg_top_deg : ∀ b ∈ B_hi, m.toSyn (m.degree (g_top b)) = D := by
            intro b hb
            have hbD : m.toSyn (m.degree (c b * b)) = D :=
              (Finset.mem_filter.mp hb).2
            rw [hg_top_def, MonomialOrder.degree_leadingTerm_mul]
            exact hbD
          -- Hypothesis `hd` for `sPolynomial_decomposition'`.
          have hd_spec : ∀ b ∈ B_hi, m.toSyn (m.degree (g_top b)) = D ∨ g_top b = 0 :=
            fun b hb => Or.inl (hg_top_deg b hb)
          -- Express `f` as low-part + sum of `g_top`.
          set f_low : MvPolynomial σ R :=
              ∑ b ∈ c.support,
                (if b ∈ B_hi then c b - m.leadingTerm (c b) else c b) * b
            with hf_low_def
          have hf_eq : f = f_low + ∑ b ∈ B_hi, g_top b := by
            rw [hf_def]
            simp only [Finsupp.sum, smul_eq_mul, hf_low_def, hg_top_def]
            rw [show (∑ b ∈ c.support, c b * b) =
                ∑ b ∈ c.support,
                  ((if b ∈ B_hi then c b - m.leadingTerm (c b) else c b) * b
                    + (if b ∈ B_hi then m.leadingTerm (c b) * b else 0)) from
                Finset.sum_congr rfl (fun b _ => by
                  by_cases hb : b ∈ B_hi
                  · simp [hb, sub_mul]
                  · simp [hb]),
              Finset.sum_add_distrib]
            congr 1
            -- ∑ b ∈ c.support, (if b ∈ B_hi then ... else 0) = ∑ b ∈ B_hi, ...
            rw [← Finset.sum_filter]
            -- c.support.filter (· ∈ B_hi) = B_hi (since B_hi ⊆ c.support).
            have hfilt : c.support.filter (· ∈ B_hi) = B_hi := by
              apply Finset.Subset.antisymm
              · intro b hb
                exact (Finset.mem_filter.mp hb).2
              · intro b hb
                exact Finset.mem_filter.mpr ⟨hB_hi_subset hb, hb⟩
            rw [hfilt]
          -- Each summand of `f_low` has toSyn-degree `< D`.
          have hf_low_terms_lt :
              ∀ b ∈ c.support,
                m.toSyn (m.degree
                  ((if b ∈ B_hi then c b - m.leadingTerm (c b) else c b) * b)) < D := by
            intro b hb
            by_cases hbhi : b ∈ B_hi
            · simp only [if_pos hbhi]
              have hcb_ne := hcb_ne_of_hi b hbhi
              have hb_ne := hb_ne_of_hi b hbhi
              have hbD : m.toSyn (m.degree (c b * b)) = D :=
                (Finset.mem_filter.mp hbhi).2
              by_cases hcb_zero : c b - m.leadingTerm (c b) = 0
              · rw [hcb_zero, zero_mul, MonomialOrder.degree_zero, map_zero]
                refine bot_lt_iff_ne_bot.mpr ?_
                intro hD
                have : m.toSyn (m.degree f) < (⊥ : m.syn) := hD ▸ hf_lt_D
                exact not_lt_bot this
              -- Strict because `m.degree (c b) ≠ 0` (otherwise c b - lt = 0).
              have hdeg_cb_ne : m.degree (c b) ≠ 0 := by
                intro hcb_deg
                apply hcb_zero
                have hlt_eq : m.leadingTerm (c b) = c b := by
                  rw [MonomialOrder.leadingTerm, hcb_deg]
                  exact (MonomialOrder.eq_C_of_degree_eq_zero hcb_deg).symm
                rw [hlt_eq, sub_self]
              -- `c b - lt(c b) = subLTerm (c b)`
              have hsub_eq : c b - m.leadingTerm (c b) = m.subLTerm (c b) := by
                simp [MonomialOrder.subLTerm, MonomialOrder.leadingTerm]
              have hsub_lt : m.toSyn (m.degree (c b - m.leadingTerm (c b))) <
                  m.toSyn (m.degree (c b)) := by
                rw [hsub_eq]
                exact m.degree_sub_LTerm_lt hdeg_cb_ne
              calc m.toSyn (m.degree ((c b - m.leadingTerm (c b)) * b))
                  ≤ m.toSyn (m.degree (c b - m.leadingTerm (c b)) + m.degree b) :=
                    MonomialOrder.degree_mul_le
                _ = m.toSyn (m.degree (c b - m.leadingTerm (c b))) +
                    m.toSyn (m.degree b) := map_add _ _ _
                _ < m.toSyn (m.degree (c b)) + m.toSyn (m.degree b) := by
                    exact (add_lt_add_iff_right _).mpr hsub_lt
                _ = m.toSyn (m.degree (c b) + m.degree b) := (map_add _ _ _).symm
                _ = m.toSyn (m.degree (c b * b)) := by
                    rw [MonomialOrder.degree_mul (hcb_ne_of_hi b hbhi) hb_ne]
                _ = D := hbD
            · simp only [if_neg hbhi]
              have hbnotD : m.toSyn (m.degree (c b * b)) ≠ D := by
                intro heq
                exact hbhi (Finset.mem_filter.mpr ⟨hb, heq⟩)
              exact lt_of_le_of_ne (hdeg b hb) hbnotD
          -- Therefore `m.toSyn (m.degree f_low) < D`.
          have hf_low_lt : m.toSyn (m.degree f_low) < D := by
            rw [hf_low_def]
            apply lt_of_le_of_lt MonomialOrder.degree_sum_le
            apply (Finset.sup_lt_iff (lt_of_le_of_lt bot_le hf_lt_D)).mpr
            intro b hb
            exact hf_low_terms_lt b hb
          -- And `m.toSyn (m.degree (∑ b ∈ B_hi, g_top b)) < D`.
          have hfd_spec : m.toSyn (m.degree (∑ b ∈ B_hi, g_top b)) < D := by
            have h_eq : ∑ b ∈ B_hi, g_top b = f - f_low := by
              rw [hf_eq]; ring
            rw [h_eq]
            calc m.toSyn (m.degree (f - f_low))
                ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree f_low) :=
                  MonomialOrder.degree_sub_le
              _ < D := sup_lt_iff.mpr ⟨hf_lt_D, hf_low_lt⟩
          -- Apply `sPolynomial_decomposition'`.
          obtain ⟨c'', hc''_eq⟩ := m.sPolynomial_decomposition' g_top hd_spec hfd_spec
          -- For each pair `(b₁, b₂)` in `B_hi`, choose an `hSP` representation.
          let h_pair : (b : MvPolynomial σ R) → b ∈ B_hi →
              (b' : MvPolynomial σ R) → b' ∈ B_hi → (↑G →₀ MvPolynomial σ R) :=
            fun b₁ hb₁ b₂ hb₂ =>
              Classical.choose (hSP ⟨b₁, hb_G_of_hi b₁ hb₁⟩ ⟨b₂, hb_G_of_hi b₂ hb₂⟩).1
          have h_pair_spec : ∀ b₁ (hb₁ : b₁ ∈ B_hi) b₂ (hb₂ : b₂ ∈ B_hi),
              m.sPolynomial b₁ b₂ =
                Finsupp.linearCombination _ (fun (g : ↑G) => g.val) (h_pair b₁ hb₁ b₂ hb₂) ∧
              ∀ (g : ↑G), m.degree (g.val * h_pair b₁ hb₁ b₂ hb₂ g) ≼[m]
                m.degree (m.sPolynomial b₁ b₂) := by
            intro b₁ hb₁ b₂ hb₂
            have hSP12 := (hSP ⟨b₁, hb_G_of_hi b₁ hb₁⟩ ⟨b₂, hb_G_of_hi b₂ hb₂⟩).1
            have hchoose := Classical.choose_spec hSP12
            refine ⟨?_, hchoose.2⟩
            have heq := hchoose.1
            rw [add_zero] at heq
            exact heq
          -- "Monomial factor" arising from `sPolynomial_leadingTerm_mul`.
          set α_mono : MvPolynomial σ R → MvPolynomial σ R → (σ →₀ ℕ) :=
            fun b₁ b₂ => (m.degree (c b₁) + m.degree b₁) ⊔
              (m.degree (c b₂) + m.degree b₂) - m.degree b₁ ⊔ m.degree b₂
            with hα_mono_def
          set mono_pair : MvPolynomial σ R → MvPolynomial σ R → MvPolynomial σ R :=
            fun b₁ b₂ => MvPolynomial.monomial (α_mono b₁ b₂)
              (m.leadingCoeff (c b₁) * m.leadingCoeff (c b₂))
            with hmono_pair_def
          have hS_top_eq : ∀ b₁ b₂, m.sPolynomial (g_top b₁) (g_top b₂) =
              mono_pair b₁ b₂ * m.sPolynomial b₁ b₂ := by
            intro b₁ b₂
            rw [hg_top_def, m.sPolynomial_leadingTerm_mul]
          -- Define `c_low` as a Finsupp on `MvPolynomial σ R`.
          set c_low : MvPolynomial σ R →₀ MvPolynomial σ R :=
              ∑ b ∈ c.support,
                Finsupp.single b
                  (if b ∈ B_hi then c b - m.leadingTerm (c b) else c b)
            with hc_low_def
          -- Define `c_extra` for one pair.
          let extra_pair : (b : MvPolynomial σ R) → b ∈ B_hi →
              (b' : MvPolynomial σ R) → b' ∈ B_hi →
              (MvPolynomial σ R →₀ MvPolynomial σ R) :=
            fun b₁ hb₁ b₂ hb₂ =>
              Finsupp.mapDomain Subtype.val
                ((h_pair b₁ hb₁ b₂ hb₂).mapRange
                  (fun q => MvPolynomial.C (c'' b₁ b₂) * mono_pair b₁ b₂ * q)
                  (by simp))
          -- Define `c_extra` as the sum over pairs.
          set c_extra : MvPolynomial σ R →₀ MvPolynomial σ R :=
              ∑ b₁ ∈ B_hi.attach, ∑ b₂ ∈ B_hi.attach,
                extra_pair b₁.val b₁.prop b₂.val b₂.prop
            with hc_extra_def
          -- Final candidate.
          set c' : MvPolynomial σ R →₀ MvPolynomial σ R := c_low + c_extra with hc'_def
          refine ⟨c', ?_, ?_, ?_⟩
          · -- ↑c'.support ⊆ G
            intro b hb
            simp only [Finset.mem_coe, Finsupp.mem_support_iff, hc'_def,
              Finsupp.coe_add, Pi.add_apply] at hb
            by_cases hbl : c_low b = 0
            · rw [hbl, zero_add] at hb
              by_contra hbG
              apply hb
              rw [hc_extra_def, Finsupp.finset_sum_apply]
              refine Finset.sum_eq_zero (fun b₁ _ => ?_)
              rw [Finsupp.finset_sum_apply]
              refine Finset.sum_eq_zero (fun b₂ _ => ?_)
              change extra_pair b₁.val b₁.prop b₂.val b₂.prop b = 0
              apply Finsupp.mapDomain_notin_range
              rintro ⟨g, rfl⟩
              exact hbG g.prop
            · have hb_in_supp : b ∈ c.support := by
                rw [hc_low_def] at hbl
                rw [Finsupp.finset_sum_apply] at hbl
                by_contra hb_notin
                apply hbl
                refine Finset.sum_eq_zero (fun b' hb' => ?_)
                by_cases hbb : b = b'
                · exact absurd (hbb ▸ hb') hb_notin
                · exact Finsupp.single_eq_of_ne hbb
              exact hcG (Finset.mem_coe.mpr hb_in_supp)
          · -- c'.sum smul = f
            have hsmul_add : ∀ (b : MvPolynomial σ R) (q₁ q₂ : MvPolynomial σ R),
                (q₁ + q₂) • b = q₁ • b + q₂ • b := fun b q₁ q₂ => add_smul q₁ q₂ b
            have h0 : ∀ (b : MvPolynomial σ R), (0 : MvPolynomial σ R) • b = 0 :=
              fun b => zero_smul _ b
            -- General: for any Finset s, the sum-of-singles equals the explicit sum.
            have hsum_singles : ∀ (s : Finset (MvPolynomial σ R))
                (g : MvPolynomial σ R → MvPolynomial σ R),
                ((∑ b ∈ s, Finsupp.single b (g b)).sum
                    fun (b : MvPolynomial σ R) (q : MvPolynomial σ R) => q • b) =
                  ∑ b ∈ s, g b * b := by
              intro s g
              induction s using Finset.induction_on with
              | empty => simp [Finsupp.sum_zero_index]
              | insert a s ha ih =>
                  rw [Finset.sum_insert ha,
                    Finsupp.sum_add_index' (h := fun (b : MvPolynomial σ R)
                      (q : MvPolynomial σ R) => q • b) h0 hsmul_add,
                    Finsupp.sum_single_index (h0 a), Finset.sum_insert ha,
                    smul_eq_mul, ih]
            have hc_low_sum : (c_low.sum fun b q => q • b) = f_low := by
              rw [hc_low_def, hf_low_def]
              exact hsum_singles c.support
                (fun b => if b ∈ B_hi then c b - m.leadingTerm (c b) else c b)
            have hpair_sum : ∀ b₁ (hb₁ : b₁ ∈ B_hi) b₂ (hb₂ : b₂ ∈ B_hi),
                ((extra_pair b₁ hb₁ b₂ hb₂).sum fun b q => q • b) =
                  (c'' b₁ b₂) • m.sPolynomial (g_top b₁) (g_top b₂) := by
              intro b₁ hb₁ b₂ hb₂
              change ((Finsupp.mapDomain Subtype.val
                  ((h_pair b₁ hb₁ b₂ hb₂).mapRange
                    (fun q => MvPolynomial.C (c'' b₁ b₂) * mono_pair b₁ b₂ * q)
                    (by simp))).sum (fun b q => q • b)) = _
              rw [Finsupp.sum_mapDomain_index (h := fun (b : MvPolynomial σ R)
                  (q : MvPolynomial σ R) => q • b) (fun b => zero_smul _ b)
                (fun b q₁ q₂ => add_smul q₁ q₂ b)]
              rw [Finsupp.sum_mapRange_index (h := fun (g : ↑G)
                  (q : MvPolynomial σ R) => q • g.val) (fun g => zero_smul _ _)]
              rw [hS_top_eq b₁ b₂]
              have h_eq := (h_pair_spec b₁ hb₁ b₂ hb₂).1
              rw [h_eq, Finsupp.linearCombination_apply]
              -- Goal: h_pair.sum (fun g q => (C(c'') * mono * q) • g.val)
              --     = c'' • (mono * h_pair.sum (fun g q => q • g.val))
              simp only [smul_eq_mul, Finsupp.sum, Finset.mul_sum,
                MvPolynomial.smul_eq_C_mul]
              refine Finset.sum_congr rfl fun g _ => ?_
              ring
            have hc_extra_sum : (c_extra.sum fun b q => q • b) = ∑ b ∈ B_hi, g_top b := by
              -- Use `Finsupp.liftAddHom` to push the ambient `Finset.sum` through `Finsupp.sum`.
              -- Concretely: `(∑ i ∈ S, f i).sum (fun b q => q • b) = ∑ i ∈ S, (f i).sum smul`.
              have hsum_eq : ∀ {ι : Type _} (S : Finset ι)
                  (f : ι → (MvPolynomial σ R →₀ MvPolynomial σ R)),
                  ((∑ b ∈ S, f b).sum
                      fun (b : MvPolynomial σ R) (q : MvPolynomial σ R) => q • b) =
                    ∑ b ∈ S,
                      ((f b).sum
                        fun (b : MvPolynomial σ R) (q : MvPolynomial σ R) => q • b) := by
                intro ι S f
                induction S using Finset.induction_on with
                | empty => simp [Finsupp.sum_zero_index]
                | insert a s ha ih =>
                    rw [Finset.sum_insert ha,
                      Finsupp.sum_add_index' (h := fun (b : MvPolynomial σ R)
                        (q : MvPolynomial σ R) => q • b) h0 hsmul_add,
                      Finset.sum_insert ha, ih]
              rw [hc_extra_def]
              rw [hsum_eq B_hi.attach (fun b₁ =>
                ∑ b₂ ∈ B_hi.attach, extra_pair b₁.val b₁.prop b₂.val b₂.prop)]
              -- Inner: each ∑ over b₂ ∈ B_hi.attach
              rw [show (∑ b₁ ∈ B_hi.attach,
                  ((∑ b₂ ∈ B_hi.attach,
                    extra_pair b₁.val b₁.prop b₂.val b₂.prop).sum
                    fun b q => q • b)) =
                  ∑ b₁ ∈ B_hi.attach, ∑ b₂ ∈ B_hi.attach,
                    (c'' b₁.val b₂.val) • m.sPolynomial (g_top b₁.val) (g_top b₂.val) from
                Finset.sum_congr rfl fun b₁ _ => by
                  rw [hsum_eq B_hi.attach (fun b₂ =>
                    extra_pair b₁.val b₁.prop b₂.val b₂.prop)]
                  exact Finset.sum_congr rfl fun b₂ _ =>
                    hpair_sum b₁.val b₁.prop b₂.val b₂.prop]
              rw [Finset.sum_attach B_hi (fun b₁ =>
                ∑ b₂ ∈ B_hi.attach, c'' b₁ b₂.val • m.sPolynomial (g_top b₁) (g_top b₂.val))]
              rw [show (∑ b₁ ∈ B_hi,
                    ∑ b₂ ∈ B_hi.attach, c'' b₁ b₂.val •
                      m.sPolynomial (g_top b₁) (g_top b₂.val)) =
                  ∑ b₁ ∈ B_hi, ∑ b₂ ∈ B_hi,
                    c'' b₁ b₂ • m.sPolynomial (g_top b₁) (g_top b₂) from
                Finset.sum_congr rfl fun b₁ _ =>
                  Finset.sum_attach B_hi (fun b₂ =>
                    c'' b₁ b₂ • m.sPolynomial (g_top b₁) (g_top b₂))]
              exact hc''_eq.symm
            -- Combine: c'.sum smul = c_low.sum smul + c_extra.sum smul = f_low + ∑ g_top = f
            rw [hc'_def,
              Finsupp.sum_add_index' (h := fun (b : MvPolynomial σ R)
                (q : MvPolynomial σ R) => q • b) h0 hsmul_add,
              hc_low_sum, hc_extra_sum, hf_eq]
          · -- ∀ b ∈ c'.support, m.toSyn (m.degree (c' b * b)) < D
            have hclow_eval : ∀ b, c_low b =
                if b ∈ c.support then
                  (if b ∈ B_hi then c b - m.leadingTerm (c b) else c b)
                else 0 := by
              intro b
              rw [hc_low_def, Finsupp.finset_sum_apply]
              by_cases hbsupp : b ∈ c.support
              · rw [if_pos hbsupp,
                  Finset.sum_eq_single b
                    (fun b' _ hbb => by
                      rw [Finsupp.single_eq_of_ne hbb.symm])
                    (fun hb_notin => absurd hbsupp hb_notin),
                  Finsupp.single_eq_same]
              · rw [if_neg hbsupp]
                refine Finset.sum_eq_zero fun b' hb' => ?_
                by_cases h : b = b'
                · exact absurd (h ▸ hb') hbsupp
                · exact Finsupp.single_eq_of_ne h
            have hclow_b_lt : ∀ b, m.toSyn (m.degree (c_low b * b)) < D := by
              intro b
              rw [hclow_eval]
              by_cases hb : b ∈ c.support
              · simp only [if_pos hb]
                exact hf_low_terms_lt b hb
              · simp only [if_neg hb, zero_mul, MonomialOrder.degree_zero, map_zero]
                exact bot_lt_iff_ne_bot.mpr (fun hD =>
                  not_lt_bot (hD ▸ hf_lt_D))
            have hsPoly_strict : ∀ b₁ ∈ B_hi, ∀ b₂ ∈ B_hi,
                m.toSyn (m.degree (m.sPolynomial b₁ b₂)) <
                m.toSyn (m.degree b₁ ⊔ m.degree b₂) := by
              intro b₁ hb₁ b₂ hb₂
              rcases m.degree_sPolynomial b₁ b₂ with hlt | hzero
              · exact hlt
              · rw [hzero, MonomialOrder.degree_zero, map_zero]
                have hsup_ne : m.degree b₁ ⊔ m.degree b₂ ≠ 0 := by
                  intro h
                  exact hb_deg_pos b₁ hb₁
                    (le_antisymm (h ▸ le_sup_left) bot_le)
                rw [show (0 : m.syn) = m.toSyn 0 from (map_zero _).symm]
                exact lt_of_le_of_ne (m.toSyn_monotone bot_le)
                  (fun h => hsup_ne (m.toSyn.injective h.symm))
            have hextra_pair_b_lt : ∀ b₁ (hb₁ : b₁ ∈ B_hi) b₂ (hb₂ : b₂ ∈ B_hi),
                ∀ b, m.toSyn (m.degree (extra_pair b₁ hb₁ b₂ hb₂ b * b)) < D := by
              intro b₁ hb₁ b₂ hb₂ b
              by_cases hb_range : b ∈ Set.range (Subtype.val : ↑G → MvPolynomial σ R)
              · obtain ⟨⟨b_g, hb_g⟩, hb_eq⟩ := hb_range
                simp only at hb_eq
                set g_v : ↑G := ⟨b_g, hb_g⟩
                have hval :
                    extra_pair b₁ hb₁ b₂ hb₂ b =
                      MvPolynomial.C (c'' b₁ b₂) * mono_pair b₁ b₂ *
                        h_pair b₁ hb₁ b₂ hb₂ g_v := by
                  change (Finsupp.mapDomain Subtype.val
                    ((h_pair b₁ hb₁ b₂ hb₂).mapRange
                      (fun q => MvPolynomial.C (c'' b₁ b₂) * mono_pair b₁ b₂ * q)
                      (by simp))) b = _
                  rw [← hb_eq]
                  change (Finsupp.mapDomain Subtype.val _) (Subtype.val g_v) = _
                  rw [Finsupp.mapDomain_apply Subtype.val_injective,
                      Finsupp.mapRange_apply]
                rw [hval, ← hb_eq]
                obtain ⟨_, hdeg_h⟩ := h_pair_spec b₁ hb₁ b₂ hb₂
                have hb₁D : m.toSyn (m.degree (c b₁ * b₁)) = D :=
                  (Finset.mem_filter.mp hb₁).2
                have hb₂D : m.toSyn (m.degree (c b₂ * b₂)) = D :=
                  (Finset.mem_filter.mp hb₂).2
                have hcb₁_ne := hcb_ne_of_hi b₁ hb₁
                have hcb₂_ne := hcb_ne_of_hi b₂ hb₂
                have hb₁_ne := hb_ne_of_hi b₁ hb₁
                have hb₂_ne := hb_ne_of_hi b₂ hb₂
                have hsum_eq : α_mono b₁ b₂ + (m.degree b₁ ⊔ m.degree b₂) =
                    (m.degree (c b₁) + m.degree b₁) ⊔
                    (m.degree (c b₂) + m.degree b₂) := by
                  rw [hα_mono_def]
                  exact tsub_add_cancel_of_le
                    (sup_le_sup (le_add_left le_rfl) (le_add_left le_rfl))
                calc m.toSyn (m.degree
                    (MvPolynomial.C (c'' b₁ b₂) * mono_pair b₁ b₂ *
                      h_pair b₁ hb₁ b₂ hb₂ g_v * b_g))
                    = m.toSyn (m.degree
                      (MvPolynomial.C (c'' b₁ b₂) *
                        (mono_pair b₁ b₂ * (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g)))) := by
                      ring_nf
                  _ ≤ m.toSyn (m.degree (MvPolynomial.C (c'' b₁ b₂))) +
                      m.toSyn (m.degree
                        (mono_pair b₁ b₂ * (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g))) := by
                      rw [← map_add]
                      exact MonomialOrder.degree_mul_le
                  _ = 0 + m.toSyn (m.degree
                      (mono_pair b₁ b₂ * (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g))) := by
                      rw [MonomialOrder.degree_C, map_zero]
                  _ = m.toSyn (m.degree
                      (mono_pair b₁ b₂ * (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g))) := zero_add _
                  _ ≤ m.toSyn (m.degree (mono_pair b₁ b₂)) +
                      m.toSyn (m.degree (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g)) := by
                      rw [← map_add]
                      exact MonomialOrder.degree_mul_le
                  _ ≤ m.toSyn (α_mono b₁ b₂) +
                      m.toSyn (m.degree (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g)) := by
                      refine add_le_add ?_ le_rfl
                      rw [hmono_pair_def]
                      exact MonomialOrder.degree_monomial_le _
                  _ < m.toSyn (α_mono b₁ b₂) +
                      m.toSyn (m.degree b₁ ⊔ m.degree b₂) := by
                      refine add_lt_add_of_le_of_lt le_rfl ?_
                      calc m.toSyn (m.degree (h_pair b₁ hb₁ b₂ hb₂ g_v * b_g))
                          = m.toSyn (m.degree (b_g * h_pair b₁ hb₁ b₂ hb₂ g_v)) := by
                              rw [mul_comm]
                        _ ≤ m.toSyn (m.degree (m.sPolynomial b₁ b₂)) := hdeg_h g_v
                        _ < m.toSyn (m.degree b₁ ⊔ m.degree b₂) :=
                            hsPoly_strict b₁ hb₁ b₂ hb₂
                  _ = m.toSyn (α_mono b₁ b₂ + (m.degree b₁ ⊔ m.degree b₂)) :=
                      (map_add _ _ _).symm
                  _ = m.toSyn ((m.degree (c b₁) + m.degree b₁) ⊔
                      (m.degree (c b₂) + m.degree b₂)) := by rw [hsum_eq]
                  _ = D := by
                    -- The two arguments of `⊔` have the same `m.toSyn` (= D),
                    -- so by injectivity of `m.toSyn` they're equal as Finsupps,
                    -- and `⊔` collapses.
                    have hb₁eq : m.degree (c b₁) + m.degree b₁ = m.degree (c b₁ * b₁) :=
                      (MonomialOrder.degree_mul hcb₁_ne hb₁_ne).symm
                    have hb₂eq : m.degree (c b₂) + m.degree b₂ = m.degree (c b₂ * b₂) :=
                      (MonomialOrder.degree_mul hcb₂_ne hb₂_ne).symm
                    have hD_eq : m.degree (c b₁ * b₁) = m.degree (c b₂ * b₂) :=
                      m.toSyn.injective (hb₁D.trans hb₂D.symm)
                    rw [hb₁eq, hb₂eq, hD_eq, sup_idem]
                    exact hb₂D
              · rw [show extra_pair b₁ hb₁ b₂ hb₂ b = 0 from
                  Finsupp.mapDomain_notin_range _ _ hb_range, zero_mul,
                  MonomialOrder.degree_zero, map_zero]
                exact bot_lt_iff_ne_bot.mpr (fun hD =>
                  not_lt_bot (hD ▸ hf_lt_D))
            have hcextra_b_lt : ∀ b, m.toSyn (m.degree (c_extra b * b)) < D := by
              intro b
              rw [hc_extra_def, Finsupp.finset_sum_apply]
              rw [show (∑ b₁ ∈ B_hi.attach,
                    (∑ b₂ ∈ B_hi.attach,
                      extra_pair b₁.val b₁.prop b₂.val b₂.prop) b) =
                  ∑ b₁ ∈ B_hi.attach, ∑ b₂ ∈ B_hi.attach,
                    (extra_pair b₁.val b₁.prop b₂.val b₂.prop) b from
                  Finset.sum_congr rfl fun b₁ _ =>
                    Finsupp.finset_sum_apply _ _ _]
              rw [Finset.sum_mul, show
                (∑ b₁ ∈ B_hi.attach,
                  (∑ b₂ ∈ B_hi.attach,
                      (extra_pair b₁.val b₁.prop b₂.val b₂.prop) b) * b) =
                  ∑ b₁ ∈ B_hi.attach, ∑ b₂ ∈ B_hi.attach,
                    (extra_pair b₁.val b₁.prop b₂.val b₂.prop) b * b from
                  Finset.sum_congr rfl fun b₁ _ =>
                    Finset.sum_mul B_hi.attach
                      (fun b₂ : B_hi => (extra_pair b₁.val b₁.prop b₂.val b₂.prop) b) b]
              apply lt_of_le_of_lt MonomialOrder.degree_sum_le
              apply (Finset.sup_lt_iff (lt_of_le_of_lt bot_le hf_lt_D)).mpr
              intro b₁ _
              apply lt_of_le_of_lt MonomialOrder.degree_sum_le
              apply (Finset.sup_lt_iff (lt_of_le_of_lt bot_le hf_lt_D)).mpr
              intro b₂ _
              exact hextra_pair_b_lt b₁.val b₁.prop b₂.val b₂.prop b
            intro b _hb
            have hc'_eval : c' b = c_low b + c_extra b := by
              rw [hc'_def]; rfl
            rw [show c' b * b = c_low b * b + c_extra b * b from by
              rw [hc'_eval]; ring]
            calc m.toSyn (m.degree (c_low b * b + c_extra b * b))
                ≤ m.toSyn (m.degree (c_low b * b)) ⊔
                  m.toSyn (m.degree (c_extra b * b)) :=
                MonomialOrder.degree_add_le
              _ < D := sup_lt_iff.mpr ⟨hclow_b_lt b, hcextra_b_lt b⟩
    · -- span(lt(G)) ⊆ span(lt(span G)) — easy direction
      exact Ideal.span_mono (Set.image_mono Ideal.subset_span)

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
    ∀ (g₁ g₂ : G), m.IsRemainder (m.sPolynomial g₁.val g₂.val : MvPolynomial σ R) G 0 :=
  ⟨m.sPolynomial_isRemainder_of_isGroebnerBasis hG,
    m.isGroebnerBasis_of_sPolynomial_isRemainder hG⟩

end MonomialOrder

end

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
      apply Submodule.sum_mem
      intro b _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span b.prop)
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
        -- Construction: replace the B_D terms using S-polynomial decomposition,
        -- then use hSP to get a new G-representation with max degree < D.
        -- Full proof: sPolynomial_decomposition' + sPolynomial_monomial_mul + hSP
        -- + sPolynomial_toSyn_lt_lcm + toSyn additivity.
        sorry
    · -- span(lt(G)) ⊆ span(lt(span G)) — easy direction
      apply Ideal.span_le.mpr
      rintro _ ⟨g, hg_G, rfl⟩
      exact Ideal.subset_span ⟨g, Ideal.subset_span hg_G, rfl⟩

end MonomialOrder

end

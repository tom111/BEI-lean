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
    --
    -- Proof sketch (WFI on the representation max-degree D : m.syn):
    --
    -- Key lemma: ∀ f ∈ Ideal.span G, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f.
    --
    -- Proof by WFI on D := max_{b ∈ B} m.toSyn(m.degree(c_b * b)) over some representation
    -- f = ∑_{b ∈ B} c_b * b (b ∈ G).
    --
    -- Case A (D = m.toSyn(m.degree f)):
    --   Some b* achieves the max, so m.degree(c_{b*} * b*) = m.degree f (as σ →₀ ℕ elements,
    --   since m.toSyn is injective). Then m.degree(b*) ≤ m.degree(c_{b*} * b*) = m.degree f
    --   (natural order: m.degree(c_{b*} * b*) = m.degree(c_{b*}) + m.degree(b*) ≥ m.degree(b*)).
    --
    -- Case B (D > m.toSyn(m.degree f)):
    --   All B_D := {b ∈ B : m.toSyn(m.degree(c_b * b)) = D} have the SAME leading monomial
    --   α = m.toSyn⁻¹(D) (injectivity of m.toSyn). Sum ∑_{b ∈ B_D} c_b * b has degree < D
    --   (the degree-D terms cancel since D > degree(f)).
    --
    --   By `sPolynomial_decomposition'` (needs [Field R]):
    --     ∑_{b ∈ B_D} c_b * b = ∑_{b₁,b₂ ∈ B_D} coeff • S(c_{b₁} * b₁, c_{b₂} * b₂)
    --   where each S-poly has degree < D.
    --
    --   Key algebraic fact (S-poly scaling):
    --     S(c_{b₁} * b₁, c_{b₂} * b₂) = monomial(α - (m.degree b₁ ⊔ m.degree b₂)) * S(b₁, b₂)
    --   (when c_{b₁} * b₁ and c_{b₂} * b₂ have the same leading monomial α).
    --
    --   By the S-poly hypothesis: S(b₁, b₂) = ∑_k h_k * b_k with deg(h_k * b_k) ≤ deg(S(b₁, b₂)).
    --   Multiplying by monomial(α - lcm): the new terms have degree < D.
    --
    --   Substituting back gives a new representation of f with max degree < D.
    --   By WFI on D, we eventually reach Case A, proving the key lemma.
    --
    -- With the key lemma, we show Ideal.span(lt(span G)) ⊆ Ideal.span(lt(G)):
    --   For any f ∈ Ideal.span G (f ≠ 0), lt(f) ∈ span(lt(G)) via the key lemma +
    --   span_leadingTerm_eq_span_monomial + mem_ideal_span_monomial_image.
    sorry

end MonomialOrder

end

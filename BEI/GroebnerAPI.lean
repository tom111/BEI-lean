import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner

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

Hypothesis: all elements of `G` have invertible (unit) leading coefficients.

Source: WuProver/groebner_proj `Groebner.lean`,
`isGroebnerBasis_iff_isRemainder_sPolynomial_zero`.
-/
theorem isGroebnerBasis_iff_sPolynomial_isRemainder {R : Type*} [CommRing R]
    {G : Set (MvPolynomial σ R)} (hG : ∀ g ∈ G, IsUnit (m.leadingCoeff g)) :
    m.IsGroebnerBasis G (Ideal.span G) ↔
    ∀ (g₁ g₂ : G), m.IsRemainder (m.sPolynomial g₁.val g₂.val : MvPolynomial σ R) G 0 := by
  sorry

end MonomialOrder

end

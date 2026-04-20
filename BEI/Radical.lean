import BEI.GroebnerBasis
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Defs

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Radicality of binomial edge ideals (Corollary 2.2)

We prove that `J_G` is a radical ideal by showing: if `I` has a Gröbner basis with
squarefree leading monomials, then `I` is radical. Applied to the Gröbner basis from
Theorem 2.1, this yields Corollary 2.2 of Herzog et al. (2010).

## Main results

- `MonomialOrder.isRadical_of_squarefree_isGroebnerBasis`: general radicality from
  squarefree Gröbner basis.
- `corollary_2_2`: `(binomialEdgeIdeal G).IsRadical`.
-/

noncomputable section

open MvPolynomial MonomialOrder SimpleGraph

/-! ## Squarefree divisibility -/

/-- Squarefree divisibility: if `m` has all values ≤ 1 and `m ≤ n • t` pointwise,
then `m ≤ t`. A squarefree monomial divides a power iff it divides the base. -/
private lemma Finsupp.squarefree_le_of_le_nsmul {σ : Type*}
    {m t : σ →₀ ℕ} {n : ℕ}
    (hsq : ∀ v, m v ≤ 1) (hle : m ≤ n • t) : m ≤ t := by
  intro v
  have hm := hsq v
  have ht := hle v
  simp only [Finsupp.smul_apply, smul_eq_mul] at ht
  by_cases hm0 : m v = 0
  · omega
  · have : 1 ≤ n * t v := by omega
    have : t v ≠ 0 := by intro h; simp [h] at this
    omega

/-! ## General Gröbner radicality theorem -/

namespace MonomialOrder

variable {σ : Type*} (m : MonomialOrder σ) {R : Type*} [Field R]

/-- If `f ∈ I`, `f ≠ 0`, and `G` is a Gröbner basis of `I`, then some nonzero
element of `G` has leading monomial ≤ leading monomial of `f`. -/
lemma exists_degree_le_of_mem
    {G : Set (MvPolynomial σ R)} {I : Ideal (MvPolynomial σ R)}
    (hGB : m.IsGroebnerBasis G I)
    {f : MvPolynomial σ R} (hf : f ∈ I) (hf0 : f ≠ 0) :
    ∃ g ∈ G, g ≠ 0 ∧ m.degree g ≤ m.degree f := by
  have hlt_mem : m.leadingTerm f ∈ Ideal.span (m.leadingTerm '' G) := by
    rw [← hGB.2]; exact Ideal.subset_span ⟨f, hf, rfl⟩
  rw [span_leadingTerm_eq_span_monomial'] at hlt_mem
  -- Convert (fun p ↦ monomial (m.degree p) 1) '' (G \ {0}) to
  -- (fun d ↦ monomial d 1) '' (m.degree '' (G \ {0}))
  rw [show (fun p => (monomial (m.degree p)) (1 : R)) = (fun d => monomial d 1) ∘ m.degree
    from rfl, Set.image_comp] at hlt_mem
  rw [mem_ideal_span_monomial_image] at hlt_mem
  have hdeg_supp : m.degree f ∈ (m.leadingTerm f).support := by
    classical
    rw [mem_support_iff, leadingTerm, coeff_monomial, if_pos rfl]
    exact m.coeff_degree_ne_zero_iff.mpr hf0
  obtain ⟨_, ⟨g, hgdiff, rfl⟩, hle⟩ := hlt_mem _ hdeg_supp
  exact ⟨g, hgdiff.1, hgdiff.2, hle⟩

/-- The linear combination in an `IsRemainder` decomposition lies in `Ideal.span G`. -/
private lemma linearCombination_mem_span
    {G : Set (MvPolynomial σ R)}
    (g : ↑G →₀ MvPolynomial σ R) :
    Finsupp.linearCombination _ (fun (b : ↑G) => (b : MvPolynomial σ R)) g ∈ Ideal.span G := by
  rw [Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun b _ =>
    Ideal.mul_mem_left _ _ (Ideal.subset_span b.prop)

/-- If `I` has a Gröbner basis `G` where every nonzero element has squarefree leading
monomial, then `I` is radical.

The proof: suppose `f^n ∈ I`. Take a remainder `r` of `f` w.r.t. `G`. If `r = 0`,
done. If `r ≠ 0`, then `r^n ∈ I` and `r^n ≠ 0`, so some GB element `g` has
`degree(g) ≤ degree(r^n) = n • degree(r)`. Since `degree(g)` is squarefree,
`degree(g) ≤ degree(r)`, contradicting the irreducibility of `r`. -/
theorem isRadical_of_squarefree_isGroebnerBasis
    {G : Set (MvPolynomial σ R)}
    (hGB : m.IsGroebnerBasis G (Ideal.span G))
    (hUnit : ∀ g ∈ G, IsUnit (m.leadingCoeff g))
    (hSqfree : ∀ g ∈ G, g ≠ 0 → ∀ v, m.degree g v ≤ 1) :
    (Ideal.span G).IsRadical := by
  intro f hf
  obtain ⟨n, hn⟩ := hf
  -- Get a remainder of f
  obtain ⟨r, ⟨g, hfgr, hdeg⟩, hirr⟩ := m.exists_isRemainder hUnit f
  -- If r = 0, f is already in the span
  by_cases hr0 : r = 0
  · rw [hr0, add_zero] at hfgr; rw [hfgr]
    exact linearCombination_mem_span g
  -- r ≠ 0: derive contradiction
  exfalso
  -- f ≡ r (mod I), so r^n ∈ I
  have h_sub : f - r ∈ Ideal.span G := by
    rw [show f - r = Finsupp.linearCombination _ (fun (b : ↑G) => (b : MvPolynomial σ R)) g
      from by rw [hfgr]; ring]
    exact linearCombination_mem_span g
  -- Use the quotient ring to show r^n ∈ I
  set I := Ideal.span G
  have h_rn_mem : r ^ n ∈ I := by
    have hmk : Ideal.Quotient.mk I f = Ideal.Quotient.mk I r := by
      rw [Ideal.Quotient.eq]; exact h_sub
    have h1 : Ideal.Quotient.mk I (f ^ n) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hn
    have h2 : Ideal.Quotient.mk I (r ^ n) = 0 := by
      rw [map_pow, ← hmk, ← map_pow]; exact h1
    exact (Ideal.Quotient.eq_zero_iff_mem).mp h2
  -- r^n ≠ 0 (field → no zero divisors → pow_ne_zero)
  have hrn0 : r ^ n ≠ 0 := pow_ne_zero _ hr0
  -- Some GB element g has degree(g) ≤ degree(r^n)
  obtain ⟨ge, hge_mem, hge0, hge_le⟩ := m.exists_degree_le_of_mem hGB h_rn_mem hrn0
  -- degree(r^n) = n • degree(r) (field is reduced)
  have h_deg_pow : m.degree (r ^ n) = n • m.degree r := m.degree_pow r n
  -- degree(ge) is squarefree and ≤ n • degree(r), so ≤ degree(r)
  have hge_le_r : m.degree ge ≤ m.degree r :=
    Finsupp.squarefree_le_of_le_nsmul (hSqfree ge hge_mem hge0) (h_deg_pow ▸ hge_le)
  -- But degree(r) ∈ r.support and irreducibility says no GB element divides it
  exact hirr (m.degree r) (m.degree_mem_support hr0) ge hge_mem hge_le_r

end MonomialOrder

/-! ## Corollary 2.2 -/

/--
**Corollary 2.2** (Herzog et al. 2010): `J_G` is a radical ideal.

Follows from `isRadical_of_squarefree_isGroebnerBasis` applied to the Gröbner basis
from Theorem 2.1 with squarefree leading monomials.
-/
theorem corollary_2_2 (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).IsRadical := by
  rw [show binomialEdgeIdeal (K := K) G = Ideal.span (groebnerBasisSet (K := K) G)
    from (groebnerBasisSet_span G).symm]
  exact binomialEdgeMonomialOrder.isRadical_of_squarefree_isGroebnerBasis
    (by rw [groebnerBasisSet_span]; exact theorem_2_1 G)
    (fun g hg => by obtain ⟨i, j, π, hπ, rfl⟩ := hg;
                    exact groebnerElement_leadingCoeff_isUnit i j π hπ)
    (fun g hg _ v => by obtain ⟨i, j, π, hπ, rfl⟩ := hg;
                        exact groebnerElement_leadingMonomial_squarefree G i j π hπ v)

end

import BEI.AdmissiblePaths
import BEI.MonomialOrder
import BEI.GroebnerAPI
import BEI.ClosedGraphs
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Algebraic lemmas for Theorem 2.1

Identities and helper lemmas used in the proof of Theorem 2.1 (Herzog et al. 2010).
Key contents:
- `fij_antisymm`, `fij_telescope`, `fij_x_telescope`: algebraic identities for f_{ij}
- `isRemainder_fij_via_groebnerElement`, `isRemainder_add`: IsRemainder helpers
- `collapse`, `rename_collapse_eq_zero`: the collapse map V ⊕ V → V
- `binomialEdgeIdeal_no_monomial`: J_G contains no monomials
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## fij identities -/

/-- `fij i₁ i₂ = -(fij i₂ i₁)` (antisymmetry). -/
lemma fij_antisymm (i₁ i₂ : V) :
    fij (K := K) i₁ i₂ = -(fij (K := K) i₂ i₁) := by
  simp only [fij]; ring

/-- **Telescoping identity for fij**: `y b * fij a c = y c * fij a b + y a * fij b c`.
This is the fundamental identity for the τ-path decomposition in Theorem 2.1. -/
lemma fij_telescope (a b c : V) :
    y (K := K) b * fij a c = y c * fij a b + y a * fij b c := by
  simp only [fij, x, y]; ring

/-- **x-telescoping identity for fij**: `x b * fij a c = x a * fij b c + x c * fij a b`.
Dual of `fij_telescope` (y-telescope). Used for the shared-first endpoint case. -/
lemma fij_x_telescope (a b c : V) :
    x (K := K) b * fij a c = x a * fij b c + x c * fij a b := by
  simp only [fij, x, y]; ring

/-! ## S-polynomial monomial bound -/

/-- Cross-condition bound for the S-polynomial monomial factor D.
When `f₁ v > f₂ v → d₁ v = 0` and vice versa, the sup of d's is bounded by D. -/
private lemma finsupp_sup_le_D {ι : Type*} (d₁ d₂ f₁ f₂ : ι →₀ ℕ)
    (h₁ : ∀ v, f₁ v < f₂ v → d₁ v = 0)
    (h₂ : ∀ v, f₂ v < f₁ v → d₂ v = 0) :
    d₁ ⊔ d₂ ≤ ((d₁ + f₁) ⊔ (d₂ + f₂) - f₁) ⊔ f₂ := by
  intro v
  simp only [Finsupp.sup_apply, Finsupp.add_apply, Finsupp.tsub_apply]
  have := h₁ v; have := h₂ v; omega

/-! ## IsRemainder helpers -/

/-- If there exists an admissible path from `a` to `b`, and `q` is any polynomial
such that `pathMonomial a b σ` divides `q` (as monomials), then
`IsRemainder (q * fij a b) groebnerBasisSet 0`.

This works because `q * fij a b = (q / pathMonomial) * groebnerElement a b σ`
and `groebnerElement a b σ ∈ groebnerBasisSet`, so `isRemainder_single_mul` applies. -/
lemma isRemainder_fij_via_groebnerElement (G : SimpleGraph V)
    (a b : V) (σ : List V) (hσ : IsAdmissiblePath G a b σ)
    (q : MvPolynomial (BinomialEdgeVars V) K)
    (d_q : BinomialEdgeVars V →₀ ℕ) (hq : q = monomial d_q 1)
    (d_σ : BinomialEdgeVars V →₀ ℕ) (hσ_eq : pathMonomial (K := K) a b σ = monomial d_σ 1)
    (hdiv : d_σ ≤ d_q) :
    binomialEdgeMonomialOrder.IsRemainder
      (q * fij (K := K) a b) (groebnerBasisSet G) 0 := by
  have hge_mem : groebnerElement (K := K) a b σ ∈ groebnerBasisSet G :=
    ⟨a, b, σ, hσ, rfl⟩
  have hge_eq : groebnerElement (K := K) a b σ = monomial d_σ 1 * fij a b := by
    show pathMonomial (K := K) a b σ * fij a b = monomial d_σ 1 * fij a b
    rw [hσ_eq]
  have hfactor : q * fij (K := K) a b =
      monomial (d_q - d_σ) 1 * groebnerElement (K := K) a b σ := by
    rw [hq, hge_eq, ← mul_assoc]
    congr 1
    show monomial d_q 1 = monomial (d_q - d_σ) 1 * monomial d_σ 1
    conv_lhs => rw [show d_q = (d_q - d_σ) + d_σ from (tsub_add_cancel_of_le hdiv).symm]
    simp [monomial_mul]
  rw [hfactor]
  exact isRemainder_single_mul _ _ _ hge_mem

/-- `IsRemainder (f₁ + f₂) G 0` from `IsRemainder f₁ G 0` and `IsRemainder f₂ G 0`,
provided both summands have degree ≤ degree of the sum. -/
lemma isRemainder_add
    (f₁ f₂ : MvPolynomial (BinomialEdgeVars V) K)
    (G : Set (MvPolynomial (BinomialEdgeVars V) K))
    (h₁ : binomialEdgeMonomialOrder.IsRemainder f₁ G 0)
    (h₂ : binomialEdgeMonomialOrder.IsRemainder f₂ G 0)
    (hd₁ : binomialEdgeMonomialOrder.degree f₁
      ≼[binomialEdgeMonomialOrder]
      binomialEdgeMonomialOrder.degree (f₁ + f₂))
    (hd₂ : binomialEdgeMonomialOrder.degree f₂
      ≼[binomialEdgeMonomialOrder]
      binomialEdgeMonomialOrder.degree (f₁ + f₂)) :
    binomialEdgeMonomialOrder.IsRemainder (f₁ + f₂) G 0 := by
  obtain ⟨⟨g₁, hf₁, hdeg₁⟩, hirr₁⟩ := h₁
  obtain ⟨⟨g₂, hf₂, hdeg₂⟩, hirr₂⟩ := h₂
  constructor
  · refine ⟨g₁ + g₂, ?_, ?_⟩
    · rw [map_add, hf₁, hf₂]; ring
    · intro b
      simp only [Finsupp.add_apply, mul_add]
      exact le_trans degree_add_le (max_le (le_trans (hdeg₁ b) hd₁) (le_trans (hdeg₂ b) hd₂))
  · intro c hc; simp at hc

/-! ## No-monomial lemma and collapse map -/

/-- Elements of `J_G` evaluate to 0 at the all-ones point (x_v = y_v = 1).
This is because each generator `x_i y_j - x_j y_i` evaluates to `1·1 - 1·1 = 0`. -/
private lemma eval_one_zero_of_mem (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) :
    MvPolynomial.eval (fun _ => (1 : K)) f = 0 := by
  have hle : binomialEdgeIdeal (K := K) G ≤
      RingHom.ker (MvPolynomial.eval (fun _ => (1 : K))) := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨i, j, _, _, rfl⟩ := hg
    simp [RingHom.mem_ker, x, y]
  exact RingHom.mem_ker.mp (hle hf)

/-- **No monomial in J_G**: If `monomial d c ∈ J_G` then `c = 0`.
Proof: evaluate at `x_v = y_v = 1`; monomials evaluate to their coefficient,
but J_G elements evaluate to 0. -/
private lemma binomialEdgeIdeal_no_monomial (G : SimpleGraph V)
    (d : BinomialEdgeVars V →₀ ℕ) (c : K)
    (h : (monomial d c : MvPolynomial (BinomialEdgeVars V) K) ∈ binomialEdgeIdeal G) :
    c = 0 := by
  have := eval_one_zero_of_mem G _ h
  simp [eval_monomial] at this
  exact this

/-- The rename homomorphism that collapses x_v and y_v to the same variable X_v.
This kills every generator x_i y_j - x_j y_i since they become X_i X_j - X_j X_i = 0. -/
def collapse : BinomialEdgeVars V → V := Sum.elim id id

/-- The collapse map sends each generator to 0:
rename collapse (x_i y_j - x_j y_i) = 0. -/
lemma rename_collapse_generator (i j : V) :
    MvPolynomial.rename (collapse (V := V))
      (x i * y j - x j * y i :
        MvPolynomial (BinomialEdgeVars V) K) = 0 := by
  simp only [collapse, x, y, map_sub, map_mul, MvPolynomial.rename_X,
    Sum.elim_inl, Sum.elim_inr]
  ring

/-- The collapse map kills J_G: rename collapse f = 0 for f ∈ J_G. -/
lemma rename_collapse_eq_zero (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) :
    MvPolynomial.rename (collapse (V := V)) f = 0 := by
  have hle : binomialEdgeIdeal (K := K) G ≤
      RingHom.ker (MvPolynomial.rename
        (collapse (V := V)) : MvPolynomial _ K →ₐ[K] _).toRingHom := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨i, j, _, _, rfl⟩ := hg
    exact RingHom.mem_ker.mpr (rename_collapse_generator i j)
  exact RingHom.mem_ker.mp (hle hf)

/-- For nonzero f ∈ J_G, there exists d' ≠ LM(f) in support(f) with the same
column degree. This follows from rename collapse f = 0 and
coeff(f, LM(f)) ≠ 0. -/
lemma exists_other_support_same_colDeg (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G) (hf_ne : f ≠ 0) :
    ∃ d' ∈ f.support, d' ≠ binomialEdgeMonomialOrder.degree f ∧
      Finsupp.mapDomain (collapse (V := V)) d' =
        Finsupp.mapDomain (collapse (V := V))
          (binomialEdgeMonomialOrder.degree f) := by
  set d := binomialEdgeMonomialOrder.degree f
  set c := Finsupp.mapDomain (collapse (V := V)) d
  have h_zero := rename_collapse_eq_zero G f hf_mem
  have h_coeff :=
    binomialEdgeMonomialOrder.coeff_degree_ne_zero_iff.mpr hf_ne
  set f' := f - MvPolynomial.monomial d (f.coeff d) with hf'_def
  have hf'_rename : (MvPolynomial.rename (collapse (V := V)) f').coeff
      c ≠ 0 := by
    rw [hf'_def, map_sub, MvPolynomial.rename_monomial]
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial]
    rw [if_pos rfl]
    have : (MvPolynomial.rename (collapse (V := V)) f).coeff c = 0 := by
      rw [h_zero]; simp
    rw [this, zero_sub, neg_ne_zero]
    exact h_coeff
  obtain ⟨u, hu_map, hu_coeff⟩ :=
    MvPolynomial.coeff_rename_ne_zero _ f' c hf'_rename
  have hu_ne : u ≠ d := by
    intro h_eq
    rw [h_eq, hf'_def, MvPolynomial.coeff_sub,
      MvPolynomial.coeff_monomial, if_pos rfl, sub_self] at hu_coeff
    exact hu_coeff rfl
  have hu_support : u ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    rw [hf'_def, MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial,
      if_neg (Ne.symm hu_ne)] at hu_coeff
    simpa using hu_coeff
  exact ⟨u, hu_support, hu_ne, hu_map⟩

end

import BEI.AdmissiblePaths
import BEI.MonomialOrder
import BEI.GroebnerAPI
import BEI.ClosedGraphs
import BEI.HerzogLemmas
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Rauh's approach to Theorem 2.1 (ARCHIVED SUPPLEMENT)

This file contains an alternative proof approach to Theorem 2.1 via Rauh (2013),
arxiv:1210.7960. The key idea: prove that every nonzero element of J_G has its
leading monomial divisible by some groebnerElement's leading monomial, then derive
the Gröbner basis property via the division algorithm.

This approach was partially completed but has two remaining sorry's:
- `exists_walk_outside_interval`: graph connectivity from sub-ideal membership
- `exists_groebnerElement_from_walk`: degree bound from walk to admissible path

The main paper formalization uses the direct Herzog S-polynomial approach instead.
This file is kept as supplementary archived code and is not on the main import path.
-/

noncomputable section

open MvPolynomial MonomialOrder

/-! ## Rauh's approach: crossing lemma and iterative reduction

The proof of `isRemainder_sPolynomial_fij_of_admissible` follows Rauh (arxiv:1210.7960),
Theorem 2.3. The key idea: any nonzero S-polynomial of two `fij`s can be written as
a difference of monomial-times-fij terms. Each such term `M * fij(a,b)` has a leading
monomial `M * x_a * y_b`. If the "variable assignment" is not antitone (i.e., the
monomial `M` is not a valid pathMonomial for any admissible path from `a` to `b`),
then some groebnerElement's leading term divides `M * x_a * y_b`, allowing reduction.
By well-founded induction on the monomial order, this process terminates at 0.

### Specialization to d₀ = 2

In the BEI case (d₀ = 2), a "crossing" in a monomial degree `d` at position `(a, b)`
means `a < b` with `d(inl a) ≥ 1` (x_a divides) and `d(inr b) ≥ 1` (y_b divides).
The pathMonomial of an admissible path from `a` to `b` consists of:
- `x_v` for internal vertices `v > b` (these have κ(v) = 1, i.e., inl)
- `y_v` for internal vertices `v < a` (these have κ(v) = 2, i.e., inr)

The antitone condition forces: smaller vertices get higher κ values (y-variables)
and larger vertices get lower κ values (x-variables). A crossing violates this.
-/
/-- If `∏ X(l_k) = monomial d 1` and `l.Nodup`, then `d t ≤ 1` for all `t`. -/
private lemma prod_X_list_exponent_le_one {σ : Type*} {R : Type*} [CommSemiring R] [Nontrivial R]
    [DecidableEq σ]
    (l : List σ) (hnd : l.Nodup) (t : σ)
    (d : σ →₀ ℕ) (hd : (l.map (fun a => (X a : MvPolynomial σ R))).prod = monomial d 1) :
    d t ≤ 1 := by
  classical
  induction l generalizing d with
  | nil =>
    simp [List.map_nil, List.prod_nil] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    simp [← heq]
  | cons a l ih =>
    obtain ⟨d', hd'⟩ := prod_X_list_eq_monomial' (R := R) l
    simp only [List.map_cons, List.prod_cons, hd'] at hd
    change monomial (Finsupp.single a 1) 1 * monomial d' 1 = monomial d 1 at hd
    rw [monomial_mul, one_mul] at hd
    have heq := monomial_left_injective (one_ne_zero (α := R)) hd
    rw [← heq]
    have hnd' := (List.nodup_cons.mp hnd).2
    have ha_notin := (List.nodup_cons.mp hnd).1
    by_cases hat : t = a
    · -- t = a: single a 1 contributes 1, d'(a) = 0 since a ∉ l
      subst hat
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
      have := prod_X_list_exponent_zero l t ha_notin d' hd'
      omega
    · -- t ≠ a: single contributes 0, use IH
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hat), zero_add]
      exact ih hnd' d' hd'

/-- The pathMonomial exponent is at most 1 at every position. -/
private lemma pathMonomial_exponent_le_one (i j : V) (π : List V)
    (hσ : IsAdmissiblePath G i j π) (w : BinomialEdgeVars V)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d w ≤ 1 := by
  obtain ⟨_, _, _, hNodup, _, _, _⟩ := hσ
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun v => j < v) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun v => v < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun v => j < v)).map
        (fun v => (X (Sum.inl v) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun v => j < v)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun v => v < i)).map
        (fun v => (X (Sum.inr v) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun v => v < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  have hint_nd : (internalVertices π).Nodup :=
    (hNodup.sublist (List.tail_sublist π)).sublist (List.dropLast_sublist _)
  have inl_inj : Function.Injective (Sum.inl : V → BinomialEdgeVars V) :=
    Sum.inl_injective
  have inr_inj : Function.Injective (Sum.inr : V → BinomialEdgeVars V) :=
    Sum.inr_injective
  have hxl_nd : ((internalVertices π).filter (fun v => j < v) |>.map Sum.inl).Nodup :=
    List.Nodup.map inl_inj (hint_nd.filter _)
  have hyl_nd : ((internalVertices π).filter (fun v => v < i) |>.map Sum.inr).Nodup :=
    List.Nodup.map inr_inj (hint_nd.filter _)
  cases w with
  | inl v =>
    -- dy has only inr entries, so dy(inl v) = 0
    have hdy_zero : dy (Sum.inl v) = 0 := by
      apply prod_X_list_exponent_zero _ _ _ _ hdy
      simp only [List.mem_map, not_exists, not_and]
      intro w _ hweq; exact absurd hweq (by simp)
    have hdx_le := prod_X_list_exponent_le_one _ hxl_nd (Sum.inl v) _ hdx
    omega
  | inr v =>
    -- dx has only inl entries, so dx(inr v) = 0
    have hdx_zero : dx (Sum.inr v) = 0 := by
      apply prod_X_list_exponent_zero _ _ _ _ hdx
      simp only [List.mem_map, not_exists, not_and]
      intro w _ hweq; exact absurd hweq (by simp)
    have hdy_le := prod_X_list_exponent_le_one _ hyl_nd (Sum.inr v) _ hdy
    omega

/-- The pathMonomial exponent at `Sum.inl v` is 0 when `v ∉ (internalVertices σ).filter (j < ·)`.
Strengthens `pathMonomial_exponent_inl_of_le` to also cover `v ∈ internals` with `v ≤ j`. -/
private lemma pathMonomial_exponent_inl_zero_of_not_mem
    (i j : V) (π : List V) (v : V)
    (hv : v ∉ (internalVertices π).filter (fun w => j < w))
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inl v) = 0 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  have hdx_zero : dx (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    simp only [List.mem_map, Sum.inl.injEq, not_exists, not_and]
    intro w hw hweq; exact hv (hweq ▸ hw)
  have hdy_zero : dy (Sum.inl v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, not_exists, not_and]
    intro w _ hweq; exact absurd hweq (by simp)
  omega

/-- The pathMonomial exponent at `Sum.inr v` is 0 when `v ∉ (internalVertices σ).filter (· < i)`. -/
private lemma pathMonomial_exponent_inr_zero_of_not_mem
    (i j : V) (π : List V) (v : V)
    (hv : v ∉ (internalVertices π).filter (fun w => w < i))
    (d : BinomialEdgeVars V →₀ ℕ)
    (hd : pathMonomial (K := K) i j π = monomial d 1) :
    d (Sum.inr v) = 0 := by
  obtain ⟨dx, hdx⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => j < w) |>.map Sum.inl)
  obtain ⟨dy, hdy⟩ := prod_X_list_eq_monomial' (R := K)
    ((internalVertices π).filter (fun w => w < i) |>.map Sum.inr)
  have hpm : pathMonomial (K := K) i j π = monomial (dx + dy) 1 := by
    simp only [pathMonomial, x, y]
    rw [show ((internalVertices π).filter (fun w => j < w)).map
        (fun w => (X (Sum.inl w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => j < w)).map Sum.inl).map X by
          simp [List.map_map],
      show ((internalVertices π).filter (fun w => w < i)).map
        (fun w => (X (Sum.inr w) : MvPolynomial (BinomialEdgeVars V) K)) =
        (((internalVertices π).filter (fun w => w < i)).map Sum.inr).map X by
          simp [List.map_map]]
    rw [hdx, hdy, monomial_mul]; congr 1; ring
  have heq : d = dx + dy :=
    monomial_left_injective (one_ne_zero (α := K)) (hd.symm.trans hpm)
  rw [heq, Finsupp.add_apply]
  have hdx_zero : dx (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdx
    simp only [List.mem_map, not_exists, not_and]
    intro w _ hweq; exact absurd hweq (by simp)
  have hdy_zero : dy (Sum.inr v) = 0 := by
    apply prod_X_list_exponent_zero _ _ _ _ hdy
    simp only [List.mem_map, Sum.inr.injEq, not_exists, not_and]
    intro w hw hweq; exact hv (hweq ▸ hw)
  omega

private lemma pathMonomial_degree_le_of_supported (i j : V) (σ : List V)
    (hσ : IsAdmissiblePath G i j σ)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hx : ∀ v ∈ internalVertices σ, j < v → 1 ≤ d (Sum.inl v))
    (hy : ∀ v ∈ internalVertices σ, v < i → 1 ≤ d (Sum.inr v)) :
    ∀ (d_σ : BinomialEdgeVars V →₀ ℕ),
      pathMonomial (K := K) i j σ = monomial d_σ 1 → d_σ ≤ d := by
  intro d_σ hd_σ w
  rcases w with v | v
  · -- w = Sum.inl v
    by_cases hv_mem : v ∈ (internalVertices σ).filter (fun w => j < w)
    · -- v is an internal vertex with j < v: d_σ(inl v) = 1 and d(inl v) ≥ 1
      have h_le := pathMonomial_exponent_le_one (G := G) i j σ hσ (Sum.inl v) d_σ hd_σ
      have h_sup := hx v (List.mem_filter.mp hv_mem).1
        (of_decide_eq_true (List.mem_filter.mp hv_mem).2)
      omega
    · -- v is NOT in the filtered list: d_σ(inl v) = 0
      have := pathMonomial_exponent_inl_zero_of_not_mem (K := K) i j σ v hv_mem d_σ hd_σ
      omega
  · -- w = Sum.inr v: symmetric
    by_cases hv_mem : v ∈ (internalVertices σ).filter (fun w => w < i)
    · have h_le := pathMonomial_exponent_le_one (G := G) i j σ hσ (Sum.inr v) d_σ hd_σ
      have h_sup := hy v (List.mem_filter.mp hv_mem).1
        (of_decide_eq_true (List.mem_filter.mp hv_mem).2)
      omega
    · have := pathMonomial_exponent_inr_zero_of_not_mem (K := K) i j σ v hv_mem d_σ hd_σ
      omega

/-- Internal vertices of a list are members of the list. -/
private lemma internalVertices_mem (π : List V) (v : V)
    (hv : v ∈ internalVertices π) : v ∈ π := by
  simp only [internalVertices] at hv
  exact List.tail_subset _ (List.dropLast_subset _ hv)

/-! ## Rauh's core divisibility claim

The key to proving `groebnerBasisSet` is a Gröbner basis (Theorem 2.1) is showing that
every nonzero element of `J_G` has its leading monomial divisible by some groebnerElement's
leading monomial.

**Previous approach (ABANDONED)**: Factor S(ge₁,ge₂) = monomial D · S(fij₁,fij₂) and prove
IsRemainder for the inner S-polynomial. This is **WRONG** because S(fij₁,fij₂) need not be
in J_G (e.g., fij(3,5) ∉ J_G when 3-5 is not an edge, even if admissible paths exist for
the original pairs through a common vertex).

**Current approach (Rauh, arxiv:1210.7960, Theorem 2)**: Prove the leading-term divisibility
claim directly, then derive IsGroebnerBasis via `exists_isRemainder` + irredundancy.

For any nonzero f ∈ J_G, the leading monomial has a "crossing" (∃ a < b with x_a | LM
and y_b | LM), because J_G is Z^V-homogeneous and contains no monomials. The crossing
yields an admissible path a→b whose groebnerElement's LT divides LM(f). -/

/-! ### Bihomogeneity of J_G (Z^V-grading via collapse weight)

To prove the crossing lemma, we need that J_G is graded by the "collapse" weight:
the weight function `collapseWeight v = Finsupp.single (collapse v) 1` assigns the same
weight to `x_v` and `y_v`. Each generator `f_{ij} = x_i y_j - x_j y_i` is homogeneous
under this grading (both monomials have weight `single i 1 + single j 1`).

We instantiate Mathlib's `GradedAlgebra` for this weight, then apply
`Ideal.homogeneous_span` to conclude that J_G is graded. This means
the collapse-m component of any `f ∈ J_G` is again in J_G. -/

/-- The collapse weight function: maps each variable to `Finsupp.single v 1` where
`v` is the underlying vertex (i.e., `inl v ↦ single v 1`, `inr v ↦ single v 1`). -/
private def collapseWeight : BinomialEdgeVars V → (V →₀ ℕ) :=
  fun v => Finsupp.single (collapse v) 1

/-- Each generator `f_{ij}` is weighted homogeneous under the collapse weight.
Both monomials `x_i · y_j` and `x_j · y_i` have collapse weight `single i 1 + single j 1`. -/
private lemma generator_isWeightedHomogeneous (i j : V) (hij : i < j) :
    MvPolynomial.IsWeightedHomogeneous (collapseWeight (V := V))
      (x (K := K) i * y j - x j * y i : MvPolynomial (BinomialEdgeVars V) K)
      (Finsupp.single i 1 + Finsupp.single j 1) := by
  -- The weight of single(inl a, 1) + single(inr b, 1) is single(a,1) + single(b,1)
  have h_weight : ∀ (a b : V),
      Finsupp.weight (collapseWeight (V := V))
        (Finsupp.single (Sum.inl a : BinomialEdgeVars V) 1 +
         Finsupp.single (Sum.inr b : BinomialEdgeVars V) 1) =
        Finsupp.single a 1 + Finsupp.single b 1 := by
    intro a b
    simp only [Finsupp.weight_apply, collapseWeight, collapse]
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by simp [Nat.add_mul]),
        Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp)]
    simp [Sum.elim_inl, Sum.elim_inr]
  -- Express the generator as monomial - monomial
  set d₁ := Finsupp.single (Sum.inl i : BinomialEdgeVars V) 1 +
             Finsupp.single (Sum.inr j : BinomialEdgeVars V) 1
  set d₂ := Finsupp.single (Sum.inl j : BinomialEdgeVars V) 1 +
             Finsupp.single (Sum.inr i : BinomialEdgeVars V) 1
  set w := collapseWeight (V := V)
  set m := Finsupp.single i 1 + Finsupp.single j 1
  -- x_i * y_j is homogeneous with weight single i 1 + single j 1
  have hm_eq : w (Sum.inl i) + w (Sum.inr j) = m := by
    change Finsupp.single i 1 + Finsupp.single j 1 = m; rfl
  have hm_eq' : w (Sum.inl j) + w (Sum.inr i) = m := by
    change Finsupp.single j 1 + Finsupp.single i 1 = m; exact add_comm _ _
  have hX := MvPolynomial.isWeightedHomogeneous_X (R := K) w
  have hxi := hX (Sum.inl i)
  have hxj := hX (Sum.inl j)
  have hyi := hX (Sum.inr i)
  have hyj := hX (Sum.inr j)
  have hxy : MvPolynomial.IsWeightedHomogeneous w
      (x (K := K) i * y j : MvPolynomial (BinomialEdgeVars V) K) m := by
    change MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.X _ * MvPolynomial.X _) m
    rw [← hm_eq]; exact hxi.mul hyj
  have hyx : MvPolynomial.IsWeightedHomogeneous w
      (x (K := K) j * y i : MvPolynomial (BinomialEdgeVars V) K) m := by
    change MvPolynomial.IsWeightedHomogeneous w (MvPolynomial.X _ * MvPolynomial.X _) m
    rw [← hm_eq']; exact hxj.mul hyi
  exact show x i * y j - x j * y i ∈ MvPolynomial.weightedHomogeneousSubmodule K w m from
    Submodule.sub_mem _ hxy hyx

/-- J_G is homogeneous under the collapse weight grading. -/
private lemma binomialEdgeIdeal_isHomogeneous (G : SimpleGraph V) :
    letI := MvPolynomial.weightedGradedAlgebra (K) (collapseWeight (V := V))
    (binomialEdgeIdeal (K := K) G).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule K (collapseWeight (V := V))) := by
  letI := MvPolynomial.weightedGradedAlgebra (K) (collapseWeight (V := V))
  apply Ideal.homogeneous_span
  intro g hg
  obtain ⟨i, j, _, hij, rfl⟩ := hg
  exact ⟨_, generator_isWeightedHomogeneous i j hij⟩

/-- The collapse-m component of any `f ∈ J_G` is again in `J_G`. -/
private lemma collapseComponent_mem (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) (m : V →₀ ℕ) :
    MvPolynomial.weightedHomogeneousComponent (collapseWeight (V := V)) m f ∈
      binomialEdgeIdeal (K := K) G := by
  letI := MvPolynomial.weightedGradedAlgebra (K) (collapseWeight (V := V))
  have hH := binomialEdgeIdeal_isHomogeneous (K := K) G
  -- IsHomogeneous says: ∀ i, ∀ ⦃r⦄, r ∈ I → ↑(decompose 𝒜 r i) ∈ I
  have h : (↑(DirectSum.decompose
    (MvPolynomial.weightedHomogeneousSubmodule K (collapseWeight (V := V))) f m) :
    MvPolynomial (BinomialEdgeVars V) K) ∈ binomialEdgeIdeal (K := K) G := hH m hf
  -- decompose for weightedGradedAlgebra = weightedHomogeneousComponent
  convert h using 1
  exact (MvPolynomial.weightedDecomposition.decompose'_apply (R := K)
    (w := collapseWeight (V := V)) f m).symm

/-! ### xydeg grading (total x-degree / y-degree) -/

/-- Map distinguishing x-variables from y-variables: `inl _ ↦ 0`, `inr _ ↦ 1`. -/
private def xydeg : BinomialEdgeVars V → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- `rename xydeg` kills J_G: `rename xydeg f = 0` for `f ∈ J_G`. -/
private lemma rename_xydeg_eq_zero (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) :
    MvPolynomial.rename (xydeg (V := V)) f = 0 := by
  have hle : binomialEdgeIdeal (K := K) G ≤
      RingHom.ker (MvPolynomial.rename
        (xydeg (V := V)) : MvPolynomial _ K →ₐ[K] _).toRingHom := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨i, j, _, _, rfl⟩ := hg
    show x i * y j - x j * y i ∈ RingHom.ker
      (MvPolynomial.rename (xydeg (V := V)) : MvPolynomial _ K →ₐ[K] _).toRingHom
    rw [RingHom.mem_ker]
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      xydeg, x, y, map_sub, map_mul, MvPolynomial.rename_X]
    ring
  exact RingHom.mem_ker.mp (hle hf)

/-- The collapse weight equals mapDomain collapse. -/
private lemma weight_collapseWeight_eq_mapDomain (d : BinomialEdgeVars V →₀ ℕ) :
    Finsupp.weight (collapseWeight (V := V)) d = Finsupp.mapDomain collapse d := by
  simp only [Finsupp.weight_apply, Finsupp.mapDomain]
  congr 1; ext a; simp [collapseWeight]

/-- Pointwise evaluation of `mapDomain collapse`:
`(mapDomain collapse e)(v) = e(inl v) + e(inr v)`. -/
private lemma mapDomain_collapse_apply (e : BinomialEdgeVars V →₀ ℕ) (v : V) :
    (Finsupp.mapDomain (collapse (V := V)) e) v = e (Sum.inl v) + e (Sum.inr v) := by
  induction e using Finsupp.induction with
  | zero => simp [Finsupp.mapDomain_zero]
  | single_add a n e ha hn ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    rw [ih]; simp only [collapse]
    rcases a with a | a
    · by_cases h : a = v
      · subst h; simp; omega
      · simp [show ¬(Sum.inl a = Sum.inl v) from fun h' => h (Sum.inl.inj h'),
              show ¬(Sum.inl a = Sum.inr v) from Sum.inl_ne_inr,
              show ¬(a = v) from h]
    · by_cases h : a = v
      · subst h; simp; omega
      · simp [show ¬(Sum.inr a = Sum.inl v) from Sum.inr_ne_inl,
              show ¬(Sum.inr a = Sum.inr v) from fun h' => h (Sum.inr.inj h'),
              show ¬(a = v) from h]

/-- Pointwise evaluation of `mapDomain xydeg` at 0:
`(mapDomain xydeg e)(0) = Σ_v e(inl v)` (total x-degree). -/
private lemma mapDomain_xydeg_zero (e : BinomialEdgeVars V →₀ ℕ) :
    (Finsupp.mapDomain (xydeg (V := V)) e) 0 =
      Finset.univ.sum (fun v : V => e (Sum.inl v)) := by
  induction e using Finsupp.induction with
  | zero => simp [Finsupp.mapDomain_zero]
  | single_add a n e ha hn ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    rw [ih, Finset.sum_add_distrib]
    congr 1
    rcases a with a | a
    · simp only [xydeg, ite_true]
      have : ∀ x : V, (if (Sum.inl a : BinomialEdgeVars V) = Sum.inl x then n else 0) =
          if a = x then n else 0 := by
        intro x; split_ifs with h1 h2 h2
        · rfl
        · exact absurd (Sum.inl.inj h1) h2
        · exact absurd (congrArg Sum.inl h2) h1
        · rfl
      simp_rw [this]; simp [Finset.mem_univ]
    · simp only [xydeg, show (1 : Fin 2) ≠ 0 from by omega, ite_false]
      simp [show ∀ x : V, (Sum.inr a : BinomialEdgeVars V) ≠ Sum.inl x from
        fun _ => Sum.inr_ne_inl]

/-- Same `mapDomain collapse` implies pointwise collapse equality. -/
private lemma same_collapse_pointwise (d d' : BinomialEdgeVars V →₀ ℕ)
    (h : Finsupp.mapDomain (collapse (V := V)) d = Finsupp.mapDomain (collapse (V := V)) d')
    (v : V) : d (Sum.inl v) + d (Sum.inr v) = d' (Sum.inl v) + d' (Sum.inr v) := by
  -- Use the weight formulation: weight collapseWeight = mapDomain collapse
  rw [← weight_collapseWeight_eq_mapDomain, ← weight_collapseWeight_eq_mapDomain] at h
  -- h : weight collapseWeight d = weight collapseWeight d'
  -- At position v: (weight cW d)(v) = d(inl v) + d(inr v)
  -- Prove this via weight_single_one_apply with Pi.single
  -- weight (Pi.single v 1) d = d v for any Finsupp d
  -- We need a version for our collapseWeight.
  -- Actually: collapseWeight = fun i => Finsupp.single (collapse i) 1
  -- (weight cW d)(v) = Σ_{i ∈ d.support} d(i) * cW(i)(v)
  -- = Σ_{i ∈ d.support} d(i) * (single (collapse i) 1)(v)
  -- = Σ_{i ∈ d.support} d(i) * (if collapse i = v then 1 else 0)
  -- = Σ_{i ∈ d.support, collapse i = v} d(i)
  -- The set {i : collapse i = v} = {inl v, inr v}
  -- So the sum = d(inl v) + d(inr v)
  -- Since weight is a Finsupp on V, equality at v gives the result.
  have hv := Finsupp.ext_iff.mp h v
  -- hv : (weight cW d) v = (weight cW d') v
  -- Now show (weight cW e) v = e(inl v) + e(inr v) for any e
  suffices key : ∀ (e : BinomialEdgeVars V →₀ ℕ),
      (Finsupp.weight (collapseWeight (V := V)) e) v = e (Sum.inl v) + e (Sum.inr v) by
    linarith [key d, key d']
  intro e
  rw [weight_collapseWeight_eq_mapDomain]
  exact mapDomain_collapse_apply e v

/-! ### Combined result: d' with same collapse AND same xydeg -/

/-- For nonzero f ∈ J_G, there exists d' ≠ LM(f) in support(f) with the same
collapse weight AND the same xydeg image. -/
private lemma exists_other_support_same_colDeg_and_xdeg (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G) (hf_ne : f ≠ 0) :
    ∃ d' ∈ f.support, d' ≠ binomialEdgeMonomialOrder.degree f ∧
      Finsupp.mapDomain (collapse (V := V)) d' =
        Finsupp.mapDomain (collapse (V := V))
          (binomialEdgeMonomialOrder.degree f) ∧
      Finsupp.mapDomain (xydeg (V := V)) d' =
        Finsupp.mapDomain (xydeg (V := V))
          (binomialEdgeMonomialOrder.degree f) := by
  classical
  set d := binomialEdgeMonomialOrder.degree f
  set m := Finsupp.weight (collapseWeight (V := V)) d
  set e := Finsupp.mapDomain (xydeg (V := V)) d
  -- Extract the collapse-m component
  set f_m := MvPolynomial.weightedHomogeneousComponent (collapseWeight (V := V)) m f
  have hfm_mem : f_m ∈ binomialEdgeIdeal (K := K) G :=
    collapseComponent_mem G f hf_mem m
  have hd_weight : Finsupp.weight (collapseWeight (V := V)) d = m := rfl
  have hd_coeff_fm : f_m.coeff d = f.coeff d := by
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos hd_weight]
  have hd_coeff_ne : f.coeff d ≠ 0 :=
    binomialEdgeMonomialOrder.coeff_degree_ne_zero_iff.mpr hf_ne
  -- Apply rename_xydeg to f_m
  have hfm_xydeg : MvPolynomial.rename (xydeg (V := V)) f_m = 0 :=
    rename_xydeg_eq_zero G f_m hfm_mem
  -- f_m - monomial d (coeff f_m d) has nonzero coeff at e under rename xydeg
  set f_m' := f_m - MvPolynomial.monomial d (f_m.coeff d)
  have hfm'_rename : (MvPolynomial.rename (xydeg (V := V)) f_m').coeff e ≠ 0 := by
    rw [show f_m' = f_m - MvPolynomial.monomial d (f_m.coeff d) from rfl,
        map_sub, MvPolynomial.rename_monomial]
    simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial]
    rw [if_pos rfl]
    have : (MvPolynomial.rename (xydeg (V := V)) f_m).coeff e = 0 := by
      rw [hfm_xydeg]; simp
    rw [this, zero_sub, neg_ne_zero, hd_coeff_fm]
    exact hd_coeff_ne
  obtain ⟨u, hu_map, hu_coeff⟩ :=
    MvPolynomial.coeff_rename_ne_zero _ f_m' e hfm'_rename
  have hu_ne : u ≠ d := by
    intro h_eq; apply hu_coeff; rw [h_eq]
    show (f_m - MvPolynomial.monomial d (f_m.coeff d)).coeff d = 0
    simp [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial]
  have hu_support_fm : u ∈ f_m.support := by
    rw [MvPolynomial.mem_support_iff]
    have := hu_coeff
    rw [show f_m' = f_m - MvPolynomial.monomial d (f_m.coeff d) from rfl] at this
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_monomial, if_neg (Ne.symm hu_ne)] at this
    simpa using this
  have hu_support : u ∈ f.support := by
    rw [MvPolynomial.mem_support_iff]
    have h := MvPolynomial.mem_support_iff.mp hu_support_fm
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at h
    split_ifs at h with h_wt
    · exact h
    · exact absurd rfl h
  have hu_weight : Finsupp.weight (collapseWeight (V := V)) u = m := by
    have h := MvPolynomial.mem_support_iff.mp hu_support_fm
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at h
    split_ifs at h with h_wt
    · exact h_wt
    · exact absurd rfl h
  have hu_collapse : Finsupp.mapDomain (collapse (V := V)) u =
      Finsupp.mapDomain (collapse (V := V)) d := by
    rw [← weight_collapseWeight_eq_mapDomain, ← weight_collapseWeight_eq_mapDomain]
    exact hu_weight
  exact ⟨u, hu_support, hu_ne, hu_collapse, hu_map⟩

/-! ### Sub-lemma 1: Crossing existence -/

/-- **Crossing existence**: For any nonzero `f ∈ J_G`, the leading monomial has a crossing:
`∃ a < b` with `d(inl a) ≥ 1` and `d(inr b) ≥ 1`. -/
private lemma exists_crossing_of_mem (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G) (hf_ne : f ≠ 0) :
    ∃ a b : V, a < b ∧
      1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inl a) ∧
      1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inr b) := by
  -- Get d' ≠ d in support(f) with same collapse and same xydeg
  obtain ⟨d', hd'_supp, hd'_ne, hd'_col, hd'_xydeg⟩ :=
    exists_other_support_same_colDeg_and_xdeg G f hf_mem hf_ne
  set d := binomialEdgeMonomialOrder.degree f
  -- Same collapse pointwise: d(inl v) + d(inr v) = d'(inl v) + d'(inr v) for all v
  have h_col : ∀ v, d (Sum.inl v) + d (Sum.inr v) = d' (Sum.inl v) + d' (Sum.inr v) :=
    fun v => same_collapse_pointwise d d' hd'_col.symm v
  -- Same xydeg: Σ_v d(inl v) = Σ_v d'(inl v) (total x-degree equal)
  -- (from mapDomain xydeg d = mapDomain xydeg d', evaluated at 0)
  -- For now, derive this from mapDomain xydeg equality
  have h_xdeg : Finsupp.mapDomain (xydeg (V := V)) d = Finsupp.mapDomain (xydeg (V := V)) d' :=
    hd'_xydeg.symm
  -- d > d' in lex
  have hd_gt : d' ≺[binomialEdgeMonomialOrder] d :=
    lt_of_le_of_ne (binomialEdgeMonomialOrder.le_degree hd'_supp) (fun h =>
      hd'_ne (binomialEdgeMonomialOrder.toSyn.injective (le_antisymm h.le h.ge)))
  -- Unpack lex: ∃ j₀, all BEV-smaller vars agree, d'(j₀) < d(j₀)
  obtain ⟨j₀, hj₀_agree, hj₀_lt⟩ : ∃ j₀, (∀ j, j < j₀ → d' j = d j) ∧ d' j₀ < d j₀ := by
    rwa [show (d' ≺[binomialEdgeMonomialOrder] d) ↔
      Finsupp.Lex (· < ·) (· < ·) d' d from Iff.rfl, Finsupp.lex_def] at hd_gt
  -- j₀ must be Sum.inr v₀ (not Sum.inl), because:
  -- if j₀ = inl v₀, all inr vars agree (inr < inl in BEV),
  -- so h_col at v₀ gives d(inl v₀) = d'(inl v₀), contradicting first-difference at j₀
  obtain ⟨v₀, rfl⟩ : ∃ v₀ : V, j₀ = Sum.inr v₀ := by
    rcases j₀ with v₀ | v₀
    · -- j₀ = inl v₀: derive contradiction
      exfalso
      -- All inr variables are BEV-smaller than inl v₀
      have h_inr_agree : ∀ v : V, d' (Sum.inr v) = d (Sum.inr v) := by
        intro v
        apply hj₀_agree
        -- inr v < inl v₀ in BinomialEdgeVars ordering
        constructor
        · exact trivial  -- binomialEdgeLE (inr v) (inl v₀) = True
        · exact not_false -- ¬binomialEdgeLE (inl v₀) (inr v) = ¬False
      -- Same collapse at v₀: d(inl v₀) + d(inr v₀) = d'(inl v₀) + d'(inr v₀)
      have := h_col v₀
      -- d(inr v₀) = d'(inr v₀)
      rw [h_inr_agree v₀] at this
      -- So d(inl v₀) = d'(inl v₀)
      have : d (Sum.inl v₀) = d' (Sum.inl v₀) := by omega
      -- But j₀ = inl v₀ means d'(inl v₀) < d(inl v₀)
      omega
    · exact ⟨v₀, rfl⟩
  -- d(inr v₀) > d'(inr v₀) ≥ 0, so d(inr v₀) ≥ 1
  have hb : 1 ≤ d (Sum.inr v₀) := by omega
  -- For v > v₀: inr v < inr v₀ in BEV (reversed: bigger V-index = smaller BEV)
  -- Helper: ordering on BinomialEdgeVars for inr
  -- We use the fact that in BinomialEdgeVars, inr v < inr v₀ iff v₀ < v
  -- (the ordering is reversed within inr)
  have h_bev_inr : ∀ v, v₀ < v →
      @LT.lt (BinomialEdgeVars V) _ (Sum.inr v) (Sum.inr v₀) := by
    intro v hv
    -- The LT on BinomialEdgeVars V is binomialEdgeLE a b ∧ ¬binomialEdgeLE b a
    -- For inr v and inr v₀: binomialEdgeLE (inr v) (inr v₀) = (v ≥ v₀)
    -- and binomialEdgeLE (inr v₀) (inr v) = (v₀ ≥ v)
    -- We need v ≥ v₀ ∧ ¬(v₀ ≥ v), i.e., v > v₀
    constructor
    · -- le: v₀ ≤ v (binomialEdgeLE (inr v) (inr v₀) = v ≥ v₀)
      exact le_of_lt hv
    · -- not le: ¬(v ≤ v₀) (¬binomialEdgeLE (inr v₀) (inr v) = ¬(v₀ ≥ v))
      exact not_le_of_gt hv
  have h_inr_hi : ∀ v, v₀ < v → d' (Sum.inr v) = d (Sum.inr v) :=
    fun v hv => hj₀_agree (Sum.inr v) (h_bev_inr v hv)
  have h_inl_hi : ∀ v, v₀ < v → d' (Sum.inl v) = d (Sum.inl v) := by
    intro v hv
    have := h_col v
    rw [h_inr_hi v hv] at this
    omega
  -- At v₀: d(inr v₀) > d'(inr v₀), so by h_col: d'(inl v₀) > d(inl v₀)
  have h_inl_v₀ : d (Sum.inl v₀) < d' (Sum.inl v₀) := by
    have := h_col v₀; omega
  -- Same total x-degree (from xydeg): Σ_v d(inl v) = Σ_v d'(inl v)
  -- This means: Σ_{v ≤ v₀} d(inl v) + Σ_{v > v₀} d(inl v) = same for d'
  -- Total x-degree equality from h_xdeg
  have h_total_xdeg : Finset.univ.sum (fun v : V => d (Sum.inl v)) =
      Finset.univ.sum (fun v : V => d' (Sum.inl v)) := by
    have h1 := mapDomain_xydeg_zero d
    have h2 := mapDomain_xydeg_zero d'
    rw [h_xdeg] at h1; linarith
  -- Split sums: below v₀, at v₀, above v₀
  -- Above v₀: d(inl v) = d'(inl v) for v > v₀ (from h_inl_hi)
  -- At v₀: d(inl v₀) < d'(inl v₀) (from h_inl_v₀)
  -- Below v₀: must compensate → Σ_{v<v₀} d(inl v) > Σ_{v<v₀} d'(inl v) ≥ 0
  -- So ∃ a < v₀ with d(inl a) ≥ 1
  by_contra h_no_crossing
  push_neg at h_no_crossing
  -- h_no_crossing : ∀ a b, a < b → d(inl a) = 0 ∨ d(inr b) = 0
  -- We need: ∀ a < v₀, d(inl a) = 0 (using h_no_crossing with b = v₀)
  have h_below : ∀ a, a < v₀ → d (Sum.inl a) = 0 := by
    intro a ha
    by_contra ha_pos
    push_neg at ha_pos
    have := h_no_crossing a v₀ ha (by omega)
    omega
  -- Now derive contradiction from total x-degree equality.
  -- Σ_v d(inl v) = Σ_{v<v₀} d(inl v) + d(inl v₀) + Σ_{v>v₀} d(inl v)
  -- = 0 + d(inl v₀) + Σ_{v>v₀} d(inl v)  [using h_below]
  -- Σ_v d'(inl v) = Σ_{v<v₀} d'(inl v) + d'(inl v₀) + Σ_{v>v₀} d'(inl v)
  -- = Σ_{v<v₀} d'(inl v) + d'(inl v₀) + Σ_{v>v₀} d(inl v)  [using h_inl_hi]
  -- Equal: 0 + d(inl v₀) = Σ_{v<v₀} d'(inl v) + d'(inl v₀)
  -- Since d(inl v₀) < d'(inl v₀): 0 < Σ_{v<v₀} d'(inl v) + d'(inl v₀) - d(inl v₀) = 0 + Σ_{v<v₀} d'(inl v)
  -- Wait: d(inl v₀) + Σ_{v>v₀} d(inl v) = Σ_{v<v₀} d'(inl v) + d'(inl v₀) + Σ_{v>v₀} d(inl v)
  -- So d(inl v₀) = Σ_{v<v₀} d'(inl v) + d'(inl v₀)
  -- But d(inl v₀) < d'(inl v₀) ≤ Σ_{v<v₀} d'(inl v) + d'(inl v₀). Not a contradiction!
  -- The contradiction is: Σ_{v<v₀} d'(inl v) ≤ 0 (because d(inl v₀) < d'(inl v₀)):
  -- d(inl v₀) = Σ_{v<v₀} d'(inl v) + d'(inl v₀) → Σ_{v<v₀} d'(inl v) = d(inl v₀) - d'(inl v₀) < 0
  -- But Σ d'(inl v) ≥ 0. CONTRADICTION!
  -- Split Finset.univ into {v < v₀}, {v₀}, {v > v₀}
  -- Split Σ_v d(inl v) using Finset.add_sum_erase
  have hv₀_mem : v₀ ∈ (Finset.univ : Finset V) := Finset.mem_univ v₀
  rw [← Finset.add_sum_erase _ _ hv₀_mem] at h_total_xdeg
  rw [← Finset.add_sum_erase _ _ hv₀_mem] at h_total_xdeg
  -- h_total_xdeg : d(inl v₀) + Σ_{v≠v₀} d(inl v) = d'(inl v₀) + Σ_{v≠v₀} d'(inl v)
  -- For v ≠ v₀ in the d-sum: v < v₀ gives 0, v > v₀ gives d'(inl v)
  have h_erase_d : (Finset.univ.erase v₀).sum (fun v => d (Sum.inl v)) ≤
      (Finset.univ.erase v₀).sum (fun v => d' (Sum.inl v)) := by
    apply Finset.sum_le_sum
    intro v hv
    simp only [Finset.mem_erase] at hv
    rcases lt_or_gt_of_ne hv.1 with hlt | hgt
    · rw [h_below v hlt]; exact Nat.zero_le _
    · exact le_of_eq (h_inl_hi v hgt).symm
  -- From h_total_xdeg and h_erase_d and h_inl_v₀:
  -- d(inl v₀) + Σ_erase d = d'(inl v₀) + Σ_erase d'
  -- Σ_erase d ≤ Σ_erase d'
  -- d(inl v₀) < d'(inl v₀)
  -- So d(inl v₀) + Σ_erase d < d'(inl v₀) + Σ_erase d'. Contradicts equality.
  omega

/-! ### Strengthened crossing: clean interval property -/

/-- **Clean crossing**: For nonzero `f ∈ J_G`, there exist `a < b` such that
`d(inl a) ≥ 1`, `d(inr b) ≥ 1`, and the open interval `(a, b)` has NO support in LM(f):
`∀ c, a < c → c < b → d(inl c) = 0 ∧ d(inr c) = 0`.

This strengthens `exists_crossing_of_mem` by choosing `a` maximal and `b` minimal
among the crossing pairs. -/
private lemma exists_clean_crossing (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G) (hf_ne : f ≠ 0) :
    ∃ a b : V, a < b ∧
      1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inl a) ∧
      1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inr b) ∧
      (∀ c : V, a < c → c < b →
        binomialEdgeMonomialOrder.degree f (Sum.inl c) = 0 ∧
        binomialEdgeMonomialOrder.degree f (Sum.inr c) = 0) := by
  -- First get any crossing
  obtain ⟨a₀, b₀, hab₀, ha₀, hb₀⟩ := exists_crossing_of_mem G f hf_mem hf_ne
  set d := binomialEdgeMonomialOrder.degree f
  -- Define A = {v : d(inl v) ≥ 1} and B = {v : d(inr v) ≥ 1}
  -- Pick a = max{v ∈ A : ∃ w ∈ B, v < w}
  -- Pick b = min{w ∈ B : a < w}
  -- The set of valid a's is nonempty (contains a₀)
  -- Use Finset operations since V is Fintype
  set A := Finset.univ.filter (fun v : V => 1 ≤ d (Sum.inl v))
  set B := Finset.univ.filter (fun v : V => 1 ≤ d (Sum.inr v))
  -- a₀ ∈ A and b₀ ∈ B with a₀ < b₀
  have ha₀_A : a₀ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha₀⟩
  have hb₀_B : b₀ ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb₀⟩
  -- Define the set of valid a-values: those in A with some element of B above them
  set validA := A.filter (fun v => B.filter (fun w => v < w) |>.Nonempty)
  have hvalidA_ne : validA.Nonempty := by
    refine ⟨a₀, Finset.mem_filter.mpr ⟨ha₀_A, ⟨b₀, Finset.mem_filter.mpr ⟨hb₀_B, hab₀⟩⟩⟩⟩
  -- Pick a = max of validA
  set a := validA.max' hvalidA_ne
  have ha_mem : a ∈ validA := Finset.max'_mem validA hvalidA_ne
  have ha_A : a ∈ A := (Finset.mem_filter.mp ha_mem).1
  have ha_max : ∀ v ∈ validA, v ≤ a := fun v hv => Finset.le_max' validA v hv
  have ha_pos : 1 ≤ d (Sum.inl a) := (Finset.mem_filter.mp ha_A).2
  -- There exists some b' ∈ B with a < b'
  obtain ⟨b', hb'_mem⟩ := (Finset.mem_filter.mp ha_mem).2
  have hb'_B : b' ∈ B := (Finset.mem_filter.mp hb'_mem).1
  have hab' : a < b' := (Finset.mem_filter.mp hb'_mem).2
  -- Define Babove = {w ∈ B : a < w}, pick b = min
  set Babove := B.filter (fun w => a < w)
  have hBabove_ne : Babove.Nonempty := ⟨b', Finset.mem_filter.mpr ⟨hb'_B, hab'⟩⟩
  set b := Babove.min' hBabove_ne
  have hb_mem : b ∈ Babove := Finset.min'_mem Babove hBabove_ne
  have hb_B : b ∈ B := (Finset.mem_filter.mp hb_mem).1
  have hab : a < b := (Finset.mem_filter.mp hb_mem).2
  have hb_min : ∀ w ∈ Babove, b ≤ w := fun w hw => Finset.min'_le Babove w hw
  have hb_pos : 1 ≤ d (Sum.inr b) := (Finset.mem_filter.mp hb_B).2
  -- Clean interval: for c with a < c < b, c ∉ A and c ∉ B
  have hclean : ∀ c : V, a < c → c < b →
      d (Sum.inl c) = 0 ∧ d (Sum.inr c) = 0 := by
    intro c hac hcb
    constructor
    · -- d(inl c) = 0: if d(inl c) ≥ 1, then c ∈ A and c ∈ validA (since b > c and b ∈ B)
      by_contra hc_pos
      push_neg at hc_pos
      have hc_A : c ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hc_valid : c ∈ validA := Finset.mem_filter.mpr ⟨hc_A,
        ⟨b, Finset.mem_filter.mpr ⟨hb_B, hcb⟩⟩⟩
      -- c ≤ a by maximality of a, but a < c: contradiction
      exact absurd (ha_max c hc_valid) (not_le.mpr hac)
    · -- d(inr c) = 0: if d(inr c) ≥ 1, then c ∈ B and c ∈ Babove (since a < c)
      by_contra hc_pos
      push_neg at hc_pos
      have hc_B : c ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
      have hc_above : c ∈ Babove := Finset.mem_filter.mpr ⟨hc_B, hac⟩
      -- b ≤ c by minimality of b, but c < b: contradiction
      exact absurd (hb_min c hc_above) (not_le.mpr hcb)
  exact ⟨a, b, hab, ha_pos, hb_pos, hclean⟩

/-! ### Edge crossing from representation

The key insight: for nonzero `f ∈ J_G`, LM(f) must have a crossing at some EDGE of G.
This follows from analyzing the coefficient of LM(f) in the representation `f = Σ qₑ fₑ`. -/

/-- Helper: `fij(i,j)` for an edge with `i < j` has degree `≤ d` when `d` has the crossing. -/
private lemma fij_degree_le_of_crossing (i j : V) (hij : i < j)
    (d : BinomialEdgeVars V →₀ ℕ)
    (hi : 1 ≤ d (Sum.inl i)) (hj : 1 ≤ d (Sum.inr j)) :
    binomialEdgeMonomialOrder.degree (fij (K := K) i j) ≤ d := by
  rw [fij_degree (K := K) i j hij]
  intro w
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rcases w with v | v
  · -- w = Sum.inl v
    have h1 : (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inl v := Sum.inr_ne_inl
    simp only [h1, ite_false, add_zero]
    by_cases hvi : i = v
    · subst hvi; simp; exact hi
    · simp [show (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inl v from
        fun h => hvi (Sum.inl.inj h)]
  · -- w = Sum.inr v
    have h1 : (Sum.inl i : BinomialEdgeVars V) ≠ Sum.inr v := Sum.inl_ne_inr
    simp only [h1, ite_false, zero_add]
    by_cases hvj : j = v
    · subst hvj; simp; exact hj
    · simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr v from
        fun h => hvj (Sum.inr.inj h)]

/-! ### Variable restriction: killing variables outside a vertex set

If f ∈ J_G and f doesn't use variables at vertices in some set S,
then f is in the sub-ideal generated by edges with both endpoints outside S. -/

/-- The ring homomorphism that kills variables at vertices in a set S:
sends x_v, y_v to 0 for v ∈ S, keeps x_v, y_v for v ∉ S. -/
private noncomputable def killVars (S : Set V) [DecidablePred (· ∈ S)] :
    MvPolynomial (BinomialEdgeVars V) K →ₐ[K] MvPolynomial (BinomialEdgeVars V) K :=
  MvPolynomial.aeval (fun v =>
    if collapse v ∈ S then 0 else MvPolynomial.X v)

/-- killVars sends generators with an endpoint in S to 0. -/
private lemma killVars_generator_eq_zero (S : Set V) [DecidablePred (· ∈ S)]
    (i j : V) (hi : i ∈ S ∨ j ∈ S) :
    killVars (K := K) S (x i * y j - x j * y i) = 0 := by
  simp only [killVars, map_sub, map_mul, MvPolynomial.aeval_X, x, y, collapse, Sum.elim_inl,
    Sum.elim_inr, id]
  rcases hi with hi | hj
  · simp [if_pos hi]
  · simp [if_pos hj]

/-- killVars fixes generators with both endpoints outside S. -/
private lemma killVars_generator_eq_self (S : Set V) [DecidablePred (· ∈ S)]
    (i j : V) (hi : i ∉ S) (hj : j ∉ S) :
    killVars (K := K) S (x i * y j - x j * y i) = x i * y j - x j * y i := by
  simp only [killVars, map_sub, map_mul, MvPolynomial.aeval_X, x, y, collapse, Sum.elim_inl,
    Sum.elim_inr, id, if_neg hi, if_neg hj]

/-- For f ∈ J_G, killVars S f is in the sub-ideal generated by edges outside S. -/
private lemma killVars_mem_subideal (G : SimpleGraph V) (S : Set V) [DecidablePred (· ∈ S)]
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) :
    killVars S f ∈ Ideal.span
      {g : MvPolynomial (BinomialEdgeVars V) K |
        ∃ i j, G.Adj i j ∧ i < j ∧ i ∉ S ∧ j ∉ S ∧ g = x i * y j - x j * y i} := by
  -- killVars is an algebra hom, so it maps the ideal into the image ideal
  -- The image of each generator is either 0 (endpoint in S) or itself (both outside S)
  set T := {g : MvPolynomial (BinomialEdgeVars V) K |
    ∃ i j, G.Adj i j ∧ i < j ∧ i ∉ S ∧ j ∉ S ∧ g = x i * y j - x j * y i}
  -- killVars maps J_G into span T via the algebra hom property
  suffices h : binomialEdgeIdeal (K := K) G ≤
      (Ideal.span T).comap (killVars S).toRingHom by
    exact h hf
  rw [show binomialEdgeIdeal (K := K) G = Ideal.span
      {g | ∃ i j, G.Adj i j ∧ i < j ∧ g = x i * y j - x j * y i} from rfl]
  apply Ideal.span_le.mpr
  intro g ⟨i, j, hadj, hij, hg_eq⟩
  show (killVars S).toRingHom g ∈ Ideal.span T
  rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, hg_eq]
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
  · rw [killVars_generator_eq_zero S i j (Or.inl hi)]; exact Ideal.zero_mem _
  · rw [killVars_generator_eq_zero S i j (Or.inl hi)]; exact Ideal.zero_mem _
  · rw [killVars_generator_eq_zero S i j (Or.inr hj)]; exact Ideal.zero_mem _
  · rw [killVars_generator_eq_self S i j hi hj]
    exact Ideal.subset_span ⟨i, j, hadj, hij, hi, hj, rfl⟩

/-- For collapse-homogeneous `f ∈ J_G` where all monomials have zero collapse weight
at vertices in S, killVars S fixes f. -/
private lemma killVars_eq_self_of_collapse_zero (S : Set V) [DecidablePred (· ∈ S)]
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hsupp : ∀ d ∈ f.support, ∀ v ∈ S, d (Sum.inl v) = 0 ∧ d (Sum.inr v) = 0) :
    killVars (K := K) S f = f := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  simp only [map_sum]
  conv_rhs => rw [← MvPolynomial.support_sum_monomial_coeff f]
  apply Finset.sum_congr rfl
  intro d hd
  -- Show: killVars S (monomial d (coeff d f)) = monomial d (coeff d f)
  show MvPolynomial.aeval _ ((MvPolynomial.monomial d) (MvPolynomial.coeff d f)) =
    (MvPolynomial.monomial d) (MvPolynomial.coeff d f)
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod]
  simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, MvPolynomial.C_mul']
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have hv_pos : 0 < d v := Finsupp.mem_support_iff.mp hv |>.bot_lt
  simp only [killVars, collapse, id, MvPolynomial.aeval_X]
  rcases v with w | w <;> simp only [Sum.elim_inl, Sum.elim_inr]
  · by_cases hw : w ∈ S
    · exact absurd (hsupp d hd w hw).1 (by omega)
    · simp [if_neg hw]
  · by_cases hw : w ∈ S
    · exact absurd (hsupp d hd w hw).2 (by omega)
    · simp [if_neg hw]

/-- For collapse-homogeneous f with clean crossing (a,b), f is in the sub-ideal
of edges outside (a,b). Uses killVars_eq_self + killVars_mem_subideal. -/
private lemma clean_crossing_subideal (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G)
    (hsupp : ∀ d ∈ f.support, ∀ v : V, a < v → v < b →
        d (Sum.inl v) = 0 ∧ d (Sum.inr v) = 0) :
    f ∈ Ideal.span {g : MvPolynomial (BinomialEdgeVars V) K |
      ∃ i j, G.Adj i j ∧ i < j ∧ ¬(a < i ∧ i < b) ∧ ¬(a < j ∧ j < b) ∧
      g = x i * y j - x j * y i} := by
  have hfix : killVars (K := K) {v : V | a < v ∧ v < b} f = f := by
    apply killVars_eq_self_of_collapse_zero
    intro d hd v ⟨hav, hvb⟩
    exact hsupp d hd v hav hvb
  rw [← hfix]
  exact killVars_mem_subideal G {v | a < v ∧ v < b} f hf_mem

/-- **Walk existence from sub-ideal membership**: If f is in the sub-ideal of edges
outside an interval (a,b), f ≠ 0, and LM(f) has x_a and y_b support, then there
exists a walk from a to b in G using only vertices outside (a,b).

This is the graph-connectivity argument: the edges generating the sub-ideal
connect a to b through vertices outside (a,b). -/
private lemma exists_walk_outside_interval (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (a b : V) (hab : a < b)
    (ha : 1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inl a))
    (hb : 1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inr b))
    (hf_sub : f ∈ Ideal.span {g : MvPolynomial (BinomialEdgeVars V) K |
      ∃ i j, G.Adj i j ∧ i < j ∧ ¬(a < i ∧ i < b) ∧ ¬(a < j ∧ j < b) ∧
      g = x i * y j - x j * y i})
    (hf_ne : f ≠ 0) :
    ∃ π : List V, π.head? = some a ∧ π.getLast? = some b ∧ π.Nodup ∧
      (∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v) ∧
      π.Chain' (fun u v => G.Adj u v) := by
  sorry

/-- **Degree bound for admissible path from walk**: Given a walk from a to b with
the vertex condition, and the LM support information, there exists an admissible path
whose groebnerElement degree ≤ LM(f). -/
private lemma exists_groebnerElement_from_walk (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (a b : V) (hab : a < b)
    (ha : 1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inl a))
    (hb : 1 ≤ binomialEdgeMonomialOrder.degree f (Sum.inr b))
    (π : List V) (hHead : π.head? = some a) (hLast : π.getLast? = some b)
    (hND : π.Nodup) (hVtx : ∀ v ∈ π, v = a ∨ v = b ∨ v < a ∨ b < v)
    (hWalk : π.Chain' (fun u v => G.Adj u v)) :
    ∃ g ∈ groebnerBasisSet (K := K) G,
      binomialEdgeMonomialOrder.degree g ≤ binomialEdgeMonomialOrder.degree f := by
  sorry

private lemma exists_groebnerElement_degree_le (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ binomialEdgeIdeal G) (hf_ne : f ≠ 0) :
    ∃ g ∈ groebnerBasisSet (K := K) G,
      binomialEdgeMonomialOrder.degree g ≤ binomialEdgeMonomialOrder.degree f := by
  -- Step 1: Take collapse-homogeneous component f_m with same LM
  set d := binomialEdgeMonomialOrder.degree f
  set m := Finsupp.weight (collapseWeight (V := V)) d
  set f_m := MvPolynomial.weightedHomogeneousComponent (collapseWeight (V := V)) m f
  have hfm_mem : f_m ∈ binomialEdgeIdeal (K := K) G := collapseComponent_mem G f hf_mem m
  have hfm_ne : f_m ≠ 0 := by
    intro h
    have hcoeff_ne : f.coeff d ≠ 0 :=
      binomialEdgeMonomialOrder.coeff_degree_ne_zero_iff.mpr hf_ne
    have hcoeff_eq : f_m.coeff d = f.coeff d := by
      show (MvPolynomial.weightedHomogeneousComponent (collapseWeight (V := V)) m f).coeff d =
        f.coeff d
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl]
    rw [h, MvPolynomial.coeff_zero] at hcoeff_eq
    exact hcoeff_ne hcoeff_eq.symm
  -- f_m has same LM as f
  have hfm_degree : binomialEdgeMonomialOrder.degree f_m = d := by
    -- d ∈ supp(f_m) since coeff(f_m, d) = coeff(f, d) ≠ 0
    have hcoeff_ne : f.coeff d ≠ 0 :=
      binomialEdgeMonomialOrder.coeff_degree_ne_zero_iff.mpr hf_ne
    have hd_supp : d ∈ f_m.support := by
      rw [MvPolynomial.mem_support_iff]
      show (MvPolynomial.weightedHomogeneousComponent (collapseWeight (V := V)) m f).coeff d ≠ 0
      rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl]
      exact hcoeff_ne
    -- All monomials of f_m are ≤ d in lex (since they're in supp(f))
    have hle : ∀ e ∈ f_m.support, e ≼[binomialEdgeMonomialOrder] d := by
      intro e he
      have he_f : e ∈ f.support := by
        rw [MvPolynomial.mem_support_iff] at he ⊢
        have := he
        rw [show f_m = MvPolynomial.weightedHomogeneousComponent _ m f from rfl,
            MvPolynomial.coeff_weightedHomogeneousComponent] at this
        split_ifs at this with hw
        · exact this
        · exact absurd rfl this
      exact binomialEdgeMonomialOrder.le_degree he_f
    have h1 : binomialEdgeMonomialOrder.degree f_m ≼[binomialEdgeMonomialOrder] d :=
      hle _ (binomialEdgeMonomialOrder.degree_mem_support hfm_ne)
    have h2 : d ≼[binomialEdgeMonomialOrder] binomialEdgeMonomialOrder.degree f_m :=
      binomialEdgeMonomialOrder.le_degree hd_supp
    exact binomialEdgeMonomialOrder.toSyn.injective (le_antisymm h1 h2)
  -- Step 2: Get a clean crossing (a, b) for f
  obtain ⟨a, b, hab, ha, hb, hclean⟩ := exists_clean_crossing G f hf_mem hf_ne
  -- All monomials of f_m have zero collapse weight at vertices in (a,b)
  have hfm_supp : ∀ e ∈ f_m.support, ∀ v : V, a < v → v < b →
      e (Sum.inl v) = 0 ∧ e (Sum.inr v) = 0 := by
    intro e he v hav hvb
    -- e ∈ support of weightedHomogeneousComponent m f means weight(e) = m
    have he_weight : Finsupp.weight (collapseWeight (V := V)) e = m := by
      have he_coeff := MvPolynomial.mem_support_iff.mp he
      rw [show f_m = MvPolynomial.weightedHomogeneousComponent _ m f from rfl,
          MvPolynomial.coeff_weightedHomogeneousComponent] at he_coeff
      split_ifs at he_coeff with hw
      · exact hw
      · exact absurd rfl he_coeff
    -- m(v) = d(inl v) + d(inr v) = 0 for v ∈ (a,b)
    have hcv := hclean v hav hvb
    have hm_v : m v = 0 := by
      show (Finsupp.weight (collapseWeight (V := V)) d) v = 0
      rw [weight_collapseWeight_eq_mapDomain, mapDomain_collapse_apply]
      have := hcv.1; have := hcv.2; simp only [d] at *; omega
    -- weight(e)(v) = e(inl v) + e(inr v) = m(v) = 0
    have he_v : e (Sum.inl v) + e (Sum.inr v) = 0 := by
      have := Finsupp.ext_iff.mp he_weight v
      rw [weight_collapseWeight_eq_mapDomain, mapDomain_collapse_apply] at this
      linarith [hm_v]
    exact ⟨by omega, by omega⟩
  -- Step 3: f_m is in the sub-ideal of edges outside (a, b)
  have hfm_sub := clean_crossing_subideal G f_m hfm_mem hfm_supp (a := a) (b := b)
  -- Step 4: Walk from a to b outside (a, b), using f_m
  have ha' : 1 ≤ binomialEdgeMonomialOrder.degree f_m (Sum.inl a) := hfm_degree ▸ ha
  have hb' : 1 ≤ binomialEdgeMonomialOrder.degree f_m (Sum.inr b) := hfm_degree ▸ hb
  obtain ⟨π, hHead, hLast, hND, hVtx, hWalk⟩ :=
    exists_walk_outside_interval G f_m a b hab ha' hb' hfm_sub hfm_ne
  -- Step 5: Extract groebnerElement with degree bound
  exact exists_groebnerElement_from_walk G f a b hab ha hb π hHead hLast hND hVtx hWalk

/-- Any element of `J_G` reduces to remainder 0 modulo `groebnerBasisSet`.
Follows from `exists_groebnerElement_degree_le` (Rauh's core claim) +
`exists_isRemainder` + irredundancy. -/
private lemma isRemainder_of_mem_ideal (G : SimpleGraph V)
    (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf_mem : f ∈ Ideal.span (groebnerBasisSet (K := K) G)) :
    binomialEdgeMonomialOrder.IsRemainder f (groebnerBasisSet (K := K) G) 0 := by
  have hUnit : ∀ g ∈ groebnerBasisSet (K := K) G,
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g hg; obtain ⟨i, j, π, hπ, rfl⟩ := hg
    exact groebnerElement_leadingCoeff_isUnit i j π hπ
  -- Get some remainder r via the division algorithm
  obtain ⟨r, ⟨⟨coeff, hsum, hdeg⟩, hirr⟩⟩ :=
    binomialEdgeMonomialOrder.exists_isRemainder hUnit f
  -- It suffices to show r = 0
  suffices hr_zero : r = 0 by
    subst hr_zero; exact ⟨⟨coeff, by simpa using hsum, hdeg⟩, by simpa using hirr⟩
  by_contra r_ne
  -- r ∈ J_G: since f ∈ span(G) and the linear combination is in span(G)
  have hlin_mem : Finsupp.linearCombination _ (fun (b : ↥(groebnerBasisSet (K := K) G)) ↦
      b.val) coeff ∈ Ideal.span (groebnerBasisSet (K := K) G) := by
    simp only [Finsupp.linearCombination_apply]
    exact Submodule.sum_mem _ fun b _ =>
      Ideal.mul_mem_left _ _ (Ideal.subset_span b.prop)
  have hr_sub : f - Finsupp.linearCombination _ (fun (b : ↥(groebnerBasisSet (K := K) G)) ↦
      b.val) coeff ∈ Ideal.span (groebnerBasisSet (K := K) G) :=
    (Ideal.span (groebnerBasisSet (K := K) G)).sub_mem hf_mem hlin_mem
  have hr_eq : f - Finsupp.linearCombination _ (fun (b : ↥(groebnerBasisSet (K := K) G)) ↦
      b.val) coeff = r := by rw [hsum]; ring
  have hr_mem : r ∈ Ideal.span (groebnerBasisSet (K := K) G) := hr_eq ▸ hr_sub
  -- Apply the core claim: some groebnerElement's LT divides r's LT
  rw [← show binomialEdgeIdeal (K := K) G = Ideal.span (groebnerBasisSet (K := K) G) from
    (groebnerBasisSet_span G).symm] at hr_mem
  obtain ⟨ge, hge_mem, hge_div⟩ := exists_groebnerElement_degree_le G r hr_mem r_ne
  -- Contradiction: r's leading monomial is in its support but divisible by ge's LT
  exact hirr _ (binomialEdgeMonomialOrder.degree_mem_support r_ne) ge hge_mem hge_div

/-! ## Theorem 2.1: Gröbner basis -/

/--
**Theorem 2.1** (Herzog et al. 2010): The set
  `{ u_π · f_{ij} | i < j, π admissible path from i to j in G }`
is a Gröbner basis of `J_G` with respect to the lex monomial order
`x_1 > ⋯ > x_n > y_1 > ⋯ > y_n`.

The proof has three steps:
1. `groebnerBasisSet_span`: `Ideal.span groebnerBasisSet = J_G`.
2. **This theorem**: Buchberger's criterion — all S-polynomials reduce to 0.
3. `theorem_2_1_reduced`: No leading monomial divides another (reducedness).

Reference: Herzog et al. (2010), Theorem 2.1; Rauh (2013), Theorem 2.
-/
theorem theorem_2_1 (G : SimpleGraph V) :
    binomialEdgeMonomialOrder.IsGroebnerBasis
      (groebnerBasisSet (K := K) G) (binomialEdgeIdeal (K := K) G) := by
  rw [show binomialEdgeIdeal (K := K) G = Ideal.span (groebnerBasisSet (K := K) G) from
    (groebnerBasisSet_span G).symm]
  rw [isGroebnerBasis_iff_sPolynomial_isRemainder (hG := fun g hg => by
    obtain ⟨i, j, π, hπ, rfl⟩ := hg
    exact groebnerElement_leadingCoeff_isUnit i j π hπ)]
  intro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩
  exact isRemainder_of_mem_ideal G _
    (sPolynomial_mem_ideal (Ideal.subset_span he₁) (Ideal.subset_span he₂))

theorem theorem_2_1_leading (G : SimpleGraph V) (f : MvPolynomial (BinomialEdgeVars V) K)
    (hf : f ∈ binomialEdgeIdeal G) (hf0 : f ≠ 0) :
    -- The leading term of f is divisible by some leading term in the basis set
    ∃ (i j : V) (π : List V) (_ : IsAdmissiblePath G i j π),
      binomialEdgeMonomialOrder.degree (groebnerElement (K := K) i j π) ≤
      binomialEdgeMonomialOrder.degree f := by
  -- Follows from theorem_2_1_groebner: the IsGroebnerBasis condition gives
  -- span(lt(I)) = span(lt(G)), so lt(f) ∈ span(lt(G)), and some basis element
  -- has leading monomial dividing lt(f).
  obtain ⟨_, hInitIdeal⟩ := theorem_2_1 (K := K) G
  -- lt(f) ∈ span(lt(binomialEdgeIdeal G))
  have hlt_mem : binomialEdgeMonomialOrder.leadingTerm f ∈
      Ideal.span (binomialEdgeMonomialOrder.leadingTerm ''
        ↑(binomialEdgeIdeal (K := K) G)) :=
    Ideal.subset_span ⟨f, hf, rfl⟩
  -- Rewrite using hGB: span(lt(I)) = span(lt(G))
  rw [hInitIdeal] at hlt_mem
  -- All groebnerBasisSet elements have unit leading coefficients
  have hG_units : ∀ g ∈ (groebnerBasisSet (K := K) G),
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g ⟨i, j, π, hπ, hge⟩
    rw [hge]; exact groebnerElement_leadingCoeff_isUnit i j π hπ
  -- Rewrite span(lt(G)) = span({monomial(deg g) 1 : g ∈ G})
  rw [span_leadingTerm_eq_span_monomial hG_units,
      ← Set.image_image (fun s => monomial s (1 : K)) binomialEdgeMonomialOrder.degree,
      mem_ideal_span_monomial_image] at hlt_mem
  -- degree f ∈ (leadingTerm f).support (since f ≠ 0)
  have hdeg_supp : binomialEdgeMonomialOrder.degree f ∈
      (binomialEdgeMonomialOrder.leadingTerm f).support := by
    simp only [MonomialOrder.leadingTerm]
    classical
    rw [support_monomial, if_neg (MonomialOrder.leadingCoeff_ne_zero_iff.mpr hf0)]
    exact Finset.mem_singleton_self _
  -- Extract: ∃ g ∈ groebnerBasisSet G, degree g ≤ degree f
  obtain ⟨si, ⟨g, hg_mem, rfl⟩, hle⟩ := hlt_mem _ hdeg_supp
  obtain ⟨i, j, π, hπ, rfl⟩ := hg_mem
  exact ⟨i, j, π, hπ, hle⟩

end

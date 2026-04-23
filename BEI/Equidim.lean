import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import BEI.ReducedHH
import toMathlib.Equidim.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Regular.RegularSequence
import toMathlib.QuotientDimension
import toMathlib.CohenMacaulay.Defs
import toMathlib.CohenMacaulay.Basic
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.TensorPolynomialAway
import toMathlib.PolynomialAwayTensor
import toMathlib.TensorLocalisation
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.MvPolynomial

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

noncomputable section

open MvPolynomial SimpleGraph

/-!
# Equidimensional surrogate theorems for binomial edge ideals

Uses `IsEquidimRing` from `toMathlib/Equidim/Defs.lean`, the local
equidimensional surrogate currently used in the BEI project.

This file carries:

- the local surrogate API (`IsEquidim`);
- the Herzog-Hibi bipartite graph setup used in the paper's Proposition 1.6;
- equidimensional surrogate results on the monomial side.

## Reference: Herzog et al. (2010), Section 1
-/

abbrev IsEquidim (R : Type*) [CommRing R] := IsEquidimRing R

/-- An integral domain is equidimensional: it has a unique minimal prime (⊥),
so the equidimensionality condition holds vacuously. -/
instance IsDomain.isEquidimRing {R : Type*} [CommRing R] [IsDomain R] :
    IsEquidimRing R where
  equidimensional P Q hP hQ := by
    have h := IsDomain.minimalPrimes_eq_singleton_bot (R := R)
    rw [h, Set.mem_singleton_iff] at hP hQ
    rw [hP, hQ]

/--
The additional condition from Proposition 1.6: whenever {i, j+1} and {j, k+1}
are edges with i < j < k then {i, k+1} is also an edge.

Stated for `Fin n` so that successor makes sense.
-/
def SatisfiesProp1_6Condition (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (i j k : Fin n) (hj : j.val + 1 < n) (hk : k.val + 1 < n),
    i < j → j < k →
    G.Adj i ⟨j.val + 1, hj⟩ →
    G.Adj j ⟨k.val + 1, hk⟩ →
    G.Adj i ⟨k.val + 1, hk⟩

/--
The three conditions of the Herzog–Hibi criterion for CM bipartite graphs,
translated back from the bipartite graph Γ to conditions on the original graph G.

In the proof of Proposition 1.6, the initial ideal `in_<(J_G)` is identified with the
edge ideal of a bipartite graph Γ on `{x₁,…,x_{n-1},y₁,…,y_{n-1}}` where
`{xᵢ, yⱼ} ∈ E(Γ)` iff `{i, j+1} ∈ E(G)` and `i ≤ j`. The three HH conditions are:

- (i)  **Diagonal**: `{xᵢ, yᵢ}` is an edge for all `i`, i.e., `G.Adj i (i+1)`.
- (ii) **Upper triangularity**: if `{xᵢ, yⱼ}` is an edge then `i ≤ j`.
       Automatic from the orientation `i < j+1`.
- (iii) **Transitivity**: if `{xᵢ, yⱼ}` and `{xⱼ, yₖ}` are edges then `{xᵢ, yₖ}` is.
        This is exactly `SatisfiesProp1_6Condition`.

Reference: Herzog, Hibi (2005); used in Herzog et al. (2010), Proposition 1.6.
-/
structure HerzogHibiConditions (n : ℕ) (G : SimpleGraph (Fin n)) : Prop where
  /-- Condition (i): consecutive vertices are adjacent (diagonal edges of Γ). -/
  diagonal : ∀ (i : Fin n) (hi : i.val + 1 < n), G.Adj i ⟨i.val + 1, hi⟩
  /-- Condition (iii): the transitivity property (= Prop 1.6 hypothesis). -/
  transitivity : SatisfiesProp1_6Condition n G

/--
Under the hypotheses of Proposition 1.6, the associated bipartite graph Γ satisfies
all three conditions of the Herzog–Hibi criterion.

This is the graph-combinatorial content of the paper's reduction. The diagonal
condition (i) follows from `closedGraph_adj_consecutive` (Proposition 1.4),
and the transitivity condition (iii) is exactly the hypothesis.
Condition (ii) (upper triangularity, `i ≤ j`) is built into
`bipartiteEdgeMonomialIdeal` and verified by `rename_yPredVar_monomialInitialIdeal`. -/
theorem prop_1_6_herzogHibi (n : ℕ) (G : SimpleGraph (Fin n))
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    HerzogHibiConditions n G :=
  ⟨fun i hi => closedGraph_adj_consecutive hClosed hConn i hi, hCond⟩

/-- Example 1.7(a), formalized at the equidimensional surrogate level:
the complete graph quotient is a domain, hence equidimensional. -/
theorem complete_isEquidim (n : ℕ) :
    IsEquidim
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
       binomialEdgeIdeal (⊤ : SimpleGraph (Fin n))) := by
  -- P_∅(K_n) ≤ J_{K_n}: every SameComponent minor is an edge in K_n
  have hP0_le : primeComponent (K := K) (⊤ : SimpleGraph (Fin n)) ∅ ≤
      binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin n)) := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_union, Set.mem_setOf_eq] at hf
    rcases hf with ⟨i, hi, _⟩ | ⟨j, k, hjk, _, rfl⟩
    · exact absurd hi (Finset.notMem_empty i)
    · exact Ideal.subset_span ⟨j, k, (top_adj j k).mpr (ne_of_lt hjk), hjk, rfl⟩
  -- J_{K_n} = P_∅(K_n), and P_∅ is prime
  rw [show binomialEdgeIdeal (K := K) (⊤ : SimpleGraph (Fin n)) =
      primeComponent (K := K) (⊤ : SimpleGraph (Fin n)) ∅ from
    le_antisymm (binomialEdgeIdeal_le_primeComponent (⊤ : SimpleGraph (Fin n)) ∅) hP0_le]
  haveI := primeComponent_isPrime (K := K) (⊤ : SimpleGraph (Fin n)) ∅
  exact inferInstance

-- Example 1.7(b) (`path_isEquidim`) is proved in PrimeDecompositionDimension.lean
-- where the dimension formula and minimal prime characterization are available.

/-! ## Initial ideal description for closed graphs (algebraic side of Prop 1.6) -/

open MonomialOrder in
/-- Helper: the monomial `monomial (single a 1 + single b 1) 1` equals `X a * X b`. -/
private lemma monomial_pair_eq_X_mul_X
    {V : Type*} {K : Type*} [CommSemiring K] (a b : BinomialEdgeVars V) :
    (monomial (Finsupp.single a 1 + Finsupp.single b 1) (1 : K) :
     MvPolynomial (BinomialEdgeVars V) K) = X a * X b := by
  change _ = monomial (Finsupp.single a 1) 1 * monomial (Finsupp.single b 1) 1
  rw [monomial_mul, mul_one]

/-- The **monomial initial ideal** of `binomialEdgeIdeal G`: the ideal generated by
    the leading monomials `x_i · y_j` for edges `{i,j}` with `i < j`.

    For closed graphs, this equals the leading-term ideal `in_<(J_G)` —
    see `initialIdeal_closed_eq`. -/
def monomialInitialIdeal (G : SimpleGraph V) :
    Ideal (MvPolynomial (BinomialEdgeVars V) K) :=
  Ideal.span { m | ∃ i j : V, G.Adj i j ∧ i < j ∧ m = X (Sum.inl i) * X (Sum.inr j) }

omit [DecidableEq V] in
open MonomialOrder in
/-- For a closed graph G, the leading-term ideal of `J_G` equals the monomial
    initial ideal `⟨x_i y_j : {i,j} ∈ E(G), i < j⟩`.

    Consequence of Theorem 1.1 (`closed_implies_groebner`) and the leading monomial
    computation `fij_degree`. -/
theorem initialIdeal_closed_eq (G : SimpleGraph V) (hClosed : IsClosedGraph G) :
    Ideal.span (binomialEdgeMonomialOrder.leadingTerm ''
      ↑(binomialEdgeIdeal (K := K) G)) =
    monomialInitialIdeal (K := K) G := by
  classical
  -- The quadratic generators form a Gröbner basis (Theorem 1.1)
  have hGB := closed_implies_groebner (K := K) G hClosed
  -- Extract: span(lt(I)) = span(lt(generators))
  rw [hGB.2]
  -- All generators have unit leading coefficients
  have hGenUnit : ∀ g ∈ generatorSet (K := K) G,
      IsUnit (binomialEdgeMonomialOrder.leadingCoeff g) := by
    intro g hg; obtain ⟨i, j, _, hij, rfl⟩ := hg
    exact fij_leadingCoeff_isUnit i j hij
  -- Convert leading terms to monomials
  rw [span_leadingTerm_eq_span_monomial hGenUnit]
  -- Show the monomial images of generatorSet = generators of monomialInitialIdeal
  unfold monomialInitialIdeal
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro m ⟨f, ⟨i, j, hadj, hij, rfl⟩, rfl⟩
    apply Ideal.subset_span
    refine ⟨i, j, hadj, hij, ?_⟩
    -- Beta-reduce and unfold fij to apply fij_degree
    change monomial (binomialEdgeMonomialOrder.degree (fij i j)) 1 = _
    rw [fij_degree i j hij]; exact monomial_pair_eq_X_mul_X _ _
  · apply Ideal.span_le.mpr
    rintro m ⟨i, j, hadj, hij, rfl⟩
    apply Ideal.subset_span
    refine ⟨fij i j, ⟨i, j, hadj, hij, rfl⟩, ?_⟩
    change monomial (binomialEdgeMonomialOrder.degree (fij i j)) 1 = _
    rw [fij_degree i j hij]; exact monomial_pair_eq_X_mul_X _ _

/-! ## The y-predecessor variable shift (Proposition 1.6 proof) -/

/-- Cyclic y-predecessor on BEI variables: `x_i ↦ x_i`, `y_j ↦ y_{(j-1) mod n}`.
    This is the automorphism `φ` from the proof of Proposition 1.6 in Herzog et al. -/
def yPredVar (n : ℕ) (hn : 0 < n) : BinomialEdgeVars (Fin n) → BinomialEdgeVars (Fin n)
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr ⟨(j.val + n - 1) % n, Nat.mod_lt _ hn⟩

private lemma mod_pred {n : ℕ} (j : Fin n) (hj : 0 < j.val) :
    (j.val + n - 1) % n = j.val - 1 := by
  rw [show j.val + n - 1 = (j.val - 1) + n from by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The y-shift maps each generator `x_i · y_j` (with `i < j`) to `x_i · y_{j-1}`. -/
theorem rename_yPredVar_generator {n : ℕ} (hn : 0 < n) (i j : Fin n) (hij : i < j) :
    rename (yPredVar n hn)
      (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial (BinomialEdgeVars (Fin n)) K) =
    X (Sum.inl i) * X (Sum.inr (⟨j.val - 1, by omega⟩ : Fin n)) := by
  simp only [map_mul, rename_X, yPredVar]
  congr 2
  exact congrArg Sum.inr (Fin.ext (mod_pred j (by omega)))

/-! ## The bipartite edge monomial ideal -/

/-- The **bipartite edge monomial ideal** associated to `G`: generated by `x_i · y_j`
    where `{i, j+1} ∈ E(G)` and `i ≤ j`. This is the image of the monomial initial
    ideal under the y-predecessor shift `φ`, and corresponds to the edge ideal of the
    bipartite graph `Γ` from the proof of Proposition 1.6.

    The constraint `i ≤ j` (condition (ii) of the Herzog–Hibi criterion) is automatic
    from the construction: initial ideal generators have `i < j`, and after the shift
    `y_j ↦ y_{j-1}` we get `i ≤ j-1`. See `rename_yPredVar_monomialInitialIdeal`. -/
def bipartiteEdgeMonomialIdeal {n : ℕ} (G : SimpleGraph (Fin n)) :
    Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
  Ideal.span { m | ∃ (i j : Fin n) (hj : j.val + 1 < n),
    G.Adj i ⟨j.val + 1, by omega⟩ ∧ i ≤ j ∧ m = X (Sum.inl i) * X (Sum.inr j) }

/-! ## Bridge to the variable-pair ideal API -/

/-- The edge set of the Herzog–Hibi bipartite graph associated to `G`:
pairs `(Sum.inl i, Sum.inr j)` where `{i, j+1} ∈ E(G)` and `i ≤ j`. -/
def hhEdgeSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set (BinomialEdgeVars (Fin n) × BinomialEdgeVars (Fin n)) :=
  { e | ∃ (i j : Fin n) (_ : j.val + 1 < n),
    G.Adj i ⟨j.val + 1, by omega⟩ ∧ i ≤ j ∧
    e = (Sum.inl i, Sum.inr j) }

/-- The bipartite edge monomial ideal equals the variable-pair ideal of the
HH edge set. -/
theorem bipartiteEdgeMonomialIdeal_eq_variablePairIdeal {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    bipartiteEdgeMonomialIdeal (K := K) G =
      MvPolynomial.variablePairIdeal (R := K) (hhEdgeSet G) := by
  unfold bipartiteEdgeMonomialIdeal MvPolynomial.variablePairIdeal hhEdgeSet
  congr 1
  ext m
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, j, hj, hadj, hle, rfl⟩
    exact ⟨Sum.inl i, Sum.inr j, ⟨i, j, hj, hadj, hle, rfl⟩, rfl⟩
  · rintro ⟨a, b, ⟨i, j, hj, hadj, hle, heq⟩, rfl⟩
    obtain ⟨rfl, rfl⟩ := Prod.eq_iff_fst_eq_snd_eq.mp heq
    exact ⟨i, j, hj, hadj, hle, rfl⟩

/-- Minimal primes of the bipartite edge monomial ideal are exactly
`span (X '' S)` for minimal vertex covers of the HH edge set. -/
theorem minimalPrime_bipartiteEdgeMonomialIdeal_iff {n : ℕ}
    (G : SimpleGraph (Fin n))
    {P : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)} :
    P ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G) ↔
      ∃ S, MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S ∧
        P = Ideal.span (MvPolynomial.X '' S) := by
  rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
  exact MvPolynomial.minimalPrime_variablePairIdeal_iff

/-! ## Diagonal edges and minimal vertex cover properties under HH conditions -/

/-- Under HH conditions, diagonal edges `(Sum.inl i, Sum.inr i)` belong to the
HH edge set for each `i` with `i.val + 1 < n`. -/
theorem hhEdgeSet_diagonal {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n) :
    (Sum.inl i, Sum.inr i) ∈ hhEdgeSet G :=
  ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩

/-- In a minimal vertex cover, for each element `v ∈ S`, removing `v` uncovers
some edge. -/
private theorem minimalCover_remove_not_cover {σ : Type*}
    {edges : Set (σ × σ)}
    {S : Set σ}
    (hS : MvPolynomial.IsMinimalVertexCover edges S)
    {v : σ} (hv : v ∈ S) :
    ¬MvPolynomial.IsVertexCover edges (S \ {v}) := by
  intro hcover
  have hle : S ⊆ S \ {v} := hS.2 _ hcover Set.diff_subset
  exact (hle hv).2 (by simp)

/-- Under HH conditions, removing `Sum.inl i` from a minimal cover reveals an uncovered
edge `(Sum.inl i, Sum.inr j)` with `Sum.inr j ∉ S`. -/
private theorem remove_inl_uncovers {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S)
    {i : Fin n} (hxi : Sum.inl i ∈ S) :
    ∃ (j : Fin n) (hj : j.val + 1 < n),
      G.Adj i ⟨j.val + 1, by omega⟩ ∧ i ≤ j ∧ Sum.inr j ∉ S := by
  have hnotcover := minimalCover_remove_not_cover hS hxi
  simp only [MvPolynomial.IsVertexCover, not_forall] at hnotcover
  obtain ⟨a, b, hab, hnot⟩ := hnotcover
  push_neg at hnot
  obtain ⟨ha_nd, hb_nd⟩ := hnot
  -- Destructure the edge, keeping the original membership
  obtain ⟨i', j, hj, hadj, hle, heq⟩ := hab
  have hai : a = Sum.inl i' := congrArg Prod.fst heq
  have hbj : b = Sum.inr j := congrArg Prod.snd heq
  -- Reconstruct edge membership for cover check
  have hab' : (a, b) ∈ hhEdgeSet G := heq ▸ ⟨i', j, hj, hadj, hle, rfl⟩
  -- Since S covers (a,b), one is in S. Since a,b ∉ S\{Sum.inl i}, one must be Sum.inl i.
  rcases hS.1 a b hab' with haS | hbS
  · -- a ∈ S but a ∉ S \ {Sum.inl i}, so a = Sum.inl i
    have : a = Sum.inl i := by
      by_contra hne; exact ha_nd ⟨haS, hne⟩
    have : i' = i := Sum.inl_injective (hai ▸ this)
    subst this
    have : Sum.inr j ∉ S := by
      intro hbS'; exact hb_nd ⟨hbj ▸ hbS', by rw [Set.mem_singleton_iff, hbj]; exact Sum.inr_ne_inl⟩
    exact ⟨j, hj, hadj, hle, this⟩
  · -- b ∈ S but b ∉ S \ {Sum.inl i}, so b = Sum.inl i
    -- But b = Sum.inr j, contradiction with Sum.inl
    have : b = Sum.inl i := by
      by_contra hne; exact hb_nd ⟨hbS, hne⟩
    exact absurd (hbj ▸ this : Sum.inr j = Sum.inl i) Sum.inr_ne_inl

/-- Under HH conditions, removing `Sum.inr i` from a minimal cover reveals an uncovered
edge `(Sum.inl j, Sum.inr i)` with `Sum.inl j ∉ S`. -/
private theorem remove_inr_uncovers {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S)
    {i : Fin n} (hyi : Sum.inr i ∈ S) :
    ∃ (j : Fin n) (hi' : i.val + 1 < n),
      G.Adj j ⟨i.val + 1, by omega⟩ ∧ j ≤ i ∧ Sum.inl j ∉ S := by
  have hnotcover := minimalCover_remove_not_cover hS hyi
  simp only [MvPolynomial.IsVertexCover, not_forall] at hnotcover
  obtain ⟨a, b, hab, hnot⟩ := hnotcover
  push_neg at hnot
  obtain ⟨ha_nd, hb_nd⟩ := hnot
  obtain ⟨i', j, hj, hadj, hle, heq⟩ := hab
  have hai : a = Sum.inl i' := congrArg Prod.fst heq
  have hbj : b = Sum.inr j := congrArg Prod.snd heq
  have hab' : (a, b) ∈ hhEdgeSet G := heq ▸ ⟨i', j, hj, hadj, hle, rfl⟩
  rcases hS.1 a b hab' with haS | hbS
  · have : a = Sum.inr i := by
      by_contra hne; exact ha_nd ⟨haS, hne⟩
    exact absurd (hai ▸ this : Sum.inl i' = Sum.inr i) Sum.inl_ne_inr
  · have : b = Sum.inr i := by
      by_contra hne; exact hb_nd ⟨hbS, hne⟩
    have : j = i := Sum.inr_injective (hbj ▸ this)
    subst this
    have : Sum.inl i' ∉ S := by
      intro haS'; exact ha_nd ⟨hai ▸ haS', by rw [Set.mem_singleton_iff, hai]; exact Sum.inl_ne_inr⟩
    exact ⟨i', hj, hadj, hle, this⟩

/-- Under HH conditions, any minimal vertex cover of `hhEdgeSet G` picks exactly one
element from each diagonal pair `{Sum.inl i, Sum.inr i}` for active indices `i`. -/
theorem minimalVertexCover_exactlyOne {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S)
    (i : Fin n) (hi : i.val + 1 < n) :
    Sum.inl i ∈ S ↔ Sum.inr i ∉ S := by
  constructor
  · -- Forward: both in S leads to contradiction via transitivity
    intro hxi hyi
    -- Removing Sum.inl i: ∃ j₁ with edge (i, j₁) and Sum.inr j₁ ∉ S
    obtain ⟨j₁, hj₁lt, hadj₁, hle₁, hj₁_notS⟩ := remove_inl_uncovers hS hxi
    have hj₁_ne : j₁ ≠ i := fun h => hj₁_notS (h ▸ hyi)
    have hj₁_gt : i < j₁ := lt_of_le_of_ne hle₁ (Ne.symm hj₁_ne)
    -- Removing Sum.inr i: ∃ i₂ with edge (i₂, i) and Sum.inl i₂ ∉ S
    obtain ⟨i₂, _, hadj₂, hle₂, hi₂_notS⟩ := remove_inr_uncovers hS hyi
    have hi₂_ne : i₂ ≠ i := fun h => hi₂_notS (h ▸ hxi)
    have hi₂_lt : i₂ < i := lt_of_le_of_ne hle₂ hi₂_ne
    -- By transitivity: G.Adj i₂ ⟨j₁.val + 1, _⟩
    have hadj_trans : G.Adj i₂ ⟨j₁.val + 1, by omega⟩ :=
      hHH.transitivity i₂ i j₁ hi hj₁lt hi₂_lt hj₁_gt hadj₂ hadj₁
    -- (Sum.inl i₂, Sum.inr j₁) ∈ hhEdgeSet G but neither endpoint is in S
    have hedge : (Sum.inl i₂, Sum.inr j₁) ∈ hhEdgeSet G :=
      ⟨i₂, j₁, hj₁lt, hadj_trans, le_of_lt (lt_trans hi₂_lt hj₁_gt), rfl⟩
    rcases hS.1 _ _ hedge with h | h
    · exact hi₂_notS h
    · exact hj₁_notS h
  · -- Backward: Sum.inr i ∉ S → Sum.inl i ∈ S (from the cover property on diagonal edge)
    intro hyi
    rcases hS.1 _ _ (hhEdgeSet_diagonal hHH i hi) with h | h
    · exact h
    · exact absurd h hyi

/-- Elements of a minimal vertex cover of `hhEdgeSet G` are exclusively `Sum.inl` or
`Sum.inr` of active indices (those with `i.val + 1 < n`). No HH conditions needed. -/
theorem minimalVertexCover_subset_active {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S)
    {v : BinomialEdgeVars (Fin n)} (hv : v ∈ S) :
    ∃ i : Fin n, (v = Sum.inl i ∨ v = Sum.inr i) ∧ i.val + 1 < n := by
  -- v ∈ S means removing v uncovers some edge in hhEdgeSet
  have hnotcover := minimalCover_remove_not_cover hS hv
  simp only [MvPolynomial.IsVertexCover, not_forall] at hnotcover
  obtain ⟨a, b, hab, hnot⟩ := hnotcover
  push_neg at hnot
  obtain ⟨ha_nd, hb_nd⟩ := hnot
  obtain ⟨i, j, hj, hadj, hle, heq⟩ := hab
  have hai : a = Sum.inl i := congrArg Prod.fst heq
  have hbj : b = Sum.inr j := congrArg Prod.snd heq
  have hab' : (a, b) ∈ hhEdgeSet G := heq ▸ ⟨i, j, hj, hadj, hle, rfl⟩
  rcases hS.1 a b hab' with haS | hbS
  · have : a = v := by by_contra hne; exact ha_nd ⟨haS, hne⟩
    exact ⟨i, Or.inl (hai ▸ this).symm, by omega⟩
  · have : b = v := by by_contra hne; exact hb_nd ⟨hbS, hne⟩
    exact ⟨j, Or.inr (hbj ▸ this).symm, hj⟩

/-- The index extraction function: given an element of a minimal vertex cover of
`hhEdgeSet G`, return the `Fin n` index it corresponds to. Elements are either
`Sum.inl i` or `Sum.inr i` for active `i` (with `i.val + 1 < n`). -/
private noncomputable def coverToIndex {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S) :
    S → Fin n := fun ⟨_, hv⟩ =>
  (minimalVertexCover_subset_active hS hv).choose

private theorem coverToIndex_spec {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S)
    (v : S) :
    ((v : BinomialEdgeVars (Fin n)) = Sum.inl (coverToIndex hS v) ∨
     (v : BinomialEdgeVars (Fin n)) = Sum.inr (coverToIndex hS v)) ∧
    (coverToIndex hS v).val + 1 < n :=
  (minimalVertexCover_subset_active hS v.2).choose_spec

/-- Under HH conditions, the index extraction `coverToIndex` is injective on any
minimal vertex cover. -/
private theorem coverToIndex_injective {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S) :
    Function.Injective (coverToIndex hS) := by
  intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
  -- Both v₁ and v₂ map to the same index i
  have hs₁ := coverToIndex_spec hS ⟨v₁, hv₁⟩
  have hs₂ := coverToIndex_spec hS ⟨v₂, hv₂⟩
  -- Replace coverToIndex hS ⟨v₂, hv₂⟩ with coverToIndex hS ⟨v₁, hv₁⟩ using heq
  rw [← heq] at hs₂
  set i := coverToIndex hS ⟨v₁, hv₁⟩
  -- By exactlyOne, exactly one of Sum.inl i, Sum.inr i is in S
  have hexact := minimalVertexCover_exactlyOne hHH hS i hs₁.2
  -- v₁ is Sum.inl i or Sum.inr i, v₂ is Sum.inl i or Sum.inr i
  -- Since exactly one of inl/inr is in S, they must be the same
  rcases hs₁.1 with h₁ | h₁ <;> rcases hs₂.1 with h₂ | h₂
  · exact Subtype.ext (h₁.trans h₂.symm)
  · exact absurd (h₂ ▸ hv₂) (hexact.mp (h₁ ▸ hv₁))
  · exact absurd (h₁ ▸ hv₁) (hexact.mp (h₂ ▸ hv₂))
  · exact Subtype.ext (h₁.trans h₂.symm)

/-- Under HH conditions, the index extraction `coverToIndex` has range exactly
`{i : Fin n | i.val + 1 < n}`. -/
private theorem coverToIndex_range {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S) :
    Set.range (coverToIndex hS) = {i : Fin n | i.val + 1 < n} := by
  ext i
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v, rfl⟩; exact (coverToIndex_spec hS v).2
  · intro hi
    -- One of Sum.inl i, Sum.inr i is in S
    rcases hS.1 _ _ (hhEdgeSet_diagonal hHH i hi) with h | h
    · refine ⟨⟨Sum.inl i, h⟩, ?_⟩
      show coverToIndex hS ⟨Sum.inl i, h⟩ = i
      have hs := coverToIndex_spec hS ⟨Sum.inl i, h⟩
      rcases hs.1 with hj | hj
      · exact (Sum.inl_injective hj).symm
      · exact absurd hj Sum.inl_ne_inr
    · refine ⟨⟨Sum.inr i, h⟩, ?_⟩
      show coverToIndex hS ⟨Sum.inr i, h⟩ = i
      have hs := coverToIndex_spec hS ⟨Sum.inr i, h⟩
      rcases hs.1 with hj | hj
      · exact absurd hj Sum.inr_ne_inl
      · exact (Sum.inr_injective hj).symm

/-- Under HH conditions, any two minimal vertex covers of `hhEdgeSet G`
have the same cardinality. -/
theorem minimalVertexCover_ncard_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {S T : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S)
    (hT : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) T) :
    S.ncard = T.ncard := by
  -- Both biject onto {i : Fin n | i.val + 1 < n} via coverToIndex
  -- Use: ncard s = Nat.card s for sets in a Fintype
  rw [← Nat.card_coe_set_eq S, ← Nat.card_coe_set_eq T]
  -- Show Nat.card S = Nat.card T by constructing S ≃ T via intermediate type
  -- Build S ≃ {i : Fin n // i.val + 1 < n}
  have hS_bij : Function.Bijective
      (fun v : S => (⟨coverToIndex hS v, (coverToIndex_spec hS v).2⟩ :
        {i : Fin n // i.val + 1 < n})) :=
    ⟨fun a b h => coverToIndex_injective hHH hS (Subtype.ext_iff.mp h),
     fun ⟨i, hi⟩ => by
      obtain ⟨v, hv⟩ := (coverToIndex_range hHH hS ▸ hi : i ∈ Set.range (coverToIndex hS))
      exact ⟨v, Subtype.ext hv⟩⟩
  have hT_bij : Function.Bijective
      (fun v : T => (⟨coverToIndex hT v, (coverToIndex_spec hT v).2⟩ :
        {i : Fin n // i.val + 1 < n})) :=
    ⟨fun a b h => coverToIndex_injective hHH hT (Subtype.ext_iff.mp h),
     fun ⟨i, hi⟩ => by
      obtain ⟨v, hv⟩ := (coverToIndex_range hHH hT ▸ hi : i ∈ Set.range (coverToIndex hT))
      exact ⟨v, Subtype.ext hv⟩⟩
  exact (Nat.card_eq_of_bijective _ hS_bij).trans (Nat.card_eq_of_bijective _ hT_bij).symm

/-! ## Equidimensionality of the bipartite edge monomial ideal -/

/-- Under HH conditions, any two minimal primes of `bipartiteEdgeMonomialIdeal G`
yield quotients of equal Krull dimension. This is the algebraic content of the
Herzog–Hibi CM criterion for the edge ideal of the bipartite graph Γ. -/
theorem bipartiteEdgeMonomialIdeal_equidimensional {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {P Q : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hP : P ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G))
    (hQ : Q ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G)) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ P) =
    ringKrullDim (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ Q) := by
  classical
  -- Extract minimal vertex covers S, T
  obtain ⟨S, hScover, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP
  obtain ⟨T, hTcover, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hQ
  -- All minimal vertex covers have the same cardinality
  have hncard : S.ncard = T.ncard := minimalVertexCover_ncard_eq hHH hScover hTcover
  -- Convert to Finset-based dimension comparison
  haveI : Fintype ↑S := Set.Finite.fintype (Set.toFinite S)
  haveI : Fintype ↑T := Set.Finite.fintype (Set.toFinite T)
  rw [show MvPolynomial.X '' S =
      (↑S.toFinset : Set _).image MvPolynomial.X from by rw [Set.coe_toFinset],
    show MvPolynomial.X '' T =
      (↑T.toFinset : Set _).image MvPolynomial.X from by rw [Set.coe_toFinset]]
  apply MvPolynomial.ringKrullDim_quotient_span_X_eq_of_card_eq
  rw [Set.ncard_eq_toFinset_card' S, Set.ncard_eq_toFinset_card' T] at hncard
  exact_mod_cast hncard

/-- Under HH conditions, the quotient by `bipartiteEdgeMonomialIdeal G` is
equidimensional in the local surrogate sense. -/
theorem bipartiteEdgeMonomialIdeal_isEquidim {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsEquidimRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
       bipartiteEdgeMonomialIdeal (K := K) G) where
  equidimensional P Q hP hQ := by
    -- Lift P, Q to minimal primes of the ideal in the ambient ring
    let mk := Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
    have hJmin : (P.comap mk) ∈ (bipartiteEdgeMonomialIdeal (K := K) G).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact Set.mem_image_of_mem _ hP
    have hJ'min : (Q.comap mk) ∈ (bipartiteEdgeMonomialIdeal (K := K) G).minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact Set.mem_image_of_mem _ hQ
    -- Third isomorphism theorem: (R/I)/(J/I) ≃ R/J
    conv_lhs => rw [show P = (P.comap mk).map mk from
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P).symm]
    conv_rhs => rw [show Q = (Q.comap mk).map mk from
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q).symm]
    rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJmin.1.2),
        ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJ'min.1.2)]
    exact bipartiteEdgeMonomialIdeal_equidimensional hHH hJmin hJ'min

/-! ## Regular elements for the Cohen–Macaulay path

Under HH conditions, each linear form `X (Sum.inl i) + X (Sum.inr i)` avoids every
minimal prime of `bipartiteEdgeMonomialIdeal G`.  Since the edge ideal is radical
(proved via `variablePairIdeal_isRadical` in `SquarefreeMonomialPrimes`), these linear
forms are non-zero-divisors on the quotient ring — the first step toward showing the
quotient is Cohen–Macaulay via a direct regular-sequence argument. -/

/-- Under HH conditions, `X (Sum.inl i) + X (Sum.inr i)` is not in any minimal
prime of the bipartite edge monomial ideal.

Each minimal prime is `span (X '' C)` for a minimal vertex cover `C`, and
`minimalVertexCover_exactlyOne` ensures `C` picks exactly one element from
each diagonal pair `{Sum.inl i, Sum.inr i}`.  Therefore the other variable
is free in the quotient `S / P`, and the sum maps to a nonzero variable. -/
theorem sum_X_not_mem_minimalPrime {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    {P : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hP : P ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G)) :
    X (Sum.inl i) + X (Sum.inr i) ∉ P := by
  -- Extract P = span(X '' C) for a minimal vertex cover C
  obtain ⟨C, hC, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP
  -- Under HH conditions, exactly one of Sum.inl i, Sum.inr i is in C
  have hexact := minimalVertexCover_exactlyOne hHH hC i hi
  -- Case split on which element of the diagonal pair is in C
  set S : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) := MvPolynomial.X '' C
  by_cases hxi : Sum.inl i ∈ C
  · -- Sum.inl i ∈ C, Sum.inr i ∉ C
    have hyi : Sum.inr i ∉ C := hexact.mp hxi
    intro hmem
    have hxi_mem : (X (Sum.inl i) : MvPolynomial _ K) ∈ Ideal.span S :=
      Ideal.subset_span ⟨Sum.inl i, hxi, rfl⟩
    have hyi_mem : (X (Sum.inr i) : MvPolynomial _ K) ∈ Ideal.span S := by
      have := (Ideal.span S).sub_mem hmem hxi_mem
      rwa [add_sub_cancel_left] at this
    exact hyi ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp hyi_mem)
  · -- Sum.inl i ∉ C, Sum.inr i ∈ C
    have hyi : Sum.inr i ∈ C := by
      rcases hC.1 _ _ (hhEdgeSet_diagonal hHH i hi) with h | h
      · exact absurd h hxi
      · exact h
    intro hmem
    have hyi_mem : (X (Sum.inr i) : MvPolynomial _ K) ∈ Ideal.span S :=
      Ideal.subset_span ⟨Sum.inr i, hyi, rfl⟩
    have hxi_mem : (X (Sum.inl i) : MvPolynomial _ K) ∈ Ideal.span S := by
      have := (Ideal.span S).sub_mem hmem hyi_mem
      rwa [add_sub_cancel_right] at this
    exact hxi ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp hxi_mem)

/-- The bipartite edge monomial ideal is radical, inherited from
`variablePairIdeal_isRadical` via the bridge
`bipartiteEdgeMonomialIdeal_eq_variablePairIdeal`. -/
theorem bipartiteEdgeMonomialIdeal_isRadical {n : ℕ} (G : SimpleGraph (Fin n)) :
    (bipartiteEdgeMonomialIdeal (K := K) G).IsRadical := by
  rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
  apply MvPolynomial.variablePairIdeal_isRadical
  intro a b hab
  obtain ⟨i, j, _, _, _, he⟩ := hab
  have := congr_arg Prod.fst he
  have := congr_arg Prod.snd he
  simp only [ne_eq] at *
  subst_vars
  exact Sum.inl_ne_inr

/-- Under HH conditions, `X (Sum.inl i) + X (Sum.inr i)` is a non-zero-divisor
on the quotient by the bipartite edge monomial ideal.

The proof uses three ingredients:
1. the edge ideal is radical (`bipartiteEdgeMonomialIdeal_isRadical`);
2. each minimal prime is a variable-generated prime from a minimal vertex cover;
3. the sum avoids every such prime (`sum_X_not_mem_minimalPrime`).

If `(x_i + y_i) · f ∈ I`, then `(x_i + y_i) · f ∈ P` for every minimal prime
`P` of `I`.  Since `P` is prime and `x_i + y_i ∉ P`, we get `f ∈ P`.  So
`f ∈ ⋂ P = radical(I) = I`. -/
theorem sum_XY_isSMulRegular {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl i) + X (Sum.inr i))) := by
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set ℓ : MvPolynomial (BinomialEdgeVars (Fin n)) K :=
    X (Sum.inl i) + X (Sum.inr i)
  set mk := Ideal.Quotient.mk I
  intro a b hab
  -- Lift to the polynomial ring
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  -- Convert smul hypothesis to ring multiplication
  simp only [smul_eq_mul] at hab
  -- hab : mk ℓ * mk a' = mk ℓ * mk b'
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at hab
  -- hab : ℓ * a' - ℓ * b' ∈ I
  rw [Ideal.Quotient.eq]
  -- Goal: a' - b' ∈ I. Show it's in radical(I) = I.
  have hdiff : ℓ * (a' - b') ∈ I := by rwa [mul_sub]
  suffices a' - b' ∈ I.radical by
    rwa [(bipartiteEdgeMonomialIdeal_isRadical (K := K) G).radical] at this
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  intro P ⟨hPI, hPprime⟩
  -- Get a minimal prime Q of I with Q ≤ P
  haveI := hPprime
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hPI
  -- ℓ * (a' - b') ∈ I ⊆ Q (since Q is a minimal prime containing I)
  have hmemQ : ℓ * (a' - b') ∈ Q := hQmin.1.2 hdiff
  -- ℓ ∉ Q (our combinatorial result)
  have hℓ_not_Q := sum_X_not_mem_minimalPrime (K := K) hHH i hi hQmin
  -- Q is prime, so a' - b' ∈ Q
  have hab_Q := (hQmin.1.1.mem_or_mem hmemQ).resolve_left hℓ_not_Q
  -- Q ≤ P, so a' - b' ∈ P
  exact hQP hab_Q

/-! ## Ideal-level transport: monomial initial ideal → bipartite edge ideal -/

/-- The y-predecessor shift `φ` transports the monomial initial ideal to the bipartite
    edge monomial ideal: `φ(monomialInitialIdeal G) = bipartiteEdgeMonomialIdeal G`.

    This is the ideal-level packaging of the per-generator transport
    `rename_yPredVar_generator`, using `Ideal.map_span` to lift from generators to ideals.

    The key correspondences are:
    - Forward: edge `{i, j}` with `i < j` gives generator `x_i y_j`; after shift,
      `x_i y_{j-1}` with `{i, (j-1)+1} = {i, j} ∈ E(G)` and `i ≤ j-1`.
    - Backward: generator `x_i y_j` with `{i, j+1} ∈ E(G)` and `i ≤ j` lifts to
      `x_i y_{j+1}` with `{i, j+1} ∈ E(G)` and `i < j+1`. -/
theorem rename_yPredVar_monomialInitialIdeal {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    Ideal.map (rename (yPredVar n hn)) (monomialInitialIdeal (K := K) G) =
    bipartiteEdgeMonomialIdeal (K := K) G := by
  unfold monomialInitialIdeal bipartiteEdgeMonomialIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · -- Forward: each image of a monomialInitialIdeal generator is a bipartite generator
    apply Ideal.span_le.mpr
    rintro m ⟨f, ⟨i, j, hadj, hij, rfl⟩, rfl⟩
    apply Ideal.subset_span
    set j' : Fin n := ⟨j.val - 1, by omega⟩
    have hj'v : j'.val = j.val - 1 := rfl
    have hj'_succ : j'.val + 1 < n := by omega
    have hj'_adj : G.Adj i ⟨j'.val + 1, hj'_succ⟩ := by
      rw [show (⟨j'.val + 1, hj'_succ⟩ : Fin n) = j from
        Fin.ext (by dsimp only; omega)]
      exact hadj
    have hj'_le : i ≤ j' := by change i.val ≤ j'.val; omega
    exact ⟨i, j', hj'_succ, hj'_adj, hj'_le, rename_yPredVar_generator hn i j hij⟩
  · -- Backward: each bipartite generator is an image of a monomialInitialIdeal generator
    apply Ideal.span_le.mpr
    rintro m ⟨i, j, hj, hadj, hij, rfl⟩
    apply Ideal.subset_span
    set j' : Fin n := ⟨j.val + 1, by omega⟩
    have hj'v : j'.val = j.val + 1 := rfl
    have hij' : i < j' := by change i.val < j'.val; omega
    have hj'_eq : (⟨j'.val - 1, by omega⟩ : Fin n) = j :=
      Fin.ext (by dsimp only; omega)
    refine ⟨X (Sum.inl i) * X (Sum.inr j'), ⟨i, j', hadj, hij', rfl⟩, ?_⟩
    rw [rename_yPredVar_generator hn i j' hij', hj'_eq]

/-! ## Equidimensionality transfer through ring isomorphism -/

/-- The local equidimensional surrogate transfers across ring isomorphisms. -/
theorem isEquidim_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (hEq : IsEquidimRing R) : IsEquidimRing S where
  equidimensional P Q hP hQ := by
    -- Pull back minimal primes of S to minimal primes of R
    have hP' : Ideal.comap e.toRingHom P ∈ minimalPrimes R := by
      have h := Ideal.minimal_primes_comap_of_surjective (f := e.toRingHom)
        e.surjective (I := ⊥) hP
      rwa [Ideal.comap_bot_of_injective e.toRingHom e.injective] at h
    have hQ' : Ideal.comap e.toRingHom Q ∈ minimalPrimes R := by
      have h := Ideal.minimal_primes_comap_of_surjective (f := e.toRingHom)
        e.surjective (I := ⊥) hQ
      rwa [Ideal.comap_bot_of_injective e.toRingHom e.injective] at h
    -- Quotient dimensions are preserved by the isomorphism
    have hPe : ringKrullDim (R ⧸ Ideal.comap e.toRingHom P) = ringKrullDim (S ⧸ P) :=
      ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv _ P e
          (Ideal.map_comap_of_surjective e.toRingHom e.surjective P).symm)
    have hQe : ringKrullDim (R ⧸ Ideal.comap e.toRingHom Q) = ringKrullDim (S ⧸ Q) :=
      ringKrullDim_eq_of_ringEquiv
        (Ideal.quotientEquiv _ Q e
          (Ideal.map_comap_of_surjective e.toRingHom e.surjective Q).symm)
    rw [← hPe, ← hQe]
    exact hEq.equidimensional _ _ hP' hQ'

/-! ## The y-predecessor variable equivalence -/

/-- The y-successor on BEI variables: inverse of `yPredVar`.
`x_i ↦ x_i`, `y_j ↦ y_{(j+1) mod n}`. -/
private def ySuccVar (n : ℕ) (hn : 0 < n) :
    BinomialEdgeVars (Fin n) → BinomialEdgeVars (Fin n)
  | Sum.inl i => Sum.inl i
  | Sum.inr j => Sum.inr ⟨(j.val + 1) % n, Nat.mod_lt _ hn⟩

private lemma ySucc_yPred (n : ℕ) (hn : 0 < n) (v : BinomialEdgeVars (Fin n)) :
    ySuccVar n hn (yPredVar n hn v) = v := by
  cases v with
  | inl i => rfl
  | inr j =>
    simp only [yPredVar, ySuccVar]
    congr 1; ext; simp only
    have hj := j.isLt
    by_cases hj0 : j.val = 0
    · -- j = 0: pred = n-1, succ of that = n % n = 0
      rw [hj0, show 0 + n - 1 = n - 1 from by omega,
          Nat.mod_eq_of_lt (by omega : n - 1 < n),
          show (n - 1 + 1) = n from by omega, Nat.mod_self]
    · -- j > 0: pred = j-1, succ of that = j
      rw [show j.val + n - 1 = (j.val - 1) + 1 * n from by omega,
          Nat.add_mul_mod_self_right,
          Nat.mod_eq_of_lt (by omega : j.val - 1 < n),
          show j.val - 1 + 1 = j.val from by omega,
          Nat.mod_eq_of_lt hj]

private lemma yPred_ySucc (n : ℕ) (hn : 0 < n) (v : BinomialEdgeVars (Fin n)) :
    yPredVar n hn (ySuccVar n hn v) = v := by
  cases v with
  | inl i => rfl
  | inr j =>
    simp only [ySuccVar, yPredVar]
    congr 1; ext; simp only
    have hj := j.isLt
    by_cases hjn : j.val + 1 < n
    · -- j+1 < n: succ = j+1, pred of that = j
      rw [Nat.mod_eq_of_lt hjn]
      rw [show (j.val + 1 + n - 1) = j.val + 1 * n from by omega,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    · -- j = n-1: succ = 0, pred of that = n-1
      have hjeq : j.val = n - 1 := by omega
      rw [show j.val + 1 = n from by omega, Nat.mod_self]
      rw [show (0 + n - 1) = n - 1 from by omega, Nat.mod_eq_of_lt (by omega)]
      exact hjeq.symm

/-- The y-predecessor shift as an equivalence on BEI variables.
`x_i ↦ x_i`, `y_j ↦ y_{(j-1) mod n}`, with inverse `y_j ↦ y_{(j+1) mod n}`. -/
def yPredEquiv (n : ℕ) (hn : 0 < n) :
    BinomialEdgeVars (Fin n) ≃ BinomialEdgeVars (Fin n) where
  toFun := yPredVar n hn
  invFun := ySuccVar n hn
  left_inv := ySucc_yPred n hn
  right_inv := yPred_ySucc n hn

/-! ## Equidimensionality of the monomial initial ideal quotient -/

/-- Under HH conditions, `S / monomialInitialIdeal G` is equidimensional in the
local surrogate sense.

Proof: the y-predecessor shift `φ` gives a ring isomorphism
`S / monomialInitialIdeal G ≃+* S / bipartiteEdgeMonomialIdeal G`,
and the bipartite edge ideal quotient is equidimensional by
`bipartiteEdgeMonomialIdeal_isEquidim`. -/
theorem monomialInitialIdeal_isEquidim {n : ℕ} (hn : 0 < n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsEquidimRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G) := by
  -- Build the ring equivalence from yPredEquiv
  set φ := (MvPolynomial.renameEquiv K (yPredEquiv n hn)).toRingEquiv
  -- Show φ maps monomialInitialIdeal to bipartiteEdgeMonomialIdeal
  have hmap : bipartiteEdgeMonomialIdeal (K := K) G =
      Ideal.map φ (monomialInitialIdeal (K := K) G) := by
    -- φ.toRingHom and rename (yPredVar n hn) act the same on generators
    have hfun : ⇑φ = ⇑(rename (yPredVar n hn) : MvPolynomial _ K →ₐ[K] MvPolynomial _ K) := by
      funext p; exact (MvPolynomial.renameEquiv_apply K (yPredEquiv n hn) p).symm
    change _ = Ideal.map φ.toRingHom _
    conv_rhs => rw [show φ.toRingHom = (rename (yPredVar n hn) :
        MvPolynomial _ K →ₐ[K] MvPolynomial _ K).toRingHom from RingHom.ext (fun x => by
      change φ x = rename (yPredVar n hn) x; exact congr_fun hfun x)]
    exact (rename_yPredVar_monomialInitialIdeal (K := K) hn G).symm
  -- Build the quotient isomorphism
  have e : MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G ≃+*
      MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.quotientEquiv _ _ φ hmap
  exact isEquidim_of_ringEquiv e.symm
    (bipartiteEdgeMonomialIdeal_isEquidim (K := K) hHH)

/-! ## Closed graph interval and component count lemmas -/

/-- In a connected closed graph, edges span intervals: if `G.Adj a b` with `a < b`,
then `G.Adj a c` for all `a < c ≤ b`. This follows from the closedness condition (2)
and consecutive adjacency, by induction on `b - c`. -/
lemma closedGraph_adj_between {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (hConn : G.Connected)
    {a b : Fin n} (hab : G.Adj a b) (ha_lt_b : a < b) :
    ∀ c : Fin n, a < c → c ≤ b → G.Adj a c := by
  suffices h : ∀ (d : ℕ) (c : Fin n),
      a < c → c ≤ b → b.val - c.val = d → G.Adj a c from
    fun c hac hcb => h _ c hac hcb rfl
  intro d; induction d with
  | zero =>
    intro c _ hcb hd; have : c = b := Fin.ext (by omega); subst this; exact hab
  | succ d ih =>
    intro c hac hcb hd
    have hcn : c.val + 1 < n := by have := b.isLt; omega
    set c' : Fin n := ⟨c.val + 1, by omega⟩
    exact hClosed.2 (by exact Fin.mk_lt_mk.mpr (by omega))
      (by exact Fin.mk_lt_mk.mpr (by omega)) (Fin.ne_of_lt hac)
      (ih c' (Fin.mk_lt_mk.mpr (by omega))
        (Fin.mk_le_mk.mpr (by omega)) (by simp [c']; omega))
      (closedGraph_adj_consecutive hClosed hConn c hcn)

/-- Components of `G[V \ S]` are convex in connected closed graphs: if `u` and `v` are
in the same component and `u < w < v` with `w ∉ S`, then `w` is in the same component
as `u`. The key is that any edge `{x, y}` with `x < w < y` on the path gives
`G.Adj x w` by `closedGraph_adj_between`. -/
lemma reflTransGen_convex_closed {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (hConn : G.Connected)
    {S : Finset (Fin n)} {u v w : Fin n}
    (_huS : u ∉ S) (hwS : w ∉ S)
    (huw : u < w) (hwv : w < v)
    (hpath : Relation.ReflTransGen
      (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) u v) :
    Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) u w := by
  induction hpath with
  | refl => exact absurd (lt_trans huw hwv) (lt_irrefl _)
  | @tail x y hux hxy ih =>
    obtain ⟨hadj_xy, hxS, _⟩ := hxy
    by_cases hxw : x < w
    · -- x < w < y. By closedness: G.Adj x w. Extend path.
      have hxy_ord : x < y := lt_trans hxw hwv
      have hadj_xw :=
        closedGraph_adj_between hClosed hConn hadj_xy hxy_ord w hxw hwv.le
      exact hux.tail ⟨hadj_xw, hxS, hwS⟩
    · -- w ≤ x.
      rcases (not_lt.mp hxw).eq_or_lt with rfl | hwx
      · exact hux  -- w = x
      · exact ih hwx  -- w < x, use IH

/-- For a connected closed graph G on `Fin n`, `componentCount G S ≤ S.card + 1`.

**Proof**: Construct an injection from connected components of G[V\S] to `Option S`.
For each component `c`, let `m(c)` be the maximum vertex in `c`. If `m(c).val + 1 < n`
then by `closedGraph_adj_consecutive`, `G.Adj m(c) (m(c)+1)`, so `m(c)+1` is in the
same component, contradicting maximality. Hence `m(c)+1 ∈ S`. Map `c ↦ some ⟨m(c)+1, _⟩`.
If `m(c)` is the last vertex, map `c ↦ none`. This map is injective because two distinct
components have distinct max vertices. -/
theorem closedGraph_componentCount_le_card_add_one {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (hConn : G.Connected)
    (S : Finset (Fin n)) :
    componentCount G S ≤ S.card + 1 := by
  classical
  unfold componentCount
  set H := G.induce {v : Fin n | v ∉ S}
  haveI : Fintype H.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  -- For each component, build the set of its Fin n vertices
  let compVerts : H.ConnectedComponent → Finset (Fin n) := fun c =>
    Finset.univ.filter (fun v => ∃ hv : v ∉ S, H.connectedComponentMk ⟨v, hv⟩ = c)
  -- Each component is nonempty
  have hne : ∀ c : H.ConnectedComponent, (compVerts c).Nonempty := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with | h v =>
    exact ⟨v.val, Finset.mem_filter.mpr ⟨Finset.mem_univ _, v.prop, rfl⟩⟩
  -- Membership characterization
  have hmem : ∀ c v, v ∈ compVerts c ↔
      ∃ hv : v ∉ S, H.connectedComponentMk ⟨v, hv⟩ = c := by
    intro c v; simp [compVerts]
  -- Max vertex of each component
  let maxV : H.ConnectedComponent → Fin n := fun c => (compVerts c).max' (hne c)
  -- maxV(c) ∈ compVerts c, hence ∉ S and in component c
  have hmaxV_mem : ∀ c, maxV c ∈ compVerts c := fun c => Finset.max'_mem _ _
  have hmaxV_not_S : ∀ c, maxV c ∉ S := by
    intro c; obtain ⟨hv, _⟩ := (hmem c _).mp (hmaxV_mem c); exact hv
  have hmaxV_comp : ∀ c, H.connectedComponentMk ⟨maxV c, hmaxV_not_S c⟩ = c := by
    intro c
    obtain ⟨hv, hc⟩ := (hmem c _).mp (hmaxV_mem c)
    exact hc
  -- If maxV(c) + 1 < n, then maxV(c) + 1 ∈ S
  have hmax_succ_in_S : ∀ c : H.ConnectedComponent, ∀ hlt : (maxV c).val + 1 < n,
      (⟨(maxV c).val + 1, hlt⟩ : Fin n) ∈ S := by
    intro c hlt
    by_contra hnotS
    set m := maxV c
    set m1 : Fin n := ⟨m.val + 1, hlt⟩
    -- m1 is adjacent to m by closedGraph_adj_consecutive
    have hadj : G.Adj m m1 := closedGraph_adj_consecutive hClosed hConn m hlt
    -- So m1 is in the same component as m in H
    have hm1_comp : H.connectedComponentMk ⟨m1, hnotS⟩ = c := by
      rw [← hmaxV_comp c, SimpleGraph.ConnectedComponent.eq]
      exact SimpleGraph.Adj.reachable (SimpleGraph.induce_adj.mpr hadj.symm)
    -- So m1 ∈ compVerts c
    have hm1_in : m1 ∈ compVerts c := (hmem c m1).mpr ⟨hnotS, hm1_comp⟩
    -- But m is the max of compVerts c, and m1.val = m.val + 1 > m.val
    have hle : m1 ≤ m := Finset.le_max' (compVerts c) m1 hm1_in
    rw [Fin.le_iff_val_le_val] at hle; simp [m1] at hle
  -- maxV is injective (a vertex belongs to exactly one component)
  have hmaxV_inj : Function.Injective maxV := by
    intro c1 c2 heq
    rw [← hmaxV_comp c1, ← hmaxV_comp c2]
    congr 1; exact Subtype.ext heq
  -- Build the injection: CC(H) → Option S
  let φ : H.ConnectedComponent → Option S := fun c =>
    if h : (maxV c).val + 1 < n then
      some ⟨⟨(maxV c).val + 1, by omega⟩, hmax_succ_in_S c h⟩
    else none
  have hφ_inj : Function.Injective φ := by
    intro c1 c2 heq
    simp only [φ] at heq
    by_cases h1 : (maxV c1).val + 1 < n <;> by_cases h2 : (maxV c2).val + 1 < n
    · simp [h1, h2] at heq
      exact hmaxV_inj (Fin.ext (by omega))
    · simp [h1, h2] at heq
    · simp [h1, h2] at heq
    · exact hmaxV_inj (Fin.ext (by omega))
  calc Fintype.card H.ConnectedComponent
      ≤ Fintype.card (Option S) := Fintype.card_le_of_injective φ hφ_inj
    _ = Fintype.card S + 1 := Fintype.card_option
    _ = S.card + 1 := by rw [Fintype.card_coe]

-- The component count equality and direct proof of Proposition 1.6 are in
-- PrimeDecompositionDimension.lean, which has access to the full minimal-prime
-- and dimension infrastructure.

/-! ## Regular sequence infrastructure for the HH Cohen–Macaulay path

The goal is to show the diagonal sums `x_0 + y_0, x_1 + y_1, …` form a regular
sequence on the quotient by the bipartite edge monomial ideal. The single-element
regularity is already `sum_XY_isSMulRegular`; the infrastructure below handles
the iterated quotients.

### Route summary

1. **Minimal-prime avoidance** (proved below): every minimal prime of
   `I + span{ℓ₀,…,ℓ_{k-1}}` is a variable-generated prime that picks exactly
   one of `{xⱼ, yⱼ}` for each active `j ≥ k`, so `ℓ_k` avoids all of them.

2. **General radical NZD lemma** (proved below): for a radical ideal, avoiding
   all minimal primes implies regularity. This is extracted from the proof of
   `sum_XY_isSMulRegular`.

3. **Nilradical regularity** (remaining gap): one must additionally show `ℓ_k`
   is a non-zero-divisor on `√(J_k) / J_k`. This module is cyclic (for k=1) or
   filtered-cyclic, and each graded piece is a quotient by a radical ideal whose
   minimal primes also avoid `ℓ_k`. See the detailed comment at the bottom.
-/

/-- The ideal generated by the diagonal sums `X (inl i) + X (inr i)` for
indices `i` with `i.val < k` and `i.val + 1 < n`. -/
noncomputable def diagonalSumIdeal (n k : ℕ) :
    Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
  Ideal.span { ℓ | ∃ (i : Fin n), i.val < k ∧ i.val + 1 < n ∧
    ℓ = X (Sum.inl i) + X (Sum.inr i) }

/-- General lemma: for a radical ideal in a Noetherian ring, an element that avoids
every minimal prime is a non-zero-divisor on the quotient.

Proof: if `ℓ · f ∈ I`, then `ℓ · f ∈ P` for each minimal prime `P` of `I`.
Since `P` is prime and `ℓ ∉ P`, we get `f ∈ P`. Then
`f ∈ ⋂ P = radical(I) = I`. -/
theorem isSMulRegular_of_radical_not_mem_minimalPrimes
    {I : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hrad : I.IsRadical)
    {ℓ : MvPolynomial (BinomialEdgeVars (Fin n)) K}
    (havoid : ∀ P ∈ I.minimalPrimes, ℓ ∉ P) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ I)
      (Ideal.Quotient.mk I ℓ) := by
  set mk := Ideal.Quotient.mk I
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul] at hab
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq] at hab
  rw [Ideal.Quotient.eq]
  have hdiff : ℓ * (a' - b') ∈ I := by rwa [mul_sub]
  suffices a' - b' ∈ I.radical by rwa [hrad.radical] at this
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  intro P ⟨hPI, hPprime⟩
  haveI := hPprime
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hPI
  have hmemQ : ℓ * (a' - b') ∈ Q := hQmin.1.2 hdiff
  have hℓ_not_Q := havoid Q hQmin
  exact hQP ((hQmin.1.1.mem_or_mem hmemQ).resolve_left hℓ_not_Q)

/-- Under HH conditions, for a minimal prime `P` of the bipartite edge ideal and
any `j < k` with `j` active, both `Sum.inl j` and `Sum.inr j` belong to the
vertex cover underlying `P ⊔ diagonalSumIdeal n k`.

More precisely: if `P = span(X '' C)` for a minimal vertex cover `C`, and
`ℓ_j = x_j + y_j ∈ P ⊔ span{ℓ_l : l < k}`, then both `x_j` and `y_j` are
in `P ⊔ span{ℓ_l : l < k}`. -/
theorem both_vars_mem_prime_sup_diagonalSum {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {P : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hP : P ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G))
    (j : Fin n) (hj : j.val + 1 < n) (hjk : j.val < k) :
    (X (Sum.inl j) : MvPolynomial _ K) ∈ P ⊔ diagonalSumIdeal (K := K) n k ∧
    (X (Sum.inr j) : MvPolynomial _ K) ∈ P ⊔ diagonalSumIdeal (K := K) n k := by
  -- ℓ_j is in diagonalSumIdeal n k
  have hℓ_mem : (X (Sum.inl j) + X (Sum.inr j) : MvPolynomial _ K) ∈
      diagonalSumIdeal (K := K) n k :=
    Ideal.subset_span ⟨j, hjk, hj, rfl⟩
  -- One of x_j, y_j is in P (from the minimal vertex cover)
  obtain ⟨C, hC, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP
  have hexact := minimalVertexCover_exactlyOne hHH hC j hj
  rcases (hC.1 _ _ (hhEdgeSet_diagonal hHH j hj)) with hxj | hyj
  · -- Sum.inl j ∈ C
    have hxi : (X (Sum.inl j) : MvPolynomial _ K) ∈
        Ideal.span (X '' C) := Ideal.subset_span ⟨Sum.inl j, hxj, rfl⟩
    have hyj_not : Sum.inr j ∉ C := hexact.mp hxj
    constructor
    · exact Ideal.mem_sup_left hxi
    · -- y_j = ℓ_j - x_j
      have : (X (Sum.inr j) : MvPolynomial _ K) =
          (X (Sum.inl j) + X (Sum.inr j)) - X (Sum.inl j) := by ring
      rw [this]
      exact (Ideal.span (X '' C) ⊔ diagonalSumIdeal (K := K) n k).sub_mem
        (Ideal.mem_sup_right hℓ_mem) (Ideal.mem_sup_left hxi)
  · -- Sum.inr j ∈ C
    have hyi : (X (Sum.inr j) : MvPolynomial _ K) ∈
        Ideal.span (X '' C) := Ideal.subset_span ⟨Sum.inr j, hyj, rfl⟩
    have hxj_not : Sum.inl j ∉ C := fun h => (hexact.mp h) hyj
    constructor
    · -- x_j = ℓ_j - y_j
      have : (X (Sum.inl j) : MvPolynomial _ K) =
          (X (Sum.inl j) + X (Sum.inr j)) - X (Sum.inr j) := by ring
      rw [this]
      exact (Ideal.span (X '' C) ⊔ diagonalSumIdeal (K := K) n k).sub_mem
        (Ideal.mem_sup_right hℓ_mem) (Ideal.mem_sup_left hyi)
    · exact Ideal.mem_sup_left hyi

/-- Under HH conditions, `X (Sum.inl k) + X (Sum.inr k)` is not in any prime
of the form `P ⊔ diagonalSumIdeal n k` where `P` is a minimal prime of the
bipartite edge ideal.

The extended ideal `P ⊔ diag` is generated by variables: the original cover `C`
plus both `x_j, y_j` for `j < k`. For `j ≥ k`, the cover still picks exactly
one of `{x_j, y_j}`, so the diagonal sum `x_k + y_k` escapes. -/
theorem sum_X_not_mem_prime_sup_diagonalSum {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val)
    {P : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hP : P ∈ Ideal.minimalPrimes (bipartiteEdgeMonomialIdeal (K := K) G)) :
    X (Sum.inl i) + X (Sum.inr i) ∉ P ⊔ diagonalSumIdeal (K := K) n k := by
  obtain ⟨C, hC, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP
  have hexact := minimalVertexCover_exactlyOne hHH hC i hi
  set S : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) := MvPolynomial.X '' C
  by_cases hxi : Sum.inl i ∈ C
  · -- Sum.inl i ∈ C, Sum.inr i ∉ C: witness f(Sum.inr i) = 1, rest 0
    have hyi : Sum.inr i ∉ C := hexact.mp hxi
    intro hmem
    set f : BinomialEdgeVars (Fin n) → K := fun v => if v = Sum.inr i then 1 else 0
    have hker : Ideal.span S ⊔ diagonalSumIdeal (K := K) n k ≤
        RingHom.ker (MvPolynomial.eval f) := by
      apply sup_le
      · apply Ideal.span_le.mpr
        rintro g ⟨v, hv, rfl⟩
        simp only [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.eval_X]
        exact if_neg (fun (heq : v = Sum.inr i) => hyi (heq ▸ hv))
      · apply Ideal.span_le.mpr
        rintro g ⟨j, hjk, _, rfl⟩
        simp only [SetLike.mem_coe, RingHom.mem_ker, map_add, MvPolynomial.eval_X]
        have hj_ne : j ≠ i := Fin.ne_of_val_ne (by omega)
        simp only [f, show (Sum.inl j : BinomialEdgeVars _) ≠ Sum.inr i from Sum.inl_ne_inr,
          show (Sum.inr j : BinomialEdgeVars _) ≠ Sum.inr i from
            fun h => hj_ne (Sum.inr_injective h), ↓reduceIte, add_zero]
    -- eval f (x_i + y_i) = 0 + 1 = 1 ≠ 0
    have hone : MvPolynomial.eval f (X (Sum.inl i) + X (Sum.inr i) :
        MvPolynomial _ K) = 1 := by
      simp only [map_add, MvPolynomial.eval_X, f,
        show (Sum.inl i : BinomialEdgeVars _) ≠ Sum.inr i from Sum.inl_ne_inr,
        ↓reduceIte, zero_add]
    exact one_ne_zero (hone ▸ RingHom.mem_ker.mp (hker hmem))
  · -- Sum.inl i ∉ C, Sum.inr i ∈ C: witness f(Sum.inl i) = 1, rest 0
    have hyi : Sum.inr i ∈ C := by
      rcases hC.1 _ _ (hhEdgeSet_diagonal hHH i hi) with h | h
      · exact absurd h hxi
      · exact h
    intro hmem
    set f : BinomialEdgeVars (Fin n) → K := fun v => if v = Sum.inl i then 1 else 0
    have hker : Ideal.span S ⊔ diagonalSumIdeal (K := K) n k ≤
        RingHom.ker (MvPolynomial.eval f) := by
      apply sup_le
      · apply Ideal.span_le.mpr
        rintro g ⟨v, hv, rfl⟩
        simp only [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.eval_X]
        exact if_neg (fun (heq : v = Sum.inl i) => hxi (heq ▸ hv))
      · apply Ideal.span_le.mpr
        rintro g ⟨j, hjk, _, rfl⟩
        simp only [SetLike.mem_coe, RingHom.mem_ker, map_add, MvPolynomial.eval_X]
        have hj_ne : j ≠ i := Fin.ne_of_val_ne (by omega)
        simp only [f, show (Sum.inl j : BinomialEdgeVars _) ≠ Sum.inl i from
            fun h => hj_ne (Sum.inl_injective h),
          show (Sum.inr j : BinomialEdgeVars _) ≠ Sum.inl i from Sum.inr_ne_inl,
          ↓reduceIte, add_zero]
    have hone : MvPolynomial.eval f (X (Sum.inl i) + X (Sum.inr i) :
        MvPolynomial _ K) = 1 := by
      simp only [map_add, MvPolynomial.eval_X, f,
        show (Sum.inr i : BinomialEdgeVars _) ≠ Sum.inl i from Sum.inr_ne_inl,
        ↓reduceIte, add_zero]
    exact one_ne_zero (hone ▸ RingHom.mem_ker.mp (hker hmem))

/-- Under HH conditions, `x_k + y_k` avoids every minimal prime of
`bipartiteEdgeMonomialIdeal G ⊔ diagonalSumIdeal n k`.

Every minimal prime of the iterated ideal contains some minimal prime `P₀` of the
edge ideal, and `P₀ ⊔ diag ⊇ I ⊔ diag` is already prime. So every minimal prime
of `I ⊔ diag` is of the form `P₀ ⊔ diag`, and `ℓ_k` avoids all of these. -/
theorem sum_X_not_mem_minimalPrime_sup_diagonalSum {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val)
    {Q : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hQ : Q ∈ (bipartiteEdgeMonomialIdeal (K := K) G ⊔
      diagonalSumIdeal (K := K) n k).minimalPrimes) :
    X (Sum.inl i) + X (Sum.inr i) ∉ Q := by
  -- Q is a minimal prime of I ⊔ diag, so Q contains I ⊔ diag ⊇ I
  have hQ_sup : bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k ≤ Q :=
    hQ.1.2
  have hQ_I : bipartiteEdgeMonomialIdeal (K := K) G ≤ Q := le_trans le_sup_left hQ_sup
  -- Get a minimal prime P₀ of I with P₀ ≤ Q
  haveI := hQ.1.1
  obtain ⟨P₀, hP₀min, hP₀Q⟩ := Ideal.exists_minimalPrimes_le hQ_I
  -- P₀ ⊔ diag contains I ⊔ diag
  have hP₀_sup : bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k ≤
      P₀ ⊔ diagonalSumIdeal (K := K) n k :=
    sup_le_sup_right hP₀min.1.2 _
  -- ℓ_k ∉ P₀ ⊔ diag (by sum_X_not_mem_prime_sup_diagonalSum)
  have havoid := sum_X_not_mem_prime_sup_diagonalSum (K := K) hHH i hi hik hP₀min
  -- P₀ ⊔ diag ≤ Q (since P₀ ≤ Q and diag ≤ Q)
  have hP₀_diag_le_Q : P₀ ⊔ diagonalSumIdeal (K := K) n k ≤ Q :=
    sup_le hP₀Q (le_trans le_sup_right hQ_sup)
  -- P₀ ⊔ diag is prime: P₀ = span(X '' C), and P₀ ⊔ diag = span(X '' C') where
  -- C' = C ∪ {both x_j, y_j : j < k}. This is a variable-generated ideal, hence prime
  -- by isPrime_span_X_image_set. Proof: both_vars_mem_prime_sup_diagonalSum shows all
  -- relevant variables are in P₀ ⊔ diag, and the reverse inclusion holds since C ⊆ C'
  -- and each ℓ_j = x_j + y_j ∈ span(X '' C') when both endpoints are in C'.
  have hP₀_diag_prime : (P₀ ⊔ diagonalSumIdeal (K := K) n k).IsPrime := by
    -- Extract C from P₀
    obtain ⟨C, hC, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP₀min
    -- Define C' = C ∪ {both inl j, inr j for active j < k}
    set C' : Set (BinomialEdgeVars (Fin n)) :=
      C ∪ {v | ∃ j : Fin n, j.val < k ∧ j.val + 1 < n ∧ (v = Sum.inl j ∨ v = Sum.inr j)}
    -- Show P₀ ⊔ diag = span(X '' C')
    suffices h : Ideal.span (X '' C) ⊔ diagonalSumIdeal (K := K) n k =
        Ideal.span (X '' C') by
      rw [h]; exact MvPolynomial.isPrime_span_X_image_set C'
    apply le_antisymm
    · -- Backward: span(X '' C) ⊔ diag ≤ span(X '' C')
      apply sup_le
      · -- span(X '' C) ≤ span(X '' C') since C ⊆ C'
        apply Ideal.span_mono
        exact Set.image_mono (Set.subset_union_left)
      · -- diag ≤ span(X '' C'): each generator x_j + y_j is in span(X '' C')
        apply Ideal.span_le.mpr
        rintro g ⟨j, hjk, hjn, rfl⟩
        have hinl : Sum.inl j ∈ C' :=
          Set.mem_union_right C ⟨j, hjk, hjn, Or.inl rfl⟩
        have hinr : Sum.inr j ∈ C' :=
          Set.mem_union_right C ⟨j, hjk, hjn, Or.inr rfl⟩
        have hXl : (X (Sum.inl j) : MvPolynomial _ K) ∈ Ideal.span (X '' C') :=
          Ideal.subset_span ⟨Sum.inl j, hinl, rfl⟩
        have hXr : (X (Sum.inr j) : MvPolynomial _ K) ∈ Ideal.span (X '' C') :=
          Ideal.subset_span ⟨Sum.inr j, hinr, rfl⟩
        exact (Ideal.span (X '' C')).add_mem hXl hXr
    · -- Forward: span(X '' C') ≤ span(X '' C) ⊔ diag
      apply Ideal.span_le.mpr
      rintro g ⟨v, hv, rfl⟩
      rcases hv with hv_C | ⟨j, hjk, hjn, hv_eq⟩
      · -- v ∈ C: X v ∈ span(X '' C) ≤ P₀ ⊔ diag
        exact Ideal.mem_sup_left (Ideal.subset_span ⟨v, hv_C, rfl⟩)
      · -- v = inl j or inr j with j < k, j active
        have hboth := both_vars_mem_prime_sup_diagonalSum (K := K) hHH hP₀min j hjn hjk
        rcases hv_eq with rfl | rfl
        · exact hboth.1
        · exact hboth.2
  -- By minimality of Q: P₀ ⊔ diag is prime and ≥ I ⊔ diag and ≤ Q,
  -- so Q ≤ P₀ ⊔ diag (hence Q = P₀ ⊔ diag)
  have hQ_le : Q ≤ P₀ ⊔ diagonalSumIdeal (K := K) n k :=
    hQ.2 ⟨hP₀_diag_prime, hP₀_sup⟩ hP₀_diag_le_Q
  -- Conclude: ℓ_k ∈ Q ⊆ P₀ ⊔ diag contradicts havoid
  exact fun hℓ_Q => havoid (hQ_le hℓ_Q)

/-! ## Iterated regularity via diagonal substitution

The proof that `x_i + y_i` is a non-zero-divisor on `S / (I ⊔ diag)` uses a
substitution homomorphism `φ` that replaces `y_j` with `-x_j` for active
`j < k`. This transforms the non-radical ideal `I ⊔ diag` into a monomial
ideal `I.map φ`, where the NZD property can be established separately.

The key structural facts are:
1. `f - φ(f) ∈ diag` for all `f` (by the universal property of `MvPolynomial`);
2. `diag ≤ ker φ` (φ kills diagonal sum generators);
3. `I.map φ ⊆ J` (follows from 1);
4. `ℓ` is NZD on `S / I.map φ` (monomial ideal NZD, the remaining gap).

From these: if `ℓ · c ∈ J`, then `ℓ · φ(c) ∈ I.map φ`, so `φ(c) ∈ I.map φ ⊆ J`,
and `c - φ(c) ∈ diag ⊆ J`, hence `c ∈ J`.
-/

/-- The diagonal substitution: `y_j ↦ -x_j` for active `j < k`, identity otherwise. -/
private noncomputable def diagSubstFun {n : ℕ} (k : ℕ) :
    BinomialEdgeVars (Fin n) → MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  Sum.elim (fun j => X (Sum.inl j))
    (fun j => if j.val < k ∧ j.val + 1 < n then -X (Sum.inl j) else X (Sum.inr j))

/-- The diagonal substitution as a K-algebra homomorphism. -/
private noncomputable def diagSubstHom {n : ℕ} (k : ℕ) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K →ₐ[K] MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  MvPolynomial.aeval (diagSubstFun (K := K) k)

/-- The diagonal substitution agrees with the identity modulo `diag`:
the two K-algebra maps `mk ∘ φ` and `mk` agree on variables, hence are equal.
Consequence: `f - φ(f) ∈ diag` for every polynomial `f`. -/
private theorem diagSubstHom_congr_mod_diag {n : ℕ} (k : ℕ)
    (f : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    f - diagSubstHom (K := K) k f ∈ diagonalSumIdeal (K := K) n k := by
  suffices h : (Ideal.Quotient.mkₐ K (diagonalSumIdeal (K := K) n k)).comp
      (diagSubstHom (K := K) k) =
    Ideal.Quotient.mkₐ K (diagonalSumIdeal (K := K) n k) by
    have h1 := AlgHom.congr_fun h f
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1
    rw [eq_comm, Ideal.Quotient.eq] at h1
    exact h1
  apply MvPolynomial.algHom_ext
  intro v
  cases v with
  | inl _ =>
    simp only [AlgHom.comp_apply, diagSubstHom, MvPolynomial.aeval_X,
      Ideal.Quotient.mkₐ_eq_mk, diagSubstFun, Sum.elim_inl]
  | inr j =>
    simp only [AlgHom.comp_apply, diagSubstHom, MvPolynomial.aeval_X,
      Ideal.Quotient.mkₐ_eq_mk, diagSubstFun, Sum.elim_inr]
    split_ifs with h
    · rw [Ideal.Quotient.eq]
      have : (-X (Sum.inl j) : MvPolynomial _ K) - X (Sum.inr j) =
        -(X (Sum.inl j) + X (Sum.inr j)) := by ring
      rw [this]
      exact (Ideal.neg_mem_iff _).mpr (Ideal.subset_span ⟨j, h.1, h.2, rfl⟩)
    · rfl

/-- `diag ≤ ker φ`: the substitution kills all diagonal sum generators. -/
private theorem diag_le_ker_diagSubstHom {n : ℕ} (k : ℕ) :
    diagonalSumIdeal (K := K) n k ≤
      RingHom.ker (diagSubstHom (K := K) k).toRingHom := by
  unfold diagonalSumIdeal
  rw [Ideal.span_le]
  rintro _ ⟨j, hjk, hjn, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  change diagSubstHom (K := K) k (X (Sum.inl j) + X (Sum.inr j)) = 0
  simp only [diagSubstHom, map_add, MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl,
    Sum.elim_inr, hjk, hjn, and_self, ite_true, add_neg_cancel]

/-- `I.map φ ⊆ J`: the φ-image of the edge ideal is contained in `I ⊔ diag`. -/
private theorem map_diagSubstHom_le {n : ℕ} {G : SimpleGraph (Fin n)} (k : ℕ) :
    Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G) ≤
    bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  set J := bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k
  have hg_J : g ∈ J := Ideal.mem_sup_left hg
  have h_diff := diagSubstHom_congr_mod_diag (K := K) k g
  have : diagSubstHom (K := K) k g = g - (g - diagSubstHom (K := K) k g) := by ring
  rw [this]
  exact J.sub_mem hg_J (Ideal.mem_sup_right h_diff)

/-- `φ` fixes `x_i + y_i` when `i ≥ k`. -/
private theorem diagSubstHom_fix_ell {n : ℕ} (k : ℕ) (i : Fin n) (hik : k ≤ i.val) :
    diagSubstHom (K := K) k (X (Sum.inl i) + X (Sum.inr i)) =
      X (Sum.inl i) + X (Sum.inr i) := by
  simp only [diagSubstHom, map_add, MvPolynomial.aeval_X, diagSubstFun,
    Sum.elim_inl, Sum.elim_inr]
  have : ¬(i.val < k) := Nat.not_lt.mpr hik
  simp [this]

/-- `(I ⊔ diag).map φ ≤ I.map φ`: the φ-image of the full ideal reduces to
the φ-image of I, since φ kills diag. -/
private theorem map_sup_diag_le {n : ℕ} {G : SimpleGraph (Fin n)} (k : ℕ) :
    Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k) ≤
    Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G) := by
  rw [Ideal.map_le_iff_le_comap]
  intro g hg
  rw [Ideal.mem_comap, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  obtain ⟨a, ha, d, hd, hgad⟩ := Submodule.mem_sup.mp hg
  rw [← hgad, map_add]
  have hd_zero : diagSubstHom (K := K) k d = 0 := by
    have := diag_le_ker_diagSubstHom (K := K) k hd
    rwa [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
  rw [hd_zero, add_zero]
  exact Ideal.mem_map_of_mem _ ha

/-- If `ℓ` is NZD on `R/√J` and on the nilradical module `√J/J`, then NZD on `R/J`. -/
private theorem isSMulRegular_of_radical_step
    {J : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    {r : MvPolynomial (BinomialEdgeVars (Fin n)) K}
    (hrad : IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ J.radical)
      (Ideal.Quotient.mk J.radical r))
    (hnil : ∀ c ∈ J.radical, r * c ∈ J → c ∈ J) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ J)
      (Ideal.Quotient.mk J r) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul, Ideal.Quotient.eq] at hab ⊢
  have hdiff : r * (a' - b') ∈ J := by rwa [mul_sub]
  have hrad_mem : a' - b' ∈ J.radical := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hrad (by
      simp only [smul_eq_mul, mul_zero, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem.mpr (J.le_radical hdiff)])
  exact hnil _ hrad_mem hdiff

/-- `ℓ` avoids all minimal primes of the monomial image ideal `I.map φ`:
no minimal prime of `I.map φ` contains both `x_i` and `y_i`.
Proof uses HH transitivity: if both `x_i·m` and `y_i·m` belong to `I.map φ`,
then some generator `x_a·y_b` has both `x_a | m` and `y_b | m`, so `m ∈ I.map φ`. -/
private theorem ell_not_mem_minimalPrime_map_diagSubstHom {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val)
    {P : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K)}
    (hP : P ∈ (Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G)).minimalPrimes) :
    X (Sum.inl i) + X (Sum.inr i) ∉ P := by
  set Iφ := Ideal.map (diagSubstHom (K := K) k).toRingHom
    (bipartiteEdgeMonomialIdeal (K := K) G) with hIφ_def
  haveI hPprime : P.IsPrime := hP.1.1
  have hIφP : Iφ ≤ P := hP.1.2
  set C : Set (BinomialEdgeVars (Fin n)) := {v | (X v : MvPolynomial _ K) ∈ P}
  set Q : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
    Ideal.span (MvPolynomial.X '' C) with hQ_def
  have hQ_prime : Q.IsPrime := MvPolynomial.isPrime_span_X_image_set C
  have hQ_le_P : Q ≤ P := Ideal.span_le.mpr fun _ ⟨v, hv, he⟩ => he ▸ hv
  -- Helper: compute φ(x_a * y_b) and show it's in P, then put it in Q
  have hIφQ : Iφ ≤ Q := by
    rw [hIφ_def, Ideal.map_le_iff_le_comap]
    change bipartiteEdgeMonomialIdeal (K := K) G ≤ _
    unfold bipartiteEdgeMonomialIdeal
    rw [Ideal.span_le]
    rintro _ ⟨a, b, hb, hadj, hab, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    have hgP : (diagSubstHom (K := K) k).toRingHom (X (Sum.inl a) * X (Sum.inr b)) ∈ P :=
      hIφP (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨a, b, hb, hadj, hab, rfl⟩))
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hgP ⊢
    split_ifs at hgP ⊢ with hcond
    · -- b < k: φ(x_a * y_b) = x_a * (-x_b)
      have hmul : X (Sum.inl a) * X (Sum.inl b) ∈ P := by
        rw [show X (Sum.inl a) * -X (Sum.inl b) =
          -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring] at hgP
        exact neg_mem_iff.mp hgP
      rw [show X (Sum.inl a) * -X (Sum.inl b) =
        -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring]
      rcases hPprime.mem_or_mem hmul with ha | hb'
      · exact Q.neg_mem (Q.mul_mem_right _ (Ideal.subset_span ⟨Sum.inl a, ha, rfl⟩))
      · exact Q.neg_mem (Q.mul_mem_left _ (Ideal.subset_span ⟨Sum.inl b, hb', rfl⟩))
    · -- b ≥ k: φ(x_a * y_b) = x_a * y_b
      rcases hPprime.mem_or_mem hgP with ha | hb'
      · exact Q.mul_mem_right _ (Ideal.subset_span ⟨Sum.inl a, ha, rfl⟩)
      · exact Q.mul_mem_left _ (Ideal.subset_span ⟨Sum.inr b, hb', rfl⟩)
  -- P = Q by minimality
  have hP_eq : P = Q := le_antisymm (hP.2 ⟨hQ_prime, hIφQ⟩ hQ_le_P) hQ_le_P
  -- Forced variables: x_j ∈ P for j < k with j+1 < n (from diagonal squares)
  have hforced : ∀ (j : Fin n), j.val < k → j.val + 1 < n → Sum.inl j ∈ C := by
    intro j hjk hjn
    change (X (Sum.inl j) : MvPolynomial _ K) ∈ P
    have hφgen : (diagSubstHom (K := K) k).toRingHom
        (X (Sum.inl j) * X (Sum.inr j)) ∈ P :=
      hIφP (Ideal.mem_map_of_mem _ (Ideal.subset_span
        ⟨j, j, hjn, hHH.diagonal j hjn, le_refl j, rfl⟩))
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hφgen
    split_ifs at hφgen with hcond
    · -- j < k holds: φ(x_j * y_j) = x_j * (-x_j) = -(x_j²)
      have : (X (Sum.inl j) : MvPolynomial _ K) ^ 2 ∈ P := by
        rw [show (X (Sum.inl j) : MvPolynomial _ K) ^ 2 =
          -(X (Sum.inl j) * -X (Sum.inl j)) from by ring]
        exact P.neg_mem hφgen
      exact hPprime.mem_of_pow_mem 2 this
    · exact absurd ⟨hjk, hjn⟩ hcond
  -- Show ℓ ∉ P = Q
  rw [hP_eq]; intro hmem
  -- Diagonal edge: x_i * y_i ∈ Q (since i ≥ k, φ fixes it)
  have hdiag : (X (Sum.inl i) * X (Sum.inr i) : MvPolynomial _ K) ∈ Q := by
    apply hIφQ
    have hgen : X (Sum.inl i) * X (Sum.inr i) ∈
        bipartiteEdgeMonomialIdeal (K := K) G :=
      Ideal.subset_span ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩
    have h := Ideal.mem_map_of_mem (diagSubstHom (K := K) k).toRingHom hgen
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at h
    split_ifs at h with hcond
    · exact absurd hcond.1 (Nat.not_lt.mpr hik)
    · exact h
  -- Both variables in Q (and hence in C)
  have hx : (X (Sum.inl i) : MvPolynomial _ K) ∈ Q := by
    rcases hQ_prime.mem_or_mem hdiag with h | h
    · exact h
    · have := Q.sub_mem hmem h; rwa [add_sub_cancel_right] at this
  have hy : (X (Sum.inr i) : MvPolynomial _ K) ∈ Q := by
    have := Q.sub_mem hmem hx; rwa [add_sub_cancel_left] at this
  have hxi : Sum.inl i ∈ C := (MvPolynomial.X_mem_span_X_image_iff (R := K)).mp hx
  have hyi : Sum.inr i ∈ C := (MvPolynomial.X_mem_span_X_image_iff (R := K)).mp hy
  -- === Extract uncovered edges via minimality + HH transitivity ===
  -- Helper to get non-containment from minimality
  have hextract (v : BinomialEdgeVars (Fin n)) (hv : v ∈ C) :
      ¬(Iφ ≤ Ideal.span (MvPolynomial.X '' (C \ {v}) :
        Set (MvPolynomial _ K))) := by
    intro h
    have hle : Ideal.span (MvPolynomial.X '' (C \ {v}) :
        Set (MvPolynomial _ K)) ≤ P :=
      (Ideal.span_mono (Set.image_mono Set.diff_subset)).trans hQ_le_P
    have hge := hP.2 ⟨MvPolynomial.isPrime_span_X_image_set _, h⟩ hle
    rw [hP_eq] at hge
    exact ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp
      (hge (Ideal.subset_span ⟨v, hv, rfl⟩))).2 rfl
  -- Removing Sum.inr i: extract edge (a₁, i) with Sum.inl a₁ ∉ C
  have hnotQ1 := hextract _ hyi
  rw [hIφ_def, Ideal.map_le_iff_le_comap] at hnotQ1
  change ¬(bipartiteEdgeMonomialIdeal (K := K) G ≤ _) at hnotQ1
  unfold bipartiteEdgeMonomialIdeal at hnotQ1
  rw [Ideal.span_le, Set.not_subset] at hnotQ1
  obtain ⟨_, ⟨a₁, b₁, hb₁, hadj₁, hab₁, rfl⟩, hg₁⟩ := hnotQ1
  rw [SetLike.mem_coe, Ideal.mem_comap] at hg₁
  simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
    MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hg₁
  set Q₁ := Ideal.span (MvPolynomial.X '' (C \ {Sum.inr i}) :
    Set (MvPolynomial _ K))
  -- b₁ must equal i
  have hb₁_eq_i : b₁ = i := by
    split_ifs at hg₁ with hcond
    · -- b₁ < k: impossible since x_{b₁} forced into C hence C \ {Sum.inr i}
      exfalso; apply hg₁
      have hb₁_C : Sum.inl b₁ ∈ C \ ({Sum.inr i} : Set _) :=
        ⟨hforced b₁ hcond.1 hb₁, Sum.inl_ne_inr⟩
      rw [show X (Sum.inl a₁) * -X (Sum.inl b₁) =
        -(X (Sum.inl a₁) * X (Sum.inl b₁) : MvPolynomial _ K) from by ring]
      exact Q₁.neg_mem (Q₁.mul_mem_left _
        (Ideal.subset_span ⟨Sum.inl b₁, hb₁_C, rfl⟩))
    · -- b₁ ≥ k: must be b₁ = i
      have ha₁_notC : Sum.inl a₁ ∉ C :=
        fun h => hg₁ (Q₁.mul_mem_right _
          (Ideal.subset_span ⟨Sum.inl a₁, ⟨h, Sum.inl_ne_inr⟩, rfl⟩))
      by_contra hb₁_ne
      have hb₁_notC : Sum.inr b₁ ∉ C :=
        fun h => hg₁ (Q₁.mul_mem_left _
          (Ideal.subset_span ⟨Sum.inr b₁, ⟨h, fun heq => hb₁_ne (Sum.inr_injective heq)⟩, rfl⟩))
      -- Show g ∈ Q: compute φ(g) = g in this branch (b₁ ≥ k), hence g ∈ Iφ ⊆ Q
      have hg_Q : (X (Sum.inl a₁) * X (Sum.inr b₁) : MvPolynomial _ K) ∈ Q := by
        apply hIφQ
        have h := Ideal.mem_map_of_mem (diagSubstHom (K := K) k).toRingHom
          (Ideal.subset_span (s := { m | ∃ (i j : Fin n) (_ : j.val + 1 < n),
            G.Adj i ⟨j.val + 1, by omega⟩ ∧ i ≤ j ∧ m = X (Sum.inl i) * X (Sum.inr j) })
            ⟨a₁, b₁, hb₁, hadj₁, hab₁, rfl⟩)
        simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
          MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, hcond,
          ite_false] at h
        exact h
      exact ha₁_notC ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp
        ((hQ_prime.mem_or_mem hg_Q).resolve_right
          (fun h => hb₁_notC ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp h))))
  -- Now b₁ = i; rewrite hg₁ and hab₁ (not hadj₁ due to dependent Fin)
  rw [hb₁_eq_i] at hg₁ hab₁
  -- hadj₁ still has b₁, but we'll use it later with hb₁_eq_i
  -- Resolve the if-then-else in hg₁ (i ≥ k, so condition is false)
  simp only [show ¬(i.val < k ∧ i.val + 1 < n) from
    fun ⟨h, _⟩ => Nat.not_lt.mpr hik h, ite_false] at hg₁
  -- hg₁ : X (Sum.inl a₁) * X (Sum.inr i) ∉ Q₁
  have ha₁_notC : Sum.inl a₁ ∉ C :=
    fun h => hg₁ (Q₁.mul_mem_right _
      (Ideal.subset_span ⟨Sum.inl a₁, ⟨h, Sum.inl_ne_inr⟩, rfl⟩))
  have ha₁_lt_i : a₁ < i := lt_of_le_of_ne hab₁ (fun h => ha₁_notC (h ▸ hxi))
  have ha₁_ge_k : k ≤ a₁.val := by
    by_contra h; push_neg at h
    exact ha₁_notC (hforced a₁ h (by omega))
  -- Removing Sum.inl i: extract edge (i, b₂) with Sum.inr b₂ ∉ C
  have hnotQ2 := hextract _ hxi
  rw [hIφ_def, Ideal.map_le_iff_le_comap] at hnotQ2
  change ¬(bipartiteEdgeMonomialIdeal (K := K) G ≤ _) at hnotQ2
  unfold bipartiteEdgeMonomialIdeal at hnotQ2
  rw [Ideal.span_le, Set.not_subset] at hnotQ2
  obtain ⟨_, ⟨a₂, b₂, hb₂, hadj₂, hab₂, rfl⟩, hg₂⟩ := hnotQ2
  rw [SetLike.mem_coe, Ideal.mem_comap] at hg₂
  simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
    MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hg₂
  set Q₂ := Ideal.span (MvPolynomial.X '' (C \ {Sum.inl i}) :
    Set (MvPolynomial _ K))
  -- a₂ must equal i
  have ha₂_eq_i : a₂ = i := by
    split_ifs at hg₂ with hcond
    · -- b₂ < k: impossible since x_{b₂} forced into C \ {Sum.inl i} (b₂ ≠ i)
      exfalso; apply hg₂
      have hb₂_ne_i : b₂ ≠ i := fun h => Nat.not_lt.mpr hik (h ▸ hcond.1)
      have hb₂_C : Sum.inl b₂ ∈ C \ ({Sum.inl i} : Set _) :=
        ⟨hforced b₂ hcond.1 hb₂, fun h => hb₂_ne_i (Sum.inl_injective h)⟩
      rw [show X (Sum.inl a₂) * -X (Sum.inl b₂) =
        -(X (Sum.inl a₂) * X (Sum.inl b₂) : MvPolynomial _ K) from by ring]
      exact Q₂.neg_mem (Q₂.mul_mem_left _
        (Ideal.subset_span ⟨Sum.inl b₂, hb₂_C, rfl⟩))
    · -- b₂ ≥ k: must be a₂ = i
      have hb₂_notC : Sum.inr b₂ ∉ C :=
        fun h => hg₂ (Q₂.mul_mem_left _
          (Ideal.subset_span ⟨Sum.inr b₂, ⟨h, Sum.inr_ne_inl⟩, rfl⟩))
      by_contra ha₂_ne
      have ha₂_notC : Sum.inl a₂ ∉ C :=
        fun h => hg₂ (Q₂.mul_mem_right _
          (Ideal.subset_span ⟨Sum.inl a₂, ⟨h, fun heq => ha₂_ne (Sum.inl_injective heq)⟩, rfl⟩))
      have hg_Q : (X (Sum.inl a₂) * X (Sum.inr b₂) : MvPolynomial _ K) ∈ Q := by
        apply hIφQ
        have h := Ideal.mem_map_of_mem (diagSubstHom (K := K) k).toRingHom
          (Ideal.subset_span (s := { m | ∃ (i j : Fin n) (_ : j.val + 1 < n),
            G.Adj i ⟨j.val + 1, by omega⟩ ∧ i ≤ j ∧ m = X (Sum.inl i) * X (Sum.inr j) })
            ⟨a₂, b₂, hb₂, hadj₂, hab₂, rfl⟩)
        simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
          MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, hcond,
          ite_false] at h
        exact h
      exact ha₂_notC ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp
        ((hQ_prime.mem_or_mem hg_Q).resolve_right
          (fun h => hb₂_notC ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp h))))
  -- Now a₂ = i; rewrite where possible
  rw [ha₂_eq_i] at hg₂ hab₂
  -- Resolve the if on b₂
  -- Resolve if-then-else: if b₂ < k, get contradiction; else proceed
  by_cases hb₂k : b₂.val < k
  · -- b₂ < k: contradiction since x_{b₂} forced into C \ {Sum.inl i}
    exfalso
    have hb₂_ne_i : b₂ ≠ i := fun h => Nat.not_lt.mpr hik (h ▸ hb₂k)
    have hb₂_C : Sum.inl b₂ ∈ C \ ({Sum.inl i} : Set _) :=
      ⟨hforced b₂ hb₂k hb₂, fun h => hb₂_ne_i (Sum.inl_injective h)⟩
    apply hg₂
    have : (X (Sum.inl i) * X (Sum.inl b₂) : MvPolynomial _ K) ∈ Q₂ :=
      Q₂.mul_mem_left _ (Ideal.subset_span ⟨Sum.inl b₂, hb₂_C, rfl⟩)
    simp only [show b₂.val < k ∧ b₂.val + 1 < n from ⟨hb₂k, hb₂⟩, and_self, ite_true]
    rw [show X (Sum.inl i) * -X (Sum.inl b₂) =
      -(X (Sum.inl i) * X (Sum.inl b₂) : MvPolynomial _ K) from by ring]
    exact Q₂.neg_mem this
  -- b₂ ≥ k: simplify hg₂
  simp only [show ¬(b₂.val < k ∧ b₂.val + 1 < n) from fun ⟨h, _⟩ => hb₂k h,
    ite_false] at hg₂
  -- hg₂ : X (Sum.inl i) * X (Sum.inr b₂) ∉ Q₂
  have hb₂_notC : Sum.inr b₂ ∉ C :=
    fun h => hg₂ (Q₂.mul_mem_left _
      (Ideal.subset_span ⟨Sum.inr b₂, ⟨h, Sum.inr_ne_inl⟩, rfl⟩))
  have hb₂_gt_i : i < b₂ := by
    rcases lt_or_eq_of_le hab₂ with h | h
    · exact h
    · exact absurd (h ▸ hyi) hb₂_notC
  -- Convert hadj₁ : G.Adj a₁ ⟨b₁.val + 1, hb₁⟩ to use i (since b₁ = i)
  have hadj₁' : G.Adj a₁ ⟨i.val + 1, hi⟩ := by
    rw [show (⟨i.val + 1, hi⟩ : Fin n) = ⟨b₁.val + 1, hb₁⟩ from
      Fin.ext (by simp [hb₁_eq_i])]
    exact hadj₁
  -- Convert hadj₂ : G.Adj a₂ ... to G.Adj i ... (since a₂ = i)
  rw [ha₂_eq_i] at hadj₂
  -- HH transitivity: (a₁, i) and (i, b₂) with a₁ < i < b₂ → (a₁, b₂) is an edge
  have hadj_trans : G.Adj a₁ ⟨b₂.val + 1, by omega⟩ :=
    hHH.transitivity a₁ i b₂ hi hb₂ ha₁_lt_i hb₂_gt_i hadj₁' hadj₂
  -- (a₁, b₂) ∈ hhEdgeSet → x_{a₁} * y_{b₂} ∈ I → φ(x_{a₁} * y_{b₂}) ∈ Iφ → in Q
  have hgen_I : X (Sum.inl a₁) * X (Sum.inr b₂) ∈
      bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.subset_span ⟨a₁, b₂, hb₂, hadj_trans,
      le_of_lt (lt_trans ha₁_lt_i hb₂_gt_i), rfl⟩
  have hgen_final : (X (Sum.inl a₁) * X (Sum.inr b₂) : MvPolynomial _ K) ∈ Q := by
    apply hIφQ
    have h := Ideal.mem_map_of_mem (diagSubstHom (K := K) k).toRingHom hgen_I
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at h
    split_ifs at h with hc
    · exact absurd hc.1 (by omega)
    · exact h
  rcases hQ_prime.mem_or_mem hgen_final with h | h
  · exact ha₁_notC ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp h)
  · exact hb₂_notC ((MvPolynomial.X_mem_span_X_image_iff (R := K)).mp h)

/-- An ideal spanned by monomials (polynomials with at-most-singleton support)
is a monomial ideal: for every `f ∈ span S` and `d ∈ f.support`,
`monomial d 1 ∈ span S`. -/
private theorem isMonomial_span_of_support_singleton
    {σ : Type*}
    {S : Set (MvPolynomial σ K)}
    (hS : ∀ s ∈ S, ∃ d, s.support ⊆ {d}) :
    (Ideal.span S).IsMonomial := by
  classical
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨e, he⟩ := hS x hx
    intro d hd
    -- d must equal e since x.support ⊆ {e}
    have hde : d = e := Finset.mem_singleton.mp (he hd)
    -- x has singleton support, so x = monomial e (coeff e x)
    have hc_ne : x.coeff e ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (hde ▸ hd)
    -- monomial d 1 = monomial e 1 = C(coeff e x)⁻¹ * x ∈ span S
    rw [hde]
    have heq : MvPolynomial.monomial e (1 : K) =
        MvPolynomial.C (x.coeff e)⁻¹ * x := by
      set c := x.coeff e with hc_def
      have hx_eq : x = MvPolynomial.monomial e c := by
        ext m
        simp only [MvPolynomial.coeff_monomial]
        by_cases hme : e = m
        · simp [hme, hc_def]
        · rw [if_neg hme]
          exact MvPolynomial.notMem_support_iff.mp
            (fun hm => hme (Finset.mem_singleton.mp (he hm)).symm)
      rw [hx_eq, MvPolynomial.C_mul_monomial, inv_mul_cancel₀ hc_ne]
    rw [heq]
    exact (Ideal.span S).mul_mem_left _ (Ideal.subset_span hx)
  | zero =>
    intro d hd; simp at hd
  | add x y _ _ ihx ihy =>
    intro d hd
    rcases Finset.mem_union.mp (Finset.mem_of_subset MvPolynomial.support_add hd) with h | h
    · exact ihx d h
    · exact ihy d h
  | smul a x _ ihx =>
    intro d hd
    simp only [smul_eq_mul] at hd
    have hd_mem := Finset.mem_of_subset (MvPolynomial.support_mul a x) hd
    rw [Finset.mem_add] at hd_mem
    obtain ⟨da, hda, df, hdf, rfl⟩ := hd_mem
    have hdf_mem := ihx df hdf
    rw [show MvPolynomial.monomial (da + df) (1 : K) =
      MvPolynomial.monomial da (1 : K) * MvPolynomial.monomial df 1 from by
        rw [MvPolynomial.monomial_mul, one_mul]]
    exact (Ideal.span S).mul_mem_left _ hdf_mem

/-- In an ideal spanned by monomials with singleton support, every support monomial
is divisible (componentwise) by some generator exponent.

This is a fundamental property of monomial ideals: `monomial d 1 ∈ span{monomial e_j 1}`
implies `∃ j, e_j ≤ d`. -/
private theorem support_divisible_by_generator
    {σ : Type*}
    {S : Set (MvPolynomial σ K)}
    (hS : ∀ s ∈ S, ∃ e, s.support ⊆ {e})
    {f : MvPolynomial σ K} (hf : f ∈ Ideal.span S) :
    ∀ d ∈ f.support, ∃ s ∈ S, ∃ e, s.support ⊆ {e} ∧ e ≤ d := by
  classical
  -- Induction on span membership
  induction hf using Submodule.span_induction with
  | mem x hx =>
    intro d hd
    obtain ⟨e, he⟩ := hS x hx
    exact ⟨x, hx, e, he, le_of_eq (Finset.mem_singleton.mp (he hd)).symm⟩
  | zero => intro d hd; simp at hd
  | add x y _ _ ihx ihy =>
    intro d hd
    rcases Finset.mem_union.mp (Finset.mem_of_subset MvPolynomial.support_add hd) with h | h
    · exact ihx d h
    · exact ihy d h
  | smul a x _ ihx =>
    intro d hd
    simp only [smul_eq_mul] at hd
    obtain ⟨da, _, df, hdf, heq⟩ :=
      Finset.mem_add.mp (Finset.mem_of_subset (MvPolynomial.support_mul a x) hd)
    obtain ⟨s, hs, e, hes, hle⟩ := ihx df hdf
    exact ⟨s, hs, e, hes, heq ▸ le_trans hle (by rw [add_comm]; exact le_self_add)⟩

/-- The image of `bipartiteEdgeMonomialIdeal G` under `diagSubstHom k` is a monomial ideal. -/
private theorem isMonomial_map_diagSubstHom {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    (Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G)).IsMonomial := by
  classical
  -- Rewrite as span of images of generators
  change (Ideal.map (diagSubstHom (K := K) k).toRingHom
    (Ideal.span _)).IsMonomial
  rw [Ideal.map_span]
  apply isMonomial_span_of_support_singleton
  rintro _ ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩
  simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
    MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
  split_ifs with hcond
  · -- b < k: image is X(inl a) * (-X(inl b)) = -(X(inl a) * X(inl b))
    refine ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1, ?_⟩
    rw [show X (Sum.inl a) * -X (Sum.inl b) =
      -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring]
    rw [show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
      MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1) 1 from by
        simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
    rw [MvPolynomial.support_neg]
    exact MvPolynomial.support_monomial_subset
  · -- b ≥ k: image is X(inl a) * X(inr b)
    refine ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1, ?_⟩
    rw [show (X (Sum.inl a) * X (Sum.inr b) : MvPolynomial _ K) =
      MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1) 1 from by
        simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
    exact MvPolynomial.support_monomial_subset

/-- Every generator of `Iφ = I.map φ` has exponent ≤ 1 at `Sum.inl i` and
`Sum.inr i` when `i ≥ k`. -/
private theorem generator_exponent_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    (k : ℕ) (i : Fin n) (hik : k ≤ i.val)
    (v : BinomialEdgeVars (Fin n)) (hv : v = Sum.inl i ∨ v = Sum.inr i)
    {s : MvPolynomial (BinomialEdgeVars (Fin n)) K}
    (hs : s ∈ (diagSubstHom (K := K) k).toRingHom ''
      { m : MvPolynomial (BinomialEdgeVars (Fin n)) K |
        ∃ (a b : Fin n) (_ : b.val + 1 < n),
        G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
        m = X (Sum.inl a) * X (Sum.inr b) })
    {e : BinomialEdgeVars (Fin n) →₀ ℕ} (hes : s.support ⊆ {e}) :
    e v ≤ 1 := by
  obtain ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩ := hs
  simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
    MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hes
  -- Helper: if s.support ⊆ {e} and s.support ⊆ {e'} and s ≠ 0, then e = e'
  have key : ∀ (f : MvPolynomial (BinomialEdgeVars (Fin n)) K)
      (e' : BinomialEdgeVars (Fin n) →₀ ℕ),
      f ≠ 0 → f.support ⊆ {e} → f.support ⊆ {e'} → e = e' := by
    intro f e' hne h1 h2
    obtain ⟨d, hd⟩ := MvPolynomial.support_nonempty.mpr hne
    exact (Finset.mem_singleton.mp (h1 hd)).symm.trans (Finset.mem_singleton.mp (h2 hd))
  split_ifs at hes with hcond
  · -- Type A: both a, b < k ≤ i, so e(v) = 0
    -- Type A: -(X_a * X_b) with a, b < k. Both a, b ≠ i since i ≥ k.
    set e' : BinomialEdgeVars (Fin n) →₀ ℕ :=
      Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1
    have hsupp : (X (Sum.inl a) * -X (Sum.inl b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K).support ⊆ {e'} := by
      -- X_a * (-X_b) has support ⊆ support(X_a * X_b) = {e'}
      have hprod_eq : (X (Sum.inl a) * X (Sum.inl b) :
          MvPolynomial (BinomialEdgeVars (Fin n)) K) = MvPolynomial.monomial e' 1 := by
        change _ = MvPolynomial.monomial
          (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1) 1
        simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]; rfl
      have : (X (Sum.inl a) * -X (Sum.inl b) :
          MvPolynomial (BinomialEdgeVars (Fin n)) K) =
          MvPolynomial.monomial e' (-1) := by
        have : (X (Sum.inl a) * -X (Sum.inl b) :
            MvPolynomial (BinomialEdgeVars (Fin n)) K) =
            -(X (Sum.inl a) * X (Sum.inl b)) := by ring
        rw [this, hprod_eq, show -(MvPolynomial.monomial e' (1 : K)) =
          MvPolynomial.monomial e' (-1) from by simp [map_neg]]
      rw [this]; exact MvPolynomial.support_monomial_subset
    have hs_ne : (X (Sum.inl a) * -X (Sum.inl b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ≠ 0 :=
      mul_ne_zero (MvPolynomial.X_ne_zero _) (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
    have he_eq : e = e' := key _ e' hs_ne hes hsupp
    rw [he_eq]; simp only [e', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    rcases hv with rfl | rfl
    · -- v = inl i: both single(inl a) and single(inl b) have 0 at inl i since a,b < k ≤ i
      have ha_ne : (Sum.inl a : BinomialEdgeVars (Fin n)) ≠ Sum.inl i :=
        fun h => by have := Sum.inl_injective h; omega
      have hb_ne : (Sum.inl b : BinomialEdgeVars (Fin n)) ≠ Sum.inl i :=
        fun h => by have := Sum.inl_injective h; omega
      simp [ha_ne, hb_ne]
    · -- v = inr i: both single(inl a) and single(inl b) have 0 at inr i
      simp []
  · -- Type B: e(inl i) ≤ 1, e(inr i) ≤ 1
    -- Type B: X_a * Y_b with b ≥ k.
    set e' : BinomialEdgeVars (Fin n) →₀ ℕ :=
      Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1
    have hsupp : (X (Sum.inl a) * X (Sum.inr b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K).support ⊆ {e'} := by
      have : (X (Sum.inl a) * X (Sum.inr b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) = MvPolynomial.monomial e' 1 := by
        change _ = MvPolynomial.monomial
          (Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1) 1
        simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]; rfl
      rw [this]; exact MvPolynomial.support_monomial_subset
    have hs_ne : (X (Sum.inl a) * X (Sum.inr b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ≠ 0 :=
      mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    have he_eq : e = e' := key _ e' hs_ne hes hsupp
    rw [he_eq]; simp only [e', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    rcases hv with rfl | rfl
    · -- v = inl i: single(inl a)(inl i) ≤ 1 and single(inr b)(inl i) = 0
      simp only [
        show (Sum.inr b : BinomialEdgeVars (Fin n)) ≠ Sum.inl i from Sum.inr_ne_inl,
        if_false, add_zero]
      split <;> omega
    · -- v = inr i: single(inl a)(inr i) = 0 and single(inr b)(inr i) ≤ 1
      simp only [
        show (Sum.inl a : BinomialEdgeVars (Fin n)) ≠ Sum.inr i from Sum.inl_ne_inr,
        if_false, zero_add]
      split <;> omega

/-- NZD on the nilradical module of the monomial image ideal:
if `c ∈ √(I.map φ)` and `ℓ * c ∈ I.map φ`, then `c ∈ I.map φ`.
This uses the monomial structure: `I.map φ` is a monomial ideal and `ℓ = x_i + y_i`
where `x_i, y_i` are algebraically independent of the "killed" variables `y_j` (j < k). -/
private theorem nilradical_nzd_map_diagSubstHom {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val) :
    ∀ c ∈ (Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G)).radical,
    (X (Sum.inl i) + X (Sum.inr i)) * c ∈
      Ideal.map (diagSubstHom (K := K) k).toRingHom
        (bipartiteEdgeMonomialIdeal (K := K) G) →
    c ∈ Ideal.map (diagSubstHom (K := K) k).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G) := by
  set Iφ := Ideal.map (diagSubstHom (K := K) k).toRingHom
    (bipartiteEdgeMonomialIdeal (K := K) G) with hIφ_def
  have hIsM : Iφ.IsMonomial := hIφ_def ▸ isMonomial_map_diagSubstHom (K := K) G k
  intro c hc_rad hprod
  -- Prove by contradiction
  by_contra hc_not
  obtain ⟨d₀, hd₀_supp, hd₀_not⟩ := Ideal.not_mem_exists_monomial_notMem hc_not
  -- Diagonal generator: x_i * y_i ∈ Iφ (since i ≥ k, φ fixes it)
  have hdiag_I : X (Sum.inl i) * X (Sum.inr i) ∈
      bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.subset_span ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩
  have hdiag : (X (Sum.inl i) * X (Sum.inr i) : MvPolynomial _ K) ∈ Iφ := by
    have h := Ideal.mem_map_of_mem (diagSubstHom (K := K) k).toRingHom hdiag_I
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at h
    split_ifs at h with hcond
    · exact absurd hcond.1 (Nat.not_lt.mpr hik)
    · exact h
  -- Helper: monomial e 1 ∈ Iφ and e ≤ d₀ implies monomial d₀ 1 ∈ Iφ
  have hdiv : ∀ e : (BinomialEdgeVars (Fin n)) →₀ ℕ,
      MvPolynomial.monomial e (1 : K) ∈ Iφ → e ≤ d₀ →
      MvPolynomial.monomial d₀ (1 : K) ∈ Iφ := by
    intro e he hle
    have : MvPolynomial.monomial d₀ (1 : K) =
        MvPolynomial.monomial (d₀ - e) 1 * MvPolynomial.monomial e 1 := by
      rw [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hle]
    rw [this]; exact Iφ.mul_mem_left _ he
  -- Helper: extract that each generator exponent has ≤ 1 at inl i and inr i
  -- For the generators of Iφ, analyze via the generating set structure.
  -- Helper: from hprod and IsMonomial, extract monomials
  have hcoeff_ne : MvPolynomial.coeff d₀ c ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd₀_supp
  -- Case analysis on d₀(inl i) and d₀(inr i)
  by_cases hxi : 0 < d₀ (Sum.inl i) <;> by_cases hyi : 0 < d₀ (Sum.inr i)
  · -- Case A: both ≥ 1 → diagonal divides
    have hle : Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 ≤ d₀ := by
      have h1 : Finsupp.single (Sum.inl i) 1 ≤ d₀ :=
        Finsupp.single_le_iff.mpr (by omega)
      have h2 : Finsupp.single (Sum.inr i) 1 ≤ d₀ :=
        Finsupp.single_le_iff.mpr (by omega)
      intro v
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      by_cases h1v : Sum.inl i = v <;> by_cases h2v : Sum.inr i = v
      · exact absurd (h2v ▸ h1v) Sum.inl_ne_inr
      all_goals simp_all <;> omega
    have hdiag_mono : MvPolynomial.monomial
        (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) (1 : K) ∈ Iφ := by
      have : (X (Sum.inl i) * X (Sum.inr i) : MvPolynomial _ K) =
          MvPolynomial.monomial
            (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1) 1 := by
        simp [MvPolynomial.X, MvPolynomial.monomial_mul]
      rwa [this] at hdiag
    exact hd₀_not (hdiv _ hdiag_mono hle)
  · -- Case B: d₀(inl i) ≥ 1, d₀(inr i) = 0
    push_neg at hyi
    have hyi0 : d₀ (Sum.inr i) = 0 := Nat.eq_zero_of_le_zero hyi
    -- d' = d₀ + single(inl i) 1 is in support of (x_i + y_i) * c
    have hxi_single : Finsupp.single (Sum.inl i) 1 ≤ d₀ :=
      Finsupp.single_le_iff.mpr (by omega)
    set d' : BinomialEdgeVars (Fin n) →₀ ℕ :=
      d₀ + (Finsupp.single (Sum.inl i) 1 : BinomialEdgeVars (Fin n) →₀ ℕ)
    -- Coefficient of d' in (x_i + y_i) * c is coeff d₀ c ≠ 0
    set xi : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inl i) with hxi_def
    set yi : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inr i) with hyi_def
    have hd'_supp : d' ∈ ((xi + yi) * c).support := by
      rw [MvPolynomial.mem_support_iff, add_mul, MvPolynomial.coeff_add]
      have h1 : MvPolynomial.coeff d' (xi * c) = MvPolynomial.coeff d₀ c := by
        rw [hxi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inl i ∈ d'.support := by
          rw [Finsupp.mem_support_iff]
          simp [d']
        rw [if_pos this]
        congr 1
        ext v
        simp only [d', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
          Pi.add_apply, Finsupp.single_apply]
        split <;> omega
      have h2 : MvPolynomial.coeff d' (yi * c) = 0 := by
        rw [hyi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inr i ∉ d'.support := by
          rw [Finsupp.mem_support_iff, not_not]
          change d' (Sum.inr i) = 0
          simp only [d', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            show (Sum.inl i : BinomialEdgeVars (Fin n)) ≠ Sum.inr i from Sum.inl_ne_inr,
            if_false, add_zero, hyi0]
        rw [if_neg this]
      rw [h1, h2, add_zero]
      exact hcoeff_ne
    -- monomial d' 1 ∈ Iφ by IsMonomial
    have hd'_Iφ : MvPolynomial.monomial d' (1 : K) ∈ Iφ := hIsM _ hprod d' hd'_supp
    -- Use hdiv: show monomial d₀ 1 ∈ Iφ by finding e ≤ d₀ with monomial e 1 ∈ Iφ
    -- monomial d' 1 ∈ Iφ, and d' = d₀ + single(inl i) 1
    -- Every generator has exponent ≤ 1 at inl i, and d₀(inl i) ≥ 1
    -- So by generator divisibility, monomial d₀ 1 ∈ Iφ
    -- Strategy: use the map_span form and support_divisible_by_generator
    set genSet : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
      (diagSubstHom (K := K) k).toRingHom ''
        { m | ∃ (a b : Fin n) (_ : b.val + 1 < n),
          G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
          m = X (Sum.inl a) * X (Sum.inr b) }
    have hIφ_span : Iφ = Ideal.span genSet := by
      rw [hIφ_def]; unfold bipartiteEdgeMonomialIdeal; rw [Ideal.map_span]
    have hd'_span : MvPolynomial.monomial d' (1 : K) ∈ Ideal.span genSet :=
      hIφ_span ▸ hd'_Iφ
    have hgenS : ∀ s ∈ genSet, ∃ e, s.support ⊆ {e} := by
      rintro _ ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
      split_ifs with hcond
      · exact ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1, by
          rw [show X (Sum.inl a) * -X (Sum.inl b) =
            -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring]
          rw [show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
            MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
              Finsupp.single (Sum.inl b) 1) 1 from by
              simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
          rw [MvPolynomial.support_neg]
          exact MvPolynomial.support_monomial_subset⟩
      · exact ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1, by
          rw [show (X (Sum.inl a) * X (Sum.inr b) : MvPolynomial _ K) =
            MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
              Finsupp.single (Sum.inr b) 1) 1 from by
              simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
          exact MvPolynomial.support_monomial_subset⟩
    have hd'_supp_d' : d' ∈ (MvPolynomial.monomial d' (1 : K)).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]; exact one_ne_zero
    obtain ⟨s, hs_mem, e, hes, hle_d'⟩ :=
      support_divisible_by_generator (K := K) hgenS hd'_span d' hd'_supp_d'
    -- e ≤ d' = d₀ + single(inl i) 1, and e(inl i) ≤ 1 (generator bound)
    have he_bound := generator_exponent_bound (K := K) k i hik (Sum.inl i) (Or.inl rfl) hs_mem hes
    -- e ≤ d₀: for inl i, e(inl i) ≤ 1 ≤ d₀(inl i); for others, same as d'
    have hle_d₀ : e ≤ d₀ := by
      intro w
      by_cases hw : w = Sum.inl i
      · rw [hw]; exact le_trans he_bound (by omega)
      · have := hle_d' w
        simp only [d', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
          show (Sum.inl i : BinomialEdgeVars (Fin n)) = w ↔ w = Sum.inl i from
            ⟨fun h => h.symm, fun h => h.symm⟩, hw, if_false, add_zero] at this
        exact this
    -- monomial e 1 ∈ Iφ (from s ∈ genSet and IsMonomial)
    have hs_Iφ : s ∈ Iφ := hIφ_span ▸ Ideal.subset_span hs_mem
    -- s ≠ 0 (it's ±(X_a * X_b))
    have hs_ne : s ≠ 0 := by
      obtain ⟨_, ⟨a', b', _, _, _, rfl⟩, rfl⟩ := hs_mem
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, ne_eq]
      split_ifs
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _)
          (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    have he_supp : e ∈ s.support := by
      obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
      have := Finset.mem_singleton.mp (hes hd_wit)
      rwa [← this]
    have he_Iφ : MvPolynomial.monomial e (1 : K) ∈ Iφ := hIsM s hs_Iφ e he_supp
    exact hd₀_not (hdiv e he_Iφ hle_d₀)
  · -- Case C: d₀(inl i) = 0, d₀(inr i) ≥ 1 — symmetric to case B
    push_neg at hxi
    have hxi0 : d₀ (Sum.inl i) = 0 := Nat.eq_zero_of_le_zero hxi
    set d' : BinomialEdgeVars (Fin n) →₀ ℕ :=
      d₀ + (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars (Fin n) →₀ ℕ)
    set xi : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inl i) with hxi_def
    set yi : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inr i) with hyi_def
    have hd'_supp : d' ∈ ((xi + yi) * c).support := by
      rw [MvPolynomial.mem_support_iff, add_mul, MvPolynomial.coeff_add]
      have h1 : MvPolynomial.coeff d' (xi * c) = 0 := by
        rw [hxi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inl i ∉ d'.support := by
          rw [Finsupp.mem_support_iff, not_not]; change d' (Sum.inl i) = 0
          simp only [d', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            show (Sum.inr i : BinomialEdgeVars (Fin n)) ≠ Sum.inl i from Sum.inr_ne_inl,
            if_false, add_zero, hxi0]
        rw [if_neg this]
      have h2 : MvPolynomial.coeff d' (yi * c) = MvPolynomial.coeff d₀ c := by
        rw [hyi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inr i ∈ d'.support := by
          rw [Finsupp.mem_support_iff]; simp [d']
        rw [if_pos this]; congr 1; ext v
        simp only [d', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
          Pi.add_apply, Finsupp.single_apply]; split <;> omega
      rw [h1, h2, zero_add]; exact hcoeff_ne
    have hd'_Iφ : MvPolynomial.monomial d' (1 : K) ∈ Iφ := hIsM _ hprod d' hd'_supp
    set genSet : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
      (diagSubstHom (K := K) k).toRingHom ''
        { m | ∃ (a b : Fin n) (_ : b.val + 1 < n),
          G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
          m = X (Sum.inl a) * X (Sum.inr b) }
    have hIφ_span : Iφ = Ideal.span genSet := by
      rw [hIφ_def]; unfold bipartiteEdgeMonomialIdeal; rw [Ideal.map_span]
    have hgenS : ∀ s ∈ genSet, ∃ e, s.support ⊆ {e} := by
      rintro _ ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
      split_ifs with hcond
      · exact ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1, by
          rw [show X (Sum.inl a) * -X (Sum.inl b) =
            -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring,
            show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
              MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
                Finsupp.single (Sum.inl b) 1) 1 from by
                simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul],
            MvPolynomial.support_neg]
          exact MvPolynomial.support_monomial_subset⟩
      · exact ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1, by
          rw [show (X (Sum.inl a) * X (Sum.inr b) : MvPolynomial _ K) =
              MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
                Finsupp.single (Sum.inr b) 1) 1 from by
                simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
          exact MvPolynomial.support_monomial_subset⟩
    have hd'_supp_d' : d' ∈ (MvPolynomial.monomial d' (1 : K)).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]; exact one_ne_zero
    obtain ⟨s, hs_mem, e, hes, hle_d'⟩ :=
      support_divisible_by_generator (K := K) hgenS (hIφ_span ▸ hd'_Iφ) d' hd'_supp_d'
    have he_bound := generator_exponent_bound (K := K) k i hik (Sum.inr i) (Or.inr rfl) hs_mem hes
    have hle_d₀ : e ≤ d₀ := by
      intro w
      by_cases hw : w = Sum.inr i
      · rw [hw]; exact le_trans he_bound (by omega)
      · have := hle_d' w
        simp only [d', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
          show (Sum.inr i : BinomialEdgeVars (Fin n)) = w ↔ w = Sum.inr i from
            ⟨fun h => h.symm, fun h => h.symm⟩, hw, if_false, add_zero] at this
        exact this
    have hs_Iφ : s ∈ Iφ := hIφ_span ▸ Ideal.subset_span hs_mem
    have hs_ne : s ≠ 0 := by
      obtain ⟨_, ⟨a', b', _, _, _, rfl⟩, rfl⟩ := hs_mem
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, ne_eq]
      split_ifs
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _)
          (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    have he_supp : e ∈ s.support := by
      obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
      rwa [← Finset.mem_singleton.mp (hes hd_wit)]
    exact hd₀_not (hdiv e (hIsM s hs_Iφ e he_supp) hle_d₀)
  · -- Case D: both = 0 — use HH transitivity
    push_neg at hxi hyi
    have hxi0 : d₀ (Sum.inl i) = 0 := Nat.eq_zero_of_le_zero hxi
    have hyi0 : d₀ (Sum.inr i) = 0 := Nat.eq_zero_of_le_zero hyi
    -- Both x_i * c and y_i * c contribute to (x_i + y_i) * c at separate monomials
    -- because d₀(inl i) = d₀(inr i) = 0
    set xi : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inl i) with hxi_def
    set yi : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inr i) with hyi_def
    -- Both d₀ + single(inl i) 1 and d₀ + single(inr i) 1 are in Iφ (via IsMonomial)
    set dx : BinomialEdgeVars (Fin n) →₀ ℕ :=
      d₀ + (Finsupp.single (Sum.inl i) 1 : BinomialEdgeVars (Fin n) →₀ ℕ)
    set dy : BinomialEdgeVars (Fin n) →₀ ℕ :=
      d₀ + (Finsupp.single (Sum.inr i) 1 : BinomialEdgeVars (Fin n) →₀ ℕ)
    -- monomial dx 1 ∈ Iφ
    have hdx_supp : dx ∈ ((xi + yi) * c).support := by
      rw [MvPolynomial.mem_support_iff, add_mul, MvPolynomial.coeff_add]
      have h1 : MvPolynomial.coeff dx (xi * c) = MvPolynomial.coeff d₀ c := by
        rw [hxi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inl i ∈ dx.support := by rw [Finsupp.mem_support_iff]; simp [dx]
        rw [if_pos this]; congr 1; ext v
        simp only [dx, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
          Pi.add_apply, Finsupp.single_apply]; split <;> omega
      have h2 : MvPolynomial.coeff dx (yi * c) = 0 := by
        rw [hyi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inr i ∉ dx.support := by
          rw [Finsupp.mem_support_iff, not_not]; change dx (Sum.inr i) = 0
          simp only [dx, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            show (Sum.inl i : BinomialEdgeVars (Fin n)) ≠ Sum.inr i from Sum.inl_ne_inr,
            if_false, add_zero, hyi0]
        rw [if_neg this]
      rw [h1, h2, add_zero]; exact hcoeff_ne
    have hdx_Iφ : MvPolynomial.monomial dx (1 : K) ∈ Iφ := hIsM _ hprod dx hdx_supp
    -- monomial dy 1 ∈ Iφ
    have hdy_supp : dy ∈ ((xi + yi) * c).support := by
      rw [MvPolynomial.mem_support_iff, add_mul, MvPolynomial.coeff_add]
      have h1 : MvPolynomial.coeff dy (xi * c) = 0 := by
        rw [hxi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inl i ∉ dy.support := by
          rw [Finsupp.mem_support_iff, not_not]; change dy (Sum.inl i) = 0
          simp only [dy, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            show (Sum.inr i : BinomialEdgeVars (Fin n)) ≠ Sum.inl i from Sum.inr_ne_inl,
            if_false, add_zero, hxi0]
        rw [if_neg this]
      have h2 : MvPolynomial.coeff dy (yi * c) = MvPolynomial.coeff d₀ c := by
        rw [hyi_def, MvPolynomial.coeff_X_mul']
        have : Sum.inr i ∈ dy.support := by rw [Finsupp.mem_support_iff]; simp [dy]
        rw [if_pos this]; congr 1; ext v
        simp only [dy, Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
          Pi.add_apply, Finsupp.single_apply]; split <;> omega
      rw [h1, h2, zero_add]; exact hcoeff_ne
    have hdy_Iφ : MvPolynomial.monomial dy (1 : K) ∈ Iφ := hIsM _ hprod dy hdy_supp
    -- Generator analysis: both dx and dy give generator info
    set genSet : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
      (diagSubstHom (K := K) k).toRingHom ''
        { m | ∃ (a b : Fin n) (_ : b.val + 1 < n),
          G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
          m = X (Sum.inl a) * X (Sum.inr b) }
    have hIφ_span : Iφ = Ideal.span genSet := by
      rw [hIφ_def]; unfold bipartiteEdgeMonomialIdeal; rw [Ideal.map_span]
    have hgenS : ∀ s ∈ genSet, ∃ e, s.support ⊆ {e} := by
      rintro _ ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
      split_ifs with hcond
      · exact ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1, by
          rw [show X (Sum.inl a) * -X (Sum.inl b) =
            -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring,
            show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
              MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
                Finsupp.single (Sum.inl b) 1) 1 from by
                simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul],
            MvPolynomial.support_neg]
          exact MvPolynomial.support_monomial_subset⟩
      · exact ⟨Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inr b) 1, by
          rw [show (X (Sum.inl a) * X (Sum.inr b) : MvPolynomial _ K) =
              MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
                Finsupp.single (Sum.inr b) 1) 1 from by
                simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
          exact MvPolynomial.support_monomial_subset⟩
    have hsupp_mono : ∀ (d : BinomialEdgeVars (Fin n) →₀ ℕ),
        d ∈ (MvPolynomial.monomial d (1 : K)).support := by
      intro d; rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]
      exact one_ne_zero
    -- From dx: get generator e_x ≤ dx with e_x(inl i) ≤ 1
    obtain ⟨sx, hsx_mem, ex, hexs, hlex_dx⟩ :=
      support_divisible_by_generator (K := K) hgenS (hIφ_span ▸ hdx_Iφ) dx (hsupp_mono dx)
    -- Since d₀(inl i) = 0, dx(inl i) = 1, and ex(inl i) ≤ 1
    -- If ex(inl i) = 0, then ex ≤ d₀, contradiction (monomial d₀ 1 ∈ Iφ)
    -- If ex(inl i) = 1, then ex involves x_a for some a, giving edge info
    have hex_bound_inl := generator_exponent_bound (K := K) k i hik
      (Sum.inl i) (Or.inl rfl) hsx_mem hexs
    -- Similarly from dy: get generator e_y ≤ dy with e_y(inr i) ≤ 1
    obtain ⟨sy, hsy_mem, ey, heys, hley_dy⟩ :=
      support_divisible_by_generator (K := K) hgenS (hIφ_span ▸ hdy_Iφ) dy (hsupp_mono dy)
    have hey_bound_inr := generator_exponent_bound (K := K) k i hik
      (Sum.inr i) (Or.inr rfl) hsy_mem heys
    -- Helper: if ex ≤ d₀, get contradiction
    have hne_sx : sx ≠ 0 := by
      obtain ⟨_, ⟨a', b', _, _, _, rfl⟩, rfl⟩ := hsx_mem
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, ne_eq]
      split_ifs
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _)
          (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    have hne_sy : sy ≠ 0 := by
      obtain ⟨_, ⟨a', b', _, _, _, rfl⟩, rfl⟩ := hsy_mem
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, ne_eq]
      split_ifs
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _)
          (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    have hex_Iφ : MvPolynomial.monomial ex (1 : K) ∈ Iφ := by
      have := MvPolynomial.support_nonempty.mpr hne_sx
      obtain ⟨d_wit, hd_wit⟩ := this
      have : ex = d_wit := (Finset.mem_singleton.mp (hexs hd_wit)).symm
      exact hIsM sx (hIφ_span ▸ Ideal.subset_span hsx_mem) ex (this ▸ hd_wit)
    have hey_Iφ : MvPolynomial.monomial ey (1 : K) ∈ Iφ := by
      have := MvPolynomial.support_nonempty.mpr hne_sy
      obtain ⟨d_wit, hd_wit⟩ := this
      have : ey = d_wit := (Finset.mem_singleton.mp (heys hd_wit)).symm
      exact hIsM sy (hIφ_span ▸ Ideal.subset_span hsy_mem) ey (this ▸ hd_wit)
    -- If ex(inl i) = 0, then ex ≤ d₀, contradiction
    by_cases hex_case : ex (Sum.inl i) = 0
    · have hle_d₀ : ex ≤ d₀ := by
        intro w; by_cases hw : w = Sum.inl i
        · rw [hw, hex_case, hxi0]
        · have := hlex_dx w
          simp only [dx, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            show (Sum.inl i : BinomialEdgeVars (Fin n)) = w ↔ w = Sum.inl i from
              ⟨Eq.symm, Eq.symm⟩, hw, if_false, add_zero] at this
          exact this
      exact hd₀_not (hdiv ex hex_Iφ hle_d₀)
    -- If ey(inr i) = 0, then ey ≤ d₀, contradiction
    by_cases hey_case : ey (Sum.inr i) = 0
    · have hle_d₀ : ey ≤ d₀ := by
        intro w; by_cases hw : w = Sum.inr i
        · rw [hw, hey_case, hyi0]
        · have := hley_dy w
          simp only [dy, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            show (Sum.inr i : BinomialEdgeVars (Fin n)) = w ↔ w = Sum.inr i from
              ⟨Eq.symm, Eq.symm⟩, hw, if_false, add_zero] at this
          exact this
      exact hd₀_not (hdiv ey hey_Iφ hle_d₀)
    -- Both ex(inl i) = 1 and ey(inr i) = 1
    have hex_inl : ex (Sum.inl i) = 1 := by omega
    have hey_inr : ey (Sum.inr i) = 1 := by omega
    -- Extract edge info from generators
    -- sx has ex(inl i) = 1, so it's a type B generator x_a * y_b with a = i
    -- (can't be type A since a, b < k ≤ i)
    -- Similarly sy has ey(inr i) = 1, type B with b = i
    -- The generator structure gives edges, and HH transitivity gives the final edge
    -- that divides d₀.
    -- For sx: ∃ a₁ b₁ with edge (a₁, b₁+1), b₁ ≥ k, and x_{a₁} y_{b₁} ∈ Iφ
    -- ex(inl i) = 1 means a₁ = i (since for type A, a,b < k, neither = i)
    -- Also ex(inr i) ≤ 1, and ex(inr i) ≤ d₀(inr i) = 0 (from dx), so b₁ ≠ i
    -- Wait: ex(inr i) ≤ dx(inr i) = d₀(inr i) + 0 = 0, so ex(inr i) = 0
    -- So the generator is x_i * y_{b₁} with b₁ ≠ i, hence b₁ > i
    -- For sy: ey(inr i) = 1 means b₂ = i, and ey(inl i) ≤ d₀(inl i) = 0,
    -- so a₂ ≠ i, hence a₂ < i
    -- HH transitivity: edges (a₂, i+1) and (i, b₁+1) with a₂ < i < b₁
    -- → edge (a₂, b₁+1), so x_{a₂} * y_{b₁} ∈ Iφ
    -- And x_{a₂} | d₀ (from ey, a₂ contributes) and y_{b₁} | d₀ (from ex, b₁ contributes)
    -- So x_{a₂} * y_{b₁} | d₀, hence monomial d₀ 1 ∈ Iφ
    -- Extract edge data from sx and sy
    obtain ⟨_, ⟨a₁, b₁, hb₁, hadj₁, hab₁, rfl⟩, rfl⟩ := hsx_mem
    obtain ⟨_, ⟨a₂, b₂, hb₂, hadj₂, hab₂, rfl⟩, rfl⟩ := hsy_mem
    -- Compute the exponent of the generator image under φ
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hexs heys
    -- Helper: convert singleton support to exponent equality
    have hmono_supp : ∀ (d : BinomialEdgeVars (Fin n) →₀ ℕ),
        (MvPolynomial.monomial d (1 : K)).support = {d} := by
      intro d; exact Finset.Subset.antisymm MvPolynomial.support_monomial_subset
        (Finset.singleton_subset_iff.mpr (hsupp_mono d))
    -- Split on whether b₁ < k
    split_ifs at hexs with hcond₁
    · -- b₁ < k: generator is -(x_{a₁} * x_{b₁})
      -- The exponent only involves inl variables, so ex(inl i) = 0 since a₁, b₁ < k ≤ i
      exfalso; apply hex_case
      have : ex = Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inl b₁) 1 := by
        have hmem : Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inl b₁) 1 ∈
            (X (Sum.inl a₁) * -X (Sum.inl b₁) :
              MvPolynomial (BinomialEdgeVars (Fin n)) K).support := by
          have hprod : (X (Sum.inl a₁) * X (Sum.inl b₁) :
              MvPolynomial (BinomialEdgeVars (Fin n)) K) =
              MvPolynomial.monomial
                (Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inl b₁) 1) 1 := by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]; rfl
          have heq : (X (Sum.inl a₁) * -X (Sum.inl b₁) :
              MvPolynomial (BinomialEdgeVars (Fin n)) K) =
              -(MvPolynomial.monomial
                (Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inl b₁) 1) 1) := by
            rw [mul_neg, hprod]
          rw [heq, MvPolynomial.support_neg]
          exact hsupp_mono _
        exact (Finset.mem_singleton.mp (hexs hmem)).symm
      rw [this]; simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      have : a₁.val < i.val := by omega
      have : b₁.val < i.val := by omega
      simp [show (Sum.inl a₁ : BinomialEdgeVars (Fin n)) ≠ Sum.inl i from
              fun h => by exact absurd (Fin.ext_iff.mp (Sum.inl_injective h)) (by omega),
            show (Sum.inl b₁ : BinomialEdgeVars (Fin n)) ≠ Sum.inl i from
              fun h => by exact absurd (Fin.ext_iff.mp (Sum.inl_injective h)) (by omega)]
    · -- b₁ ≥ k: generator is x_{a₁} * y_{b₁}
      have hex_eq : ex = Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inr b₁) 1 := by
        have hmem : Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inr b₁) 1 ∈
            (X (Sum.inl a₁) * X (Sum.inr b₁) : MvPolynomial _ K).support := by
          simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
            MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial]
          exact one_ne_zero
        exact (Finset.mem_singleton.mp (hexs hmem)).symm
      -- ex(inl i) = 1 → a₁ = i (use contrapositive: if a₁ ≠ i then ex(inl i) = 0)
      have ha₁_eq : a₁ = i := by
        by_contra h
        apply hex_case; rw [hex_eq]
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
        have : (Sum.inl a₁ : BinomialEdgeVars (Fin n)) ≠ Sum.inl i :=
          fun heq => h (Sum.inl_injective heq)
        have : (Sum.inr b₁ : BinomialEdgeVars (Fin n)) ≠ Sum.inl i := Sum.inr_ne_inl
        simp [*]
      -- b₁ ≠ i (from ex(inr i) ≤ dx(inr i) = d₀(inr i) = 0)
      have hb₁_ne_i : b₁ ≠ i := by
        intro hb; apply hex_case
        -- If b₁ = i, then ex(inr i) = 1, but dx(inr i) = d₀(inr i) = 0
        have h1 : ex (Sum.inr i) = 1 := by
          rw [hex_eq, hb]; simp []
        have h2 : ex (Sum.inr i) ≤ 0 := by
          have := hlex_dx (Sum.inr i)
          simp only [dx, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            hyi0] at this
          exact this
        omega
      have hb₁_gt_i : i < b₁ := lt_of_le_of_ne (ha₁_eq ▸ hab₁) (Ne.symm hb₁_ne_i)
      -- y_{b₁} divides d₀
      have hyb₁ : 1 ≤ d₀ (Sum.inr b₁) := by
        have := hlex_dx (Sum.inr b₁)
        rw [hex_eq] at this
        simp only [dx, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] at this
        simp only [
          if_true] at this
        exact this
      -- Split on whether b₂ < k for sy
      split_ifs at heys with hcond₂
      · -- b₂ < k: ey only involves inl vars, so ey(inr i) = 0 → contradiction
        exfalso; apply hey_case
        have : ey = Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1 := by
          have hmem : Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1 ∈
              (X (Sum.inl a₂) * -X (Sum.inl b₂) :
                MvPolynomial (BinomialEdgeVars (Fin n)) K).support := by
            have hprod : (X (Sum.inl a₂) * X (Sum.inl b₂) :
                MvPolynomial (BinomialEdgeVars (Fin n)) K) =
                MvPolynomial.monomial
                  (Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1) 1 := by
              simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]; rfl
            have heq : (X (Sum.inl a₂) * -X (Sum.inl b₂) :
                MvPolynomial (BinomialEdgeVars (Fin n)) K) =
                -(MvPolynomial.monomial
                  (Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1) 1) := by
              rw [mul_neg, hprod]
            rw [heq, MvPolynomial.support_neg]
            exact hsupp_mono _
          exact (Finset.mem_singleton.mp (heys hmem)).symm
        rw [this]; simp []
      · -- b₂ ≥ k: generator is x_{a₂} * y_{b₂}
        have hey_eq : ey = Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₂) 1 := by
          have hmem : Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₂) 1 ∈
              (X (Sum.inl a₂) * X (Sum.inr b₂) : MvPolynomial _ K).support := by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
              MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial]
            exact one_ne_zero
          exact (Finset.mem_singleton.mp (heys hmem)).symm
        -- ey(inr i) = 1 → b₂ = i
        have hb₂_eq : b₂ = i := by
          by_contra h
          apply hey_case; rw [hey_eq]
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
          have : (Sum.inl a₂ : BinomialEdgeVars (Fin n)) ≠ Sum.inr i := Sum.inl_ne_inr
          have : (Sum.inr b₂ : BinomialEdgeVars (Fin n)) ≠ Sum.inr i :=
            fun heq => h (Sum.inr_injective heq)
          simp [*]
        -- a₂ ≠ i (from ey(inl i) ≤ dy(inl i) = d₀(inl i) = 0)
        have ha₂_ne_i : a₂ ≠ i := by
          intro ha
          have h1 : ey (Sum.inl i) = 1 := by
            rw [hey_eq, hb₂_eq, ha]
            simp []
          have h2 : ey (Sum.inl i) ≤ 0 := by
            have := hley_dy (Sum.inl i)
            simp only [dy, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
              
              hxi0] at this
            exact this
          omega
        have ha₂_lt_i : a₂ < i := lt_of_le_of_ne (hb₂_eq ▸ hab₂) ha₂_ne_i
        -- x_{a₂} divides d₀
        have hxa₂ : 1 ≤ d₀ (Sum.inl a₂) := by
          have := hley_dy (Sum.inl a₂)
          rw [hey_eq] at this
          simp only [dy, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            
            
            if_true] at this
          exact this
        -- HH transitivity: edges (a₂, i+1) and (i, b₁+1) with a₂ < i < b₁ → edge (a₂, b₁+1)
        have hadj_trans : G.Adj a₂ ⟨b₁.val + 1, hb₁⟩ :=
          hHH.transitivity a₂ i b₁ hi hb₁ ha₂_lt_i hb₁_gt_i (hb₂_eq ▸ hadj₂) (ha₁_eq ▸ hadj₁)
        -- x_{a₂} * y_{b₁} ∈ bipartiteEdgeMonomialIdeal
        have hgen_mem : X (Sum.inl a₂) * X (Sum.inr b₁) ∈
            bipartiteEdgeMonomialIdeal (K := K) G :=
          Ideal.subset_span ⟨a₂, b₁, hb₁, hadj_trans,
            le_of_lt (lt_trans ha₂_lt_i hb₁_gt_i), rfl⟩
        -- Its image under φ is itself (since b₁ ≥ k)
        have hgen_Iφ : MvPolynomial.monomial
            (Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₁) 1) (1 : K) ∈ Iφ := by
          have heq : (X (Sum.inl a₂) * X (Sum.inr b₁) : MvPolynomial _ K) =
              MvPolynomial.monomial
                (Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₁) 1) 1 := by
            simp [MvPolynomial.X, MvPolynomial.monomial_mul]
          have himg := Ideal.mem_map_of_mem (diagSubstHom (K := K) k).toRingHom hgen_mem
          simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
            MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at himg
          simp only [show ¬(b₁.val < k ∧ b₁.val + 1 < n) from fun ⟨h, _⟩ => hcond₁ ⟨h, hb₁⟩,
            if_false] at himg
          rwa [heq] at himg
        -- single(inl a₂) 1 + single(inr b₁) 1 ≤ d₀
        have hle_d₀ : Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₁) 1 ≤ d₀ := by
          intro w
          simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
          have hdisjoint : w = Sum.inl a₂ → w ≠ Sum.inr b₁ := fun h₁ h₂ =>
            absurd (h₁.symm.trans h₂) Sum.inl_ne_inr
          rcases Classical.em (w = Sum.inl a₂) with h₁ | h₁
          · subst h₁
            have h₂ : Sum.inl a₂ ≠ Sum.inr b₁ := Sum.inl_ne_inr
            rw [if_pos rfl, if_neg (Ne.symm h₂), add_zero]; exact hxa₂
          · rw [if_neg (Ne.symm h₁), zero_add]
            split_ifs with h₂
            · subst h₂; exact hyb₁
            · exact Nat.zero_le _
        exact hd₀_not (hdiv _ hgen_Iφ hle_d₀)

private theorem isSMulRegular_map_diagSubstHom {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        Ideal.map (diagSubstHom (K := K) k).toRingHom
          (bipartiteEdgeMonomialIdeal (K := K) G))
      (Ideal.Quotient.mk
        (Ideal.map (diagSubstHom (K := K) k).toRingHom
          (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl i) + X (Sum.inr i))) := by
  set Iφ := Ideal.map (diagSubstHom (K := K) k).toRingHom
    (bipartiteEdgeMonomialIdeal (K := K) G)
  apply isSMulRegular_of_radical_step
  · -- NZD on S / √(Iφ): use radical + prime avoidance
    exact isSMulRegular_of_radical_not_mem_minimalPrimes
      Iφ.radical_isRadical
      (fun P hP => by
        -- minimal primes of √(Iφ) = minimal primes of Iφ
        rw [Ideal.radical_minimalPrimes] at hP
        exact ell_not_mem_minimalPrime_map_diagSubstHom (K := K) hHH i hi hik hP)
  · exact nilradical_nzd_map_diagSubstHom (K := K) hHH i hi hik

/-- **Iterated regularity**: Under HH conditions, `x_i + y_i` is a non-zero-divisor
on `S / (I ⊔ diag)` where `I = bipartiteEdgeMonomialIdeal G` and
`diag = diagonalSumIdeal n k`, for any `i` with `k ≤ i.val` and `i.val + 1 < n`.

Proof via the diagonal substitution `φ`:
- Apply `φ` (which kills `diag`) to reduce to NZD on `S / I.map φ` (monomial ideal).
- Use `f - φ(f) ∈ diag` and `I.map φ ⊆ J` to transfer back. -/
theorem sum_XY_isSMulRegular_mod_diagonalSum {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        (bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G ⊔
        diagonalSumIdeal (K := K) n k) (X (Sum.inl i) + X (Sum.inr i))) := by
  set J := bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set diag := diagonalSumIdeal (K := K) n k
  set ℓ : MvPolynomial (BinomialEdgeVars (Fin n)) K := X (Sum.inl i) + X (Sum.inr i)
  set φ := diagSubstHom (K := K) k
  set Iφ := Ideal.map φ.toRingHom I
  -- Lift to the polynomial ring
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul, Ideal.Quotient.eq] at hab ⊢
  set c := a' - b'
  have hℓc : ℓ * c ∈ J := by rw [mul_sub]; exact hab
  -- Step 1: Apply φ to get ℓ * φ(c) ∈ I.map φ
  have h_map_mem : φ.toRingHom (ℓ * c) ∈ Iφ :=
    map_sup_diag_le (K := K) k (Ideal.mem_map_of_mem φ.toRingHom hℓc)
  rw [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    diagSubstHom_fix_ell (K := K) k i hik] at h_map_mem
  -- h_map_mem : ℓ * φ(c) ∈ Iφ
  -- Step 2: NZD on S / Iφ gives φ(c) ∈ Iφ
  have h_nzd := isSMulRegular_map_diagSubstHom (K := K) hHH i hi hik
  have hφc_mem : φ c ∈ Iφ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : Ideal.Quotient.mk Iφ ℓ * Ideal.Quotient.mk Iφ (φ c) = 0 := by
      rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h_map_mem
    exact h_nzd (show _ • _ = _ • _ from by
      simp only [smul_eq_mul, mul_zero]; exact h1)
  -- Step 3: c = (c - φ(c)) + φ(c) ∈ diag + Iφ ⊆ J
  have h_diff : c - φ c ∈ diag :=
    diagSubstHom_congr_mod_diag (K := K) k c
  have h_Iφ_le : Iφ ≤ J := map_diagSubstHom_le (K := K) k
  change c ∈ J
  have : c = (c - φ c) + φ c := by ring
  rw [this]
  exact J.add_mem (Ideal.mem_sup_right h_diff) (h_Iφ_le hφc_mem)

/-! ### Weakly regular sequence packaging -/

section WeaklyRegularPackaging

variable {K : Type*} [Field K]

open RingTheory.Sequence MvPolynomial

/-- Membership in `J.map mk_I` is equivalent to membership in `I ⊔ J`. -/
private lemma mem_map_mk_iff_mem_sup {R : Type*} [CommRing R]
    {I J : Ideal R} (x : R) :
    Ideal.Quotient.mk I x ∈ J.map (Ideal.Quotient.mk I) ↔ x ∈ I ⊔ J := by
  constructor
  · intro h
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h
    obtain ⟨j, hj, hjx⟩ := h
    rw [Ideal.Quotient.eq] at hjx
    have : x - j ∈ I := by
      rw [show x - j = -(j - x) from by ring]; exact I.neg_mem hjx
    rw [show x = (x - j) + j from by ring]
    exact (I ⊔ J).add_mem (Ideal.mem_sup_left this) (Ideal.mem_sup_right hj)
  · intro h
    have : Ideal.Quotient.mk I x ∈ (I ⊔ J).map (Ideal.Quotient.mk I) :=
      Ideal.mem_map_of_mem _ h
    rwa [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq] at this

/-- Transfer of `IsSMulRegular` through double quotient: if `r` is a NZD on
`R ⧸ (I ⊔ J)`, then `mk_I(r)` is a NZD on `(R ⧸ I) ⧸ J.map mk_I`
(where the scalar action uses the `R ⧸ I`-algebra structure). -/
private lemma isSMulRegular_of_doubleQuot {R : Type*} [CommRing R]
    {I J : Ideal R} {r : R}
    (hreg : IsSMulRegular (R ⧸ (I ⊔ J))
      (Ideal.Quotient.mk (I ⊔ J) r)) :
    IsSMulRegular ((R ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
      (Ideal.Quotient.mk I r) := by
  set mkI := Ideal.Quotient.mk I
  set mkIJ := Ideal.Quotient.mk (I ⊔ J)
  set mkJ' := Ideal.Quotient.mk (Ideal.map mkI J)
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨a'', rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨b'', rfl⟩ := Ideal.Quotient.mk_surjective b'
  change mkI r • mkJ' (mkI a'') = mkI r • mkJ' (mkI b'') at hab
  simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] at hab
  have hab' : mkJ' (mkI (r * a'')) = mkJ' (mkI (r * b'')) := by
    rwa [map_mul mkI r a'', map_mul mkI r b'']
  rw [Ideal.Quotient.eq, ← map_sub, mem_map_mk_iff_mem_sup,
      show r * a'' - r * b'' = r * (a'' - b'') from by ring] at hab'
  rw [Ideal.Quotient.eq, ← map_sub, mem_map_mk_iff_mem_sup]
  have h1 : mkIJ r * mkIJ (a'' - b'') = 0 := by
    rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hab'
  have h2 := hreg (show mkIJ r • mkIJ (a'' - b'') = mkIJ r • 0 from by
    rw [smul_eq_mul, smul_zero]; exact h1)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

/-- For the self-module of a ring, `I • ⊤ = I` as a submodule. -/
private lemma ideal_smul_top_self {R : Type*} [CommRing R] (I : Ideal R) :
    I • (⊤ : Submodule R R) = I.restrictScalars R := by
  rw [Ideal.smul_top_eq_map, show algebraMap R R = RingHom.id R from rfl,
      Ideal.map_id]

/-- `Ideal.ofList` commutes with ring homomorphism maps. -/
private lemma Ideal.ofList_map {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (rs : List R) :
    (Ideal.ofList rs).map f = Ideal.ofList (rs.map f) := by
  simp only [Ideal.ofList, Ideal.map_span]
  congr 1; ext x; simp [List.mem_map]

/-- The step-`i` module quotient in `IsWeaklyRegular` on the self-module
of `R ⧸ I` matches the double quotient `(R ⧸ I) ⧸ J.map mk_I`. -/
private lemma self_module_step_eq {R : Type*} [CommRing R]
    {I : Ideal R} (rs : List R) (i : ℕ) :
    Ideal.ofList (List.take i (rs.map (Ideal.Quotient.mk I))) •
      (⊤ : Submodule (R ⧸ I) (R ⧸ I)) =
    ((Ideal.ofList (List.take i rs)).map
      (Ideal.Quotient.mk I)).restrictScalars (R ⧸ I) := by
  rw [ideal_smul_top_self]; congr 1
  rw [← List.map_take, Ideal.ofList_map]

/-- The i-th diagonal linear form `x_i + y_i` for `i < n - 1`. -/
private noncomputable def diagElem (n : ℕ) (j : Fin (n - 1)) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  X (Sum.inl (j.castLE (by omega))) + X (Sum.inr (j.castLE (by omega)))

/-- The ordered list of diagonal linear forms `[x₀+y₀, …, x_{n-2}+y_{n-2}]`. -/
private noncomputable def diagElems (n : ℕ) :
    List (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
  List.ofFn (diagElem (K := K) n)

/-- The ideal generated by the first `k` diagonal elements equals
`diagonalSumIdeal n k` when `k ≤ n - 1`. -/
private lemma diagElems_ofList_take_eq {n : ℕ} (k : ℕ) (hk : k ≤ n - 1) :
    Ideal.ofList ((diagElems (K := K) n).take k) =
      diagonalSumIdeal (K := K) n k := by
  simp only [Ideal.ofList, diagonalSumIdeal, diagElems]
  congr 1; ext f
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem,
    List.length_ofFn, List.getElem_ofFn, Nat.min_eq_left hk]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjn : j < n := by omega
    exact ⟨⟨j, hjn⟩, (show (⟨j, hjn⟩ : Fin n).val < k from hj),
      (show (⟨j, hjn⟩ : Fin n).val + 1 < n from by simp; omega),
      by simp [diagElem, Fin.castLE]⟩
  · rintro ⟨i, hik, _, rfl⟩
    exact ⟨i.val, by omega, by simp [diagElem, Fin.castLE]⟩

/-- **Weakly regular sequence packaging**: Under HH conditions, the diagonal
elements `[mk(x₀+y₀), …, mk(x_{n-2}+y_{n-2})]` form a weakly regular
sequence on the self-module of `S ⧸ bipartiteEdgeMonomialIdeal G`.

This packages the iterated regularity theorem
`sum_XY_isSMulRegular_mod_diagonalSum` into the Mathlib `IsWeaklyRegular`
format, using the bridge lemmas `isSMulRegular_of_doubleQuot`,
`ideal_smul_top_self`, and `self_module_step_eq`. -/
theorem bipartiteEdgeMonomialIdeal_isWeaklyRegular
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsWeaklyRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G)
      ((diagElems (K := K) n).map
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))) := by
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set mkI := Ideal.Quotient.mk I
  set rs := diagElems (K := K) n
  refine IsWeaklyRegular.mk fun idx hidx => ?_
  have hlen : rs.length = n - 1 := List.length_ofFn
  have hidx' : idx < n - 1 := by
    simp [rs, diagElems] at hidx; omega
  have hidxn : idx < n := by omega
  -- Rewrite the module quotient to a double-quotient ring quotient
  rw [self_module_step_eq rs idx, diagElems_ofList_take_eq idx (by omega)]
  -- Identify the idx-th element
  simp only [List.getElem_map, rs, diagElems, List.getElem_ofFn]
  -- Transfer regularity through the double quotient
  apply isSMulRegular_of_doubleQuot (I := I)
    (J := diagonalSumIdeal (K := K) n idx)
  -- Close with the iterated regularity theorem
  simp only [diagElem, Fin.castLE]
  have : (⟨idx, hidxn⟩ : Fin n).val + 1 < n := by simp; omega
  exact sum_XY_isSMulRegular_mod_diagonalSum hHH ⟨idx, hidxn⟩ this le_rfl

/-- The weakly regular sequence has length `n - 1`. -/
theorem diagElems_length {n : ℕ} :
    (diagElems (K := K) n).length = n - 1 := List.length_ofFn

end WeaklyRegularPackaging

/-! ### Krull dimension of radical equidimensional quotients -/

/-- For a radical ideal `I` in a Noetherian ring with all minimal prime
quotients having the same Krull dimension `d`, the quotient `R ⧸ I` also
has Krull dimension `d`.

Uses `ringKrullDim_quotient_radical` (the sup formula) together with
equidimensionality to compute the sup as a constant. -/
theorem ringKrullDim_quotient_radical_equidim {R : Type*} [CommRing R]
    [IsNoetherianRing R]
    {I : Ideal R} (hne : I ≠ ⊤) (hrad : I.IsRadical)
    {d : WithBot ℕ∞}
    (hequidim : ∀ P ∈ I.minimalPrimes, ringKrullDim (R ⧸ P) = d) :
    ringKrullDim (R ⧸ I) = d := by
  -- minimalPrimes is nonempty since I ≠ ⊤
  have hne_mp : I.minimalPrimes.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact (Ideal.minimalPrimes_eq_empty_iff I).not.mpr hne
  obtain ⟨P₀, hP₀⟩ := hne_mp
  -- Use the sup formula
  rw [ringKrullDim_quotient_radical I hrad]
  apply le_antisymm
  · -- ≤: every term in the sup equals d
    exact iSup₂_le fun P hP => (hequidim P hP).le
  · -- ≥: the sup is ≥ d (using P₀)
    exact le_iSup₂_of_le P₀ hP₀ (hequidim P₀ hP₀).ge

/-! ### HH quotient dimension formula -/

section HHDimension

variable {K : Type*} [Field K]

open MvPolynomial

/-- `{i : Fin n // i.val + 1 < n}` has cardinality `n - 1`. -/
private lemma card_active_indices (n : ℕ) :
    Nat.card {i : Fin n // i.val + 1 < n} = n - 1 := by
  rw [Nat.card_eq_fintype_card, show Fintype.card {i : Fin n // i.val + 1 < n} =
    Fintype.card (Fin (n - 1)) from ?_, Fintype.card_fin]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨i, hi⟩ => ⟨i.val, by omega⟩
    invFun := fun ⟨j, hj⟩ => ⟨⟨j, by omega⟩, by change j + 1 < n; omega⟩
    left_inv := fun ⟨i, hi⟩ => by simp
    right_inv := fun ⟨j, hj⟩ => by simp
  }

/-- Under HH conditions, any minimal vertex cover of `hhEdgeSet G` has exactly
`n - 1` elements. -/
private theorem minimalVertexCover_ncard_val {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {S : Set (BinomialEdgeVars (Fin n))}
    (hS : MvPolynomial.IsMinimalVertexCover (hhEdgeSet G) S) :
    S.ncard = n - 1 := by
  rw [← Nat.card_coe_set_eq S]
  have hS_bij : Function.Bijective
      (fun v : S => (⟨coverToIndex hS v, (coverToIndex_spec hS v).2⟩ :
        {i : Fin n // i.val + 1 < n})) :=
    ⟨fun a b h => coverToIndex_injective hHH hS (Subtype.ext_iff.mp h),
     fun ⟨i, hi⟩ => by
      obtain ⟨v, hv⟩ := (coverToIndex_range hHH hS ▸ hi : i ∈ Set.range (coverToIndex hS))
      exact ⟨v, Subtype.ext hv⟩⟩
  rw [Nat.card_eq_of_bijective _ hS_bij, card_active_indices]

/-- The bipartite edge monomial ideal is a proper ideal. -/
private lemma bipartiteEdgeMonomialIdeal_ne_top {n : ℕ} (G : SimpleGraph (Fin n)) :
    bipartiteEdgeMonomialIdeal (K := K) G ≠ ⊤ := by
  rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
  intro h
  have hle : MvPolynomial.variablePairIdeal (R := K) (hhEdgeSet G) ≤
      Ideal.span (MvPolynomial.X '' Set.univ) :=
    MvPolynomial.variablePairIdeal_le_span_X_iff.mpr fun _ _ _ => Or.inl trivial
  exact (MvPolynomial.isPrime_span_X_image_set (R := K)
    (Set.univ : Set (BinomialEdgeVars (Fin n)))).ne_top
    (eq_top_iff.mpr (h ▸ hle))

/-- **HH quotient dimension formula**: Under HH conditions,
`dim(S ⧸ bipartiteEdgeMonomialIdeal G) = n + 1`.

Proof: the ideal is radical with equidimensional minimal primes. Each
minimal prime `span(X '' C)` corresponds to a minimal vertex cover `C`
with `n - 1` elements, yielding quotient dimension `2n - (n - 1) = n + 1`.
The result follows from `ringKrullDim_quotient_radical_equidim`. -/
theorem ringKrullDim_bipartiteEdgeMonomialIdeal {n : ℕ} (hn : 0 < n)
    {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) = ↑(n + 1 : ℕ) := by
  apply ringKrullDim_quotient_radical_equidim
    (bipartiteEdgeMonomialIdeal_ne_top G) (bipartiteEdgeMonomialIdeal_isRadical G)
  intro P hP
  obtain ⟨C, hCcover, rfl⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hP
  haveI : Fintype ↑C := Set.Finite.fintype (Set.toFinite C)
  rw [show MvPolynomial.X '' C =
      (↑C.toFinset : Set _).image MvPolynomial.X from by rw [Set.coe_toFinset]]
  rw [MvPolynomial.ringKrullDim_quotient_span_X_image]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_coe]
  have hncard := minimalVertexCover_ncard_val hHH hCcover
  rw [Set.ncard_eq_toFinset_card' C] at hncard
  rw [hncard]; simp only [BinomialEdgeVars, Fintype.card_sum, Fintype.card_fin]
  congr 1; omega

end HHDimension

/-! ### NZD of `X(inl ⟨n-1,_⟩)` on `S ⧸ (I ⊔ diag_{n-1})` -/

section XInlLastNZD

variable {K : Type*} [Field K]

open MvPolynomial

/-- Every generator of `I.map φ_{n-1}` has exponent 0 at `Sum.inl ⟨n-1,_⟩`.

When `k = n - 1`, the generators of `bipartiteEdgeMonomialIdeal G` are
`X(inl a) * X(inr b)` with `b.val + 1 < n` (i.e. `b.val ≤ n-2`).
Under `φ_{n-1}`, `X(inr b)` maps to `-X(inl b)` since `b.val < n-1`.
So every generator image is `±X(inl a) * X(inl b)` with `a, b ≤ n-2 < n-1`,
hence exponent 0 at `Sum.inl ⟨n-1,_⟩`. -/
private theorem generator_exponent_zero_at_inl_last {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)}
    {s : MvPolynomial (BinomialEdgeVars (Fin n)) K}
    (hs : s ∈ (diagSubstHom (K := K) (n - 1)).toRingHom ''
      { m : MvPolynomial (BinomialEdgeVars (Fin n)) K |
        ∃ (a b : Fin n) (_ : b.val + 1 < n),
        G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
        m = X (Sum.inl a) * X (Sum.inr b) })
    {e : BinomialEdgeVars (Fin n) →₀ ℕ} (hes : s.support ⊆ {e}) :
    e (Sum.inl ⟨n - 1, by omega⟩) = 0 := by
  obtain ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩ := hs
  simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
    MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hes
  -- b.val < n - 1 since b.val + 1 < n, so the condition is satisfied
  have hb_cond : b.val < n - 1 ∧ b.val + 1 < n := ⟨by omega, hb⟩
  rw [if_pos hb_cond] at hes
  -- Generator image is X(inl a) * (-X(inl b)) = -(X(inl a) * X(inl b))
  -- with exponent vector single(inl a) 1 + single(inl b) 1
  set e' : BinomialEdgeVars (Fin n) →₀ ℕ :=
    Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1
  have hab_val : a.val ≤ b.val := hab
  have hsupp : (X (Sum.inl a) * -X (Sum.inl b) :
      MvPolynomial (BinomialEdgeVars (Fin n)) K).support ⊆ {e'} := by
    rw [show X (Sum.inl a) * -X (Sum.inl b) =
      -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring]
    rw [show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
      MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
        Finsupp.single (Sum.inl b) 1) 1 from by
        simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
    rw [MvPolynomial.support_neg]; exact MvPolynomial.support_monomial_subset
  have hs_ne : (X (Sum.inl a) * -X (Sum.inl b) :
      MvPolynomial (BinomialEdgeVars (Fin n)) K) ≠ 0 :=
    mul_ne_zero (MvPolynomial.X_ne_zero _) (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
  -- e = e' since both are the unique support element
  have he_eq : e = e' := by
    obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
    exact (Finset.mem_singleton.mp (hes hd_wit)).symm.trans
      (Finset.mem_singleton.mp (hsupp hd_wit))
  rw [he_eq]; simp only [e', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
  -- a.val ≤ b.val ≤ n-2 < n-1, so both singles are 0 at inl ⟨n-1,_⟩
  have ha_ne : (Sum.inl a : BinomialEdgeVars (Fin n)) ≠ Sum.inl ⟨n - 1, by omega⟩ :=
    fun h => by
      have heq := congr_arg Fin.val (Sum.inl_injective h)
      simp at heq; omega
  have hb_ne : (Sum.inl b : BinomialEdgeVars (Fin n)) ≠ Sum.inl ⟨n - 1, by omega⟩ :=
    fun h => by
      have heq := congr_arg Fin.val (Sum.inl_injective h)
      simp at heq; omega
  simp [ha_ne, hb_ne]

/-- `φ_{n-1}` fixes `X(inl ⟨n-1,_⟩)`: the diagonal substitution acts as
identity on all `inl` variables. -/
private theorem diagSubstHom_fix_X_inl_last {n : ℕ} (hn : 2 ≤ n) :
    diagSubstHom (K := K) (n - 1)
      (X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))) =
    X (Sum.inl ⟨n - 1, by omega⟩) := by
  simp only [diagSubstHom, MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl]

/-- `X(inl ⟨n-1,_⟩)` is a NZD on `S ⧸ I.map φ_{n-1}`.

Proof: the monomial ideal `I.map φ_{n-1}` is generated by monomials
not involving `Sum.inl ⟨n-1,_⟩`. The standard monomial-divisibility
argument shows that if `X_v · c ∈ I` then `c ∈ I`. -/
private theorem X_inl_last_isSMulRegular_map_diagSubstHom {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
          (bipartiteEdgeMonomialIdeal (K := K) G))
      (Ideal.Quotient.mk
        (Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
          (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl (⟨n - 1, by omega⟩ : Fin n)))) := by
  set Iφ := Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
    (bipartiteEdgeMonomialIdeal (K := K) G) with hIφ_def
  set v : BinomialEdgeVars (Fin n) := Sum.inl ⟨n - 1, by omega⟩
  have hIsM : Iφ.IsMonomial := hIφ_def ▸ isMonomial_map_diagSubstHom (K := K) G (n - 1)
  -- Lift to polynomial ring and prove by contradiction
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul, Ideal.Quotient.eq] at hab ⊢
  set c := a' - b'
  have hvc : X v * c ∈ Iφ := by rw [mul_sub]; exact hab
  -- Prove c ∈ Iφ by contradiction
  by_contra hc_not
  obtain ⟨d₀, hd₀_supp, hd₀_not⟩ := Ideal.not_mem_exists_monomial_notMem hc_not
  have hcoeff_ne : MvPolynomial.coeff d₀ c ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd₀_supp
  -- d' = d₀ + e_v is in support of X_v * c
  set d' : BinomialEdgeVars (Fin n) →₀ ℕ :=
    d₀ + (Finsupp.single v 1 : BinomialEdgeVars (Fin n) →₀ ℕ)
  have hd'_supp : d' ∈ (X v * c).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul']
    have : v ∈ d'.support := by
      rw [Finsupp.mem_support_iff]; simp [d']
    rw [if_pos this]; convert hcoeff_ne using 1; congr 1; ext w
    simp only [d', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
      Pi.add_apply, Finsupp.single_apply]; split <;> omega
  -- monomial d' 1 ∈ Iφ by IsMonomial
  have hd'_Iφ : MvPolynomial.monomial d' (1 : K) ∈ Iφ := hIsM _ hvc d' hd'_supp
  -- Use support_divisible_by_generator to find generator exponent e ≤ d'
  set genSet : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
    (diagSubstHom (K := K) (n - 1)).toRingHom ''
      { m | ∃ (a b : Fin n) (_ : b.val + 1 < n),
        G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
        m = X (Sum.inl a) * X (Sum.inr b) }
  have hIφ_span : Iφ = Ideal.span genSet := by
    rw [hIφ_def]; unfold bipartiteEdgeMonomialIdeal; rw [Ideal.map_span]
  have hgenS : ∀ s ∈ genSet, ∃ e, s.support ⊆ {e} := by
    rintro _ ⟨_, ⟨a', b', hb', hadj, hab', rfl⟩, rfl⟩
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
    split_ifs with hcond
    · exact ⟨Finsupp.single (Sum.inl a') 1 + Finsupp.single (Sum.inl b') 1, by
        rw [show X (Sum.inl a') * -X (Sum.inl b') =
          -(X (Sum.inl a') * X (Sum.inl b') : MvPolynomial _ K) from by ring]
        rw [show (X (Sum.inl a') * X (Sum.inl b') : MvPolynomial _ K) =
          MvPolynomial.monomial (Finsupp.single (Sum.inl a') 1 +
            Finsupp.single (Sum.inl b') 1) 1 from by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
        rw [MvPolynomial.support_neg]
        exact MvPolynomial.support_monomial_subset⟩
    · exact ⟨Finsupp.single (Sum.inl a') 1 + Finsupp.single (Sum.inr b') 1, by
        rw [show (X (Sum.inl a') * X (Sum.inr b') : MvPolynomial _ K) =
          MvPolynomial.monomial (Finsupp.single (Sum.inl a') 1 +
            Finsupp.single (Sum.inr b') 1) 1 from by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
        exact MvPolynomial.support_monomial_subset⟩
  have hd'_supp_d' : d' ∈ (MvPolynomial.monomial d' (1 : K)).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]
    exact one_ne_zero
  obtain ⟨s, hs_mem, e, hes, hle_d'⟩ :=
    support_divisible_by_generator (K := K) hgenS (hIφ_span ▸ hd'_Iφ) d' hd'_supp_d'
  -- e(v) = 0 since generators don't involve v
  have he_zero := generator_exponent_zero_at_inl_last (K := K) hn hs_mem hes
  -- e ≤ d₀: for w = v, e(v) = 0 ≤ d₀(v); for w ≠ v, e(w) ≤ d'(w) = d₀(w)
  have hle_d₀ : e ≤ d₀ := by
    intro w
    by_cases hw : w = v
    · subst hw; rw [he_zero]; exact Nat.zero_le _
    · have := hle_d' w
      simp only [d', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        show v = w ↔ w = v from ⟨fun h => h.symm, fun h => h.symm⟩,
        hw, if_false, add_zero] at this
      exact this
  -- monomial e 1 ∈ Iφ
  have hs_Iφ : s ∈ Iφ := hIφ_span ▸ Ideal.subset_span hs_mem
  have hs_ne : s ≠ 0 := by
    obtain ⟨_, ⟨a', b', _, _, _, rfl⟩, rfl⟩ := hs_mem
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, ne_eq]
    split_ifs
    · exact mul_ne_zero (MvPolynomial.X_ne_zero _)
        (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
    · exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
  have he_supp : e ∈ s.support := by
    obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
    have := Finset.mem_singleton.mp (hes hd_wit)
    rwa [← this]
  have he_Iφ : MvPolynomial.monomial e (1 : K) ∈ Iφ := hIsM s hs_Iφ e he_supp
  -- monomial d₀ 1 = monomial(d₀ - e) 1 * monomial e 1 ∈ Iφ
  have hd₀_Iφ : MvPolynomial.monomial d₀ (1 : K) ∈ Iφ := by
    have : MvPolynomial.monomial d₀ (1 : K) =
        MvPolynomial.monomial (d₀ - e) 1 * MvPolynomial.monomial e 1 := by
      rw [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hle_d₀]
    rw [this]; exact Iφ.mul_mem_left _ he_Iφ
  exact hd₀_not hd₀_Iφ

/-- Under HH conditions, `X(Sum.inl ⟨n-1,_⟩)` is a NZD on
`S ⧸ (bipartiteEdgeMonomialIdeal G ⊔ diagonalSumIdeal n (n-1))`.

Proof via the diagonal substitution `φ = diagSubstHom (n-1)`:
1. Apply `φ` (which kills `diag`) to reduce to NZD on `S ⧸ I.map φ`.
2. `φ` fixes `X(inl ⟨n-1,_⟩)` since `diagSubstFun` returns `X(inl j)` for all `inl` inputs.
3. NZD of `X(inl ⟨n-1,_⟩)` on `S ⧸ I.map φ` follows from monomial ideal structure
   (generators don't involve this variable).
4. Transfer back using `c - φ(c) ∈ diag`. -/
theorem X_inl_last_isSMulRegular_mod_diagonalSum {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        (bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n (n - 1)))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G ⊔
        diagonalSumIdeal (K := K) n (n - 1))
        (X (Sum.inl (⟨n - 1, by omega⟩ : Fin n)))) := by
  set J := bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n (n - 1)
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set diag := diagonalSumIdeal (K := K) n (n - 1)
  set xv : MvPolynomial (BinomialEdgeVars (Fin n)) K :=
    X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))
  set φ := diagSubstHom (K := K) (n - 1)
  set Iφ := Ideal.map φ.toRingHom I
  -- Lift to the polynomial ring
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul, Ideal.Quotient.eq] at hab ⊢
  set c := a' - b'
  have hxvc : xv * c ∈ J := by rw [mul_sub]; exact hab
  -- Step 1: Apply φ to get xv * φ(c) ∈ Iφ
  have h_map_mem : φ.toRingHom (xv * c) ∈ Iφ :=
    map_sup_diag_le (K := K) (n - 1) (Ideal.mem_map_of_mem φ.toRingHom hxvc)
  rw [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    diagSubstHom_fix_X_inl_last (K := K) hn] at h_map_mem
  -- h_map_mem : xv * φ(c) ∈ Iφ
  -- Step 2: NZD on S / Iφ gives φ(c) ∈ Iφ
  have h_nzd := X_inl_last_isSMulRegular_map_diagSubstHom (K := K) hn (G := G)
  have hφc_mem : φ c ∈ Iφ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : Ideal.Quotient.mk Iφ xv * Ideal.Quotient.mk Iφ (φ c) = 0 := by
      rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h_map_mem
    exact h_nzd (show _ • _ = _ • _ from by
      simp only [smul_eq_mul, mul_zero]; exact h1)
  -- Step 3: c = (c - φ(c)) + φ(c) ∈ diag + Iφ ⊆ J
  have h_diff : c - φ c ∈ diag :=
    diagSubstHom_congr_mod_diag (K := K) (n - 1) c
  have h_Iφ_le : Iφ ≤ J := map_diagSubstHom_le (K := K) (n - 1)
  change c ∈ J
  have : c = (c - φ c) + φ c := by ring
  rw [this]
  exact J.add_mem (Ideal.mem_sup_right h_diff) (h_Iφ_le hφc_mem)

end XInlLastNZD

/-! ### NZD of `X(inr ⟨n-1,_⟩)` on `S ⧸ (I ⊔ diag_{n-1} ⊔ ⟨x_{n-1}⟩)` -/

section XInrLastNZD

variable {K : Type*} [Field K]

open MvPolynomial

/-- `φ_{n-1}` fixes `X(inr ⟨n-1,_⟩)`: since `diagSubstFun (n-1)` has
condition `j.val < n-1`, which is false for `j = ⟨n-1,_⟩`. -/
private theorem diagSubstHom_fix_X_inr_last {n : ℕ} (hn : 2 ≤ n) :
    diagSubstHom (K := K) (n - 1)
      (X (Sum.inr (⟨n - 1, by omega⟩ : Fin n))) =
    X (Sum.inr ⟨n - 1, by omega⟩) := by
  simp only [diagSubstHom, MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inr]
  split_ifs with h
  · omega
  · rfl

/-- `(I ⊔ diag ⊔ ⟨x_{n-1}⟩).map φ ≤ I.map φ ⊔ ⟨x_{n-1}⟩`:
φ kills diag, maps I to I.map φ, and fixes `x_{n-1}`. -/
private theorem map_sup_diag_sup_span_inl_le {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} :
    Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n (n - 1) ⊔
        Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))}) ≤
    Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G) ⊔
      Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))} := by
  set φ := (diagSubstHom (K := K) (n - 1)).toRingHom
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set diag := diagonalSumIdeal (K := K) n (n - 1)
  set xv : MvPolynomial (BinomialEdgeVars (Fin n)) K :=
    X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))
  -- (I ⊔ diag ⊔ span{xv}).map φ = (I ⊔ diag).map φ ⊔ span{xv}.map φ
  rw [Ideal.map_sup]
  apply sup_le_sup
  · -- (I ⊔ diag).map φ ≤ I.map φ
    exact map_sup_diag_le (K := K) (n - 1)
  · -- span{xv}.map φ ≤ span{xv}
    rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨p, hp, rfl⟩
    rw [Set.mem_singleton_iff.mp hp]
    change (diagSubstHom (K := K) (n - 1) xv) ∈ _
    rw [diagSubstHom_fix_X_inl_last (K := K) hn]
    exact Ideal.mem_span_singleton_self xv

/-- `I.map φ ⊔ ⟨x_{n-1}⟩ ≤ I ⊔ diag ⊔ ⟨x_{n-1}⟩`. -/
private theorem map_diagSubstHom_sup_span_le {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} :
    Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G) ⊔
      Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))} ≤
    bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n (n - 1) ⊔
      Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))} := by
  exact sup_le_sup_right (map_diagSubstHom_le (K := K) (n - 1)) _

/-- `I.map φ ⊔ ⟨x_{n-1}⟩` is a monomial ideal: both pieces are monomial. -/
private theorem isMonomial_map_diagSubstHom_sup_span {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) :
    (Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
      (bipartiteEdgeMonomialIdeal (K := K) G) ⊔
      Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))}).IsMonomial := by
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set Iφ := Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom I
  set xv : BinomialEdgeVars (Fin n) := Sum.inl ⟨n - 1, by omega⟩
  -- Write Iφ ⊔ span{X xv} as a single span
  set genI := (diagSubstHom (K := K) (n - 1)).toRingHom ''
    { m : MvPolynomial (BinomialEdgeVars (Fin n)) K |
      ∃ (a b : Fin n) (_ : b.val + 1 < n),
      G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
      m = X (Sum.inl a) * X (Sum.inr b) }
  set genX := ({X xv} : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K))
  have hIφ_span : Iφ = Ideal.span genI := by
    change Ideal.map _ (Ideal.span _) = _; rw [Ideal.map_span]
  have hJφ_span : Iφ ⊔ Ideal.span genX = Ideal.span (genI ∪ genX) := by
    rw [hIφ_span]; exact (Submodule.span_union genI genX).symm
  rw [hJφ_span]
  apply isMonomial_span_of_support_singleton
  intro s hs
  rcases hs with hs_left | hs_right
  · -- s ∈ genI: use existing proof from isMonomial_map_diagSubstHom
    obtain ⟨_, ⟨a', b', hb', hadj, hab', rfl⟩, rfl⟩ := hs_left
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
    split_ifs with hcond
    · exact ⟨Finsupp.single (Sum.inl a') 1 + Finsupp.single (Sum.inl b') 1, by
        rw [show X (Sum.inl a') * -X (Sum.inl b') =
          -(X (Sum.inl a') * X (Sum.inl b') : MvPolynomial _ K) from by ring]
        rw [show (X (Sum.inl a') * X (Sum.inl b') : MvPolynomial _ K) =
          MvPolynomial.monomial (Finsupp.single (Sum.inl a') 1 +
            Finsupp.single (Sum.inl b') 1) 1 from by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
        rw [MvPolynomial.support_neg]
        exact MvPolynomial.support_monomial_subset⟩
    · exact ⟨Finsupp.single (Sum.inl a') 1 + Finsupp.single (Sum.inr b') 1, by
        rw [show (X (Sum.inl a') * X (Sum.inr b') : MvPolynomial _ K) =
          MvPolynomial.monomial (Finsupp.single (Sum.inl a') 1 +
            Finsupp.single (Sum.inr b') 1) 1 from by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
        exact MvPolynomial.support_monomial_subset⟩
  · -- s ∈ genX = {X xv}
    rw [Set.mem_singleton_iff] at hs_right
    exact ⟨Finsupp.single xv 1, by rw [hs_right]; exact MvPolynomial.support_X.subset⟩

/-- Every generator of the extended ideal `I.map φ ⊔ ⟨x_{n-1}⟩` has
exponent 0 at `Sum.inr ⟨n-1,_⟩`.

For `I.map φ` generators: these are `±X(inl a)·X(inl b)` (when `b.val < n-1`)
or `X(inl a)·X(inr b)` (when `b.val ≥ n-1`, but `b.val + 1 < n` forces
`b.val ≤ n-2 < n-1`, so only the first case occurs). Either way, exponent at
`Sum.inr ⟨n-1,_⟩` is 0.

For the `⟨x_{n-1}⟩` generator: `X(Sum.inl ⟨n-1,_⟩)` has exponent 0 at
`Sum.inr ⟨n-1,_⟩`. -/
private theorem generator_exponent_zero_at_inr_last {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)}
    {s : MvPolynomial (BinomialEdgeVars (Fin n)) K}
    (hs : s ∈ ((diagSubstHom (K := K) (n - 1)).toRingHom ''
      { m : MvPolynomial (BinomialEdgeVars (Fin n)) K |
        ∃ (a b : Fin n) (_ : b.val + 1 < n),
        G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
        m = X (Sum.inl a) * X (Sum.inr b) }) ∪
      ({X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))} :
        Set (MvPolynomial (BinomialEdgeVars (Fin n)) K)))
    {e : BinomialEdgeVars (Fin n) →₀ ℕ} (hes : s.support ⊆ {e}) :
    e (Sum.inr ⟨n - 1, by omega⟩) = 0 := by
  rcases hs with hs_left | hs_right
  · -- s is a generator of I.map φ
    obtain ⟨_, ⟨a, b, hb, hadj, hab, rfl⟩, rfl⟩ := hs_left
    simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
      MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr] at hes
    -- b.val < n - 1 since b.val + 1 < n
    have hb_cond : b.val < n - 1 ∧ b.val + 1 < n := ⟨by omega, hb⟩
    rw [if_pos hb_cond] at hes
    -- Generator image is X(inl a) * (-X(inl b)) = -(X(inl a) * X(inl b))
    set e' : BinomialEdgeVars (Fin n) →₀ ℕ :=
      Finsupp.single (Sum.inl a) 1 + Finsupp.single (Sum.inl b) 1
    have hsupp : (X (Sum.inl a) * -X (Sum.inl b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K).support ⊆ {e'} := by
      rw [show X (Sum.inl a) * -X (Sum.inl b) =
        -(X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) from by ring]
      rw [show (X (Sum.inl a) * X (Sum.inl b) : MvPolynomial _ K) =
        MvPolynomial.monomial (Finsupp.single (Sum.inl a) 1 +
          Finsupp.single (Sum.inl b) 1) 1 from by
          simp [MvPolynomial.X, MvPolynomial.monomial_mul]]
      rw [MvPolynomial.support_neg]; exact MvPolynomial.support_monomial_subset
    have hs_ne : (X (Sum.inl a) * -X (Sum.inl b) :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ≠ 0 :=
      mul_ne_zero (MvPolynomial.X_ne_zero _) (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
    -- e = e' since both are the unique support element
    have he_eq : e = e' := by
      obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
      exact (Finset.mem_singleton.mp (hes hd_wit)).symm.trans
        (Finset.mem_singleton.mp (hsupp hd_wit))
    rw [he_eq]; simp [e']
  · -- s = X(inl ⟨n-1, _⟩), exponent at inr is 0
    rw [Set.mem_singleton_iff] at hs_right
    have hsupp : s.support ⊆ {Finsupp.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1} := by
      rw [hs_right]; exact MvPolynomial.support_X.subset
    have hs_ne : s ≠ 0 := by rw [hs_right]; exact MvPolynomial.X_ne_zero _
    set e' : BinomialEdgeVars (Fin n) →₀ ℕ :=
      Finsupp.single (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) 1
    have he_eq : e = e' := by
      obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
      exact (Finset.mem_singleton.mp (hes hd_wit)).symm.trans
        (Finset.mem_singleton.mp (hsupp hd_wit))
    rw [he_eq]; simp [e']

/-- `X(inr ⟨n-1,_⟩)` is a NZD on `S ⧸ (I.map φ ⊔ ⟨x_{n-1}⟩)`.

Proof: the ideal is monomial. Generators don't involve `Sum.inr ⟨n-1,_⟩`.
Standard monomial divisibility argument. -/
private theorem X_inr_last_isSMulRegular_map_diagSubstHom_sup {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        (Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
          (bipartiteEdgeMonomialIdeal (K := K) G) ⊔
          Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))}))
      (Ideal.Quotient.mk
        (Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom
          (bipartiteEdgeMonomialIdeal (K := K) G) ⊔
          Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))})
        (X (Sum.inr (⟨n - 1, by omega⟩ : Fin n)))) := by
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set Iφ := Ideal.map (diagSubstHom (K := K) (n - 1)).toRingHom I
  set xv : BinomialEdgeVars (Fin n) := Sum.inl ⟨n - 1, by omega⟩
  set yv : BinomialEdgeVars (Fin n) := Sum.inr ⟨n - 1, by omega⟩
  set Jφ := Iφ ⊔ Ideal.span {(X xv : MvPolynomial (BinomialEdgeVars (Fin n)) K)}
  have hIsM : Jφ.IsMonomial := isMonomial_map_diagSubstHom_sup_span (K := K) hn G
  -- Set up generating sets
  set genI : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
    (diagSubstHom (K := K) (n - 1)).toRingHom ''
      { m | ∃ (a b : Fin n) (_ : b.val + 1 < n),
        G.Adj a ⟨b.val + 1, by omega⟩ ∧ a ≤ b ∧
        m = X (Sum.inl a) * X (Sum.inr b) }
  set genX : Set (MvPolynomial (BinomialEdgeVars (Fin n)) K) := {X xv}
  set genAll := genI ∪ genX
  have hIφ_genI : Iφ = Ideal.span genI := by
    change Ideal.map _ (Ideal.span _) = _; rw [Ideal.map_span]
  have hJφ_span : Jφ = Ideal.span genAll := by
    change Iφ ⊔ Ideal.span genX = _
    rw [hIφ_genI]; exact (Submodule.span_union genI genX).symm
  have hgenS : ∀ s ∈ genAll, ∃ e, s.support ⊆ {e} := by
    intro s hs
    rcases hs with hs_left | hs_right
    · obtain ⟨_, ⟨a', b', hb', hadj, hab', rfl⟩, rfl⟩ := hs_left
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr]
      split_ifs with hcond
      · exact ⟨Finsupp.single (Sum.inl a') 1 + Finsupp.single (Sum.inl b') 1, by
          rw [show X (Sum.inl a') * -X (Sum.inl b') =
            -(X (Sum.inl a') * X (Sum.inl b') : MvPolynomial _ K) from by ring]
          rw [show (X (Sum.inl a') * X (Sum.inl b') : MvPolynomial _ K) =
            MvPolynomial.monomial (Finsupp.single (Sum.inl a') 1 +
              Finsupp.single (Sum.inl b') 1) 1 from by
              simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
          rw [MvPolynomial.support_neg]
          exact MvPolynomial.support_monomial_subset⟩
      · exact ⟨Finsupp.single (Sum.inl a') 1 + Finsupp.single (Sum.inr b') 1, by
          rw [show (X (Sum.inl a') * X (Sum.inr b') : MvPolynomial _ K) =
            MvPolynomial.monomial (Finsupp.single (Sum.inl a') 1 +
              Finsupp.single (Sum.inr b') 1) 1 from by
              simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]]
          exact MvPolynomial.support_monomial_subset⟩
    · rw [Set.mem_singleton_iff] at hs_right
      exact ⟨Finsupp.single xv 1, by rw [hs_right]; exact MvPolynomial.support_X.subset⟩
  -- Lift to polynomial ring and prove by contradiction
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul, Ideal.Quotient.eq] at hab ⊢
  set c := a' - b'
  have hvc : X yv * c ∈ Jφ := by rw [mul_sub]; exact hab
  -- Prove c ∈ Jφ by contradiction
  by_contra hc_not
  obtain ⟨d₀, hd₀_supp, hd₀_not⟩ := Ideal.not_mem_exists_monomial_notMem hc_not
  have hcoeff_ne : MvPolynomial.coeff d₀ c ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hd₀_supp
  -- d' = d₀ + e_yv is in support of X_yv * c
  set d' : BinomialEdgeVars (Fin n) →₀ ℕ :=
    d₀ + (Finsupp.single yv 1 : BinomialEdgeVars (Fin n) →₀ ℕ)
  have hd'_supp : d' ∈ (X yv * c).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul']
    have : yv ∈ d'.support := by
      rw [Finsupp.mem_support_iff]; simp [d']
    rw [if_pos this]; convert hcoeff_ne using 1; congr 1; ext w
    simp only [d', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply,
      Pi.add_apply, Finsupp.single_apply]; split <;> omega
  -- monomial d' 1 ∈ Jφ by IsMonomial
  have hd'_Jφ : MvPolynomial.monomial d' (1 : K) ∈ Jφ := hIsM _ hvc d' hd'_supp
  -- Use support_divisible_by_generator to find generator exponent e ≤ d'
  have hd'_supp_d' : d' ∈ (MvPolynomial.monomial d' (1 : K)).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]
    exact one_ne_zero
  obtain ⟨s, hs_mem, e, hes, hle_d'⟩ :=
    support_divisible_by_generator (K := K) hgenS (hJφ_span ▸ hd'_Jφ) d' hd'_supp_d'
  -- e(yv) = 0 since generators don't involve yv
  have he_zero := generator_exponent_zero_at_inr_last (K := K) hn hs_mem hes
  -- e ≤ d₀: for w = yv, e(yv) = 0 ≤ d₀(yv); for w ≠ yv, e(w) ≤ d'(w) = d₀(w)
  have hle_d₀ : e ≤ d₀ := by
    intro w
    by_cases hw : w = yv
    · subst hw; rw [he_zero]; exact Nat.zero_le _
    · have := hle_d' w
      simp only [d', Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
        show yv = w ↔ w = yv from ⟨fun h => h.symm, fun h => h.symm⟩,
        hw, if_false, add_zero] at this
      exact this
  -- monomial e 1 ∈ Jφ
  have hs_Jφ : s ∈ Jφ := hJφ_span ▸ Ideal.subset_span hs_mem
  have hs_ne : s ≠ 0 := by
    rcases hs_mem with hs_left | hs_right
    · obtain ⟨_, ⟨a', b', _, _, _, rfl⟩, rfl⟩ := hs_left
      simp only [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, diagSubstHom,
        MvPolynomial.aeval_X, diagSubstFun, Sum.elim_inl, Sum.elim_inr, ne_eq]
      split_ifs
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _)
          (neg_ne_zero.mpr (MvPolynomial.X_ne_zero _))
      · exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)
    · rw [Set.mem_singleton_iff] at hs_right; rw [hs_right]; exact MvPolynomial.X_ne_zero _
  have he_supp : e ∈ s.support := by
    obtain ⟨d_wit, hd_wit⟩ := MvPolynomial.support_nonempty.mpr hs_ne
    have := Finset.mem_singleton.mp (hes hd_wit)
    rwa [← this]
  have he_Jφ : MvPolynomial.monomial e (1 : K) ∈ Jφ := hIsM s hs_Jφ e he_supp
  -- monomial d₀ 1 = monomial(d₀ - e) 1 * monomial e 1 ∈ Jφ
  have hd₀_Jφ : MvPolynomial.monomial d₀ (1 : K) ∈ Jφ := by
    have : MvPolynomial.monomial d₀ (1 : K) =
        MvPolynomial.monomial (d₀ - e) 1 * MvPolynomial.monomial e 1 := by
      rw [MvPolynomial.monomial_mul, one_mul, tsub_add_cancel_of_le hle_d₀]
    rw [this]; exact Jφ.mul_mem_left _ he_Jφ
  exact hd₀_not hd₀_Jφ

/-- Under HH conditions, `X(Sum.inr ⟨n-1,_⟩)` is a NZD on
`S ⧸ (bipartiteEdgeMonomialIdeal G ⊔ diagonalSumIdeal n (n-1) ⊔ ⟨X(inl ⟨n-1,_⟩)⟩)`.

Proof via the diagonal substitution `φ = diagSubstHom (n-1)`:
1. Apply `φ` (kills diag, fixes `x_{n-1}`) to reduce to NZD on `S ⧸ (I.map φ ⊔ ⟨x_{n-1}⟩)`.
2. `φ` fixes `X(inr ⟨n-1,_⟩)` since `diagSubstFun` returns `X(inr j)` when `j.val < n-1` is false.
3. NZD follows from monomial ideal structure (no generator involves `Sum.inr ⟨n-1,_⟩`).
4. Transfer back using `c - φ(c) ∈ diag ⊆ J`. -/
theorem X_inr_last_isSMulRegular_mod_diagonalSum_sup {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        (bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n (n - 1) ⊔
          Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))}))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G ⊔
        diagonalSumIdeal (K := K) n (n - 1) ⊔
          Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))})
        (X (Sum.inr (⟨n - 1, by omega⟩ : Fin n)))) := by
  set J := bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n (n - 1) ⊔
    Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))}
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set diag := diagonalSumIdeal (K := K) n (n - 1)
  set xv : MvPolynomial (BinomialEdgeVars (Fin n)) K :=
    X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))
  set yv : MvPolynomial (BinomialEdgeVars (Fin n)) K :=
    X (Sum.inr (⟨n - 1, by omega⟩ : Fin n))
  set φ := diagSubstHom (K := K) (n - 1)
  set Iφ := Ideal.map φ.toRingHom I
  set Jφ := Iφ ⊔ Ideal.span {xv}
  -- Lift to the polynomial ring
  intro a b hab
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  simp only [smul_eq_mul, ← map_mul, Ideal.Quotient.eq] at hab ⊢
  set c := a' - b'
  have hyvc : yv * c ∈ J := by rw [mul_sub]; exact hab
  -- Step 1: Apply φ to get yv * φ(c) ∈ Jφ
  have h_map_mem : φ.toRingHom (yv * c) ∈ Jφ := by
    have h1 := Ideal.mem_map_of_mem φ.toRingHom hyvc
    exact map_sup_diag_sup_span_inl_le (K := K) hn h1
  rw [map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    diagSubstHom_fix_X_inr_last (K := K) hn] at h_map_mem
  -- h_map_mem : yv * φ(c) ∈ Jφ
  -- Step 2: NZD on S / Jφ gives φ(c) ∈ Jφ
  have h_nzd := X_inr_last_isSMulRegular_map_diagSubstHom_sup (K := K) hn (G := G)
  have hφc_mem : φ c ∈ Jφ := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 : Ideal.Quotient.mk Jφ yv * Ideal.Quotient.mk Jφ (φ c) = 0 := by
      rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h_map_mem
    exact h_nzd (show _ • _ = _ • _ from by
      simp only [smul_eq_mul, mul_zero]; exact h1)
  -- Step 3: c = (c - φ(c)) + φ(c) ∈ diag + Jφ ⊆ J
  have h_diff : c - φ c ∈ diag :=
    diagSubstHom_congr_mod_diag (K := K) (n - 1) c
  have h_Jφ_le : Jφ ≤ J := map_diagSubstHom_sup_span_le (K := K) hn
  change c ∈ J
  have : c = (c - φ c) + φ c := by ring
  rw [this]
  exact J.add_mem (Ideal.mem_sup_left (Ideal.mem_sup_right h_diff)) (h_Jφ_le hφc_mem)

end XInrLastNZD

/-! ### Full regular sequence of length n + 1

The diagonal sums `x₀+y₀, …, x_{n-2}+y_{n-2}` form a weakly regular
sequence of length `n - 1` (proved above as `bipartiteEdgeMonomialIdeal_isWeaklyRegular`).
The two free variables `x_{n-1}` and `y_{n-1}` extend this to a weakly
regular sequence of length `n + 1 = dim(S/I)`.
-/

section FullRegularSequence

variable {K : Type*} [Field K]
open MvPolynomial RingTheory.Sequence

/-- The full regular sequence: `n - 1` diagonal sums followed by
the two free variables `x_{n-1}` and `y_{n-1}`. -/
private noncomputable def fullRegSeq (n : ℕ) (hn : 2 ≤ n) :
    List (MvPolynomial (BinomialEdgeVars (Fin n)) K) :=
  diagElems (K := K) n ++
    ([X (Sum.inl ⟨n - 1, by omega⟩), X (Sum.inr ⟨n - 1, by omega⟩)] :
      List (MvPolynomial (BinomialEdgeVars (Fin n)) K))

private theorem fullRegSeq_length {n : ℕ} (hn : 2 ≤ n) :
    (fullRegSeq (K := K) n hn).length = n + 1 := by
  simp [fullRegSeq, diagElems_length]; omega

/-- `Ideal.ofList (diagElems n) = diagonalSumIdeal n (n - 1)`. -/
private lemma ofList_diagElems_eq {n : ℕ} :
    Ideal.ofList (diagElems (K := K) n) = diagonalSumIdeal (K := K) n (n - 1) := by
  have h : (diagElems (K := K) n).length ≤ n - 1 := by simp [diagElems_length]
  conv_lhs => rw [← List.take_of_length_le h]
  exact diagElems_ofList_take_eq (n - 1) le_rfl

/-- For `idx ≤ n - 1`, `Ideal.ofList (take idx fullRegSeq)` equals
`diagonalSumIdeal n idx`. -/
private lemma ofList_take_fullRegSeq_le {n : ℕ} (hn : 2 ≤ n)
    (idx : ℕ) (hidx : idx ≤ n - 1) :
    Ideal.ofList ((fullRegSeq (K := K) n hn).take idx) =
      diagonalSumIdeal (K := K) n idx := by
  simp only [fullRegSeq, List.take_append, diagElems_length,
    show idx - (n - 1) = 0 from by omega, List.take_zero, List.append_nil]
  exact diagElems_ofList_take_eq idx hidx

/-- `Ideal.ofList (take n fullRegSeq) = diag_{n-1} ⊔ ⟨x_{n-1}⟩`. -/
private lemma ofList_take_n_fullRegSeq {n : ℕ} (hn : 2 ≤ n) :
    Ideal.ofList ((fullRegSeq (K := K) n hn).take n) =
      diagonalSumIdeal (K := K) n (n - 1) ⊔
        Ideal.span {(X (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) :
          MvPolynomial (BinomialEdgeVars (Fin n)) K)} := by
  simp only [fullRegSeq, List.take_append, diagElems_length,
    show n - (n - 1) = 1 from by omega]
  rw [List.take_of_length_le (show (diagElems (K := K) n).length ≤ n by
    simp [diagElems_length])]
  simp only [show List.take 1 ([X (Sum.inl ⟨n - 1, by omega⟩),
      X (Sum.inr ⟨n - 1, by omega⟩)] : List (MvPolynomial (BinomialEdgeVars (Fin n)) K)) =
    [X (Sum.inl ⟨n - 1, by omega⟩)] from rfl]
  rw [Ideal.ofList_append, Ideal.ofList_singleton, ofList_diagElems_eq]

/-- Under HH conditions with `n ≥ 2`, the full regular sequence forms
a weakly regular sequence of length `n + 1` on `S ⧸ bipartiteEdgeMonomialIdeal G`. -/
theorem bipartiteEdgeMonomialIdeal_isWeaklyRegular_full {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsWeaklyRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G)
      ((fullRegSeq (K := K) n hn).map
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))) := by
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set mkI := Ideal.Quotient.mk I
  set rs := fullRegSeq (K := K) n hn
  have hrslen : rs.length = n + 1 := fullRegSeq_length hn
  refine IsWeaklyRegular.mk fun idx hidx => ?_
  simp only [List.length_map] at hidx
  rw [hrslen] at hidx
  by_cases h_diag : idx < n - 1
  · -- Case 1: Diagonal elements (idx < n - 1)
    rw [self_module_step_eq rs idx]
    simp only [List.getElem_map]
    rw [ofList_take_fullRegSeq_le hn idx (by omega)]
    have hlt : idx < (diagElems (K := K) n).length := by simp [diagElems_length]; omega
    rw [show rs[idx] = (diagElems (K := K) n)[idx]'hlt from
      List.getElem_append_left hlt]
    simp only [diagElems, List.getElem_ofFn]
    apply isSMulRegular_of_doubleQuot (I := I) (J := diagonalSumIdeal (K := K) n idx)
    simp only [diagElem, Fin.castLE]
    exact sum_XY_isSMulRegular_mod_diagonalSum hHH ⟨idx, by omega⟩ (by simp; omega) le_rfl
  · by_cases h_x : idx = n - 1
    · -- Case 2: x_{n-1} (idx = n - 1)
      subst h_x
      rw [self_module_step_eq rs (n - 1)]
      simp only [List.getElem_map]
      rw [ofList_take_fullRegSeq_le hn (n - 1) le_rfl]
      have hge : (diagElems (K := K) n).length ≤ n - 1 := by simp [diagElems_length]
      rw [show rs[n - 1] = (X (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) :
          MvPolynomial (BinomialEdgeVars (Fin n)) K) from by
        simp [rs, fullRegSeq, List.getElem_append_right hge, diagElems_length]]
      apply isSMulRegular_of_doubleQuot (I := I)
        (J := diagonalSumIdeal (K := K) n (n - 1))
      exact X_inl_last_isSMulRegular_mod_diagonalSum hn G
    · -- Case 3: y_{n-1} (idx = n)
      have h_y : idx = n := by omega
      -- simp handles the dependent-type list indexing
      simp only [h_y]
      -- rw can handle List.take (no proof dependency in its type)
      rw [show List.take idx (List.map (↑mkI) rs) =
          List.take n (List.map (↑mkI) rs) from by rw [h_y]]
      rw [self_module_step_eq rs n]
      simp only [List.getElem_map]
      rw [ofList_take_n_fullRegSeq hn]
      have hge : (diagElems (K := K) n).length ≤ n := by simp [diagElems_length]
      rw [show rs[n]'(by simp [hrslen]) = (X (Sum.inr (⟨n - 1, by omega⟩ : Fin n)) :
          MvPolynomial (BinomialEdgeVars (Fin n)) K) from by
        simp only [rs, fullRegSeq, List.getElem_append_right hge, diagElems_length]
        norm_num [show n - (n - 1) = 1 from by omega]]
      apply isSMulRegular_of_doubleQuot (I := I)
        (J := diagonalSumIdeal (K := K) n (n - 1) ⊔
          Ideal.span {(X (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) :
            MvPolynomial (BinomialEdgeVars (Fin n)) K)})
      rw [show I ⊔ (diagonalSumIdeal (K := K) n (n - 1) ⊔
            Ideal.span {(X (Sum.inl (⟨n - 1, by omega⟩ : Fin n)) :
              MvPolynomial (BinomialEdgeVars (Fin n)) K)}) =
          I ⊔ diagonalSumIdeal (K := K) n (n - 1) ⊔
            Ideal.span {X (Sum.inl (⟨n - 1, by omega⟩ : Fin n))}
        from (sup_assoc ..).symm]
      exact X_inr_last_isSMulRegular_mod_diagonalSum_sup hn G

end FullRegularSequence

/-! ### Augmentation ideal and local CM -/

section AugmentationCM

variable {K : Type*} [Field K]
open MvPolynomial RingTheory.Sequence

/-- All generators of the bipartite edge monomial ideal have zero constant term. -/
private lemma bipartiteEdgeMonomialIdeal_le_ker_constantCoeff {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    bipartiteEdgeMonomialIdeal (K := K) G ≤
      RingHom.ker (MvPolynomial.constantCoeff (R := K)
        (σ := BinomialEdgeVars (Fin n))) := by
  apply Ideal.span_le.mpr
  intro f hf
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  obtain ⟨a, b, _, _, _, rfl⟩ := hf
  simp [constantCoeff_X]

/-- The factored constant coefficient map `S/I → K`. -/
private noncomputable def quotConstCoeff {n : ℕ} (G : SimpleGraph (Fin n)) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G →+* K :=
  Ideal.Quotient.lift _ MvPolynomial.constantCoeff
    (bipartiteEdgeMonomialIdeal_le_ker_constantCoeff G)

/-- The factored constant coefficient map is surjective (via `C`). -/
private lemma quotConstCoeff_surjective {n : ℕ} (G : SimpleGraph (Fin n)) :
    Function.Surjective (quotConstCoeff (K := K) G) := by
  intro k
  exact ⟨Ideal.Quotient.mk _ (C k), by simp [quotConstCoeff, constantCoeff_C]⟩

/-- The augmentation ideal of `S/I`: kernel of the evaluation-at-zero map. -/
private noncomputable def augIdeal {n : ℕ} (G : SimpleGraph (Fin n)) :
    Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
  RingHom.ker (quotConstCoeff (K := K) G)

/-- The augmentation ideal is maximal. -/
private lemma augIdeal_isMaximal {n : ℕ} (G : SimpleGraph (Fin n)) :
    (augIdeal (K := K) G).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (quotConstCoeff_surjective G)

/-- Variable images are in the augmentation ideal. -/
private lemma mkI_X_mem_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    (v : BinomialEdgeVars (Fin n)) :
    Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∈
      augIdeal (K := K) G := by
  rw [augIdeal, RingHom.mem_ker, quotConstCoeff]
  simp [constantCoeff_X]

/-- Sums of variable images are in the augmentation ideal. -/
private lemma mkI_X_add_X_mem_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    (v w : BinomialEdgeVars (Fin n)) :
    Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v + X w) ∈
      augIdeal (K := K) G := by
  rw [map_add]
  exact (augIdeal G).add_mem (mkI_X_mem_augIdeal G v) (mkI_X_mem_augIdeal G w)

/-- All elements of the full regular sequence are in the augmentation ideal. -/
private lemma fullRegSeq_mem_augIdeal {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    ∀ r ∈ (fullRegSeq (K := K) n hn).map
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)),
      r ∈ augIdeal (K := K) G := by
  intro r hr
  simp only [List.mem_map] at hr
  obtain ⟨f, hf, rfl⟩ := hr
  simp only [fullRegSeq, List.mem_append, List.mem_cons] at hf
  rcases hf with hf | hf | hf
  · -- f is a diagonal element
    simp only [diagElems, List.mem_ofFn] at hf
    obtain ⟨j, rfl⟩ := hf
    exact mkI_X_add_X_mem_augIdeal G _ _
  · -- f = X(inl ⟨n-1, _⟩)
    subst hf; exact mkI_X_mem_augIdeal G _
  · -- f = X(inr ⟨n-1, _⟩)
    simp only [List.mem_nil_iff, or_false] at hf
    subst hf; exact mkI_X_mem_augIdeal G _

private instance augIdeal_isPrime {n : ℕ} (G : SimpleGraph (Fin n)) :
    (augIdeal (K := K) G).IsPrime := (augIdeal_isMaximal G).isPrime

/-- **Cohen–Macaulay at the augmentation ideal**: Under HH conditions with `n ≥ 2`,
the localization of `S ⧸ bipartiteEdgeMonomialIdeal G` at the augmentation ideal
is a Cohen–Macaulay local ring. -/
theorem isCohenMacaulayLocalRing_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K) G)) := by
  set p := augIdeal (K := K) G with p_def
  set Rₚ := Localization.AtPrime p with Rₚ_def
  -- Step 1: Get the weakly regular sequence and its membership
  set rs := (fullRegSeq (K := K) n hn).map
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
  have hreg_R := bipartiteEdgeMonomialIdeal_isWeaklyRegular_full (K := K) hn hHH
  have hmem_p := fullRegSeq_mem_augIdeal (K := K) hn G
  -- Step 2: Transfer to regular → weakly regular at localization
  have hwreg : IsWeaklyRegular Rₚ (rs.map (algebraMap _ Rₚ)) :=
    (IsWeaklyRegular.isRegular_of_isLocalization_of_mem Rₚ p hreg_R hmem_p).toIsWeaklyRegular
  -- Step 3: All mapped elements are in the maximal ideal of Rₚ
  have hmem : ∀ r ∈ rs.map (algebraMap _ Rₚ), r ∈ IsLocalRing.maximalIdeal Rₚ := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hmem_p s hs)
  -- Step 4: Length = n + 1
  have hlen : (rs.map (algebraMap _ Rₚ)).length = n + 1 := by
    simp only [List.length_map, rs, fullRegSeq_length hn]
  -- Step 5: Dimension of Rₚ = n + 1
  have hdim : ringKrullDim Rₚ = ↑(n + 1 : ℕ) := by
    apply le_antisymm
    · -- dim(Rₚ) = height(p) ≤ dim(R) = n + 1
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height p Rₚ,
        Ideal.height_eq_primeHeight]
      exact Ideal.primeHeight_le_ringKrullDim.trans
        (ringKrullDim_bipartiteEdgeMonomialIdeal (by omega) hHH).le
    · -- n + 1 ≤ dim(Rₚ): from the weakly regular sequence
      calc ↑(↑(n + 1 : ℕ) : ℕ∞) = ↑(rs.map (algebraMap _ Rₚ)).length := by
              rw [hlen]; rfl
        _ ≤ ringKrullDim Rₚ :=
              weaklyRegular_length_le_ringKrullDim Rₚ hwreg hmem
  -- Step 6: Apply CM criterion
  exact isCohenMacaulayLocalRing_of_weaklyRegular_length_eq_dim hwreg hmem
    (show ringKrullDim Rₚ = ↑(rs.map (algebraMap _ Rₚ)).length by
      rw [hdim, hlen])

/-! #### Last-pair permutation: [X(inl last), X(inr last), diagElems…] weakly regular -/

open List in
/-- The fullRegSeq permuted to have the last pair first is still weakly regular on
`(A_H)_aug`. This is a direct application of
`IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal`. -/
private lemma lastPair_prefix_isWeaklyRegular_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    let mk := Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
    let Rp := Localization.AtPrime (augIdeal (K := K) G)
    let last : Fin n := ⟨n - 1, by omega⟩
    let rs_perm : List Rp :=
      [algebraMap _ Rp (mk (X (Sum.inl last))),
       algebraMap _ Rp (mk (X (Sum.inr last)))] ++
      ((diagElems n).map mk).map (algebraMap _ Rp)
    RingTheory.Sequence.IsWeaklyRegular Rp rs_perm := by
  intro mk Rp last rs_perm
  set p := augIdeal (K := K) G
  -- Start from the regular sequence on Rp
  set rs : List Rp := ((fullRegSeq (K := K) n hn).map mk).map (algebraMap _ Rp)
  have hreg_R := bipartiteEdgeMonomialIdeal_isWeaklyRegular_full (K := K) hn hHH
  have hmem_p := fullRegSeq_mem_augIdeal (K := K) hn G
  have hwreg : RingTheory.Sequence.IsWeaklyRegular Rp rs :=
    (IsWeaklyRegular.isRegular_of_isLocalization_of_mem Rp p hreg_R hmem_p).toIsWeaklyRegular
  have hmem : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal Rp := by
    intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hmem_p s hs)
  -- rs.Perm rs_perm: the two differ by moving last two elements to the front
  have hperm : rs.Perm rs_perm := by
    -- fullRegSeq = diagElems ++ [X(inl last)] ++ [X(inr last)]
    -- rs = mapped(diagElems ++ [X(inl last), X(inr last)])
    -- rs_perm = [X(inl last), X(inr last)] ++ mapped diagElems
    simp only [rs, rs_perm, fullRegSeq, List.map_append, List.map_cons, List.map_nil]
    -- Goal: ((diagElems n).map mk).map alg ++ [alg (mk X(inl)), alg (mk X(inr))] ~
    --       [alg (mk X(inl)), alg (mk X(inr))] ++ ((diagElems n).map mk).map alg
    exact List.perm_append_comm
  -- Apply permutation lemma
  exact IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hwreg hperm hmem

/-- Extract the first IsSMulRegular from the permuted regular sequence: `X(inl last)`
is `IsSMulRegular` in `(A_H)_aug`. -/
private lemma isSMulRegular_X_inl_last_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsSMulRegular (Localization.AtPrime (augIdeal (K := K) G))
      (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))) := by
  have hwreg := lastPair_prefix_isWeaklyRegular_at_augIdeal (K := K) hn hHH
  simp only [List.cons_append, List.nil_append] at hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hwreg
  exact hwreg.1

/-- `X(inl last)` lies in the maximal ideal of `(A_H)_aug`. -/
private lemma X_inl_last_mem_maximalIdeal {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) :
    (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (augIdeal (K := K) G)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (mkI_X_mem_augIdeal G _)

/-- **Reduced HH CM, half 1**: quotient of `(A_H)_aug` by `X(inl last)` is CM local. -/
private theorem isCohenMacaulayLocalRing_quot_lastInl {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    haveI : IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K) G)) :=
      isCohenMacaulayLocalRing_at_augIdeal hn hHH
    haveI := quotSMulTopLocalRing (X_inl_last_mem_maximalIdeal (K := K) (by omega) G)
    IsCohenMacaulayLocalRing (QuotSMulTop
      (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨n - 1, by omega⟩))))
      (Localization.AtPrime (augIdeal (K := K) G))) := by
  haveI : IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K) G)) :=
    isCohenMacaulayLocalRing_at_augIdeal hn hHH
  exact isCohenMacaulayLocalRing_quotient
    (isSMulRegular_X_inl_last_at_augIdeal hn hHH)
    (X_inl_last_mem_maximalIdeal (by omega) G)

/-- `X(inr last)` is `IsSMulRegular` on `QuotSMulTop x_last Rp` (as Rp-module). -/
private lemma isSMulRegular_X_inr_last_quot_lastInl {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    IsSMulRegular
      (QuotSMulTop
        (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨n - 1, by omega⟩))))
        (Localization.AtPrime (augIdeal (K := K) G)))
      (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨n - 1, by omega⟩)))) := by
  have hwreg := lastPair_prefix_isWeaklyRegular_at_augIdeal (K := K) hn hHH
  simp only [List.cons_append, List.nil_append] at hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hwreg
  obtain ⟨_, hwreg2⟩ := hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hwreg2
  exact hwreg2.1

/-- `X(inr last)` lies in the maximal ideal of `(A_H)_aug`. -/
private lemma X_inr_last_mem_maximalIdeal {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph (Fin n)) :
    (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨n - 1, by omega⟩)))) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (augIdeal (K := K) G)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.mem_map_of_mem _ (mkI_X_mem_augIdeal G _)

set_option synthInstance.maxHeartbeats 400000 in
-- synth budget needed: nested quotient + localization instance search is heavy.
/-- `mk y_last` (image of `X(inr last)` in the first quotient) is `IsSMulRegular`
on `QuotSMulTop x_last Rp`, extracted via the *primed* cons_iff lemma which
produces the correct scalar type. -/
private lemma isSMulRegular_mk_y_last {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    let Rp := Localization.AtPrime (augIdeal (K := K) G)
    let x_last : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))
    let y_last : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨n - 1, by omega⟩)))
    IsSMulRegular (QuotSMulTop x_last Rp)
      (Ideal.Quotient.mk (Ideal.span {x_last}) y_last) := by
  intro Rp x_last y_last
  have hwreg := lastPair_prefix_isWeaklyRegular_at_augIdeal (K := K) hn hHH
  simp only [List.cons_append, List.nil_append] at hwreg
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff'] at hwreg
  obtain ⟨_, hwreg2⟩ := hwreg
  simp only [List.map_cons] at hwreg2
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff'] at hwreg2
  exact hwreg2.1

open scoped Pointwise in
/-- Bridging lemma: `(x • ⊤ : Submodule R R) = Ideal.span {x}` as ideals. This lets
us identify `QuotSMulTop x R` with `R ⧸ Ideal.span {x}`. -/
private lemma smul_top_eq_span_singleton {R : Type*} [CommRing R] (x : R) :
    ((x • (⊤ : Submodule R R)) : Ideal R) = Ideal.span {x} := by
  apply le_antisymm
  · rintro y ⟨z, _, rfl⟩
    change (DistribSMul.toLinearMap R R x) z ∈ Ideal.span {x}
    exact Ideal.mem_span_singleton'.mpr ⟨z, by simp [mul_comm]⟩
  · intro y hy
    rcases Ideal.mem_span_singleton'.mp hy with ⟨z, rfl⟩
    refine ⟨z, Submodule.mem_top, ?_⟩
    change (DistribSMul.toLinearMap R R x) z = z * x
    simp [mul_comm]

open scoped Pointwise in
/-- Ring equivalence between the two quotient views: `QuotSMulTop x R ≃+* R ⧸ Ideal.span {x}`.
Since `Ideal R = Submodule R R` definitionally, this is just `Ideal.quotEquivOfEq` applied
to `smul_top_eq_span_singleton`. -/
private noncomputable def quotSMulTopRingEquivIdealQuotient
    {R : Type*} [CommRing R] (x : R) :
    QuotSMulTop x R ≃+* R ⧸ Ideal.span {x} :=
  Ideal.quotEquivOfEq (smul_top_eq_span_singleton x)

/-- `Ideal.span {x_last}` is proper (x_last is not a unit since it's in maximalIdeal). -/
private lemma span_x_inl_last_ne_top {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n)) :
    Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))} ≠ (⊤ : Ideal _) := by
  intro htop
  have hunit : IsUnit (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))) :=
    Ideal.span_singleton_eq_top.mp htop
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (X_inl_last_mem_maximalIdeal (K := K) hn G) hunit

end AugmentationCM

/-! ### HH bipartite edge ideal: global Cohen–Macaulay theorem -/

section GlobalCM

open IsLocalRing

variable {K' : Type*} [Field K']

/-- CM of `Rp ⧸ Ideal.span {x_last}` (ideal-quotient form), transferred from CM of
`QuotSMulTop x_last Rp` via the bridging ring equiv. This unsticks the `Ideal` vs
`Submodule` quotient type mismatch for the second quotient iteration. -/
private theorem isCohenMacaulayLocalRing_idealQuot_lastInl {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    haveI : Nontrivial (Localization.AtPrime (augIdeal (K := K') G) ⧸
        Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
            (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
      Ideal.Quotient.nontrivial_iff.mpr (span_x_inl_last_ne_top (K := K') (by omega) G)
    haveI : IsLocalRing (Localization.AtPrime (augIdeal (K := K') G) ⧸
        Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
            (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
      IsLocalRing.of_surjective'
        (Ideal.Quotient.mk (Ideal.span {algebraMap _
          (Localization.AtPrime (augIdeal (K := K') G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
            (X (Sum.inl ⟨n - 1, by omega⟩)))}))
        Ideal.Quotient.mk_surjective
    IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K') G) ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}) := by
  haveI := quotSMulTopLocalRing (X_inl_last_mem_maximalIdeal (K := K') (by omega) G)
  haveI : Nontrivial (Localization.AtPrime (augIdeal (K := K') G) ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_x_inl_last_ne_top (K := K') (by omega) G)
  haveI : IsLocalRing (Localization.AtPrime (augIdeal (K := K') G) ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {algebraMap _
        (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}))
      Ideal.Quotient.mk_surjective
  have hCM := isCohenMacaulayLocalRing_quot_lastInl (K := K') hn hHH
  exact isCohenMacaulayLocalRing_of_ringEquiv' hCM
    (quotSMulTopRingEquivIdealQuotient _)

set_option synthInstance.maxHeartbeats 400000 in
-- synth budget needed: iterated quotient-by-regular-element + CM instance search.
/-- **L5 CM corollary**: the reduced HH ring at its augmentation is Cohen–Macaulay.
Specifically, `(Rp ⧸ x_last) ⧸ (mk y_last)` is CM local. This is the reduced HH ring
(HH ring with the trailing isolated pair dropped) localized at its own augmentation. -/
private theorem isCohenMacaulayLocalRing_reducedHH_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    let Rp := Localization.AtPrime (augIdeal (K := K') G)
    let xL : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))
    let yL : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
        (X (Sum.inr ⟨n - 1, by omega⟩)))
    let RpQ := Rp ⧸ Ideal.span {xL}
    let mkyL : RpQ := Ideal.Quotient.mk (Ideal.span {xL}) yL
    haveI : Nontrivial RpQ := Ideal.Quotient.nontrivial_iff.mpr
      (span_x_inl_last_ne_top (K := K') (by omega) G)
    haveI : IsLocalRing RpQ :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI hmem_max : mkyL ∈ IsLocalRing.maximalIdeal RpQ := by
      have hlocal : IsLocalHom (Ideal.Quotient.mk (Ideal.span {xL})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      rw [IsLocalRing.mem_maximalIdeal]
      intro hunit
      have hmem := X_inr_last_mem_maximalIdeal (K := K') (by omega) G
      rw [IsLocalRing.mem_maximalIdeal] at hmem
      exact hmem (hlocal.map_nonunit _ hunit)
    haveI := quotSMulTopLocalRing hmem_max
    IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ) := by
  intros Rp xL yL RpQ mkyL
  haveI : Nontrivial RpQ := Ideal.Quotient.nontrivial_iff.mpr
    (span_x_inl_last_ne_top (K := K') (by omega) G)
  haveI : IsLocalRing RpQ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsCohenMacaulayLocalRing RpQ := isCohenMacaulayLocalRing_idealQuot_lastInl hn hHH
  have hmem_max : mkyL ∈ IsLocalRing.maximalIdeal RpQ := by
    have hlocal : IsLocalHom (Ideal.Quotient.mk (Ideal.span {xL})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    have hmem := X_inr_last_mem_maximalIdeal (K := K') (by omega) G
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    exact hmem (hlocal.map_nonunit _ hunit)
  -- IsSMulRegular of mkyL on RpQ as self-scalar
  have hreg : IsSMulRegular RpQ mkyL := by
    -- Step 1: transfer IsSMulRegular of yL (Rp-scalar) from QuotSMulTop to RpQ
    have hreg_Rp : IsSMulRegular RpQ yL := by
      have h := isSMulRegular_X_inr_last_quot_lastInl (K := K') hn hHH
      exact (LinearEquiv.isSMulRegular_congr
        (Submodule.quotEquivOfEq _ _ (smul_top_eq_span_singleton _)) _).mp h
    -- Step 2: convert Rp-scalar to self-scalar
    exact (isSMulRegular_map (a := yL)
      (fun r : Rp => (Ideal.Quotient.mk (Ideal.span {xL}) r))
      (fun _ => rfl)).mpr hreg_Rp
  exact isCohenMacaulayLocalRing_quotient hreg hmem_max



variable {K : Type*} [Field K]

/-! #### Structural lemmas for the graded local-to-global step -/

/-- In the quotient by the bipartite edge monomial ideal, if all variable images lie in
a prime `p`, then the augmentation ideal is contained in `p`.

The proof uses `MvPolynomial.mem_ideal_span_X_image`: a polynomial with zero constant
coefficient lies in the ideal generated by variables. -/
private lemma augIdeal_le_of_forall_mkI_X_mem {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    (hvar : ∀ v : BinomialEdgeVars (Fin n),
      Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∈ p) :
    augIdeal (K := K) G ≤ p := by
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [augIdeal, RingHom.mem_ker, quotConstCoeff, Ideal.Quotient.lift_mk] at ha
  -- f has zero constant coefficient → f ∈ Ideal.span (range X)
  have hmem : f ∈ Ideal.span (Set.range
      (X : BinomialEdgeVars (Fin n) → MvPolynomial (BinomialEdgeVars (Fin n)) K)) := by
    rw [show Set.range X = X '' Set.univ from Set.image_univ.symm,
        MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have : m ≠ 0 := by
      intro h; subst h
      simp only [MvPolynomial.mem_support_iff] at hm; exact hm ha
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
    exact ⟨i, Set.mem_univ _, hi⟩
  -- The image of span(range X) under mk is contained in p
  have hmap : Ideal.map (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
      (Ideal.span (Set.range X)) ≤ p := by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hf
    exact hvar v
  exact hmap (Ideal.mem_map_of_mem _ hmem)

/-- If a prime `p` is not contained in the augmentation ideal, then some variable
image lies outside `p`.

Proof: `augIdeal` is maximal; if all variable images were in `p`, then
`augIdeal ≤ p` by `augIdeal_le_of_forall_mkI_X_mem`, so `p = augIdeal`
(maximality), contradicting `p ⊄ augIdeal`. -/
private lemma exists_var_not_mem_of_not_le_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    (hp : ¬(p ≤ augIdeal (K := K) G)) :
    ∃ v : BinomialEdgeVars (Fin n),
      Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∉ p := by
  by_contra h
  push_neg at h
  -- All variable images are in p, so augIdeal ≤ p
  have h_le := augIdeal_le_of_forall_mkI_X_mem G h
  -- augIdeal is maximal and p is proper, so augIdeal = p, hence p ≤ augIdeal
  exact hp ((augIdeal_isMaximal (K := K) G).eq_of_le
    (Ideal.IsPrime.ne_top ‹_›) h_le).symm.le

/-- A variable image not in `p` becomes a unit in the localization `R_p`. -/
private lemma isUnit_algebraMap_mkI_X {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {v : BinomialEdgeVars (Fin n)}
    (hv : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∉ p) :
    IsUnit (algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) :=
  IsLocalization.map_units (Localization.AtPrime p) ⟨_, show _ ∈ p.primeCompl from hv⟩

/-- In the localization `R_p`, if a variable `X v` is a unit and `X v * X w ∈ I`
(i.e., `(v, w)` is an edge of the HH bipartite graph), then `X w` maps to zero.

This is the key structural fact: inverting one variable kills its neighbors in the
bipartite graph. -/
private lemma algebraMap_mkI_X_eq_zero_of_edge {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {v w : BinomialEdgeVars (Fin n)}
    (hedge : X v * X w ∈ bipartiteEdgeMonomialIdeal (K := K) G)
    (hv : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∉ p) :
    algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X w)) = 0 := by
  set mk := Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
  set Rp := Localization.AtPrime p
  have h0 : mk (X v * X w) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hedge
  have h1 : algebraMap _ Rp (mk (X v)) * algebraMap _ Rp (mk (X w)) = 0 := by
    rw [← map_mul, ← map_mul, h0, map_zero]
  exact (IsUnit.mul_right_eq_zero (isUnit_algebraMap_mkI_X G hv)).mp h1

/-- Under HH conditions with `p ⊄ augIdeal`, every diagonal edge `(x_i, y_i)` in the
HH bipartite graph has one endpoint that is a unit and the other that is zero in `R_p`.

More precisely: if `Sum.inl i` is not in `p`, then `y_i` maps to zero (and vice versa).
The HH diagonal ensures `x_i y_i ∈ I` for `i + 1 < n`. -/
private lemma algebraMap_mkI_y_eq_zero_of_x_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (hHH : HerzogHibiConditions n G)
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {i : Fin n} (hi : i.val + 1 < n)
    (hxi : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inl i)) ∉ p) :
    algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr i))) = 0 := by
  apply algebraMap_mkI_X_eq_zero_of_edge G _ hxi
  exact Ideal.subset_span ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩

/-- Symmetric version: if `Sum.inr i` is not in `p`, then `x_i` maps to zero. -/
private lemma algebraMap_mkI_x_eq_zero_of_y_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (hHH : HerzogHibiConditions n G)
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {i : Fin n} (hi : i.val + 1 < n)
    (hyi : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inr i)) ∉ p) :
    algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl i))) = 0 := by
  apply algebraMap_mkI_X_eq_zero_of_edge G _ hyi
  -- Need X (Sum.inr i) * X (Sum.inl i) ∈ I; the ideal contains x_i * y_i = y_i * x_i
  have hmem : X (Sum.inl i) * X (Sum.inr i) ∈
      bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.subset_span ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩
  rwa [mul_comm] at hmem

/-! #### Flat base change: full regular sequence is weakly regular on any localization -/

/-- The full regular sequence, mapped to any localization `R_p`, is weakly regular
on `R_p` as an `R_p`-module. This holds for ALL primes `p`, regardless of whether
`p ≤ augIdeal`.

The proof uses flat base change: localization is flat, so `IsWeaklyRegular R rs`
transfers to `IsWeaklyRegular (R ⊗ R_p) rs` by `isWeaklyRegular_rTensor`,
then `R ⊗_R R_p ≅ R_p` by `TensorProduct.lid`, and finally
`isWeaklyRegular_map_algebraMap_iff` converts to the mapped sequence. -/
private lemma fullRegSeq_isWeaklyRegular_localization
    {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G))
    [p.IsPrime] :
    RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime p)
      (((fullRegSeq (K := K) n hn).map
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))).map
        (algebraMap _ (Localization.AtPrime p))) := by
  set R := MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G
  set Rp := Localization.AtPrime p
  set rs := (fullRegSeq (K := K) n hn).map
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
  -- fullRegSeq is weakly regular on R
  have hreg : RingTheory.Sequence.IsWeaklyRegular R rs :=
    bipartiteEdgeMonomialIdeal_isWeaklyRegular_full (K := K) hn hHH
  -- R_p is flat over R
  haveI : Module.Flat R Rp := IsLocalization.flat Rp p.primeCompl
  -- Flat base change + lid + algebraMap iff
  exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff Rp Rp rs).mpr
    ((LinearEquiv.isWeaklyRegular_congr (TensorProduct.lid R Rp) rs).mp
      hreg.isWeaklyRegular_rTensor)

/-! #### Minimal primes are below the augmentation ideal -/

/-- Every minimal prime of the HH quotient ring is contained in the augmentation ideal.

The proof uses the minimal vertex cover classification: each minimal prime of the
bipartite edge monomial ideal is `span(X '' C)` for a vertex cover `C`. Its image
in the quotient ring is generated by variable images, all of which lie in the
augmentation ideal by `mkI_X_mem_augIdeal`. -/
private lemma minimalPrime_le_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    {q : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    (hq : q ∈ minimalPrimes _) :
    q ≤ augIdeal (K := K) G := by
  -- Q = comap mk q is a minimal prime of bipartiteEdgeMonomialIdeal G
  have hQ : (q.comap (Ideal.Quotient.mk _)) ∈
      (bipartiteEdgeMonomialIdeal (K := K) G).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q, hq, rfl⟩
  -- Q = span(X '' C) for some minimal vertex cover C
  obtain ⟨C, _, hQeq⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hQ
  -- q = map mk (comap mk q) since mk is surjective
  rw [show q = (q.comap (Ideal.Quotient.mk _)).map (Ideal.Quotient.mk _) from
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q).symm]
  -- Now q = map mk (span(X '' C)), generated by variable images
  rw [hQeq, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨v, _, rfl⟩ := hf
  exact mkI_X_mem_augIdeal G v

/-! #### Regular elements in primes of positive height -/

/-- In a reduced ring, an element outside all minimal primes is SMulRegular.

In a reduced ring `sInf (minimalPrimes R) = 0`, so if `r ∉ q` for each
minimal prime `q`, then `r * s = 0` forces `s ∈ ∩ q = 0`. -/
private lemma isSMulRegular_of_not_mem_minimalPrimes'
    {S : Type*} [CommRing S] [IsReduced S]
    {r : S} (hr : ∀ q ∈ minimalPrimes S, r ∉ q) : IsSMulRegular S r := by
  intro a b hab
  have heq : r * a = r * b := by exact_mod_cast hab
  have h0 : r * (a - b) = 0 := by rw [mul_sub]; exact sub_eq_zero.mpr heq
  have hmem : a - b ∈ sInf (minimalPrimes S) := by
    rw [Ideal.mem_sInf]; intro q hq
    exact (((minimalPrimes_eq_minimals (R := S) ▸ hq).1).mem_or_mem
      (h0 ▸ q.zero_mem : r * (a - b) ∈ q)).resolve_left (hr q hq)
  rw [show sInf (minimalPrimes S) = (⊥ : Ideal S) from by
    change sInf ((⊥ : Ideal S).minimalPrimes) = ⊥
    rw [Ideal.sInf_minimalPrimes]; exact nilradical_eq_zero S, Ideal.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

/-- **Regular element in `p ∩ m` for reduced rings**: In a reduced Noetherian ring
where every minimal prime is below a non-minimal prime `m`, any prime `p` of positive
height contains an `R`-regular element that also lies in `m`.

The proof uses a domain-based argument: for each minimal prime `q`, we show
`p ⊓ m ⊄ q`. Since `q` is prime and both `p` and `m` strictly contain `q`
(by height and minimality considerations), taking `a ∈ p \ q` and `b ∈ m \ q`
gives `ab ∈ (p ⊓ m) \ q` by primality. Prime avoidance then produces an element
outside all minimal primes (hence regular). -/
private theorem exists_smulRegular_in_inf'
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsReduced S]
    (m : Ideal S) [m.IsPrime]
    (hmin_le : ∀ q ∈ minimalPrimes S, q ≤ m)
    (hm_ne_min : m ∉ minimalPrimes S)
    (p : Ideal S) [p.IsPrime]
    (hp : (0 : WithBot ℕ∞) < Ideal.height p) :
    ∃ x ∈ p, x ∈ m ∧ IsSMulRegular S x := by
  have hp_not_min : p ∉ minimalPrimes S := by
    intro hmin; simp [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff.mpr hmin] at hp
  -- Step 1: p ⊓ m ⊄ q for each minimal prime q
  have hp_inf_not_le : ∀ q ∈ minimalPrimes S, ¬(p ⊓ m ≤ q) := by
    intro q hq hle
    have hq_prime : q.IsPrime := (minimalPrimes_eq_minimals (R := S) ▸ hq).1
    -- p contains some minimal prime q'; since q' ≤ m, we get q' ≤ p ⊓ m ≤ q, hence q' = q
    obtain ⟨q', hq'min, hq'p⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal S) ≤ p from bot_le)
    have hq'minR : q' ∈ minimalPrimes S := hq'min
    have hq'q : q' ≤ q := le_trans (le_inf hq'p (hmin_le q' hq'minR)) hle
    have hq'eq : q' = q := le_antisymm hq'q
      ((minimalPrimes_eq_minimals (R := S) ▸ hq).2
        (minimalPrimes_eq_minimals (R := S) ▸ hq'minR).1 hq'q)
    -- So q ≤ p and q < p, q < m
    have hq_lt_p : q < p := lt_of_le_of_ne (hq'eq ▸ hq'p) (fun h => hp_not_min (h.symm ▸ hq))
    have hq_lt_m : q < m := lt_of_le_of_ne (hmin_le q hq) (fun h => hm_ne_min (h.symm ▸ hq))
    -- Domain argument: a ∈ p\q, b ∈ m\q, ab ∈ (p ⊓ m) \ q
    obtain ⟨a, hap, haq⟩ := Set.exists_of_ssubset hq_lt_p
    obtain ⟨b, hbm, hbq⟩ := Set.exists_of_ssubset hq_lt_m
    exact (hq_prime.mem_or_mem (hle ⟨p.mul_mem_right b hap, m.mul_mem_left a hbm⟩)).elim haq hbq
  -- Step 2: prime avoidance → ∃ x ∈ p ⊓ m outside all minimal primes
  have hfin : (minimalPrimes S).Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing S ⊥
  have h_not_sub : ¬((p ⊓ m : Set S) ⊆ ⋃ q ∈ minimalPrimes S, (q : Set S)) := by
    rw [show (p ⊓ m : Set S) = ↑(p ⊓ m : Ideal S) from rfl,
      Ideal.subset_union_prime_finite hfin 0 0
        (fun q hq _ _ => (minimalPrimes_eq_minimals (R := S) ▸ hq).1)]
    exact fun ⟨q, hq, hle⟩ => hp_inf_not_le q hq hle
  obtain ⟨x, hx_mem, hx_not_mem⟩ := Set.not_subset.mp h_not_sub
  simp only [Set.mem_iUnion] at hx_not_mem; push_neg at hx_not_mem
  exact ⟨x, hx_mem.1, hx_mem.2, isSMulRegular_of_not_mem_minimalPrimes' hx_not_mem⟩

/-- **Regular element in `p ∩ augIdeal` for the HH quotient**: For any prime `p` not
contained in the augmentation ideal, there exists an element of `p ∩ augIdeal` that is
a non-zero-divisor on the HH quotient ring.

This is the key ingredient for the graded CM induction: it provides the regular element
in `maxIdeal(R_p) ∩ maxIdeal(R_{m⁺})` needed for both forward and converse CM transfer.

The proof uses:
- the HH quotient is reduced (`bipartiteEdgeMonomialIdeal_isRadical`);
- all minimal primes are below `augIdeal` (`minimalPrime_le_augIdeal`);
- a domain-based prime avoidance argument (`exists_smulRegular_in_inf'`). -/
private lemma exists_smulRegular_in_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    (hp : ¬(p ≤ augIdeal (K := K) G)) :
    ∃ x ∈ p, x ∈ augIdeal (K := K) G ∧
      IsSMulRegular (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) x := by
  -- Abbreviations (using let to avoid set-renaming issues)
  change ∃ x ∈ p, x ∈ augIdeal (K := K) G ∧ IsSMulRegular _ x
  haveI hm_prime : (augIdeal (K := K) G).IsPrime := augIdeal_isPrime G
  haveI : IsReduced (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (bipartiteEdgeMonomialIdeal_isRadical G)
  haveI : IsNoetherianRing (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
    Ideal.Quotient.isNoetherianRing _
  -- height(p) > 0: all minimal primes ≤ augIdeal, so p minimal ⟹ p ≤ augIdeal
  have hp_pos : (0 : WithBot ℕ∞) < Ideal.height p := by
    rw [Ideal.height_eq_primeHeight]
    by_contra h; push_neg at h
    have h0 : p.primeHeight = 0 := nonpos_iff_eq_zero.mp (by exact_mod_cast h)
    exact hp (minimalPrime_le_augIdeal G (Ideal.primeHeight_eq_zero_iff.mp h0))
  -- augIdeal is not minimal: if it were, sInf = augIdeal, but sInf = 0 (reduced).
  -- Then augIdeal = ⊥ means ⊥ is maximal, so R is a field with dim 0,
  -- contradicting dim(R) = n+1 ≥ 3.
  set R' := MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G
  have hm_ne_min : augIdeal (K := K) G ∉ minimalPrimes R' := by
    intro hmin
    have hsInf : sInf (minimalPrimes R') = augIdeal (K := K) G := le_antisymm
      (sInf_le hmin)
      (le_sInf (fun q hq => (minimalPrimes_eq_minimals (R := R') ▸ hmin).2
        (minimalPrimes_eq_minimals (R := R') ▸ hq).1 (minimalPrime_le_augIdeal G hq)))
    have h0 : sInf (minimalPrimes R') = (⊥ : Ideal R') := by
      change sInf ((⊥ : Ideal R').minimalPrimes) = ⊥
      rw [Ideal.sInf_minimalPrimes]; exact nilradical_eq_zero R'
    have hbot : augIdeal (K := K) G = ⊥ := by rw [← hsInf, h0]
    have hdim := ringKrullDim_bipartiteEdgeMonomialIdeal (K := K) (by omega : 1 ≤ n) hHH
    haveI : (nilradical R').IsMaximal := by
      have : nilradical R' = ⊥ := nilradical_eq_zero R'
      rw [this]; exact hbot ▸ augIdeal_isMaximal G
    haveI := Ring.KrullDimLE.of_isMaximal_nilradical R'
    haveI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr
      (bipartiteEdgeMonomialIdeal_ne_top (K := K) G)
    have hfield : ringKrullDim R' = 0 := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp ‹_›
    rw [hfield] at hdim; exact absurd hdim (by norm_cast)
  exact exists_smulRegular_in_inf' (augIdeal (K := K) G)
    (fun q hq => minimalPrime_le_augIdeal G hq) hm_ne_min p hp_pos

/-! #### Graded contraction lemma

The **graded contraction lemma** for `MvPolynomial` quotients:
in a quotient by a homogeneous ideal, any element with invertible constant
coefficient is a non-zero-divisor.  This is the key ingredient in the
Bruns–Herzog 2.1.3(b) proof that graded CM at the irrelevant ideal implies
global CM. -/

/-- If `f` has zero constant coefficient and all homogeneous components of `g` below
degree `d` vanish, then `homogeneousComponent d (f * g) = 0`.

This is the degree-counting core of the graded contraction argument:
the lowest-degree component of the product is determined only by the constant
coefficient of the first factor. -/
private lemma homogeneousComponent_mul_eq_zero_of_low_degrees
    {σ : Type*} {R : Type*} [CommSemiring R]
    {f g : MvPolynomial σ R} {d : ℕ}
    (hf : MvPolynomial.constantCoeff f = 0)
    (hg : ∀ j < d, MvPolynomial.homogeneousComponent j g = 0) :
    MvPolynomial.homogeneousComponent d (f * g) = 0 := by
  classical
  ext m
  rw [MvPolynomial.coeff_homogeneousComponent, MvPolynomial.coeff_zero]
  split_ifs with hmd
  · rw [MvPolynomial.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases ha : a = 0
    · simp [ha, ← MvPolynomial.constantCoeff_eq, hf]
    · have hab_deg : a.degree + b.degree = d := by
        rw [← Finsupp.degree.map_add, hab]; exact hmd
      have ha_pos : 0 < a.degree := by
        rw [pos_iff_ne_zero]; exact fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
      have hb_lt : b.degree < d := by omega
      have : MvPolynomial.coeff b g = 0 := by
        have := congr_arg (MvPolynomial.coeff b) (hg b.degree hb_lt)
        rwa [MvPolynomial.coeff_homogeneousComponent, if_pos rfl,
          MvPolynomial.coeff_zero] at this
      rw [this, mul_zero]
  · rfl

/-- Helper: `homogeneousComponent j` applied to a sum of lower homogeneous
components of `g` recovers `homogeneousComponent j g` for `j < d`. -/
private lemma homogeneousComponent_sum_low_eq
    {σ : Type*} {R : Type*} [CommSemiring R]
    (g : MvPolynomial σ R) (d : ℕ) {j : ℕ} (hj : j < d) :
    MvPolynomial.homogeneousComponent j
      (∑ k ∈ Finset.range d, MvPolynomial.homogeneousComponent k g) =
    MvPolynomial.homogeneousComponent j g := by
  rw [_root_.map_sum (MvPolynomial.homogeneousComponent j)]
  simp_rw [MvPolynomial.homogeneousComponent_of_mem
    (MvPolynomial.homogeneousComponent_mem _ g)]
  exact (Finset.sum_ite_eq (Finset.range d) j _).trans
    (if_pos (Finset.mem_range.mpr hj))

/-- **Graded contraction lemma for `MvPolynomial`**: if `I` is a homogeneous
ideal (closed under taking homogeneous components), `f * g ∈ I`, and
`constantCoeff f` is a unit, then `g ∈ I`.

Equivalently: in `MvPolynomial σ K ⧸ I`, any element with invertible
constant coefficient is a non-zero-divisor.

The proof works by strong induction on the degree: at each step,
subtracting the already-proved low-degree components and using the
degree-counting lemma `homogeneousComponent_mul_eq_zero_of_low_degrees`
shows that the unit constant coefficient of `f` forces each successive
homogeneous component of `g` into `I`. -/
private theorem mem_of_mul_mem_of_isUnit_constantCoeff
    {σ : Type*} {K : Type*} [Field K]
    {I : Ideal (MvPolynomial σ K)}
    (hI_hom : ∀ p ∈ I, ∀ (d : ℕ), MvPolynomial.homogeneousComponent d p ∈ I)
    {f g : MvPolynomial σ K}
    (hfg : f * g ∈ I)
    (hf : IsUnit (MvPolynomial.constantCoeff f)) :
    g ∈ I := by
  classical
  -- Suffice to show all homogeneous components are in I
  suffices h : ∀ d, MvPolynomial.homogeneousComponent d g ∈ I by
    rw [show g = ∑ i ∈ Finset.range (g.totalDegree + 1),
      MvPolynomial.homogeneousComponent i g from (MvPolynomial.sum_homogeneousComponent g).symm]
    exact I.sum_mem (fun d _ => h d)
  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    set c := MvPolynomial.constantCoeff f
    set g_low := ∑ j ∈ Finset.range d, MvPolynomial.homogeneousComponent j g
    have hg_low_mem : g_low ∈ I :=
      I.sum_mem (fun j hj => ih j (Finset.mem_range.mp hj))
    -- g - g_low has no components below degree d
    have hg_high_vanish : ∀ j < d,
        MvPolynomial.homogeneousComponent j (g - g_low) = 0 := by
      intro j hj
      rw [map_sub, homogeneousComponent_sum_low_eq g d hj, sub_self]
    -- homogeneousComponent d (g - g_low) = homogeneousComponent d g
    have hcomp_eq : MvPolynomial.homogeneousComponent d (g - g_low) =
        MvPolynomial.homogeneousComponent d g := by
      rw [map_sub]
      have : MvPolynomial.homogeneousComponent d g_low = 0 := by
        rw [_root_.map_sum (MvPolynomial.homogeneousComponent d)]
        simp_rw [MvPolynomial.homogeneousComponent_of_mem
          (MvPolynomial.homogeneousComponent_mem _ g)]
        exact Finset.sum_eq_zero
          (fun k hk => if_neg (by rw [Finset.mem_range] at hk; omega))
      rw [this, sub_zero]
    -- f * (g - g_low) ∈ I
    have hfg_high : f * (g - g_low) ∈ I := by
      rw [mul_sub]; exact I.sub_mem hfg (I.mul_mem_left f hg_low_mem)
    -- Write f = C c + f' where f' has zero constant coefficient
    set f' := f - MvPolynomial.C c
    have hf'_cc : MvPolynomial.constantCoeff f' = 0 := by simp [f', c]
    -- degree-d component of f' * (g - g_low) vanishes
    have hvanish : MvPolynomial.homogeneousComponent d (f' * (g - g_low)) = 0 :=
      homogeneousComponent_mul_eq_zero_of_low_degrees hf'_cc hg_high_vanish
    -- degree-d component of f * (g - g_low) is in I
    have hcomp_fgh : MvPolynomial.homogeneousComponent d (f * (g - g_low)) ∈ I :=
      hI_hom _ hfg_high d
    -- so C c * homogeneousComponent d g ∈ I
    have hCcg : MvPolynomial.C c * MvPolynomial.homogeneousComponent d g ∈ I := by
      have : f * (g - g_low) = MvPolynomial.C c * (g - g_low) + f' * (g - g_low) := by ring
      rw [this, map_add, hvanish, add_zero, MvPolynomial.homogeneousComponent_C_mul,
        hcomp_eq] at hcomp_fgh
      exact hcomp_fgh
    -- C c is a unit → cancel
    exact (Submodule.smul_mem_iff_of_isUnit I (RingHom.isUnit_map MvPolynomial.C hf)).mp hCcg

/-! #### Homogeneity of the bipartite edge monomial ideal -/

/-- The bipartite edge monomial ideal is a monomial ideal: for every polynomial
in `I`, each support monomial (with coefficient 1) is also in `I`. -/
private theorem bipartiteEdgeMonomialIdeal_isMonomial {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (bipartiteEdgeMonomialIdeal (K := K) G).IsMonomial := by
  apply isMonomial_span_of_support_singleton
  rintro _ ⟨i, j, hj, hadj, hle, rfl⟩
  exact ⟨Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1, by
    rw [show (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial _ K) =
      monomial (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1) 1 from by
      simp [X, monomial_mul]]
    exact support_monomial_subset⟩

/-- Monomial ideals are closed under taking homogeneous components. -/
private theorem isMonomial_homogeneousComponent_mem {n : ℕ}
    (G : SimpleGraph (Fin n))
    (p : MvPolynomial (BinomialEdgeVars (Fin n)) K)
    (hp : p ∈ bipartiteEdgeMonomialIdeal (K := K) G) (d : ℕ) :
    MvPolynomial.homogeneousComponent d p ∈ bipartiteEdgeMonomialIdeal (K := K) G := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply]
  apply Ideal.sum_mem
  intro m hm
  rw [Finset.mem_filter] at hm
  have hmon : MvPolynomial.monomial m (1 : K) ∈ bipartiteEdgeMonomialIdeal (K := K) G :=
    bipartiteEdgeMonomialIdeal_isMonomial G p hp m hm.1
  rw [show MvPolynomial.monomial m (MvPolynomial.coeff m p) =
    MvPolynomial.C (MvPolynomial.coeff m p) * MvPolynomial.monomial m 1 from by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  exact Ideal.mul_mem_left _ _ hmon

/-! #### F2 route scaffolding: unit set, neighborhood, survivors -/

/-- Neighborhood of `U` in the HH bipartite graph (undirected). -/
private def hhNbhd {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Set (BinomialEdgeVars (Fin n)) :=
  { w | ∃ u ∈ U, (u, w) ∈ hhEdgeSet G ∨ (w, u) ∈ hhEdgeSet G }

/-- `U` is independent in the HH bipartite graph. -/
private def hhIndep {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Prop :=
  ∀ ⦃u v⦄, u ∈ U → v ∈ U → (u, v) ∉ hhEdgeSet G

/-- Survivor set: vertices neither in `U` nor adjacent to `U`. -/
private def hhSurvivors {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Set (BinomialEdgeVars (Fin n)) :=
  (U ∪ hhNbhd G U)ᶜ

/-! #### Lemma 3 — one-sided survivors are isolated in `Γ_W` -/

/-- **Lemma 3 (x-case)**: Under HH conditions, if `x_i` is a survivor but `y_i` is not,
then every HH-neighbor of `x_i` is outside the survivor set. -/
private lemma hhSurvivor_x_isolated {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))}
    {i : Fin n}
    (hxi : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hyi : (Sum.inr i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U)
    {j : Fin n} (hedge : (Sum.inl i, Sum.inr j) ∈ hhEdgeSet G) :
    (Sum.inr j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
  -- Unpack the edge data
  obtain ⟨i', j', hj', hadj_ij, hij, heq⟩ := hedge
  rw [Prod.mk.injEq] at heq
  obtain ⟨hil, hir⟩ := heq
  have hii' : i = i' := Sum.inl.inj hil
  have hjj' : j = j' := Sum.inr.inj hir
  subst hii'; subst hjj'
  -- Diagonal edge at i exists: hedge forces i.val + 1 < n
  have hi_succ : i.val + 1 < n := by
    have : i.val + 1 ≤ j.val + 1 := by exact_mod_cast Nat.succ_le_succ hij
    omega
  -- hyi: inr i ∉ (U ∪ N)ᶜ, so inr i ∈ U ∪ N
  have hy_in : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ U ∪ hhNbhd G U := by
    by_contra h; exact hyi h
  -- Case analysis on how inr i fails to be a survivor
  rcases hy_in with hy_U | hy_N
  · -- inr i ∈ U: the diagonal edge (inl i, inr i) forces inl i ∈ N(U), contradicting inl i ∈ W
    exfalso
    apply hxi
    refine Or.inr ⟨Sum.inr i, hy_U, Or.inr ?_⟩
    exact ⟨i, i, hi_succ, hHH.diagonal i hi_succ, le_refl i, rfl⟩
  · -- inr i ∈ N(U): choose u ∈ U adjacent to inr i.
    obtain ⟨u, hu_U, hu_adj⟩ := hy_N
    rcases hu_adj with he1 | he2
    · -- (u, inr i) ∈ hhEdgeSet: u = Sum.inl a, and the edge is (inl a, inr i)
      obtain ⟨a, i'', hi_succ', hadj_ai, h_ai, heq_ai⟩ := he1
      have hu_eq : u = Sum.inl a := (Prod.mk.inj heq_ai).1
      have hi_eq : i = i'' := Sum.inr.inj (Prod.mk.inj heq_ai).2
      subst hi_eq
      -- a ≤ i; a ≠ i because inl a ∈ U and inl i ∈ W
      have ha_ne_i : a ≠ i := by
        rintro rfl
        apply hxi
        exact Or.inl (hu_eq ▸ hu_U)
      have ha_lt_i : a < i := lt_of_le_of_ne h_ai ha_ne_i
      -- Split on whether j = i
      by_cases hji : j = i
      · rw [hji]; exact hyi
      · have hi_lt_j : i < j := lt_of_le_of_ne hij (Ne.symm hji)
        -- HH transitivity on a < i < j
        have hadj_aj : G.Adj a ⟨j.val + 1, hj'⟩ :=
          hHH.transitivity a i j hi_succ' hj' ha_lt_i hi_lt_j hadj_ai hadj_ij
        -- Therefore (inl a, inr j) ∈ hhEdgeSet, so inr j ∈ N(U) via u = inl a
        intro hj_W
        apply hj_W
        refine Or.inr ⟨Sum.inl a, hu_eq ▸ hu_U, Or.inl ?_⟩
        refine ⟨a, j, hj', hadj_aj, ?_, rfl⟩
        exact le_of_lt (lt_of_lt_of_le ha_lt_i hij)
    · -- (inr i, u) ∈ hhEdgeSet: impossible since edges are (inl _, inr _)
      exfalso
      obtain ⟨i'', j'', _, _, _, heq_bad⟩ := he2
      exact Sum.inl_ne_inr ((Prod.mk.inj heq_bad).1.symm)

/-- **Lemma 3 (y-case)**: symmetric to the x-case. If `y_i` is a survivor but `x_i` is not,
then every HH-neighbor of `y_i` is outside the survivor set. -/
private lemma hhSurvivor_y_isolated {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))}
    {i : Fin n}
    (hyi : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hxi : (Sum.inl i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U)
    {j : Fin n} (hedge : (Sum.inl j, Sum.inr i) ∈ hhEdgeSet G) :
    (Sum.inl j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
  obtain ⟨j', i', hi', hadj_ji, hji, heq⟩ := hedge
  rw [Prod.mk.injEq] at heq
  obtain ⟨hil, hir⟩ := heq
  have hjj' : j = j' := Sum.inl.inj hil
  have hii' : i = i' := Sum.inr.inj hir
  subst hjj'; subst hii'
  -- Diagonal edge at i exists (hedge needs i.val + 1 < n directly)
  -- hxi: inl i ∉ (U ∪ N)ᶜ, so inl i ∈ U ∪ N
  have hx_in : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ U ∪ hhNbhd G U := by
    by_contra h; exact hxi h
  rcases hx_in with hx_U | hx_N
  · -- inl i ∈ U: diagonal (inl i, inr i) forces inr i ∈ N, contradicting inr i ∈ W
    exfalso
    apply hyi
    refine Or.inr ⟨Sum.inl i, hx_U, Or.inl ?_⟩
    exact ⟨i, i, hi', hHH.diagonal i hi', le_refl i, rfl⟩
  · -- inl i ∈ N(U): choose u ∈ U adjacent to inl i
    obtain ⟨u, hu_U, hu_adj⟩ := hx_N
    rcases hu_adj with he1 | he2
    · -- (u, inl i) ∈ hhEdgeSet: impossible (edges go inl → inr)
      exfalso
      obtain ⟨i'', j'', _, _, _, heq_bad⟩ := he1
      exact Sum.inl_ne_inr ((Prod.mk.inj heq_bad).2)
    · -- (inl i, u) ∈ hhEdgeSet: u = Sum.inr b, and the edge is (inl i, inr b)
      obtain ⟨i'', b, hb_succ, hadj_ib, h_ib, heq_ib⟩ := he2
      have hi_eq : i = i'' := Sum.inl.inj (Prod.mk.inj heq_ib).1
      have hu_eq : u = Sum.inr b := (Prod.mk.inj heq_ib).2
      subst hi_eq
      -- i ≤ b; b ≠ i because inr b ∈ U and inr i ∈ W
      have hb_ne_i : b ≠ i := by
        rintro rfl
        apply hyi
        exact Or.inl (hu_eq ▸ hu_U)
      have hi_lt_b : i < b := lt_of_le_of_ne h_ib (Ne.symm hb_ne_i)
      -- Split on whether j = i
      by_cases hji_eq : j = i
      · rw [hji_eq]; exact hxi
      · have hj_lt_i : j < i := lt_of_le_of_ne hji hji_eq
        -- HH transitivity on j < i < b
        have hadj_jb : G.Adj j ⟨b.val + 1, hb_succ⟩ :=
          hHH.transitivity j i b hi' hb_succ hj_lt_i hi_lt_b hadj_ji hadj_ib
        -- Therefore (inl j, inr b) ∈ hhEdgeSet, so inl j ∈ N(U) via u = inr b
        intro hj_W
        apply hj_W
        refine Or.inr ⟨Sum.inr b, hu_eq ▸ hu_U, Or.inr ?_⟩
        refine ⟨j, b, hb_succ, hadj_jb, ?_, rfl⟩
        exact le_of_lt (lt_of_lt_of_le hj_lt_i h_ib)

/-! #### Step 2/3: paired survivors, smaller HH graph, restricted ring -/

/-- The paired-survivor index set `C`: indices `i : Fin n` with `i.val + 1 < n`
and both `inl i` and `inr i` in `hhSurvivors G U`.

These are the indices on which a fresh pair of variables `(x'_a, y'_a)` will
sit in the reduced HH ring `A^red_{G'}`. -/
private noncomputable def pairedSurvivors {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter
    (fun i => i.val + 1 < n ∧
      (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U ∧
      (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)

/-- The size `r = |C|` of the paired-survivor set. -/
private noncomputable abbrev pairedCount {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : ℕ :=
  (pairedSurvivors G U).card

/-- The order-preserving embedding `Fin r ↪o Fin n` from the paired-survivor
set, using `Finset.orderEmbOfFin`. -/
private noncomputable def pairedSurvivorsEmb {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) :
    Fin (pairedCount G U) ↪o Fin n :=
  (pairedSurvivors G U).orderEmbOfFin rfl

/-- The `a`-th paired-survivor index `c_a : Fin n`. -/
private noncomputable abbrev pairedSurvivorsVal {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) : Fin n :=
  pairedSurvivorsEmb G U a

/-- `pairedSurvivorsVal G U a` is indeed a paired-survivor element. -/
private theorem pairedSurvivorsVal_mem {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) :
    pairedSurvivorsVal G U a ∈ pairedSurvivors G U :=
  Finset.orderEmbOfFin_mem _ _ a

/-- Unpacks `pairedSurvivorsVal_mem` into the three component facts. -/
private theorem pairedSurvivorsVal_spec {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) :
    (pairedSurvivorsVal G U a).val + 1 < n ∧
    (Sum.inl (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G U ∧
    (Sum.inr (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G U := by
  have h := pairedSurvivorsVal_mem G U a
  classical
  unfold pairedSurvivors at h
  rw [Finset.mem_filter] at h
  exact h.2

/-- The auxiliary "HH-edge in the smaller graph" relation, encoded one-sidedly
so that `smallerHHGraph := SimpleGraph.fromRel smallerHHRel` has HH-shaped
edges after symmetrisation. -/
private noncomputable def smallerHHRel {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (u v : Fin (pairedCount G U + 1)) : Prop :=
  ∃ (a b : Fin (pairedCount G U)),
    a ≤ b ∧
    u = a.castSucc ∧
    v.val = b.val + 1 ∧
    ∃ (hc : (pairedSurvivorsVal G U b).val + 1 < n),
      G.Adj (pairedSurvivorsVal G U a)
        ⟨(pairedSurvivorsVal G U b).val + 1, hc⟩

/-- The smaller HH graph `G'` on `Fin (r + 1)` associated to `(G, U)`. Edges
come from the HH edges of `G` restricted to paired-survivor indices. -/
private noncomputable def smallerHHGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    SimpleGraph (Fin (pairedCount G U + 1)) :=
  SimpleGraph.fromRel (smallerHHRel G U)

/-- The smaller HH graph inherits the HH conditions from the original. -/
private theorem smallerHHGraph_herzogHibi {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) :
    HerzogHibiConditions (pairedCount G U + 1) (smallerHHGraph G U) := by
  refine ⟨?_, ?_⟩
  · -- Diagonal: for i : Fin (r + 1) with i.val + 1 < r + 1,
    --   G'.Adj i ⟨i.val + 1, _⟩.
    intro i hi
    -- i.val < r, so i = (⟨i.val, _⟩ : Fin r).castSucc.
    have hi_lt : i.val < pairedCount G U := by omega
    set a : Fin (pairedCount G U) := ⟨i.val, hi_lt⟩ with ha_def
    -- Diagonal at c_a : Fin n.
    have hc_succ : (pairedSurvivorsVal G U a).val + 1 < n :=
      (pairedSurvivorsVal_spec G U a).1
    have hadj : G.Adj (pairedSurvivorsVal G U a)
        ⟨(pairedSurvivorsVal G U a).val + 1, hc_succ⟩ :=
      hHH.diagonal _ hc_succ
    -- Package as smallerHHRel with a = b.
    rw [smallerHHGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨a, a, le_refl a, ?_, ?_, hc_succ, hadj⟩⟩
    · -- i ≠ ⟨i.val + 1, hi⟩
      intro heq
      have : i.val = i.val + 1 := congrArg Fin.val heq
      omega
    · -- i = a.castSucc
      apply Fin.ext
      simp [a, Fin.castSucc, Fin.castAdd, Fin.castLE]
    · -- (⟨i.val + 1, hi⟩ : Fin (r+1)).val = a.val + 1
      simp [a]
  · -- Transitivity.
    intro i j k hj hk hij hjk hadj1 hadj2
    -- Unpack G'.Adj i ⟨j.val + 1, hj⟩.
    rw [smallerHHGraph, SimpleGraph.fromRel_adj] at hadj1 hadj2
    obtain ⟨_, hrel1⟩ := hadj1
    obtain ⟨_, hrel2⟩ := hadj2
    -- smallerHHRel is one-sided: u = castSucc a, v.val = b.val + 1. The reverse
    -- direction is impossible because castSucc has val < r while b.val + 1 is
    -- something's +1. We match the forward direction in each case.
    -- First hadj1: pick the Or-branch that matches the shape (i = castSucc a,
    -- ⟨j.val + 1, hj⟩ = ... b.val + 1). Since j.val + 1 = b.val + 1 forces
    -- j.val = b.val, consistent with the forward branch.
    have hrel1_fwd : smallerHHRel G U i ⟨j.val + 1, hj⟩ := by
      rcases hrel1 with h | h
      · exact h
      · -- reverse: smallerHHRel G U ⟨j.val+1, hj⟩ i
        -- Then ⟨j.val+1, hj⟩ = a.castSucc for some a, so j.val + 1 = a.val < r.
        -- That's fine numerically; but then i.val = b.val + 1, and we want
        -- i to be an a.castSucc in the forward direction. Extract the data
        -- and swap into the forward shape.
        -- We actually do NOT need to swap: the forward shape is what we need.
        -- So match the data: u = ⟨j.val+1, hj⟩, v = i.
        obtain ⟨a, b, hab, hu_eq, hv_eq, hc, hadj⟩ := h
        -- u.val = a.val, and also u.val = j.val + 1, so a.val = j.val + 1.
        have hav : a.val = j.val + 1 := by
          have := congrArg Fin.val hu_eq
          simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
          omega
        -- i.val = b.val + 1 from hv_eq.
        -- But i < j < k in Fin (r+1) means i.val < j.val. And i.val = b.val + 1,
        -- a.val = j.val + 1 with a ≤ b. So j.val + 1 ≤ b.val, hence
        -- i.val = b.val + 1 ≥ j.val + 2 > j.val, contradicting i < j.
        have : j.val + 1 ≤ b.val := hav ▸ hab
        have hi_val : i.val = b.val + 1 := hv_eq
        have : i.val > j.val := by omega
        exact absurd hij (not_lt.mpr (le_of_lt (Fin.lt_def.mpr this)))
    have hrel2_fwd : smallerHHRel G U j ⟨k.val + 1, hk⟩ := by
      rcases hrel2 with h | h
      · exact h
      · obtain ⟨a, b, hab, hu_eq, hv_eq, hc, hadj⟩ := h
        have hav : a.val = k.val + 1 := by
          have := congrArg Fin.val hu_eq
          simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
          omega
        have : k.val + 1 ≤ b.val := hav ▸ hab
        have hj_val : j.val = b.val + 1 := hv_eq
        have : j.val > k.val := by omega
        exact absurd hjk (not_lt.mpr (le_of_lt (Fin.lt_def.mpr this)))
    -- Now unpack the forward relations and apply HH.transitivity on G.
    obtain ⟨a₁, b₁, hab₁, hu₁, hv₁, hc₁, hadj₁⟩ := hrel1_fwd
    obtain ⟨a₂, b₂, hab₂, hu₂, hv₂, hc₂, hadj₂⟩ := hrel2_fwd
    -- From hu₁: i.val = a₁.val (via castSucc).
    have ha₁i : a₁.val = i.val := by
      have h1 := congrArg Fin.val hu₁
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at h1
      omega
    -- From hv₁: j.val + 1 = b₁.val + 1, so b₁.val = j.val.
    have hb₁j : b₁.val = j.val := by
      have h1 : (⟨j.val + 1, hj⟩ : Fin (pairedCount G U + 1)).val = b₁.val + 1 := hv₁
      simp at h1
      omega
    -- From hu₂: j.val = a₂.val.
    have ha₂j : a₂.val = j.val := by
      have h1 := congrArg Fin.val hu₂
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at h1
      omega
    -- From hv₂: k.val = b₂.val.
    have hb₂k : b₂.val = k.val := by
      have h1 : (⟨k.val + 1, hk⟩ : Fin (pairedCount G U + 1)).val = b₂.val + 1 := hv₂
      simp at h1
      omega
    -- Instead of working with a₂ and b₁ separately, use b₁ as the middle index.
    -- a₂ = b₁ numerically.
    have ha₂_eq_b₁ : a₂ = b₁ := Fin.ext (by omega)
    -- i < j ⇒ a₁ < b₁ (a₁.val = i.val, b₁.val = j.val), so c_{a₁} < c_{b₁}.
    have ha₁_lt_b₁ : pairedSurvivorsVal G U a₁ < pairedSurvivorsVal G U b₁ := by
      have : a₁ < b₁ := Fin.lt_def.mpr (by rw [ha₁i, hb₁j]; exact Fin.lt_def.mp hij)
      exact (pairedSurvivorsEmb G U).strictMono this
    -- j < k ⇒ b₁ < b₂, so c_{b₁} < c_{b₂}.
    have hb₁_lt_b₂ : pairedSurvivorsVal G U b₁ < pairedSurvivorsVal G U b₂ := by
      have : b₁ < b₂ := Fin.lt_def.mpr (by rw [hb₁j, hb₂k]; exact Fin.lt_def.mp hjk)
      exact (pairedSurvivorsEmb G U).strictMono this
    -- Transport hadj₂ so its first argument is c_{b₁} instead of c_{a₂}.
    have hadj₂' : G.Adj (pairedSurvivorsVal G U b₁)
        ⟨(pairedSurvivorsVal G U b₂).val + 1, hc₂⟩ := by
      have h := hadj₂
      rw [ha₂_eq_b₁] at h
      exact h
    -- Apply HH.transitivity on G at indices c_{a₁} < c_{b₁} < c_{b₂}.
    have hadj_G : G.Adj (pairedSurvivorsVal G U a₁)
        ⟨(pairedSurvivorsVal G U b₂).val + 1, hc₂⟩ :=
      hHH.transitivity _ _ _ hc₁ hc₂ ha₁_lt_b₁ hb₁_lt_b₂ hadj₁ hadj₂'
    -- Repackage as G'.Adj i ⟨k.val + 1, hk⟩.
    rw [smallerHHGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨a₁, b₂, ?_, hu₁, ?_, hc₂, hadj_G⟩⟩
    · -- i ≠ ⟨k.val + 1, hk⟩: since i < j < k, i.val < k.val < k.val + 1.
      intro heq
      have : i.val = k.val + 1 := congrArg Fin.val heq
      have hi_lt_k : i.val < k.val := lt_trans (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
      omega
    · -- a₁ ≤ b₂: a₁.val = i.val < k.val = b₂.val via i < j < k.
      have : a₁.val < b₂.val := by
        rw [ha₁i, hb₂k]
        exact lt_trans (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
      exact le_of_lt (Fin.lt_def.mpr this)
    · -- (⟨k.val + 1, hk⟩ : Fin (r+1)).val = b₂.val + 1, since b₂.val = k.val.
      simp [hb₂k]

/-! #### Step 3 — restricted ring over `W`

For any `W : Set (BinomialEdgeVars (Fin n))`, we view `MvPolynomial W K` as
the polynomial ring over the subtype `{v // v ∈ W}`, and the restricted edge
set picks the HH edges whose both endpoints lie in `W`. -/

/-- The HH edge set restricted to edges with both endpoints in `W`. -/
private def hhEdgeSetRestrict {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) :
    Set (BinomialEdgeVars (Fin n) × BinomialEdgeVars (Fin n)) :=
  { e | e ∈ hhEdgeSet G ∧ e.1 ∈ W ∧ e.2 ∈ W }

/-- `K[W]`: the polynomial ring over the subtype `{v // v ∈ W}`. -/
private abbrev polyRestrict {n : ℕ} (W : Set (BinomialEdgeVars (Fin n))) :
    Type _ :=
  MvPolynomial W K

/-- The restricted edge set transported to pairs of elements of `W`. -/
private def restrictedEdgesSubtype {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) :
    Set (W × W) :=
  { e | (e.1.val, e.2.val) ∈ hhEdgeSet G }

/-- The restricted edge ideal inside `K[W]`. -/
private def restrictedEdgeIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) :
    Ideal (polyRestrict (K := K) W) :=
  MvPolynomial.variablePairIdeal (R := K) (restrictedEdgesSubtype G W)

/-- The `Λ` set: survivors not in the paired-survivor pairs.

`Λ = W \ ({inl i : i ∈ C} ∪ {inr i : i ∈ C})`, where
`W = hhSurvivors G U` and `C = pairedSurvivors G U`. -/
private def lambdaSet {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) :
    Set (BinomialEdgeVars (Fin n)) :=
  hhSurvivors G U \
    (((pairedSurvivors G U : Finset (Fin n)) : Set (Fin n)).image
        (fun i => (Sum.inl i : BinomialEdgeVars (Fin n))) ∪
     ((pairedSurvivors G U : Finset (Fin n)) : Set (Fin n)).image Sum.inr)

/-- The restricted HH ring `K[W] / I(Γ_G|_W)`. -/
private abbrev restrictedHHRing {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) : Type _ :=
  polyRestrict (K := K) W ⧸ restrictedEdgeIdeal (K := K) G W

/-! #### Step 4/5/6: the L4 iso

The isomorphism `K[W] / I(Γ_G|_W) ≃ₐ[K] A^red_{G'} ⊗_K K[Λ]` on generators:

* `X ⟨Sum.inl c_a, _⟩ ↦ (mk X(inl a)) ⊗ 1` for paired-survivor `a`.
* `X ⟨Sum.inr c_a, _⟩ ↦ (mk X(inr a)) ⊗ 1` similarly.
* `X ⟨λ, _⟩ ↦ 1 ⊗ X ⟨λ, _⟩` for `λ ∈ lambdaSet G U`.
-/

/-- The inverse of `pairedSurvivorsEmb`: given `i ∈ pairedSurvivors G U`,
return the `Fin r` index. -/
private noncomputable def pairedSurvivorsIdx {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) : Fin (pairedCount G U) :=
  ((pairedSurvivors G U).orderIsoOfFin rfl).symm ⟨i, hi⟩

private theorem pairedSurvivorsVal_idx {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    pairedSurvivorsVal G U (pairedSurvivorsIdx G U hi) = i := by
  have h : ((pairedSurvivors G U).orderIsoOfFin rfl)
      (((pairedSurvivors G U).orderIsoOfFin rfl).symm ⟨i, hi⟩) = ⟨i, hi⟩ :=
    ((pairedSurvivors G U).orderIsoOfFin rfl).apply_symm_apply _
  have h' : (((pairedSurvivors G U).orderIsoOfFin rfl)
      (((pairedSurvivors G U).orderIsoOfFin rfl).symm ⟨i, hi⟩) : Fin n) = i :=
    congrArg Subtype.val h
  -- The LHS unfolds to `(pairedSurvivors G U).orderEmbOfFin rfl (idx)`
  -- which is `pairedSurvivorsVal G U (pairedSurvivorsIdx G U hi)`.
  rw [Finset.coe_orderIsoOfFin_apply] at h'
  exact h'

private theorem pairedSurvivorsIdx_val {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) :
    pairedSurvivorsIdx G U (pairedSurvivorsVal_mem G U a) = a := by
  unfold pairedSurvivorsIdx pairedSurvivorsVal pairedSurvivorsEmb
  have : ((pairedSurvivors G U).orderIsoOfFin rfl).symm
      (((pairedSurvivors G U).orderIsoOfFin rfl) a) = a :=
    ((pairedSurvivors G U).orderIsoOfFin rfl).symm_apply_apply _
  -- ⟨pairedSurvivorsVal G U a, pairedSurvivorsVal_mem G U a⟩ = orderIsoOfFin a
  have heq : ((pairedSurvivors G U).orderIsoOfFin rfl) a =
      ⟨pairedSurvivorsVal G U a, pairedSurvivorsVal_mem G U a⟩ := by
    apply Subtype.ext
    simp [Finset.coe_orderIsoOfFin_apply, pairedSurvivorsVal, pairedSurvivorsEmb]
  rw [heq] at this
  exact this

/-- `pairedSurvivorsIdx` preserves `<`. -/
private theorem pairedSurvivorsIdx_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n)))
    {i j : Fin n} (hi : i ∈ pairedSurvivors G U) (hj : j ∈ pairedSurvivors G U)
    (hlt : i < j) :
    pairedSurvivorsIdx G U hi < pairedSurvivorsIdx G U hj := by
  -- Apply the order iso: it is order-preserving so `i < j` gives the indices as
  -- subtypes and then the strictMono of symm on the image gives `idx < idx`.
  have h1 : (⟨i, hi⟩ : { x // x ∈ pairedSurvivors G U }) <
      ⟨j, hj⟩ := hlt
  exact ((pairedSurvivors G U).orderIsoOfFin rfl).symm.strictMono h1

/-- `pairedSurvivorsIdx` preserves `≤`. -/
private theorem pairedSurvivorsIdx_le {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n)))
    {i j : Fin n} (hi : i ∈ pairedSurvivors G U) (hj : j ∈ pairedSurvivors G U)
    (hle : i ≤ j) :
    pairedSurvivorsIdx G U hi ≤ pairedSurvivorsIdx G U hj := by
  have h1 : (⟨i, hi⟩ : { x // x ∈ pairedSurvivors G U }) ≤
      ⟨j, hj⟩ := hle
  exact ((pairedSurvivors G U).orderIsoOfFin rfl).symm.monotone h1

/-- A paired-survivor index `i` satisfies `i.val + 1 < n`. -/
private theorem pairedSurvivors_succ_lt {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    i.val + 1 < n := by
  classical
  unfold pairedSurvivors at hi
  rw [Finset.mem_filter] at hi
  exact hi.2.1

/-- A paired-survivor index `i` has `inl i ∈ hhSurvivors G U`. -/
private theorem pairedSurvivors_inl_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U := by
  classical
  unfold pairedSurvivors at hi
  rw [Finset.mem_filter] at hi
  exact hi.2.2.1

/-- A paired-survivor index `i` has `inr i ∈ hhSurvivors G U`. -/
private theorem pairedSurvivors_inr_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hi : i ∈ pairedSurvivors G U) :
    (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U := by
  classical
  unfold pairedSurvivors at hi
  rw [Finset.mem_filter] at hi
  exact hi.2.2.2

/-- For `v ∈ hhSurvivors G U` with `v.val = Sum.inl i`, if `i ∉ pairedSurvivors G U`,
then `v.val ∈ lambdaSet G U`. -/
private theorem lambdaSet_mem_of_inl_not_paired {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ lambdaSet G U := by
  classical
  refine ⟨hmem, ?_⟩
  rintro (⟨j, hjmem, hj⟩ | ⟨j, hjmem, hj⟩)
  · -- Sum.inl j = Sum.inl i, so i = j, so j ∈ pairedSurvivors → contradiction.
    have hij : i = j := by
      have : Sum.inl (α := Fin n) (β := Fin n) j = Sum.inl i := hj
      exact (Sum.inl.inj this).symm
    subst hij
    exact hi hjmem
  · -- Sum.inr j = Sum.inl i: impossible.
    cases hj

/-- For `v ∈ hhSurvivors G U` with `v.val = Sum.inr i`, if `i ∉ pairedSurvivors G U`,
then `v.val ∈ lambdaSet G U`. -/
private theorem lambdaSet_mem_of_inr_not_paired {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) {i : Fin n}
    (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ lambdaSet G U := by
  classical
  refine ⟨hmem, ?_⟩
  rintro (⟨j, hjmem, hj⟩ | ⟨j, hjmem, hj⟩)
  · cases hj
  · have hij : i = j := by
      have : Sum.inr (α := Fin n) (β := Fin n) j = Sum.inr i := hj
      exact (Sum.inr.inj this).symm
    subst hij
    exact hi hjmem

/-- Image of an `Sum.inl i` survivor in the tensor product. -/
private noncomputable def L4ForwardInl {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (i : Fin n) (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) := by
  classical
  by_cases hi : i ∈ pairedSurvivors G U
  · -- paired: map to (mk X(inl a)) ⊗ 1
    exact ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
      (X (Sum.inl (pairedSurvivorsIdx G U hi)))) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1
  · -- isolated: map to 1 ⊗ X ⟨inl i, _⟩
    exact (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
      (X ⟨(Sum.inl i : BinomialEdgeVars (Fin n)),
        lambdaSet_mem_of_inl_not_paired G U hmem hi⟩ :
          MvPolynomial (lambdaSet G U) K)

/-- Image of an `Sum.inr i` survivor in the tensor product. -/
private noncomputable def L4ForwardInr {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (i : Fin n) (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) := by
  classical
  by_cases hi : i ∈ pairedSurvivors G U
  · exact ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
      (X (Sum.inr (pairedSurvivorsIdx G U hi)))) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1
  · exact (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
      (X ⟨(Sum.inr i : BinomialEdgeVars (Fin n)),
        lambdaSet_mem_of_inr_not_paired G U hmem hi⟩ :
          MvPolynomial (lambdaSet G U) K)

/-- Paired case of `L4ForwardInl`. -/
private theorem L4ForwardInl_of_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∈ pairedSurvivors G U) :
    L4ForwardInl (K := K) G U i hmem =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
        (X (Sum.inl (pairedSurvivorsIdx G U hi)))) :
          BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  unfold L4ForwardInl
  rw [dif_pos hi]

/-- Isolated case of `L4ForwardInl`. -/
private theorem L4ForwardInl_of_not_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    L4ForwardInl (K := K) G U i hmem =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X ⟨(Sum.inl i : BinomialEdgeVars (Fin n)),
          lambdaSet_mem_of_inl_not_paired G U hmem hi⟩ :
            MvPolynomial (lambdaSet G U) K) := by
  classical
  unfold L4ForwardInl
  rw [dif_neg hi]

/-- Paired case of `L4ForwardInr`. -/
private theorem L4ForwardInr_of_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∈ pairedSurvivors G U) :
    L4ForwardInr (K := K) G U i hmem =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
        (X (Sum.inr (pairedSurvivorsIdx G U hi)))) :
          BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  unfold L4ForwardInr
  rw [dif_pos hi]

/-- Isolated case of `L4ForwardInr`. -/
private theorem L4ForwardInr_of_not_paired {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    {i : Fin n} (hmem : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hi : i ∉ pairedSurvivors G U) :
    L4ForwardInr (K := K) G U i hmem =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X ⟨(Sum.inr i : BinomialEdgeVars (Fin n)),
          lambdaSet_mem_of_inr_not_paired G U hmem hi⟩ :
            MvPolynomial (lambdaSet G U) K) := by
  classical
  unfold L4ForwardInr
  rw [dif_neg hi]

/-- Step 4 forward on generators: send a survivor variable to its image in the
tensor product. -/
private noncomputable def L4ForwardGen {n : ℕ}
    {G : SimpleGraph (Fin n)} (_hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (_hU : hhIndep G U)
    (v : hhSurvivors G U) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) :=
  match hvc : (v.val : BinomialEdgeVars (Fin n)) with
  | Sum.inl i => L4ForwardInl (K := K) G U i (hvc ▸ v.property)
  | Sum.inr i => L4ForwardInr (K := K) G U i (hvc ▸ v.property)

/-- `L4ForwardGen` on an `Sum.inl` survivor. -/
private theorem L4ForwardGen_inl {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) {i : Fin n} (hvc : v.val = Sum.inl i) :
    L4ForwardGen (K := K) hHH U hU v =
      L4ForwardInl (K := K) G U i (hvc ▸ v.property) := by
  -- Use Subtype.ext_iff pattern to unfold v.
  obtain ⟨vv, hvv⟩ := v
  change vv = Sum.inl i at hvc
  subst hvc
  rfl

/-- `L4ForwardGen` on an `Sum.inr` survivor. -/
private theorem L4ForwardGen_inr {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) {i : Fin n} (hvc : v.val = Sum.inr i) :
    L4ForwardGen (K := K) hHH U hU v =
      L4ForwardInr (K := K) G U i (hvc ▸ v.property) := by
  obtain ⟨vv, hvv⟩ := v
  change vv = Sum.inr i at hvc
  subst hvc
  rfl

/-- The underlying polynomial algebra hom from `K[W]` extending `L4ForwardGen`. -/
private noncomputable def L4ForwardPoly {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    polyRestrict (K := K) (hhSurvivors G U) →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
  MvPolynomial.aeval (L4ForwardGen (K := K) hHH U hU)

@[simp]
private theorem L4ForwardPoly_X {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) :
    L4ForwardPoly (K := K) hHH U hU (X v) = L4ForwardGen (K := K) hHH U hU v := by
  unfold L4ForwardPoly
  simp [MvPolynomial.aeval_X]

/-- Each restricted edge generator `X p * X q` maps to zero under the polynomial
forward map. This is the key well-definedness fact for descending through
the restricted edge ideal. -/
private theorem L4ForwardPoly_vanishes_on_gens {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    {p q : hhSurvivors G U}
    (hedge : (p.val, q.val) ∈ hhEdgeSet G) :
    L4ForwardPoly (K := K) hHH U hU (X p * X q) = 0 := by
  classical
  -- Unpack the edge.
  obtain ⟨i, j, hj_succ, hadjG, hle_ij, heq⟩ := hedge
  have hpl : p.val = Sum.inl i := by
    have h := (Prod.mk.injEq _ _ _ _).mp heq
    exact h.1
  have hqr : q.val = Sum.inr j := by
    have h := (Prod.mk.injEq _ _ _ _).mp heq
    exact h.2
  -- Both `p` and `q` belong to `hhSurvivors G U`.
  have hp_mem : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    hpl ▸ p.property
  have hq_mem : (Sum.inr j : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    hqr ▸ q.property
  -- Rewrite X p * X q to X (inl i) via Subtype ext.
  rw [map_mul, L4ForwardPoly_X, L4ForwardPoly_X,
    L4ForwardGen_inl (K := K) hHH hU p hpl,
    L4ForwardGen_inr (K := K) hHH hU q hqr]
  -- Case split on whether i and j are in pairedSurvivors.
  by_cases hi : i ∈ pairedSurvivors G U
  · by_cases hj : j ∈ pairedSurvivors G U
    · -- Both paired. Produce (mk X(inl a)) ⊗ 1 * (mk X(inr b)) ⊗ 1
      -- = (mk (X(inl a) * X(inr b))) ⊗ 1, and the product is in reducedHHIdeal.
      rw [L4ForwardInl_of_paired (K := K) G U hp_mem hi,
        L4ForwardInr_of_paired (K := K) G U hq_mem hj]
      -- Indices:
      set a : Fin (pairedCount G U) := pairedSurvivorsIdx G U hi with ha_def
      set b : Fin (pairedCount G U) := pairedSurvivorsIdx G U hj with hb_def
      -- a ≤ b from i ≤ j.
      have hab : a ≤ b := pairedSurvivorsIdx_le G U hi hj hle_ij
      -- The G' edge: need G'.Adj a.castSucc ⟨b.val+1, _⟩.
      -- b+1 < r+1 since b.val < r.
      have hbsucc : b.val + 1 < pairedCount G U + 1 := by
        have : b.val < pairedCount G U := b.isLt
        omega
      -- The underlying indices satisfy pairedSurvivorsVal G U a = i,
      -- pairedSurvivorsVal G U b = j.
      have ha_val : pairedSurvivorsVal G U a = i := pairedSurvivorsVal_idx G U hi
      have hb_val : pairedSurvivorsVal G U b = j := pairedSurvivorsVal_idx G U hj
      -- Rewrite hadjG.
      have hc_succ : (pairedSurvivorsVal G U b).val + 1 < n := by
        rw [hb_val]; exact hj_succ
      have hadjG' : G.Adj (pairedSurvivorsVal G U a)
          ⟨(pairedSurvivorsVal G U b).val + 1, hc_succ⟩ := by
        rw [ha_val]
        have : (⟨(pairedSurvivorsVal G U b).val + 1, hc_succ⟩ : Fin n) =
            ⟨j.val + 1, hj_succ⟩ := by apply Fin.ext; simp [hb_val]
        rw [this]; exact hadjG
      -- G'.Adj a.castSucc ⟨b.val+1, hbsucc⟩.
      have hadjGp : (smallerHHGraph G U).Adj a.castSucc ⟨b.val + 1, hbsucc⟩ := by
        rw [smallerHHGraph, SimpleGraph.fromRel_adj]
        refine ⟨?_, Or.inl ⟨a, b, hab, rfl, ?_, hc_succ, hadjG'⟩⟩
        · intro heq
          have : a.val = b.val + 1 := by
            have := congrArg Fin.val heq
            simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
            exact this
          have hab_val : a.val ≤ b.val := hab
          omega
        · simp
      -- Thus X(inl a) * X(inr b) ∈ reducedHHIdeal (smallerHHGraph G U).
      have hmem_red : (X (Sum.inl a) * X (Sum.inr b) :
          MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K) ∈
          BEI.reducedHHIdeal (K := K) (smallerHHGraph G U) :=
        BEI.X_inl_mul_X_inr_mem_reducedHHIdeal (K := K) hab hbsucc hadjGp
      -- Now compute the product in the tensor.
      -- (mk X(inl a) ⊗ 1) * (mk X(inr b) ⊗ 1) = mk (X(inl a) * X(inr b)) ⊗ 1 = 0 ⊗ 1 = 0.
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul,
        (Ideal.Quotient.eq_zero_iff_mem).mpr hmem_red, TensorProduct.zero_tmul]
    · -- i ∈ paired, j ∉ paired. Contradiction via L3 lemmas.
      -- Since j ∈ hhSurvivors via hq_mem : Sum.inr j ∈ hhSurvivors, and j ∉ paired,
      -- one of j+1 ≥ n, Sum.inl j ∉ hhSurvivors, Sum.inr j ∉ hhSurvivors.
      -- Since Sum.inr j ∈ hhSurvivors, and j+1 < n, we have Sum.inl j ∉ hhSurvivors.
      have hj_not_paired : ¬((j.val + 1 < n ∧
          (Sum.inl j : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U ∧
          (Sum.inr j : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)) := by
        intro hh
        apply hj
        unfold pairedSurvivors
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hh⟩
      -- Derive Sum.inl j ∉ hhSurvivors.
      have hxj_not : (Sum.inl j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
        intro hxj
        exact hj_not_paired ⟨hj_succ, hxj, hq_mem⟩
      -- Apply hhSurvivor_y_isolated: Sum.inl j isolates from neighbours.
      -- The neighbour is Sum.inr i with edge (inl i, inr j)? No — the statement:
      -- hhSurvivor_y_isolated says Sum.inr j ∈ hhSurvivors, Sum.inl j ∉, then
      -- every edge (Sum.inl k, Sum.inr j) has Sum.inl k ∉ hhSurvivors.
      -- Apply with k = i: we know hadj : G.Adj i ⟨j+1⟩ so (inl i, inr j) ∈ hhEdgeSet.
      have hedge_ij : (Sum.inl i, Sum.inr j) ∈ hhEdgeSet G :=
        ⟨i, j, hj_succ, hadjG, hle_ij, rfl⟩
      have hxi_not : (Sum.inl i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U :=
        hhSurvivor_y_isolated hHH hq_mem hxj_not hedge_ij
      exact absurd hp_mem hxi_not
  · -- i ∉ paired.
    -- By similar reasoning, Sum.inl i ∈ hhSurvivors (via hp_mem), so either
    -- i+1 ≥ n OR Sum.inr i ∉ hhSurvivors. First: i+1 < n since i ≤ j < n
    -- and j+1 < n, so i < j+1 ≤ n-1+1 = n. Wait, we need i.val + 1 < n.
    -- Actually from hle_ij : i ≤ j and hj_succ : j.val + 1 < n, we get
    -- i.val ≤ j.val, hence i.val + 1 ≤ j.val + 1 < n.
    have hi_succ : i.val + 1 < n := by
      have : i.val ≤ j.val := hle_ij
      omega
    have hi_not_paired : ¬((i.val + 1 < n ∧
        (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U ∧
        (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)) := by
      intro hh
      apply hi
      unfold pairedSurvivors
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hh⟩
    have hyi_not : (Sum.inr i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
      intro hyi
      exact hi_not_paired ⟨hi_succ, hp_mem, hyi⟩
    -- Apply hhSurvivor_x_isolated: Sum.inl i ∈ hhSurvivors, Sum.inr i ∉ hhSurvivors,
    -- then every edge (Sum.inl i, Sum.inr k) has Sum.inr k ∉ hhSurvivors.
    have hedge_ij : (Sum.inl i, Sum.inr j) ∈ hhEdgeSet G :=
      ⟨i, j, hj_succ, hadjG, hle_ij, rfl⟩
    have hyj_not : (Sum.inr j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U :=
      hhSurvivor_x_isolated hHH hp_mem hyi_not hedge_ij
    exact absurd hq_mem hyj_not

/-- The forward map vanishes on the entire restricted edge ideal. -/
private theorem L4ForwardPoly_vanishes {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (x : polyRestrict (K := K) (hhSurvivors G U)) :
    x ∈ restrictedEdgeIdeal (K := K) G (hhSurvivors G U) →
      L4ForwardPoly (K := K) hHH U hU x = 0 := by
  intro hx
  unfold restrictedEdgeIdeal MvPolynomial.variablePairIdeal at hx
  refine Submodule.span_induction (p := fun y _ =>
    L4ForwardPoly (K := K) hHH U hU y = 0) ?_ ?_ ?_ ?_ hx
  · -- Generators: y = X p * X q for an edge.
    rintro y ⟨p, q, hpq, rfl⟩
    -- Translate hpq : (p, q) ∈ restrictedEdgesSubtype, i.e. (p.val, q.val) ∈ hhEdgeSet G.
    exact L4ForwardPoly_vanishes_on_gens hHH hU hpq
  · simp
  · intros _ _ _ _ hx hy; simp [hx, hy]
  · intros r x _ hx; simp [hx]

/-- Step 4 forward: the descent to the quotient. -/
private noncomputable def L4Forward {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    restrictedHHRing (K := K) G (hhSurvivors G U) →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
  Ideal.Quotient.liftₐ (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
    (L4ForwardPoly (K := K) hHH U hU)
    (L4ForwardPoly_vanishes (K := K) hHH hU)

/-! #### Step 5 — backward map -/

/-- Backward on a reduced-HH generator `Sum.inl a` or `Sum.inr a`:
`x'_a ↦ mk X ⟨Sum.inl c_a, _⟩`, `y'_a ↦ mk X ⟨Sum.inr c_a, _⟩`. -/
private noncomputable def L4BackwardRedGen {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin (pairedCount G U))) :
    restrictedHHRing (K := K) G (hhSurvivors G U) :=
  match v with
  | Sum.inl a =>
      Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
        (X ⟨(Sum.inl (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)),
          pairedSurvivors_inl_mem G U (pairedSurvivorsVal_mem G U a)⟩)
  | Sum.inr a =>
      Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
        (X ⟨(Sum.inr (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)),
          pairedSurvivors_inr_mem G U (pairedSurvivorsVal_mem G U a)⟩)

/-- The polynomial hom extending `L4BackwardRedGen`. -/
private noncomputable def L4BackwardRedPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  MvPolynomial.aeval (L4BackwardRedGen (K := K) G U)

@[simp]
private theorem L4BackwardRedPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin (pairedCount G U))) :
    L4BackwardRedPoly (K := K) G U (X v) = L4BackwardRedGen (K := K) G U v := by
  unfold L4BackwardRedPoly
  simp [MvPolynomial.aeval_X]

/-- Unpacking of `smallerHHGraph` edges (forward direction only, with `a ≤ b` as a
required hypothesis): given the adjacency and the ordering constraint,
extract the underlying `G`-edge on paired-survivor indices. -/
private theorem smallerHHGraph_adj_imp {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Set (BinomialEdgeVars (Fin n))}
    {a : Fin (pairedCount G U)} {b : Fin (pairedCount G U)}
    (hab : a ≤ b) (hb : b.val + 1 < pairedCount G U + 1)
    (hadj : (smallerHHGraph G U).Adj a.castSucc ⟨b.val + 1, hb⟩) :
    ∃ hc : (pairedSurvivorsVal G U b).val + 1 < n,
      G.Adj (pairedSurvivorsVal G U a)
        ⟨(pairedSurvivorsVal G U b).val + 1, hc⟩ := by
  rw [smallerHHGraph, SimpleGraph.fromRel_adj] at hadj
  obtain ⟨_, h⟩ := hadj
  rcases h with h | h
  · obtain ⟨a', b', _, hu_eq, hv_eq, hc, hadj'⟩ := h
    have ha_eq : a = a' := by
      apply Fin.ext
      have := congrArg Fin.val hu_eq
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
      omega
    have hb_eq : b = b' := by
      apply Fin.ext
      have h1 : (⟨b.val + 1, hb⟩ : Fin (pairedCount G U + 1)).val = b'.val + 1 := hv_eq
      simp at h1
      omega
    subst ha_eq; subst hb_eq
    exact ⟨hc, hadj'⟩
  · -- reverse branch: impossible given a ≤ b.
    exfalso
    obtain ⟨a', b', hab', hu_eq, hv_eq, _, _⟩ := h
    -- u = ⟨b.val+1, hb⟩ = a'.castSucc, so a'.val = b.val+1
    -- v = a.castSucc, v.val = b'.val+1, so a.val = b'.val + 1
    have ha' : a'.val = b.val + 1 := by
      have := congrArg Fin.val hu_eq
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
      omega
    have hb' : a.val = b'.val + 1 := by
      have h1 : (a.castSucc : Fin (pairedCount G U + 1)).val = b'.val + 1 := hv_eq
      simp at h1
      exact h1
    -- a' ≤ b' gives b.val + 1 ≤ b'.val, and a.val = b'.val + 1, so a.val ≥ b.val + 2.
    have h1 : a'.val ≤ b'.val := hab'
    have h2 : a.val ≤ b.val := hab
    omega

/-- The backward reduced-HH polynomial hom vanishes on reducedHH generators. -/
private theorem L4BackwardRedPoly_vanishes_on_gens {n : ℕ}
    {G : SimpleGraph (Fin n)} (U : Set (BinomialEdgeVars (Fin n)))
    {a b : BinomialEdgeVars (Fin (pairedCount G U))}
    (hab : (a, b) ∈ BEI.reducedHHEdgeSet (smallerHHGraph G U)) :
    L4BackwardRedPoly (K := K) G U (X a * X b) = 0 := by
  obtain ⟨a', b', hbsucc, hadjGp, hle, heq⟩ := hab
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _|>.mp heq
  -- Now a = Sum.inl a', b = Sum.inr b', with G'.Adj a'.castSucc ⟨b'.val+1, hbsucc⟩ and a' ≤ b'.
  obtain ⟨hc, hadjG⟩ := smallerHHGraph_adj_imp hle hbsucc hadjGp
  -- Use pairedSurvivorsVal_spec to get the underlying indices and the edge membership.
  set ia : Fin n := pairedSurvivorsVal G U a' with hia_def
  set ib : Fin n := pairedSurvivorsVal G U b' with hib_def
  -- Under the backward map, X(inl a') ↦ mk X ⟨Sum.inl ia, _⟩
  -- and X(inr b') ↦ mk X ⟨Sum.inr ib, _⟩.
  -- Their product in restrictedHHRing is mk (X ⟨inl ia, _⟩ * X ⟨inr ib, _⟩), which is in
  -- restrictedEdgeIdeal because (inl ia, inr ib) ∈ hhEdgeSet G.
  rw [map_mul]
  rw [L4BackwardRedPoly_X, L4BackwardRedPoly_X]
  simp only [L4BackwardRedGen]
  -- Get the indexed memberships.
  have hia_mem : (Sum.inl ia : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    pairedSurvivors_inl_mem G U (pairedSurvivorsVal_mem G U a')
  have hib_mem : (Sum.inr ib : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U :=
    pairedSurvivors_inr_mem G U (pairedSurvivorsVal_mem G U b')
  -- The strict monotonicity gives c_a' ≤ c_b' from a' ≤ b'.
  have hia_le_ib : ia ≤ ib := (pairedSurvivorsEmb G U).monotone hle
  -- The edge in hhEdgeSet G.
  have hedge : (Sum.inl ia, Sum.inr ib) ∈ hhEdgeSet G :=
    ⟨ia, ib, hc, hadjG, hia_le_ib, rfl⟩
  -- The edge in restrictedEdgesSubtype.
  have hedge_sub : (⟨(Sum.inl ia : BinomialEdgeVars (Fin n)), hia_mem⟩,
      ⟨(Sum.inr ib : BinomialEdgeVars (Fin n)), hib_mem⟩) ∈
      restrictedEdgesSubtype G (hhSurvivors G U) := hedge
  -- The product is in restrictedEdgeIdeal.
  have hmem_ideal : (X ⟨(Sum.inl ia : BinomialEdgeVars (Fin n)), hia_mem⟩ *
      X ⟨(Sum.inr ib : BinomialEdgeVars (Fin n)), hib_mem⟩ :
      polyRestrict (K := K) (hhSurvivors G U)) ∈
      restrictedEdgeIdeal (K := K) G (hhSurvivors G U) :=
    Ideal.subset_span ⟨_, _, hedge_sub, rfl⟩
  rw [← map_mul, (Ideal.Quotient.eq_zero_iff_mem).mpr hmem_ideal]

/-- Step 5 backward reduced: `A^red_{G'} →ₐ[K] K[W]/I(Γ_G|_W)`. -/
private noncomputable def L4BackwardRed {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    BEI.reducedHHRing (K := K) (smallerHHGraph G U) →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  Ideal.Quotient.liftₐ (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
    (L4BackwardRedPoly (K := K) G U) (by
      intro x hx
      unfold BEI.reducedHHIdeal MvPolynomial.variablePairIdeal at hx
      refine Submodule.span_induction (p := fun y _ =>
        L4BackwardRedPoly (K := K) G U y = 0) ?_ ?_ ?_ ?_ hx
      · rintro y ⟨a, b, hab, rfl⟩
        exact L4BackwardRedPoly_vanishes_on_gens U hab
      · simp
      · intros _ _ _ _ hx hy; simp [hx, hy]
      · intros r x _ hx; simp [hx])

/-- Step 5 backward on `K[Λ]`: `X ⟨λ, _⟩ ↦ mk (X ⟨λ, _⟩)`. -/
private noncomputable def L4BackwardPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    MvPolynomial (lambdaSet G U) K →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  MvPolynomial.aeval (fun v =>
    Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
      (X ⟨v.val, v.property.1⟩))

@[simp]
private theorem L4BackwardPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (v : lambdaSet G U) :
    L4BackwardPoly (K := K) G U (X v) =
      Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U))
        (X ⟨v.val, v.property.1⟩) := by
  unfold L4BackwardPoly
  simp [MvPolynomial.aeval_X]

/-- Step 5 backward: full backward map via `Algebra.TensorProduct.lift`. -/
private noncomputable def L4Backward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (MvPolynomial (lambdaSet G U) K) →ₐ[K]
      restrictedHHRing (K := K) G (hhSurvivors G U) :=
  Algebra.TensorProduct.lift (L4BackwardRed (K := K) G U)
    (L4BackwardPoly (K := K) G U) (fun _ _ => mul_comm _ _)

/-! #### Step 6 — bijectivity and assembly -/

/-- The quotient map `aeval (L4ForwardGen) = (Ideal.Quotient.mk ∘ aeval) ...`.
-- Forward on `mk (X v)` equals `L4ForwardGen v`. -/
private theorem L4Forward_mk_X {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) :
    L4Forward (K := K) hHH U hU
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U)) (X v)) =
    L4ForwardGen (K := K) hHH U hU v := by
  unfold L4Forward
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact L4ForwardPoly_X (K := K) hHH hU v

/-- Composition Backward ∘ Forward = id, generator-level (on `mk (X v)`). -/
private theorem L4Backward_Forward_mk_X {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : hhSurvivors G U) :
    (L4Backward (K := K) G U) (L4Forward (K := K) hHH U hU
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U)) (X v))) =
    Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G (hhSurvivors G U)) (X v) := by
  classical
  rw [L4Forward_mk_X]
  -- Case on v.val using match.
  obtain ⟨vv, hvv⟩ := v
  match hvc : vv, hvv with
  | Sum.inl i, hvv =>
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨Sum.inl i, hvv⟩ rfl]
    by_cases hi : i ∈ pairedSurvivors G U
    · rw [L4ForwardInl_of_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      unfold L4BackwardRed
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      change (L4BackwardRedPoly (K := K) G U) (X _) = _
      rw [L4BackwardRedPoly_X]
      simp only [L4BackwardRedGen]
      have h := pairedSurvivorsVal_idx G U hi
      -- Rewrite the target using the identity.
      congr 2
      apply Subtype.ext
      simp [h]
    · rw [L4ForwardInl_of_not_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [L4BackwardPoly_X]
  | Sum.inr i, hvv =>
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨Sum.inr i, hvv⟩ rfl]
    by_cases hi : i ∈ pairedSurvivors G U
    · rw [L4ForwardInr_of_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      unfold L4BackwardRed
      rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
      change (L4BackwardRedPoly (K := K) G U) (X _) = _
      rw [L4BackwardRedPoly_X]
      simp only [L4BackwardRedGen]
      have h := pairedSurvivorsVal_idx G U hi
      congr 2
      apply Subtype.ext
      simp [h]
    · rw [L4ForwardInr_of_not_paired (K := K) G U hvv hi]
      unfold L4Backward
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rw [L4BackwardPoly_X]

/-- Composition Backward ∘ Forward = id, at the algHom level. -/
private theorem L4Backward_Forward {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    (L4Backward (K := K) G U).comp (L4Forward (K := K) hHH U hU) =
      AlgHom.id K (restrictedHHRing (K := K) G (hhSurvivors G U)) := by
  -- Use quotient-algHom extension: suffices to check on mk (X v) for v : hhSurvivors G U.
  apply Ideal.Quotient.algHom_ext
  -- Now we have: f.comp (Quotient.mkₐ) = g.comp (Quotient.mkₐ), on polynomials.
  apply MvPolynomial.algHom_ext
  intro v
  change (L4Backward (K := K) G U) (L4Forward (K := K) hHH U hU
    (Ideal.Quotient.mk _ (X v))) = _
  rw [L4Backward_Forward_mk_X]
  rfl

/-- Composition Forward ∘ Backward on pure tensors, left case `mk (X v) ⊗ 1`. -/
private theorem L4Forward_Backward_inl_tmul {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : BinomialEdgeVars (Fin (pairedCount G U))) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
          (X v) : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) (X v) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  -- Simplify L4Backward on the pure tensor.
  have h_inc : (L4Backward (K := K) G U)
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) (X v) :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1) =
      (L4BackwardRed (K := K) G U)
        (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) (X v)) := by
    unfold L4Backward
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  rw [h_inc]
  unfold L4BackwardRed
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change (L4Forward (K := K) hHH U hU)
    ((L4BackwardRedPoly (K := K) G U) (X v)) = _
  rw [L4BackwardRedPoly_X]
  -- L4BackwardRedGen v: case on v.
  rcases v with a | a
  · simp only [L4BackwardRedGen]
    rw [L4Forward_mk_X]
    have hi : pairedSurvivorsVal G U a ∈ pairedSurvivors G U :=
      pairedSurvivorsVal_mem G U a
    have hmem : (Sum.inl (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
        hhSurvivors G U := pairedSurvivors_inl_mem G U hi
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨_, hmem⟩ rfl]
    rw [L4ForwardInl_of_paired (K := K) G U hmem hi]
    rw [pairedSurvivorsIdx_val]
  · simp only [L4BackwardRedGen]
    rw [L4Forward_mk_X]
    have hi : pairedSurvivorsVal G U a ∈ pairedSurvivors G U :=
      pairedSurvivorsVal_mem G U a
    have hmem : (Sum.inr (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
        hhSurvivors G U := pairedSurvivors_inr_mem G U hi
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨_, hmem⟩ rfl]
    rw [L4ForwardInr_of_paired (K := K) G U hmem hi]
    rw [pairedSurvivorsIdx_val]

/-- Composition Forward ∘ Backward on pure tensors, right case `1 ⊗ X v`. -/
private theorem L4Forward_Backward_inr_tmul {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (v : lambdaSet G U) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
          (X v : MvPolynomial (lambdaSet G U) K))) =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X v : MvPolynomial (lambdaSet G U) K) := by
  classical
  have h_inc : (L4Backward (K := K) G U)
      ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K]
        (X v : MvPolynomial (lambdaSet G U) K)) =
      (L4BackwardPoly (K := K) G U) (X v) := by
    unfold L4Backward
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  rw [h_inc, L4BackwardPoly_X, L4Forward_mk_X]
  -- Case on v.val.
  have hvprop : v.val ∈ lambdaSet G U := v.property
  obtain ⟨vv, hvv⟩ := v
  match hvc : vv, hvv with
  | Sum.inl i, hvv =>
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨Sum.inl i, hvv.1⟩ rfl]
    have hi : i ∉ pairedSurvivors G U := by
      intro hi
      apply hvv.2
      exact Or.inl ⟨i, hi, rfl⟩
    rw [L4ForwardInl_of_not_paired (K := K) G U hvv.1 hi]
  | Sum.inr i, hvv =>
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨Sum.inr i, hvv.1⟩ rfl]
    have hi : i ∉ pairedSurvivors G U := by
      intro hi
      apply hvv.2
      exact Or.inr ⟨i, hi, rfl⟩
    rw [L4ForwardInr_of_not_paired (K := K) G U hvv.1 hi]

/-- Forward ∘ Backward on `a ⊗ 1` (left factor). Reduce to generators via an algHom
equality on `MvPolynomial`. -/
private theorem L4Forward_Backward_left {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (p : MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) p :
          BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)) p :
        BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1 := by
  classical
  -- Think of both sides as K-algebra homs from `MvPoly` to the tensor product.
  -- φ_L : p ↦ forward (backward (mk p ⊗ 1))
  -- φ_R : p ↦ mk p ⊗ 1
  -- Both are K-algebra homs; they agree on X v (by L4Forward_Backward_inl_tmul),
  -- hence on all polynomials.
  set φL : MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    ((L4Forward (K := K) hHH U hU).comp (L4Backward (K := K) G U)).comp
      (((Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (B := MvPolynomial (lambdaSet G U) K))).comp
        (Ideal.Quotient.mkₐ K (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))))
  set φR : MvPolynomial (BinomialEdgeVars (Fin (pairedCount G U))) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    ((Algebra.TensorProduct.includeLeft
        (R := K) (S := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (B := MvPolynomial (lambdaSet G U) K))).comp
      (Ideal.Quotient.mkₐ K (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U)))
  have hφeq : φL = φR := by
    apply MvPolynomial.algHom_ext
    intro v
    -- Unfold both sides.
    change (L4Forward (K := K) hHH U hU) ((L4Backward (K := K) G U)
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
        (X v) : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1)) =
        (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) (smallerHHGraph G U))
          (X v) : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] 1
    exact L4Forward_Backward_inl_tmul hHH hU v
  have := congrArg (fun φ => φ p) hφeq
  exact this

/-- Forward ∘ Backward on `1 ⊗ b` (right factor). -/
private theorem L4Forward_Backward_right {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (b : MvPolynomial (lambdaSet G U) K) :
    (L4Forward (K := K) hHH U hU)
      ((L4Backward (K := K) G U)
        ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] b)) =
      (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] b := by
  classical
  set φL : MvPolynomial (lambdaSet G U) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    ((L4Forward (K := K) hHH U hU).comp (L4Backward (K := K) G U)).comp
      (Algebra.TensorProduct.includeRight
        (R := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (B := MvPolynomial (lambdaSet G U) K))
  set φR : MvPolynomial (lambdaSet G U) K →ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
    Algebra.TensorProduct.includeRight
      (R := K) (A := BEI.reducedHHRing (K := K) (smallerHHGraph G U))
      (B := MvPolynomial (lambdaSet G U) K)
  have hφeq : φL = φR := by
    apply MvPolynomial.algHom_ext
    intro v
    change (L4Forward (K := K) hHH U hU) ((L4Backward (K := K) G U)
      ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] X v)) =
        (1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] X v
    exact L4Forward_Backward_inr_tmul hHH hU v
  have := congrArg (fun φ => φ b) hφeq
  exact this

/-- Forward ∘ Backward on pure tensors. -/
private theorem L4Forward_Backward_tmul {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))} (hU : hhIndep G U)
    (a : BEI.reducedHHRing (K := K) (smallerHHGraph G U))
    (b : MvPolynomial (lambdaSet G U) K) :
    (L4Forward (K := K) hHH U hU) ((L4Backward (K := K) G U) (a ⊗ₜ[K] b)) =
      a ⊗ₜ[K] b := by
  classical
  -- Factor a ⊗ b = (a ⊗ 1) * (1 ⊗ b).
  have hsplit : a ⊗ₜ[K] b =
      ((a ⊗ₜ[K] (1 : MvPolynomial (lambdaSet G U) K)) *
        ((1 : BEI.reducedHHRing (K := K) (smallerHHGraph G U)) ⊗ₜ[K] b)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hsplit, map_mul, map_mul]
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [L4Forward_Backward_left hHH hU p, L4Forward_Backward_right hHH hU b]

/-- Composition Forward ∘ Backward = id, at the algHom level. -/
private theorem L4Forward_Backward {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    (L4Forward (K := K) hHH U hU).comp (L4Backward (K := K) G U) =
      AlgHom.id K (TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K)) := by
  classical
  apply Algebra.TensorProduct.ext'
  intro a b
  exact L4Forward_Backward_tmul hHH hU a b

/-- **Step 6: the L4 isomorphism.** -/
private noncomputable def L4Iso {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) (hU : hhIndep G U) :
    restrictedHHRing (K := K) G (hhSurvivors G U) ≃ₐ[K]
      TensorProduct K (BEI.reducedHHRing (K := K) (smallerHHGraph G U))
        (MvPolynomial (lambdaSet G U) K) :=
  AlgEquiv.ofAlgHom (L4Forward (K := K) hHH U hU) (L4Backward (K := K) G U)
    (L4Forward_Backward (K := K) hHH U hU) (L4Backward_Forward (K := K) hHH U hU)

/-! #### Step L1: monomial-localisation ring iso

For a Finset `U` of variables, independent in `Γ_G`, set
`s_U := ∏ u ∈ U, X u ∈ MvPolynomial σ K` and `W := σ \ (U ∪ N(U))`
(= `hhSurvivors G ↑U`). The L1 iso is a K-algebra isomorphism

  `R[s_U⁻¹] ≃ₐ[K] (restrictedHHRing G W) ⊗[K] Localization.Away s_U^U`

where `s_U^U` is the product of the variables `X ⟨u, _⟩` inside
`MvPolynomial {v // v ∈ U} K`, and `R := MvPolynomial σ K ⧸ I`
with `I = bipartiteEdgeMonomialIdeal G`. On generators:

* `mkI (X v) ↦ (mk X ⟨v, _⟩) ⊗ 1`          for `v ∈ W`;
* `mkI (X v) ↦ 0`                          for `v ∈ N(U)`;
* `mkI (X v) ↦ 1 ⊗ algebraMap (X ⟨v, _⟩)`  for `v ∈ U`.
-/

/-- The unit-variable product `s_U := ∏_{u ∈ U} X u` inside `MvPolynomial σ K`. -/
private noncomputable def hhUnitProduct {n : ℕ}
    (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K :=
  ∏ u ∈ U, X (R := K) u

/-- The product of U-variables viewed in the subtype-indexed polynomial ring
`MvPolynomial {v // v ∈ (U : Set _)} K`. -/
private noncomputable def hhUnitProductSub {n : ℕ}
    (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K :=
  ∏ u ∈ U.attach, X (R := K) ⟨u.val, by exact_mod_cast u.property⟩

/-- The target of the L1 forward hom. -/
private abbrev L1Target {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (BinomialEdgeVars (Fin n))) : Type _ :=
  TensorProduct K
    (restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
    (Localization.Away (hhUnitProductSub (K := K) U))

/-- Forward generator: send `v : BinomialEdgeVars (Fin n)` to its image in the
target, with a three-way case split on `W` / `U` / `N(U)` (other). The `N(U)`
case is not explicitly stated; we use the default value `0` when neither
`v ∈ W` nor `v ∈ U`, which is the correct image for `v ∈ N(U)`. -/
private noncomputable def L1ForwardGen {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin n)) : L1Target (K := K) G U := by
  classical
  by_cases hW : v ∈ hhSurvivors G (U : Set _)
  · exact ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
      (hhSurvivors G (U : Set _))) (X ⟨v, hW⟩) :
        restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1)
  · by_cases hU : v ∈ U
    · exact (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X (R := K) ⟨v, by exact_mod_cast hU⟩))
    · exact 0

/-- `L1ForwardGen` on a survivor (W) variable. -/
private theorem L1ForwardGen_of_W {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {v : BinomialEdgeVars (Fin n)}
    (hW : v ∈ hhSurvivors G (U : Set _)) :
    L1ForwardGen (K := K) G U v =
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨v, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1) := by
  classical
  unfold L1ForwardGen
  rw [dif_pos hW]

/-- `L1ForwardGen` on a unit (U) variable (which cannot simultaneously be in W). -/
private theorem L1ForwardGen_of_U {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hU : v ∈ U) :
    L1ForwardGen (K := K) G U v =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X (R := K) ⟨v, by exact_mod_cast hU⟩)) := by
  classical
  unfold L1ForwardGen
  rw [dif_neg hnW, dif_pos hU]

/-- `L1ForwardGen` on a neighborhood (N(U)) variable, i.e. neither in `W` nor in `U`. -/
private theorem L1ForwardGen_of_N {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hnU : v ∉ U) :
    L1ForwardGen (K := K) G U v = 0 := by
  classical
  unfold L1ForwardGen
  rw [dif_neg hnW, dif_neg hnU]

/-- The polynomial-level L1 forward map. -/
private noncomputable def L1ForwardPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial (BinomialEdgeVars (Fin n)) K →ₐ[K] L1Target (K := K) G U :=
  MvPolynomial.aeval (L1ForwardGen (K := K) G U)

@[simp]
private theorem L1ForwardPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : BinomialEdgeVars (Fin n)) :
    L1ForwardPoly (K := K) G U (X v) = L1ForwardGen (K := K) G U v := by
  unfold L1ForwardPoly
  simp [MvPolynomial.aeval_X]

/-! ##### Well-definedness: `L1ForwardPoly` kills the bipartite edge ideal -/

/-- An HH edge `(p, q) = (Sum.inl i, Sum.inr j)` with `p, q` both in `W`:
then `X⟨p⟩ * X⟨q⟩` is a restricted-edge generator, hence killed in
`restrictedHHRing G W`. -/
private theorem L1Forward_vanishes_on_gen_W_W {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    {p q : BinomialEdgeVars (Fin n)}
    (hedge : (p, q) ∈ hhEdgeSet G)
    (hpW : p ∈ hhSurvivors G (U : Set _))
    (hqW : q ∈ hhSurvivors G (U : Set _)) :
    L1ForwardPoly (K := K) G U (X p * X q) = 0 := by
  classical
  rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X,
    L1ForwardGen_of_W hpW, L1ForwardGen_of_W hqW]
  -- (mk X⟨p⟩ ⊗ 1) * (mk X⟨q⟩ ⊗ 1) = (mk (X⟨p⟩ * X⟨q⟩)) ⊗ 1 = 0 ⊗ 1 = 0.
  have hedge_sub : ((⟨p, hpW⟩ : (hhSurvivors G (U : Set _))),
      (⟨q, hqW⟩ : (hhSurvivors G (U : Set _)))) ∈
      restrictedEdgesSubtype G (hhSurvivors G (U : Set _)) := hedge
  have hmem_ideal : (X ⟨p, hpW⟩ * X ⟨q, hqW⟩ :
      polyRestrict (K := K) (hhSurvivors G (U : Set _))) ∈
      restrictedEdgeIdeal (K := K) G (hhSurvivors G (U : Set _)) :=
    Ideal.subset_span ⟨_, _, hedge_sub, rfl⟩
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul,
    (Ideal.Quotient.eq_zero_iff_mem).mpr hmem_ideal, TensorProduct.zero_tmul]

/-- The forward hom kills the HH edge generator `X p * X q`. -/
private theorem L1Forward_vanishes_on_gens {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _))
    {p q : BinomialEdgeVars (Fin n)}
    (hedge : (p, q) ∈ hhEdgeSet G) :
    L1ForwardPoly (K := K) G U (X p * X q) = 0 := by
  classical
  -- Four-way case on whether p and q are in W.
  by_cases hpW : p ∈ hhSurvivors G (U : Set _)
  · by_cases hqW : q ∈ hhSurvivors G (U : Set _)
    · -- p, q both in W.
      exact L1Forward_vanishes_on_gen_W_W hedge hpW hqW
    · -- p ∈ W, q ∉ W. Is q ∈ U or q ∈ N(U)?
      rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X, L1ForwardGen_of_W hpW]
      by_cases hqU : q ∈ U
      · -- q ∈ U, then p (as other endpoint) ∈ N(U); but p ∈ W — contradiction.
        exfalso
        apply hpW
        -- p ∈ U ∪ hhNbhd G U because (p, q) ∈ hhEdgeSet and q ∈ U.
        refine Or.inr ⟨q, (by exact_mod_cast hqU : q ∈ (U : Set _)),
          Or.inr hedge⟩
      · rw [L1ForwardGen_of_N (show q ∉ hhSurvivors G (U : Set _) from hqW) hqU,
          mul_zero]
  · by_cases hqW : q ∈ hhSurvivors G (U : Set _)
    · -- p ∉ W, q ∈ W.
      rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X, L1ForwardGen_of_W hqW]
      by_cases hpU : p ∈ U
      · -- p ∈ U, q ∈ W. Then q ∈ N(U) via the edge — contradiction with hqW.
        exfalso
        apply hqW
        refine Or.inr ⟨p, (by exact_mod_cast hpU : p ∈ (U : Set _)),
          Or.inl hedge⟩
      · rw [L1ForwardGen_of_N hpW hpU, zero_mul]
    · -- Both p, q ∉ W. Case on whether they are in U.
      rw [map_mul, L1ForwardPoly_X, L1ForwardPoly_X]
      by_cases hpU : p ∈ U
      · by_cases hqU : q ∈ U
        · -- Both in U: independence forbids the edge.
          exfalso
          have hpU_set : p ∈ (U : Set (BinomialEdgeVars (Fin n))) := by
            exact_mod_cast hpU
          have hqU_set : q ∈ (U : Set (BinomialEdgeVars (Fin n))) := by
            exact_mod_cast hqU
          exact hU hpU_set hqU_set hedge
        · rw [L1ForwardGen_of_U hpW hpU, L1ForwardGen_of_N hqW hqU, mul_zero]
      · rw [L1ForwardGen_of_N hpW hpU, zero_mul]

/-- The forward polynomial hom vanishes on the entire bipartite edge ideal. -/
private theorem L1ForwardPoly_vanishes {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _))
    (x : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    x ∈ bipartiteEdgeMonomialIdeal (K := K) G →
      L1ForwardPoly (K := K) G U x = 0 := by
  classical
  rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
  intro hx
  unfold MvPolynomial.variablePairIdeal at hx
  refine Submodule.span_induction (p := fun y _ =>
    L1ForwardPoly (K := K) G U y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨p, q, hpq, rfl⟩
    exact L1Forward_vanishes_on_gens hU hpq
  · simp
  · intros _ _ _ _ hx hy; simp [hx, hy]
  · intros r x _ hx; simp [hx]

/-- Descent of `L1ForwardPoly` to the quotient ring `R`. -/
private noncomputable def L1ForwardQuot {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) →ₐ[K] L1Target (K := K) G U :=
  Ideal.Quotient.liftₐ (bipartiteEdgeMonomialIdeal (K := K) G)
    (L1ForwardPoly (K := K) G U) (L1ForwardPoly_vanishes hU)

private theorem L1ForwardQuot_mk {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (p : MvPolynomial (BinomialEdgeVars (Fin n)) K) :
    L1ForwardQuot (K := K) G U hU
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) p) =
      L1ForwardPoly (K := K) G U p := by
  unfold L1ForwardQuot
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  rfl

/-! ##### Extend `L1ForwardQuot` over `Localization.Away (mkI s_U)` -/

/-- The K-algebra hom sending `X u` for `u ∈ U` to
`1 ⊗ algebraMap (X ⟨u.val, u.property⟩)`. Used to prove that `L1ForwardPoly` on
`hhUnitProduct U` is `1 ⊗ algebraMap (hhUnitProductSub U)`, hence a unit. -/
private noncomputable def L1UnitRightHom {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K →ₐ[K]
      L1Target (K := K) G U :=
  Algebra.TensorProduct.includeRight.comp
    (IsScalarTower.toAlgHom K
      (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
      (Localization.Away (hhUnitProductSub (K := K) U)))

/-- `L1UnitRightHom` on `X v` equals `1 ⊗ algebraMap (X v)`. -/
private theorem L1UnitRightHom_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : (U : Set (BinomialEdgeVars (Fin n)))) :
    L1UnitRightHom (K := K) G U (X v) =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X v)) := by
  unfold L1UnitRightHom
  rw [AlgHom.comp_apply]
  change Algebra.TensorProduct.includeRight _ = _
  rw [Algebra.TensorProduct.includeRight_apply]
  rfl

/-- Key identity: on U-variables, `L1ForwardPoly` agrees with `L1UnitRightHom ∘ map`,
where `map : MvPolynomial σ K → MvPolynomial U K` sends `X u` to `X ⟨u, hu⟩` if
`u ∈ U` and to `0` otherwise. We phrase this cleanly via a direct calculation on
the product `hhUnitProduct`. -/
private theorem L1ForwardPoly_hhUnitProduct_eq {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    L1ForwardPoly (K := K) G U (hhUnitProduct U) =
      L1UnitRightHom (K := K) G U (hhUnitProductSub (K := K) U) := by
  classical
  unfold hhUnitProduct hhUnitProductSub
  rw [map_prod, map_prod]
  -- Rewrite LHS via Finset.prod_attach.
  rw [← Finset.prod_attach U
    (f := fun u => L1ForwardPoly (K := K) G U (X (R := K) u))]
  apply Finset.prod_congr rfl
  intro u _
  -- For u ∈ U, L1ForwardPoly (X u) = 1 ⊗ algebraMap (X ⟨u, hu⟩) (via L1ForwardGen_of_U),
  -- and L1UnitRightHom (X ⟨u, hu⟩) = 1 ⊗ algebraMap (X ⟨u, hu⟩) (via L1UnitRightHom_X).
  have huU : u.val ∈ U := u.property
  have hnW : u.val ∉ hhSurvivors G (U : Set _) := by
    intro hW
    apply hW
    exact Or.inl (by exact_mod_cast huU)
  rw [L1ForwardPoly_X, L1ForwardGen_of_U hnW huU]
  rw [L1UnitRightHom_X]

set_option maxHeartbeats 400000 in
-- heartbeats needed to elaborate the composed AlgHom over a tensor target.
/-- `L1UnitRightHom` factors as `includeRight ∘ algebraMap`. -/
private theorem L1UnitRightHom_eq_includeRight_algebraMap {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (p : MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K) :
    L1UnitRightHom (K := K) G U p =
      (Algebra.TensorProduct.includeRight
          (R := K)
          (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
          (B := Localization.Away (hhUnitProductSub (K := K) U)))
        (algebraMap
          (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
          (Localization.Away (hhUnitProductSub (K := K) U)) p) := by
  unfold L1UnitRightHom
  rfl

/-- Each U-variable `X u`, after forward L1, maps to a unit in the target. -/
private theorem L1ForwardPoly_X_U_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    {u : BinomialEdgeVars (Fin n)} (huU : u ∈ U) :
    IsUnit (L1ForwardPoly (K := K) G U (X u)) := by
  classical
  rw [L1ForwardPoly_X]
  have hnW : u ∉ hhSurvivors G (U : Set _) := by
    intro hW; apply hW; exact Or.inl (by exact_mod_cast huU)
  rw [L1ForwardGen_of_U hnW huU]
  -- algebraMap (X ⟨u, _⟩) divides hhUnitProductSub U, which is a unit.
  set uSub : (U : Set (BinomialEdgeVars (Fin n))) :=
    ⟨u, by exact_mod_cast huU⟩ with huSub_def
  have hprod_unit : IsUnit
      (algebraMap
        (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
        (Localization.Away (hhUnitProductSub (K := K) U))
        (hhUnitProductSub (K := K) U)) :=
    IsLocalization.Away.algebraMap_isUnit (hhUnitProductSub (K := K) U)
  have hmem : (⟨u, huU⟩ : {v // v ∈ U}) ∈ U.attach := Finset.mem_attach _ _
  -- Factor hhUnitProductSub U = X uSub * (∏ u' ∈ erase).
  have hsplit :
      (X (R := K) uSub :
        MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K) *
      (∏ u' ∈ U.attach.erase ⟨u, huU⟩,
        X (R := K) (⟨u'.val, by exact_mod_cast u'.property⟩ :
          (U : Set (BinomialEdgeVars (Fin n))))) =
      hhUnitProductSub (K := K) U := by
    unfold hhUnitProductSub
    rw [← Finset.prod_erase_mul _ _ hmem, mul_comm]
  have hXunit : IsUnit
      ((algebraMap (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
          (Localization.Away (hhUnitProductSub (K := K) U)))
        (X (R := K) uSub)) := by
    apply isUnit_of_mul_isUnit_left (y := (algebraMap _
      (Localization.Away (hhUnitProductSub (K := K) U)))
      (∏ u' ∈ U.attach.erase ⟨u, huU⟩,
        X (R := K) (⟨u'.val, by exact_mod_cast u'.property⟩ :
          (U : Set (BinomialEdgeVars (Fin n))))))
    rw [← map_mul, hsplit]
    exact hprod_unit
  -- Now transport through includeRight.
  have hright : IsUnit
      ((Algebra.TensorProduct.includeRight
          (R := K)
          (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
          (B := Localization.Away (hhUnitProductSub (K := K) U))).toRingHom
      ((algebraMap _ (Localization.Away (hhUnitProductSub (K := K) U)))
        (X (R := K) uSub))) :=
    RingHom.isUnit_map _ hXunit
  exact hright

/-- The image of `s_U` in the target is a unit. We prove this by computing the
image as a product over `U` of factors of the form `1 ⊗ algebraMap (X u')`, each
of which is a unit. -/
private theorem L1ForwardPoly_hhUnitProduct_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    IsUnit (L1ForwardPoly (K := K) G U (hhUnitProduct U)) := by
  classical
  unfold hhUnitProduct
  rw [_root_.map_prod]
  -- Each factor L1ForwardPoly (X u) is a unit for u ∈ U. Iterate.
  have h : ∀ (s : Finset (BinomialEdgeVars (Fin n))) (_hs : s ⊆ U),
      IsUnit (∏ u ∈ s, L1ForwardPoly (K := K) G U (X u)) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]; exact isUnit_one
    | @insert a s hnotin ih =>
      rw [Finset.prod_insert hnotin]
      refine (L1ForwardPoly_X_U_isUnit G U (hs (Finset.mem_insert_self _ _))).mul ?_
      exact ih (fun x hxs => hs (Finset.mem_insert_of_mem hxs))
  exact h U (Finset.Subset.refl _)

/-- The image of `mkI s_U` in the target is a unit. -/
private theorem L1ForwardQuot_mkI_hhUnitProduct_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    IsUnit (L1ForwardQuot (K := K) G U hU
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U))) := by
  rw [L1ForwardQuot_mk]
  exact L1ForwardPoly_hhUnitProduct_isUnit (K := K) G U

/-- The L1 forward hom from `Localization.Away (mkI s_U)` into the target. -/
private noncomputable def L1Forward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    Localization.Away
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U))
      →ₐ[K] L1Target (K := K) G U := by
  refine IsLocalization.liftAlgHom
    (M := Submonoid.powers
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U)))
    (f := L1ForwardQuot (K := K) G U hU)
    (S := Localization.Away
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U))) ?_
  rintro ⟨y, k, rfl⟩
  rw [map_pow]
  exact (L1ForwardQuot_mkI_hhUnitProduct_isUnit (K := K) G U hU).pow k

/-! ##### Backward hom: target → Localization.Away (mkI s_U) -/

/-- Abbreviation for `Localization.Away (mkI s_U)` as a `K`-algebra. -/
private abbrev L1Source {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Finset (BinomialEdgeVars (Fin n))) : Type _ :=
  Localization.Away
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (hhUnitProduct U))

/-- The backward map on the restricted polynomial ring: `X ⟨v, _⟩ ↦ mkI (X v) / 1`. -/
private noncomputable def L1BackwardLeftPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    polyRestrict (K := K) (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Source (K := K) G U :=
  MvPolynomial.aeval fun v =>
    (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val))

@[simp]
private theorem L1BackwardLeftPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : hhSurvivors G (U : Set _)) :
    L1BackwardLeftPoly (K := K) G U (X v) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) := by
  unfold L1BackwardLeftPoly
  simp [MvPolynomial.aeval_X]

/-- `L1BackwardLeftPoly` kills the restricted edge ideal. -/
private theorem L1BackwardLeftPoly_vanishes {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (x : polyRestrict (K := K) (hhSurvivors G (U : Set _))) :
    x ∈ restrictedEdgeIdeal (K := K) G (hhSurvivors G (U : Set _)) →
      L1BackwardLeftPoly (K := K) G U x = 0 := by
  intro hx
  classical
  unfold restrictedEdgeIdeal MvPolynomial.variablePairIdeal at hx
  refine Submodule.span_induction (p := fun y _ =>
    L1BackwardLeftPoly (K := K) G U y = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨p, q, hpq, rfl⟩
    -- hpq : (p.val, q.val) ∈ hhEdgeSet G. Then X p.val * X q.val ∈ I.
    have hedge : (p.val, q.val) ∈ hhEdgeSet G := hpq
    have hpoly : (X p.val * X q.val :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ∈
          bipartiteEdgeMonomialIdeal (K := K) G := by
      rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
      exact Ideal.subset_span ⟨p.val, q.val, hedge, rfl⟩
    rw [map_mul, L1BackwardLeftPoly_X, L1BackwardLeftPoly_X]
    rw [← map_mul, ← map_mul,
      (Ideal.Quotient.eq_zero_iff_mem).mpr hpoly, map_zero]
  · simp
  · intros _ _ _ _ hx hy; simp [hx, hy]
  · intros r x _ hx; simp [hx]

/-- Descent to `restrictedHHRing G W → L1Source`. -/
private noncomputable def L1BackwardLeft {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Source (K := K) G U :=
  Ideal.Quotient.liftₐ (restrictedEdgeIdeal (K := K) G (hhSurvivors G (U : Set _)))
    (L1BackwardLeftPoly (K := K) G U) (L1BackwardLeftPoly_vanishes G U)

/-- The backward map on the unit-subring polynomial `K[U]`: `X⟨u, hu⟩ ↦ mkI(X u) / 1`. -/
private noncomputable def L1BackwardRightPoly {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K →ₐ[K]
      L1Source (K := K) G U :=
  MvPolynomial.aeval fun v =>
    (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val))

@[simp]
private theorem L1BackwardRightPoly_X {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (v : (U : Set (BinomialEdgeVars (Fin n)))) :
    L1BackwardRightPoly (K := K) G U (X v) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) := by
  unfold L1BackwardRightPoly
  simp [MvPolynomial.aeval_X]

/-- The image of `hhUnitProductSub U` under `L1BackwardRightPoly` is the image of
`mkI s_U` in the source localisation, hence a unit. -/
private theorem L1BackwardRightPoly_hhUnitProductSub_isUnit {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    IsUnit (L1BackwardRightPoly (K := K) G U (hhUnitProductSub (K := K) U)) := by
  classical
  -- Strategy: build three products over U.attach that coincide and glue them.
  -- Step 1: rewrite LHS via `L1BackwardRightPoly` `map_prod` and pointwise `_X`.
  have hLHS : L1BackwardRightPoly (K := K) G U (hhUnitProductSub (K := K) U) =
      ∏ u ∈ U.attach,
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)) (X u.val)) := by
    unfold hhUnitProductSub
    rw [_root_.map_prod]
    apply Finset.prod_congr rfl
    intro u _
    rw [L1BackwardRightPoly_X]
  -- Step 2: rewrite RHS `algebraMap (mk (∏ u ∈ U, X u))` via composition of the
  -- quotient ring hom and the algebraMap and two `map_prod` expansions.
  have hRHS : (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U)) =
      ∏ u ∈ U.attach,
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)) (X u.val)) := by
    -- First, `(algebraMap _ _ ∘ mk)` is a ring hom f : MvPoly σ K → L1Source.
    -- f(hhUnitProduct U) = f(∏ u ∈ U, X u) = ∏ u ∈ U, f(X u) = ∏ u ∈ U.attach, f(X u.val).
    have hfmap : ((algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U)).comp
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) :
          MvPolynomial _ K →+* _))) (hhUnitProduct U) =
        ∏ u ∈ U, ((algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U)).comp
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) :
          MvPolynomial _ K →+* _))) (X (R := K) u) := by
      unfold hhUnitProduct
      rw [_root_.map_prod]
    -- Simplify LHS-expression and apply Finset.prod_attach.
    simp only [RingHom.coe_comp, Function.comp_apply] at hfmap
    rw [hfmap]
    exact (Finset.prod_attach U (f := fun u =>
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)) (X u)))).symm
  rw [hLHS, ← hRHS]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- Descent to `Localization.Away (hhUnitProductSub U) → L1Source`. -/
private noncomputable def L1BackwardRight {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    Localization.Away (hhUnitProductSub (K := K) U) →ₐ[K]
      L1Source (K := K) G U := by
  refine IsLocalization.liftAlgHom
    (M := Submonoid.powers (hhUnitProductSub (K := K) U))
    (f := L1BackwardRightPoly (K := K) G U)
    (S := Localization.Away (hhUnitProductSub (K := K) U)) ?_
  rintro ⟨y, k, rfl⟩
  rw [map_pow]
  exact (L1BackwardRightPoly_hhUnitProductSub_isUnit (K := K) G U).pow k

/-- The L1 backward hom: assembled via `Algebra.TensorProduct.lift`. -/
private noncomputable def L1Backward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n))) :
    L1Target (K := K) G U →ₐ[K] L1Source (K := K) G U :=
  Algebra.TensorProduct.lift
    (L1BackwardLeft (K := K) G U) (L1BackwardRight (K := K) G U)
    (fun _ _ => mul_comm _ _)

/-! ##### Compositions are identity -/

/-- Forward then Backward on `algebraMap` of `mk X v` (with `v` a W-variable). -/
private theorem L1Backward_Forward_algebraMap_mk_X_of_W {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) {v : BinomialEdgeVars (Fin n)}
    (hW : v ∈ hhSurvivors G (U : Set _)) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W hW]
  -- Now L1Backward on (mk X⟨v, hW⟩) ⊗ 1 = L1BackwardLeft (mk X⟨v, hW⟩).
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  -- L1BackwardLeft (mk (X ⟨v, hW⟩)) = L1BackwardLeftPoly (X ⟨v, hW⟩).
  unfold L1BackwardLeft
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  exact L1BackwardLeftPoly_X G U ⟨v, hW⟩

/-- Forward then Backward on `algebraMap` of `mk X v` (with `v` a U-variable). -/
private theorem L1Backward_Forward_algebraMap_mk_X_of_U {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hvU : v ∈ U) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_U hnW hvU]
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  -- L1BackwardRight (algebraMap X ⟨v, hvU⟩) = L1BackwardRightPoly (X ⟨v, hvU⟩).
  unfold L1BackwardRight
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  exact L1BackwardRightPoly_X G U ⟨v, by exact_mod_cast hvU⟩

/-- Forward then Backward on `algebraMap` of `mk X v` (with `v` a N(U)-variable). -/
private theorem L1Backward_Forward_algebraMap_mk_X_of_N {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) {v : BinomialEdgeVars (Fin n)}
    (hnW : v ∉ hhSurvivors G (U : Set _)) (hnU : v ∉ U) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  -- v ∈ N(U): there is some u ∈ U with (u, v) ∈ hhEdgeSet G or (v, u) ∈ hhEdgeSet G.
  -- Then mkI(X u * X v) = 0, and mkI(X u) is a unit, so mkI(X v) = 0 in source.
  have hv_N : v ∈ hhNbhd G (U : Set _) := by
    -- v ∉ hhSurvivors means v ∈ U ∪ N(U). v ∉ U gives v ∈ N(U).
    by_contra hvN
    apply hnW
    intro h
    rcases h with hvU' | hvN'
    · exact hnU (by exact_mod_cast hvU')
    · exact hvN hvN'
  obtain ⟨u, huU, huadj⟩ := hv_N
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_N hnW hnU]
  rw [map_zero]
  -- Prove RHS = 0.
  -- There exists u ∈ U s.t. (u, v) or (v, u) in hhEdgeSet G. In both cases X u * X v ∈ I.
  have hpoly_zero : (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u) *
        Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) = 0 := by
    have hprod_mem : (X u * X v :
        MvPolynomial (BinomialEdgeVars (Fin n)) K) ∈
          bipartiteEdgeMonomialIdeal (K := K) G := by
      rw [bipartiteEdgeMonomialIdeal_eq_variablePairIdeal]
      rcases huadj with h1 | h2
      · exact Ideal.subset_span ⟨u, v, h1, rfl⟩
      · -- (v, u) ∈ hhEdgeSet. Then X v * X u ∈ I, and X u * X v = X v * X u.
        have : (X v * X u : MvPolynomial (BinomialEdgeVars (Fin n)) K) ∈
            MvPolynomial.variablePairIdeal (R := K) (hhEdgeSet G) :=
          Ideal.subset_span ⟨v, u, h2, rfl⟩
        rw [mul_comm]; exact this
    have : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u * X v) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr hprod_mem
    rw [map_mul] at this
    rw [this, map_zero]
  -- mkI (X u) is a unit in source, because it divides the unit `algebraMap (mkI s_U)`.
  have hu_unit : IsUnit ((algebraMap
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G)
      (L1Source (K := K) G U))
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u))) := by
    -- Use isUnit_of_mul_isUnit_left: if `x * y` is a unit, so is `x`.
    -- Take `y = algebraMap(mkI (∏_{w ∈ U \ {u}} X w))` so that
    -- `x * y = algebraMap(mkI s_U)` is a unit by construction.
    apply isUnit_of_mul_isUnit_left (y :=
      (algebraMap
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (∏ w ∈ U.erase u, X (R := K) w)))
    -- The product equals `algebraMap (mkI s_U)`, which is a unit.
    have hprod_eq :
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X u)) *
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (∏ w ∈ U.erase u, X (R := K) w)) =
        (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U)) := by
      rw [← map_mul, ← map_mul]
      congr 1
      -- X u * ∏ w ∈ U.erase u, X w = ∏ v ∈ U, X v.
      unfold hhUnitProduct
      rw [mul_comm, Finset.prod_erase_mul _ _ huU]
    rw [hprod_eq]
    exact IsLocalization.Away.algebraMap_isUnit _
  -- From mkI(X u) * mkI(X v) = 0 in source and mkI(X u) unit, conclude mkI(X v) = 0.
  have : (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) = 0 := by
    have h_mul := hpoly_zero
    rw [map_mul] at h_mul
    exact (hu_unit.mul_right_eq_zero).mp h_mul
  rw [this]

/-- Backward ∘ Forward on the quotient level: on `mk X v` it equals
`algebraMap (mk X v)`. -/
private theorem L1Backward_Forward_quot_mk_X {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) (v : BinomialEdgeVars (Fin n)) :
    L1Backward (K := K) G U
        (L1ForwardQuot (K := K) G U hU
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
      (algebraMap
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v)) := by
  classical
  by_cases hW : v ∈ hhSurvivors G (U : Set _)
  · exact L1Backward_Forward_algebraMap_mk_X_of_W hU hW
  · by_cases hvU : v ∈ U
    · exact L1Backward_Forward_algebraMap_mk_X_of_U hU hW hvU
    · exact L1Backward_Forward_algebraMap_mk_X_of_N hU hW hvU

/-- Backward ∘ Forward on the quotient level, stated as an algHom equality at the
`MvPolynomial` level. -/
private theorem L1Backward_Forward_quot_algHom {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    ((L1Backward (K := K) G U).comp
        (L1ForwardQuot (K := K) G U hU)).comp
      (Ideal.Quotient.mkₐ K (bipartiteEdgeMonomialIdeal (K := K) G)) =
    ((IsScalarTower.toAlgHom K
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U))).comp
      (Ideal.Quotient.mkₐ K (bipartiteEdgeMonomialIdeal (K := K) G)) := by
  apply MvPolynomial.algHom_ext
  intro v
  change (L1Backward (K := K) G U) (L1ForwardQuot (K := K) G U hU
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) =
    (algebraMap _ (L1Source (K := K) G U))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))
  exact L1Backward_Forward_quot_mk_X hU v

/-- Backward ∘ Forward = id (Localization level). -/
private theorem L1Backward_Forward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    (L1Backward (K := K) G U).comp (L1Forward (K := K) G U hU) =
      AlgHom.id K (L1Source (K := K) G U) := by
  apply
    IsLocalization.algHom_ext (W := Submonoid.powers
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (hhUnitProduct U)))
  -- Reduce to equality on algebraMap from R.
  have hBF : ((L1Backward (K := K) G U).comp
        (L1Forward (K := K) G U hU)).comp
      (IsScalarTower.toAlgHom K
        (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G)
        (L1Source (K := K) G U)) =
      IsScalarTower.toAlgHom K _ (L1Source (K := K) G U) := by
    -- First: L1Forward ∘ algebraMap_R = L1ForwardQuot (by the `liftAlgHom` property).
    have hLF : (L1Forward (K := K) G U hU).comp
        (IsScalarTower.toAlgHom K
          (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
            bipartiteEdgeMonomialIdeal (K := K) G)
          (L1Source (K := K) G U)) =
        L1ForwardQuot (K := K) G U hU := by
      apply AlgHom.ext
      intro x
      change L1Forward (K := K) G U hU
          (algebraMap _ (L1Source (K := K) G U) x) = L1ForwardQuot _ _ _ x
      unfold L1Forward
      rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
      rfl
    -- Now combine: (Bwd ∘ Fwd) ∘ algebraMap = Bwd ∘ (Fwd ∘ algebraMap) = Bwd ∘ ForwardQuot,
    -- and we want it to equal algebraMap. Use algHom_ext on the quotient.
    rw [AlgHom.comp_assoc, hLF]
    -- Now goal: L1Backward ∘ L1ForwardQuot = algebraMap (as K-alg homs from R).
    apply Ideal.Quotient.algHom_ext
    -- Goal: (Bwd ∘ ForwardQuot) ∘ mkₐ = algebraMap ∘ mkₐ
    exact L1Backward_Forward_quot_algHom G U hU
  apply AlgHom.ext
  intro x
  change (L1Backward (K := K) G U) (L1Forward (K := K) G U hU
    ((algebraMap _ (L1Source (K := K) G U)) x)) =
      (AlgHom.id K _) ((algebraMap _ (L1Source (K := K) G U)) x)
  exact congrArg (fun φ : _ →ₐ[K] L1Source (K := K) G U => φ x) hBF

/-- Forward ∘ Backward on `(mk X⟨v, hW⟩) ⊗ 1` (left pure tensor, W case). -/
private theorem L1Forward_Backward_tmul_left_X {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) (v : hhSurvivors G (U : Set _)) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _))) (X v) :
              restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X v) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1 := by
  classical
  -- L1Backward on (mk X v) ⊗ 1 = L1BackwardLeft (mk X v).
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  unfold L1BackwardLeft
  rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
  change L1Forward (K := K) G U hU (L1BackwardLeftPoly (K := K) G U (X v)) = _
  rw [L1BackwardLeftPoly_X]
  -- L1Forward (algebraMap (mk X v.val)) = L1ForwardQuot (mk X v.val).
  unfold L1Forward
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change L1ForwardQuot (K := K) G U hU
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) = _
  rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W v.property]

/-- Forward ∘ Backward on `1 ⊗ algebraMap (X ⟨u, hu⟩)` (right pure tensor, U case). -/
private theorem L1Forward_Backward_tmul_right_X {n : ℕ}
    {G : SimpleGraph (Fin n)} {U : Finset (BinomialEdgeVars (Fin n))}
    (hU : hhIndep G (U : Set _)) (v : (U : Set (BinomialEdgeVars (Fin n)))) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
            (algebraMap
                (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
                (Localization.Away (hhUnitProductSub (K := K) U))
              (X v)))) =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap
            (MvPolynomial ((U : Set (BinomialEdgeVars (Fin n)))) K)
            (Localization.Away (hhUnitProductSub (K := K) U))
          (X v)) := by
  classical
  -- L1Backward on 1 ⊗ (algebraMap X v) = L1BackwardRight (algebraMap X v).
  unfold L1Backward
  rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
  unfold L1BackwardRight
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change L1Forward (K := K) G U hU (L1BackwardRightPoly (K := K) G U (X v)) = _
  rw [L1BackwardRightPoly_X]
  -- L1Forward (algebraMap (mk X v.val)) = L1ForwardQuot (mk X v.val).
  unfold L1Forward
  rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  change L1ForwardQuot (K := K) G U hU
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v.val)) = _
  rw [L1ForwardQuot_mk, L1ForwardPoly_X]
  -- v ∈ U, v ∉ W (because U ⊆ Wᶜ).
  have hvU : v.val ∈ U := by exact_mod_cast v.property
  have hvU_set : v.val ∈ (U : Set (BinomialEdgeVars (Fin n))) := by
    exact_mod_cast hvU
  have hvnW : v.val ∉ hhSurvivors G (U : Set _) := by
    intro h
    exact h (Or.inl hvU_set)
  rw [L1ForwardGen_of_U hvnW hvU]

-- The `set φL, set φR` pattern plus MvPolynomial/Ideal.Quotient extensionality
set_option maxHeartbeats 1600000 in
-- heartbeats needed: target type `L1Target` is a heavy tensor product of a quotient
-- and a localization; algHom extensionality on pure tensors is expensive.
/-- Forward ∘ Backward on left pure tensors (algHom equality): reduce to generators
via quotient + polynomial extensionality. -/
private theorem L1Forward_Backward_left {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U (a ⊗ₜ[K] 1)) = a ⊗ₜ[K] 1 := by
  classical
  set φL : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Target (K := K) G U :=
    ((L1Forward (K := K) G U hU).comp (L1Backward (K := K) G U)).comp
      (Algebra.TensorProduct.includeLeft
        (R := K) (S := K)
        (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
        (B := Localization.Away (hhUnitProductSub (K := K) U)))
  set φR : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)) →ₐ[K]
      L1Target (K := K) G U :=
    Algebra.TensorProduct.includeLeft
      (R := K) (S := K)
      (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
      (B := Localization.Away (hhUnitProductSub (K := K) U))
  have hφ : φL = φR := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro v
    change L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _))) (X v) :
              restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1)) =
      (Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X v) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1
    exact L1Forward_Backward_tmul_left_X hU v
  have := congrArg (fun φ => φ a) hφ
  exact this

set_option maxHeartbeats 1600000 in
-- heartbeats needed: heavy tensor-product extensionality; see L1Forward_Backward_left.
/-- Forward ∘ Backward on right pure tensors (algHom equality). -/
private theorem L1Forward_Backward_right {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (b : Localization.Away (hhUnitProductSub (K := K) U)) :
    L1Forward (K := K) G U hU
        (L1Backward (K := K) G U (1 ⊗ₜ[K] b)) = 1 ⊗ₜ[K] b := by
  classical
  set φL : Localization.Away (hhUnitProductSub (K := K) U) →ₐ[K]
      L1Target (K := K) G U :=
    ((L1Forward (K := K) G U hU).comp (L1Backward (K := K) G U)).comp
      (Algebra.TensorProduct.includeRight
        (R := K)
        (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
        (B := Localization.Away (hhUnitProductSub (K := K) U)))
  set φR : Localization.Away (hhUnitProductSub (K := K) U) →ₐ[K]
      L1Target (K := K) G U :=
    Algebra.TensorProduct.includeRight
      (R := K)
      (A := restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
      (B := Localization.Away (hhUnitProductSub (K := K) U))
  have hφ : φL = φR := by
    refine IsLocalization.algHom_ext
      (W := Submonoid.powers (hhUnitProductSub (K := K) U)) ?_
    apply MvPolynomial.algHom_ext
    intro v
    change L1Forward (K := K) G U hU
        (L1Backward (K := K) G U
          ((1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
            (algebraMap _
              (Localization.Away (hhUnitProductSub (K := K) U)) (X v)))) =
      (1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (algebraMap _
          (Localization.Away (hhUnitProductSub (K := K) U)) (X v))
    exact L1Forward_Backward_tmul_right_X hU v
  have := congrArg (fun φ => φ b) hφ
  exact this

/-- Forward ∘ Backward = id. -/
private theorem L1Forward_Backward {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    (L1Forward (K := K) G U hU).comp (L1Backward (K := K) G U) =
      AlgHom.id K (L1Target (K := K) G U) := by
  apply Algebra.TensorProduct.ext'
  intro a b
  -- Factor a ⊗ b = (a ⊗ 1) * (1 ⊗ b).
  have hsplit : a ⊗ₜ[K] b =
      ((a ⊗ₜ[K] (1 : Localization.Away (hhUnitProductSub (K := K) U))) *
        ((1 : restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] b)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  change (L1Forward (K := K) G U hU) ((L1Backward (K := K) G U) (a ⊗ₜ[K] b)) =
    a ⊗ₜ[K] b
  rw [hsplit, map_mul, map_mul, L1Forward_Backward_left G U hU a,
    L1Forward_Backward_right G U hU b]

/-- **The L1 iso.** Monomial-localisation of the HH quotient at the independent
unit product `s_U` decomposes as a tensor of the restricted HH ring on `W` with
the Laurent polynomial ring on `U`:

  `R[s_U⁻¹] ≃ₐ[K] (restrictedHHRing G W) ⊗[K] Localization.Away s_U^U`. -/
private noncomputable def L1Iso {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    Localization.Away
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U))
      ≃ₐ[K]
      TensorProduct K
        (restrictedHHRing (K := K) G (hhSurvivors G (U : Set _)))
        (Localization.Away (hhUnitProductSub (K := K) U)) :=
  AlgEquiv.ofAlgHom (L1Forward (K := K) G U hU) (L1Backward (K := K) G U)
    (L1Forward_Backward G U hU) (L1Backward_Forward G U hU)

/-! ### Session A′: the reduced HH ring at its augmentation is CM local

The goal is

    IsCohenMacaulayLocalRing (Localization.AtPrime (augIdealReduced G))

for any HH graph `G` on `Fin (r + 1)`.

**Base case `r = 0`**: the reduced HH ring on no variables is `K` (a field),
`augIdealReduced = ⊥`, and `Localization.AtPrime ⊥ (field)` is CM local.

**Inductive case `r ≥ 1`**: bridge from L5 CM output to
`Localization.AtPrime (augIdealReduced G)` via the chain
  (L5) = (Rp ⧸ x_last) ⧸ y_last
       ≅ Rp ⧸ ⟨x_last, y_last⟩
       ≅ (R_G ⧸ ⟨x_last, y_last⟩)_{augIdeal / ...}
       ≅ Localization.AtPrime (augIdealReduced G)
where each step uses either `DoubleQuot`, quotient/localization commutation,
or the polynomial-level "kill last pair" ring equivalence.
-/

/-! #### Base case `r = 0`: reduced HH ring is the field `K` -/

/-- For `r = 0`, the index type `BinomialEdgeVars (Fin 0)` is empty. -/
private instance isEmpty_binomialEdgeVars_fin_zero :
    IsEmpty (BinomialEdgeVars (Fin 0)) :=
  inferInstanceAs (IsEmpty (Fin 0 ⊕ Fin 0))

/-- When the index type is empty, the reduced HH ideal has no generators, so it equals `⊥`. -/
private theorem reducedHHIdeal_eq_bot_of_r_zero {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) :
    BEI.reducedHHIdeal (K := K) G' = ⊥ := by
  unfold BEI.reducedHHIdeal MvPolynomial.variablePairIdeal
  rw [Ideal.span_eq_bot]
  rintro x ⟨a, _, _, _⟩
  exact (IsEmpty.false a).elim

/-- The reduced HH ring is isomorphic to `K` when `r = 0`. -/
private noncomputable def reducedHHRing_equiv_K_of_r_zero {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) : BEI.reducedHHRing (K := K) G' ≃ₐ[K] K :=
  (Ideal.quotientEquivAlgOfEq K (reducedHHIdeal_eq_bot_of_r_zero G')).trans <|
    (AlgEquiv.quotientBot K _).trans
      (MvPolynomial.isEmptyAlgEquiv K (BinomialEdgeVars (Fin 0)))

/-- `augIdealReduced G' = ⊥` when `r = 0`: in a field, every proper ideal is `⊥`. -/
private theorem augIdealReduced_eq_bot_of_r_zero {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) :
    BEI.augIdealReduced (K := K) G' = ⊥ := by
  -- reducedHHRing G' is a field (via iso to K), hence every proper ideal is ⊥.
  have hfield : IsField (BEI.reducedHHRing (K := K) G') :=
    (reducedHHRing_equiv_K_of_r_zero G').toRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  letI : Field (BEI.reducedHHRing (K := K) G') := hfield.toField
  have hmax : (BEI.augIdealReduced (K := K) G').IsMaximal := BEI.augIdealReduced_isMaximal G'
  have hne_top : BEI.augIdealReduced (K := K) G' ≠ ⊤ := hmax.ne_top
  rcases Ideal.eq_bot_or_top (BEI.augIdealReduced (K := K) G') with heq | heq
  · exact heq
  · exact absurd heq hne_top

/-- **Base case** (`r = 0`): the localization of the reduced HH ring at its
augmentation ideal is CM local. Proof: `reducedHHRing G'` is a field, the
augmentation ideal is `⊥`, and the localization has Krull dimension 0. -/
private theorem isCohenMacaulayLocalRing_at_augIdealReduced_base {K : Type*} [Field K]
    (G' : SimpleGraph (Fin 1)) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) := by
  -- reducedHHRing G' is a field.
  have hfield : IsField (BEI.reducedHHRing (K := K) G') :=
    (reducedHHRing_equiv_K_of_r_zero G').toRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  letI : Field (BEI.reducedHHRing (K := K) G') := hfield.toField
  -- Krull dim of localization = height of augIdealReduced = 0 (since augIdealReduced = ⊥).
  apply isCohenMacaulayLocalRing_of_ringKrullDim_eq_zero
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (BEI.augIdealReduced (K := K) G')
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G')),
    Ideal.height_eq_primeHeight]
  have h : (BEI.augIdealReduced (K := K) G').primeHeight = 0 :=
    Ideal.primeHeight_eq_zero_iff.mpr (by
      rw [augIdealReduced_eq_bot_of_r_zero, IsDomain.minimalPrimes_eq_singleton_bot,
        Set.mem_singleton_iff])
  rw [h]; rfl

/-! #### Inductive case `r ≥ 1`: "kill last pair" bridge to `reducedHHRing`

We build a 4-step bridge from L5's CM output
`QuotSMulTop mkyL RpQ` (= `(Rp ⧸ xL) ⧸ yL`) to
`Localization.AtPrime (augIdealReduced G)`:

1. `QuotSMulTop mkyL RpQ ≃+* (Rp ⧸ xL) ⧸ span{mkyL}` (existing bridge).
2. `(Rp ⧸ xL) ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}` (DoubleQuot).
3. `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime (augIdeal.map mk_J) (R_G ⧸ J)`
   where `J = span{mkI X(inl r), mkI X(inr r)}` (localisation-quotient commutation).
4. `R_G ⧸ J ≃ₐ[K] reducedHHRing G` (the "kill last pair" polynomial iso).

Then transport L5's CM conclusion via `isCohenMacaulayLocalRing_of_ringEquiv'`.
-/

variable {r : ℕ}

/-- Forward variable map for the "kill last pair" iso: `inl i ↦ mkI X(inl i.castSucc)`
if `i.val < r`, else `0`. Similarly for `inr`. The "last" variables (index `r`)
are sent to `0`. -/
private noncomputable def killLastPairForwardVar
    {G : SimpleGraph (Fin (r + 1))} :
    BinomialEdgeVars (Fin (r + 1)) → BEI.reducedHHRing (K := K) G
  | Sum.inl ⟨i, _⟩ =>
      if h : i < r then
        Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inl ⟨i, h⟩))
      else 0
  | Sum.inr ⟨i, _⟩ =>
      if h : i < r then
        Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inr ⟨i, h⟩))
      else 0

/-- The forward polynomial-level algebra hom
`MvPolynomial (BinomialEdgeVars (Fin (r+1))) K →ₐ[K] reducedHHRing G`. -/
private noncomputable def killLastPairForwardPoly
    (G : SimpleGraph (Fin (r + 1))) :
    MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K →ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  aeval (killLastPairForwardVar (K := K) (G := G))

/-- `bipartiteEdgeMonomialIdeal G` is contained in the kernel of `killLastPairForwardPoly`.
Every generator `X(inl i) * X(inr j)` with `j.val + 1 < r + 1` has `j.val < r`, so
`j : Fin r`; additionally `i ≤ j` forces `i.val ≤ j.val < r`, so `i : Fin r`.
Hence the product maps to a reducedHH generator. -/
private lemma killLastPairForwardPoly_kills_bipartite
    (G : SimpleGraph (Fin (r + 1))) :
    bipartiteEdgeMonomialIdeal (K := K) G ≤
      RingHom.ker (killLastPairForwardPoly (K := K) G).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨i, j, hj, hadj, hle, rfl⟩
  -- `j.val + 1 < r + 1` ⟹ `j.val < r` ⟹ `i.val ≤ j.val < r`.
  have hjr : j.val < r := by omega
  have hir : i.val < r := lt_of_le_of_lt (by exact_mod_cast hle) hjr
  -- The map sends `X(inl i) * X(inr j)` to the corresponding reducedHH generator.
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  change (killLastPairForwardPoly (K := K) G) (X (Sum.inl i) * X (Sum.inr j)) = 0
  rw [map_mul]
  change (killLastPairForwardPoly (K := K) G) (X (Sum.inl i)) *
      (killLastPairForwardPoly (K := K) G) (X (Sum.inr j)) = 0
  unfold killLastPairForwardPoly
  rw [aeval_X, aeval_X]
  -- Now rewrite the variable map on the two elements.
  have hvar_inl : killLastPairForwardVar (K := K) (G := G) (Sum.inl i) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G)
        (X (Sum.inl ⟨i.val, hir⟩)) := by
    rcases i with ⟨iv, _⟩
    simp [killLastPairForwardVar, hir]
  have hvar_inr : killLastPairForwardVar (K := K) (G := G) (Sum.inr j) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G)
        (X (Sum.inr ⟨j.val, hjr⟩)) := by
    rcases j with ⟨jv, _⟩
    simp [killLastPairForwardVar, hjr]
  rw [hvar_inl, hvar_inr, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  -- Show the product is in reducedHHIdeal.
  have hle' : (⟨i.val, hir⟩ : Fin r) ≤ ⟨j.val, hjr⟩ := by
    change i.val ≤ j.val; exact_mod_cast hle
  have hjsucc : (⟨j.val, hjr⟩ : Fin r).val + 1 < r + 1 := by simp; omega
  -- The adjacency condition.
  have hadj' : G.Adj (⟨i.val, hir⟩ : Fin r).castSucc
      ⟨(⟨j.val, hjr⟩ : Fin r).val + 1, hjsucc⟩ := by
    have heq1 : (⟨i.val, hir⟩ : Fin r).castSucc = i := Fin.ext rfl
    have heq2 : (⟨(⟨j.val, hjr⟩ : Fin r).val + 1, hjsucc⟩ : Fin (r + 1)) =
        ⟨j.val + 1, by omega⟩ := rfl
    rw [heq1, heq2]; exact hadj
  exact BEI.X_inl_mul_X_inr_mem_reducedHHIdeal hle' hjsucc hadj'

/-- The forward algebra hom `R_G →ₐ[K] reducedHHRing G`, obtained by descending
`killLastPairForwardPoly` through `bipartiteEdgeMonomialIdeal G`. -/
private noncomputable def killLastPairForwardRG
    (G : SimpleGraph (Fin (r + 1))) :
    (MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) →ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  Ideal.Quotient.liftₐ _ (killLastPairForwardPoly (K := K) G)
    (fun a ha => by
      have := killLastPairForwardPoly_kills_bipartite (K := K) G ha
      simpa [RingHom.mem_ker] using this)

/-- The "kill last pair" ideal in `R_G`: the span of the images of `X(inl r), X(inr r)`. -/
private noncomputable def killLastPairIdeal (G : SimpleGraph (Fin (r + 1))) :
    Ideal (MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
  Ideal.span
    { Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨r, lt_add_one r⟩)),
      Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨r, lt_add_one r⟩)) }

/-- `killLastPairForwardRG` kills `killLastPairIdeal G` — both last variables map to `0`. -/
private lemma killLastPairForwardRG_kills_lastPair
    (G : SimpleGraph (Fin (r + 1))) :
    killLastPairIdeal (K := K) G ≤
      RingHom.ker (killLastPairForwardRG (K := K) G).toRingHom := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  rcases hx with rfl | rfl
  · change killLastPairForwardRG (K := K) G
      (Ideal.Quotient.mk _ (X (Sum.inl ⟨r, lt_add_one r⟩))) = 0
    unfold killLastPairForwardRG
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    change killLastPairForwardPoly (K := K) G (X (Sum.inl ⟨r, lt_add_one r⟩)) = 0
    unfold killLastPairForwardPoly
    rw [aeval_X]
    simp [killLastPairForwardVar]
  · change killLastPairForwardRG (K := K) G
      (Ideal.Quotient.mk _ (X (Sum.inr ⟨r, lt_add_one r⟩))) = 0
    unfold killLastPairForwardRG
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    change killLastPairForwardPoly (K := K) G (X (Sum.inr ⟨r, lt_add_one r⟩)) = 0
    unfold killLastPairForwardPoly
    rw [aeval_X]
    simp [killLastPairForwardVar]

/-- The forward algebra hom `(R_G ⧸ J) →ₐ[K] reducedHHRing G` where `J = killLastPairIdeal G`. -/
private noncomputable def killLastPairForward
    (G : SimpleGraph (Fin (r + 1))) :
    ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸
        killLastPairIdeal (K := K) G) →ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  Ideal.Quotient.liftₐ _ (killLastPairForwardRG (K := K) G)
    (fun a ha => by
      have := killLastPairForwardRG_kills_lastPair (K := K) G ha
      simpa [RingHom.mem_ker] using this)

/-! ##### Backward direction: `reducedHHRing G →ₐ[K] R_G ⧸ killLastPairIdeal G` -/

/-- Backward variable map: `inl i ↦ mk_quot(mkI X(inl i.castSucc))`. -/
private noncomputable def killLastPairBackwardVar
    (G : SimpleGraph (Fin (r + 1))) :
    BinomialEdgeVars (Fin r) →
      ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G) ⧸
          killLastPairIdeal (K := K) G)
  | Sum.inl i =>
      Ideal.Quotient.mk _
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl i.castSucc)))
  | Sum.inr i =>
      Ideal.Quotient.mk _
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr i.castSucc)))

/-- The backward polynomial-level algebra hom
`MvPolynomial (BinomialEdgeVars (Fin r)) K →ₐ[K] (R_G ⧸ killLastPairIdeal G)`. -/
private noncomputable def killLastPairBackwardPoly
    (G : SimpleGraph (Fin (r + 1))) :
    MvPolynomial (BinomialEdgeVars (Fin r)) K →ₐ[K]
      ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G) ⧸
          killLastPairIdeal (K := K) G) :=
  aeval (killLastPairBackwardVar (K := K) G)

/-- `reducedHHIdeal G` is contained in the kernel of `killLastPairBackwardPoly`.
Each reducedHH generator `X(inl a) * X(inr b)` (with `a ≤ b < r` and edge
`{a, b+1}` in `G`) maps under `castSucc` embedding to a bipartite-edge generator
in `R_G`, which is zero in `R_G` (hence zero in the further quotient). -/
private lemma killLastPairBackwardPoly_kills_reducedHHIdeal
    (G : SimpleGraph (Fin (r + 1))) :
    BEI.reducedHHIdeal (K := K) G ≤
      RingHom.ker (killLastPairBackwardPoly (K := K) G).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨a, b, ⟨a', b', hb', hadj, hle, heq⟩, rfl⟩
  obtain ⟨rfl, rfl⟩ := Prod.eq_iff_fst_eq_snd_eq.mp heq
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  change (killLastPairBackwardPoly (K := K) G) (X (Sum.inl a') * X (Sum.inr b')) = 0
  rw [map_mul]
  change (killLastPairBackwardPoly (K := K) G) (X (Sum.inl a')) *
      (killLastPairBackwardPoly (K := K) G) (X (Sum.inr b')) = 0
  unfold killLastPairBackwardPoly
  rw [aeval_X, aeval_X]
  show (killLastPairBackwardVar (K := K) G (Sum.inl a')) *
      (killLastPairBackwardVar (K := K) G (Sum.inr b')) = 0
  unfold killLastPairBackwardVar
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  -- The product lies in `killLastPairIdeal G`, since it is already 0 in `R_G`:
  -- `X(inl a'.castSucc) * X(inr b'.castSucc) ∈ bipartiteEdgeMonomialIdeal G`.
  have hj : (b'.castSucc : Fin (r + 1)).val + 1 < r + 1 := by
    have : (b'.castSucc : Fin (r + 1)).val = b'.val := rfl
    rw [this]; omega
  have hadj' : G.Adj (a'.castSucc : Fin (r + 1))
      ⟨(b'.castSucc : Fin (r + 1)).val + 1, hj⟩ := by
    have heq : (⟨(b'.castSucc : Fin (r + 1)).val + 1, hj⟩ : Fin (r + 1)) =
        ⟨b'.val + 1, hb'⟩ := rfl
    rw [heq]; exact hadj
  have hle' : (a'.castSucc : Fin (r + 1)) ≤ b'.castSucc := by
    change a'.val ≤ b'.val; exact_mod_cast hle
  have hmem_R : (X (Sum.inl a'.castSucc) * X (Sum.inr b'.castSucc) :
      MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K) ∈
      bipartiteEdgeMonomialIdeal (K := K) G := by
    refine Ideal.subset_span ?_
    exact ⟨a'.castSucc, b'.castSucc, hj, hadj', hle', rfl⟩
  have : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inl a'.castSucc) * X (Sum.inr b'.castSucc)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem_R
  rw [this]
  exact (killLastPairIdeal (K := K) G).zero_mem

/-- The backward algebra hom `reducedHHRing G →ₐ[K] (R_G ⧸ killLastPairIdeal G)`. -/
private noncomputable def killLastPairBackward
    (G : SimpleGraph (Fin (r + 1))) :
    BEI.reducedHHRing (K := K) G →ₐ[K]
      ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
          bipartiteEdgeMonomialIdeal (K := K) G) ⧸
          killLastPairIdeal (K := K) G) :=
  Ideal.Quotient.liftₐ _ (killLastPairBackwardPoly (K := K) G)
    (fun a ha => by
      have := killLastPairBackwardPoly_kills_reducedHHIdeal (K := K) G ha
      simpa [RingHom.mem_ker] using this)

/-! ##### Assembly: `killLastPairEquiv` -/

/-- Application lemma: `killLastPairForward` applied to the double-quotient of a polynomial
equals `killLastPairForwardPoly` applied to the polynomial. -/
private lemma killLastPairForward_apply_mk_mk
    (G : SimpleGraph (Fin (r + 1)))
    (p : MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K) :
    killLastPairForward (K := K) G
      (Ideal.Quotient.mk (killLastPairIdeal (K := K) G)
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) p)) =
    killLastPairForwardPoly (K := K) G p := rfl

/-- Application lemma: `killLastPairBackward` applied to the quotient of a polynomial
equals `killLastPairBackwardPoly` applied to the polynomial. -/
private lemma killLastPairBackward_apply_mk
    (G : SimpleGraph (Fin (r + 1)))
    (p : MvPolynomial (BinomialEdgeVars (Fin r)) K) :
    killLastPairBackward (K := K) G
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) p) =
    killLastPairBackwardPoly (K := K) G p := rfl

/-- Variable-level value of the forward map on `inl i.castSucc` (non-last). -/
private lemma killLastPairForwardVar_inl_castSucc
    (G : SimpleGraph (Fin (r + 1))) (i : Fin r) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inl i.castSucc) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inl i)) := by
  rcases i with ⟨iv, hiv⟩
  simp [killLastPairForwardVar, Fin.castSucc, hiv]

/-- Variable-level value of the forward map on `inr i.castSucc` (non-last). -/
private lemma killLastPairForwardVar_inr_castSucc
    (G : SimpleGraph (Fin (r + 1))) (i : Fin r) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inr i.castSucc) =
      Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X (Sum.inr i)) := by
  rcases i with ⟨iv, hiv⟩
  simp [killLastPairForwardVar, Fin.castSucc, hiv]

/-- Variable-level value of the forward map on `inl ⟨r, _⟩` (last). -/
private lemma killLastPairForwardVar_inl_last
    (G : SimpleGraph (Fin (r + 1))) (h : r < r + 1) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inl ⟨r, h⟩) = 0 := by
  simp [killLastPairForwardVar]

/-- Variable-level value of the forward map on `inr ⟨r, _⟩` (last). -/
private lemma killLastPairForwardVar_inr_last
    (G : SimpleGraph (Fin (r + 1))) (h : r < r + 1) :
    killLastPairForwardVar (K := K) (G := G) (Sum.inr ⟨r, h⟩) = 0 := by
  simp [killLastPairForwardVar]

/-- Both compositions `forward ∘ backward` and `backward ∘ forward` are the identity,
so `killLastPairForward` and `killLastPairBackward` assemble into a ring equivalence. -/
private noncomputable def killLastPairEquiv
    (G : SimpleGraph (Fin (r + 1))) :
    ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸
        killLastPairIdeal (K := K) G) ≃ₐ[K]
      BEI.reducedHHRing (K := K) G :=
  AlgEquiv.ofAlgHom (killLastPairForward (K := K) G)
    (killLastPairBackward (K := K) G)
    (by
      -- forward ∘ backward = id on `reducedHHRing G`. Use quotient + MvPolynomial
      -- algHom_ext: it suffices to check equality on variables (images of `X v`).
      refine Ideal.Quotient.algHom_ext _ ?_
      refine MvPolynomial.algHom_ext (fun v => ?_)
      -- Goal: ((F ∘ B) ∘ mk) (X v) = (id ∘ mk) (X v).
      change killLastPairForward (K := K) G
          (killLastPairBackward (K := K) G
            (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X v))) =
        Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X v)
      rw [killLastPairBackward_apply_mk]
      show killLastPairForward (K := K) G
          (killLastPairBackwardPoly (K := K) G (X v)) = _
      change killLastPairForward (K := K) G
          (aeval (killLastPairBackwardVar (K := K) G) (X v)) = _
      rw [aeval_X]
      cases v with
      | inl i =>
        change killLastPairForward (K := K) G
            (Ideal.Quotient.mk _
              (Ideal.Quotient.mk _ (X (Sum.inl i.castSucc)))) = _
        rw [killLastPairForward_apply_mk_mk]
        show killLastPairForwardPoly (K := K) G (X (Sum.inl i.castSucc)) = _
        change aeval (killLastPairForwardVar (K := K) (G := G)) (X (Sum.inl i.castSucc)) = _
        rw [aeval_X, killLastPairForwardVar_inl_castSucc]
      | inr i =>
        change killLastPairForward (K := K) G
            (Ideal.Quotient.mk _
              (Ideal.Quotient.mk _ (X (Sum.inr i.castSucc)))) = _
        rw [killLastPairForward_apply_mk_mk]
        show killLastPairForwardPoly (K := K) G (X (Sum.inr i.castSucc)) = _
        change aeval (killLastPairForwardVar (K := K) (G := G)) (X (Sum.inr i.castSucc)) = _
        rw [aeval_X, killLastPairForwardVar_inr_castSucc])
    (by
      -- backward ∘ forward = id on `(R_G ⧸ killLastPairIdeal)`.
      refine Ideal.Quotient.algHom_ext _ ?_
      refine Ideal.Quotient.algHom_ext _ ?_
      refine MvPolynomial.algHom_ext (fun v => ?_)
      -- Goal: ((B ∘ F) ∘ mk ∘ mk) (X v) = (id ∘ mk ∘ mk) (X v).
      change killLastPairBackward (K := K) G
          (killLastPairForward (K := K) G
            (Ideal.Quotient.mk _
              (Ideal.Quotient.mk _ (X v)))) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (X v))
      rw [killLastPairForward_apply_mk_mk]
      show killLastPairBackward (K := K) G
          (killLastPairForwardPoly (K := K) G (X v)) = _
      change killLastPairBackward (K := K) G
          (aeval (killLastPairForwardVar (K := K) (G := G)) (X v)) = _
      rw [aeval_X]
      cases v with
      | inl i =>
        rcases i with ⟨iv, hiv⟩
        by_cases h : iv < r
        · -- Non-last: iv < r. Write i = ⟨iv, hiv⟩ as (⟨iv, h⟩ : Fin r).castSucc.
          have heq : (⟨iv, hiv⟩ : Fin (r + 1)) = (⟨iv, h⟩ : Fin r).castSucc := rfl
          rw [heq, killLastPairForwardVar_inl_castSucc]
          rw [killLastPairBackward_apply_mk]
          change killLastPairBackwardPoly (K := K) G (X (Sum.inl ⟨iv, h⟩)) = _
          change aeval (killLastPairBackwardVar (K := K) G) (X (Sum.inl ⟨iv, h⟩)) = _
          rw [aeval_X]
          show killLastPairBackwardVar (K := K) G (Sum.inl ⟨iv, h⟩) = _
          rfl
        · -- Last: iv = r. Forward sends to 0; we need `0 = mk(mk(X(inl ⟨r, hiv⟩)))`.
          have hiv_eq : iv = r := by omega
          subst hiv_eq
          rw [killLastPairForwardVar_inl_last]
          rw [map_zero]
          -- Show `0 = mk(mk(X(inl ⟨r, hiv⟩)))` in `(R_G ⧸ killLastPairIdeal)`.
          symm
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (by left; rfl)
      | inr i =>
        rcases i with ⟨iv, hiv⟩
        by_cases h : iv < r
        · have heq : (⟨iv, hiv⟩ : Fin (r + 1)) = (⟨iv, h⟩ : Fin r).castSucc := rfl
          rw [heq, killLastPairForwardVar_inr_castSucc]
          rw [killLastPairBackward_apply_mk]
          change killLastPairBackwardPoly (K := K) G (X (Sum.inr ⟨iv, h⟩)) = _
          change aeval (killLastPairBackwardVar (K := K) G) (X (Sum.inr ⟨iv, h⟩)) = _
          rw [aeval_X]
          rfl
        · have hiv_eq : iv = r := by omega
          subst hiv_eq
          rw [killLastPairForwardVar_inr_last]
          rw [map_zero]
          symm
          rw [Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.subset_span (by right; rfl))

/-! ##### Localisation-quotient commutation (Step 3 of the bridge)

We build a ring equivalence
    `Rp ⧸ span{xL, yL}  ≃+*  Localization.AtPrime (augIdealQuot G) (R_G ⧸ killLastPairIdeal G)`
where `Rp = Localization.AtPrime (augIdeal G)`, xL, yL are the images of the last-pair
variables in Rp, and `augIdealQuot G = augIdeal G`-map to the quotient.

The bridge uses:
- forward: `Rp/J_Rp → Localization.AtPrime augIdealQuot`, defined by factoring
  `Localization.localRingHom` through the quotient.
- backward: `Localization.AtPrime augIdealQuot → Rp/J_Rp`, defined via the universal
  property (`IsLocalization.lift`).
-/

/-! ##### Image of `augIdeal G` under `killLastPairEquiv` is `augIdealReduced G` -/

/-- The image of `augIdeal G` under the double-quotient projection, as an ideal
in `R_G ⧸ killLastPairIdeal G`. -/
private noncomputable def augIdealQuot (G : SimpleGraph (Fin (r + 1))) :
    Ideal ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸
        killLastPairIdeal (K := K) G) :=
  (augIdeal (K := K) G).map (Ideal.Quotient.mk (killLastPairIdeal (K := K) G))

/-- `killLastPairIdeal G ⊆ augIdeal G`: both last-pair generators lie in the augmentation
ideal (they are variables with zero constant coefficient). -/
private lemma killLastPairIdeal_le_augIdeal (G : SimpleGraph (Fin (r + 1))) :
    killLastPairIdeal (K := K) G ≤ augIdeal (K := K) G := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact mkI_X_mem_augIdeal G _
  · exact mkI_X_mem_augIdeal G _

/-- `augIdealQuot G` is a maximal ideal (hence prime). Proof: use that
`(R_G ⧸ killLastPairIdeal) ⧸ augIdealQuot ≃ R_G ⧸ augIdeal = K`, a field. -/
private instance augIdealQuot_isMaximal (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).IsMaximal := by
  haveI : (augIdeal (K := K) G).IsMaximal := augIdeal_isMaximal G
  -- Use DoubleQuot.quotQuotEquivQuotOfLE to get the isomorphism.
  have hiso : ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) ⧸ killLastPairIdeal (K := K) G) ⧸
      augIdealQuot (K := K) G ≃+*
      (MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸ augIdeal (K := K) G :=
    DoubleQuot.quotQuotEquivQuotOfLE (killLastPairIdeal_le_augIdeal G)
  -- The target is a field (quotient by maximal), hence the source's quotient is too.
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  have hRHS_field : IsField ((MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) ⧸ augIdeal (K := K) G) :=
    Ideal.Quotient.maximal_ideal_iff_isField_quotient _ |>.mp inferInstance
  exact MulEquiv.isField hRHS_field hiso.toMulEquiv

private instance augIdealQuot_isPrime (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).IsPrime := (augIdealQuot_isMaximal G).isPrime

/-- `augIdealQuot G` maps onto `augIdealReduced G` under `killLastPairEquiv`. -/
private lemma killLastPairEquiv_map_augIdealQuot
    (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).map
      (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom =
    BEI.augIdealReduced (K := K) G := by
  -- Show both inclusions.
  apply le_antisymm
  · -- `⊆`: every generator of augIdealQuot maps into augIdealReduced.
    -- augIdealQuot = map of augIdeal = map of (map of RingHom.ker constantCoeff).
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    -- x ∈ augIdealQuot G = (augIdeal G).map mk_J.
    -- First push into augIdeal, then factor through quotient.
    rw [augIdealQuot, Ideal.mem_comap] at *
    -- x ∈ (augIdeal G).map mk_J, i.e., there exist quotient representatives.
    -- Use constantCoeff factoring. Strategy: the forward algebra hom sends augIdeal
    -- (at the polynomial level) to augIdealReduced, because constant coefficients
    -- commute with the aeval.
    -- Prove augIdealQuot ≤ comap (mk_J ∘ mk_bipartite) of (polynomial augIdeal-like thing).
    -- Simpler: it suffices to show for x = mk_J (y) with y ∈ augIdeal G,
    -- that (killLastPairEquiv G) (mk_J y) ∈ augIdealReduced G.
    -- Use Ideal.map_mono-style induction via Submodule.span_induction.
    induction hx using Submodule.span_induction with
    | mem z hz =>
      -- z = mk_J y with y ∈ augIdeal G.
      obtain ⟨y, hy, rfl⟩ := hz
      -- killLastPairEquiv (mk_J y) = killLastPairForward (mk_J y) = killLastPairForwardRG y.
      change (killLastPairEquiv (K := K) G) (Ideal.Quotient.mk _ y) ∈
        BEI.augIdealReduced (K := K) G
      -- y ∈ augIdeal G = ker quotConstCoeff, in R_G.
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
      -- Now use: killLastPairEquiv (mk_J (mk_I p)) = killLastPairForwardPoly p.
      change killLastPairForwardPoly (K := K) G p ∈ BEI.augIdealReduced (K := K) G
      -- The polynomial forward map applied to p: write p via induction.
      -- augIdealReduced = ker quotConstCoeffReduced, so it suffices to show
      -- quotConstCoeffReduced (killLastPairForwardPoly p) = constantCoeff p
      -- provided that the constant coefficient of p is 0 (since mk_I p ∈ augIdeal).
      -- Extract the constant coefficient condition.
      have hcc : constantCoeff p = 0 := by
        -- augIdeal G = RingHom.ker quotConstCoeff; check.
        change quotConstCoeff G
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) p) = 0 at hy
        simpa [quotConstCoeff] using hy
      -- Now show killLastPairForwardPoly p has zero reduced constant coefficient.
      have key : BEI.quotConstCoeffReduced G (killLastPairForwardPoly (K := K) G p) = 0 := by
        -- Both sides are ring homs applied to p; check they agree (and that composition
        -- equals constantCoeff on MvPolynomial side).
        -- Approach: show `(quotConstCoeffReduced G) ∘ killLastPairForwardPoly = constantCoeff`.
        suffices h : ((BEI.quotConstCoeffReduced G).comp
            (killLastPairForwardPoly (K := K) G).toRingHom) p = constantCoeff p by
          have : BEI.quotConstCoeffReduced G (killLastPairForwardPoly (K := K) G p) =
              constantCoeff p := h
          rw [this, hcc]
        -- This reduces to showing the compositions agree on generators.
        -- aeval_unique pattern: both are ring homs MvPol → K agreeing on all X v and C c.
        refine congrFun (congrArg DFunLike.coe
          (MvPolynomial.ringHom_ext (f := ((BEI.quotConstCoeffReduced G).comp
            (killLastPairForwardPoly (K := K) G).toRingHom))
            (g := (constantCoeff :
              MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K →+* K))
            ?_ ?_)) p
        · intro c
          -- Left: C c → killLastPairForwardPoly (C c) = C c in reducedHHRing → K.
          -- Both give c.
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
          rw [show killLastPairForwardPoly (K := K) G (C c) =
              algebraMap K _ c from (killLastPairForwardPoly (K := K) G).commutes c]
          change BEI.quotConstCoeffReduced G
              (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (C c)) = _
          unfold BEI.quotConstCoeffReduced
          rw [Ideal.Quotient.lift_mk]
          simp
        · intro v
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
          change BEI.quotConstCoeffReduced G
              (killLastPairForwardPoly (K := K) G (X v)) = constantCoeff (X v)
          change BEI.quotConstCoeffReduced G
              (aeval (killLastPairForwardVar (K := K) (G := G)) (X v)) = _
          rw [aeval_X, constantCoeff_X]
          -- Now compute: quotConstCoeffReduced (killLastPairForwardVar v) = 0.
          cases v with
          | inl i =>
            rcases i with ⟨iv, hiv⟩
            by_cases h : iv < r
            · simp only [killLastPairForwardVar, h, dif_pos]
              change BEI.quotConstCoeffReduced G
                (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X _)) = 0
              unfold BEI.quotConstCoeffReduced
              rw [Ideal.Quotient.lift_mk]
              simp
            · simp only [killLastPairForwardVar, h, dif_neg, not_false_eq_true]
              rfl
          | inr i =>
            rcases i with ⟨iv, hiv⟩
            by_cases h : iv < r
            · simp only [killLastPairForwardVar, h, dif_pos]
              change BEI.quotConstCoeffReduced G
                (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) (X _)) = 0
              unfold BEI.quotConstCoeffReduced
              rw [Ideal.Quotient.lift_mk]
              simp
            · simp only [killLastPairForwardVar, h, dif_neg, not_false_eq_true]
              rfl
      -- Conclude.
      change killLastPairForwardPoly (K := K) G p ∈
        RingHom.ker (BEI.quotConstCoeffReduced G)
      exact key
    | zero =>
      change (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom 0 ∈
        BEI.augIdealReduced (K := K) G
      rw [map_zero]; exact (BEI.augIdealReduced (K := K) G).zero_mem
    | add x y _ _ hxi hyi =>
      change (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom (x + y) ∈
        BEI.augIdealReduced (K := K) G
      rw [map_add]; exact (BEI.augIdealReduced (K := K) G).add_mem hxi hyi
    | smul a x _ hxi =>
      change (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom (a • x) ∈
        BEI.augIdealReduced (K := K) G
      rw [smul_eq_mul, map_mul]
      exact (BEI.augIdealReduced (K := K) G).mul_mem_left _ hxi
  · -- `⊇`: every generator of augIdealReduced comes from something in augIdealQuot.
    -- Simpler: since killLastPairEquiv is bijective, for any x ∈ augIdealReduced, let y :=
    -- (killLastPairEquiv G).symm x. Show y ∈ augIdealQuot G.
    intro x hx
    rw [Ideal.mem_map_iff_of_surjective
      (f := (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom)
      (hf := (killLastPairEquiv (K := K) G).surjective)]
    -- Take preimage under the iso.
    refine ⟨(killLastPairEquiv (K := K) G).symm x, ?_, by simp⟩
    -- Now show (killLastPairEquiv G).symm x ∈ augIdealQuot.
    -- It equals `killLastPairBackward (K := K) G x`. Use the backward version.
    -- Strategy: lift x ∈ augIdealReduced back through reducedHHRing G.
    -- Write x = mk_I q for some q : MvPol (BinomialEdgeVars (Fin r)) K with
    -- constantCoeff q = 0. Then backward sends this to mk_J (mk_I (aeval castSucc q)).
    -- Show constantCoeff of aeval castSucc q is 0 → the image lies in augIdealQuot.
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hcc : constantCoeff q = 0 := by
      simp only [BEI.augIdealReduced, RingHom.mem_ker] at hx
      unfold BEI.quotConstCoeffReduced at hx
      rw [Ideal.Quotient.lift_mk] at hx
      exact hx
    -- (killLastPairEquiv G).symm (mk_I q) = killLastPairBackward G (mk_I q) =
    -- killLastPairBackwardPoly q = mk_J (mk_I (aeval castSucc-eval q)).
    change (killLastPairEquiv (K := K) G).symm
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) q) ∈ augIdealQuot (K := K) G
    -- killLastPairEquiv.symm = killLastPairBackward (by AlgEquiv.ofAlgHom.symm).
    have hsymm : (killLastPairEquiv (K := K) G).symm
      (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) q) =
      killLastPairBackward (K := K) G
        (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G) q) := rfl
    rw [hsymm, killLastPairBackward_apply_mk]
    change killLastPairBackwardPoly (K := K) G q ∈ augIdealQuot (K := K) G
    -- Now show this.
    -- augIdealQuot = map mk_J of augIdeal = map mk_J of (map mk_I of (ker constantCoeff)).
    -- So it suffices to show: there is some p : MvPol (Fin (r+1)) with constantCoeff p = 0
    -- and killLastPairBackwardPoly q = mk_J (mk_I p).
    -- Choose p = killLastPairInjPoly q — the polynomial obtained by applying castSucc to
    -- the variables of q. Then constantCoeff commutes with this renaming.
    -- Concretely: killLastPairBackwardPoly q is defined as aeval (killLastPairBackwardVar G) q.
    -- Its value on a basis element X v = mk_J (mk_I (X (inj v))).
    -- We can write killLastPairBackwardPoly q = mk_J (mk_I (rename inj q)) where
    -- inj = Sum.map castSucc castSucc. Then constantCoeff (rename inj q) = constantCoeff q = 0.
    -- Define the injection map.
    let inj : BinomialEdgeVars (Fin r) → BinomialEdgeVars (Fin (r + 1))
      | Sum.inl i => Sum.inl i.castSucc
      | Sum.inr i => Sum.inr i.castSucc
    -- Show killLastPairBackwardPoly q = mk_J (mk_I (rename inj q)).
    have hrename : killLastPairBackwardPoly (K := K) G q =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (rename inj q)) := by
      -- Both sides are ring homs from MvPol (BinomialEdgeVars (Fin r)) K.
      refine congrFun (congrArg DFunLike.coe
        (MvPolynomial.ringHom_ext
          (f := (killLastPairBackwardPoly (K := K) G).toRingHom)
          (g := ((Ideal.Quotient.mk _).comp
            ((Ideal.Quotient.mk _).comp (rename inj).toRingHom)))
          ?_ ?_)) q
      · intro c
        change killLastPairBackwardPoly (K := K) G (C c) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (rename inj (C c)))
        rw [rename_C]
        rw [show killLastPairBackwardPoly (K := K) G (C c) = algebraMap K _ c from
          (killLastPairBackwardPoly (K := K) G).commutes c]
        rfl
      · intro v
        change killLastPairBackwardPoly (K := K) G (X v) =
          Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (rename inj (X v)))
        rw [rename_X]
        change aeval (killLastPairBackwardVar (K := K) G) (X v) = _
        rw [aeval_X]
        cases v with
        | inl i => rfl
        | inr i => rfl
    rw [hrename]
    -- Show mk_J (mk_I (rename inj q)) ∈ augIdealQuot = map mk_J of augIdeal.
    unfold augIdealQuot
    refine Ideal.mem_map_of_mem _ ?_
    -- mk_I (rename inj q) ∈ augIdeal G.
    change quotConstCoeff G
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (rename inj q)) = 0
    simp [quotConstCoeff, constantCoeff_rename, hcc]

/-! ##### Step 3: Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot -/

/-- The map `augIdeal G = augIdealQuot.comap (Quotient.mk killLastPairIdeal)`.
This is the comap compatibility needed for `Localization.localRingHom`. -/
private lemma augIdeal_eq_comap_augIdealQuot
    (G : SimpleGraph (Fin (r + 1))) :
    augIdeal (K := K) G =
      (augIdealQuot (K := K) G).comap
        (Ideal.Quotient.mk (killLastPairIdeal (K := K) G)) := by
  unfold augIdealQuot
  -- augIdeal ⊆ augIdealQuot.comap mk_J follows from Ideal.le_comap_map.
  -- Reverse: augIdealQuot.comap mk_J ≤ augIdeal using killLastPairIdeal ⊆ augIdeal
  -- together with Ideal.comap_map_of_surjective.
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
  -- Now goal: augIdeal = augIdeal ⊔ comap (Quotient.mk _) ⊥. comap(mk, ⊥) = killLastPairIdeal.
  have hcomap : Ideal.comap (Ideal.Quotient.mk (killLastPairIdeal (K := K) G)) ⊥
      = killLastPairIdeal (K := K) G := by
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  rw [hcomap]
  -- Need: augIdeal = augIdeal ⊔ killLastPairIdeal, i.e., killLastPairIdeal ≤ augIdeal.
  apply le_antisymm
  · exact le_sup_left
  · refine sup_le le_rfl ?_
    -- killLastPairIdeal = span {mk(X(inl r)), mk(X(inr r))} ⊆ augIdeal.
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact mkI_X_mem_augIdeal G _
    · exact mkI_X_mem_augIdeal G _

/-- The `localRingHom` from `Rp = Localization.AtPrime (augIdeal G)` to
`Localization.AtPrime (augIdealQuot G)`, lifted from the quotient map
`R_G → R_G ⧸ killLastPairIdeal G`. -/
private noncomputable def quotLocalRingHom
    (G : SimpleGraph (Fin (r + 1))) :
    Localization.AtPrime (augIdeal (K := K) G) →+*
      Localization.AtPrime (augIdealQuot (K := K) G) :=
  Localization.localRingHom (augIdeal (K := K) G) (augIdealQuot (K := K) G)
    (Ideal.Quotient.mk (killLastPairIdeal (K := K) G))
    (augIdeal_eq_comap_augIdealQuot G)

/-- `quotLocalRingHom` applied to the image of a polynomial in `R_G` under `algebraMap R_G Rp`
factors as `algebraMap (R_G/J) (Localization.AtPrime augIdealQuot) ∘ (Quotient.mk J)`. -/
private lemma quotLocalRingHom_algebraMap
    (G : SimpleGraph (Fin (r + 1)))
    (x : MvPolynomial (BinomialEdgeVars (Fin (r + 1))) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :
    quotLocalRingHom (G := G) (algebraMap _ _ x) =
    algebraMap _ (Localization.AtPrime (augIdealQuot (K := K) G))
      (Ideal.Quotient.mk (killLastPairIdeal (K := K) G) x) := by
  simp [quotLocalRingHom, Localization.localRingHom_to_map]

set_option maxHeartbeats 400000 in
-- heartbeats needed to elaborate the composed quotient/localization ring hom.
/-- The `localRingHom` kills `span{xL, yL}`: both last-pair images map to 0
under `R_G → R_G ⧸ killLastPairIdeal → Localization.AtPrime augIdealQuot`. -/
private lemma quotLocalRingHom_kills_lastPair
    (G : SimpleGraph (Fin (r + 1))) :
    Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨r, lt_add_one r⟩))),
      algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
      Set (Localization.AtPrime (augIdeal (K := K) G))) ≤
      RingHom.ker (quotLocalRingHom (G := G)) := by
  apply Ideal.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  rcases hx with rfl | rfl
  · rw [quotLocalRingHom_algebraMap]
    have h0 : Ideal.Quotient.mk (killLastPairIdeal (K := K) G)
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨r, lt_add_one r⟩))) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by left; rfl)
    rw [h0, map_zero]
  · rw [quotLocalRingHom_algebraMap]
    have h0 : Ideal.Quotient.mk (killLastPairIdeal (K := K) G)
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨r, lt_add_one r⟩))) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by right; rfl)
    rw [h0, map_zero]

/-- The forward map `Rp ⧸ span{xL, yL} → Localization.AtPrime augIdealQuot`, obtained
by factoring `quotLocalRingHom` through the quotient. -/
private noncomputable def RpModLastPairToLoc
    (G : SimpleGraph (Fin (r + 1))) :
    ((Localization.AtPrime (augIdeal (K := K) G)) ⧸
        Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨r, lt_add_one r⟩))),
        algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inr ⟨r, lt_add_one r⟩)))})) →+*
      Localization.AtPrime (augIdealQuot (K := K) G) :=
  Ideal.Quotient.lift _ (quotLocalRingHom (G := G))
    (fun a ha => by
      have := quotLocalRingHom_kills_lastPair (G := G) ha
      simpa [RingHom.mem_ker] using this)

/-- Surjectivity of `RpModLastPairToLoc`: every element of the target is in the image. -/
private lemma RpModLastPairToLoc_surjective
    (G : SimpleGraph (Fin (r + 1))) :
    Function.Surjective (RpModLastPairToLoc (K := K) (G := G)) := by
  intro y
  -- y ∈ Localization.AtPrime augIdealQuot, write y = mk'(r_bar, s_bar) with
  -- r_bar ∈ R_G/J, s_bar ∈ augIdealQuot.primeCompl.
  -- Lift to R_G: r_bar = mk_J r, s_bar = mk_J s with s ∉ augIdeal G.
  obtain ⟨⟨r_bar, s_bar⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (augIdealQuot (K := K) G).primeCompl y
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r_bar
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (s_bar : _ ⧸ killLastPairIdeal (K := K) G)
  -- Check s ∉ augIdeal G.
  have hs_ne : s ∉ augIdeal (K := K) G := by
    intro hmem
    -- s_bar.prop : s_bar ∉ augIdealQuot (i.e., s_bar ∈ primeCompl).
    -- But s ∈ augIdeal implies mk_J s ∈ augIdealQuot, and mk_J s = s_bar.
    have : (s_bar : _ ⧸ killLastPairIdeal (K := K) G) ∈ augIdealQuot (K := K) G := by
      rw [← hs]; exact Ideal.mem_map_of_mem _ hmem
    exact s_bar.prop this
  -- So s ∈ augIdeal.primeCompl; let s_Rp := mk'(1, s) as element ∈ Rp.
  -- Then s is a unit in Rp. Use mk'(r, s) ∈ Rp.
  let s' : (augIdeal (K := K) G).primeCompl := ⟨s, hs_ne⟩
  refine ⟨Ideal.Quotient.mk _ (IsLocalization.mk' _ r s'), ?_⟩
  -- Show this maps to the right element.
  change RpModLastPairToLoc (G := G)
    (Ideal.Quotient.mk _ (IsLocalization.mk' _ r s')) =
    IsLocalization.mk' _ _ s_bar
  unfold RpModLastPairToLoc
  rw [Ideal.Quotient.lift_mk]
  change quotLocalRingHom (G := G) (IsLocalization.mk' _ r s') = _
  rw [quotLocalRingHom, Localization.localRingHom_mk']
  -- Now the two sides should match up.
  congr 1
  exact Subtype.ext hs

/-- Injectivity of `RpModLastPairToLoc`. -/
private lemma RpModLastPairToLoc_injective
    (G : SimpleGraph (Fin (r + 1))) :
    Function.Injective (RpModLastPairToLoc (K := K) (G := G)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  -- x = mk_span y for some y : Rp.
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- y = mk'(p, s) with p : R_G, s ∈ augIdeal.primeCompl.
  obtain ⟨⟨p, s⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (augIdeal (K := K) G).primeCompl y
  -- hx says quotLocalRingHom (mk' p s) = 0, i.e., mk' (mk_J p) (mk_J s) = 0 in target.
  -- That means there's t ∈ augIdealQuot.primeCompl with t * (mk_J p) = 0, i.e.,
  -- t * (mk_J p) = 0 in R_G/J, i.e., t * p ∈ killLastPairIdeal.
  -- Then: in R_G, we have t * p ∈ killLastPairIdeal. Take preimage t0 of t with t0 ∉ augIdeal.
  -- Then mk'(p, s) is equivalent (in Rp) to something whose t0-multiple is in killLastPair
  -- map, which means it's in span{xL, yL}.
  have hx' : RpModLastPairToLoc (G := G)
    (Ideal.Quotient.mk _ (IsLocalization.mk' _ p s)) = 0 := hx
  unfold RpModLastPairToLoc at hx'
  rw [Ideal.Quotient.lift_mk] at hx'
  rw [quotLocalRingHom, Localization.localRingHom_mk'] at hx'
  -- Now hx' : mk' _ (mk_J p) (mk_J s) = 0. Use IsLocalization.mk'_eq_zero_iff.
  rw [IsLocalization.mk'_eq_zero_iff] at hx'
  obtain ⟨⟨t_bar, ht_bar⟩, ht⟩ := hx'
  simp only at ht
  -- t_bar ∈ augIdealQuot.primeCompl, t_bar * mk_J p = 0 in R_G/J.
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t_bar
  -- t ∉ augIdeal (since t_bar ∉ augIdealQuot via Ideal.mem_map comap compat).
  have ht_ne : t ∉ augIdeal (K := K) G := by
    intro hmem
    apply ht_bar
    exact Ideal.mem_map_of_mem _ hmem
  -- ht : mk_J t * mk_J p = 0, i.e., mk_J (t * p) = 0, i.e., t * p ∈ killLastPairIdeal.
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ht
  -- Now: mk_J (t*p) ∈ killLastPairIdeal means (t * p) ∈ killLastPairIdeal.
  -- Goal: mk_span (mk'(p, s)) = 0, i.e., mk'(p, s) ∈ span{xL, yL}.
  rw [Ideal.Quotient.eq_zero_iff_mem]
  -- mk'(p, s) = alg(p) * alg(s)⁻¹, and alg(p) * alg(t) ∈ span{xL, yL} (since t*p ∈ killLastPair).
  -- So: mk'(p, s) = alg(t)⁻¹ * alg(p) * alg(s)⁻¹ * alg(t) = alg(t*p) * (alg(s))⁻¹ * alg(t)⁻¹,
  -- and alg(t*p) ∈ span{xL, yL}.
  -- Since t ∉ augIdeal, alg(t) is a unit.
  have ht_unit : IsUnit (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G)) t) := by
    apply IsLocalization.map_units _ (⟨t, ht_ne⟩ : (augIdeal (K := K) G).primeCompl)
  -- Now: mk'(p, s) * alg(t) = mk'(p * t, s) = mk'(t * p, s) ∈ alg(killLastPairIdeal).span.
  have key : IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s *
      algebraMap _ _ t ∈
      Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inl ⟨r, lt_add_one r⟩))),
      algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
      Set (Localization.AtPrime (augIdeal (K := K) G))) := by
    -- mk'(p, s) * alg(t) = alg(t) * mk'(p, s) = mk'(t*p, s) = alg(t*p) * alg(s)⁻¹.
    have h1 : IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s *
        algebraMap _ _ t =
        IsLocalization.mk' _ (t * p) s := by
      rw [mul_comm]
      exact IsLocalization.mul_mk'_eq_mk'_of_mul t p s
    rw [h1]
    -- Now show mk' (t*p) s ∈ span{xL, yL}.
    -- alg (t * p) ∈ span, and mk'(x, s) = alg(x) * alg(s)⁻¹. So mk'(t*p, s) is in span iff
    -- alg(t*p) is (since units preserve the span).
    have halg : algebraMap _ (Localization.AtPrime (augIdeal (K := K) G)) (t * p) ∈
        Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨r, lt_add_one r⟩))),
        algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
        Set (Localization.AtPrime (augIdeal (K := K) G))) := by
      -- (t * p) ∈ killLastPairIdeal. killLastPairIdeal = span{mk(X(inl r)), mk(X(inr r))}.
      -- So (t * p) is an R_G-linear combination of those. alg preserves this.
      have hmap : Ideal.map (algebraMap _ (Localization.AtPrime (augIdeal (K := K) G)))
          (killLastPairIdeal (K := K) G) ≤
          Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
            (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
              (X (Sum.inl ⟨r, lt_add_one r⟩))),
          algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
            (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
              (X (Sum.inr ⟨r, lt_add_one r⟩)))} :
          Set (Localization.AtPrime (augIdeal (K := K) G))) := by
        unfold killLastPairIdeal
        rw [Ideal.map_span]
        apply Ideal.span_le.mpr
        intro z hz
        simp only [Set.image_insert_eq, Set.image_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Ideal.subset_span (by left; rfl)
        · exact Ideal.subset_span (by right; rfl)
      exact hmap (Ideal.mem_map_of_mem _ ht)
    -- Now mk'(t*p, s) = alg(t*p) * alg(s)⁻¹ (via mk'_eq_mul_mk'_one or similar).
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ halg
  -- Since alg(t) is a unit, mk'(p,s) ∈ span{xL,yL}.
  obtain ⟨u, hu⟩ := ht_unit
  change IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s ∈ _
  have hmk'_eq : IsLocalization.mk' (Localization.AtPrime (augIdeal (K := K) G)) p s =
      (IsLocalization.mk' _ p s * algebraMap _ _ t) * ↑u⁻¹ := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [hmk'_eq]
  exact Ideal.mul_mem_right _ _ key

/-- The ring equiv `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot`. -/
private noncomputable def RpModLastPairEquivLoc
    (G : SimpleGraph (Fin (r + 1))) :
    ((Localization.AtPrime (augIdeal (K := K) G)) ⧸
        Ideal.span ({algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inl ⟨r, lt_add_one r⟩))),
        algebraMap _ (Localization.AtPrime (augIdeal (K := K) G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
            (X (Sum.inr ⟨r, lt_add_one r⟩)))})) ≃+*
      Localization.AtPrime (augIdealQuot (K := K) G) :=
  RingEquiv.ofBijective (RpModLastPairToLoc (G := G))
    ⟨RpModLastPairToLoc_injective G, RpModLastPairToLoc_surjective G⟩

/-! ##### Step 4: `Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced` -/

/-- The image of `augIdealQuot.primeCompl` under `killLastPairEquiv` is
`augIdealReduced.primeCompl`. -/
private lemma killLastPairEquiv_map_primeCompl
    (G : SimpleGraph (Fin (r + 1))) :
    (augIdealQuot (K := K) G).primeCompl.map
        (killLastPairEquiv (K := K) G).toRingEquiv.toMonoidHom =
      (BEI.augIdealReduced (K := K) G).primeCompl := by
  ext x
  simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro hxI
    apply hy
    have hmap := killLastPairEquiv_map_augIdealQuot (K := K) G
    -- hxI : killLastPairEquiv y ∈ augIdealReduced. Use hmap to convert.
    -- killLastPairEquiv y = (equiv).toMonoidHom y, which is the same as
    -- (equiv).toRingEquiv.toRingHom y.
    have hxI' : (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom y ∈
        (augIdealQuot (K := K) G).map
          (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom := by
      rw [hmap]; exact hxI
    rw [Ideal.mem_map_iff_of_surjective
        ((killLastPairEquiv (K := K) G).toRingEquiv.toRingHom)
        (killLastPairEquiv (K := K) G).surjective] at hxI'
    obtain ⟨z, hz, hyeq⟩ := hxI'
    have : z = y := (killLastPairEquiv (K := K) G).injective hyeq
    subst this
    exact hz
  · intro hx
    refine ⟨(killLastPairEquiv (K := K) G).symm x, ?_, ?_⟩
    · intro hyI
      apply hx
      have hmap := killLastPairEquiv_map_augIdealQuot (K := K) G
      -- From hyI : (equiv).symm x ∈ augIdealQuot, get (equiv) ((equiv).symm x) = x
      -- is in augIdealReduced.
      have hstep : (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom
          ((killLastPairEquiv (K := K) G).symm x) ∈ BEI.augIdealReduced (K := K) G := by
        rw [← hmap]; exact Ideal.mem_map_of_mem _ hyI
      -- (equiv).toRingEquiv.toRingHom v = (equiv) v by defn; then apply_symm_apply.
      have hcoe : (killLastPairEquiv (K := K) G).toRingEquiv.toRingHom
          ((killLastPairEquiv (K := K) G).symm x) = x := by
        change (killLastPairEquiv (K := K) G) ((killLastPairEquiv (K := K) G).symm x) = x
        exact (killLastPairEquiv (K := K) G).apply_symm_apply x
      rwa [hcoe] at hstep
    · exact (killLastPairEquiv (K := K) G).apply_symm_apply x

/-- The ring equiv between localisations at corresponding primes, transported through
`killLastPairEquiv` via `IsLocalization.ringEquivOfRingEquiv`. -/
private noncomputable def locAugIdealQuotEquivLocAugIdealReduced
    (G : SimpleGraph (Fin (r + 1))) :
    Localization.AtPrime (augIdealQuot (K := K) G) ≃+*
      Localization.AtPrime (BEI.augIdealReduced (K := K) G) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := (augIdealQuot (K := K) G).primeCompl)
    (T := (BEI.augIdealReduced (K := K) G).primeCompl)
    (Localization.AtPrime (augIdealQuot (K := K) G))
    (Localization.AtPrime (BEI.augIdealReduced (K := K) G))
    (killLastPairEquiv (K := K) G).toRingEquiv
    (killLastPairEquiv_map_primeCompl G)

/-! ##### Assembly: `isCohenMacaulayLocalRing_at_augIdealReduced_step` -/

set_option maxHeartbeats 800000 in
-- heartbeats needed: assembly over iterated quotients + localizations.
/-- **Inductive case** (`r ≥ 1`): Bridge from L5's CM conclusion
`IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ)` to CM of
`Localization.AtPrime (augIdealReduced G)`. Uses the 4-step ring-iso chain:
1. `QuotSMulTop mkyL RpQ ≃+* RpQ ⧸ span{mkyL}` (existing bridge).
2. `RpQ ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}` (DoubleQuot).
3. `Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot` (Step 3).
4. `Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced` (Step 4).
-/
private theorem isCohenMacaulayLocalRing_at_augIdealReduced_step
    {r : ℕ} (hr : 1 ≤ r) {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := by
  -- Introduce notations matching the L5 output.
  set Rp := Localization.AtPrime (augIdeal (K := K) G) with Rp_def
  -- L5's n = r + 1; hn : 2 ≤ r + 1 from hr : 1 ≤ r.
  have hn : 2 ≤ r + 1 := by omega
  -- The bipartite-edge ring element `X(inl ⟨r, _⟩)` is the last x.
  -- L5 uses `⟨(r + 1) - 1, _⟩ = ⟨r, _⟩`.
  have hrr1 : (r + 1) - 1 = r := by omega
  set xL : Rp := algebraMap _ Rp
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inl ⟨r, lt_add_one r⟩))) with xL_def
  set yL : Rp := algebraMap _ Rp
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inr ⟨r, lt_add_one r⟩))) with yL_def
  -- L5 notation uses ⟨(r+1)-1, _⟩, which is definitionally ⟨r, _⟩ after hrr1.
  -- We need to convert between the two forms to apply L5.
  have hbd : (r + 1) - 1 < r + 1 := by omega
  have hFin : (⟨r, lt_add_one r⟩ : Fin (r + 1)) = ⟨(r + 1) - 1, hbd⟩ :=
    Fin.ext hrr1.symm
  have hFin' : (⟨(r + 1) - 1, hbd⟩ : Fin (r + 1)) = ⟨r, lt_add_one r⟩ := Fin.ext hrr1
  have h_xL_eq : xL = algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl ⟨(r + 1) - 1, hbd⟩))) := by
    rw [hFin', xL_def]
  have h_yL_eq : yL = algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr ⟨(r + 1) - 1, hbd⟩))) := by
    rw [hFin', yL_def]
  -- Apply L5 to get CM of QuotSMulTop mkyL RpQ.
  have hL5 := isCohenMacaulayLocalRing_reducedHH_at_augIdeal (K' := K) hn hHH
  -- hL5's xL, yL, RpQ, mkyL definitions match ours modulo the (r+1)-1 = r issue.
  -- Transfer through the form match via `xL_eq, yL_eq`.
  set RpQ := Rp ⧸ Ideal.span {xL} with RpQ_def
  set mkyL : RpQ := Ideal.Quotient.mk (Ideal.span {xL}) yL with mkyL_def
  have hCM_L5 : IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ) := by
    -- L5 gives CM of QuotSMulTop (at (r+1)-1 form). Convert.
    convert hL5 using 3
  -- Hoisted membership / non-top facts used across Steps 1, 2, 2'.
  have hxLmem : xL ∈ IsLocalRing.maximalIdeal Rp :=
    X_inl_last_mem_maximalIdeal (K := K) (by omega) G
  have hyLmem : yL ∈ IsLocalRing.maximalIdeal Rp :=
    X_inr_last_mem_maximalIdeal (K := K) (by omega) G
  have hne_sup : Ideal.span {xL} ⊔ Ideal.span {yL} ≠ ⊤ := by
    intro htop
    have hle : Ideal.span {xL} ⊔ Ideal.span {yL} ≤ IsLocalRing.maximalIdeal Rp :=
      sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hxLmem)
             ((Ideal.span_singleton_le_iff_mem _).mpr hyLmem)
    exact (IsLocalRing.maximalIdeal.isMaximal Rp).ne_top (top_le_iff.mp (htop ▸ hle))
  haveI : IsLocalRing RpQ := by
    haveI : Nontrivial RpQ := Ideal.Quotient.nontrivial_iff.mpr
      (span_x_inl_last_ne_top (K := K) (by omega) G)
    exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmem_max : mkyL ∈ IsLocalRing.maximalIdeal RpQ := by
    haveI : IsLocalHom (Ideal.Quotient.mk (Ideal.span {xL})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    apply (IsLocalRing.mem_maximalIdeal _).mp hyLmem
    exact (isUnit_map_iff (Ideal.Quotient.mk (Ideal.span {xL})) yL).mp hunit
  -- Step 1: QuotSMulTop mkyL RpQ ≃+* RpQ ⧸ span{mkyL}.
  have hstep1 : IsCohenMacaulayLocalRing (RpQ ⧸ Ideal.span {mkyL}) := by
    haveI := quotSMulTopLocalRing hmem_max
    haveI := hCM_L5
    haveI : Nontrivial (RpQ ⧸ Ideal.span {mkyL}) :=
      Ideal.Quotient.nontrivial_iff.mpr (by
        rw [Ne, Ideal.span_singleton_eq_top]
        exact (IsLocalRing.mem_maximalIdeal _).mp hmem_max)
    haveI : IsLocalRing (RpQ ⧸ Ideal.span {mkyL}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact isCohenMacaulayLocalRing_of_ringEquiv' hCM_L5
      (quotSMulTopRingEquivIdealQuotient mkyL)
  -- Step 2: RpQ ⧸ span{mkyL} ≃+* Rp ⧸ span{xL, yL}.
  have hstep2 : IsCohenMacaulayLocalRing
      (Rp ⧸ (Ideal.span {xL} ⊔ Ideal.span {yL})) := by
    -- span{mkyL} = span{yL}.map(Quotient.mk (span{xL})), so DoubleQuot.quotQuotEquivQuotSup
    -- gives (Rp ⧸ span{xL}) ⧸ span{mkyL} ≃+* Rp ⧸ (span{xL} ⊔ span{yL}).
    have hmap : (Ideal.span {yL}).map (Ideal.Quotient.mk (Ideal.span {xL})) =
        Ideal.span {mkyL} := by
      rw [Ideal.map_span, Set.image_singleton]
    haveI : Nontrivial (Rp ⧸ (Ideal.span {xL} ⊔ Ideal.span {yL})) :=
      Ideal.Quotient.nontrivial_iff.mpr hne_sup
    haveI : IsLocalRing (Rp ⧸ (Ideal.span {xL} ⊔ Ideal.span {yL})) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact isCohenMacaulayLocalRing_of_ringEquiv' hstep1
      ((Ideal.quotEquivOfEq hmap.symm).trans (DoubleQuot.quotQuotEquivQuotSup _ _))
  -- Step 2.5: span{xL} ⊔ span{yL} = span{xL, yL} (set equality).
  have hsup_eq : Ideal.span {xL} ⊔ Ideal.span {yL} =
      Ideal.span ({xL, yL} : Set Rp) := by
    rw [show ({xL, yL} : Set Rp) = {xL} ∪ {yL} from Set.insert_eq _ _,
      Ideal.span_union]
  have hstep2' : IsCohenMacaulayLocalRing
      (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) := by
    haveI : Nontrivial (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) :=
      Ideal.Quotient.nontrivial_iff.mpr (hsup_eq ▸ hne_sup)
    haveI : IsLocalRing (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    exact isCohenMacaulayLocalRing_of_ringEquiv' hstep2 (Ideal.quotEquivOfEq hsup_eq)
  -- Step 3: Rp ⧸ span{xL, yL} ≃+* Localization.AtPrime augIdealQuot.
  have hstep3 : IsCohenMacaulayLocalRing
      (Localization.AtPrime (augIdealQuot (K := K) G)) := by
    haveI : IsLocalRing (Rp ⧸ Ideal.span ({xL, yL} : Set Rp)) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : IsLocalRing (Localization.AtPrime (augIdealQuot (K := K) G)) :=
      inferInstance
    exact isCohenMacaulayLocalRing_of_ringEquiv' hstep2' (RpModLastPairEquivLoc G)
  -- Step 4: Localization.AtPrime augIdealQuot ≃+* Localization.AtPrime augIdealReduced.
  haveI : IsLocalRing (Localization.AtPrime (augIdealQuot (K := K) G)) := inferInstance
  haveI : IsLocalRing (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := inferInstance
  exact isCohenMacaulayLocalRing_of_ringEquiv' hstep3
    (locAugIdealQuotEquivLocAugIdealReduced G)

/-- **Combined** inductive + base case: CM of `Localization.AtPrime (augIdealReduced G)`
for any HH graph `G` on `Fin (r + 1)`. -/
private theorem isCohenMacaulayLocalRing_at_augIdealReduced
    {r : ℕ} {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayLocalRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := by
  by_cases hr : r = 0
  · subst hr
    exact isCohenMacaulayLocalRing_at_augIdealReduced_base (K := K) G
  · exact isCohenMacaulayLocalRing_at_augIdealReduced_step (K := K)
      (by omega) hHH

/-! #### Session B: promote local CM at `augIdealReduced` to global CM. -/

/-- **Session B**: The localisation of the reduced HH ring at its augmentation
ideal is globally Cohen–Macaulay. Immediate from Session A′ and
`IsCohenMacaulayRing.of_isCohenMacaulayLocalRing`. -/
private theorem isCohenMacaulayRing_at_augIdealReduced
    {r : ℕ} {G : SimpleGraph (Fin (r + 1))}
    (hHH : HerzogHibiConditions (r + 1) G) :
    IsCohenMacaulayRing
      (Localization.AtPrime (BEI.augIdealReduced (K := K) G)) := by
  haveI := isCohenMacaulayLocalRing_at_augIdealReduced (K := K) hHH
  exact IsCohenMacaulayRing.of_isCohenMacaulayLocalRing

/-! #### Session C1: the bundled equiv `E_U`.

Composing `L1Iso`, `L4Iso`, the tensor associator, and `polynomialAwayTensorEquiv`,
we obtain a single K-algebra equivalence from the monomial localisation of the
HH quotient at `s_U` to
`reducedHHRing G' ⊗[K] Localization.Away (rename Sum.inr (hhUnitProductSub U))`,
where `G' = smallerHHGraph G (↑U)` and the `Sum.inr` embeds the `U`-index into
`↑(lambdaSet G (↑U)) ⊕ ↑(U : Set _)`. -/
set_option maxHeartbeats 400000 in
-- heartbeats needed: E_U is a 4-step AlgEquiv composition over heavy types.
/-- **Session C1: the bundled monomial-localisation equiv `E_U`** for an
independent finset `U`. Specialised to `K : Type` (universe 0) so that it can
be composed with `polynomialAwayTensorEquiv`, which requires all type arguments
in a single universe. All downstream callers instantiate `K` at universe 0. -/
private noncomputable def E_U {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _)) :
    Localization.Away
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
          (hhUnitProduct U))
      ≃ₐ[K]
      TensorProduct K
        (BEI.reducedHHRing (K := K) (smallerHHGraph G (U : Set _)))
        (Localization.Away
          (rename (R := K)
            (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
            (τ := ↑(lambdaSet G (U : Set _)) ⊕
              ↑((U : Set (BinomialEdgeVars (Fin n)))))
            Sum.inr
            (hhUnitProductSub (K := K) U))) := by
  classical
  -- Abbreviations for readability and to pin down types for typeclass search.
  let Uset : Set (BinomialEdgeVars (Fin n)) := ↑U
  let G' := smallerHHGraph G Uset
  let Λ : Set (BinomialEdgeVars (Fin n)) := lambdaSet G Uset
  let A := BEI.reducedHHRing (K := K) G'
  let P := MvPolynomial (↑Λ) K
  let Lsub := Localization.Away (hhUnitProductSub (K := K) U)
  -- Step 1: L1 iso.
  refine (L1Iso (K := K) G U hU).trans ?_
  -- Step 2: apply L4Iso to the left tensor factor.
  refine (Algebra.TensorProduct.congr
      (L4Iso (K := K) hHH Uset hU)
      (AlgEquiv.refl (R := K) (A₁ := Lsub))).trans ?_
  -- Step 3: reassociate the triple tensor.
  refine (Algebra.TensorProduct.assoc K K K A P Lsub).trans ?_
  -- Step 4: merge the polynomial factor with the localisation.
  exact Algebra.TensorProduct.congr
    (AlgEquiv.refl (R := K) (A₁ := A))
    (polynomialAwayTensorEquiv
      (K := K) (α := (Λ : Type _))
      (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
      (hhUnitProductSub (K := K) U))

set_option maxHeartbeats 800000 in
-- heartbeats needed: E_U is a 4-step AlgEquiv.trans; unfolding its action on a
-- specific element requires elaborating nested tensor/localization types.
/-- **E_U forward on a paired-left survivor variable**.

For `a : Fin (pairedCount G U)`, the embedded index `c_a := pairedSurvivorsVal G U a`
gives a paired-left survivor `v_emb = Sum.inl c_a ∈ hhSurvivors G U`. Applying `E_U` to
the algebraMap image of `mkI (X v_emb)` yields the pure tensor
`mkI_red (X (Sum.inl a)) ⊗ 1`.

Proof: trace the 4-step composition of `E_U`:
1. `L1Iso` sends it via `L1Forward` to `(mk_W (X ⟨v_emb, hW⟩)) ⊗ 1`.
2. `Algebra.TensorProduct.congr (L4Iso …) AlgEquiv.refl` applied to the pure tensor
   gives `(L4Iso (mk_W (X ⟨v_emb, hW⟩))) ⊗ 1`; by `L4Forward_mk_X` +
   `L4ForwardGen_inl` + `L4ForwardInl_of_paired` + `pairedSurvivorsIdx_val`, the
   inner image is `(mk_red (X (Sum.inl a))) ⊗ 1`, yielding
   `((mk_red (X (Sum.inl a))) ⊗ 1) ⊗ 1`.
3. The associator sends `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`, giving
   `(mk_red (X (Sum.inl a))) ⊗ (1 ⊗ 1)`.
4. `congr refl polynomialAwayTensorEquiv` applied to a pure tensor sends
   `x ⊗ w ↦ x ⊗ (polynomialAwayTensorEquiv w)`; `polynomialAwayTensorEquiv (1 ⊗ 1) = 1`
   by `map_one`. -/
private theorem E_U_algebraMap_mkI_X_pairedSurvivor_inl
    {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : Fin (pairedCount G (U : Set _))) :
    (E_U hHH U hU) (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl (pairedSurvivorsVal G (U : Set _) a))))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
        (smallerHHGraph G (U : Set _)))) (X (Sum.inl a)))
          ⊗ₜ[K] (1 : Localization.Away
            (rename (R := K)
              (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
              (τ := ↑(lambdaSet G (U : Set _)) ⊕
                ↑((U : Set (BinomialEdgeVars (Fin n)))))
              Sum.inr
              (hhUnitProductSub (K := K) U))) := by
  classical
  set i : Fin n := pairedSurvivorsVal G (U : Set _) a with hi_def
  have hi_mem : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
  have hW : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G (U : Set _) := pairedSurvivors_inl_mem G _ hi_mem
  -- Unfold E_U as a sequence of four AlgEquiv.trans applications.
  unfold E_U
  -- Step 1: L1Iso applied to algebraMap (mkI (X (Sum.inl i))) = (mk_W X ⟨_, hW⟩) ⊗ 1.
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hStep1 : L1Iso (K := K) G U hU (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl i)))) =
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inl i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1) := by
    simp only [L1Iso, AlgEquiv.ofAlgHom_apply]
    unfold L1Forward
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change L1ForwardQuot (K := K) G U hU
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inl i))) = _
    rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W hW]
  rw [hStep1]
  -- Step 2: Algebra.TensorProduct.congr (L4Iso …) refl on a pure tensor.
  -- Compute L4Iso on (mk X ⟨Sum.inl i, hW⟩) first.
  have hi_ps : i ∈ pairedSurvivors G (U : Set _) := hi_mem
  have hidx : pairedSurvivorsIdx G (U : Set _) hi_ps = a :=
    pairedSurvivorsIdx_val G _ a
  have hStep2_inner :
      (L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inl i, hW⟩)) =
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
            (smallerHHGraph G (U : Set _))))
          (X (Sum.inl a))) ⊗ₜ[K]
          (1 : MvPolynomial (lambdaSet G (U : Set _)) K) := by
    simp only [L4Iso, AlgEquiv.ofAlgHom_apply]
    rw [L4Forward_mk_X]
    rw [L4ForwardGen_inl (K := K) hHH hU ⟨Sum.inl i, hW⟩ rfl,
      L4ForwardInl_of_paired (K := K) G (U : Set _) hW hi_ps]
    rw [hidx]
  -- Step 2: congr (L4Iso …) refl on the pure tensor (mk ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (L4Iso (K := K) hHH (U : Set _) hU)
        (AlgEquiv.refl (R := K) (A₁ := Localization.Away
          (hhUnitProductSub (K := K) U))))
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inl i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      ((L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inl i, hW⟩))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  rw [hStep2_inner]
  -- Step 3: the associator maps (x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z).
  rw [Algebra.TensorProduct.assoc_tmul]
  -- Step 4: congr refl polynomialAwayTensorEquiv on pure tensor x ⊗ (1 ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K)
        (A₁ := BEI.reducedHHRing (K := K) (smallerHHGraph G (U : Set _))))
        (polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U)))
      (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inl a))) ⊗ₜ[K]
        ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
          (1 : Localization.Away (hhUnitProductSub (K := K) U)))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inl a))) ⊗ₜ[K]
        ((polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U))
          ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
            (1 : Localization.Away (hhUnitProductSub (K := K) U))))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  -- polynomialAwayTensorEquiv (1 ⊗ 1) = polynomialAwayTensorEquiv 1 = 1.
  have h11 : ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
      (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      (1 : TensorProduct K (MvPolynomial (lambdaSet G (U : Set _)) K)
        (Localization.Away (hhUnitProductSub (K := K) U))) := rfl
  rw [h11, map_one]

set_option maxHeartbeats 800000 in
-- heartbeats needed: E_U is a 4-step AlgEquiv.trans; unfolding its action on a
-- specific element requires elaborating nested tensor/localization types.
/-- **E_U forward on a paired-right survivor variable**.

Symmetric companion to `E_U_algebraMap_mkI_X_pairedSurvivor_inl`: for
`a : Fin (pairedCount G U)`, the embedded index `c_a := pairedSurvivorsVal G U a`
gives a paired-right survivor `v_emb = Sum.inr c_a ∈ hhSurvivors G U`. Applying `E_U`
to the algebraMap image of `mkI (X v_emb)` yields the pure tensor
`mkI_red (X (Sum.inr a)) ⊗ 1`. -/
private theorem E_U_algebraMap_mkI_X_pairedSurvivor_inr
    {K : Type} [Field K]
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (U : Finset (BinomialEdgeVars (Fin n)))
    (hU : hhIndep G (U : Set _))
    (a : Fin (pairedCount G (U : Set _))) :
    (E_U hHH U hU) (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr (pairedSurvivorsVal G (U : Set _) a))))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
        (smallerHHGraph G (U : Set _)))) (X (Sum.inr a)))
          ⊗ₜ[K] (1 : Localization.Away
            (rename (R := K)
              (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
              (τ := ↑(lambdaSet G (U : Set _)) ⊕
                ↑((U : Set (BinomialEdgeVars (Fin n)))))
              Sum.inr
              (hhUnitProductSub (K := K) U))) := by
  classical
  set i : Fin n := pairedSurvivorsVal G (U : Set _) a with hi_def
  have hi_mem : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
  have hW : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G (U : Set _) := pairedSurvivors_inr_mem G _ hi_mem
  -- Unfold E_U as a sequence of four AlgEquiv.trans applications.
  unfold E_U
  -- Step 1: L1Iso applied to algebraMap (mkI (X (Sum.inr i))) = (mk_W X ⟨_, hW⟩) ⊗ 1.
  rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply]
  have hStep1 : L1Iso (K := K) G U hU (algebraMap _ _
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr i)))) =
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inr i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K] 1) := by
    simp only [L1Iso, AlgEquiv.ofAlgHom_apply]
    unfold L1Forward
    rw [IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
    change L1ForwardQuot (K := K) G U hU
      ((Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
        (X (Sum.inr i))) = _
    rw [L1ForwardQuot_mk, L1ForwardPoly_X, L1ForwardGen_of_W hW]
  rw [hStep1]
  -- Step 2: Algebra.TensorProduct.congr (L4Iso …) refl on a pure tensor.
  -- Compute L4Iso on (mk X ⟨Sum.inr i, hW⟩) first.
  have hi_ps : i ∈ pairedSurvivors G (U : Set _) := hi_mem
  have hidx : pairedSurvivorsIdx G (U : Set _) hi_ps = a :=
    pairedSurvivorsIdx_val G _ a
  have hStep2_inner :
      (L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inr i, hW⟩)) =
        ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
            (smallerHHGraph G (U : Set _))))
          (X (Sum.inr a))) ⊗ₜ[K]
          (1 : MvPolynomial (lambdaSet G (U : Set _)) K) := by
    simp only [L4Iso, AlgEquiv.ofAlgHom_apply]
    rw [L4Forward_mk_X]
    rw [L4ForwardGen_inr (K := K) hHH hU ⟨Sum.inr i, hW⟩ rfl,
      L4ForwardInr_of_paired (K := K) G (U : Set _) hW hi_ps]
    rw [hidx]
  -- Step 2: congr (L4Iso …) refl on the pure tensor (mk ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (L4Iso (K := K) hHH (U : Set _) hU)
        (AlgEquiv.refl (R := K) (A₁ := Localization.Away
          (hhUnitProductSub (K := K) U))))
      ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
          (hhSurvivors G (U : Set _))) (X ⟨Sum.inr i, hW⟩) :
          restrictedHHRing (K := K) G (hhSurvivors G (U : Set _))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      ((L4Iso (K := K) hHH (U : Set _) hU)
          ((Ideal.Quotient.mk (restrictedEdgeIdeal (K := K) G
              (hhSurvivors G (U : Set _)))) (X ⟨Sum.inr i, hW⟩))) ⊗ₜ[K]
        (1 : Localization.Away (hhUnitProductSub (K := K) U))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  rw [hStep2_inner]
  -- Step 3: the associator maps (x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z).
  rw [Algebra.TensorProduct.assoc_tmul]
  -- Step 4: congr refl polynomialAwayTensorEquiv on pure tensor x ⊗ (1 ⊗ 1).
  rw [show (Algebra.TensorProduct.congr (AlgEquiv.refl (R := K)
        (A₁ := BEI.reducedHHRing (K := K) (smallerHHGraph G (U : Set _))))
        (polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U)))
      (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inr a))) ⊗ₜ[K]
        ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
          (1 : Localization.Away (hhUnitProductSub (K := K) U)))) =
      ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K)
          (smallerHHGraph G (U : Set _)))) (X (Sum.inr a))) ⊗ₜ[K]
        ((polynomialAwayTensorEquiv (K := K)
          (α := (lambdaSet G (U : Set _) : Type _))
          (β := ((U : Set (BinomialEdgeVars (Fin n))) : Type _))
          (hhUnitProductSub (K := K) U))
          ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
            (1 : Localization.Away (hhUnitProductSub (K := K) U))))
      from by
        simp [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]]
  -- polynomialAwayTensorEquiv (1 ⊗ 1) = polynomialAwayTensorEquiv 1 = 1.
  have h11 : ((1 : MvPolynomial (lambdaSet G (U : Set _)) K) ⊗ₜ[K]
      (1 : Localization.Away (hhUnitProductSub (K := K) U))) =
      (1 : TensorProduct K (MvPolynomial (lambdaSet G (U : Set _)) K)
        (Localization.Away (hhUnitProductSub (K := K) U))) := rfl
  rw [h11, map_one]

/-! #### Main theorem -/

set_option maxHeartbeats 1600000 in
-- heartbeats + synth budget needed: main graded local-to-global assembly is heavy.
set_option synthInstance.maxHeartbeats 400000 in
/-- **Graded local-to-global for the HH quotient**: Under HH conditions, the quotient
`S ⧸ bipartiteEdgeMonomialIdeal G` is a Cohen–Macaulay ring.

The proof splits into two cases by whether a prime `p` is contained in the
augmentation ideal `m⁺`:

- **Case `p ≤ m⁺`**: By localization transitivity,
  `R_p ≅ (R_{m⁺})_{p'}` where `p' = p · R_{m⁺}`. Since `R_{m⁺}` is CM and CM localizes.
- **Case `p ⊄ m⁺`**: F2 route. Pick `U := {v | mkI(X v) ∉ p}`. The independent-set
  hypothesis holds by primality (edge monomials are zero in `R = S/I`). Localize away
  from `s_U := mkI(∏_{u ∈ U} X u)`; the bundled equiv `E_U` identifies this with
  `reducedHHRing(G') ⊗[K] Localization.Away(...)`. Push `p_Lsu` through `E_U` to get
  a prime `𝔓`; generator-level forward traces (C3a-inl/inr) plus maximality of
  `augIdealReduced` give `𝔓.comap includeLeft = augIdealReduced G'`. Apply the
  tensor-left-localisation bridge (C2) and the L7 replacement
  (`isCohenMacaulayLocalRing_localization_tensor_away`), then transport back.

References: Bruns–Herzog, Theorem 2.1.3(b); Herzog–Hibi (2005). -/
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal
    {K : Type} [Field K]
    {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G) := by
  set R := MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G
  set I := bipartiteEdgeMonomialIdeal (K := K) G
  set m := augIdeal (K := K) G
  constructor
  intro p _
  by_cases hp : p ≤ m
  · -- Case p ⊆ augIdeal: CM by localization transitivity.
    set Rm := Localization.AtPrime m
    have hdisj : Disjoint (↑m.primeCompl : Set R) (↑p) := by
      rw [Set.disjoint_left]; intro x hx hxp; exact hx (hp hxp)
    set p' := Ideal.map (algebraMap R Rm) p
    haveI hp' : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Rm p ‹_› hdisj
    haveI : IsCohenMacaulayLocalRing Rm :=
      isCohenMacaulayLocalRing_at_augIdeal (K := K) hn hHH
    set q := Ideal.comap (algebraMap R Rm) p' with hq_def
    have hqp : q = p := IsLocalization.comap_map_of_isPrime_disjoint _ Rm ‹_› hdisj
    haveI : q.IsPrime := hqp ▸ ‹p.IsPrime›
    haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p') :=
      isCohenMacaulayLocalRing_localization_atPrime p'
    have hCM_q : IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
      isCohenMacaulayLocalRing_of_ringEquiv' ‹_›
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          m.primeCompl p').symm.toRingEquiv
    have hpc : q.primeCompl = p.primeCompl := by
      ext x; exact not_congr (by rw [hqp])
    exact cast (show IsCohenMacaulayLocalRing (Localization.AtPrime q) =
      IsCohenMacaulayLocalRing (Localization.AtPrime p) by
        change IsCohenMacaulayLocalRing (Localization q.primeCompl) =
          IsCohenMacaulayLocalRing (Localization p.primeCompl)
        rw [hpc]) hCM_q
  · -- Case p ⊄ augIdeal: F2 decomposition via E_U, C2 bridge, and L7 replacement.
    classical
    -- Step 1: Pick U = "unit" variables (those whose mkI image is NOT in p).
    set U : Finset (BinomialEdgeVars (Fin n)) :=
      Finset.univ.filter (fun v => (Ideal.Quotient.mk I (X v) : R) ∉ p) with hU_def
    -- Step 2: U is HH-independent. HH edge ⇒ X u * X v ∈ I ⇒ product = 0 ∈ p ⇒ one of
    -- mkI(X u), mkI(X v) is in p, contradicting membership in U.
    have hU_indep : hhIndep G (U : Set _) := by
      intro u v hu hv hedge
      have huf : u ∈ U := by exact_mod_cast hu
      have hvf : v ∈ U := by exact_mod_cast hv
      have hu_nmem : Ideal.Quotient.mk I (X u) ∉ p := (Finset.mem_filter.mp huf).2
      have hv_nmem : Ideal.Quotient.mk I (X v) ∉ p := (Finset.mem_filter.mp hvf).2
      obtain ⟨i, j, hj, hadj, hle, heq⟩ := hedge
      rw [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hmem : X (Sum.inl i) * X (Sum.inr j) ∈ I :=
        Ideal.subset_span ⟨i, j, hj, hadj, hle, rfl⟩
      have h_mul_zero :
          (Ideal.Quotient.mk I (X (Sum.inl i))) * (Ideal.Quotient.mk I (X (Sum.inr j))) = 0 := by
        rw [← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
      have h_mul_mem :
          (Ideal.Quotient.mk I (X (Sum.inl i))) * (Ideal.Quotient.mk I (X (Sum.inr j))) ∈ p := by
        rw [h_mul_zero]; exact p.zero_mem
      rcases ‹p.IsPrime›.mem_or_mem h_mul_mem with hxu | hxv
      · exact hu_nmem hxu
      · exact hv_nmem hxv
    -- Step 3: sU := mkI(∏_{u ∈ U} X u) ∉ p.
    set sU : R := Ideal.Quotient.mk I (hhUnitProduct (K := K) U) with hsU_def
    have hsU_nmem : sU ∉ p := by
      rw [hsU_def]
      unfold hhUnitProduct
      rw [map_prod]
      intro hmem
      rcases Ideal.IsPrime.prod_mem_iff.mp hmem with ⟨u, hu, hu_in⟩
      exact (Finset.mem_filter.mp hu).2 hu_in
    -- Step 4: localize R away from sU.
    set Lsu := Localization.Away sU
    have hdisj : Disjoint (↑(Submonoid.powers sU) : Set R) (↑p : Set R) := by
      rw [Set.disjoint_left]
      rintro x ⟨k, rfl⟩ hx
      exact hsU_nmem (‹p.IsPrime›.mem_of_pow_mem _ hx)
    set p_Lsu : Ideal Lsu := Ideal.map (algebraMap R Lsu) p with p_Lsu_def
    haveI hp_Lsu : p_Lsu.IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint _ Lsu p ‹_› hdisj
    have hcomap_p : p_Lsu.comap (algebraMap R Lsu) = p :=
      IsLocalization.comap_map_of_isPrime_disjoint _ Lsu ‹_› hdisj
    -- Step 5: apply E_U and pull p_Lsu back to 𝔓.
    set G' : SimpleGraph (Fin (pairedCount G (U : Set _) + 1)) :=
      smallerHHGraph G (U : Set _) with G'_def
    set A := BEI.reducedHHRing (K := K) G' with A_def
    set Lnew := Localization.Away (rename (R := K)
      (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
      (τ := ↑(lambdaSet G (U : Set _)) ⊕
        ↑((U : Set (BinomialEdgeVars (Fin n)))))
      Sum.inr (hhUnitProductSub (K := K) U)) with Lnew_def
    let e_U := E_U (K := K) hHH U hU_indep
    set 𝔓 : Ideal (TensorProduct K A Lnew) := p_Lsu.comap e_U.symm.toRingHom with 𝔓_def
    haveI h𝔓 : 𝔓.IsPrime := Ideal.IsPrime.comap e_U.symm.toRingHom
    -- Step 6: 𝔓.comap includeLeft = augIdealReduced G'.
    have h_contract : 𝔓.comap
        (Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := A) (B := Lnew)).toRingHom =
        BEI.augIdealReduced (K := K) G' := by
      -- Each reduced variable lies in 𝔓.comap includeLeft.
      have h_gen : ∀ (v : BinomialEdgeVars (Fin (pairedCount G (U : Set _)))),
          ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G')) (X v) : A) ∈
            𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
              (A := A) (B := Lnew)).toRingHom := by
        intro v
        rw [Ideal.mem_comap]
        change ((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G')) (X v) ⊗ₜ[K]
          (1 : Lnew)) ∈ 𝔓
        rcases v with a | a
        · set i := pairedSurvivorsVal G (U : Set _) a
          have hi_ps : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
          have hi_surv : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈
              hhSurvivors G (U : Set _) := pairedSurvivors_inl_mem G _ hi_ps
          have hi_not_in_U : (Sum.inl i : BinomialEdgeVars (Fin n)) ∉ U := by
            intro h
            exact hi_surv (Or.inl (by exact_mod_cast h))
          have hmkI_in_p : Ideal.Quotient.mk I (X (Sum.inl i)) ∈ p := by
            by_contra h_notin
            exact hi_not_in_U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_notin⟩)
          have halg_in : algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inl i))) ∈ p_Lsu :=
            Ideal.mem_map_of_mem _ hmkI_in_p
          have hC3a := E_U_algebraMap_mkI_X_pairedSurvivor_inl (K := K) hHH U hU_indep a
          have halg_eq :
              algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inl i))) =
                e_U.symm
                  (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                    (X (Sum.inl a))) ⊗ₜ[K] (1 : Lnew)) := by
            rw [← hC3a]; exact (AlgEquiv.symm_apply_apply e_U _).symm
          have hsymm_in : e_U.symm
              (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                (X (Sum.inl a))) ⊗ₜ[K] (1 : Lnew)) ∈ p_Lsu :=
            halg_eq ▸ halg_in
          rw [𝔓_def, Ideal.mem_comap]
          exact hsymm_in
        · set i := pairedSurvivorsVal G (U : Set _) a
          have hi_ps : i ∈ pairedSurvivors G (U : Set _) := pairedSurvivorsVal_mem G _ a
          have hi_surv : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈
              hhSurvivors G (U : Set _) := pairedSurvivors_inr_mem G _ hi_ps
          have hi_not_in_U : (Sum.inr i : BinomialEdgeVars (Fin n)) ∉ U := by
            intro h
            exact hi_surv (Or.inl (by exact_mod_cast h))
          have hmkI_in_p : Ideal.Quotient.mk I (X (Sum.inr i)) ∈ p := by
            by_contra h_notin
            exact hi_not_in_U (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_notin⟩)
          have halg_in : algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inr i))) ∈ p_Lsu :=
            Ideal.mem_map_of_mem _ hmkI_in_p
          have hC3a := E_U_algebraMap_mkI_X_pairedSurvivor_inr (K := K) hHH U hU_indep a
          have halg_eq :
              algebraMap R Lsu (Ideal.Quotient.mk I (X (Sum.inr i))) =
                e_U.symm
                  (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                    (X (Sum.inr a))) ⊗ₜ[K] (1 : Lnew)) := by
            rw [← hC3a]; exact (AlgEquiv.symm_apply_apply e_U _).symm
          have hsymm_in : e_U.symm
              (((Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
                (X (Sum.inr a))) ⊗ₜ[K] (1 : Lnew)) ∈ p_Lsu :=
            halg_eq ▸ halg_in
          rw [𝔓_def, Ideal.mem_comap]
          exact hsymm_in
      -- augIdealReduced ≤ comap (via span of variables + zero constant coefficient).
      have h_le_comap : BEI.augIdealReduced (K := K) G' ≤
          𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
            (A := A) (B := Lnew)).toRingHom := by
        intro x hx
        obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
        rw [BEI.augIdealReduced, RingHom.mem_ker,
          BEI.quotConstCoeffReduced, Ideal.Quotient.lift_mk] at hx
        have hmem : f ∈ Ideal.span (Set.range
            (X : BinomialEdgeVars (Fin (pairedCount G (U : Set _))) →
              MvPolynomial (BinomialEdgeVars (Fin (pairedCount G (U : Set _)))) K)) := by
          rw [show Set.range X = X '' Set.univ from Set.image_univ.symm,
              MvPolynomial.mem_ideal_span_X_image]
          intro mono hm
          have hne : mono ≠ 0 := by
            intro hzero; subst hzero
            simp only [MvPolynomial.mem_support_iff] at hm; exact hm hx
          obtain ⟨idx, hidx⟩ := Finsupp.ne_iff.mp hne
          exact ⟨idx, Set.mem_univ _, hidx⟩
        have hmap :
            Ideal.map (Ideal.Quotient.mk (BEI.reducedHHIdeal (K := K) G'))
              (Ideal.span (Set.range X)) ≤
            𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
              (A := A) (B := Lnew)).toRingHom := by
          rw [Ideal.map_span]
          apply Ideal.span_le.mpr
          rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
          exact h_gen v
        exact hmap (Ideal.mem_map_of_mem _ hmem)
      -- Comap is proper (𝔓 prime, so 1 ∉ 𝔓).
      have h_ne_top : 𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
          (A := A) (B := Lnew)).toRingHom ≠ ⊤ := by
        intro htop
        apply h𝔓.ne_top
        rw [Ideal.eq_top_iff_one]
        have h1 : (1 : A) ∈ 𝔓.comap (Algebra.TensorProduct.includeLeft (R := K) (S := K)
            (A := A) (B := Lnew)).toRingHom := by rw [htop]; trivial
        rw [Ideal.mem_comap, map_one] at h1
        exact h1
      exact ((BEI.augIdealReduced_isMaximal G').eq_of_le h_ne_top h_le_comap).symm
    -- Step 7: apply C2 bridge.
    haveI h𝔓' : (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced G') 𝔓).IsPrime :=
      Algebra.tensorLeftLocalisedPrime_isPrime
        (B := Lnew) (BEI.augIdealReduced G') 𝔓 h_contract
    let e_C2 : Localization.AtPrime 𝔓 ≃+*
        Localization.AtPrime
          (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced (K := K) G') 𝔓) :=
      Algebra.tensorLeftLocalisationEquiv (BEI.augIdealReduced G') 𝔓 h_contract
    -- Step 8+9: L7 replacement gives CM-local at the tensor-pushed prime.
    haveI hCM_A : IsCohenMacaulayRing (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) :=
      isCohenMacaulayRing_at_augIdealReduced (K := K)
        (smallerHHGraph_herzogHibi hHH (U : Set _))
    haveI : IsNoetherianRing (BEI.reducedHHRing (K := K) G') :=
      Ideal.Quotient.isNoetherianRing _
    haveI : IsNoetherianRing (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) :=
      IsLocalization.isNoetherianRing (BEI.augIdealReduced (K := K) G').primeCompl
        (Localization.AtPrime (BEI.augIdealReduced (K := K) G')) inferInstance
    haveI hCM_𝔓' : IsCohenMacaulayLocalRing
        (Localization.AtPrime
          (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced (K := K) G') 𝔓)) :=
      TensorPolynomialAway.isCohenMacaulayLocalRing_localization_tensor_away
        (A := Localization.AtPrime (BEI.augIdealReduced (K := K) G'))
        (rename (R := K)
          (σ := ↑((U : Set (BinomialEdgeVars (Fin n)))))
          (τ := ↑(lambdaSet G (U : Set _)) ⊕
            ↑((U : Set (BinomialEdgeVars (Fin n)))))
          Sum.inr (hhUnitProductSub (K := K) U))
        (Algebra.tensorLeftLocalisedPrime K (BEI.augIdealReduced G') 𝔓)
    -- Step 10a: transport back through e_C2.
    have hCM_𝔓 : IsCohenMacaulayLocalRing (Localization.AtPrime 𝔓) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hCM_𝔓' e_C2.symm
    -- Step 10b: transport to Localization.AtPrime p_Lsu via e_U.
    have hH : p_Lsu.primeCompl.map e_U.toRingEquiv.toMonoidHom = 𝔓.primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        intro hmem
        apply hx
        rw [𝔓_def, Ideal.mem_comap] at hmem
        change e_U.symm.toRingHom (e_U.toRingEquiv x) ∈ p_Lsu at hmem
        rw [show e_U.toRingEquiv x = e_U x from rfl] at hmem
        change e_U.symm (e_U x) ∈ p_Lsu at hmem
        rwa [AlgEquiv.symm_apply_apply] at hmem
      · intro hy
        refine ⟨e_U.symm y, ?_, ?_⟩
        · intro hymem
          apply hy
          rw [𝔓_def, Ideal.mem_comap]
          exact hymem
        · change e_U.toRingEquiv (e_U.symm y) = y
          exact AlgEquiv.apply_symm_apply e_U y
    let e_locP : Localization.AtPrime p_Lsu ≃+* Localization.AtPrime 𝔓 :=
      IsLocalization.ringEquivOfRingEquiv
        (S := Localization.AtPrime p_Lsu)
        (Q := Localization.AtPrime 𝔓)
        (M := p_Lsu.primeCompl)
        (T := 𝔓.primeCompl)
        e_U.toRingEquiv hH
    have hCM_pLsu : IsCohenMacaulayLocalRing (Localization.AtPrime p_Lsu) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hCM_𝔓 e_locP.symm
    -- Step 10c: loc-of-loc to Localization.AtPrime p.
    set q₁ := Ideal.comap (algebraMap R Lsu) p_Lsu with q₁_def
    have hq₁p : q₁ = p := hcomap_p
    haveI : q₁.IsPrime := hq₁p ▸ ‹p.IsPrime›
    have hCM_q₁ : IsCohenMacaulayLocalRing (Localization.AtPrime q₁) :=
      isCohenMacaulayLocalRing_of_ringEquiv' hCM_pLsu
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (Submonoid.powers sU) p_Lsu).symm.toRingEquiv
    have hpc : q₁.primeCompl = p.primeCompl := by
      ext x; exact not_congr (by rw [hq₁p])
    exact cast (show IsCohenMacaulayLocalRing (Localization.AtPrime q₁) =
      IsCohenMacaulayLocalRing (Localization.AtPrime p) by
        change IsCohenMacaulayLocalRing (Localization q₁.primeCompl) =
          IsCohenMacaulayLocalRing (Localization p.primeCompl)
        rw [hpc]) hCM_q₁

end GlobalCM

/-- Under HH conditions, `S ⧸ monomialInitialIdeal G` is globally Cohen–Macaulay.

This is the `J_G`-side monomial CM statement: for a graph `G` satisfying the
Herzog–Hibi conditions (in particular, any closed graph satisfying the
Proposition 1.6 condition — see `prop_1_6_herzogHibi`), the quotient of the
polynomial ring by the monomial initial ideal of `J_G` is Cohen–Macaulay.

Proof: transport the HH bipartite CM theorem
`isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal` along the
`y`-predecessor ring isomorphism built from `rename_yPredVar_monomialInitialIdeal`.

Restricted to `K : Type` because the underlying HH theorem is universe-monomorphic. -/
theorem monomialInitialIdeal_isCohenMacaulay
    {K : Type} [Field K]
    {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G) := by
  have hn0 : 0 < n := by omega
  set φ := (MvPolynomial.renameEquiv K (yPredEquiv n hn0)).toRingEquiv
  have hmap : bipartiteEdgeMonomialIdeal (K := K) G =
      Ideal.map φ (monomialInitialIdeal (K := K) G) := by
    have hfun : ⇑φ = ⇑(rename (yPredVar n hn0) : MvPolynomial _ K →ₐ[K] MvPolynomial _ K) := by
      funext p; exact (MvPolynomial.renameEquiv_apply K (yPredEquiv n hn0) p).symm
    change _ = Ideal.map φ.toRingHom _
    conv_rhs => rw [show φ.toRingHom = (rename (yPredVar n hn0) :
        MvPolynomial _ K →ₐ[K] MvPolynomial _ K).toRingHom from RingHom.ext (fun x => by
      change φ x = rename (yPredVar n hn0) x; exact congr_fun hfun x)]
    exact (rename_yPredVar_monomialInitialIdeal (K := K) hn0 G).symm
  have e : MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ monomialInitialIdeal (K := K) G ≃+*
      MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.quotientEquiv _ _ φ hmap
  haveI : IsCohenMacaulayRing
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G) :=
    isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal hn hHH
  exact isCohenMacaulayRing_of_ringEquiv e.symm

end

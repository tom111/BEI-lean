import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
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
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.MvPolynomial.Homogeneous

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
    {σ : Type*} [DecidableEq σ]
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
    {σ : Type*} [DecidableEq σ]
    {S : Set (MvPolynomial σ K)}
    (hS : ∀ s ∈ S, ∃ e, s.support ⊆ {e})
    {f : MvPolynomial σ K} (hf : f ∈ Ideal.span S) :
    ∀ d ∈ f.support, ∃ s ∈ S, ∃ e, s.support ⊆ {e} ∧ e ≤ d := by
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
      simp [Finsupp.single_apply, ha_ne, hb_ne]
    · -- v = inr i: both single(inl a) and single(inl b) have 0 at inr i
      simp [Finsupp.single_apply]
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
      simp only [Finsupp.single_apply, Sum.inl.injEq,
        show (Sum.inr b : BinomialEdgeVars (Fin n)) ≠ Sum.inl i from Sum.inr_ne_inl,
        if_false, add_zero]
      split <;> omega
    · -- v = inr i: single(inl a)(inr i) = 0 and single(inr b)(inr i) ≤ 1
      simp only [Finsupp.single_apply,
        show (Sum.inl a : BinomialEdgeVars (Fin n)) ≠ Sum.inr i from Sum.inl_ne_inr,
        if_false, Sum.inr.injEq, zero_add]
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
          show d' (Sum.inr i) = 0
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
          rw [Finsupp.mem_support_iff, not_not]; show d' (Sum.inl i) = 0
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
          rw [Finsupp.mem_support_iff, not_not]; show dx (Sum.inr i) = 0
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
          rw [Finsupp.mem_support_iff, not_not]; show dy (Sum.inl i) = 0
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
            (X (Sum.inl a₁) * -X (Sum.inl b₁) : MvPolynomial (BinomialEdgeVars (Fin n)) K).support := by
          have hprod : (X (Sum.inl a₁) * X (Sum.inl b₁) : MvPolynomial (BinomialEdgeVars (Fin n)) K) =
            MvPolynomial.monomial (Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inl b₁) 1) 1 := by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]; rfl
          have heq : (X (Sum.inl a₁) * -X (Sum.inl b₁) : MvPolynomial (BinomialEdgeVars (Fin n)) K) =
            -(MvPolynomial.monomial (Finsupp.single (Sum.inl a₁) 1 + Finsupp.single (Sum.inl b₁) 1) 1) := by
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
            MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]
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
          rw [hex_eq, hb]; simp [Finsupp.single_apply, Sum.inl_ne_inr]
        have h2 : ex (Sum.inr i) ≤ 0 := by
          have := hlex_dx (Sum.inr i)
          simp only [dx, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            Sum.inl_ne_inr, if_false, add_zero, hyi0] at this
          exact this
        omega
      have hb₁_gt_i : i < b₁ := lt_of_le_of_ne (ha₁_eq ▸ hab₁) (Ne.symm hb₁_ne_i)
      -- y_{b₁} divides d₀
      have hyb₁ : 1 ≤ d₀ (Sum.inr b₁) := by
        have := hlex_dx (Sum.inr b₁)
        rw [hex_eq] at this
        simp only [dx, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
          Sum.inl_ne_inr, if_false, add_zero] at this
        simp only [show (Sum.inr b₁ : BinomialEdgeVars (Fin n)) = Sum.inr b₁ from rfl,
          if_true] at this
        exact this
      -- Split on whether b₂ < k for sy
      split_ifs at heys with hcond₂
      · -- b₂ < k: ey only involves inl vars, so ey(inr i) = 0 → contradiction
        exfalso; apply hey_case
        have : ey = Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1 := by
          have hmem : Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1 ∈
              (X (Sum.inl a₂) * -X (Sum.inl b₂) : MvPolynomial (BinomialEdgeVars (Fin n)) K).support := by
            have hprod : (X (Sum.inl a₂) * X (Sum.inl b₂) : MvPolynomial (BinomialEdgeVars (Fin n)) K) =
              MvPolynomial.monomial (Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1) 1 := by
              simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]; rfl
            have heq : (X (Sum.inl a₂) * -X (Sum.inl b₂) : MvPolynomial (BinomialEdgeVars (Fin n)) K) =
              -(MvPolynomial.monomial (Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inl b₂) 1) 1) := by
              rw [mul_neg, hprod]
            rw [heq, MvPolynomial.support_neg]
            exact hsupp_mono _
          exact (Finset.mem_singleton.mp (heys hmem)).symm
        rw [this]; simp [Finsupp.single_apply, Sum.inl_ne_inr]
      · -- b₂ ≥ k: generator is x_{a₂} * y_{b₂}
        have hey_eq : ey = Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₂) 1 := by
          have hmem : Finsupp.single (Sum.inl a₂) 1 + Finsupp.single (Sum.inr b₂) 1 ∈
              (X (Sum.inl a₂) * X (Sum.inr b₂) : MvPolynomial _ K).support := by
            simp only [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
              MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_pos rfl]
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
            simp [Finsupp.single_apply, Sum.inl_ne_inr]
          have h2 : ey (Sum.inl i) ≤ 0 := by
            have := hley_dy (Sum.inl i)
            simp only [dy, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
              show (Sum.inl i : BinomialEdgeVars (Fin n)) ≠ Sum.inr i from Sum.inl_ne_inr,
              if_false, add_zero, hxi0] at this
            exact this
          omega
        have ha₂_lt_i : a₂ < i := lt_of_le_of_ne (hb₂_eq ▸ hab₂) ha₂_ne_i
        -- x_{a₂} divides d₀
        have hxa₂ : 1 ≤ d₀ (Sum.inl a₂) := by
          have := hley_dy (Sum.inl a₂)
          rw [hey_eq] at this
          simp only [dy, Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply,
            Sum.inr_ne_inl, if_false, add_zero,
            show (Sum.inl a₂ : BinomialEdgeVars (Fin n)) = Sum.inl a₂ from rfl,
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
            simp [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]
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
    invFun := fun ⟨j, hj⟩ => ⟨⟨j, by omega⟩, by show j + 1 < n; omega⟩
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

end AugmentationCM

/-! ### Cohen–Macaulay transfer through ring equivalence -/

section CMTransfer

universe u₀

open RingTheory.Sequence IsLocalRing

variable {A₀ B₀ : Type u₀} [CommRing A₀] [CommRing B₀]

/-- A ring equivalence between local rings is a local ring homomorphism. -/
private instance ringEquiv_isLocalHom [IsLocalRing A₀] [IsLocalRing B₀]
    (e : A₀ ≃+* B₀) : IsLocalHom e.toRingHom where
  map_nonunit a ha := by
    rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at ha
    exact (isUnit_map_iff e a).mp ha

/-- Weakly regular sequences transfer through ring equivalences.

The proof chains two Mathlib results:
1. `LinearEquiv.isWeaklyRegular_congr` transfers weak regularity between modules
   over the same ring (using the A-linear equivalence `A ≃ₗ[A] B`).
2. `isWeaklyRegular_map_algebraMap_iff` relates `IsWeaklyRegular B rs` (as A-module)
   to `IsWeaklyRegular B (rs.map e)` (as B-module) via the scalar tower. -/
private lemma isWeaklyRegular_map_ringEquiv (e : A₀ ≃+* B₀) {rs : List A₀}
    (hreg : IsWeaklyRegular A₀ rs) : IsWeaklyRegular B₀ (rs.map e) := by
  letI : Algebra A₀ B₀ := e.toRingHom.toAlgebra
  let eₗ : A₀ ≃ₗ[A₀] B₀ :=
    { e.toAddEquiv with
      map_smul' := fun a x => by
        change e (a * x) = e.toRingHom a * e x
        exact e.map_mul a x }
  exact (isWeaklyRegular_map_algebraMap_iff B₀ B₀ rs).mpr
    ((LinearEquiv.isWeaklyRegular_congr eₗ rs).mp hreg)

/-- Cohen–Macaulay local rings are invariant under ring equivalences.

Transfer strategy: `dim(B) = dim(A) = depth(A)`. Then `depth(A) ≤ depth(B)`
(by mapping weakly regular sequences via `isWeaklyRegular_map_ringEquiv`) and
`depth(B) ≤ dim(B)` (always), giving `dim(B) = depth(B)`. -/
private theorem isCohenMacaulayLocalRing_of_ringEquiv
    [IsLocalRing A₀] [IsLocalRing B₀]
    [hCM : IsCohenMacaulayLocalRing A₀] (e : A₀ ≃+* B₀) :
    IsCohenMacaulayLocalRing B₀ where
  depth_eq_dim := by
    have hdim : ringKrullDim B₀ = ringKrullDim A₀ := (ringKrullDim_eq_of_ringEquiv e).symm
    rw [hdim, hCM.depth_eq_dim]; congr 1
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨rs, rfl, hreg, hmem⟩
      exact le_sSup ⟨rs.map e, by simp, isWeaklyRegular_map_ringEquiv e hreg,
        fun r hr => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
          exact map_nonunit e.toRingHom a (hmem a ha)⟩
    · apply sSup_le
      rintro _ ⟨rs, rfl, hreg, hmem⟩
      exact le_sSup ⟨rs.map e.symm, by simp, isWeaklyRegular_map_ringEquiv e.symm hreg,
        fun r hr => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
          exact map_nonunit e.symm.toRingHom a (hmem a ha)⟩

end CMTransfer

/-! ### HH bipartite edge ideal: global Cohen–Macaulay theorem -/

section GlobalCM

open IsLocalRing

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

/-! #### Lemmas 1, 2, 4, 5, 6, 7 — scaffolding for the F2 route

Statements only; proofs are deferred. See
`guides/work_packages/HH_GLOBAL_CM_FROM_AUGIDEAL.md` for the full plan. -/

/-! #### Main theorem -/

/-- **Graded local-to-global for the HH quotient**: Under HH conditions, the quotient
`S ⧸ bipartiteEdgeMonomialIdeal G` is a Cohen–Macaulay ring.

The proof splits into two cases by whether a prime `p` is contained in the
augmentation ideal `m⁺`:

- **Case `p ≤ m⁺`**: By localization transitivity,
  `R_p ≅ (R_{m⁺})_{p'}` where `p' = p · R_{m⁺}`. Since `R_{m⁺}` is CM
  (by `isCohenMacaulayLocalRing_at_augIdeal`) and CM localizes
  (`isCohenMacaulayLocalRing_localization_atPrime`), `R_p` is CM.

- **Case `p ⊄ m⁺`**: By `exists_var_not_mem_of_not_le_augIdeal`, some variable
  image `X_v` is not in `p`, hence is a unit in `R_p`. By HH diagonal conditions,
  the paired variable `X_w` becomes zero. This simplifies `R_p` to a localization
  of a smaller polynomial quotient, which is CM by an inductive/structural argument.

References: Bruns–Herzog, Theorem 2.1.3(b); Herzog–Hibi (2005). -/
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_augIdeal
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
    -- R_m is CM local; (R_m)_{p'} is CM for any prime p' of R_m.
    -- R_p ≅ (R_m)_{p'} where p' = map p, and comap p' = p.
    -- Transfer CM through the localization-localization AlgEquiv.
    set Rm := Localization.AtPrime m
    have hdisj : Disjoint (↑m.primeCompl : Set R) (↑p) := by
      rw [Set.disjoint_left]; intro x hx hxp; exact hx (hp hxp)
    set p' := Ideal.map (algebraMap R Rm) p
    haveI hp' : p'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ Rm p ‹_› hdisj
    haveI : IsCohenMacaulayLocalRing Rm :=
      isCohenMacaulayLocalRing_at_augIdeal (K := K) hn hHH
    -- Factor through the localization-localization isomorphism
    set q := Ideal.comap (algebraMap R Rm) p' with hq_def
    have hqp : q = p := IsLocalization.comap_map_of_isPrime_disjoint _ Rm ‹_› hdisj
    haveI : q.IsPrime := hqp ▸ ‹p.IsPrime›
    -- (R_m)_{p'} is CM by CM localization
    haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p') :=
      isCohenMacaulayLocalRing_localization_atPrime p'
    -- R_q ≃ (R_m)_{p'}, and q = p
    have hCM_q : IsCohenMacaulayLocalRing (Localization.AtPrime q) :=
      isCohenMacaulayLocalRing_of_ringEquiv
        (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          m.primeCompl p').symm.toRingEquiv
    -- Transport from q to p: since q = p, the localization types are equal
    have hpc : q.primeCompl = p.primeCompl := by
      ext x; exact not_congr (by rw [hqp])
    exact cast (show IsCohenMacaulayLocalRing (Localization.AtPrime q) =
      IsCohenMacaulayLocalRing (Localization.AtPrime p) by
        change IsCohenMacaulayLocalRing (Localization q.primeCompl) =
          IsCohenMacaulayLocalRing (Localization p.primeCompl)
        rw [hpc]) hCM_q
  · -- Case p ⊄ augIdeal: reduce to "polynomial rings over fields are CM."
    --
    -- By the HH structure + local-ring dichotomy (ab = 0, a + b unit ⟹
    -- one is 0), every variable is either 0 or a unit in R_p.  The monomial
    -- generators of I each have at least one zero factor, so they vanish.
    -- The ring R_p is therefore isomorphic to a localization of
    -- K[surviving variables] — a polynomial ring in the unit variables.
    -- CM then follows from the standard fact that polynomial rings over
    -- fields are Cohen–Macaulay (equivalently: regular local rings are CM),
    -- which is not yet in Mathlib.
    sorry

end GlobalCM

end

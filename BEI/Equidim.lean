import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import toMathlib.Equidim.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

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

/-! ## Statement of the iterated regularity theorem

The full regular-sequence result and analysis of the remaining gap.
-/

/-- **Iterated regularity** (statement with gap):
Under HH conditions, `x_k + y_k` is a non-zero-divisor on the quotient
`S / (I ⊔ diag)` where `I = bipartiteEdgeMonomialIdeal G` and
`diag = diagonalSumIdeal n k`.

### Proved steps

1. Every minimal prime of `I ⊔ diag` is of the form `span(X '' C')` where `C'`
   extends a minimal vertex cover of `hhEdgeSet G` by adding both `x_j, y_j`
   for `j < k`.  (Follows from `sum_X_not_mem_prime_sup_diagonalSum`.)

2. `x_k + y_k` avoids all such primes.  (See above.)

3. The radical `√(I ⊔ diag)` equals `(x_j, y_j : j < k) + I_{≥k}` where
   `I_{≥k}` is the edge ideal restricted to indices `≥ k`. This is a radical
   (squarefree monomial) ideal, so `x_k + y_k` is a non-zero-divisor on
   `S / √(I ⊔ diag)` by `isSMulRegular_of_radical_not_mem_minimalPrimes`.

### Remaining gap

The ideal `I ⊔ diag` is NOT radical: it contains `x_j² = x_j(x_j + y_j) - x_j y_j`
for each `j < k`, but not `x_j` itself. Therefore the standard "radical = intersection
of minimal primes" argument only gives `f ∈ √(I ⊔ diag)`, not `f ∈ I ⊔ diag`.

The nilradical `√(I ⊔ diag) / (I ⊔ diag)` is generated by `x̄₀, …, x̄_{k-1}`.
For `k = 1`, it is cyclic with annihilator `(x₀, x₁y₁) = (x₀, I_{≥1})` in the
reduced ring, which is itself radical with no associated prime containing both
`x_k` and `y_k`. This shows `ℓ_k` is NZD on the nilradical module, completing
the proof for `k = 1`.

The general case uses a filtration of the nilradical module; each graded piece
is a quotient by a radical variable-generated ideal that also avoids `ℓ_k`.

Viable route: factor the exact sequence
  `0 → √(I ⊔ diag)/(I ⊔ diag) → S/(I ⊔ diag) → S/√(I ⊔ diag) → 0`
and show `ℓ_k` is NZD on both outer terms (the first via the filtration argument,
the second via radicality + prime avoidance).
-/
theorem sum_XY_isSMulRegular_mod_diagonalSum {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) (i : Fin n) (hi : i.val + 1 < n)
    (hik : k ≤ i.val) :
    IsSMulRegular
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        (bipartiteEdgeMonomialIdeal (K := K) G ⊔ diagonalSumIdeal (K := K) n k))
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G ⊔
        diagonalSumIdeal (K := K) n k) (X (Sum.inl i) + X (Sum.inr i))) := by
  sorry

end

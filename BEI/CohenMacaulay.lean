import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import toMathlib.CohenMacaulay.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

noncomputable section

open MvPolynomial SimpleGraph

/-!
# Cohen-Macaulay rings and binomial edge ideals

Uses `IsCohenMacaulayRing` from `toMathlib/CohenMacaulay/Defs.lean`, which defines
CM via equidimensionality (all minimal primes have the same height). This is a
consequence of the full CM definition (depth = dim), adapted from mathlib PR #26218.

Formalizes Proposition 1.6 of Herzog et al. (2010):
  If G is a connected closed graph satisfying an additional interval condition,
  then S/J_G is Cohen-Macaulay.

## Reference: Herzog et al. (2010), Section 1
-/

-- Re-export for backward compatibility
abbrev IsCohenMacaulay (R : Type*) [CommRing R] := IsCohenMacaulayRing R

/-- An integral domain is CM: it has a unique minimal prime (⊥),
so the equidimensionality condition holds vacuously. -/
instance IsDomain.isCohenMacaulayRing {R : Type*} [CommRing R] [IsDomain R] :
    IsCohenMacaulayRing R where
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

/-- Example 1.7(a): The complete graph K_n yields a Cohen-Macaulay quotient.
The complete graph has J_G = P_∅(G), which is prime, so R/J_G is a domain and
hence trivially CM (unique minimal prime). -/
theorem complete_is_CM (n : ℕ) :
    IsCohenMacaulay
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

-- Example 1.7(b) (path_is_CM) is proved in PrimeDecompositionDimension.lean
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

/-- Under HH conditions, the quotient by `bipartiteEdgeMonomialIdeal G` is Cohen–Macaulay
(equidimensional). -/
theorem bipartiteEdgeMonomialIdeal_isCohenMacaulay {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G) :
    IsCohenMacaulayRing
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

/-! ## Proposition 1.6 -/

/--
Proposition 1.6: If G is connected, closed with respect to its labeling, and satisfies
the interval condition, then S/J_G is Cohen-Macaulay.

**Reduction chain** (paper-faithful, following Herzog et al. (2010)):

1. **Initial ideal** (`initialIdeal_closed_eq`): For closed G, `in_<(J_G)` is generated
   by the monomials `{xᵢ yⱼ : {i,j} ∈ E(G), i < j}`.

2. **Variable shift** (`rename_yPredVar_monomialInitialIdeal`): The automorphism
   `φ: yⱼ ↦ y_{j-1}` transports the monomial initial ideal to the bipartite edge
   ideal of the graph Γ (`bipartiteEdgeMonomialIdeal`).

3. **HH conditions** (`prop_1_6_herzogHibi`): Γ satisfies the three conditions of
   the Herzog–Hibi CM criterion (diagonal, upper-triangularity, transitivity).

4. **Equidimensionality** (`bipartiteEdgeMonomialIdeal_isCohenMacaulay`): Under HH
   conditions, all minimal vertex covers of Γ have the same size, so the quotient
   by the bipartite edge monomial ideal is equidimensional (CM in the local sense).

**Remaining gap**: CM transfer from initial ideal (`S/in_<(I)` CM → `S/I` CM).
This is a standard result in Gröbner basis theory (not yet in Mathlib).

Reference: Herzog et al. (2010), Proposition 1.6.
-/
theorem prop_1_6 (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n))
    (hConn : G.Connected)
    (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsCohenMacaulay
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal G) := by
  -- Step 1: Initial ideal of J_G for closed graphs
  have _hInit := initialIdeal_closed_eq (K := K) G hClosed
  -- Step 2: Variable shift transports monomial initial ideal to bipartite edge ideal
  have _hTransport := rename_yPredVar_monomialInitialIdeal (K := K) hn G
  -- Step 3: HH conditions on the bipartite graph Γ
  have hHH := prop_1_6_herzogHibi n G hConn hClosed hCond
  -- Step 4: The bipartite edge ideal quotient is CM (equidimensional)
  have _hCM := bipartiteEdgeMonomialIdeal_isCohenMacaulay (K := K) hHH
  -- Remaining gap: CM transfer from initial ideal to original ideal
  -- S/in_<(J_G) CM → S/J_G CM (standard Gröbner basis theory result)
  sorry

end

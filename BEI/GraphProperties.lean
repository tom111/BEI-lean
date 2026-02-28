import BEI.Definitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

variable {V : Type*} [LinearOrder V] [DecidableEq V]

/-!
# Graph-theoretic properties for binomial edge ideals

This file develops the graph theory needed for Sections 1 and 2 of
Herzog et al. (2010):

- Chordal graphs (no induced cycle of length ≥ 4)
- Claw-free graphs (no induced K_{1,3})
- The closure G̅ of a graph (minimal closed supergraph, Proposition 1.5)
- Admissible paths (Section 2, before Theorem 2.1)

## References: Herzog et al. (2010), Sections 1–2
-/

open SimpleGraph

/-! ## Chordal and claw-free graphs -/

/--
A graph is **chordal** if every cycle of length ≥ 4 has a chord (an edge between
two non-consecutive vertices of the cycle). Equivalently, G has no induced cycle
of length ≥ 4.

We use the induced-cycle formulation: for any injective map f : Fin n → V (n ≥ 4)
whose consecutive pairs are all adjacent (forming a cycle), some non-consecutive
pair is also adjacent.

Note: the walk-based statement `∀ w : IsCycle, w.length ≤ 3` is *too strong* —
K₄ is closed and has 4-cycles. The correct statement allows chords.
-/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ (n : ℕ) (hn : 4 ≤ n) (f : Fin n ↪ V),
    (∀ i : Fin n, G.Adj (f i) (f ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) →
    ∃ (i j : Fin n),
      (j.val + 1) % n ≠ i.val ∧ (i.val + 1) % n ≠ j.val ∧ G.Adj (f i) (f j)

/--
A graph is **claw-free** if it contains no induced subgraph isomorphic to K_{1,3}.
A claw consists of a center vertex adjacent to three mutually non-adjacent vertices.
-/
def IsClawFree (G : SimpleGraph V) : Prop :=
  ∀ (c a b d : V),
    a ≠ b → b ≠ d → a ≠ d →
    G.Adj c a → G.Adj c b → G.Adj c d →
    G.Adj a b ∨ G.Adj b d ∨ G.Adj a d

/-! ## The closure of a graph (Proposition 1.5) -/

/--
The **closure** G̅ of G is the minimal graph (by edge inclusion) that
contains G and is closed with respect to the given linear order.

Constructed as the infimum of all closed supergraphs.

Reference: Herzog et al. (2010), Proposition 1.5.
-/
noncomputable def graphClosure (G : SimpleGraph V) : SimpleGraph V :=
  sInf { H : SimpleGraph V | G ≤ H ∧ IsClosedGraph H }

/-- The closure contains the original graph. -/
theorem graphClosure_le (G : SimpleGraph V) : G ≤ graphClosure G :=
  le_sInf fun _ hH => hH.1

/-- The complete graph is a closed supergraph of any graph. -/
theorem top_isClosedGraph : IsClosedGraph (⊤ : SimpleGraph V) := by
  constructor
  · intro i j k _ _ hjk _ _
    exact (SimpleGraph.top_adj j k).mpr hjk
  · intro i j k _ _ hij _ _
    exact (SimpleGraph.top_adj i j).mpr hij

/-- The set of closed supergraphs is always nonempty (contains ⊤). -/
theorem closedSupergraphs_nonempty (G : SimpleGraph V) :
    Set.Nonempty { H : SimpleGraph V | G ≤ H ∧ IsClosedGraph H } :=
  ⟨⊤, le_top, top_isClosedGraph⟩

/-- The closure is itself closed. -/
theorem graphClosure_isClosedGraph (G : SimpleGraph V) :
    IsClosedGraph (graphClosure G) := by
  have hs := closedSupergraphs_nonempty G
  constructor
  · -- Condition 1: diverging from a common minimum
    intro i j k hij hik hjk hadj_ij hadj_ik
    -- After unfolding graphClosure = sInf {...}, adjacency in the sInf means
    -- adjacency in every closed supergraph of G
    simp only [graphClosure, SimpleGraph.sInf_adj_of_nonempty hs, Set.mem_setOf_eq] at *
    intro H ⟨hGH, hHcl⟩
    exact hHcl.1 hij hik hjk (hadj_ij H ⟨hGH, hHcl⟩) (hadj_ik H ⟨hGH, hHcl⟩)
  · -- Condition 2: converging to a common maximum
    intro i j k hik hjk hij hadj_ik hadj_jk
    simp only [graphClosure, SimpleGraph.sInf_adj_of_nonempty hs, Set.mem_setOf_eq] at *
    intro H ⟨hGH, hHcl⟩
    exact hHcl.2 hik hjk hij (hadj_ik H ⟨hGH, hHcl⟩) (hadj_jk H ⟨hGH, hHcl⟩)

/-- The closure is the minimal closed supergraph. -/
theorem graphClosure_minimal (G H : SimpleGraph V)
    (hGH : G ≤ H) (hH : IsClosedGraph H) : graphClosure G ≤ H :=
  sInf_le ⟨hGH, hH⟩

/-- Proposition 1.5: The closure is the unique minimal closed supergraph. -/
theorem prop_1_5 (G : SimpleGraph V) :
    ∃! H : SimpleGraph V,
      G ≤ H ∧ IsClosedGraph H ∧
      ∀ H' : SimpleGraph V, G ≤ H' → IsClosedGraph H' → H ≤ H' :=
  ⟨graphClosure G,
   ⟨graphClosure_le G, graphClosure_isClosedGraph G,
    fun H' hGH' hH' => graphClosure_minimal G H' hGH' hH'⟩,
   by
     intro H ⟨hGH, hHcl, hHmin⟩
     apply le_antisymm
     · -- H ≤ graphClosure G: graphClosure G also satisfies the minimality property of H
       exact hHmin (graphClosure G) (graphClosure_le G) (graphClosure_isClosedGraph G)
     · -- graphClosure G ≤ H: by definition of graphClosure as sInf
       exact graphClosure_minimal G H hGH hHcl⟩

/-! ## Properties of closed graphs (Proposition 1.2) -/

/-- Proposition 1.2(1): Every closed graph is chordal. -/
theorem closedGraph_isChordal (G : SimpleGraph V) (h : IsClosedGraph G) :
    IsChordal G := by
  intro n hn f hcycle
  have hn_pos : 0 < n := by omega
  -- Pick the index i₀ where f is minimised
  obtain ⟨i₀, _, hi₀_min⟩ :=
    Finset.exists_min_image Finset.univ (f : Fin n → V)
      ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  -- The successor j = i₀ + 1 (mod n) and predecessor k = i₀ - 1 (mod n)
  let j : Fin n := ⟨(i₀.val + 1) % n, Nat.mod_lt _ hn_pos⟩
  let k : Fin n := ⟨(i₀.val + n - 1) % n, Nat.mod_lt _ hn_pos⟩
  -- Auxiliary: (k.val + 1) % n = i₀.val (k is the predecessor of i₀ in the cycle)
  -- omega can't handle % with variable n, so we do explicit cases on i₀.val
  have hk_succ : (k.val + 1) % n = i₀.val := by
    simp only [k]
    rcases Nat.eq_zero_or_pos i₀.val with h0 | hpos
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n),
          show n - 1 + 1 = n from by omega, Nat.mod_self]
    · rw [show i₀.val + n - 1 = (i₀.val - 1) + n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i₀.val - 1 < n),
          show i₀.val - 1 + 1 = i₀.val from by omega,
          Nat.mod_eq_of_lt i₀.isLt]
  -- i₀ ≠ j (n ≥ 4 > 1)
  have hi₀j : i₀ ≠ j := by
    intro heq
    have hval := congr_arg Fin.val heq
    simp only [j] at hval
    rcases Nat.lt_or_ge (i₀.val + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval; omega
    · rw [show i₀.val + 1 = n from by omega, Nat.mod_self] at hval; omega
  -- i₀ ≠ k (n ≥ 4 > 1)
  have hi₀k : i₀ ≠ k := by
    intro heq
    have hval := congr_arg Fin.val heq
    simp only [k] at hval
    rcases Nat.eq_zero_or_pos i₀.val with h0 | hpos
    · rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)] at hval; omega
    · rw [show i₀.val + n - 1 = (i₀.val - 1) + n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i₀.val - 1 < n)] at hval
      omega
  -- j ≠ k (n ≥ 4 > 2)
  have hjk : j ≠ k := by
    intro heq
    have hval := congr_arg Fin.val heq
    simp only [j, k] at hval
    rcases Nat.lt_or_ge (i₀.val + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval
      rcases Nat.eq_zero_or_pos i₀.val with h0 | hpos
      · -- i₀.val = 0: hval becomes 1 = (n-1) % n = n-1, contradicting n ≥ 4
        simp only [h0, Nat.zero_add] at hval
        rw [Nat.mod_eq_of_lt (by omega : n - 1 < n)] at hval; omega
      · rw [show i₀.val + n - 1 = (i₀.val - 1) + n from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i₀.val - 1 < n)] at hval
        omega
    · rw [show i₀.val + 1 = n from by omega, Nat.mod_self] at hval
      rw [show i₀.val + n - 1 = (i₀.val - 1) + n from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i₀.val - 1 < n)] at hval
      omega
  -- Minimality gives strict lower bounds
  have hfj : f i₀ < f j :=
    lt_of_le_of_ne (hi₀_min j (Finset.mem_univ j)) (f.injective.ne hi₀j)
  have hfk : f i₀ < f k :=
    lt_of_le_of_ne (hi₀_min k (Finset.mem_univ k)) (f.injective.ne hi₀k)
  -- Cycle edges at i₀ and at k
  have hAdj_j : G.Adj (f i₀) (f j) := hcycle i₀
  have hAdj_k : G.Adj (f i₀) (f k) := by
    have hck := hcycle k
    have : (⟨(k.val + 1) % n, Nat.mod_lt _ hn_pos⟩ : Fin n) = i₀ := Fin.ext hk_succ
    rw [this] at hck; exact G.symm hck
  -- Closed condition gives the chord f j — f k
  have hchord : G.Adj (f j) (f k) :=
    h.1 hfj hfk (f.injective.ne hjk) hAdj_j hAdj_k
  -- j and k are non-consecutive (distance 2 in a cycle of length ≥ 4)
  refine ⟨j, k, ?_, ?_, hchord⟩
  · -- (k.val + 1) % n ≠ j.val  ←→  i₀.val ≠ (i₀.val + 1) % n
    rw [hk_succ]; simp only [j]
    rcases Nat.lt_or_ge (i₀.val + 1) n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; omega
    · rw [show i₀.val + 1 = n from by omega, Nat.mod_self]; omega
  · -- (j.val + 1) % n ≠ k.val  (j's successor is i₀+2 mod n, not i₀-1)
    simp only [j, k]
    rcases Nat.eq_zero_or_pos i₀.val with h0 | hpos
    · -- i₀.val = 0: j.val = 1, j.succ.val = 2, k.val = n-1
      rw [h0, Nat.zero_add, Nat.mod_eq_of_lt (by omega : 1 < n),
          show (1 : ℕ) + 1 = 2 from rfl, Nat.mod_eq_of_lt (by omega : 2 < n),
          Nat.zero_add, Nat.mod_eq_of_lt (by omega : n - 1 < n)]
      omega
    · rcases Nat.lt_or_ge (i₀.val + 1) n with hlt | hge
      · -- j.val = i₀.val + 1, k.val = i₀.val - 1
        rw [Nat.mod_eq_of_lt hlt,
            show i₀.val + n - 1 = (i₀.val - 1) + n from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i₀.val - 1 < n)]
        rcases Nat.lt_or_ge (i₀.val + 2) n with hlt2 | hge2
        · rw [show i₀.val + 1 + 1 = i₀.val + 2 from by omega,
              Nat.mod_eq_of_lt hlt2]; omega
        · rw [show i₀.val + 1 + 1 = n from by omega, Nat.mod_self]; omega
      · -- i₀.val = n - 1: j.val = 0, j.succ.val = 1, k.val = n - 2
        rw [show i₀.val + 1 = n from by omega, Nat.mod_self, Nat.zero_add,
            Nat.mod_eq_of_lt (by omega : 1 < n),
            show i₀.val + n - 1 = (i₀.val - 1) + n from by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : i₀.val - 1 < n)]
        omega

/-- Proposition 1.2(2): Every closed graph is claw-free. -/
theorem closedGraph_isClawFree (G : SimpleGraph V) (h : IsClosedGraph G) :
    IsClawFree G := by
  intro c a b d hab hbd had cadj_a cadj_b cadj_d
  -- Case split on position of each of a, b, d relative to c.
  -- In each of the 8 cases, two of the three vertices lie on the same side of c,
  -- and we apply condition 1 (both > c) or condition 2 (both < c) of IsClosedGraph.
  rcases lt_or_gt_of_ne (G.ne_of_adj cadj_a).symm with ha | ha <;>
    rcases lt_or_gt_of_ne (G.ne_of_adj cadj_b).symm with hb | hb <;>
    rcases lt_or_gt_of_ne (G.ne_of_adj cadj_d).symm with hd | hd
  · -- a < c, b < c, d < c: use condition 2 on (a, b) both below c
    exact Or.inl (h.2 ha hb hab (G.symm cadj_a) (G.symm cadj_b))
  · -- a < c, b < c, c < d
    exact Or.inl (h.2 ha hb hab (G.symm cadj_a) (G.symm cadj_b))
  · -- a < c, c < b, d < c: use condition 2 on (a, d) both below c
    exact Or.inr (Or.inr (h.2 ha hd had (G.symm cadj_a) (G.symm cadj_d)))
  · -- a < c, c < b, c < d: use condition 1 on (b, d) both above c
    exact Or.inr (Or.inl (h.1 hb hd hbd cadj_b cadj_d))
  · -- c < a, b < c, d < c: use condition 2 on (b, d) both below c
    exact Or.inr (Or.inl (h.2 hb hd hbd (G.symm cadj_b) (G.symm cadj_d)))
  · -- c < a, b < c, c < d: use condition 1 on (a, d) both above c
    exact Or.inr (Or.inr (h.1 ha hd had cadj_a cadj_d))
  · -- c < a, c < b, d < c: use condition 1 on (a, b) both above c
    exact Or.inl (h.1 ha hb hab cadj_a cadj_b)
  · -- c < a, c < b, c < d
    exact Or.inl (h.1 ha hb hab cadj_a cadj_b)

/-- Proposition 1.2: Every closed graph is chordal and claw-free. -/
theorem prop_1_2 (G : SimpleGraph V) (h : IsClosedGraph G) :
    IsChordal G ∧ IsClawFree G :=
  ⟨closedGraph_isChordal G h, closedGraph_isClawFree G h⟩

/-! ## The directed graph G* and shortest paths (Proposition 1.4) -/

/-- An arc in G*: the edge {i,j} is directed i → j when i < j. -/
def directedAdj (G : SimpleGraph V) (i j : V) : Prop :=
  G.Adj i j ∧ i < j

/-- A list forms a directed walk if each consecutive pair is a directed edge. -/
def IsDirectedWalk (G : SimpleGraph V) : List V → Prop
  | []          => False
  | [_]         => True
  | (a :: b :: rest) => directedAdj G a b ∧ IsDirectedWalk G (b :: rest)

/--
**Proposition 1.4** (Herzog et al. 2010): G is closed with respect to the given
linear order if and only if for every pair i < j, all shortest walks from i to j
in G are directed (every edge goes from smaller to larger vertex).

The associated acyclic directed graph G* (with arrow i → j whenever {i,j} ∈ E(G)
and i < j) satisfies: all shortest undirected paths between any two vertices are
directed. This characterizes closed graphs.

Note: The hypothesis applies to ALL pairs i < j (not just adjacent ones). When
i and j are not connected, the quantifier over walks is vacuously true.

Reference: Herzog et al. (2010), Proposition 1.4 ("characterization").
-/
theorem prop_1_4 (G : SimpleGraph V) :
    IsClosedGraph G ↔
    ∀ (i j : V), i < j →
    ∀ (w : G.Walk i j), w.length = G.dist i j → IsDirectedWalk G w.support := by
  constructor
  · -- (→) closed graph → all shortest walks directed
    -- Proof: if not directed, find first local extremum, use closedness to shortcut. Sorry.
    intro _hClosed
    sorry
  · -- (←) all shortest walks directed → closed graph
    intro h
    refine ⟨?_, ?_⟩
    · -- Condition 1: i < j → i < k → j ≠ k → G.Adj i j → G.Adj i k → G.Adj j k
      intro i j k hij hik hjk_ne hadj_ij hadj_ik
      rcases lt_or_gt_of_ne hjk_ne with hjk | hkj
      · -- Case j < k: build walk j → i → k, get contradiction
        by_contra h_nadj
        let W := Walk.cons hadj_ij.symm (Walk.cons hadj_ik Walk.nil)
        have hW_len : W.length = 2 := rfl
        have hd_le : G.dist j k ≤ 2 := hW_len ▸ dist_le W
        have hd_pos : 0 < G.dist j k := W.reachable.pos_dist_of_ne (ne_of_lt hjk)
        have hd1 : G.dist j k ≠ 1 := mt dist_eq_one_iff_adj.mp h_nadj
        have hd2 : G.dist j k = 2 := by omega
        have hdirected := h j k hjk W (by rw [hW_len, hd2])
        -- hdirected : IsDirectedWalk G [j, i, k]; first step requires j < i, false
        exact absurd hdirected.1.2 (not_lt.mpr hij.le)
      · -- Case k < j: build walk k → i → j, get contradiction
        -- hkj : j > k, equivalently k < j
        by_contra h_nadj
        let W := Walk.cons hadj_ik.symm (Walk.cons hadj_ij Walk.nil)
        have hW_len : W.length = 2 := rfl
        have hkj' : k < j := hkj
        have hd_le : G.dist k j ≤ 2 := hW_len ▸ dist_le W
        have hd_pos : 0 < G.dist k j := W.reachable.pos_dist_of_ne (ne_of_lt hkj')
        have hd1 : G.dist k j ≠ 1 := fun h => h_nadj (dist_eq_one_iff_adj.mp h).symm
        have hd2 : G.dist k j = 2 := by omega
        have hdirected := h k j hkj' W (by rw [hW_len, hd2])
        -- hdirected : IsDirectedWalk G [k, i, j]; first step requires k < i, false
        exact absurd hdirected.1.2 (not_lt.mpr hik.le)
    · -- Condition 2: i < k → j < k → i ≠ j → G.Adj i k → G.Adj j k → G.Adj i j
      intro i j k hik hjk hij_ne hadj_ik hadj_jk
      rcases lt_or_gt_of_ne hij_ne with hij | hji
      · -- Case i < j: build walk i → k → j, get contradiction
        by_contra h_nadj
        let W := Walk.cons hadj_ik (Walk.cons hadj_jk.symm Walk.nil)
        have hW_len : W.length = 2 := rfl
        have hd_le : G.dist i j ≤ 2 := hW_len ▸ dist_le W
        have hd_pos : 0 < G.dist i j := W.reachable.pos_dist_of_ne (ne_of_lt hij)
        have hd1 : G.dist i j ≠ 1 := mt dist_eq_one_iff_adj.mp h_nadj
        have hd2 : G.dist i j = 2 := by omega
        have hdirected := h i j hij W (by rw [hW_len, hd2])
        -- hdirected : IsDirectedWalk G [i, k, j]; second step requires k < j, false
        exact absurd hdirected.2.1.2 (not_lt.mpr hjk.le)
      · -- Case j < i: build walk j → k → i, get contradiction
        -- hji : i > j, equivalently j < i
        by_contra h_nadj
        let W := Walk.cons hadj_jk (Walk.cons hadj_ik.symm Walk.nil)
        have hW_len : W.length = 2 := rfl
        have hji' : j < i := hji
        have hd_le : G.dist j i ≤ 2 := hW_len ▸ dist_le W
        have hd_pos : 0 < G.dist j i := W.reachable.pos_dist_of_ne (ne_of_lt hji')
        have hd1 : G.dist j i ≠ 1 := fun h => h_nadj (dist_eq_one_iff_adj.mp h).symm
        have hd2 : G.dist j i = 2 := by omega
        have hdirected := h j i hji' W (by rw [hW_len, hd2])
        -- hdirected : IsDirectedWalk G [j, k, i]; second step requires k < i, false
        exact absurd hdirected.2.1.2 (not_lt.mpr hik.le)

/--
**Corollary 1.3** (Herzog et al. 2010): A bipartite graph is closed if and only if
it is a **path graph** (a forest in which every vertex has degree at most 2,
i.e., a disjoint union of paths).

Proof sketch: A bipartite graph has no odd cycles. A closed graph is chordal,
and a chordal graph with no odd cycles must be a forest. If that forest is not
a disjoint union of paths, it contains an induced claw, contradicting Prop. 1.2(2).

Reference: Herzog et al. (2010), Corollary 1.3.
-/
theorem cor_1_3 (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj]
    (hBip : ∃ (φ : V → Bool), ∀ ⦃u v : V⦄, G.Adj u v → φ u ≠ φ v) :
    IsClosedGraph G ↔ G.IsAcyclic ∧ ∀ v, G.degree v ≤ 2 := by
  sorry

/-! ## Admissible paths (Section 2) -/

/--
A list `π` is an **admissible path** from `i` to `j` in G (with `i < j`) if:
1. `π` starts at `i`, ends at `j`, with no repeated vertices.
2. Every internal vertex satisfies `v < i` or `v > j`.
3. No proper sublist satisfying 1–2 exists (minimality).
4. Consecutive vertices in `π` are adjacent in G.

Reference: Herzog et al. (2010), Section 2.
-/
def IsAdmissiblePath (G : SimpleGraph V) (i j : V) (π : List V) : Prop :=
  i < j ∧
  π.head? = some i ∧
  π.getLast? = some j ∧
  π.Nodup ∧
  (∀ v ∈ π, v = i ∨ v = j ∨ v < i ∨ j < v) ∧
  π.Chain' (fun a b => G.Adj a b) ∧
  ∀ (π' : List V),
    π'.Sublist π → π' ≠ π →
    π'.head? = some i → π'.getLast? = some j →
    ¬ (∀ v ∈ π', v = i ∨ v = j ∨ v < i ∨ j < v)

/-- Every edge {i,j} with i < j yields the trivial admissible path [i, j]. -/
theorem edge_is_admissible (G : SimpleGraph V) {i j : V}
    (h : G.Adj i j) (hij : i < j) :
    IsAdmissiblePath G i j [i, j] := by
  refine ⟨hij, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [List.Nodup, G.ne_of_adj h]
  · intro v hv
    simp at hv
    rcases hv with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · simp [List.Chain', h]
  · intro π' hSub hNe hHead hLast _
    have hij_ne : i ≠ j := G.ne_of_adj h
    apply hNe
    -- Extract the leading vertex: π' = i :: t
    obtain ⟨t, rfl⟩ : ∃ t, π' = i :: t := by
      cases π' with
      | nil => simp at hHead
      | cons a t =>
        simp only [List.head?_cons, Option.some.injEq] at hHead
        exact ⟨t, by rw [hHead]⟩
    -- Case-split on how (i :: t) is a sublist of (i :: [j])
    cases hSub with
    | cons _ hSub' =>
      -- hSub' : (i :: t) <+ [j]; length forces t = []
      exfalso
      cases t with
      | nil =>
        simp at hLast
        exact hij_ne hLast
      | cons _ _ =>
        have h1 := hSub'.length_le
        simp only [List.length_cons, List.length_nil] at h1
        omega
    | cons₂ _ hSub' =>
      -- hSub' : t <+ [j]
      cases hSub' with
      | cons _ hSub'' =>
        -- hSub'' : t <+ []; forces t = []
        exfalso
        cases hSub''
        simp at hLast
        exact hij_ne hLast
      | cons₂ _ hSub'' =>
        -- t = j :: t'' with hSub'' : t'' <+ []
        cases hSub''
        rfl

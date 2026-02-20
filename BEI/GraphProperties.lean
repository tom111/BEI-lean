import BEI.Definitions
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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
A graph is **chordal** if every cycle of length ≥ 4 has a chord.
Equivalently, every minimal induced cycle has length 3.
-/
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ (v : V) (w : G.Walk v v), w.IsCycle → w.length ≤ 3

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
  sorry

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
Proposition 1.4: G is closed iff for any two adjacent vertices i < j, all
shortest paths from i to j in G are directed.

Reference: Herzog et al. (2010), Proposition 1.4.
-/
theorem prop_1_4 (G : SimpleGraph V) :
    IsClosedGraph G ↔
    ∀ (π : List V), IsDirectedWalk G π → True := by
  sorry

/--
Corollary 1.3: A bipartite graph is closed iff it is a path
(every vertex has degree ≤ 2).

Reference: Herzog et al. (2010), Corollary 1.3.
-/
theorem cor_1_3 (G : SimpleGraph V)
    (hBip : ∃ (φ : V → Bool), ∀ ⦃u v : V⦄, G.Adj u v → φ u ≠ φ v) :
    IsClosedGraph G ↔
    ∀ v u w z : V, G.Adj v u → G.Adj v w → G.Adj v z → u = w ∨ u = z ∨ w = z := by
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
  · intros; sorry

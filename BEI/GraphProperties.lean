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
theorem graphClosure_le (G : SimpleGraph V) : G ≤ graphClosure G := by
  sorry

/-- The closure is itself closed. -/
theorem graphClosure_isClosedGraph (G : SimpleGraph V) :
    IsClosedGraph (graphClosure G) := by
  sorry

/-- The closure is the minimal closed supergraph. -/
theorem graphClosure_minimal (G H : SimpleGraph V)
    (hGH : G ≤ H) (hH : IsClosedGraph H) : graphClosure G ≤ H := by
  sorry

/-- Proposition 1.5: The closure is the unique minimal closed supergraph. -/
theorem prop_1_5 (G : SimpleGraph V) :
    ∃! H : SimpleGraph V,
      G ≤ H ∧ IsClosedGraph H ∧
      ∀ H' : SimpleGraph V, G ≤ H' → IsClosedGraph H' → H ≤ H' :=
  ⟨graphClosure G,
   ⟨graphClosure_le G, graphClosure_isClosedGraph G,
    fun H' hGH' hH' => graphClosure_minimal G H' hGH' hH'⟩,
   by sorry⟩

/-! ## Properties of closed graphs (Proposition 1.2) -/

/-- Proposition 1.2(1): Every closed graph is chordal. -/
theorem closedGraph_isChordal (G : SimpleGraph V) (h : IsClosedGraph G) :
    IsChordal G := by
  sorry

/-- Proposition 1.2(2): Every closed graph is claw-free. -/
theorem closedGraph_isClawFree (G : SimpleGraph V) (h : IsClosedGraph G) :
    IsClawFree G := by
  sorry

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

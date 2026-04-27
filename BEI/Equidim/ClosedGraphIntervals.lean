import BEI.GraphProperties
import BEI.ClosedGraphs
import BEI.PrimeIdeals

variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

noncomputable section

open SimpleGraph

/-!
# Closed-graph interval and component-count lemmas

For a connected closed graph `G`, edges span intervals
(`closedGraph_adj_between`), components of `G[V \ S]` are convex along the
linear order (`reflTransGen_convex_closed`), and the number of connected
components of `G[V \ S]` is at most `S.card + 1`
(`closedGraph_componentCount_le_card_add_one`).

## Reference: Herzog et al. (2010), Section 1
-/

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

end

import BEI.MinimalPrimes
import Mathlib.Combinatorics.SimpleGraph.Matching

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Cycle-specific minimal-prime consequences

This file isolates the cycle component-count lemmas and the unmixed branch of
Corollary 3.7 from `BEI/MinimalPrimes.lean`.
-/

noncomputable section

open MvPolynomial SimpleGraph

private def singletonSurvivors (v : V) : Set V := {x : V | x ∉ ({v} : Finset V)}

private def pairSurvivors (u w : V) : Set V := {x : V | x ∉ ({u, w} : Finset V)}

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma mem_singletonSurvivors_iff {v x : V} :
    x ∈ singletonSurvivors v ↔ x ≠ v := by
  simp [singletonSurvivors]

omit [LinearOrder V] [Fintype V] in
private lemma mem_pairSurvivors_iff {u w x : V} :
    x ∈ pairSurvivors u w ↔ x ≠ u ∧ x ≠ w := by
  simp [pairSurvivors, Finset.mem_insert, Finset.mem_singleton, not_or]

omit [Fintype V] in
private lemma fst_ne_of_mem_pairSurvivors {u w x : V} (hx : x ∈ pairSurvivors u w) : x ≠ u :=
  (mem_pairSurvivors_iff.mp hx).1

omit [Fintype V] in
private lemma snd_ne_of_mem_pairSurvivors {u w x : V} (hx : x ∈ pairSurvivors u w) : x ≠ w :=
  (mem_pairSurvivors_iff.mp hx).2

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Transfer a `G`-walk whose support lies in `S` to reachability in `G.induce S`. -/
private lemma reachable_induce_of_walk (G : SimpleGraph V) (S : Set V)
    {a b : V} (w : G.Walk a b) (hsup : ∀ x ∈ w.support, x ∈ S) :
    (G.induce S).Reachable ⟨a, hsup a w.start_mem_support⟩ ⟨b, hsup b w.end_mem_support⟩ := by
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v w hadj rest ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hsup
    have hsup' : ∀ x ∈ rest.support, x ∈ S := fun x hx => hsup x (Or.inr hx)
    exact (SimpleGraph.Adj.reachable (show (G.induce S).Adj ⟨u, hsup u (Or.inl rfl)⟩
      ⟨v, hsup v (Or.inr rest.start_mem_support)⟩ from hadj)).trans (ih hsup')

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma isCycles_of_isCycleGraph (G : SimpleGraph V) (hCyc : IsCycleGraph G) :
    G.IsCycles := by
  intro v _
  obtain ⟨u', w', huw, huv, hvw, honly⟩ := hCyc.2 v
  apply Set.ncard_eq_two.mpr
  refine ⟨u', w', huw, ?_⟩
  ext z
  simp only [SimpleGraph.neighborSet]
  exact ⟨fun hz => honly z hz, fun hz => hz.elim (· ▸ huv) (· ▸ hvw)⟩

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma mem_support_of_cycle_walk (G : SimpleGraph V) (hConn : G.Connected) {u : V}
    {c : G.Walk u u}
    (hc_verts : c.toSubgraph.verts = (G.connectedComponentMk u).supp) (v : V) :
    v ∈ c.support := by
  rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hc_verts]
  simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
  exact hConn.preconnected v u

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma mem_tail_support_of_ne (G : SimpleGraph V) {a b : V} (w : G.Walk a b)
    (hw : ¬w.Nil) {v : V} (hv : v ≠ a) (hmem : v ∈ w.support) :
    v ∈ w.tail.support := by
  rw [w.support_tail_of_not_nil hw]
  have h_cons := (List.cons_head_tail w.support_ne_nil).symm
  rw [SimpleGraph.Walk.head_support w] at h_cons
  rw [h_cons] at hmem
  exact (List.mem_cons.mp hmem).resolve_left hv

omit [DecidableEq V] in
private lemma cycle_edge_mem_edges (G : SimpleGraph V) (hConn : G.Connected)
    (hcycles : G.IsCycles) {u : V} {c : G.Walk u u} (hc_cycle : c.IsCycle)
    (hc_verts : c.toSubgraph.verts = (G.connectedComponentMk u).supp) :
    ∀ a b : V, G.Adj a b → s(a, b) ∈ c.edges := by
  intro a b hab
  rw [← SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
  have ha_mem : a ∈ c.support := mem_support_of_cycle_walk G hConn hc_verts a
  exact (hc_cycle.adj_toSubgraph_iff_of_isCycles hcycles
    (c.mem_verts_toSubgraph.mpr ha_mem) b).mpr hab

/-! ## Corollary 3.7 unmixed branch -/

-- Hamiltonian cycle extraction plus `takeUntil` reachability is still expensive here.
omit [DecidableEq V] in
/-- In a cycle graph, the induced subgraph on `V \ {v}` is preconnected.
Uses the `IsCycles` API: obtain a Hamiltonian cycle walk at `v`, take its tail
(a path visiting every other vertex), then transfer initial segments into the
induced subgraph. -/
private lemma cycle_induce_preconnected (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (_hn : 3 ≤ Fintype.card V) :
    (G.induce (singletonSurvivors v)).Preconnected := by
  classical
  obtain ⟨hConn, hDeg⟩ := hCyc
  obtain ⟨n1, _, _, hadj1, _, _⟩ := hDeg v
  let S := singletonSurvivors v
  let G' := G.induce S
  have hcycles : G.IsCycles := by
    intro w _
    obtain ⟨u', w', huw, huv, hvw, honly⟩ := hDeg w
    apply Set.ncard_eq_two.mpr
    refine ⟨u', w', huw, ?_⟩
    ext z
    simp only [SimpleGraph.neighborSet]
    exact ⟨fun hz => honly z hz, fun hz => hz.elim (· ▸ huv) (· ▸ hvw)⟩
  have hv_supp : v ∈ (G.connectedComponentMk v).supp := by
    simp [SimpleGraph.ConnectedComponent.supp]
  obtain ⟨c, hc_cycle, hc_verts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv_supp ⟨n1, hadj1⟩
  have htail_path := hc_cycle.isPath_tail
  have hc_snd_ne : c.snd ≠ v := (G.ne_of_adj (c.adj_snd hc_cycle.not_nil)).symm
  have hc_snd_S : c.snd ∈ S := by
    simpa [S, mem_singletonSurvivors_iff] using hc_snd_ne
  suffices hsuff : ∀ (t : V) (ht : t ∈ S), G'.Reachable ⟨c.snd, hc_snd_S⟩ ⟨t, ht⟩ by
    intro ⟨a, ha⟩ ⟨b, hb⟩
    exact (hsuff a ha).symm.trans (hsuff b hb)
  intro t ht
  have ht_ne : t ≠ v := by
    simpa [S, mem_singletonSurvivors_iff] using ht
  have ht_supp : t ∈ c.support := mem_support_of_cycle_walk G hConn hc_verts t
  have ht_tail : t ∈ c.tail.support :=
    mem_tail_support_of_ne G c hc_cycle.not_nil ht_ne ht_supp
  let w := c.tail.takeUntil t ht_tail
  have hv_not : v ∉ w.support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil htail_path ht_tail (Ne.symm ht_ne)
  have hw_S : ∀ x ∈ w.support, x ∈ S := by
    intro x hx
    have hxv : x ≠ v := by
      intro h
      exact hv_not (h ▸ hx)
    simpa [S, mem_singletonSurvivors_iff] using hxv
  exact reachable_induce_of_walk G S w hw_S

omit [DecidableEq V] in
/-- Removing a single vertex from a cycle graph gives a connected induced
subgraph. Therefore `componentCount G {v} = 1`. -/
theorem cycle_componentCount_singleton (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    componentCount G {v} = 1 := by
  classical
  unfold componentCount
  let S := singletonSurvivors v
  let G' := G.induce S
  obtain ⟨n1, _, _, hadj1, _, _⟩ := hCyc.2 v
  have hn1v : n1 ≠ v := G.ne_of_adj hadj1.symm
  have hn1S : n1 ∈ S := by
    simpa [S, mem_singletonSurvivors_iff] using hn1v
  have hpc : G'.Preconnected := by
    simpa [G', S] using cycle_induce_preconnected G hCyc v hn
  haveI := hpc.subsingleton_connectedComponent
  change Nat.card G'.ConnectedComponent = 1
  exact Nat.card_of_subsingleton (G'.connectedComponentMk ⟨n1, hn1S⟩)

omit [LinearOrder V] [DecidableEq V] in
/-- On a cycle with `n ≥ 4` vertices, there exist two non-adjacent vertices. -/
theorem cycle_exists_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 4 ≤ Fintype.card V) :
    ∃ u w : V, u ≠ w ∧ ¬G.Adj u w := by
  classical
  have hDeg := hCyc.2
  obtain ⟨v⟩ := hCyc.1.nonempty
  obtain ⟨n1, n2, _, hadj1, hadj2, honly⟩ := hDeg v
  have h3 : ({v, n1, n2} : Finset V).card ≤ 3 := Finset.card_le_three
  have : ∃ w : V, w ∉ ({v, n1, n2} : Finset V) := by
    by_contra h
    push_neg at h
    have hsub : Finset.univ ⊆ ({v, n1, n2} : Finset V) := fun x _ => h x
    have huniv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
    linarith [Finset.card_le_card hsub, h3, huniv, hn]
  obtain ⟨w, hw⟩ := this
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  exact ⟨v, w, Ne.symm hw.1, fun hadj => (honly w hadj).elim hw.2.1 hw.2.2⟩

omit [Fintype V] in
private lemma cycle_edge_on_arc (G : SimpleGraph V) {u w : V} (S : Set V)
    (hS : S = pairSurvivors u w) {c : G.Walk u u} (hc_not_nil : ¬c.Nil)
    {arc1 : G.Walk c.snd w} {arc2 : G.Walk w u}
    (htail_edges : c.tail.edges = arc1.edges ++ arc2.edges)
    (hedge_of_adj : ∀ a b : V, G.Adj a b → s(a, b) ∈ c.edges) :
    ∀ a b : V, a ∈ S → b ∈ S → G.Adj a b →
      s(a, b) ∈ arc1.edges ∨ s(a, b) ∈ arc2.edges := by
  intro a b haS hbS hab
  have ha_pair : a ∈ pairSurvivors u w := by simpa [hS] using haS
  have hb_pair : b ∈ pairSurvivors u w := by simpa [hS] using hbS
  have hab_c := hedge_of_adj a b hab
  rw [← c.cons_tail_eq hc_not_nil, SimpleGraph.Walk.edges_cons] at hab_c
  have ha_ne_u : a ≠ u := fst_ne_of_mem_pairSurvivors ha_pair
  rcases List.mem_cons.mp hab_c with h | h
  · exfalso
    have hb_ne_u : b ≠ u := fst_ne_of_mem_pairSurvivors hb_pair
    have hu_mem : u ∈ (s(a, b) : Sym2 V) := h ▸ Sym2.mem_mk_left u c.snd
    rcases Sym2.mem_iff.mp hu_mem with h_eq | h_eq
    · exact ha_ne_u h_eq.symm
    · exact hb_ne_u h_eq.symm
  · exact List.mem_append.mp (htail_edges ▸ h)

omit [Fintype V] in
private lemma cycle_vertex_on_arc {G : SimpleGraph V} {u w : V} (S : Set V)
    (hS : S = pairSurvivors u w) {c : G.Walk u u} {arc1 : G.Walk c.snd w}
    {arc2 : G.Walk w u} (hmem_tail_of_ne_u : ∀ v : V, v ≠ u → v ∈ c.tail.support)
    (htail_spec : arc1.append arc2 = c.tail) :
    ∀ v : V, v ∈ S → v ∈ arc1.support ∨ v ∈ arc2.support := by
  intro v hv
  have hv_pair : v ∈ pairSurvivors u w := by simpa [hS] using hv
  have hv_ne_u : v ≠ u := fst_ne_of_mem_pairSurvivors hv_pair
  have hv_tail := hmem_tail_of_ne_u v hv_ne_u
  rw [← htail_spec, SimpleGraph.Walk.support_append] at hv_tail
  rcases List.mem_append.mp hv_tail with h | h
  · exact Or.inl h
  · exact Or.inr (List.tail_subset _ h)

omit [Fintype V] in
private lemma cycle_arc1_reachable (G : SimpleGraph V) {u w : V} (S : Set V)
    (hS : S = pairSurvivors u w) {c : G.Walk u u} {arc1 : G.Walk c.snd w}
    (harc1_path : arc1.IsPath) (hu_not_arc1 : u ∉ arc1.support) (hc_snd_S : c.snd ∈ S) :
    ∀ (t : V), t ∈ arc1.support → t ≠ w → (ht : t ∈ S) →
      (G.induce S).Reachable ⟨c.snd, hc_snd_S⟩ ⟨t, ht⟩ := by
  intro t ht htw htS
  have hw_not : w ∉ (arc1.takeUntil t ht).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil harc1_path ht htw.symm
  have hu_not : u ∉ (arc1.takeUntil t ht).support := fun hu =>
    hu_not_arc1 (SimpleGraph.Walk.support_takeUntil_subset arc1 ht hu)
  exact reachable_induce_of_walk G S (arc1.takeUntil t ht) fun x hx => by
    have hxu : x ≠ u := by
      intro h
      exact hu_not (h ▸ hx)
    have hxw : x ≠ w := by
      intro h
      exact hw_not (h ▸ hx)
    simpa [hS, mem_pairSurvivors_iff] using ⟨hxu, hxw⟩

omit [Fintype V] in
private lemma cycle_arc2_reachable (G : SimpleGraph V) {u w : V} (S : Set V)
    (hS : S = pairSurvivors u w) {arc2 : G.Walk w u} (harc2_path : arc2.IsPath)
    (harc2_not_nil : ¬arc2.Nil) (harc2_snd_S : arc2.snd ∈ S) :
    ∀ (t : V), t ∈ arc2.support → t ≠ w → t ≠ u → (ht : t ∈ S) →
      (G.induce S).Reachable ⟨arc2.snd, harc2_snd_S⟩ ⟨t, ht⟩ := by
  intro t ht htw htu htS
  have harc2_tail_path : arc2.tail.IsPath := by
    rw [← SimpleGraph.Walk.cons_tail_eq arc2 harc2_not_nil] at harc2_path
    exact harc2_path.of_cons
  have ht_tail : t ∈ arc2.tail.support := by
    have hcons := arc2.cons_support_tail harc2_not_nil
    rw [← hcons] at ht
    exact (List.mem_cons.mp ht).resolve_left htw
  have hw_not_tail : w ∉ arc2.tail.support := by
    intro hmem
    have hnodup := harc2_path.support_nodup
    rw [← arc2.cons_support_tail harc2_not_nil] at hnodup
    exact (List.nodup_cons.mp hnodup).1 hmem
  have hu_not : u ∉ (arc2.tail.takeUntil t ht_tail).support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil harc2_tail_path ht_tail htu.symm
  have hw_not : w ∉ (arc2.tail.takeUntil t ht_tail).support := fun hw =>
    hw_not_tail (SimpleGraph.Walk.support_takeUntil_subset arc2.tail ht_tail hw)
  exact reachable_induce_of_walk G S (arc2.tail.takeUntil t ht_tail) fun x hx => by
    have hxu : x ≠ u := by
      intro h
      exact hu_not (h ▸ hx)
    have hxw : x ≠ w := by
      intro h
      exact hw_not (h ▸ hx)
    simpa [hS, mem_pairSurvivors_iff] using ⟨hxu, hxw⟩

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma cycle_arcs_intersect_only_at_split {G : SimpleGraph V} {u w : V}
    {c : G.Walk u u} {arc1 : G.Walk c.snd w} {arc2 : G.Walk w u}
    (htail_path : c.tail.IsPath) (harc2_not_nil : ¬arc2.Nil)
    (htail_spec : arc1.append arc2 = c.tail) :
    ∀ v : V, v ∈ arc1.support → v ∈ arc2.support → v = w := by
  intro v hv1 hv2
  by_contra hvw
  have hnodup := htail_path.support_nodup
  rw [← htail_spec, SimpleGraph.Walk.support_append] at hnodup
  have hv_arc2_tail : v ∈ arc2.support.tail := by
    rw [← arc2.support_tail_of_not_nil harc2_not_nil]
    have hcons := arc2.cons_support_tail harc2_not_nil
    rw [← hcons] at hv2
    exact (List.mem_cons.mp hv2).resolve_left hvw
  exact List.disjoint_of_nodup_append hnodup hv1 hv_arc2_tail

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
private lemma cycle_no_cross_edge {G : SimpleGraph V} {S : Set V}
    {u1 v1 u2 v2 : V} {arc1 : G.Walk u1 v1} {arc2 : G.Walk u2 v2}
    (hedge_on_arc : ∀ x y : V, x ∈ S → y ∈ S → G.Adj x y →
      s(x, y) ∈ arc1.edges ∨ s(x, y) ∈ arc2.edges) :
    ∀ x y : V, x ∈ S → y ∈ S → G.Adj x y →
      (x ∈ arc1.support ∧ y ∈ arc1.support) ∨ (x ∈ arc2.support ∧ y ∈ arc2.support) := by
  intro x y hx hy hxy
  rcases hedge_on_arc x y hx hy hxy with h | h
  · exact Or.inl
      ⟨SimpleGraph.Walk.fst_mem_support_of_mem_edges arc1 h,
        SimpleGraph.Walk.snd_mem_support_of_mem_edges arc1 h⟩
  · exact Or.inr
      ⟨SimpleGraph.Walk.fst_mem_support_of_mem_edges arc2 h,
        SimpleGraph.Walk.snd_mem_support_of_mem_edges arc2 h⟩

omit [Fintype V] in
private lemma cycle_pair_separated (G : SimpleGraph V) {u w : V} (S : Set V)
    (hS : S = pairSurvivors u w) {c : G.Walk u u} {arc1 : G.Walk c.snd w}
    {arc2 : G.Walk w u}
    (hno_cross_edge : ∀ x y : V, x ∈ S → y ∈ S → G.Adj x y →
      (x ∈ arc1.support ∧ y ∈ arc1.support) ∨ (x ∈ arc2.support ∧ y ∈ arc2.support))
    (harc_disjoint : ∀ v : V, v ∈ arc1.support → v ∈ arc2.support → v = w)
    (hc_snd_arc1 : c.snd ∈ arc1.support) (hc_snd_not_arc2 : c.snd ∉ arc2.support)
    (harc2_snd_not_arc1 : arc2.snd ∉ arc1.support) (hc_snd_S : c.snd ∈ S)
    (harc2_snd_S : arc2.snd ∈ S) :
    ¬(G.induce S).Reachable ⟨c.snd, hc_snd_S⟩ ⟨arc2.snd, harc2_snd_S⟩ := by
  intro ⟨p⟩
  suffices h : ∀ (a b : S) (q : (G.induce S).Walk a b),
      (a : V) ∈ arc1.support → (a : V) ∉ arc2.support → (b : V) ∈ arc1.support by
    exact harc2_snd_not_arc1 (h _ _ p hc_snd_arc1 hc_snd_not_arc2)
  intro a b q
  induction q with
  | nil =>
      intro ha _
      exact ha
  | @cons x y z hadj_xy rest ih =>
      intro hx_arc1 hx_not_arc2
      apply ih
      · rcases hno_cross_edge x y x.2 y.2 hadj_xy with ⟨_, hy1⟩ | ⟨hx2, _⟩
        · exact hy1
        · exact absurd hx2 hx_not_arc2
      · intro hy_arc2
        rcases hno_cross_edge x y x.2 y.2 hadj_xy with ⟨_, hy1⟩ | ⟨hx2, _⟩
        · have hyw := harc_disjoint y hy1 hy_arc2
          have hy_pair : (y : V) ∈ pairSurvivors u w := by simpa [hS] using y.2
          exact snd_ne_of_mem_pairSurvivors hy_pair hyw
        · exact hx_not_arc2 hx2

omit [Fintype V] in
private lemma cycle_components_cover (G : SimpleGraph V) {u w : V} (S : Set V)
    (hS : S = pairSurvivors u w) {c : G.Walk u u} {arc1 : G.Walk c.snd w}
    {arc2 : G.Walk w u} (hc_snd_S : c.snd ∈ S) (harc2_snd_S : arc2.snd ∈ S)
    (hmem_arc : ∀ v : V, v ∈ S → v ∈ arc1.support ∨ v ∈ arc2.support)
    (harc1_reach : ∀ (t : V), t ∈ arc1.support → t ≠ w → (ht : t ∈ S) →
      (G.induce S).Reachable ⟨c.snd, hc_snd_S⟩ ⟨t, ht⟩)
    (harc2_reach : ∀ (t : V), t ∈ arc2.support → t ≠ w → t ≠ u → (ht : t ∈ S) →
      (G.induce S).Reachable ⟨arc2.snd, harc2_snd_S⟩ ⟨t, ht⟩) :
    ∀ comp : (G.induce S).ConnectedComponent,
      comp = (G.induce S).connectedComponentMk ⟨c.snd, hc_snd_S⟩ ∨
        comp = (G.induce S).connectedComponentMk ⟨arc2.snd, harc2_snd_S⟩ := by
  intro comp
  obtain ⟨⟨v, hv⟩, rfl⟩ := Quot.exists_rep comp
  rcases hmem_arc v hv with harc | harc
  · have hv_pair : v ∈ pairSurvivors u w := by simpa [hS] using hv
    have hvw : v ≠ w := snd_ne_of_mem_pairSurvivors hv_pair
    exact Or.inl (SimpleGraph.ConnectedComponent.sound (harc1_reach v harc hvw hv).symm)
  · have hv_pair : v ∈ pairSurvivors u w := by simpa [hS] using hv
    have hvw : v ≠ w := snd_ne_of_mem_pairSurvivors hv_pair
    have hvu : v ≠ u := fst_ne_of_mem_pairSurvivors hv_pair
    exact Or.inr (SimpleGraph.ConnectedComponent.sound (harc2_reach v harc hvw hvu hv).symm)

-- The pair-removal theorem still assembles two arc decompositions and component separation.
/-- Removing two non-adjacent vertices from a cycle gives exactly `2` components. -/
theorem cycle_componentCount_pair_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (u w : V) (hne : u ≠ w) (hnadj : ¬G.Adj u w) (_hn : 4 ≤ Fintype.card V) :
    componentCount G {u, w} = 2 := by
  classical
  obtain ⟨hConn, hDeg⟩ := hCyc
  let S := pairSurvivors u w
  let G' := G.induce S
  unfold componentCount
  have hcycles : G.IsCycles := by
    intro v _
    obtain ⟨u', w', huw, huv, hvw, honly⟩ := hDeg v
    apply Set.ncard_eq_two.mpr
    refine ⟨u', w', huw, ?_⟩
    ext z
    simp only [SimpleGraph.neighborSet]
    exact ⟨fun hz => honly z hz, fun hz => hz.elim (· ▸ huv) (· ▸ hvw)⟩
  haveI : LocallyFinite G := fun _ => Fintype.ofFinite _
  obtain ⟨n1, _, _, hadj1, _, _⟩ := hDeg u
  obtain ⟨c, hc_cycle, hc_verts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (show u ∈ (G.connectedComponentMk u).supp by simp [SimpleGraph.ConnectedComponent.supp])
      ⟨n1, hadj1⟩
  have hedge_of_adj := cycle_edge_mem_edges G hConn hcycles hc_cycle hc_verts
  have htail_path := hc_cycle.isPath_tail
  have hc_not_nil := hc_cycle.not_nil
  have hc_snd_adj : G.Adj u c.snd := c.adj_snd hc_not_nil
  have hc_snd_ne_u : c.snd ≠ u := (G.ne_of_adj hc_snd_adj).symm
  have hc_snd_ne_w : c.snd ≠ w := fun h => hnadj (h ▸ hc_snd_adj)
  have hc_snd_pair : c.snd ∈ pairSurvivors u w := by
    exact mem_pairSurvivors_iff.mpr ⟨hc_snd_ne_u, hc_snd_ne_w⟩
  have hc_snd_S : c.snd ∈ S := by
    simpa [S] using hc_snd_pair
  have hmem_tail_of_ne_u : ∀ v : V, v ≠ u → v ∈ c.tail.support := by
    intro v hv
    exact mem_tail_support_of_ne G c hc_not_nil hv (mem_support_of_cycle_walk G hConn hc_verts v)
  have hw_tail : w ∈ c.tail.support := hmem_tail_of_ne_u w hne.symm
  let arc1 := c.tail.takeUntil w hw_tail
  let arc2 := c.tail.dropUntil w hw_tail
  have harc1_path : arc1.IsPath := htail_path.takeUntil hw_tail
  have harc2_path : arc2.IsPath := htail_path.dropUntil hw_tail
  have htail_spec : arc1.append arc2 = c.tail := c.tail.take_spec hw_tail
  have hu_not_arc1 : u ∉ arc1.support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil htail_path hw_tail hne
  have htail_edges : c.tail.edges = arc1.edges ++ arc2.edges := by
    rw [← htail_spec]
    exact SimpleGraph.Walk.edges_append arc1 arc2
  have hedge_on_arc : ∀ a b : V, a ∈ S → b ∈ S → G.Adj a b →
      s(a, b) ∈ arc1.edges ∨ s(a, b) ∈ arc2.edges :=
    cycle_edge_on_arc G S rfl hc_not_nil htail_edges hedge_of_adj
  have harc2_not_nil : ¬arc2.Nil := fun h => hne.symm (SimpleGraph.Walk.Nil.eq h)
  have harc2_snd_adj : G.Adj w arc2.snd := arc2.adj_snd harc2_not_nil
  have harc2_snd_ne_u : arc2.snd ≠ u := fun h => hnadj (h ▸ harc2_snd_adj).symm
  have harc2_snd_ne_w : arc2.snd ≠ w := (G.ne_of_adj harc2_snd_adj).symm
  have harc2_snd_pair : arc2.snd ∈ pairSurvivors u w := by
    exact mem_pairSurvivors_iff.mpr ⟨harc2_snd_ne_u, harc2_snd_ne_w⟩
  have harc2_snd_S : arc2.snd ∈ S := by
    simpa [S] using harc2_snd_pair
  have harc2_snd_mem : arc2.snd ∈ arc2.support :=
    List.mem_of_mem_tail (arc2.snd_mem_tail_support harc2_not_nil)
  have hmem_arc : ∀ v : V, v ∈ S → v ∈ arc1.support ∨ v ∈ arc2.support :=
    cycle_vertex_on_arc S rfl hmem_tail_of_ne_u htail_spec
  have harc1_reach : ∀ (t : V), t ∈ arc1.support → t ≠ w → (ht : t ∈ S) →
      G'.Reachable ⟨c.snd, hc_snd_S⟩ ⟨t, ht⟩ := by
    simpa [G'] using cycle_arc1_reachable G S rfl harc1_path hu_not_arc1 hc_snd_S
  have harc2_reach : ∀ (t : V), t ∈ arc2.support → t ≠ w → t ≠ u → (ht : t ∈ S) →
      G'.Reachable ⟨arc2.snd, harc2_snd_S⟩ ⟨t, ht⟩ := by
    simpa [G'] using cycle_arc2_reachable G S rfl harc2_path harc2_not_nil harc2_snd_S
  have harc_disjoint : ∀ v : V, v ∈ arc1.support → v ∈ arc2.support → v = w :=
    cycle_arcs_intersect_only_at_split htail_path harc2_not_nil htail_spec
  have hno_cross_edge : ∀ (a b : V), a ∈ S → b ∈ S → G.Adj a b →
      (a ∈ arc1.support ∧ b ∈ arc1.support) ∨ (a ∈ arc2.support ∧ b ∈ arc2.support) :=
    cycle_no_cross_edge hedge_on_arc
  have hc_snd_arc1 : c.snd ∈ arc1.support := arc1.start_mem_support
  have hc_snd_not_arc2 : c.snd ∉ arc2.support := fun h =>
    hc_snd_ne_w (harc_disjoint c.snd hc_snd_arc1 h)
  have harc2_snd_not_arc1 : arc2.snd ∉ arc1.support := fun h =>
    harc2_snd_ne_w (harc_disjoint arc2.snd h harc2_snd_mem)
  have hsep : ¬G'.Reachable ⟨c.snd, hc_snd_S⟩ ⟨arc2.snd, harc2_snd_S⟩ := by
    simpa [G'] using
      cycle_pair_separated G S rfl hno_cross_edge harc_disjoint hc_snd_arc1 hc_snd_not_arc2
        harc2_snd_not_arc1 hc_snd_S harc2_snd_S
  let comp1 := G'.connectedComponentMk ⟨c.snd, hc_snd_S⟩
  let comp2 := G'.connectedComponentMk ⟨arc2.snd, harc2_snd_S⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨comp1, comp2, fun heq => hsep (SimpleGraph.ConnectedComponent.exact heq), ?_⟩
  ext comp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  simpa [comp1, comp2, G'] using
    cycle_components_cover G S rfl hc_snd_S harc2_snd_S hmem_arc harc1_reach harc2_reach comp

omit [DecidableEq V] in
/--
**Corollary 3.7 (unmixed branch)**: For a cycle `G` with `n ≥ 3` vertices,
`J_G` is prime iff `J_G` is unmixed.

Reference: Herzog et al. (2010), Corollary 3.7 (a)↔(b)↔(c).
-/
theorem corollary_3_7_unmixed (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    (binomialEdgeIdeal (K := K) G).IsPrime ↔
    (binomialEdgeIdeal (K := K) G).IsUnmixed := by
  constructor
  · exact Ideal.IsPrime.isUnmixed
  · intro hunmixed
    rw [← corollary_3_7 (K := K) G hCyc hn]
    by_contra h4
    have hn4 : 4 ≤ Fintype.card V := by omega
    obtain ⟨u, w, huw, hnadj⟩ := cycle_exists_nonadj G hCyc hn4
    have hP0_min : primeComponent (K := K) G ∅ ∈
        (binomialEdgeIdeal (K := K) G).minimalPrimes := by
      exact (corollary_3_9 (K := K) G ∅ hCyc.1).mpr (Or.inl rfl)
    have hPuw_min : primeComponent (K := K) G {u, w} ∈
        (binomialEdgeIdeal (K := K) G).minimalPrimes := by
      apply (corollary_3_9 (K := K) G {u, w} hCyc.1).mpr
      right
      intro i hi
      rw [cutVertex_iff_componentCount]
      refine ⟨hi, ?_⟩
      rw [cycle_componentCount_pair_nonadj G hCyc u w huw hnadj hn4]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · subst i
        have hu_not_mem : u ∉ ({w} : Finset V) := by
          simp [huw]
        rw [show ({u, w} : Finset V) = insert u ({w} : Finset V) by rfl]
        rw [Finset.erase_insert hu_not_mem]
        rw [cycle_componentCount_singleton G hCyc _ (by omega)]
        omega
      · subst i
        have hw_not_mem : w ∉ ({u} : Finset V) := by
          simp [Ne.symm huw]
        rw [show ({u, w} : Finset V) = insert w ({u} : Finset V) by rw [Finset.pair_comm]]
        rw [Finset.erase_insert hw_not_mem]
        rw [cycle_componentCount_singleton G hCyc _ (by omega)]
        omega
    have hc0 : componentCount G ∅ = 1 := by
      rw [componentCount_empty]
      haveI := hCyc.1.preconnected.subsingleton_connectedComponent
      exact Nat.card_of_subsingleton (G.connectedComponentMk hCyc.1.nonempty.some)
    have hP0_ht : Ideal.height (primeComponent (K := K) G ∅) =
        (Fintype.card V - 1 : ℕ) := by
      rw [lemma_3_1 (K := K)]
      congr 1
      simp [hc0]
    have hcuw : componentCount G {u, w} = 2 :=
      cycle_componentCount_pair_nonadj G hCyc u w huw hnadj hn4
    have hPuw_ht : Ideal.height (primeComponent (K := K) G {u, w}) =
        (Fintype.card V : ℕ) := by
      rw [lemma_3_1 (K := K)]
      congr 1
      rw [hcuw, Finset.card_pair huw]
      omega
    have : Ideal.height (primeComponent (K := K) G ∅) ≠
        Ideal.height (primeComponent (K := K) G {u, w}) := by
      rw [hP0_ht, hPuw_ht]
      simp only [ne_eq, Nat.cast_inj]
      omega
    exact this (hunmixed _ _ hP0_min hPuw_min)

end

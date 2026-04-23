import BEI.PrimeDecomposition

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Minimal prime ideals of J_G (Propositions 3.8 and 3.9)

This file characterizes the containment order of `{P_S(G)}` and identifies
which `P_S(G)` are minimal primes of `J_G`.

## Main results

- **Proposition 3.8**: `P_T(G) ⊆ P_S(G)` iff T ⊆ S and components of G[V\T]
  refine into components of G[V\S].
- **Corollary 3.9**: `P_S(G)` is minimal iff S = ∅ or every vertex of S is a
  cut-vertex in the appropriate induced subgraph.

## Reference: Herzog et al. (2010), Proposition 3.8, Corollary 3.9
-/

noncomputable section

open MvPolynomial SimpleGraph

/-! ## Cut vertices -/

/--
A vertex `i ∈ S` is a **cut-vertex relative to S** if
  `c(S \ {i}) < c(S)`
i.e., removing `i` from S strictly decreases the component count.
Equivalently, `i` separates some component of G[V \ (S \ {i})].

Reference: Herzog et al. (2010), Corollary 3.9.
-/
def IsCutVertexRelative (G : SimpleGraph V) (S : Finset V) (i : V) : Prop :=
  i ∈ S ∧ componentCount G (S.erase i) < componentCount G S

private def evalInlWitness (i : V) : BinomialEdgeVars V → K :=
  fun v => if v = Sum.inl i then 1 else 0

private def evalPairWitness (u v : V) : BinomialEdgeVars V → K :=
  fun w => if w = Sum.inl u then 1 else if w = Sum.inr v then 1 else 0

omit [Fintype V] in
private lemma primeComponent_le_ker_evalInlWitness
    (G : SimpleGraph V) (S : Finset V) (i : V) (hi : i ∉ S) :
    primeComponent (K := K) G S ≤ RingHom.ker (MvPolynomial.eval (evalInlWitness (K := K) i)) := by
  apply Ideal.span_le.mpr
  intro f hf
  simp only [SetLike.mem_coe, RingHom.mem_ker]
  simp only [Set.mem_union, Set.mem_setOf_eq] at hf
  rcases hf with ⟨s, hsS, rfl | rfl⟩ | ⟨j, k, _, _, rfl⟩
  · simp only [MvPolynomial.eval_X, evalInlWitness]
    apply if_neg
    intro heq
    have hsi : s = i := by
      change (Sum.inl s : V ⊕ V) = Sum.inl i at heq
      exact Sum.inl.inj heq
    exact hi (hsi ▸ hsS)
  · simp [evalInlWitness]
  · simp [x, y, evalInlWitness]

omit [Fintype V] in
private lemma primeComponent_le_ker_evalPairWitness
    (G : SimpleGraph V) (S : Finset V) (u v : V) (huS : u ∉ S) (hvS : v ∉ S)
    (hnotpath : ¬Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) u v) :
    primeComponent (K := K) G S ≤
      RingHom.ker (MvPolynomial.eval (evalPairWitness (K := K) u v)) := by
  have hR_sym_S : Symmetric (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) :=
    fun a b ⟨ha, hb, hc⟩ => ⟨G.symm ha, hc, hb⟩
  apply Ideal.span_le.mpr
  intro f hf
  simp only [SetLike.mem_coe, RingHom.mem_ker, Set.mem_union, Set.mem_setOf_eq] at hf ⊢
  rcases hf with ⟨s, hsS, rfl | rfl⟩ | ⟨j, k, hjk, hjkS, rfl⟩
  · simp only [MvPolynomial.eval_X, evalPairWitness,
      if_neg (show (Sum.inl s : BinomialEdgeVars V) ≠ Sum.inl u from
        fun h => huS (Sum.inl.inj h ▸ hsS)),
      if_neg (show (Sum.inl s : BinomialEdgeVars V) ≠ Sum.inr v from by simp)]
  · simp only [MvPolynomial.eval_X, evalPairWitness,
      if_neg (show (Sum.inr s : BinomialEdgeVars V) ≠ Sum.inl u from by simp),
      if_neg (show (Sum.inr s : BinomialEdgeVars V) ≠ Sum.inr v from
        fun h => hvS (Sum.inr.inj h ▸ hsS))]
  · simp only [x, y, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      evalPairWitness,
      if_neg (show (Sum.inl j : BinomialEdgeVars V) ≠ Sum.inr v from by simp),
      if_neg (show (Sum.inr k : BinomialEdgeVars V) ≠ Sum.inl u from by simp),
      if_neg (show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inr v from by simp),
      if_neg (show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inl u from by simp)]
    rcases eq_or_ne j u with hjU | hjU
    · have hkU : k ≠ u := ne_of_gt (hjU ▸ hjk)
      simp only [if_pos (congrArg Sum.inl hjU), one_mul,
        if_neg (show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl u from
          fun h => hkU (Sum.inl.inj h)), zero_mul, sub_zero]
      rcases eq_or_ne k v with hkV | hkV
      · rw [hjU, hkV] at hjkS
        exact absurd hjkS.2.2 hnotpath
      · simp [show (Sum.inr k : BinomialEdgeVars V) ≠ Sum.inr v from
          fun h => hkV (Sum.inr.inj h)]
    · simp only [if_neg (show (Sum.inl j : BinomialEdgeVars V) ≠ Sum.inl u from
        fun h => hjU (Sum.inl.inj h)), zero_mul, zero_sub, neg_eq_zero]
      rcases eq_or_ne k u with hkU | hkU
      · simp only [if_pos (congrArg Sum.inl hkU), one_mul]
        rcases eq_or_ne j v with hjV | hjV
        · rw [hkU, hjV] at hjkS
          exact absurd (Relation.ReflTransGen.symmetric hR_sym_S hjkS.2.2) hnotpath
        · simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr v from
            fun h => hjV (Sum.inr.inj h)]
      · simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl u from
          fun h => hkU (Sum.inl.inj h)]

omit [LinearOrder V] [Fintype V] in
private lemma evalPairWitness_cross_eq_one (u v : V) (huv : u ≠ v) :
    MvPolynomial.eval (evalPairWitness (K := K) u v) (x u * y v - x v * y u) = 1 := by
  simp only [x, y, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X]
  have h1 : evalPairWitness (K := K) u v (Sum.inl u) = 1 := by
    simp [evalPairWitness]
  have h2 : evalPairWitness (K := K) u v (Sum.inr v) = 1 := by
    simp [evalPairWitness, show (Sum.inr v : BinomialEdgeVars V) ≠ Sum.inl u from by simp]
  have h3 : evalPairWitness (K := K) u v (Sum.inl v) = 0 := by
    simp [evalPairWitness, show (Sum.inl v : BinomialEdgeVars V) ≠ Sum.inl u from
      fun h => huv (Sum.inl.inj h).symm, show (Sum.inl v : BinomialEdgeVars V) ≠ Sum.inr v from
      by simp]
  have h4 : evalPairWitness (K := K) u v (Sum.inr u) = 0 := by
    simp [evalPairWitness, show (Sum.inr u : BinomialEdgeVars V) ≠ Sum.inl u from by simp,
      show (Sum.inr u : BinomialEdgeVars V) ≠ Sum.inr v from fun h => huv (Sum.inr.inj h)]
  simp [h1, h2, h3, h4]

/-! ## Key sub-lemma: variables outside S are not in P_S -/

omit [DecidableEq V] [Fintype V] in
/-- If `i ∉ S`, then `X(Sum.inl i) ∉ primeComponent G S`.
Proved by evaluating at the point `x_i = 1`, everything else `= 0`. -/
lemma prop_3_8_var_not_mem (G : SimpleGraph V) (S : Finset V) (i : V) (hi : i ∉ S) :
    X (Sum.inl i) ∉ primeComponent (K := K) G S := by
  intro hmem
  have h0 : MvPolynomial.eval (evalInlWitness (K := K) i)
      (X (Sum.inl i) : MvPolynomial (BinomialEdgeVars V) K) = 0 :=
    RingHom.mem_ker.mp (primeComponent_le_ker_evalInlWitness (K := K) G S i hi hmem)
  simp [evalInlWitness] at h0

/-! ## Proposition 3.8: Containment of prime ideals -/

omit [DecidableEq V] [Fintype V] in
/-- Component preservation sub-lemma for `prop_3_8` (→ direction):
If `P_T ≤ P_S` and `u, v ∉ T ∪ S` are in the same component of `G[V\T]`,
then they are in the same component of `G[V\S]`.

**Proof** (by contradiction, evaluation map argument):
Define `σ : BinomialEdgeVars V → K` by `σ(x_u) = 1`, `σ(y_v) = 1`, everything else `= 0`.
- Every generator of `P_S` evaluates to 0 under `σ`:
  - `X(inl s)` for `s ∈ S`: `s ≠ u` since `u ∉ S`, so `σ(Sum.inl s) = 0`.
  - `X(inr s)` for `s ∈ S`: `s ≠ v` since `v ∉ S`, so `σ(Sum.inr s) = 0`.
  - `x_j y_k - x_k y_j` with `SameComponent G S j k`:
    the evaluation is nonzero only if `(j=u, k=v)` or `(k=u, j=v)`.
    Both cases require `SameComponent G S u v`, contradicting the assumption.
- But `x_u y_v - x_v y_u ∈ P_T ≤ P_S` (it is a generator of `P_T`, or negated generator
  if `u > v`), and `σ(x_u y_v - x_v y_u) = 1 ≠ 0`. Contradiction. -/
private lemma prop_3_8_sameComponent_preserved
    (G : SimpleGraph V) (S T : Finset V)
    (hle : primeComponent (K := K) G T ≤ primeComponent (K := K) G S)
    (u v : V) (huT : u ∉ T) (hvT : v ∉ T) (huS : u ∉ S) (hvS : v ∉ S)
    (hsc : SameComponent G T u v) : SameComponent G S u v := by
  by_contra hnotSC
  have hnotpath : ¬Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) u v :=
    fun hpath => hnotSC ⟨huS, hvS, hpath⟩
  have huv : u ≠ v := fun heq => hnotpath (heq ▸ Relation.ReflTransGen.refl)
  -- Symmetry helpers
  have hR_sym_T : Symmetric (fun a b => G.Adj a b ∧ a ∉ T ∧ b ∉ T) :=
    fun a b ⟨ha, hb, hc⟩ => ⟨G.symm ha, hc, hb⟩
  -- x_u * y_v - x_v * y_u ∈ P_T
  have hmem_T : x u * y v - x v * y u ∈ primeComponent (K := K) G T := by
    rcases lt_or_gt_of_ne huv with hlt | hlt
    · exact Ideal.subset_span (Set.mem_union_right _ ⟨u, v, hlt, hsc, rfl⟩)
    · have hscvu : SameComponent G T v u :=
        ⟨hvT, huT, Relation.ReflTransGen.symmetric hR_sym_T hsc.2.2⟩
      have hgen : x v * y u - x u * y v ∈ primeComponent (K := K) G T :=
        Ideal.subset_span (Set.mem_union_right _ ⟨v, u, hlt, hscvu, rfl⟩)
      have hneg := (primeComponent (K := K) G T).neg_mem hgen
      rwa [neg_sub] at hneg
  have hmem_S := hle hmem_T
  have hker := primeComponent_le_ker_evalPairWitness (K := K) G S u v huS hvS hnotpath
  have heval := evalPairWitness_cross_eq_one (K := K) u v huv
  exact one_ne_zero (heval.symm.trans (RingHom.mem_ker.mp (hker hmem_S)))

omit [DecidableEq V] [Fintype V] in
/--
**Proposition 3.8** (Herzog et al. 2010):
`P_T(G) ⊆ P_S(G)` if and only if:
- `T ⊆ S`, and
- every connected component of `G[V \ T]` whose vertices intersect `V \ S`
  is contained (on `V \ S`) in a single component of `G[V \ S]`.

**Fidelity: Equivalent.** The paper's condition is stated in terms of vertex sets of
connected components; the Lean version uses `SameComponent G T u v → SameComponent G S u v`
for vertices outside S, which is the same.

Reference: Herzog et al. (2010), Proposition 3.8.
-/
theorem prop_3_8 (G : SimpleGraph V) (S T : Finset V) :
    primeComponent (K := K) G T ≤ primeComponent (K := K) G S ↔
    T ≤ S ∧
    ∀ (u v : V), u ∉ T → v ∉ T → u ∉ S → v ∉ S →
      SameComponent G T u v → SameComponent G S u v := by
  constructor
  · -- (→): P_T ≤ P_S implies T ≤ S and components of G[V\T] refine into G[V\S].
    intro h
    exact ⟨fun a haT => by
      -- T ≤ S: if a ∈ T then a ∈ S. If a ∉ S, prop_3_8_var_not_mem gives X(inl a) ∉ P_S,
      -- but X(inl a) ∈ P_T ≤ P_S — contradiction.
      by_contra haS
      exact prop_3_8_var_not_mem G S a haS
        (h (Ideal.subset_span (Set.mem_union_left _ ⟨a, haT, Or.inl rfl⟩))),
      fun u v huT hvT huS hvS hsc =>
        prop_3_8_sameComponent_preserved G S T h u v huT hvT huS hvS hsc⟩
  · -- (←): T ≤ S and component-preservation implies P_T ≤ P_S.
    -- Every generator of P_T is in P_S by 3 cases on membership in S.
    intro ⟨hTS, hComp⟩
    apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_union, Set.mem_setOf_eq] at hf
    rcases hf with ⟨i, hiT, hf_eq⟩ | ⟨j, k, hjk, hscT, rfl⟩
    · -- Generator of P_T type 1: f = X(inl i) or X(inr i) with i ∈ T ⊆ S
      rcases hf_eq with rfl | rfl
      · exact Ideal.subset_span (Set.mem_union_left _ ⟨i, hTS hiT, Or.inl rfl⟩)
      · exact Ideal.subset_span (Set.mem_union_left _ ⟨i, hTS hiT, Or.inr rfl⟩)
    · -- Generator of P_T type 2: f = x_j * y_k - x_k * y_j with SameComponent G T j k
      have hjT := hscT.1
      have hkT := hscT.2.1
      by_cases hjS : j ∈ S
      · -- j ∈ S: X(inl j) and X(inr j) are in P_S; use them
        have hxj : X (Sum.inl j) ∈ primeComponent (K := K) G S :=
          Ideal.subset_span (Set.mem_union_left _ ⟨j, hjS, Or.inl rfl⟩)
        have hyj : X (Sum.inr j) ∈ primeComponent (K := K) G S :=
          Ideal.subset_span (Set.mem_union_left _ ⟨j, hjS, Or.inr rfl⟩)
        apply (primeComponent (K := K) G S).sub_mem
        · exact Ideal.mul_mem_right _ _ hxj
        · exact (primeComponent (K := K) G S).mul_mem_left _ hyj
      · by_cases hkS : k ∈ S
        · -- k ∈ S: X(inl k) and X(inr k) are in P_S; use them
          have hxk : X (Sum.inl k) ∈ primeComponent (K := K) G S :=
            Ideal.subset_span (Set.mem_union_left _ ⟨k, hkS, Or.inl rfl⟩)
          have hyk : X (Sum.inr k) ∈ primeComponent (K := K) G S :=
            Ideal.subset_span (Set.mem_union_left _ ⟨k, hkS, Or.inr rfl⟩)
          apply (primeComponent (K := K) G S).sub_mem
          · exact (primeComponent (K := K) G S).mul_mem_left _ hyk
          · exact Ideal.mul_mem_right _ _ hxk
        · -- j ∉ S, k ∉ S: use component-preservation to get SameComponent G S j k
          apply Ideal.subset_span
          exact Set.mem_union_right _ ⟨j, k, hjk,
            hComp j k hjT hkT hjS hkS hscT, rfl⟩

/-! ## Corollary 3.9: Minimal prime characterization -/

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Helper: a walk in the induced subgraph gives a `ReflTransGen` path. -/
lemma induced_walk_to_reflTransGen {G : SimpleGraph V} {S : Finset V}
    (u v : {w : V | w ∉ S}) (walk : (G.induce {w : V | w ∉ S}).Walk u v) :
    Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) u.val v.val := by
  induction walk with
  | nil => exact Relation.ReflTransGen.refl
  | @cons p q r hadj _ ih =>
    exact Relation.ReflTransGen.head ⟨SimpleGraph.induce_adj.mp hadj, p.2, q.2⟩ ih

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Monotonicity of `SameComponent`: if `T ⊆ S`, then any path avoiding `S` also avoids `T`,
so `SameComponent G S u v → SameComponent G T u v`. -/
lemma SameComponent_mono (G : SimpleGraph V) {S T : Finset V} (hTS : T ≤ S)
    {u v : V} (hsc : SameComponent G S u v) : SameComponent G T u v := by
  refine ⟨fun huT => hsc.1 (hTS huT), fun hvT => hsc.2.1 (hTS hvT), ?_⟩
  exact Relation.ReflTransGen.lift id
    (fun a b ⟨hadj, haS, hbS⟩ => ⟨hadj, fun haT => haS (hTS haT), fun hbT => hbS (hTS hbT)⟩)
    hsc.2.2

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- Convert `SameComponent G S u v` to `Reachable` in the induced subgraph `G[V \ S]`. -/
lemma sameComponent_to_reachable (G : SimpleGraph V) (S : Finset V)
    (u v : V) (huS : u ∉ S) (hvS : v ∉ S) (hsc : SameComponent G S u v) :
    (G.induce {w : V | w ∉ S}).Reachable ⟨u, huS⟩ ⟨v, hvS⟩ := by
  obtain ⟨_, _, hpath⟩ := hsc
  -- Generalize the target vertex to handle intermediate vertices in the induction
  suffices ∀ (w : V),
      Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) u w →
      ∀ (hwS : w ∉ S), (G.induce {w : V | w ∉ S}).Reachable ⟨u, huS⟩ ⟨w, hwS⟩ from
    this v hpath hvS
  intro w hrtg
  induction hrtg with
  | refl => intro _; exact ⟨SimpleGraph.Walk.nil⟩
  | @tail b c _ hbc ih =>
    intro hcS
    obtain ⟨walk_ub⟩ := ih hbc.2.1
    let b' : {w : V | w ∉ S} := ⟨b, hbc.2.1⟩
    let c' : {w : V | w ∉ S} := ⟨c, hcS⟩
    have hadj : (G.induce {w : V | w ∉ S}).Adj b' c' :=
      SimpleGraph.induce_adj.mpr hbc.1
    exact ⟨walk_ub.append (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)⟩

/-- If `i` is a cut-vertex relative to `S`, then two components of `G[V \ S]` merge when `i` is
removed from `S`. Formally: there exist `a, b ∉ S` connected in `G[V \ (S \ {i})]` but not in
`G[V \ S]`. -/
lemma exists_merged_of_cutVertex (G : SimpleGraph V) (S : Finset V) (i : V)
    (hcut : IsCutVertexRelative G S i) :
    ∃ a b : V, a ∉ S ∧ b ∉ S ∧
      SameComponent G (S.erase i) a b ∧ ¬SameComponent G S a b := by
  classical
  unfold IsCutVertexRelative componentCount at hcut
  obtain ⟨_, hlt⟩ := hcut
  haveI : Fintype (G.induce {v : V | v ∉ S.erase i}).ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype (G.induce {v : V | v ∉ S}).ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hlt
  -- The inclusion V \ S ⊆ V \ (S \ {i}) induces a map on connected components
  have hincl : ({w : V | w ∉ S} : Set V) ⊆ {w : V | w ∉ S.erase i} :=
    fun w hw h => hw (Finset.erase_subset i S h)
  let ι := SimpleGraph.induceHomOfLE G hincl
  let f := SimpleGraph.ConnectedComponent.map ι.toHom
  -- By pigeonhole (more components in domain than codomain), f is not injective
  obtain ⟨c1, c2, hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hlt
  -- Extract representatives from the connected components
  revert hne hfeq
  induction c1 using SimpleGraph.ConnectedComponent.ind with | h a =>
  induction c2 using SimpleGraph.ConnectedComponent.ind with | h b =>
  intro hne hfeq
  refine ⟨a.val, b.val, a.prop, b.prop, ?_, ?_⟩
  · -- SameComponent G (S.erase i) a b: f maps them to the same component
    refine ⟨fun h => a.prop (Finset.erase_subset i S h),
            fun h => b.prop (Finset.erase_subset i S h), ?_⟩
    -- f(c1) = f(c2) means a and b are in the same component of G[V \ (S \ {i})]
    have hreach : (G.induce {w : V | w ∉ S.erase i}).Reachable (ι.toHom a) (ι.toHom b) := by
      rw [← SimpleGraph.ConnectedComponent.eq]
      exact hfeq
    obtain ⟨walk⟩ := hreach
    exact induced_walk_to_reflTransGen
      (⟨a.val, fun h => a.prop (Finset.erase_subset i S h)⟩)
      (⟨b.val, fun h => b.prop (Finset.erase_subset i S h)⟩) walk
  · -- ¬SameComponent G S a b: they are in different components of G[V \ S]
    intro hsc
    apply hne
    rw [SimpleGraph.ConnectedComponent.eq]
    exact sameComponent_to_reachable G S a.val b.val a.prop b.prop hsc

/-- Helper: if `a → i → c` with `a, c ∉ S` and `i` is not a cut vertex relative to `S`,
then `a` and `c` are connected in `G[V ∖ S]`. Proved by showing the component-count map
`G[V∖S].CC → G[V∖(S∖{i})].CC` is surjective but not injective, contradicting the
non-cut-vertex hypothesis. -/
private lemma bypass_adj {G : SimpleGraph V} {S : Finset V} {i a c : V}
    (haS : a ∉ S) (hcS : c ∉ S) (hai : G.Adj a i) (hic : G.Adj i c)
    (hnotlt : ¬(componentCount G (S.erase i) < componentCount G S)) :
    Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) a c := by
  classical
  by_contra hnotpath; apply hnotlt
  unfold componentCount
  haveI : Fintype (G.induce {v : V | v ∉ S.erase i}).ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype (G.induce {v : V | v ∉ S}).ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hincl : ({w : V | w ∉ S} : Set V) ⊆ {w : V | w ∉ S.erase i} :=
    fun w hw h => hw (Finset.erase_subset i S h)
  let ι := SimpleGraph.induceHomOfLE G hincl
  let iSe : {w : V | w ∉ S.erase i} := ⟨i, Finset.notMem_erase i S⟩
  let f := SimpleGraph.ConnectedComponent.map ι.toHom
  apply Fintype.card_lt_of_surjective_not_injective f
  · intro cc
    induction cc using SimpleGraph.ConnectedComponent.ind with | h v =>
    by_cases hvi : v.val = i
    · refine ⟨(G.induce {w | w ∉ S}).connectedComponentMk ⟨a, haS⟩, ?_⟩
      simp only [f, SimpleGraph.ConnectedComponent.map_mk]
      rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.Reachable,
          show v = iSe from Subtype.ext hvi]
      exact ⟨SimpleGraph.Walk.cons (v := iSe) (by rw [SimpleGraph.induce_adj]; exact hai)
             SimpleGraph.Walk.nil⟩
    · have hvS : v.val ∉ S := fun h => v.2 (Finset.mem_erase.mpr ⟨hvi, h⟩)
      refine ⟨(G.induce {w | w ∉ S}).connectedComponentMk ⟨v.val, hvS⟩, ?_⟩
      have heq : ι.toHom ⟨v.val, hvS⟩ = v := Subtype.ext rfl
      rw [show f ((G.induce {w | w ∉ S}).connectedComponentMk ⟨v.val, hvS⟩) =
               (G.induce {w | w ∉ S.erase i}).connectedComponentMk (ι.toHom ⟨v.val, hvS⟩) from
           SimpleGraph.ConnectedComponent.map_mk ι.toHom ⟨v.val, hvS⟩, heq]
  · intro hinj; apply hnotpath
    have hCaCc : (G.induce {w | w ∉ S}).connectedComponentMk ⟨a, haS⟩ ≠
                 (G.induce {w | w ∉ S}).connectedComponentMk ⟨c, hcS⟩ := by
      rw [ne_eq, SimpleGraph.ConnectedComponent.eq, SimpleGraph.Reachable]
      rintro ⟨walk⟩
      exact hnotpath (induced_walk_to_reflTransGen ⟨a, haS⟩ ⟨c, hcS⟩ walk)
    exact absurd (hinj (by
      simp only [f, SimpleGraph.ConnectedComponent.map_mk]
      rw [SimpleGraph.ConnectedComponent.eq, SimpleGraph.Reachable]
      exact ⟨SimpleGraph.Walk.cons (v := iSe) (by rw [SimpleGraph.induce_adj]; exact hai)
              (SimpleGraph.Walk.cons (v := SimpleGraph.induceHomOfLE G hincl |>.toHom ⟨c, hcS⟩)
                (by rw [SimpleGraph.induce_adj]; exact hic) SimpleGraph.Walk.nil)⟩)) hCaCc

/-- Key component-preservation sub-lemma: if `i ∈ S` is **not** a cut-vertex relative to `S`
(i.e., removing `i` from `S` does not decrease the component count of `G[V ∖ S]`),
then any path in `G[V ∖ (S ∖ {i})]` between vertices of `V ∖ S` can be lifted to a path in
`G[V ∖ S]`.

**Proof**: Since `¬IsCutVertexRelative G S i`, `i` does not increase the component count
when removed from `S`. This means all neighbors of `i` in `V ∖ S` lie in the same component
of `G[V ∖ S]`. We induct on the path using a stronger motive tracking both the main path and
a "pending bypass" when the path passes through `i`. -/
private lemma sameComponent_of_notCutVertex
    (G : SimpleGraph V) (S : Finset V) (i : V)
    (hiS : i ∈ S) (hnotcut : ¬IsCutVertexRelative G S i)
    {u v : V} (huS : u ∉ S) (hvS : v ∉ S)
    (hsc : SameComponent G (S.erase i) u v) : SameComponent G S u v := by
  have hnotcut_lt : ¬(componentCount G (S.erase i) < componentCount G S) :=
    fun hlt => hnotcut ⟨hiS, hlt⟩
  obtain ⟨_, _, hpath⟩ := hsc
  refine ⟨huS, hvS, ?_⟩
  -- Induction motive: track both the path case and the "last step was into i" case
  let C : ∀ (a : V), Relation.ReflTransGen
      (fun x y => G.Adj x y ∧ x ∉ S.erase i ∧ y ∉ S.erase i) a v → Prop :=
    fun a _ => (a ∉ S → Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) a v) ∧
               (a = i → ∃ w ∉ S, G.Adj i w ∧
                Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) w v)
  have hmain : C u hpath := by
    apply Relation.ReflTransGen.head_induction_on (motive := C) hpath
    · -- Base case: at v; first part is refl, second is vacuous since v ≠ i
      exact ⟨fun _ => Relation.ReflTransGen.refl, fun hvi => absurd hiS (hvi ▸ hvS)⟩
    · intro a c hac _hcv IH
      constructor
      · intro haS
        rcases eq_or_ne c i with rfl | hci
        · -- c = i: bypass using IH's "pending" info + bypass_adj
          obtain ⟨w, hwS, hw_adj, hpath_w⟩ := IH.2 rfl
          exact Relation.ReflTransGen.trans
            (bypass_adj haS hwS hac.1 hw_adj hnotcut_lt) hpath_w
        · -- c ∉ S: direct step
          have hcS : c ∉ S := fun h => hac.2.2 (Finset.mem_erase.mpr ⟨hci, h⟩)
          exact Relation.ReflTransGen.head ⟨hac.1, haS, hcS⟩ (IH.1 hcS)
      · intro hai
        rcases eq_or_ne c i with rfl | hci
        · -- c = i: but a = i → G.Adj i i, impossible
          exact absurd (hai ▸ hac.1) (SimpleGraph.irrefl G)
        · -- c ∉ S: record c as the "next after i"
          have hcS : c ∉ S := fun h => hac.2.2 (Finset.mem_erase.mpr ⟨hci, h⟩)
          exact ⟨c, hcS, hai ▸ hac.1, IH.1 hcS⟩
  exact hmain.1 huS

/-- When `i ∈ S` is not a cut-vertex relative to `S`, the prime component `P_{S ∖ {i}}`
is contained in `P_S`. Used to show `P_S` is not minimal when a non-cut-vertex exists. -/
private lemma primeComponent_erase_le_of_notCutVertex
    (G : SimpleGraph V) (S : Finset V) (i : V)
    (hiS : i ∈ S) (hnotcut : ¬IsCutVertexRelative G S i) :
    primeComponent (K := K) G (S.erase i) ≤ primeComponent (K := K) G S := by
  rw [prop_3_8]
  refine ⟨Finset.erase_subset i S, fun u v _ _ huS hvS hsc =>
    sameComponent_of_notCutVertex G S i hiS hnotcut huS hvS hsc⟩

/--
**Corollary 3.9** (Herzog et al. 2010): Assuming G is connected,
`P_S(G)` is a minimal prime of `J_G` if and only if either:
- S = ∅ (then P_∅(G) is the "generic" prime), or
- every vertex in S is a cut-vertex relative to S.

**Proof of (→):** If some `i ∈ S` is not a cut-vertex relative to `S`, then
`P_{S ∖ {i}}` is a prime ideal with `J_G ≤ P_{S ∖ {i}} ≤ P_S` but
`P_S ≰ P_{S ∖ {i}}` (by `prop_3_8`, since `S ⊄ S ∖ {i}`). This contradicts minimality of `P_S`.

**Proof of (←):** If `S = ∅`, then the only `P_T ≤ P_∅` has `T = ∅` (by `prop_3_8`).
If all vertices of `S` are cut-vertices, suppose `P_T ≤ P_S` with `T ⊆ S`. For any `i ∈ S \ T`,
the cut-vertex condition provides `a, b ∉ S` connected in `G[V \ (S \ {i})]` but not in `G[V \ S]`.
Since `T ⊆ S \ {i}`, monotonicity gives connectivity in `G[V \ T]`, and the refinement from
`P_T ≤ P_S` lifts this to `G[V \ S]` -- contradiction. Hence `S ⊆ T`, so `T = S`,
and `P_S` is minimal among `{P_T}`. We conclude via `minimalPrimes_characterization`.

**Fidelity: Equivalent.** The paper states `c(S \ {i}) < c(S)` for each `i ∈ S`;
the Lean version uses `IsCutVertexRelative G S i`, which captures the same condition.

Reference: Herzog et al. (2010), Corollary 3.9.
-/
theorem corollary_3_9 (G : SimpleGraph V) (S : Finset V)
    (hConn : G.Connected) :
    primeComponent (K := K) G S ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes ↔
    S = ∅ ∨ ∀ i ∈ S, IsCutVertexRelative G S i := by
  simp only [Ideal.minimalPrimes, Set.mem_setOf_eq, Minimal]
  constructor
  · -- (→): P_S minimal → S = ∅ or every vertex of S is a cut-vertex relative to S.
    -- Contrapositive: if ∃ i ∈ S that is NOT a cut-vertex, exhibit P_{S\{i}} strictly below P_S.
    intro hmin
    by_contra h
    push_neg at h
    obtain ⟨hSne, i, hiS, hnotcut⟩ := h
    -- P_{S\{i}} is prime and contains J_G
    have hT_prime : (primeComponent (K := K) G (S.erase i)).IsPrime :=
      primeComponent_isPrime G (S.erase i)
    have hJT : binomialEdgeIdeal (K := K) G ≤ primeComponent (K := K) G (S.erase i) :=
      binomialEdgeIdeal_le_primeComponent G (S.erase i)
    -- P_{S\{i}} ≤ P_S (the main content: non-cut-vertex → component preservation)
    have hTS : primeComponent (K := K) G (S.erase i) ≤ primeComponent (K := K) G S :=
      primeComponent_erase_le_of_notCutVertex G S i hiS hnotcut
    -- By minimality of P_S: P_S ≤ P_{S\{i}}
    have hPS_le : primeComponent (K := K) G S ≤ primeComponent (K := K) G (S.erase i) :=
      hmin.2 ⟨hT_prime, hJT⟩ hTS
    -- But P_S ≰ P_{S\{i}} by prop_3_8 (since S ≰ S\{i}, as i ∈ S, i ∉ S\{i})
    have hnotPS_le : ¬(primeComponent (K := K) G S ≤ primeComponent (K := K) G (S.erase i)) := by
      intro hle
      rw [prop_3_8] at hle
      exact absurd (hle.1 hiS) (Finset.notMem_erase i S)
    exact hnotPS_le hPS_le
  · -- (←): S = ∅ or all vertices are cut-vertices → P_S minimal.
    intro h
    -- Reduce to membership in minimalPrimes, then use minimalPrimes_characterization
    suffices hmem : primeComponent (K := K) G S ∈
        (binomialEdgeIdeal (K := K) G).minimalPrimes by
      simp only [Ideal.minimalPrimes, Set.mem_setOf_eq, Minimal] at hmem
      exact hmem
    rw [minimalPrimes_characterization]
    refine ⟨S, rfl, fun T hTS => ?_⟩
    -- Need: P_T ≤ P_S → P_S ≤ P_T. By prop_3_8: T ⊆ S and refinement.
    obtain ⟨hTsubS, hComp_TS⟩ := (prop_3_8 G S T).mp hTS
    -- It suffices to show S ⊆ T (together with T ⊆ S gives S = T, so P_S = P_T).
    suffices hSsubT : S ≤ T by
      exact le_of_eq (le_antisymm hSsubT hTsubS ▸ rfl)
    -- Show S ⊆ T by contradiction: if ∃ i ∈ S \ T, derive contradiction from cut-vertex
    intro i hiS
    by_contra hiT
    -- i is a cut-vertex relative to S (by hypothesis)
    have hcut : IsCutVertexRelative G S i := by
      rcases h with rfl | hcut
      · simp at hiS
      · exact hcut i hiS
    -- Cut-vertex gives merged components: ∃ a, b ∉ S, same in G[V\(S\{i})] but not in G[V\S]
    obtain ⟨a, b, haS, hbS, hsc_erase, hnotsc_S⟩ :=
      exists_merged_of_cutVertex G S i hcut
    -- Since T ⊆ S and i ∉ T: T ⊆ S \ {i}
    have hT_sub_erase : T ≤ S.erase i :=
      fun x hxT => Finset.mem_erase.mpr ⟨fun hxi => hiT (hxi ▸ hxT), hTsubS hxT⟩
    -- Monotonicity: SameComponent G (S.erase i) a b → SameComponent G T a b
    have hsc_T : SameComponent G T a b :=
      SameComponent_mono G hT_sub_erase hsc_erase
    -- Refinement from P_T ≤ P_S: SameComponent G T a b → SameComponent G S a b
    have haT : a ∉ T := fun haT => haS (hTsubS haT)
    have hbT : b ∉ T := fun hbT => hbS (hTsubS hbT)
    have hsc_S : SameComponent G S a b := hComp_TS a b haT hbT haS hbS hsc_T
    exact hnotsc_S hsc_S

omit [DecidableEq V] in
/-- The set of minimal primes of J_G is finite. -/
theorem minimalPrimes_finite (G : SimpleGraph V) :
    Set.Finite (binomialEdgeIdeal (K := K) G).minimalPrimes :=
  -- MvPolynomial over a field in finitely many variables is Noetherian:
  -- Field K → Artinian → Noetherian; BinomialEdgeVars V = V ⊕ V is Finite when V is.
  Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (BinomialEdgeVars V) K) (binomialEdgeIdeal (K := K) G)

omit [LinearOrder V] [Fintype V] in
/--
`i` is a cut-vertex relative to S iff adding i to `S \ {i}` strictly increases c(S):
  `c(S) > c(S \ {i})`
-/
theorem cutVertex_iff_componentCount (G : SimpleGraph V) (S : Finset V) (i : V) :
    IsCutVertexRelative G S i ↔
    i ∈ S ∧ componentCount G (S.erase i) < componentCount G S := by
  rfl

end

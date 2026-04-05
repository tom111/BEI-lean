import BEI.PrimeIdeals
import BEI.PrimeDecomposition
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Combinatorics.SimpleGraph.Matching

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

/-! ## Key sub-lemma: variables outside S are not in P_S -/

/-- If `i ∉ S`, then `X(Sum.inl i) ∉ primeComponent G S`.
Proved by evaluating at the point `x_i = 1`, everything else `= 0`. -/
lemma prop_3_8_var_not_mem (G : SimpleGraph V) (S : Finset V) (i : V) (hi : i ∉ S) :
    X (Sum.inl i) ∉ primeComponent (K := K) G S := by
  -- Evaluate at σ: x_i ↦ 1, everything else ↦ 0
  let σ : BinomialEdgeVars V → K := fun v => if v = Sum.inl i then 1 else 0
  -- Every generator of primeComponent G S evaluates to 0 under σ
  have hker : primeComponent (K := K) G S ≤ RingHom.ker (MvPolynomial.eval σ) := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [SetLike.mem_coe, RingHom.mem_ker]
    simp only [Set.mem_union, Set.mem_setOf_eq] at hf
    rcases hf with ⟨s, hsS, rfl | rfl⟩ | ⟨j, k, _, _, rfl⟩
    · -- X(Sum.inl s): s ∈ S but i ∉ S, so s ≠ i
      simp only [MvPolynomial.eval_X, σ]
      apply if_neg
      intro heq
      have hsi : s = i := by
        change (Sum.inl s : V ⊕ V) = Sum.inl i at heq; exact Sum.inl.inj heq
      exact hi (hsi ▸ hsS)
    · -- X(Sum.inr s): different constructor from Sum.inl
      simp [σ]
    · -- x j * y k - x k * y j: y-variables all evaluate to 0
      simp [x, y, σ]
  -- Contradiction: if X(inl i) ∈ primeComponent G S, eval σ gives 1 = 0
  intro hmem
  have h0 : MvPolynomial.eval σ (X (Sum.inl i) : MvPolynomial (BinomialEdgeVars V) K) = 0 :=
    RingHom.mem_ker.mp (hker hmem)
  simp [σ] at h0

/-! ## Proposition 3.8: Containment of prime ideals -/

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
  have hR_sym_S : Symmetric (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) :=
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
  -- Evaluation map: x_u ↦ 1, y_v ↦ 1, everything else ↦ 0
  let σ : BinomialEdgeVars V → K :=
    fun w => if w = Sum.inl u then 1 else if w = Sum.inr v then 1 else 0
  -- Every generator of P_S evaluates to 0 under σ
  have hker : primeComponent (K := K) G S ≤ RingHom.ker (MvPolynomial.eval σ) := by
    apply Ideal.span_le.mpr
    intro f hf
    simp only [SetLike.mem_coe, RingHom.mem_ker, Set.mem_union, Set.mem_setOf_eq] at hf ⊢
    rcases hf with ⟨s, hsS, rfl | rfl⟩ | ⟨j, k, hjk, hjkS, rfl⟩
    · -- X(inl s): s ≠ u since s ∈ S but u ∉ S
      simp only [MvPolynomial.eval_X, σ,
        if_neg (show (Sum.inl s : BinomialEdgeVars V) ≠ Sum.inl u from
          fun h => huS (Sum.inl.inj h ▸ hsS)),
        if_neg (show (Sum.inl s : BinomialEdgeVars V) ≠ Sum.inr v from by simp)]
    · -- X(inr s): s ≠ v since s ∈ S but v ∉ S
      simp only [MvPolynomial.eval_X, σ,
        if_neg (show (Sum.inr s : BinomialEdgeVars V) ≠ Sum.inl u from by simp),
        if_neg (show (Sum.inr s : BinomialEdgeVars V) ≠ Sum.inr v from
          fun h => hvS (Sum.inr.inj h ▸ hsS))]
    · -- x_j * y_k - x_k * y_j: eval = 0 (SameComponent G S j k cannot give path u→v)
      simp only [x, y, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X, σ,
        if_neg (show (Sum.inl j : BinomialEdgeVars V) ≠ Sum.inr v from by simp),
        if_neg (show (Sum.inr k : BinomialEdgeVars V) ≠ Sum.inl u from by simp),
        if_neg (show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inr v from by simp),
        if_neg (show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inl u from by simp)]
      -- Goal: (if Sum.inl j = Sum.inl u then 1 else 0) * (if Sum.inr k = Sum.inr v then 1 else 0)
      --     - (if Sum.inl k = Sum.inl u then 1 else 0) * (if Sum.inr j = Sum.inr v then 1 else 0) = 0
      rcases eq_or_ne j u with hjU | hjU
      · -- j = u: k ≠ u (since j < k), so second product = 0
        have hkU : k ≠ u := ne_of_gt (hjU ▸ hjk)
        simp only [if_pos (congrArg Sum.inl hjU), one_mul,
                   if_neg (show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl u from
                     fun h => hkU (Sum.inl.inj h)), zero_mul, sub_zero]
        -- Goal: (if Sum.inr k = Sum.inr v then 1 else 0) = 0
        rcases eq_or_ne k v with hkV | hkV
        · rw [hjU, hkV] at hjkS; exact absurd hjkS.2.2 hnotpath
        · simp [show (Sum.inr k : BinomialEdgeVars V) ≠ Sum.inr v from
            fun h => hkV (Sum.inr.inj h)]
      · -- j ≠ u: first product = 0
        simp only [if_neg (show (Sum.inl j : BinomialEdgeVars V) ≠ Sum.inl u from
                     fun h => hjU (Sum.inl.inj h)),
                   zero_mul, zero_sub, neg_eq_zero]
        -- Goal: (if Sum.inl k = Sum.inl u then 1 else 0) * (if Sum.inr j = Sum.inr v then 1 else 0) = 0
        rcases eq_or_ne k u with hkU | hkU
        · simp only [if_pos (congrArg Sum.inl hkU), one_mul]
          -- Goal: (if Sum.inr j = Sum.inr v then 1 else 0) = 0
          rcases eq_or_ne j v with hjV | hjV
          · rw [hkU, hjV] at hjkS
            exact absurd (Relation.ReflTransGen.symmetric hR_sym_S hjkS.2.2) hnotpath
          · simp [show (Sum.inr j : BinomialEdgeVars V) ≠ Sum.inr v from
              fun h => hjV (Sum.inr.inj h)]
        · simp [show (Sum.inl k : BinomialEdgeVars V) ≠ Sum.inl u from
            fun h => hkU (Sum.inl.inj h)]
  -- Contradiction: eval σ (x_u * y_v - x_v * y_u) = 1, but it's in the kernel (= 0)
  have heval : MvPolynomial.eval σ (x u * y v - x v * y u) = 1 := by
    simp only [x, y, MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    have h1 : σ (Sum.inl u) = 1 := by simp [σ]
    have h2 : σ (Sum.inr v) = 1 := by
      simp [σ, show (Sum.inr v : BinomialEdgeVars V) ≠ Sum.inl u from by simp]
    have h3 : σ (Sum.inl v) = 0 := by
      simp [σ, show (Sum.inl v : BinomialEdgeVars V) ≠ Sum.inl u from
              fun h => huv (Sum.inl.inj h).symm,
            show (Sum.inl v : BinomialEdgeVars V) ≠ Sum.inr v from by simp]
    have h4 : σ (Sum.inr u) = 0 := by
      simp [σ, show (Sum.inr u : BinomialEdgeVars V) ≠ Sum.inl u from by simp,
            show (Sum.inr u : BinomialEdgeVars V) ≠ Sum.inr v from
              fun h => huv (Sum.inr.inj h)]
    simp [h1, h2, h3, h4]
  exact one_ne_zero (heval.symm.trans (RingHom.mem_ker.mp (hker hmem_S)))

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

/-- Helper: a walk in the induced subgraph gives a `ReflTransGen` path. -/
private lemma induced_walk_to_reflTransGen {G : SimpleGraph V} {S : Finset V}
    (u v : {w : V | w ∉ S}) (walk : (G.induce {w : V | w ∉ S}).Walk u v) :
    Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) u.val v.val := by
  induction walk with
  | nil => exact Relation.ReflTransGen.refl
  | @cons p q r hadj _ ih =>
    exact Relation.ReflTransGen.head ⟨SimpleGraph.induce_adj.mp hadj, p.2, q.2⟩ ih

/-- Monotonicity of `SameComponent`: if `T ⊆ S`, then any path avoiding `S` also avoids `T`,
so `SameComponent G S u v → SameComponent G T u v`. -/
private lemma SameComponent_mono (G : SimpleGraph V) {S T : Finset V} (hTS : T ≤ S)
    {u v : V} (hsc : SameComponent G S u v) : SameComponent G T u v := by
  refine ⟨fun huT => hsc.1 (hTS huT), fun hvT => hsc.2.1 (hTS hvT), ?_⟩
  exact Relation.ReflTransGen.lift id
    (fun a b ⟨hadj, haS, hbS⟩ => ⟨hadj, fun haT => haS (hTS haT), fun hbT => hbS (hTS hbT)⟩)
    hsc.2.2

/-- Convert `SameComponent G S u v` to `Reachable` in the induced subgraph `G[V \ S]`. -/
private lemma sameComponent_to_reachable (G : SimpleGraph V) (S : Finset V)
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
private lemma exists_merged_of_cutVertex (G : SimpleGraph V) (S : Finset V) (i : V)
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

/-- The set of minimal primes of J_G is finite. -/
theorem minimalPrimes_finite (G : SimpleGraph V) :
    Set.Finite (binomialEdgeIdeal (K := K) G).minimalPrimes :=
  -- MvPolynomial over a field in finitely many variables is Noetherian:
  -- Field K → Artinian → Noetherian; BinomialEdgeVars V = V ⊕ V is Finite when V is.
  Ideal.finite_minimalPrimes_of_isNoetherianRing
    (MvPolynomial (BinomialEdgeVars V) K) (binomialEdgeIdeal (K := K) G)

/--
`i` is a cut-vertex relative to S iff adding i to `S \ {i}` strictly increases c(S):
  `c(S) > c(S \ {i})`
-/
theorem cutVertex_iff_componentCount (G : SimpleGraph V) (S : Finset V) (i : V) :
    IsCutVertexRelative G S i ↔
    i ∈ S ∧ componentCount G (S.erase i) < componentCount G S := by
  rfl

/-- Transfer a G-walk whose support lies in S to reachability in G.induce S. -/
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

/-! ## Corollary 3.7 unmixed branch -/

-- Cycle walk transfer through IsCycles API
set_option maxHeartbeats 800000 in
/-- In a cycle graph, the induced subgraph on `V \ {v}` is preconnected.
Uses the IsCycles API: obtain a Hamiltonian cycle walk at v, take its tail (a path visiting
every other vertex), then transfer initial segments into the induced subgraph. -/
private lemma cycle_induce_preconnected (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (_hn : 3 ≤ Fintype.card V) :
    (G.induce {x : V | x ∉ ({v} : Finset V)}).Preconnected := by
  classical
  obtain ⟨hConn, hDeg⟩ := hCyc
  obtain ⟨n1, _, _, hadj1, _, _⟩ := hDeg v
  have hn1v : n1 ≠ v := G.ne_of_adj hadj1.symm
  set S : Set V := {x : V | x ∉ ({v} : Finset V)} with hS_def
  set G' := G.induce S
  have hn1S : n1 ∈ S := by simp [S, hn1v]
  -- Bridge: IsCycleGraph → IsCycles
  have hcycles : G.IsCycles := by
    intro w hw; obtain ⟨u', w', huw, huv, hvw, honly'⟩ := hDeg w
    apply Set.ncard_eq_two.mpr; refine ⟨u', w', huw, ?_⟩
    ext z; simp only [SimpleGraph.neighborSet]
    exact ⟨fun hz => honly' z hz, fun hz => hz.elim (· ▸ huv) (· ▸ hvw)⟩
  -- Get cycle walk based at v visiting all vertices
  have hv_supp : v ∈ (G.connectedComponentMk v).supp := by
    simp [SimpleGraph.ConnectedComponent.supp]
  obtain ⟨c, hc_cycle, hc_verts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      hv_supp ⟨n1, hadj1⟩
  have htail_path := hc_cycle.isPath_tail
  have hc_snd_ne : c.snd ≠ v := (G.ne_of_adj (c.adj_snd hc_cycle.not_nil)).symm
  have hc_snd_S : c.snd ∈ S := by simp [S, hc_snd_ne]
  -- For any t ∈ S, build a walk from c.snd to t in G' via takeUntil on c.tail
  suffices hsuff : ∀ (t : V) (ht : t ∈ S), G'.Reachable ⟨c.snd, hc_snd_S⟩ ⟨t, ht⟩ by
    intro ⟨a, ha⟩ ⟨b, hb⟩; exact (hsuff a ha).symm.trans (hsuff b hb)
  intro t ht
  have ht_ne : t ≠ v := by intro h; simp [S, h] at ht
  have ht_supp : t ∈ c.support := by
    rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hc_verts]
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact hConn.preconnected t v
  have ht_tail : t ∈ c.tail.support := by
    rw [c.support_tail_of_not_nil hc_cycle.not_nil]
    have h_cons := (List.cons_head_tail c.support_ne_nil).symm
    rw [SimpleGraph.Walk.head_support c] at h_cons; rw [h_cons] at ht_supp
    exact (List.mem_cons.mp ht_supp).resolve_left ht_ne
  -- The walk from c.snd to t avoids v (endpoint avoidance on the path c.tail)
  let w := c.tail.takeUntil t ht_tail
  have hv_not : v ∉ w.support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil htail_path ht_tail (Ne.symm ht_ne)
  have hw_S : ∀ x ∈ w.support, x ∈ S := by
    intro x hx; simp only [S, Set.mem_setOf_eq, Finset.mem_singleton]
    exact fun h => hv_not (h ▸ hx)
  exact reachable_induce_of_walk G S w hw_S

/-- Removing a single vertex from a cycle graph gives a connected induced subgraph.
Therefore `componentCount G {v} = 1`. -/
theorem cycle_componentCount_singleton (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (v : V) (hn : 3 ≤ Fintype.card V) :
    componentCount G {v} = 1 := by
  classical
  unfold componentCount
  set G' := G.induce {x : V | x ∉ ({v} : Finset V)}
  obtain ⟨n1, _, _, _, _, _⟩ := hCyc.2 v
  have hn1v : n1 ≠ v := G.ne_of_adj (by assumption : G.Adj v n1).symm
  have hn1S : n1 ∈ ({x : V | x ∉ ({v} : Finset V)} : Set V) := by simp [hn1v]
  have hpc := cycle_induce_preconnected G hCyc v hn
  haveI := hpc.subsingleton_connectedComponent
  exact Nat.card_of_subsingleton (G'.connectedComponentMk ⟨n1, hn1S⟩)

/-- On a cycle with n ≥ 4 vertices, there exist two non-adjacent vertices. -/
theorem cycle_exists_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 4 ≤ Fintype.card V) :
    ∃ u w : V, u ≠ w ∧ ¬G.Adj u w := by
  have hDeg := hCyc.2
  -- Pick any vertex v
  obtain ⟨v⟩ := hCyc.1.nonempty
  obtain ⟨n1, n2, hn12, hadj1, hadj2, honly⟩ := hDeg v
  -- {v, n1, n2} has 3 elements; since |V| ≥ 4, there exists w ∉ {v, n1, n2}
  have h3 : ({v, n1, n2} : Finset V).card ≤ 3 := Finset.card_le_three
  have huniv : (Finset.univ : Finset V).card = Fintype.card V := Finset.card_univ
  have : ∃ w : V, w ∉ ({v, n1, n2} : Finset V) := by
    by_contra h; push_neg at h
    have : Finset.univ ⊆ {v, n1, n2} := fun x _ => h x
    linarith [Finset.card_le_card this]
  obtain ⟨w, hw⟩ := this
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
  -- w ≠ v and w is not adjacent to v (since v's only neighbors are n1 and n2)
  exact ⟨v, w, Ne.symm hw.1, fun hadj => (honly w hadj).elim hw.2.1 hw.2.2⟩

set_option maxHeartbeats 4000000 in
/-- Removing two non-adjacent vertices from a cycle gives exactly 2 components. -/
theorem cycle_componentCount_pair_nonadj (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (u w : V) (hne : u ≠ w) (hnadj : ¬G.Adj u w) (hn : 4 ≤ Fintype.card V) :
    componentCount G {u, w} = 2 := by
  classical
  obtain ⟨hConn, hDeg⟩ := hCyc
  set S : Set V := {x : V | x ∉ ({u, w} : Finset V)} with hS_def
  set G' := G.induce S
  unfold componentCount
  -- Bridge: IsCycleGraph → IsCycles
  have hcycles : G.IsCycles := by
    intro v _; obtain ⟨u', w', huw, huv, hvw, honly'⟩ := hDeg v
    apply Set.ncard_eq_two.mpr; refine ⟨u', w', huw, ?_⟩
    ext z; simp only [SimpleGraph.neighborSet]
    exact ⟨fun hz => honly' z hz, fun hz => hz.elim (· ▸ huv) (· ▸ hvw)⟩
  haveI : LocallyFinite G := fun _ => Fintype.ofFinite _
  -- Hamiltonian cycle walk at u
  obtain ⟨n1, n2, hn12, hadj1, hadj2, honly_u⟩ := hDeg u
  obtain ⟨c, hc_cycle, hc_verts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
      (show u ∈ (G.connectedComponentMk u).supp by
        simp [SimpleGraph.ConnectedComponent.supp]) ⟨n1, hadj1⟩
  -- Every vertex is on the cycle
  have hmem_cycle : ∀ v : V, v ∈ c.support := by
    intro v; rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hc_verts]
    simp only [SimpleGraph.ConnectedComponent.mem_supp_iff, SimpleGraph.ConnectedComponent.eq]
    exact hConn.preconnected v u
  -- Every G-edge is an edge of c (key: IsCycles + Hamiltonian)
  have hedge_of_adj : ∀ a b : V, G.Adj a b → s(a, b) ∈ c.edges := by
    intro a b hab
    rw [← SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges]
    exact (hc_cycle.adj_toSubgraph_iff_of_isCycles hcycles
      (c.mem_verts_toSubgraph.mpr (hmem_cycle a)) b).mpr hab
  -- c.tail is a path from c.snd to u
  have htail_path := hc_cycle.isPath_tail
  have hc_not_nil := hc_cycle.not_nil
  have hc_snd_adj : G.Adj u c.snd := c.adj_snd hc_not_nil
  have hc_snd_ne_u : c.snd ≠ u := (G.ne_of_adj hc_snd_adj).symm
  have hc_snd_ne_w : c.snd ≠ w := fun h => hnadj (h ▸ hc_snd_adj)
  have hc_snd_S : c.snd ∈ S := by
    simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hc_snd_ne_u, hc_snd_ne_w⟩
  -- Any vertex ≠ u is on c.tail
  have hmem_tail_of_ne_u : ∀ v : V, v ≠ u → v ∈ c.tail.support := by
    intro v hvu
    have hv_supp := hmem_cycle v
    rw [← c.cons_support_tail hc_not_nil] at hv_supp
    exact (List.mem_cons.mp hv_supp).resolve_left hvu
  have hw_tail : w ∈ c.tail.support := hmem_tail_of_ne_u w hne.symm
  -- Split c.tail at w: arc1 = c.snd → ... → w, arc2 = w → ... → u
  set arc1 := c.tail.takeUntil w hw_tail
  set arc2 := c.tail.dropUntil w hw_tail
  have harc1_path : arc1.IsPath := htail_path.takeUntil hw_tail
  have harc2_path : arc2.IsPath := htail_path.dropUntil hw_tail
  have htail_spec : arc1.append arc2 = c.tail := c.tail.take_spec hw_tail
  have hu_not_arc1 : u ∉ arc1.support :=
    SimpleGraph.Walk.endpoint_notMem_support_takeUntil htail_path hw_tail hne
  -- Edge decomposition
  have htail_edges : c.tail.edges = arc1.edges ++ arc2.edges := by
    rw [← htail_spec]; exact SimpleGraph.Walk.edges_append arc1 arc2
  -- Every G-edge between surviving vertices is on an arc
  have hedge_on_arc : ∀ a b : V, a ∈ S → b ∈ S → G.Adj a b →
      s(a, b) ∈ arc1.edges ∨ s(a, b) ∈ arc2.edges := by
    intro a b haS hbS hab
    have hab_c := hedge_of_adj a b hab
    rw [← c.cons_tail_eq hc_not_nil, SimpleGraph.Walk.edges_cons] at hab_c
    have ha_ne_u : a ≠ u := by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at haS
      exact haS.1
    rcases List.mem_cons.mp hab_c with h | h
    · exfalso
      have hb_ne_u : b ≠ u := by
        simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at hbS
        exact hbS.1
      have hu_mem : u ∈ (s(a, b) : Sym2 V) := h ▸ Sym2.mem_mk_left u c.snd
      rcases Sym2.mem_iff.mp hu_mem with rfl | rfl
      · exact ha_ne_u rfl
      · exact hb_ne_u rfl
    · exact List.mem_append.mp (htail_edges ▸ h)
  -- Arc2 has a surviving vertex: arc2.snd
  have harc2_not_nil : ¬arc2.Nil := fun h => hne.symm (SimpleGraph.Walk.Nil.eq h)
  have harc2_snd_adj : G.Adj w arc2.snd := arc2.adj_snd harc2_not_nil
  have harc2_snd_ne_u : arc2.snd ≠ u := fun h => hnadj (h ▸ harc2_snd_adj).symm
  have harc2_snd_ne_w : arc2.snd ≠ w := (G.ne_of_adj harc2_snd_adj).symm
  have harc2_snd_S : arc2.snd ∈ S := by
    simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨harc2_snd_ne_u, harc2_snd_ne_w⟩
  have harc2_snd_mem : arc2.snd ∈ arc2.support :=
    List.mem_of_mem_tail (arc2.snd_mem_tail_support harc2_not_nil)
  -- Every surviving vertex is on arc1.support or arc2.support
  have hmem_arc : ∀ v : V, v ∈ S → v ∈ arc1.support ∨ v ∈ arc2.support := by
    intro v hv
    have hv_ne_u : v ≠ u := by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      exact hv.1
    have hv_tail := hmem_tail_of_ne_u v hv_ne_u
    rw [← htail_spec, SimpleGraph.Walk.support_append] at hv_tail
    rcases List.mem_append.mp hv_tail with h | h
    · exact Or.inl h
    · exact Or.inr (List.tail_subset _ h)
  -- Arc1 connectivity: surviving arc1 vertices are G'-reachable from c.snd
  have harc1_reach : ∀ (t : V), t ∈ arc1.support → t ≠ w → (ht : t ∈ S) →
      G'.Reachable ⟨c.snd, hc_snd_S⟩ ⟨t, ht⟩ := by
    intro t ht htw htS
    have hw_not : w ∉ (arc1.takeUntil t ht).support :=
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil harc1_path ht htw.symm
    have hu_not : u ∉ (arc1.takeUntil t ht).support := fun hu =>
      hu_not_arc1 (SimpleGraph.Walk.support_takeUntil_subset arc1 ht hu)
    exact reachable_induce_of_walk G S (arc1.takeUntil t ht) fun x hx => by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun hxu => hu_not (hxu ▸ hx), fun hxw => hw_not (hxw ▸ hx)⟩
  -- Arc2 connectivity: surviving arc2 vertices are G'-reachable from arc2.snd
  have harc2_reach : ∀ (t : V), t ∈ arc2.support → t ≠ w → t ≠ u → (ht : t ∈ S) →
      G'.Reachable ⟨arc2.snd, harc2_snd_S⟩ ⟨t, ht⟩ := by
    intro t ht htw htu htS
    have harc2_tail_path : arc2.tail.IsPath := by
      rw [← SimpleGraph.Walk.cons_tail_eq arc2 harc2_not_nil] at harc2_path
      exact harc2_path.of_cons
    have ht_tail : t ∈ arc2.tail.support := by
      have := arc2.cons_support_tail harc2_not_nil
      rw [← this] at ht
      exact (List.mem_cons.mp ht).resolve_left htw
    have hw_not_tail : w ∉ arc2.tail.support := by
      intro hmem
      have := harc2_path.support_nodup
      rw [← arc2.cons_support_tail harc2_not_nil] at this
      exact (List.nodup_cons.mp this).1 hmem
    have hu_not : u ∉ (arc2.tail.takeUntil t ht_tail).support :=
      SimpleGraph.Walk.endpoint_notMem_support_takeUntil harc2_tail_path ht_tail htu.symm
    have hw_not : w ∉ (arc2.tail.takeUntil t ht_tail).support := fun hw =>
      hw_not_tail (SimpleGraph.Walk.support_takeUntil_subset arc2.tail ht_tail hw)
    exact reachable_induce_of_walk G S (arc2.tail.takeUntil t ht_tail) fun x hx => by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun hxu => hu_not (hxu ▸ hx), fun hxw => hw_not (hxw ▸ hx)⟩
  -- Arc disjointness: arc1.support ∩ arc2.support = {w}
  have harc_disjoint : ∀ v : V, v ∈ arc1.support → v ∈ arc2.support → v = w := by
    intro v hv1 hv2
    by_contra hvw
    have hnodup := htail_path.support_nodup
    rw [← htail_spec, SimpleGraph.Walk.support_append] at hnodup
    have hv_arc2_tail : v ∈ arc2.support.tail := by
      rw [← arc2.support_tail_of_not_nil harc2_not_nil]
      have := arc2.cons_support_tail harc2_not_nil
      rw [← this] at hv2
      exact (List.mem_cons.mp hv2).resolve_left hvw
    exact List.disjoint_of_nodup_append hnodup hv1 hv_arc2_tail
  -- Cross-edge classification
  have hno_cross_edge : ∀ (a b : V), a ∈ S → b ∈ S → G.Adj a b →
      (a ∈ arc1.support ∧ b ∈ arc1.support) ∨ (a ∈ arc2.support ∧ b ∈ arc2.support) := by
    intro a b haS hbS hab
    rcases hedge_on_arc a b haS hbS hab with h | h
    · exact Or.inl ⟨SimpleGraph.Walk.fst_mem_support_of_mem_edges arc1 h,
                     SimpleGraph.Walk.snd_mem_support_of_mem_edges arc1 h⟩
    · exact Or.inr ⟨SimpleGraph.Walk.fst_mem_support_of_mem_edges arc2 h,
                     SimpleGraph.Walk.snd_mem_support_of_mem_edges arc2 h⟩
  -- Key membership
  have hc_snd_arc1 : c.snd ∈ arc1.support := arc1.start_mem_support
  have hc_snd_not_arc2 : c.snd ∉ arc2.support :=
    fun h => hc_snd_ne_w (harc_disjoint c.snd hc_snd_arc1 h)
  have harc2_snd_not_arc1 : arc2.snd ∉ arc1.support :=
    fun h => harc2_snd_ne_w (harc_disjoint arc2.snd h harc2_snd_mem)
  -- Separation: c.snd and arc2.snd in different components
  have hsep : ¬G'.Reachable ⟨c.snd, hc_snd_S⟩ ⟨arc2.snd, harc2_snd_S⟩ := by
    intro ⟨p⟩
    suffices h : ∀ (a b : S) (q : G'.Walk a b),
        (a : V) ∈ arc1.support → (a : V) ∉ arc2.support → (b : V) ∈ arc1.support by
      exact harc2_snd_not_arc1 (h _ _ p hc_snd_arc1 hc_snd_not_arc2)
    intro a b q
    induction q with
    | nil => intro ha _; exact ha
    | @cons x y z hadj_xy rest ih =>
      intro hx_arc1 hx_not_arc2
      apply ih
      · rcases hno_cross_edge x y x.2 y.2 hadj_xy with ⟨_, hy1⟩ | ⟨hx2, _⟩
        · exact hy1
        · exact absurd hx2 hx_not_arc2
      · intro hy_arc2
        rcases hno_cross_edge x y x.2 y.2 hadj_xy with ⟨_, hy1⟩ | ⟨hx2, _⟩
        · have hyw := harc_disjoint y hy1 hy_arc2
          have hyS := y.2
          simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton,
            not_or] at hyS
          exact hyS.2 hyw
        · exact hx_not_arc2 hx2
  -- Assemble: Nat.card = 2
  set comp1 := G'.connectedComponentMk ⟨c.snd, hc_snd_S⟩
  set comp2 := G'.connectedComponentMk ⟨arc2.snd, harc2_snd_S⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨comp1, comp2, fun heq => hsep (SimpleGraph.ConnectedComponent.exact heq), ?_⟩
  ext comp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
  obtain ⟨⟨v, hv⟩, rfl⟩ := Quot.exists_rep comp
  rcases hmem_arc v hv with harc | harc
  · have hvw : v ≠ w := by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      exact hv.2
    exact Or.inl (SimpleGraph.ConnectedComponent.sound (harc1_reach v harc hvw hv).symm)
  · have hvw : v ≠ w := by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      exact hv.2
    have hvu : v ≠ u := by
      simp only [S, Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, not_or] at hv
      exact hv.1
    exact Or.inr (SimpleGraph.ConnectedComponent.sound (harc2_reach v harc hvw hvu hv).symm)
/--
**Corollary 3.7 (unmixed branch)**: For a cycle G with n ≥ 3 vertices,
  `J_G` is prime ↔ `J_G` is unmixed.

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
      right; intro i hi
      rw [cutVertex_iff_componentCount]
      refine ⟨hi, ?_⟩
      rw [cycle_componentCount_pair_nonadj G hCyc u w huw hnadj hn4]
      -- c({u,w}.erase i) = 1 since i ∈ {u,w} means {u,w}\{i} is a singleton
      -- and c(singleton) = 1 by cycle_componentCount_singleton
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      -- i ∈ {u, w} so either i = u or i = w
      rcases hi with rfl | rfl
      · -- i = u: {u,w}.erase u = {w}, componentCount G {w} = 1 < 2
        simp [huw]
        rw [cycle_componentCount_singleton G hCyc _ (by omega)]; omega
      · -- i = w: {u,w}.erase w = {u}, componentCount G {u} = 1 < 2
        have hne : i ∉ ({u} : Finset V) := by simp [show i ≠ u from Ne.symm huw]
        rw [show ({u, i} : Finset V) = insert i {u} from by rw [Finset.pair_comm]]
        rw [Finset.erase_insert hne]
        rw [cycle_componentCount_singleton G hCyc _ (by omega)]; omega
    have hc0 : componentCount G ∅ = 1 := by
      rw [componentCount_empty]
      haveI := hCyc.1.preconnected.subsingleton_connectedComponent
      have hne := hCyc.1.nonempty
      exact Nat.card_of_subsingleton (G.connectedComponentMk hne.some)
    have hP0_ht : Ideal.height (primeComponent (K := K) G ∅) =
        (Fintype.card V - 1 : ℕ) := by
      rw [lemma_3_1 (K := K)]; congr 1
      simp [hc0]
    have hcuw : componentCount G {u, w} = 2 :=
      cycle_componentCount_pair_nonadj G hCyc u w huw hnadj hn4
    have hPuw_ht : Ideal.height (primeComponent (K := K) G {u, w}) =
        (Fintype.card V : ℕ) := by
      rw [lemma_3_1 (K := K)]; congr 1
      rw [hcuw, Finset.card_pair huw]; omega
    have : Ideal.height (primeComponent (K := K) G ∅) ≠
        Ideal.height (primeComponent (K := K) G {u, w}) := by
      rw [hP0_ht, hPuw_ht]
      simp only [ne_eq, Nat.cast_inj]
      omega
    exact this (hunmixed _ _ hP0_min hPuw_min)

end

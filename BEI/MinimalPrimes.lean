import BEI.PrimeIdeals
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Artinian.Ring

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

/--
**Corollary 3.9** (Herzog et al. 2010): Assuming G is connected,
`P_S(G)` is a minimal prime of `J_G` if and only if either:
- S = ∅ (then P_∅(G) = J_G is the "generic" prime), or
- every vertex in S is a cut-vertex relative to S.

Reference: Herzog et al. (2010), Corollary 3.9.
-/
theorem corollary_3_9 (G : SimpleGraph V) (S : Finset V)
    (hConn : G.Connected) :
    primeComponent (K := K) G S ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes ↔
    S = ∅ ∨ ∀ i ∈ S, IsCutVertexRelative G S i := by
  sorry

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

end

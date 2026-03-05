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
    refine ⟨fun a haT => ?_, sorry⟩
    -- T ≤ S: if a ∈ T then a ∈ S. If a ∉ S, prop_3_8_var_not_mem gives X(inl a) ∉ P_S,
    -- but X(inl a) ∈ P_T ≤ P_S — contradiction.
    by_contra haS
    exact prop_3_8_var_not_mem G S a haS
      (h (Ideal.subset_span (Set.mem_union_left _ ⟨a, haT, Or.inl rfl⟩)))
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

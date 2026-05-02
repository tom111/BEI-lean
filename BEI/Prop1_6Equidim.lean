import BEI.PrimeDecompositionDimensionCore
import BEI.PrimeDecomposition
import BEI.MinimalPrimes

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Path graph and Proposition 1.6 equidimensional surrogate

Path-graph (Example 1.7b) and Proposition 1.6 surrogate machinery split out of
`BEI/PrimeDecompositionDimension.lean`. These two blocks share a substantial
amount of internal arithmetic (cut-vertex / merged-component bookkeeping under
the closed-graph hypothesis) but only weakly interact with the rest of the
Section 3 surrogate package.

## Public paper-facing endpoints

- `path_isEquidim`: Example 1.7(b), the path graph at the equidimensional
  surrogate level.
- `prop_1_6_equidim`: equidimensional surrogate of Proposition 1.6.

The Cor 3.4 / Cor 3.7 surrogate variants and `corollary_3_3` family live in
`BEI/PrimeDecompositionDimension.lean` and
`BEI/PrimeDecompositionDimensionCore.lean` respectively.

## Reference: Herzog et al. (2010), Proposition 1.6, Example 1.7.
-/

noncomputable section

open MvPolynomial SimpleGraph

/-! ## Building the local equidimensional surrogate from minimal primes -/

omit [LinearOrder V] [DecidableEq V] [Fintype V] in
/-- If all `Ideal.minimalPrimes` of `J` have the same quotient dimension, then `R ⧸ J`
is equidimensional in the local surrogate sense. -/
private theorem isEquidim_of_equidim_minimalPrimes
    (J : Ideal (MvPolynomial (BinomialEdgeVars V) K))
    (hequal : ∀ P Q : Ideal (MvPolynomial (BinomialEdgeVars V) K),
      P ∈ J.minimalPrimes → Q ∈ J.minimalPrimes →
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ Q)) :
    IsEquidimRing (MvPolynomial (BinomialEdgeVars V) K ⧸ J) where
  equidimensional P' Q' hP'min hQ'min := by
    -- Convert: minimalPrimes (R/J) → J.minimalPrimes via comap
    have hP_mem : Ideal.comap (Ideal.Quotient.mk J) P' ∈ J.minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P', hP'min, rfl⟩
    have hQ_mem : Ideal.comap (Ideal.Quotient.mk J) Q' ∈ J.minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨Q', hQ'min, rfl⟩
    rw [ringKrullDim_quotQuot_eq J P', ringKrullDim_quotQuot_eq J Q']
    exact hequal _ _ hP_mem hQ_mem


omit [LinearOrder V] in
/-- If `a, b ∉ T`, `SameComponent G (T.erase j) a b`, and `¬ SameComponent G T a b`,
then `componentCount G (T.erase j) < componentCount G T`.

Proof: the inclusion `V \ T ⊆ V \ (T.erase j)` induces a map `f` on connected
components. `f` is surjective (every CC of `G[V \ (T.erase j)]` contains a
vertex of `V \ T`, because if `j`'s CC were `{j}` alone then `a, b` would be
connected in `G[V \ T]`, contradicting the hypothesis). `f` is not injective
(`a` and `b` are in different CCs of `V \ T` but mapped to the same CC).
By `Fintype.card_lt_of_surjective_not_injective`, the result follows. -/
private lemma componentCount_lt_of_merged
    (G : SimpleGraph V) (T : Finset V) (j : V) (hjT : j ∈ T)
    {a b : V} (haT : a ∉ T) (hbT : b ∉ T)
    (hsc : SameComponent G (T.erase j) a b) (hnotsc : ¬SameComponent G T a b) :
    componentCount G (T.erase j) < componentCount G T := by
  classical
  unfold componentCount
  haveI : Fintype (G.induce {v : V | v ∉ T.erase j}).ConnectedComponent := Fintype.ofFinite _
  haveI : Fintype (G.induce {v : V | v ∉ T}).ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have hincl : ({w : V | w ∉ T} : Set V) ⊆ {w | w ∉ T.erase j} :=
    fun w hw h => hw (Finset.erase_subset j T h)
  let ι := SimpleGraph.induceHomOfLE G hincl
  let f := SimpleGraph.ConnectedComponent.map ι.toHom
  -- We show: card(CCs of G[V\T]) > card(CCs of G[V\(T.erase j)])
  -- The inclusion V\T ⊆ V\(T.erase j) induces f on CCs.
  -- f is surjective + not injective → strict inequality.
  -- First establish that j is reachable from a in G[V\(T.erase j)].
  -- If not, the walk from a to b avoids j and lifts to G[V\T], contradiction.
  have haTe : a ∉ T.erase j := fun h => haT (Finset.erase_subset j T h)
  have hbTe : b ∉ T.erase j := fun h => hbT (Finset.erase_subset j T h)
  have hjTe : (j : V) ∉ T.erase j := Finset.notMem_erase j T
  -- j and a are in the same CC of G[V\(T.erase j)].
  -- Proof: if not, the SC path from a to b avoids j and lifts to G[V\T].
  have hja_same : (G.induce {w | w ∉ T.erase j}).Reachable
      ⟨j, hjTe⟩ ⟨a, haTe⟩ := by
    by_contra hja_diff
    apply hnotsc
    obtain ⟨_, _, hpath⟩ := hsc
    refine ⟨haT, hbT, ?_⟩
    -- Lift hpath from G[V\(T.erase j)] to G[V\T] by showing it avoids j.
    -- Strategy: prove simultaneously that (1) the path lifts and (2) j is not visited.
    -- We strengthen the induction: for any z reachable from a in G[V\(T.erase j)],
    -- z ≠ j and z is reachable from a in G[V\T].
    suffices ∀ (z : V),
        Relation.ReflTransGen (fun p q => G.Adj p q ∧ p ∉ T.erase j ∧ q ∉ T.erase j) a z →
        z ≠ j ∧ Relation.ReflTransGen (fun p q => G.Adj p q ∧ p ∉ T ∧ q ∉ T) a z from
      (this b hpath).2
    intro z haz
    induction haz with
    | refl =>
      exact ⟨fun haj => haT (haj ▸ hjT), .refl⟩
    | @tail x y hax_path hxy ih =>
      obtain ⟨hx_ne_j, hax_lifted⟩ := ih
      have hy_ne_j : y ≠ j := by
        intro hyj; apply hja_diff
        exact (sameComponent_to_reachable G (T.erase j) a j haTe hjTe
          ⟨haTe, hjTe, hax_path.tail (hyj ▸ hxy)⟩).symm
      obtain ⟨hadj, hxTe, hyTe⟩ := hxy
      exact ⟨hy_ne_j, hax_lifted.tail ⟨hadj,
        fun hxT => hxTe (Finset.mem_erase.mpr ⟨hx_ne_j, hxT⟩),
        fun hyT => hyTe (Finset.mem_erase.mpr ⟨hy_ne_j, hyT⟩)⟩⟩
  apply Fintype.card_lt_of_surjective_not_injective f
  · -- Surjective
    intro cc
    induction cc using SimpleGraph.ConnectedComponent.ind with | h v =>
    by_cases hvj : v.val = j
    · -- v's CC contains j, which is in a's CC. Use a as preimage.
      refine ⟨(G.induce {w | w ∉ T}).connectedComponentMk ⟨a, haT⟩, ?_⟩
      simp only [f, SimpleGraph.ConnectedComponent.map_mk]
      -- Goal: CC of ι(a) = CC of v, where v.val = j
      -- ι.toHom ⟨a, haT⟩ = ⟨a, haTe⟩ (by Subtype.ext rfl)
      -- CC of ⟨a, haTe⟩ = CC of ⟨j, hjTe⟩ (by hja_same)
      -- v = ⟨j, hjTe⟩ (by hvj)
      have hιa : ι.toHom ⟨a, haT⟩ = ⟨a, haTe⟩ := Subtype.ext rfl
      rw [hιa, SimpleGraph.ConnectedComponent.eq]
      have hv_eq : v = ⟨j, hjTe⟩ := Subtype.ext hvj
      rw [hv_eq]
      exact hja_same.symm
    · -- v ≠ j, so v ∈ V\T
      have hvT : v.val ∉ T := fun h =>
        v.prop (Finset.mem_erase.mpr ⟨fun hh => hvj hh, h⟩)
      refine ⟨(G.induce {w | w ∉ T}).connectedComponentMk ⟨v.val, hvT⟩, ?_⟩
      have : ι.toHom ⟨v.val, hvT⟩ = v := Subtype.ext rfl
      rw [show f ((G.induce {w | w ∉ T}).connectedComponentMk ⟨v.val, hvT⟩) =
               (G.induce {w | w ∉ T.erase j}).connectedComponentMk (ι.toHom ⟨v.val, hvT⟩) from
           SimpleGraph.ConnectedComponent.map_mk ι.toHom ⟨v.val, hvT⟩, this]
  · -- Not injective
    intro hinj
    have hCab : (G.induce {w | w ∉ T}).connectedComponentMk ⟨a, haT⟩ ≠
                (G.induce {w | w ∉ T}).connectedComponentMk ⟨b, hbT⟩ := by
      rw [ne_eq, SimpleGraph.ConnectedComponent.eq]
      rintro ⟨walk⟩
      exact hnotsc (reachable_induce_imp_sameComponent G T ⟨walk⟩)
    apply hCab; apply hinj
    simp only [f, SimpleGraph.ConnectedComponent.map_mk]
    rw [SimpleGraph.ConnectedComponent.eq]
    exact sameComponent_to_reachable G (T.erase j) a b haTe hbTe hsc

/-! ## Example 1.7(b): Path graph at the equidimensional surrogate level -/

/-- The path graph on Fin n is connected when n ≥ 1.
Proof: vertex 0 can reach any vertex k by walking along edges 0-1-2-...-k. -/
private theorem path_connected (n : ℕ) (hn : n ≥ 1) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n),
      G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    G.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨fun u v => ?_, ⟨⟨0, by omega⟩⟩⟩
  suffices ∀ (w : Fin n), G.Reachable ⟨0, by omega⟩ w by
    exact (this u).symm.trans (this v)
  intro w
  -- Induction on w.val
  have : ∀ k (hk : k < n), G.Reachable ⟨0, by omega⟩ ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl _
    | succ k ih =>
      intro hk
      have hk' : k < n := by omega
      have hadj : G.Adj ⟨k, hk'⟩ ⟨k + 1, hk⟩ := by rw [hPath]; left; rfl
      exact (ih hk').trans (SimpleGraph.Adj.reachable hadj)
  exact this w.val w.isLt

/-- In a path graph, if vertices u, v ∉ S and all integers strictly between u.val and v.val
are also not in S, then u and v are in the same component of G[V\S]. -/
private theorem path_sameComponent_of_interval (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n),
      G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (S : Finset (Fin n)) (u v : Fin n) (huS : u ∉ S) (hvS : v ∉ S)
    (huv : u.val ≤ v.val)
    (hint : ∀ k : Fin n, u.val < k.val → k.val < v.val → k ∉ S) :
    SameComponent G S u v := by
  refine ⟨huS, hvS, ?_⟩
  -- Induction on the gap between u and v
  suffices ∀ (d : ℕ) (a b : Fin n), a ∉ S → b ∉ S → a.val + d = b.val →
      (∀ k : Fin n, a.val < k.val → k.val < b.val → k ∉ S) →
      Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ S ∧ y ∉ S) a b from
    this (v.val - u.val) u v huS hvS (by omega) hint
  intro d
  induction d with
  | zero =>
    intro a b _ _ hd _
    have : a = b := Fin.ext (by omega)
    subst this; exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro a b haS hbS hd hint'
    have ha1 : a.val + 1 < n := by omega
    let a' : Fin n := ⟨a.val + 1, ha1⟩
    have ha'val : a'.val = a.val + 1 := rfl
    have ha'S : a' ∉ S := by
      cases d with
      | zero =>
        have hab : a' = b := Fin.ext (by omega)
        rw [hab]; exact hbS
      | succ d =>
        have h1 : a.val < a'.val := by omega
        have h2 : a'.val < b.val := by omega
        exact hint' a' h1 h2
    have hadj : G.Adj a a' := by
      rw [hPath]; left; exact ha'val
    have hd' : a'.val + d = b.val := by omega
    have hint'' : ∀ k : Fin n, a'.val < k.val → k.val < b.val → k ∉ S :=
      fun k hk1 hk2 => hint' k (by omega) hk2
    exact Relation.ReflTransGen.head ⟨hadj, haS, ha'S⟩ (ih a' b ha'S hbS hd' hint'')

/-- For a path graph on `Fin n`, `componentCount G S ≤ S.card + 1`.

**Proof**: Construct an injection from connected components to `Option S`.
For each component `c` of `G[V\S]`, let `m(c)` be the maximum vertex in `c`.
If `m(c).val + 1 < n`, then the vertex `m(c) + 1` must be in `S` (otherwise it would
be adjacent to `m(c)` in the path and thus in the same component, contradicting
maximality). Map `c` to `some ⟨m(c)+1, _⟩`. If `m(c).val + 1 ≥ n`, map to `none`.
This map is injective because two distinct components cannot share their max vertex. -/
private theorem path_componentCount_le_card_add_one (n : ℕ) (_hn : n ≥ 1)
    (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n),
      G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
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
    -- m1 is adjacent to m in the path
    have hadj : G.Adj m m1 := by rw [hPath]; left; rfl
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

/-- In a path graph, any `ReflTransGen` walk that avoids `T` and starts at a vertex
with value `< j.val` (where `j ∈ T`) stays strictly below `j.val`. This is the
discrete intermediate-value argument: each step changes `.val` by 1, so crossing
`j.val` would require visiting `j`, contradicting avoidance of `T`. -/
private lemma path_reflTransGen_stays_below (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n), G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (T : Finset (Fin n)) (j : Fin n) (hjT : j ∈ T)
    {a c : Fin n} (ha_lt : a.val < j.val)
    (hac : Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ T ∧ y ∉ T) a c) :
    c.val < j.val := by
  induction hac with
  | refl => exact ha_lt
  | @tail b d _ hbd ih =>
    have hb_lt := ih
    obtain ⟨hadj, _, hdT⟩ := hbd
    rw [hPath] at hadj
    rcases hadj with h | h
    · -- b.val + 1 = d.val
      by_contra hd_ge; push_neg at hd_ge
      have : d.val ≤ j.val := by omega
      have : d.val = j.val := by omega
      have : d = j := Fin.ext this
      exact hdT (this ▸ hjT)
    · -- d.val + 1 = b.val
      omega

/-- Symmetric version: a walk starting above `j.val` stays above `j.val`. -/
private lemma path_reflTransGen_stays_above (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n), G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (T : Finset (Fin n)) (j : Fin n) (hjT : j ∈ T)
    {a c : Fin n} (ha_gt : j.val < a.val)
    (hac : Relation.ReflTransGen (fun x y => G.Adj x y ∧ x ∉ T ∧ y ∉ T) a c) :
    j.val < c.val := by
  induction hac with
  | refl => exact ha_gt
  | @tail b d _ hbd ih =>
    have hb_gt := ih
    obtain ⟨hadj, _, hdT⟩ := hbd
    rw [hPath] at hadj
    rcases hadj with h | h
    · -- b.val + 1 = d.val
      omega
    · -- d.val + 1 = b.val
      by_contra hd_le; push_neg at hd_le
      have : d.val ≥ j.val := by omega
      have : d.val = j.val := by omega
      have : d = j := Fin.ext this
      exact hdT (this ▸ hjT)

/-- In a path graph, if `j ∈ T` separates `a` (with `a.val < j.val`) from `b`
(with `b.val > j.val`), then `a` and `b` are not connected in `G[V \ T]`. -/
private lemma path_not_sameComponent_across (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n), G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (T : Finset (Fin n)) (j a b : Fin n) (hjT : j ∈ T)
    (_haT : a ∉ T) (_hbT : b ∉ T)
    (ha : a.val < j.val) (hb : j.val < b.val) :
    ¬SameComponent G T a b := by
  intro ⟨_, _, hpath⟩
  have hc_lt := path_reflTransGen_stays_below n G hPath T j hjT ha hpath
  omega

/-- In a path graph, witnesses `a, b ∉ S` produced by `exists_merged_of_cutVertex G S j`
sit on opposite sides of `j` in the natural order on `Fin n`.

If both witnesses lay on the same side, `path_sameComponent_of_interval` would put them in
the same component of `G[V \ S]`, contradicting `¬SameComponent G S a b`. -/
private lemma path_witnesses_opposite_sides {n : ℕ} (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n), G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    {S : Finset (Fin n)} {j a b : Fin n}
    (hjS : j ∈ S) (haS : a ∉ S) (hbS : b ∉ S)
    (hsc_ej : SameComponent G (S.erase j) a b)
    (hnotsc_S : ¬SameComponent G S a b) :
    (a.val < j.val ∧ j.val < b.val) ∨ (b.val < j.val ∧ j.val < a.val) := by
  have ha_ne : a.val ≠ j.val := fun h => haS (Fin.ext h ▸ hjS)
  have hb_ne : b.val ≠ j.val := fun h => hbS (Fin.ext h ▸ hjS)
  rcases Nat.lt_or_gt_of_ne ha_ne with ha_lt | ha_gt <;>
    rcases Nat.lt_or_gt_of_ne hb_ne with hb_lt | hb_gt
  · -- Both below j: derive SameComponent G S a b, contradicting hnotsc_S.
    exfalso; apply hnotsc_S
    rcases le_or_gt a.val b.val with hab | hab
    · exact path_sameComponent_of_interval n G hPath S a b haS hbS hab (fun k hak hkb => by
        by_contra hkS
        have hkj : k ≠ j := fun h => by omega
        exact path_not_sameComponent_across n G hPath (S.erase j) k a b
          (Finset.mem_erase.mpr ⟨hkj, hkS⟩)
          (fun h => haS (Finset.erase_subset j S h))
          (fun h => hbS (Finset.erase_subset j S h))
          (by omega) (by omega) hsc_ej)
    · exact (path_sameComponent_of_interval n G hPath S b a hbS haS (by omega)
        (fun k hbk hka => by
          by_contra hkS
          have hkj : k ≠ j := fun h => by omega
          exact path_not_sameComponent_across n G hPath (S.erase j) k b a
            (Finset.mem_erase.mpr ⟨hkj, hkS⟩)
            (fun h => hbS (Finset.erase_subset j S h))
            (fun h => haS (Finset.erase_subset j S h))
            (by omega) (by omega) hsc_ej.symm)).symm
  · exact Or.inl ⟨ha_lt, hb_gt⟩
  · exact Or.inr ⟨hb_lt, ha_gt⟩
  · -- Both above j: symmetric to the "both below" case.
    exfalso; apply hnotsc_S
    rcases le_or_gt a.val b.val with hab | hab
    · exact path_sameComponent_of_interval n G hPath S a b haS hbS hab (fun k hak hkb => by
        by_contra hkS
        have hkj : k ≠ j := fun h => by omega
        exact path_not_sameComponent_across n G hPath (S.erase j) k a b
          (Finset.mem_erase.mpr ⟨hkj, hkS⟩)
          (fun h => haS (Finset.erase_subset j S h))
          (fun h => hbS (Finset.erase_subset j S h))
          (by omega) (by omega) hsc_ej)
    · exact (path_sameComponent_of_interval n G hPath S b a hbS haS (by omega)
        (fun k hbk hka => by
          by_contra hkS
          have hkj : k ≠ j := fun h => by omega
          exact path_not_sameComponent_across n G hPath (S.erase j) k b a
            (Finset.mem_erase.mpr ⟨hkj, hkS⟩)
            (fun h => hbS (Finset.erase_subset j S h))
            (fun h => haS (Finset.erase_subset j S h))
            (by omega) (by omega) hsc_ej.symm)).symm

/-- In a path graph, if `j` is a cut vertex relative to `S`, then `j` is also a cut vertex
relative to `S.erase i` for any `i` with `j ∈ S.erase i`.

Strategy: take the merging witnesses `a, b ∉ S` from `exists_merged_of_cutVertex`, observe
they sit on opposite sides of `j` (`path_witnesses_opposite_sides`), then transfer them to
`S.erase i`: monotonicity `S.erase i ⊆ S` keeps `a, b` outside the smaller set,
`(S.erase i).erase j ⊆ S.erase j` preserves their merger after erasing `j`, and
`path_not_sameComponent_across` re-blocks them in `S.erase i` because `j` still separates
their sides. The component-count strict inequality is then `componentCount_lt_of_merged`. -/
private lemma path_cutVertex_of_erase (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n), G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (S : Finset (Fin n)) (i j : Fin n)
    (hijS : j ∈ S.erase i)
    (hcutj : IsCutVertexRelative G S j) :
    IsCutVertexRelative G (S.erase i) j := by
  have hjS : j ∈ S := Finset.mem_of_mem_erase hijS
  refine ⟨hijS, ?_⟩
  obtain ⟨a, b, haS, hbS, hsc_ej, hnotsc_S⟩ := exists_merged_of_cutVertex G S j hcutj
  have hab_opp := path_witnesses_opposite_sides G hPath hjS haS hbS hsc_ej hnotsc_S
  have haSi : a ∉ S.erase i := fun h => haS (Finset.erase_subset i S h)
  have hbSi : b ∉ S.erase i := fun h => hbS (Finset.erase_subset i S h)
  have herase_sub : (S.erase i).erase j ≤ S.erase j := fun x hx => by
    rw [Finset.mem_erase] at hx ⊢
    exact ⟨hx.1, Finset.mem_of_mem_erase hx.2⟩
  have hsc_eij : SameComponent G ((S.erase i).erase j) a b :=
    SameComponent_mono G herase_sub hsc_ej
  have hnotsc_Si : ¬SameComponent G (S.erase i) a b := by
    rcases hab_opp with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact path_not_sameComponent_across n G hPath (S.erase i) j a b hijS haSi hbSi ha hb
    · exact fun h => path_not_sameComponent_across n G hPath (S.erase i) j b a
        hijS hbSi haSi hb ha h.symm
  exact componentCount_lt_of_merged G (S.erase i) j hijS haSi hbSi hsc_eij hnotsc_Si

/-- For the path graph, removing a set S of non-consecutive interior vertices from the path
creates |S| + 1 connected components (each removed vertex splits one path segment in two).
For minimal primes of J_G, S consists of such vertices, so c(S) = |S| + c(∅). -/
private theorem path_minimalPrime_dim_eq (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n),
      G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (S : Finset (Fin n))
    (hmin : primeComponent (K := K) G S ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes) :
    (Fintype.card (Fin n) - S.card + componentCount G S : ℕ) =
    (Fintype.card (Fin n) + componentCount G ∅ : ℕ) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hn : n ≥ 1 := by obtain ⟨v, _⟩ := hne; exact Fin.pos v
    have hconn := path_connected n hn G hPath
    have hc0 : componentCount G ∅ = 1 := by
      rw [componentCount_empty]
      haveI : Subsingleton G.ConnectedComponent :=
        hconn.preconnected.subsingleton_connectedComponent
      haveI : Nonempty G.ConnectedComponent :=
        ⟨G.connectedComponentMk ⟨0, by omega⟩⟩
      exact Nat.card_unique
    have hub : componentCount G S ≤ S.card + 1 :=
      path_componentCount_le_card_add_one n hn G hPath S
    have hSn : S.card ≤ n := by
      calc S.card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
        _ = n := Fintype.card_fin n
    -- Prove c(S) = |S| + 1 by combining upper bound with strong induction.
    -- Strategy: by strong induction on |S|. For nonempty S:
    --   (a) corollary_3_9 gives every i ∈ S is a cut vertex ⟹ c(S\{i}) < c(S)
    --   (b) upper bound: c(S) ≤ |S| + 1
    --   (c) IH on S\{i} (which is also a minimal prime by cut-vertex preservation for
    --       paths): c(S\{i}) = |S\{i}| + 1 = |S|
    --   (d) from (a): c(S) > c(S\{i}) = |S|, so c(S) ≥ |S| + 1
    --   (e) from (b) and (d): c(S) = |S| + 1
    -- The key path-specific input is cut-vertex preservation under erasure for
    -- non-consecutive interior vertices.
    suffices hlb : componentCount G S ≥ S.card + 1 by
      rw [Fintype.card_fin, hc0]; omega
    -- Obtain cut vertex from corollary_3_9
    have hcv : ∀ i ∈ S, IsCutVertexRelative G S i := by
      have h39 := (corollary_3_9 (K := K) G S hconn).mp hmin
      rcases h39 with rfl | h
      · exact absurd rfl (Finset.Nonempty.ne_empty hne)
      · exact h
    obtain ⟨i, hiS⟩ := hne
    have hcut_lt := (hcv i hiS).2  -- c(S.erase i) < c(S)
    -- P_{S.erase i} is also a minimal prime (cut vertex preservation for paths)
    -- For paths: elements of S are non-consecutive interior vertices.
    -- Erasing i doesn't affect neighborhoods of remaining j ∈ S (since |i-j| ≥ 2),
    -- so each j is still a cut vertex relative to S.erase i.
    have hmin_erase : primeComponent (K := K) G (S.erase i) ∈
        (binomialEdgeIdeal (K := K) G).minimalPrimes := by
      rw [corollary_3_9 (K := K) G (S.erase i) hconn]
      rcases (S.erase i).eq_empty_or_nonempty with heq | _
      · exact Or.inl heq
      · right; intro j hjS'
        exact path_cutVertex_of_erase n G hPath S i j hjS' (hcv j (Finset.mem_of_mem_erase hjS'))
    -- IH on S.erase i: c(S.erase i) = |S.erase i| + 1
    have ih := path_minimalPrime_dim_eq n G hPath (S.erase i) hmin_erase
    have hcard_erase := Finset.card_erase_of_mem hiS
    rw [Fintype.card_fin, hc0] at ih
    -- ih : n - (S.card - 1) + c(S.erase i) = n + 1
    -- From cut vertex: c(S) > c(S.erase i) = n + 1 - (n - (S.card - 1)) = S.card
    omega
  termination_by S.card
  decreasing_by exact Finset.card_erase_lt_of_mem hiS

/--
**Example 1.7(b)** at the equidimensional surrogate level: the path on `n` vertices
(with natural ordering) yields an equidimensional quotient.

Proof: Every minimal prime `P_S` of `J_G` satisfies `dim(R/P_S) = n + 1`.
This is because for valid S (non-consecutive interior vertices), removing S from
the path creates |S| + 1 connected components, so `n - |S| + c(S) = n + 1`.
Since all minimal primes have equal quotient dimension, `R/J_G` is equidimensional.
-/
theorem path_isEquidim (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n),
      G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    IsEquidim
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal G) := by
  apply isEquidim_of_equidim_minimalPrimes
  intro P Q hP hQ
  -- Every minimal prime is P_S for some S
  have hP' := hP; have hQ' := hQ
  rw [minimalPrimes_characterization G] at hP' hQ'
  obtain ⟨SP, rfl, _⟩ := hP'
  obtain ⟨SQ, rfl, _⟩ := hQ'
  -- Use the dimension formula
  rw [ringKrullDim_quot_primeComponent, ringKrullDim_quot_primeComponent]
  -- Reduce to the combinatorial fact
  congr 1
  have hP_eq := path_minimalPrime_dim_eq (K := K) n G hPath SP hP
  have hQ_eq := path_minimalPrime_dim_eq (K := K) n G hPath SQ hQ
  omega

/-! ## Proposition 1.6: closed graphs are CM -/

omit [LinearOrder V] [Fintype V] in
/-- From `SameComponent G (S.erase j) a b` and `¬ SameComponent G S a b`,
extract a vertex `u ∉ S` adjacent to `j` with `SameComponent G S a u`.
The path from `a` to `b` in `G[V\(S\{j})]` must visit `j` (otherwise it lifts
to `G[V\S]`); the predecessor of the first visit gives the bridge. -/
private lemma exists_adj_bridge_of_sameComponent_erase
    {G : SimpleGraph V} {S : Finset V} {j a b : V}
    (hjS : j ∈ S) (haS : a ∉ S) (_hbS : b ∉ S)
    (hsc : SameComponent G (S.erase j) a b)
    (hnotsc : ¬ SameComponent G S a b) :
    ∃ u, u ∉ S ∧ G.Adj u j ∧ SameComponent G S a u := by
  obtain ⟨_, _, hpath⟩ := hsc
  -- The path either avoids j (lifts → contradiction) or visits j (extract bridge).
  suffices ∀ z,
    Relation.ReflTransGen (fun p q => G.Adj p q ∧ p ∉ S.erase j ∧ q ∉ S.erase j) a z →
    (z ≠ j ∧ z ∉ S ∧ Relation.ReflTransGen (fun p q => G.Adj p q ∧ p ∉ S ∧ q ∉ S) a z) ∨
    (∃ u, u ∉ S ∧ G.Adj u j ∧
      Relation.ReflTransGen (fun p q => G.Adj p q ∧ p ∉ S ∧ q ∉ S) a u) from by
    rcases this b hpath with ⟨_, hbS', hpath_lifted⟩ | ⟨u, huS, hadj, hpath'⟩
    · exact absurd ⟨haS, hbS', hpath_lifted⟩ hnotsc
    · exact ⟨u, huS, hadj, haS, huS, hpath'⟩
  intro z haz
  induction haz with
  | refl =>
    left; exact ⟨fun h => haS (h ▸ hjS), haS, .refl⟩
  | @tail x y _ hxy ih =>
    rcases ih with ⟨hx_ne_j, hxS, hax_lifted⟩ | hresult
    · by_cases hyj : y = j
      · right; exact ⟨x, hxS, hyj ▸ hxy.1, hax_lifted⟩
      · left
        have hyS : y ∉ S := fun hyS => hxy.2.2 (Finset.mem_erase.mpr ⟨hyj, hyS⟩)
        exact ⟨hyj, hyS, hax_lifted.tail ⟨hxy.1, hxS, hyS⟩⟩
    · right; exact hresult

/-- In a connected closed graph with `SatisfiesProp1_6Condition`, if `p < s` and
`G.Adj p t` (with `s ≤ t`, ensured by `closedGraph_adj_between`) and `G.Adj s q`
(with `s < q`), then `G.Adj p q`.

The proof uses `closedGraph_adj_between` to get `G.Adj p (s+1)`, then either
`q = s+1` (done) or `hCond` with `γ = q-1` to get `G.Adj p q`. -/
private lemma adj_of_gap {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (hConn : G.Connected)
    (hCond : SatisfiesProp1_6Condition n G)
    {p s t q : Fin n}
    (hps : p < s) (hst : s < t) (hadj_pt : G.Adj p t)
    (hsq : s < q) (hadj_sq : G.Adj s q) : G.Adj p q := by
  have hs1n : s.val + 1 < n := by have := t.isLt; omega
  have hs1 : Fin.mk (s.val + 1) (by omega) ≤ t :=
    Fin.mk_le_mk.mpr (by omega)
  have hps1 : p < Fin.mk (s.val + 1) (by omega) :=
    Fin.mk_lt_mk.mpr (by omega)
  have hadj_ps1 : G.Adj p ⟨s.val + 1, by omega⟩ :=
    closedGraph_adj_between hClosed hConn hadj_pt (lt_trans hps hst) ⟨s.val + 1, by omega⟩
      hps1 hs1
  by_cases hq_eq : q = ⟨s.val + 1, by omega⟩
  · rwa [hq_eq]
  · have hq_gt : s.val + 1 < q.val := by
      have := Fin.lt_def.mp hsq
      simp only [Fin.ext_iff] at hq_eq; omega
    have hq_pos : 0 < q.val := by omega
    have hqn : q.val < n := q.isLt
    set m : Fin n := ⟨q.val - 1, by omega⟩
    have hm_val : m.val = q.val - 1 := rfl
    have hm1 : m.val + 1 = q.val := by omega
    have hsm : s < m := Fin.mk_lt_mk.mpr (by omega)
    have hadj_sm1 : G.Adj s ⟨m.val + 1, by omega⟩ := by
      have : (⟨m.val + 1, by omega⟩ : Fin n) = q := Fin.ext (by omega)
      rw [this]; exact hadj_sq
    have hadj_pm1 := hCond p s m hs1n (by omega) hps hsm hadj_ps1 hadj_sm1
    have : (⟨m.val + 1, by omega⟩ : Fin n) = q := Fin.ext (by omega)
    rw [this] at hadj_pm1; exact hadj_pm1

/-- Under `SatisfiesProp1_6Condition`, if `j` is a cut vertex relative to `S` and
`i ≠ j` is in `S`, then `j` is a cut vertex relative to `S.erase i`.

The idea: from `exists_merged_of_cutVertex G S j` we get witnesses `a, b` with
`SameComponent G (S.erase j) a b` and `¬ SameComponent G S a b`.
By monotonicity, `SameComponent G ((S.erase i).erase j) a b`.
The key step is `¬ SameComponent G (S.erase i) a b`: if they WERE connected in
`G[V \ (S \ {i})]`, the path must go through `i` (since `a, b` are not connected
in `G[V \ S]`). In a closed graph, both `i` and `j` lie in S-gaps between
convex components of `G[V \ S]`. Prop 1.6 forbids having two gap elements in
the same gap (the transitivity condition forces an edge between component
endpoints, contradicting separation). So `i` and `j` are in different gaps.
But a path from `a` to `b` through `i` must cross `j`'s gap without using `j`,
which is impossible since the gap consists entirely of S-elements. -/
private lemma closedGraph_cutVertex_preserved_of_erase
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hClosed : IsClosedGraph G) (hConn : G.Connected)
    (hCond : SatisfiesProp1_6Condition n G)
    (S : Finset (Fin n)) (i j : Fin n)
    (hjSi : j ∈ S.erase i)
    (hcutj : IsCutVertexRelative G S j) :
    IsCutVertexRelative G (S.erase i) j := by
  have hjS : j ∈ S := Finset.mem_of_mem_erase hjSi
  have hij : j ≠ i := (Finset.mem_erase.mp hjSi).1
  constructor
  · exact hjSi
  · -- Need: componentCount G ((S.erase i).erase j) < componentCount G (S.erase i)
    -- Get witnesses a, b separated by j
    obtain ⟨a, b, haS, hbS, hsc_ej, hnotsc_S⟩ :=
      exists_merged_of_cutVertex G S j hcutj
    -- a, b ∉ S.erase i (since a, b ∉ S and S.erase i ⊆ S)
    have haSi : a ∉ S.erase i := fun h => haS (Finset.erase_subset i S h)
    have hbSi : b ∉ S.erase i := fun h => hbS (Finset.erase_subset i S h)
    -- SameComponent G ((S.erase i).erase j) a b (by monotonicity)
    have herase_sub : (S.erase i).erase j ≤ S.erase j := by
      intro x hx
      rw [Finset.mem_erase] at hx ⊢
      exact ⟨hx.1, Finset.mem_of_mem_erase hx.2⟩
    have hsc_eij : SameComponent G ((S.erase i).erase j) a b :=
      SameComponent_mono G herase_sub hsc_ej
    -- Key: ¬ SameComponent G (S.erase i) a b
    -- This is where `SatisfiesProp1_6Condition` enters. The argument:
    -- Assume SC G (S.erase i) a b. The path from a to b in G[(V\S)∪{i}] must go
    -- through i (since ¬SC G S a b). By convexity of components in closed graphs,
    -- i and j must both lie in the single gap between a's and b's components.
    -- But the path through i avoids j, and the path through j avoids i.
    -- Having two S-elements in the same gap, both bridging the gap, combined with
    -- SatisfiesProp1_6Condition and closedGraph_adj_between, forces an edge between
    -- the component endpoints, contradicting them being in different components.
    have hnotsc_Si : ¬SameComponent G (S.erase i) a b := by
      by_cases hiS : i ∈ S
      · -- i ∈ S: use bridge extraction + gap analysis
        intro hsc_Si
        -- Bridge extraction for j (a-side and b-side)
        obtain ⟨u₁, hu₁S, hadj_u₁j, hsc_au₁⟩ :=
          exists_adj_bridge_of_sameComponent_erase hjS haS hbS hsc_ej hnotsc_S
        obtain ⟨v₁, hv₁S, hadj_v₁j, hsc_v₁b_raw⟩ :=
          exists_adj_bridge_of_sameComponent_erase hjS hbS haS hsc_ej.symm
            (fun h => hnotsc_S h.symm)
        -- Bridge extraction for i (a-side and b-side)
        obtain ⟨u₂, hu₂S, hadj_u₂i, hsc_au₂⟩ :=
          exists_adj_bridge_of_sameComponent_erase hiS haS hbS hsc_Si hnotsc_S
        obtain ⟨v₂, hv₂S, hadj_v₂i, hsc_v₂b_raw⟩ :=
          exists_adj_bridge_of_sameComponent_erase hiS hbS haS hsc_Si.symm
            (fun h => hnotsc_S h.symm)
        -- Normalize bridge components to have b on the right
        have hsc_v₁b : SameComponent G S v₁ b := hsc_v₁b_raw.symm
        have hsc_v₂b : SameComponent G S v₂ b := hsc_v₂b_raw.symm
        -- u₁, u₂ in a's component; v₁, v₂ in b's component (different components)
        have hsc_u₁v₁ : ¬SameComponent G S u₁ v₁ := fun hsc =>
          hnotsc_S (hsc_au₁.trans (hsc.trans hsc_v₁b))
        have hu₁v₁ : u₁ ≠ v₁ := fun h => hsc_u₁v₁ ⟨hu₁S, h ▸ hv₁S, h ▸ .refl⟩
        have hsc_u₂v₂ : ¬SameComponent G S u₂ v₂ := fun hsc =>
          hnotsc_S (hsc_au₂.trans (hsc.trans hsc_v₂b))
        -- j must be between u₁ and v₁: if both on same side, IsClosedGraph
        -- gives G.Adj u₁ v₁, contradicting different components
        have hbetween_j : (u₁ < j ∧ j < v₁) ∨ (v₁ < j ∧ j < u₁) := by
          have hu₁j : u₁ ≠ j := fun h => hu₁S (h ▸ hjS)
          have hv₁j : v₁ ≠ j := fun h => hv₁S (h ▸ hjS)
          rcases lt_or_gt_of_ne hu₁j with h1 | h1 <;>
            rcases lt_or_gt_of_ne hv₁j with h2 | h2
          · -- both < j: condition 2 gives Adj u₁ v₁
            exact absurd (hClosed.2 h1 h2 hu₁v₁ hadj_u₁j hadj_v₁j)
              (fun h => hsc_u₁v₁ ⟨hu₁S, hv₁S, .single ⟨h, hu₁S, hv₁S⟩⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · -- both > j: condition 1 gives Adj u₁ v₁
            exact absurd (hClosed.1 h1 h2 hu₁v₁ hadj_u₁j.symm hadj_v₁j.symm)
              (fun h => hsc_u₁v₁ ⟨hu₁S, hv₁S, .single ⟨h, hu₁S, hv₁S⟩⟩)
        -- Similarly i must be between u₂ and v₂
        have hu₂v₂ : u₂ ≠ v₂ := fun h => hsc_u₂v₂ ⟨hu₂S, h ▸ hv₂S, h ▸ .refl⟩
        have hbetween_i : (u₂ < i ∧ i < v₂) ∨ (v₂ < i ∧ i < u₂) := by
          have hu₂i : u₂ ≠ i := fun h => hu₂S (h ▸ hiS)
          have hv₂i : v₂ ≠ i := fun h => hv₂S (h ▸ hiS)
          rcases lt_or_gt_of_ne hu₂i with h1 | h1 <;>
            rcases lt_or_gt_of_ne hv₂i with h2 | h2
          · exact absurd (hClosed.2 h1 h2 hu₂v₂ hadj_u₂i hadj_v₂i)
              (fun h => hsc_u₂v₂ ⟨hu₂S, hv₂S, .single ⟨h, hu₂S, hv₂S⟩⟩)
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨h2, h1⟩
          · exact absurd (hClosed.1 h1 h2 hu₂v₂ hadj_u₂i.symm hadj_v₂i.symm)
              (fun h => hsc_u₂v₂ ⟨hu₂S, hv₂S, .single ⟨h, hu₂S, hv₂S⟩⟩)
        -- Gap analysis: SatisfiesProp1_6Condition + closedGraph_adj_between
        -- give a direct edge between the two components → contradiction.
        -- Helper: edge between components gives SC a b, contradicting hnotsc_S
        have mk_sc : ∀ {p q : Fin n}, p ∉ S → q ∉ S →
            SameComponent G S a p → SameComponent G S q b →
            G.Adj p q → SameComponent G S a b := fun hpS hqS hap hqb hadj =>
          hap.trans ⟨hpS, hqS, .single ⟨hadj, hpS, hqS⟩⟩ |>.trans hqb
        -- Convexity helper: if a b-side vertex β lies between two a-side
        -- vertices α₁ < β < α₂, then β is in a's component by convexity,
        -- contradicting β being in b's component.
        have convex_a : ∀ {α₁ α₂ β : Fin n},
            α₁ ∉ S → α₂ ∉ S → β ∉ S →
            SameComponent G S a α₁ → SameComponent G S a α₂ →
            SameComponent G S β b →
            α₁ < β → β < α₂ → False := by
          intro α₁ α₂ β hα₁S hα₂S hβS hsc_aα₁ hsc_aα₂ hsc_βb hlt₁ hlt₂
          have hsc_α₁α₂ : SameComponent G S α₁ α₂ := hsc_aα₁.symm.trans hsc_aα₂
          have hsc_α₁β : SameComponent G S α₁ β :=
            ⟨hα₁S, hβS, reflTransGen_convex_closed hClosed hConn hα₁S hβS hlt₁ hlt₂
              hsc_α₁α₂.2.2⟩
          exact hnotsc_S (hsc_aα₁.trans (hsc_α₁β.trans hsc_βb))
        -- Symmetric: a-side vertex between two b-side vertices
        have convex_b : ∀ {β₁ β₂ α : Fin n},
            β₁ ∉ S → β₂ ∉ S → α ∉ S →
            SameComponent G S β₁ b → SameComponent G S β₂ b →
            SameComponent G S a α →
            β₁ < α → α < β₂ → False := by
          intro β₁ β₂ α hβ₁S hβ₂S hαS hsc_β₁b hsc_β₂b hsc_aα hlt₁ hlt₂
          have hsc_β₁β₂ : SameComponent G S β₁ β₂ := hsc_β₁b.trans hsc_β₂b.symm
          have hsc_β₁α : SameComponent G S β₁ α :=
            ⟨hβ₁S, hαS, reflTransGen_convex_closed hClosed hConn hβ₁S hαS hlt₁ hlt₂
              hsc_β₁β₂.2.2⟩
          exact hnotsc_S (hsc_aα.trans (hsc_β₁α.symm.trans hsc_β₁b))
        -- Edge helper: G.Adj α β with α a-side, β b-side → contradiction
        have edge_contra : ∀ {α β : Fin n},
            α ∉ S → β ∉ S →
            SameComponent G S a α → SameComponent G S β b →
            G.Adj α β → False :=
          fun hαS hβS hsc_aα hsc_βb hadj =>
            hnotsc_S (mk_sc hαS hβS hsc_aα hsc_βb hadj)
        -- Closed-graph projection: if s < α, s < β, α ≠ β,
        -- G.Adj s α, G.Adj s β, then G.Adj α β
        -- (this is hClosed.1)
        -- Case analysis on bridge orientations
        rcases hbetween_j with ⟨hu₁j, hjv₁⟩ | ⟨hv₁j, hju₁⟩ <;>
          rcases hbetween_i with ⟨hu₂i, hiv₂⟩ | ⟨hv₂i, hiu₂⟩
        · -- Case 1: u₁ < j < v₁, u₂ < i < v₂
          -- a-side: u₁ (below j), u₂ (below i); b-side: v₁ (above j), v₂ (above i)
          -- Strategy: find an a-to-b edge via adj_of_gap or convexity.
          -- Sub-case on u₁ vs v₂:
          rcases lt_or_gt_of_ne (fun h : u₁ = v₂ =>
            hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b))) with hu₁v₂ | hv₂u₁
          · -- u₁ < v₂
            rcases lt_or_gt_of_ne (fun h : u₂ = v₁ =>
              hnotsc_S (hsc_au₂.trans (h ▸ hsc_v₁b))) with hu₂v₁ | hv₁u₂
            · -- u₂ < v₁: all a-side < all b-side (potentially)
              -- Use adj_of_gap: pick the right a-side vertex and b-side vertex
              -- Try p = u₂, adj to i (u₂ < i), and q = v₁ (above j, j < v₁)
              -- Need u₂ < i < j < v₁ or u₂ < j < i... depends on i vs j order
              rcases lt_or_gt_of_ne (Ne.symm hij) with hij | hji
              · -- i < j: u₂ < i, so adj_of_gap(u₂, i, v₂, v₁) if i < j < v₁
                -- Actually: adj_of_gap(p=u₂, s=i, t=v₂, q=v₁)
                -- needs u₂ < i < v₂, G.Adj u₂ v₂ — but we don't have G.Adj u₂ v₂!
                -- Better: adj_of_gap(p=u₁, s=i, t=j, q=v₂)
                -- needs u₁ < i. If u₁ < i: done. If u₁ > i: need different approach.
                rcases lt_or_gt_of_ne (fun h : u₁ = i =>
                  hu₁S (h ▸ hiS)) with hu₁i | hiu₁
                · -- u₁ < i < j: adj_of_gap(u₁, i, j, v₂) → G.Adj u₁ v₂
                  exact edge_contra hu₁S hv₂S hsc_au₁ hsc_v₂b
                    (adj_of_gap hClosed hConn hCond hu₁i hij hadj_u₁j hiv₂
                      hadj_v₂i.symm)
                · -- i < u₁ < j:
                  -- closedGraph_adj_between on G.Adj i v₂ (i < v₂) gives
                  -- G.Adj i u₁ if u₁ ≤ v₂ (true since u₁ < v₂ = hu₁v₂)
                  have hadj_iu₁ := closedGraph_adj_between hClosed hConn
                    hadj_v₂i.symm hiv₂ u₁ hiu₁ hu₁v₂.le
                  -- hClosed.1: i < u₁, i < v₂, u₁ ≠ v₂, G.Adj i u₁, G.Adj i v₂
                  -- → G.Adj u₁ v₂
                  exact edge_contra hu₁S hv₂S hsc_au₁ hsc_v₂b
                    (hClosed.1 hiu₁ hiv₂ (fun h : u₁ = v₂ =>
                      hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b)))
                      hadj_iu₁ hadj_v₂i.symm)
              · -- j < i: adj_of_gap(u₂, j, i, v₁) needs u₂ < j
                rcases lt_or_gt_of_ne (fun h : u₂ = j =>
                  hu₂S (h ▸ hjS)) with hu₂j | hju₂
                · -- u₂ < j < i: adj_of_gap(u₂, j, i, v₁)
                  exact edge_contra hu₂S hv₁S hsc_au₂ hsc_v₁b
                    (adj_of_gap hClosed hConn hCond hu₂j hji hadj_u₂i hjv₁
                      hadj_v₁j.symm)
                · -- j < u₂ < i:
                  have hadj_ju₂ := closedGraph_adj_between hClosed hConn
                    hadj_v₁j.symm hjv₁ u₂ hju₂ hu₂v₁.le
                  exact edge_contra hu₂S hv₁S hsc_au₂ hsc_v₁b
                    (hClosed.1 hju₂ hjv₁ (fun h : u₂ = v₁ =>
                      hnotsc_S (hsc_au₂.trans (h ▸ hsc_v₁b)))
                      hadj_ju₂ hadj_v₁j.symm)
            · -- v₁ < u₂: v₁ (b-side) < u₂ (a-side)
              -- v₁ < u₂ < i, and v₁ > j (from hjv₁), so j < v₁ < u₂ < i
              -- But u₁ < j < v₁ < u₂: v₁ between u₁ and u₂ → convexity
              exact convex_a hu₁S hu₂S hv₁S hsc_au₁ hsc_au₂ hsc_v₁b
                (lt_trans hu₁j hjv₁) hv₁u₂
          · -- v₂ < u₁: v₂ (b-side) < u₁ (a-side)
            -- v₂ < u₁ < j, and v₂ > i (from hiv₂), so i < v₂ < u₁
            -- u₂ < i < v₂ < u₁: v₂ between u₂ and u₁ → convexity
            exact convex_a hu₂S hu₁S hv₂S hsc_au₂ hsc_au₁ hsc_v₂b
              (lt_trans hu₂i hiv₂) hv₂u₁
        · -- Case 2: u₁ < j < v₁, v₂ < i < u₂
          -- a-side: u₁ (below j), u₂ (above i); b-side: v₁ (above j), v₂ (below i)
          rcases lt_or_gt_of_ne (fun h : u₂ = v₁ =>
            hnotsc_S (hsc_au₂.trans (h ▸ hsc_v₁b))) with hu₂v₁ | hv₁u₂
          · -- u₂ > v₁ handled below; here u₂ < v₁
            rcases lt_or_gt_of_ne (fun h : u₁ = v₂ =>
              hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b))) with hu₁v₂ | hv₂u₁
            · -- u₁ < v₂ < i < u₂ < v₁? Not necessarily.
              -- u₁ < j, v₂ < i, u₂ > i, v₁ > j
              rcases lt_or_gt_of_ne (Ne.symm hij) with hij | hji
              · -- i < j: v₂ < i < j, u₁ < j, u₂ > i, v₁ > j
                rcases lt_or_gt_of_ne (fun h : u₁ = i =>
                  hu₁S (h ▸ hiS)) with hu₁i | hiu₁
                · -- u₁ < i < j: adj_of_gap(u₁, i, j, u₂) needs i < u₂
                  -- G.Adj u₁ j (u₁ < j), G.Adj i u₂ (= hadj_u₂i.symm, i < u₂)
                  -- adj_of_gap gives G.Adj u₁ u₂ — but both a-side!
                  -- Instead: adj_of_gap(u₁, i, j, v₂)?
                  -- needs i < v₂ — but v₂ < i! So no.
                  -- Try: adj_of_gap(v₂, i, u₂, v₁)?
                  -- v₂ < i < u₂, G.Adj v₂ u₂? No.
                  -- Try closedGraph_adj_between on G.Adj u₁ j (u₁ < j):
                  -- gives G.Adj u₁ c for u₁ < c ≤ j. If v₂ in (u₁, j]:
                  -- G.Adj u₁ v₂. v₂ < i < j and u₁ < j.
                  -- Need u₁ < v₂? hu₁v₂ says u₁ < v₂. And v₂ < i < j, so v₂ ≤ j.
                  exact edge_contra hu₁S hv₂S hsc_au₁ hsc_v₂b
                    (closedGraph_adj_between hClosed hConn hadj_u₁j hu₁j v₂
                      hu₁v₂ (le_of_lt (lt_trans hv₂i hij)))
                · -- i < u₁ < j: use hClosed.1 via G.Adj i u₁ and G.Adj i v₂
                  -- v₂ < i, so G.Adj v₂ i (hadj_v₂i), i.e., G.Adj i v₂ wrong dir
                  -- Actually hadj_v₂i : G.Adj v₂ i, so i > v₂.
                  -- We want G.Adj u₁ v₂ with u₁ > v₂ (since u₁ > i > v₂)
                  -- closedGraph_adj_between on G.Adj u₁ j (u₁ < j):
                  -- gives G.Adj u₁ c for u₁ < c ≤ j. v₂ < i < u₁, so v₂ < u₁.
                  -- Can't reach v₂ from u₁ via this edge (wrong direction).
                  -- Try hClosed.2: v₂ < u₁ < j, G.Adj v₂ j? No.
                  -- closedGraph_adj_between on G.Adj v₂ i (v₂ < i):
                  -- gives G.Adj v₂ c for v₂ < c ≤ i. u₁ > i, so can't reach u₁.
                  -- What about G.Adj u₂ i (hadj_u₂i) with i < u₂:
                  -- closedGraph_adj_between on G.Adj i u₂ (i < u₂):
                  -- gives G.Adj i c for i < c ≤ u₂.
                  -- hClosed.2: v₂ < i, u₁ < ... hmm
                  -- Try: v₂ < i and v₂ < u₁ (since i < u₁). G.Adj v₂ i.
                  -- closedGraph_adj_between on G.Adj v₂ i (v₂ < i):
                  -- gives G.Adj v₂ u₁ if v₂ < u₁ ≤ i. But u₁ > i! Can't.
                  -- Try connecting via j:
                  -- G.Adj u₁ j (u₁ < j), G.Adj v₁ j (j < v₁).
                  -- hClosed.2 on j: u₁ < j, v₂ < j (v₂ < i < j), u₁ ≠ v₂,
                  -- G.Adj u₁ j, G.Adj v₂ j? We don't have G.Adj v₂ j!
                  -- Do we? v₂ < i < j. closedGraph_adj_between would need
                  -- some edge from v₂ spanning to j. We have G.Adj v₂ i (v₂ < i).
                  -- Not spanning to j.
                  -- Try via u₂: i < u₂, G.Adj u₂ i (= G.Adj i u₂ reversed).
                  -- closedGraph_adj_between on G.Adj i u₂ (i < u₂):
                  -- G.Adj i c for i < c ≤ u₂.
                  -- If j ≤ u₂: G.Adj i j. But j ∈ S!
                  -- From G.Adj i j (if j ≤ u₂): closedGraph_adj_between gives
                  -- G.Adj i c for i < c ≤ j... but we want edges to v₂ or from v₂.
                  -- Actually, we need a totally different approach.
                  -- v₂ < i < u₁ < j: v₂ is b-side, u₁ is a-side.
                  -- v₂ < u₁. G.Adj v₂ i (v₂ < i). G.Adj u₁ j (u₁ < j).
                  -- hClosed.2: v₂ < u₁ and ??? < u₁... no.
                  -- Let's try u₂ > i and v₁ > j:
                  -- If u₂ > j (which requires j < u₂):
                  -- closedGraph_adj_between on G.Adj i u₂ (i < u₂):
                  -- G.Adj i j if j ≤ u₂. Since i < j (hij) and j < u₂ would give
                  -- j ≤ u₂. But is j < u₂?
                  -- j ∈ S, u₂ ∉ S, so j ≠ u₂. If j < u₂: G.Adj i j from above.
                  -- Then hClosed.2 on j: u₁ < j, v₂ < j (v₂ < i < j),
                  -- v₂ ≠ u₁, G.Adj u₁ j, need G.Adj v₂ j.
                  -- G.Adj v₂ j? closedGraph_adj_between on G.Adj v₂ i (v₂ < i):
                  -- gives G.Adj v₂ c for v₂ < c ≤ i. j > i, can't reach j.
                  -- From G.Adj i j: closedGraph_adj_between on G.Adj i j? Wait,
                  -- does G.Adj i j even hold? Only if j ≤ u₂ as established.
                  -- If G.Adj i j: hClosed.2(v₂ < j, i < j, v₂ ≠ i,
                  -- G.Adj v₂ j? NO we need G.Adj v₂ j and G.Adj i j → G.Adj v₂ i)
                  -- We have G.Adj v₂ i and G.Adj i j. To get G.Adj v₂ j:
                  -- hClosed.1(v₂ < i, v₂ < j, i ≠ j, G.Adj v₂ i, G.Adj v₂ j)
                  -- Circular! We need G.Adj v₂ j to apply hClosed.1.
                  -- OK. I think the issue is: in this sub-case (v₂ < i < u₁ < j)
                  -- with Case 2 (v₂ < i < u₂), we can't directly connect v₂ to u₁
                  -- without involving gap vertices.
                  -- BUT: can v₂ be between u₁ and u₂?
                  -- u₂ > i and u₁ > i, so both a-side above i.
                  -- v₂ < i. So v₂ < min(u₁, u₂). No interleaving with a-side.
                  -- Can v₁ be helpful? v₁ > j > u₁ > i > v₂.
                  -- u₂ > i. If u₂ < v₁: both a-side and b-side above j?
                  -- u₂ could be > j or < j. u₂ > i and j > i.
                  -- If u₂ > j: closedGraph_adj_between on G.Adj i u₂ (i < u₂):
                  -- G.Adj i j (i < j ≤ u₂). Then from G.Adj i j (i < j) and
                  -- G.Adj i v₂ (= hadj_v₂i.symm... wait, i > v₂, so
                  -- hadj_v₂i : G.Adj v₂ i means G.Adj v₂ i, not G.Adj i v₂).
                  -- Hmm, SimpleGraph.Adj is symmetric, so G.Adj v₂ i = G.Adj i v₂.
                  -- OK so G.Adj i v₂ is just hadj_v₂i (by symmetry).
                  -- So we have G.Adj i j (just derived) and G.Adj i v₂ (= hadj_v₂i).
                  -- Wait, i > v₂ so i < v₂ is false. hadj_v₂i : G.Adj v₂ i.
                  -- i > v₂. hClosed.1(v₂ < i, v₂ < ?): nope, wrong direction.
                  -- From hClosed.2: u₁ < j, v₂ < j (since v₂ < i < j),
                  -- u₁ ≠ v₂, G.Adj u₁ j, G.Adj v₂ j → G.Adj u₁ v₂.
                  -- But we need G.Adj v₂ j! Derive:
                  -- G.Adj v₂ i (hadj_v₂i, v₂ < i) and G.Adj i j (derived, i < j).
                  -- hClosed.1(v₂ < i, v₂ < j (v₂ < i < j), i ≠ j,
                  -- G.Adj v₂ i, G.Adj v₂ j → G.Adj i j). Circular again!
                  -- We need G.Adj v₂ j to conclude G.Adj u₁ v₂.
                  -- To get G.Adj v₂ j: we have G.Adj v₂ i (v₂ < i).
                  -- closedGraph_adj_between on G.Adj v₂ i: G.Adj v₂ c for v₂ < c ≤ i.
                  -- j > i, so can't reach j.
                  -- What if we use adj_of_gap with G.Adj v₂ i and G.Adj i j?
                  -- adj_of_gap needs p < s < t, G.Adj p t.
                  -- Here p = v₂, s = i, t must satisfy G.Adj v₂ t with s < t.
                  -- But G.Adj v₂ i only reaches up to i, not beyond.
                  -- Unless we can extend. G.Adj v₂ i (v₂ < i) and G.Adj i j (i < j).
                  -- adj_of_gap(v₂, i, i, j) needs i < i, impossible.
                  -- Need a different edge for v₂ spanning to j.
                  -- KEY INSIGHT: use SatisfiesProp1_6Condition!
                  -- adj_of_gap(v₂, i, i, j): need G.Adj v₂ t with t > i and v₂ < i.
                  -- But we only have G.Adj v₂ i.
                  -- Hmm wait, adj_of_gap only uses closedGraph_adj_between and hCond.
                  -- It can't extend beyond the initial spanning edge.
                  -- So we're stuck with this approach.
                  -- ALTERNATIVE: maybe the case i < u₁ can't actually happen?
                  -- No, it can. Example: S = {2, 4}, i = 4, j = 2, u₁ = 3, v₁ = 5,
                  -- u₂ = 5, v₂ = 1. But wait, in Case 2 we have v₂ < i < u₂, so
                  -- v₂ < 4 < u₂. And u₁ < j = 2 < v₁. So u₁ < 2. And i < u₁
                  -- would be 4 < u₁ < 2, impossible.
                  -- AHA! In case i < j with Case 2 (v₂ < i < u₂) and Case 1
                  -- (u₁ < j < v₁): i < j and u₁ < j and i < u₁ means i < u₁ < j.
                  -- v₂ < i, so v₂ < i < u₁ < j. Now u₂ > i, so u₂ > i.
                  -- Could u₂ be between j and v₁? u₂ > i. If u₂ < j: i < u₂ < j.
                  -- Then we have v₂ < i < u₁ < j and v₂ < i < u₂ < j. All above v₂.
                  -- Also v₁ > j. Where is u₂ relative to u₁, v₁?
                  -- Actually, I realize the problem:
                  -- In this case 2 scenario where i < u₁ and v₂ < i:
                  -- v₂ < i < u₁. Since u₁ ∉ S and v₂ ∉ S:
                  -- If v₂ < u₁, can we check convexity?
                  -- v₂ b-side, u₁ a-side. v₂ could be between two b-side vertices.
                  -- b-side: v₁ > j > u₁ > i > v₂. v₂ < ... < v₁.
                  -- No a-side vertex between v₂ and v₁ (both b-side).
                  -- What if u₁ is between v₂ and v₁?
                  -- v₂ < i < u₁ < j < v₁. u₁ between v₂ and v₁ (b-side).
                  -- convex_b(v₂, v₁, u₁)! v₂ < u₁ < v₁.
                  -- But wait: we need v₂ < u₁ < v₁ and u₁ ∉ S.
                  -- v₂ < u₁: ✓ (v₂ < i < u₁)
                  -- u₁ < v₁: ✓ (u₁ < j < v₁)
                  -- YES! convex_b gives the contradiction!
                  exact convex_b hv₂S hv₁S hu₁S hsc_v₂b hsc_v₁b hsc_au₁
                    (lt_trans hv₂i hiu₁) (lt_trans hu₁j hjv₁)
              · -- j < i: v₂ < j < i, u₁ < j
                -- u₂ > i > j > u₁: u₁ < j, u₂ > i > j.
                -- v₂ < j, v₁ > j.
                -- All we need: u₁ < j < v₁ and v₂ < j < u₂.
                -- v₂ < u₁? Or u₁ < v₂? v₂ < i? No: v₂ < i from case I2.
                -- v₂ < i but j < i, so v₂ could be > j or < j.
                -- We know v₂ < i and j < i but v₂ vs j unknown.
                rcases lt_or_gt_of_ne (fun h : v₂ = j => hv₂S (h ▸ hjS))
                  with hv₂j | hjv₂
                · -- v₂ < j: v₂ < j, u₁ < j.
                  -- hClosed.2(v₂ < j, u₁ < j, v₂ ≠ u₁, G.Adj v₂ j?, G.Adj u₁ j)
                  -- Need G.Adj v₂ j. v₂ < i and j < i. v₂ < j < i.
                  -- closedGraph_adj_between on G.Adj v₂ i (v₂ < i):
                  -- G.Adj v₂ j (v₂ < j ≤ i, well j < i so j ≤ i-1 < i,
                  -- actually j.val < i.val so j ≤ i is Fin.le from j < i).
                  have hadj_v₂j : G.Adj v₂ j :=
                    closedGraph_adj_between hClosed hConn hadj_v₂i hv₂i j hv₂j
                      (le_of_lt hji)
                  have hu₁v₂_ne : u₁ ≠ v₂ := fun h =>
                    hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b))
                  -- hClosed.2: u₁ < j, v₂ < j, u₁ ≠ v₂, G.Adj u₁ j, G.Adj v₂ j
                  -- → G.Adj u₁ v₂
                  exact edge_contra hu₁S hv₂S hsc_au₁ hsc_v₂b
                    (hClosed.2 hu₁j hv₂j hu₁v₂_ne hadj_u₁j hadj_v₂j)
                · -- j < v₂ < i: v₂ between u₁ and u₂?
                  -- u₁ < j < v₂ < i < u₂.
                  -- u₁ (a-side) between v₂ and v₁?
                  -- u₁ < j < v₂. So u₁ < v₂. And v₁ > j > u₁.
                  -- convex_b(hv₂S... ): v₁ > j. u₁ < j < v₂.
                  -- u₁ between v₂ and v₁? Need v₂ < u₁ or u₁ < v₂.
                  -- u₁ < j < v₂. So u₁ < v₂. u₁ < v₁ (since u₁ < j < v₁).
                  -- Is u₁ between v₂ and v₁? No: u₁ < v₂ < v₁, so u₁ is
                  -- below both.
                  -- What about u₂? u₂ > i > v₂ > j > u₁. So u₂ > v₂.
                  -- v₂ between u₁ and u₂ (a-side)! u₁ < v₂ < u₂ (a-side).
                  -- convex_a! v₂ (b-side) between u₁, u₂ (a-side).
                  exact convex_a hu₁S hu₂S hv₂S hsc_au₁ hsc_au₂ hsc_v₂b
                    (lt_trans hu₁j hjv₂) (lt_trans hv₂i hiu₂)
            · -- hv₂u₁ : v₂ < u₁. Case 2: u₁ < j < v₁, v₂ < i < u₂, u₂ < v₁.
              -- v₂ < u₁ < j < v₁: u₁ (a-side) between v₂, v₁ (b-side). convex_b!
              exact convex_b hv₂S hv₁S hu₁S hsc_v₂b hsc_v₁b hsc_au₁
                hv₂u₁ (lt_trans hu₁j hjv₁)
          · -- v₁ < u₂: v₁ (b-side) < u₂ (a-side)
            -- v₁ > j, u₂ > i, v₂ < i, u₁ < j.
            -- v₁ < u₂. Is v₁ between a-side vertices?
            -- a-side: u₁ < j < v₁ < u₂. So u₁ < v₁ < u₂.
            -- convex_a: v₁ (b-side) between u₁ and u₂ (a-side).
            exact convex_a hu₁S hu₂S hv₁S hsc_au₁ hsc_au₂ hsc_v₁b
              (lt_trans hu₁j hjv₁) hv₁u₂
        · -- Case 3: v₁ < j < u₁, u₂ < i < v₂
          -- a-side: u₁ (above j), u₂ (below i); b-side: v₁ (below j), v₂ (above i)
          rcases lt_or_gt_of_ne (fun h : u₂ = v₁ =>
            hnotsc_S (hsc_au₂.trans (h ▸ hsc_v₁b))) with hu₂v₁ | hv₁u₂
          · -- u₂ < v₁: u₂ < v₁ < j
            -- u₁ > j, v₂ > i. v₁ < j < u₁ and u₂ < i < v₂.
            -- Is u₂ between v₁ and v₂?
            -- v₁ < j and u₂ < i. If v₁ > u₂ or v₁ < u₂...
            -- u₂ < v₁ (this branch). v₂ > i. v₁ < j.
            -- v₁ < j. u₁ > j. v₂ > i. u₂ < i.
            -- Position: u₂ < i, u₂ < v₁ < j < u₁, v₂ > i.
            rcases lt_or_gt_of_ne (Ne.symm hij) with hij | hji
            · -- i < j: u₂ < i < j.
              -- u₂ < v₁ < j. v₁ < j and i < j. v₁ vs i?
              -- If v₁ < i: u₂ < v₁ < i < j < u₁.
              -- v₁ (b-side) between u₂ and u₁ (a-side). convex_a.
              -- If v₁ > i: u₂ < i < v₁ < j < u₁.
              -- u₂ (a-side) between v₂ and v₁? v₂ > i and v₁ > i.
              -- But u₂ < i < both v₁ and v₂. No interleaving.
              -- If v₁ = i: impossible (v₁ ∉ S, i ∈ S).
              rcases lt_or_gt_of_ne (fun h : v₁ = i => hv₁S (h ▸ hiS)) with
                hv₁i | hiv₁
              · -- v₁ < i: u₂ < v₁ < i. convex_a(u₂, u₁, v₁)
                exact convex_a hu₂S hu₁S hv₁S hsc_au₂ hsc_au₁ hsc_v₁b
                  hu₂v₁ (lt_trans hv₁i (lt_trans hij hju₁))
              · -- i < v₁ < j: u₂ < i < v₁ < j < u₁
                -- adj_of_gap(u₂, i, v₁, ?) — no, need G.Adj u₂ v₁.
                -- Actually closedGraph_adj_between on G.Adj u₂ i is too short.
                -- Try: hClosed.2(u₂ < v₁, i < v₁, u₂ ≠ i, G.Adj u₂ v₁?, G.Adj i v₁?)
                -- Don't have either.
                -- adj_of_gap(u₂, i, v₂, v₁): u₂ < i < v₂, G.Adj u₂ v₂? No.
                -- Hmm. closedGraph_adj_between on G.Adj i v₂ (i < v₂):
                -- G.Adj i c for i < c ≤ v₂. If v₁ ≤ v₂: G.Adj i v₁.
                -- Then hClosed.2(u₂ < v₁, i < v₁, u₂ ≠ i,
                --   G.Adj u₂ v₁? ... still need G.Adj u₂ v₁.
                -- OK use hClosed.1: u₂ < i, u₂ < v₁ (since u₂ < v₁ in this branch),
                -- i ≠ v₁, G.Adj u₂ i (hadj_u₂i), G.Adj u₂ v₁?
                -- Still circular.
                -- Different approach: convex_b?
                -- v₁ < j < u₁, so u₁ between v₁ and v₂?
                -- v₂ > i and u₁ > j > v₁. If u₁ < v₂:
                -- v₁ < u₁ < v₂. convex_b(v₁, v₂, u₁): u₁ a-side between v₁, v₂ b-side.
                -- v₁ < u₁ ✓ (v₁ < j < u₁). u₁ < v₂? Need to check.
                rcases lt_or_gt_of_ne (fun h : u₁ = v₂ =>
                  hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b))) with hu₁v₂ | hv₂u₁
                · -- u₁ < v₂: v₁ < u₁ < v₂. convex_b!
                  exact convex_b hv₁S hv₂S hu₁S hsc_v₁b hsc_v₂b hsc_au₁
                    (lt_trans hv₁j hju₁) hu₁v₂
                · -- v₂ < u₁: v₂ > i and u₁ > j > i. So v₂ < u₁.
                  -- v₂ between u₂ and u₁? u₂ < i < v₂ < u₁ (v₂ > i, v₂ < u₁).
                  -- convex_a(u₂, u₁, v₂): u₂ < v₂ < u₁.
                  exact convex_a hu₂S hu₁S hv₂S hsc_au₂ hsc_au₁ hsc_v₂b
                    (lt_trans hu₂i hiv₂) hv₂u₁
            · -- j < i: v₁ < j < i, u₂ < i, u₁ > j, v₂ > i
              -- u₂ < v₁ < j < i. u₁ > j.
              rcases lt_or_gt_of_ne (fun h : u₁ = i => hu₁S (h ▸ hiS)) with
                hu₁i | hiu₁
              · -- u₁ < i: j < u₁ < i. u₂ < v₁ < j < u₁ < i.
                -- v₁ between u₂ and u₁: convex_a.
                exact convex_a hu₂S hu₁S hv₁S hsc_au₂ hsc_au₁ hsc_v₁b
                  hu₂v₁ (lt_trans hv₁j hju₁)
              · -- u₁ > i: v₁ < j < i < u₁.
                -- adj_of_gap(u₂, j, i, v₁)?
                -- u₂ < j? u₂ < v₁ < j. Yes, u₂ < v₁ < j.
                -- adj_of_gap(u₂, j, i, v₁):
                -- u₂ < j < i, G.Adj u₂ i (hadj_u₂i), j < v₁? No, v₁ < j.
                -- Hmm, v₁ < j, so G.Adj j v₁ → j > v₁.
                -- We want q = v₁ with j < v₁? No, v₁ < j.
                -- Different pivot: use G.Adj i v₂ (i < v₂) and connect u₂ to v₂.
                -- adj_of_gap(u₂, j, i, v₂):
                -- u₂ < j (u₂ < v₁ < j ✓), j < i (✓), G.Adj u₂ i (hadj_u₂i),
                -- j < v₂? v₂ > i > j. Yes.
                -- G.Adj j v₂: from closedGraph_adj_between on G.Adj j v₁?
                -- No: v₁ < j, so G.Adj v₁ j with v₁ < j, i.e., G.Adj j v₁ reversed.
                -- closedGraph_adj_between on G.Adj v₁ j (v₁ < j)? No, it gives
                -- G.Adj v₁ c for v₁ < c ≤ j, not G.Adj j c.
                -- Hmm. G.Adj j v₂: j < v₂ (j < i < v₂).
                -- Do we have an edge from j to something > j? G.Adj u₁ j with u₁ > j
                -- means G.Adj j u₁. From closedGraph_adj_between on G.Adj j u₁ (j < u₁):
                -- G.Adj j c for j < c ≤ u₁. If v₂ ≤ u₁: G.Adj j v₂.
                -- v₂ > i and u₁ > i. v₂ vs u₁?
                rcases lt_or_gt_of_ne (fun h : v₂ = u₁ =>
                  hnotsc_S (hsc_au₁.trans (h.symm ▸ hsc_v₂b))) with hv₂u₁ | hu₁v₂
                · -- v₂ < u₁: G.Adj j v₂ from closedGraph_adj_between on G.Adj j u₁.
                  have hadj_ju₁ : G.Adj j u₁ := hadj_u₁j.symm
                  have hadj_jv₂ := closedGraph_adj_between hClosed hConn
                    hadj_ju₁ hju₁ v₂ (lt_trans hji hiv₂) hv₂u₁.le
                  -- adj_of_gap(u₂, j, u₁, v₂) or directly:
                  -- hClosed.2: u₂ < j (u₂ < v₁ < j), v₂ < ??? no.
                  -- Actually: we have G.Adj u₂ i (u₂ < i) and G.Adj j v₂ (j < v₂).
                  -- adj_of_gap(u₂, j, i, v₂):
                  -- u₂ < j ✓, j < i ✓, G.Adj u₂ i ✓, j < v₂ ✓, G.Adj j v₂ ✓
                  exact edge_contra hu₂S hv₂S hsc_au₂ hsc_v₂b
                    (adj_of_gap hClosed hConn hCond
                      (lt_trans hu₂v₁ hv₁j) hji hadj_u₂i
                      (lt_trans hji hiv₂) hadj_jv₂)
                · -- u₁ < v₂: v₁ < j < i < u₁ < v₂.
                  -- u₁ between v₁ and v₂: convex_b!
                  exact convex_b hv₁S hv₂S hu₁S hsc_v₁b hsc_v₂b hsc_au₁
                    (lt_trans hv₁j hju₁) hu₁v₂
          · -- v₁ > u₂: u₂ < i and v₁ < j.
            -- v₁ < j < u₁ and u₂ < i < v₂.
            -- u₂ > v₁: u₂ > v₁ > ... wait, this branch is hv₁u₂ : v₁ > u₂? No!
            -- rcases ... with hu₂v₁ | hv₁u₂. hv₁u₂ means v₁ > u₂? Let me check.
            -- lt_or_gt_of_ne gives .inl (u₂ < v₁) or .inr (u₂ > v₁).
            -- So hv₁u₂ : u₂ > v₁. Confusing name. Let me re-read.
            -- Actually: rcases lt_or_gt_of_ne ... with hu₂v₁ | hv₁u₂
            -- lt_or_gt_of_ne (h : u₂ ≠ v₁) gives u₂ < v₁ or u₂ > v₁.
            -- .inl = u₂ < v₁ (named hu₂v₁)
            -- .inr = u₂ > v₁ (named hv₁u₂ : v₁ < u₂)
            -- Wait, lt_or_gt_of_ne h gives h.lt_or_lt which is a < b ∨ b < a.
            -- For Fin, lt_or_gt_of_ne (h : a ≠ b) gives a < b ∨ b < a.
            -- So .inr is v₁ < u₂.
            -- So hv₁u₂ : v₁ < u₂. Good.
            -- v₁ < j < u₁ and v₁ < u₂ < i < v₂.
            -- v₁ < u₂: u₂ > v₁. If u₂ > j:
            rcases lt_or_gt_of_ne (fun h : u₂ = j => hu₂S (h ▸ hjS)) with
              hu₂j | hju₂
            · -- u₂ < j: v₁ < u₂ < j < u₁. u₂ between v₁ and v₂?
              -- v₂ > i and u₂ < j. If i < j: u₂ < i < j (since u₂ < i and i < j).
              -- v₂ > i. u₂ < i < v₂. Is u₂ between v₁ and v₂?
              -- v₁ < u₂ and u₂ < v₂ (since u₂ < i < v₂).
              -- convex_b(v₁, v₂, u₂): u₂ a-side between v₁, v₂ b-side. ✓
              exact convex_b hv₁S hv₂S hu₂S hsc_v₁b hsc_v₂b hsc_au₂
                hv₁u₂ (lt_trans hu₂i hiv₂)
            · -- j < u₂: u₂ > j. v₁ < j < u₂ < i < v₂. u₁ > j.
              -- u₁ vs u₂: both a-side, both > j. u₁ > j and u₂ > j.
              -- u₂ < i < v₂ and u₁ > j. If u₁ > i:
              -- v₁ < j < u₂ < i < v₂ and u₁ > i.
              -- If u₁ < v₂: convex_b(v₁, v₂, u₁)? v₁ < u₁? v₁ < j < u₁. u₁ < v₂. ✓
              -- convex_b!
              rcases lt_or_gt_of_ne (fun h : u₁ = v₂ =>
                hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b))) with hu₁v₂ | hv₂u₁
              · exact convex_b hv₁S hv₂S hu₁S hsc_v₁b hsc_v₂b hsc_au₁
                  (lt_trans hv₁j hju₁) hu₁v₂
              · -- v₂ < u₁: v₂ between u₂ and u₁? u₂ < i < v₂ and u₁ > v₂ > i > u₂?
                -- Wait u₂ > j and u₁ > j. u₂ < i. v₂ > i. u₁ > v₂? v₂ < u₁.
                -- u₂ < i < v₂ < u₁. convex_a(u₂, u₁, v₂)!
                exact convex_a hu₂S hu₁S hv₂S hsc_au₂ hsc_au₁ hsc_v₂b
                  (lt_trans hu₂i hiv₂) hv₂u₁
        · -- Case 4: v₁ < j < u₁, v₂ < i < u₂
          -- a-side: u₁ (above j), u₂ (above i); b-side: v₁ (below j), v₂ (below i)
          -- In every sub-case, use adj_of_gap or convexity.
          rcases lt_or_gt_of_ne (Ne.symm hij) with hij | hji
          · -- i < j:
            -- v₂ < i < j, v₁ < j. adj_of_gap(v₁, i, j, u₂):
            -- Need v₁ < i. v₁ < j and v₂ < i. Is v₁ < i?
            rcases lt_or_gt_of_ne (fun h : v₁ = i => hv₁S (h ▸ hiS)) with hv₁i | hiv₁
            · -- v₁ < i: adj_of_gap(v₁, i, j, u₂)
              exact edge_contra hu₂S hv₁S hsc_au₂ hsc_v₁b
                (adj_of_gap hClosed hConn hCond hv₁i hij hadj_v₁j hiu₂
                  hadj_u₂i.symm).symm
            · -- i < v₁ < j: v₂ < i < v₁ < j < u₁.
              -- u₂ > i. Is u₂ between v₁ and v₂? v₂ < i < u₂ and v₁ > i.
              -- If u₂ < v₁: v₂ < u₂ < v₁. convex_b(v₂, v₁, u₂)!
              -- If u₂ > v₁: i < v₁ < u₂, and j < u₁.
              --   v₁ < j and v₁ < u₂. hClosed.2(v₁ < j, v₂ < j (v₂ < i < j),
              --   no, try adj_of_gap.
              rcases lt_or_gt_of_ne (fun h : u₂ = v₁ =>
                hnotsc_S (hsc_au₂.trans (h ▸ hsc_v₁b))) with hu₂v₁ | hv₁u₂
              · -- u₂ < v₁: convex_b(v₂, v₁, u₂). v₂ < i < u₂ (hiu₂), u₂ < v₁ (hu₂v₁).
                -- Wait v₂ < u₂ < v₁. Need v₂ < u₂. v₂ < i < u₂ ✓.
                exact convex_b hv₂S hv₁S hu₂S hsc_v₂b hsc_v₁b hsc_au₂
                  (lt_trans hv₂i hiu₂) hu₂v₁
              · -- v₁ < u₂: i < v₁ < u₂. Also v₁ < j < u₁.
                -- adj_of_gap(v₁, i, j, u₂)? v₁ > i, so v₁ < i is false. Can't.
                -- Try hClosed.2: v₁ < j, v₂ < j (v₂ < i < j), v₁ ≠ v₂,
                -- G.Adj v₁ j, G.Adj v₂ j? Need G.Adj v₂ j.
                -- closedGraph_adj_between on G.Adj v₂ i (v₂ < i):
                -- G.Adj v₂ c for v₂ < c ≤ i. j > i, can't reach j.
                -- Try: closedGraph_adj_between on G.Adj i u₂ (i < u₂):
                -- G.Adj i v₁ if i < v₁ ≤ u₂. hiv₁ ✓, hv₁u₂.le ✓.
                -- Then hClosed.1(i < v₁, i < u₂, v₁ ≠ u₂, G.Adj i v₁, G.Adj i u₂)
                -- → G.Adj v₁ u₂. edge_contra!
                have hadj_iv₁ := closedGraph_adj_between hClosed hConn
                  hadj_u₂i.symm hiu₂ v₁ hiv₁ hv₁u₂.le
                exact edge_contra hu₂S hv₁S hsc_au₂ hsc_v₁b
                  (hClosed.1 hiv₁ hiu₂ (fun h : v₁ = u₂ =>
                    hnotsc_S (hsc_au₂.trans (h ▸ hsc_v₁b)))
                    hadj_iv₁ hadj_u₂i.symm).symm
          · -- j < i:
            -- v₁ < j < i, v₂ < i. adj_of_gap(v₂, j, i, u₁):
            -- Need v₂ < j. v₂ < i and j < i. v₁ < j.
            rcases lt_or_gt_of_ne (fun h : v₂ = j => hv₂S (h ▸ hjS)) with hv₂j | hjv₂
            · -- v₂ < j: adj_of_gap(v₂, j, i, u₁)
              exact edge_contra hu₁S hv₂S hsc_au₁ hsc_v₂b
                (adj_of_gap hClosed hConn hCond hv₂j hji hadj_v₂i hju₁
                  hadj_u₁j.symm).symm
            · -- j < v₂ < i: v₁ < j < v₂ < i < u₂.
              -- u₁ > j. Is u₁ between v₂ and v₁? v₁ < j < u₁ and u₁ vs v₂?
              rcases lt_or_gt_of_ne (fun h : u₁ = v₂ =>
                hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b))) with hu₁v₂ | hv₂u₁
              · -- u₁ < v₂: v₁ < u₁ < v₂. convex_b(v₁, v₂, u₁)!
                exact convex_b hv₁S hv₂S hu₁S hsc_v₁b hsc_v₂b hsc_au₁
                  (lt_trans hv₁j hju₁) hu₁v₂
              · -- v₂ < u₁: j < v₂ < u₁. Also j < u₁.
                -- closedGraph_adj_between on G.Adj j u₁ (j < u₁):
                -- G.Adj j v₂ (j < v₂ ≤ u₁, hjv₂ ✓, hv₂u₁.le ✓).
                -- Then hClosed.1(j < v₂, j < u₁, v₂ ≠ u₁, G.Adj j v₂, G.Adj j u₁)
                -- → G.Adj v₂ u₁. edge_contra!
                have hadj_jv₂ := closedGraph_adj_between hClosed hConn
                  hadj_u₁j.symm hju₁ v₂ hjv₂ hv₂u₁.le
                exact edge_contra hu₁S hv₂S hsc_au₁ hsc_v₂b
                  (hClosed.1 hjv₂ hju₁ (fun h : v₂ = u₁ =>
                    hnotsc_S (hsc_au₁.trans (h ▸ hsc_v₂b)))
                    hadj_jv₂ hadj_u₁j.symm).symm
      · -- i ∉ S: S.erase i = S, trivial
        rwa [Finset.erase_eq_of_notMem hiS]
    -- Apply the general componentCount lemma
    exact componentCount_lt_of_merged G (S.erase i) j hjSi haSi hbSi hsc_eij hnotsc_Si

/-- For a connected closed graph satisfying `SatisfiesProp1_6Condition`, every
minimal-prime set `S` satisfies `componentCount G S = S.card + 1`.

The theorem is false without `SatisfiesProp1_6Condition` (counterexample: the
closed graph on Fin 5 with edges making a "fan" has a minimal-prime set S
with c(S) < |S| + 1).

**Proof**: By strong induction on `|S|`. Base `S = ∅`: c(∅) = 1 = 0 + 1.
Step `|S| ≥ 1`: pick `i ∈ S`. By `corollary_3_9`, `i` is a cut vertex, so
`c(S) > c(S.erase i)`. Under `SatisfiesProp1_6Condition`, `S.erase i` is also
a minimal-prime set (`closedGraph_cutVertex_preserved_of_erase`). The IH gives
`c(S.erase i) = |S|`. Combined with `c(S) ≤ |S| + 1`: `c(S) = |S| + 1`. -/
private theorem closedGraph_minimalPrime_componentCount_eq
    {n : ℕ} {G : SimpleGraph (Fin n)}
    (hConn : G.Connected) (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G)
    {S : Finset (Fin n)}
    (hSmin : primeComponent (K := K) G S ∈
      (binomialEdgeIdeal (K := K) G).minimalPrimes) :
    componentCount G S = S.card + 1 := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · -- S = ∅: c(∅) = 1 (connected) = 0 + 1
    rw [componentCount_empty, Finset.card_empty]
    haveI : Subsingleton G.ConnectedComponent :=
      hConn.preconnected.subsingleton_connectedComponent
    haveI : Nonempty G.ConnectedComponent := by
      obtain ⟨v⟩ := hConn.nonempty
      exact ⟨G.connectedComponentMk v⟩
    exact Nat.card_unique
  · -- S ≠ ∅: strong induction on |S|
    have hub := closedGraph_componentCount_le_card_add_one hClosed hConn S
    have hcv : ∀ i ∈ S, IsCutVertexRelative G S i := by
      have h39 := (corollary_3_9 (K := K) G S hConn).mp hSmin
      rcases h39 with rfl | h
      · exact absurd rfl (Finset.Nonempty.ne_empty hne)
      · exact h
    obtain ⟨i, hiS⟩ := hne
    have hcut_lt := (hcv i hiS).2  -- c(S.erase i) < c(S)
    -- P_{S.erase i} is also a minimal prime (cut vertex preservation under Prop 1.6)
    have hmin_erase : primeComponent (K := K) G (S.erase i) ∈
        (binomialEdgeIdeal (K := K) G).minimalPrimes := by
      rw [corollary_3_9 (K := K) G (S.erase i) hConn]
      rcases (S.erase i).eq_empty_or_nonempty with heq | _
      · exact Or.inl heq
      · right; intro j hjSi
        exact closedGraph_cutVertex_preserved_of_erase hClosed hConn hCond S i j hjSi
          (hcv j (Finset.mem_of_mem_erase hjSi))
    -- IH on S.erase i
    have ih := closedGraph_minimalPrime_componentCount_eq hConn hClosed hCond hmin_erase
    have hcard_erase := Finset.card_erase_of_mem hiS
    -- ih: c(S.erase i) = (S.erase i).card + 1 = S.card
    -- hcut_lt: c(S.erase i) < c(S)
    -- hub: c(S) ≤ S.card + 1
    omega
  termination_by S.card
  decreasing_by exact Finset.card_erase_lt_of_mem hiS

/--
Direct equidimensional surrogate variant of Proposition 1.6:
if `G` is a connected closed graph satisfying the interval condition, then `S/J_G`
is equidimensional in the local BEI sense.

**Proof** (direct equidimensionality, not the paper's Gröbner degeneration route):

For every minimal prime `P_S` of `J_G`, the dimension formula gives
`dim(R/P_S) = n - |S| + c(S)`. By `closedGraph_minimalPrime_componentCount_eq`,
`c(S) = |S| + 1` for every minimal-prime set `S`, so `dim(R/P_S) = n + 1` uniformly.
Since all minimal primes have the same quotient dimension, the quotient ring is
equidimensional in the local surrogate sense.
-/
theorem prop_1_6_equidim (n : ℕ) (_hn : 0 < n) (G : SimpleGraph (Fin n))
    (hConn : G.Connected)
    (hClosed : IsClosedGraph G)
    (hCond : SatisfiesProp1_6Condition n G) :
    IsEquidim
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal G) := by
  apply isEquidim_of_equidim_minimalPrimes
  intro P Q hP hQ
  have hP' := hP; have hQ' := hQ
  rw [minimalPrimes_characterization G] at hP' hQ'
  obtain ⟨SP, rfl, _⟩ := hP'; obtain ⟨SQ, rfl, _⟩ := hQ'
  rw [ringKrullDim_quot_primeComponent, ringKrullDim_quot_primeComponent]
  congr 1
  have hP_eq :=
    closedGraph_minimalPrime_componentCount_eq (K := K) hConn hClosed hCond hP
  have hQ_eq :=
    closedGraph_minimalPrime_componentCount_eq (K := K) hConn hClosed hCond hQ
  have hSP : SP.card ≤ Fintype.card (Fin n) :=
    SP.card_le_univ.trans (by simp)
  have hSQ : SQ.card ≤ Fintype.card (Fin n) :=
    SQ.card_le_univ.trans (by simp)
  omega


end

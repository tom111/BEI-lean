import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import BEI.Equidim.Transport
import BEI.Equidim.ClosedGraphIntervals
import BEI.Equidim.IteratedRegularity
import BEI.Equidim.AugmentationLocalCM
import BEI.Equidim.GlobalCMSetup
import BEI.PrimeIdeals
import BEI.GraphProperties
import BEI.ClosedGraphs
import BEI.ReducedHH
import toMathlib.Equidim.Defs
import toMathlib.SquarefreeMonomialPrimes
import toMathlib.HeightVariableIdeal
import toMathlib.QuotientDimension
import toMathlib.IdealQuotientHelpers
import toMathlib.MinimalPrimesRegular
import toMathlib.MvPolynomialHomogeneous
import toMathlib.CohenMacaulay.Defs
import toMathlib.CohenMacaulay.Basic
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.TensorPolynomialAway
import toMathlib.PolynomialAwayTensor
import toMathlib.TensorLocalisation
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.MvPolynomial

variable {K : Type*} [Field K]

noncomputable section

open MvPolynomial SimpleGraph IsLocalRing

/-!
# Equidimensional surrogate: F2 route scaffolding

This file isolates the F2-route scaffolding for the global Cohen-Macaulay
proof: the unit-set / neighbourhood / survivors definitions, the one-sided
survivor isolation lemma (Lemma 3), the paired-survivor / smaller HH graph
infrastructure, and the restricted-ring setup over the survivor set `W`.

## Reference: Herzog et al. (2010), proof of Proposition 1.6
-/

/-! #### F2 route scaffolding: unit set, neighborhood, survivors -/

/-- Neighborhood of `U` in the HH bipartite graph (undirected). -/
def hhNbhd {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Set (BinomialEdgeVars (Fin n)) :=
  { w | ∃ u ∈ U, (u, w) ∈ hhEdgeSet G ∨ (w, u) ∈ hhEdgeSet G }

/-- `U` is independent in the HH bipartite graph. -/
def hhIndep {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Prop :=
  ∀ ⦃u v⦄, u ∈ U → v ∈ U → (u, v) ∉ hhEdgeSet G

/-- Survivor set: vertices neither in `U` nor adjacent to `U`. -/
def hhSurvivors {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Set (BinomialEdgeVars (Fin n)) :=
  (U ∪ hhNbhd G U)ᶜ

/-! #### Lemma 3 — one-sided survivors are isolated in `Γ_W` -/

/-- **Lemma 3 (x-case)**: Under HH conditions, if `x_i` is a survivor but `y_i` is not,
then every HH-neighbor of `x_i` is outside the survivor set. -/
lemma hhSurvivor_x_isolated {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))}
    {i : Fin n}
    (hxi : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hyi : (Sum.inr i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U)
    {j : Fin n} (hedge : (Sum.inl i, Sum.inr j) ∈ hhEdgeSet G) :
    (Sum.inr j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
  -- Unpack the edge data
  obtain ⟨i', j', hj', hadj_ij, hij, heq⟩ := hedge
  rw [Prod.mk.injEq] at heq
  obtain ⟨hil, hir⟩ := heq
  have hii' : i = i' := Sum.inl.inj hil
  have hjj' : j = j' := Sum.inr.inj hir
  subst hii'; subst hjj'
  -- Diagonal edge at i exists: hedge forces i.val + 1 < n
  have hi_succ : i.val + 1 < n := by
    have : i.val + 1 ≤ j.val + 1 := by exact_mod_cast Nat.succ_le_succ hij
    omega
  -- hyi: inr i ∉ (U ∪ N)ᶜ, so inr i ∈ U ∪ N
  have hy_in : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ U ∪ hhNbhd G U := by
    by_contra h; exact hyi h
  -- Case analysis on how inr i fails to be a survivor
  rcases hy_in with hy_U | hy_N
  · -- inr i ∈ U: the diagonal edge (inl i, inr i) forces inl i ∈ N(U), contradicting inl i ∈ W
    exfalso
    apply hxi
    refine Or.inr ⟨Sum.inr i, hy_U, Or.inr ?_⟩
    exact ⟨i, i, hi_succ, hHH.diagonal i hi_succ, le_refl i, rfl⟩
  · -- inr i ∈ N(U): choose u ∈ U adjacent to inr i.
    obtain ⟨u, hu_U, hu_adj⟩ := hy_N
    rcases hu_adj with he1 | he2
    · -- (u, inr i) ∈ hhEdgeSet: u = Sum.inl a, and the edge is (inl a, inr i)
      obtain ⟨a, i'', hi_succ', hadj_ai, h_ai, heq_ai⟩ := he1
      have hu_eq : u = Sum.inl a := (Prod.mk.inj heq_ai).1
      have hi_eq : i = i'' := Sum.inr.inj (Prod.mk.inj heq_ai).2
      subst hi_eq
      -- a ≤ i; a ≠ i because inl a ∈ U and inl i ∈ W
      have ha_ne_i : a ≠ i := by
        rintro rfl
        apply hxi
        exact Or.inl (hu_eq ▸ hu_U)
      have ha_lt_i : a < i := lt_of_le_of_ne h_ai ha_ne_i
      -- Split on whether j = i
      by_cases hji : j = i
      · rw [hji]; exact hyi
      · have hi_lt_j : i < j := lt_of_le_of_ne hij (Ne.symm hji)
        -- HH transitivity on a < i < j
        have hadj_aj : G.Adj a ⟨j.val + 1, hj'⟩ :=
          hHH.transitivity a i j hi_succ' hj' ha_lt_i hi_lt_j hadj_ai hadj_ij
        -- Therefore (inl a, inr j) ∈ hhEdgeSet, so inr j ∈ N(U) via u = inl a
        intro hj_W
        apply hj_W
        refine Or.inr ⟨Sum.inl a, hu_eq ▸ hu_U, Or.inl ?_⟩
        refine ⟨a, j, hj', hadj_aj, ?_, rfl⟩
        exact le_of_lt (lt_of_lt_of_le ha_lt_i hij)
    · -- (inr i, u) ∈ hhEdgeSet: impossible since edges are (inl _, inr _)
      exfalso
      obtain ⟨i'', j'', _, _, _, heq_bad⟩ := he2
      exact Sum.inl_ne_inr ((Prod.mk.inj heq_bad).1.symm)

/-- **Lemma 3 (y-case)**: symmetric to the x-case. If `y_i` is a survivor but `x_i` is not,
then every HH-neighbor of `y_i` is outside the survivor set. -/
lemma hhSurvivor_y_isolated {n : ℕ} {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    {U : Set (BinomialEdgeVars (Fin n))}
    {i : Fin n}
    (hyi : (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)
    (hxi : (Sum.inl i : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U)
    {j : Fin n} (hedge : (Sum.inl j, Sum.inr i) ∈ hhEdgeSet G) :
    (Sum.inl j : BinomialEdgeVars (Fin n)) ∉ hhSurvivors G U := by
  obtain ⟨j', i', hi', hadj_ji, hji, heq⟩ := hedge
  rw [Prod.mk.injEq] at heq
  obtain ⟨hil, hir⟩ := heq
  have hjj' : j = j' := Sum.inl.inj hil
  have hii' : i = i' := Sum.inr.inj hir
  subst hjj'; subst hii'
  -- Diagonal edge at i exists (hedge needs i.val + 1 < n directly)
  -- hxi: inl i ∉ (U ∪ N)ᶜ, so inl i ∈ U ∪ N
  have hx_in : (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ U ∪ hhNbhd G U := by
    by_contra h; exact hxi h
  rcases hx_in with hx_U | hx_N
  · -- inl i ∈ U: diagonal (inl i, inr i) forces inr i ∈ N, contradicting inr i ∈ W
    exfalso
    apply hyi
    refine Or.inr ⟨Sum.inl i, hx_U, Or.inl ?_⟩
    exact ⟨i, i, hi', hHH.diagonal i hi', le_refl i, rfl⟩
  · -- inl i ∈ N(U): choose u ∈ U adjacent to inl i
    obtain ⟨u, hu_U, hu_adj⟩ := hx_N
    rcases hu_adj with he1 | he2
    · -- (u, inl i) ∈ hhEdgeSet: impossible (edges go inl → inr)
      exfalso
      obtain ⟨i'', j'', _, _, _, heq_bad⟩ := he1
      exact Sum.inl_ne_inr ((Prod.mk.inj heq_bad).2)
    · -- (inl i, u) ∈ hhEdgeSet: u = Sum.inr b, and the edge is (inl i, inr b)
      obtain ⟨i'', b, hb_succ, hadj_ib, h_ib, heq_ib⟩ := he2
      have hi_eq : i = i'' := Sum.inl.inj (Prod.mk.inj heq_ib).1
      have hu_eq : u = Sum.inr b := (Prod.mk.inj heq_ib).2
      subst hi_eq
      -- i ≤ b; b ≠ i because inr b ∈ U and inr i ∈ W
      have hb_ne_i : b ≠ i := by
        rintro rfl
        apply hyi
        exact Or.inl (hu_eq ▸ hu_U)
      have hi_lt_b : i < b := lt_of_le_of_ne h_ib (Ne.symm hb_ne_i)
      -- Split on whether j = i
      by_cases hji_eq : j = i
      · rw [hji_eq]; exact hxi
      · have hj_lt_i : j < i := lt_of_le_of_ne hji hji_eq
        -- HH transitivity on j < i < b
        have hadj_jb : G.Adj j ⟨b.val + 1, hb_succ⟩ :=
          hHH.transitivity j i b hi' hb_succ hj_lt_i hi_lt_b hadj_ji hadj_ib
        -- Therefore (inl j, inr b) ∈ hhEdgeSet, so inl j ∈ N(U) via u = inr b
        intro hj_W
        apply hj_W
        refine Or.inr ⟨Sum.inr b, hu_eq ▸ hu_U, Or.inr ?_⟩
        refine ⟨j, b, hb_succ, hadj_jb, ?_, rfl⟩
        exact le_of_lt (lt_of_lt_of_le hj_lt_i h_ib)

/-! #### Step 2/3: paired survivors, smaller HH graph, restricted ring -/

/-- The paired-survivor index set `C`: indices `i : Fin n` with `i.val + 1 < n`
and both `inl i` and `inr i` in `hhSurvivors G U`.

These are the indices on which a fresh pair of variables `(x'_a, y'_a)` will
sit in the reduced HH ring `A^red_{G'}`. -/
noncomputable def pairedSurvivors {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : Finset (Fin n) := by
  classical
  exact (Finset.univ : Finset (Fin n)).filter
    (fun i => i.val + 1 < n ∧
      (Sum.inl i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U ∧
      (Sum.inr i : BinomialEdgeVars (Fin n)) ∈ hhSurvivors G U)

/-- The size `r = |C|` of the paired-survivor set. -/
noncomputable abbrev pairedCount {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) : ℕ :=
  (pairedSurvivors G U).card

/-- The order-preserving embedding `Fin r ↪o Fin n` from the paired-survivor
set, using `Finset.orderEmbOfFin`. -/
noncomputable def pairedSurvivorsEmb {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) :
    Fin (pairedCount G U) ↪o Fin n :=
  (pairedSurvivors G U).orderEmbOfFin rfl

/-- The `a`-th paired-survivor index `c_a : Fin n`. -/
noncomputable abbrev pairedSurvivorsVal {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) : Fin n :=
  pairedSurvivorsEmb G U a

/-- `pairedSurvivorsVal G U a` is indeed a paired-survivor element. -/
theorem pairedSurvivorsVal_mem {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) :
    pairedSurvivorsVal G U a ∈ pairedSurvivors G U :=
  Finset.orderEmbOfFin_mem _ _ a

/-- Unpacks `pairedSurvivorsVal_mem` into the three component facts. -/
private theorem pairedSurvivorsVal_spec {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (a : Fin (pairedCount G U)) :
    (pairedSurvivorsVal G U a).val + 1 < n ∧
    (Sum.inl (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G U ∧
    (Sum.inr (pairedSurvivorsVal G U a) : BinomialEdgeVars (Fin n)) ∈
      hhSurvivors G U := by
  have h := pairedSurvivorsVal_mem G U a
  classical
  unfold pairedSurvivors at h
  rw [Finset.mem_filter] at h
  exact h.2

/-- The auxiliary "HH-edge in the smaller graph" relation, encoded one-sidedly
so that `smallerHHGraph := SimpleGraph.fromRel smallerHHRel` has HH-shaped
edges after symmetrisation. -/
private noncomputable def smallerHHRel {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n)))
    (u v : Fin (pairedCount G U + 1)) : Prop :=
  ∃ (a b : Fin (pairedCount G U)),
    a ≤ b ∧
    u = a.castSucc ∧
    v.val = b.val + 1 ∧
    ∃ (hc : (pairedSurvivorsVal G U b).val + 1 < n),
      G.Adj (pairedSurvivorsVal G U a)
        ⟨(pairedSurvivorsVal G U b).val + 1, hc⟩

/-- The smaller HH graph `G'` on `Fin (r + 1)` associated to `(G, U)`. Edges
come from the HH edges of `G` restricted to paired-survivor indices. -/
noncomputable def smallerHHGraph {n : ℕ}
    (G : SimpleGraph (Fin n)) (U : Set (BinomialEdgeVars (Fin n))) :
    SimpleGraph (Fin (pairedCount G U + 1)) :=
  SimpleGraph.fromRel (smallerHHRel G U)

/-- The smaller HH graph inherits the HH conditions from the original. -/
theorem smallerHHGraph_herzogHibi {n : ℕ}
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    (U : Set (BinomialEdgeVars (Fin n))) :
    HerzogHibiConditions (pairedCount G U + 1) (smallerHHGraph G U) := by
  refine ⟨?_, ?_⟩
  · -- Diagonal: for i : Fin (r + 1) with i.val + 1 < r + 1,
    --   G'.Adj i ⟨i.val + 1, _⟩.
    intro i hi
    -- i.val < r, so i = (⟨i.val, _⟩ : Fin r).castSucc.
    have hi_lt : i.val < pairedCount G U := by omega
    set a : Fin (pairedCount G U) := ⟨i.val, hi_lt⟩ with ha_def
    -- Diagonal at c_a : Fin n.
    have hc_succ : (pairedSurvivorsVal G U a).val + 1 < n :=
      (pairedSurvivorsVal_spec G U a).1
    have hadj : G.Adj (pairedSurvivorsVal G U a)
        ⟨(pairedSurvivorsVal G U a).val + 1, hc_succ⟩ :=
      hHH.diagonal _ hc_succ
    -- Package as smallerHHRel with a = b.
    rw [smallerHHGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨a, a, le_refl a, ?_, ?_, hc_succ, hadj⟩⟩
    · -- i ≠ ⟨i.val + 1, hi⟩
      intro heq
      have : i.val = i.val + 1 := congrArg Fin.val heq
      omega
    · -- i = a.castSucc
      apply Fin.ext
      simp [a, Fin.castSucc, Fin.castAdd, Fin.castLE]
    · -- (⟨i.val + 1, hi⟩ : Fin (r+1)).val = a.val + 1
      simp [a]
  · -- Transitivity.
    intro i j k hj hk hij hjk hadj1 hadj2
    -- Unpack G'.Adj i ⟨j.val + 1, hj⟩.
    rw [smallerHHGraph, SimpleGraph.fromRel_adj] at hadj1 hadj2
    obtain ⟨_, hrel1⟩ := hadj1
    obtain ⟨_, hrel2⟩ := hadj2
    -- smallerHHRel is one-sided: u = castSucc a, v.val = b.val + 1. The reverse
    -- direction is impossible because castSucc has val < r while b.val + 1 is
    -- something's +1. We match the forward direction in each case.
    -- First hadj1: pick the Or-branch that matches the shape (i = castSucc a,
    -- ⟨j.val + 1, hj⟩ = ... b.val + 1). Since j.val + 1 = b.val + 1 forces
    -- j.val = b.val, consistent with the forward branch.
    have hrel1_fwd : smallerHHRel G U i ⟨j.val + 1, hj⟩ := by
      rcases hrel1 with h | h
      · exact h
      · -- reverse: smallerHHRel G U ⟨j.val+1, hj⟩ i
        -- Then ⟨j.val+1, hj⟩ = a.castSucc for some a, so j.val + 1 = a.val < r.
        -- That's fine numerically; but then i.val = b.val + 1, and we want
        -- i to be an a.castSucc in the forward direction. Extract the data
        -- and swap into the forward shape.
        -- We actually do NOT need to swap: the forward shape is what we need.
        -- So match the data: u = ⟨j.val+1, hj⟩, v = i.
        obtain ⟨a, b, hab, hu_eq, hv_eq, hc, hadj⟩ := h
        -- u.val = a.val, and also u.val = j.val + 1, so a.val = j.val + 1.
        have hav : a.val = j.val + 1 := by
          have := congrArg Fin.val hu_eq
          simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
          omega
        -- i.val = b.val + 1 from hv_eq.
        -- But i < j < k in Fin (r+1) means i.val < j.val. And i.val = b.val + 1,
        -- a.val = j.val + 1 with a ≤ b. So j.val + 1 ≤ b.val, hence
        -- i.val = b.val + 1 ≥ j.val + 2 > j.val, contradicting i < j.
        have : j.val + 1 ≤ b.val := hav ▸ hab
        have hi_val : i.val = b.val + 1 := hv_eq
        have : i.val > j.val := by omega
        exact absurd hij (not_lt.mpr (le_of_lt (Fin.lt_def.mpr this)))
    have hrel2_fwd : smallerHHRel G U j ⟨k.val + 1, hk⟩ := by
      rcases hrel2 with h | h
      · exact h
      · obtain ⟨a, b, hab, hu_eq, hv_eq, hc, hadj⟩ := h
        have hav : a.val = k.val + 1 := by
          have := congrArg Fin.val hu_eq
          simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at this
          omega
        have : k.val + 1 ≤ b.val := hav ▸ hab
        have hj_val : j.val = b.val + 1 := hv_eq
        have : j.val > k.val := by omega
        exact absurd hjk (not_lt.mpr (le_of_lt (Fin.lt_def.mpr this)))
    -- Now unpack the forward relations and apply HH.transitivity on G.
    obtain ⟨a₁, b₁, hab₁, hu₁, hv₁, hc₁, hadj₁⟩ := hrel1_fwd
    obtain ⟨a₂, b₂, hab₂, hu₂, hv₂, hc₂, hadj₂⟩ := hrel2_fwd
    -- From hu₁: i.val = a₁.val (via castSucc).
    have ha₁i : a₁.val = i.val := by
      have h1 := congrArg Fin.val hu₁
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at h1
      omega
    -- From hv₁: j.val + 1 = b₁.val + 1, so b₁.val = j.val.
    have hb₁j : b₁.val = j.val := by
      have h1 : (⟨j.val + 1, hj⟩ : Fin (pairedCount G U + 1)).val = b₁.val + 1 := hv₁
      simp at h1
      omega
    -- From hu₂: j.val = a₂.val.
    have ha₂j : a₂.val = j.val := by
      have h1 := congrArg Fin.val hu₂
      simp [Fin.castSucc, Fin.castAdd, Fin.castLE] at h1
      omega
    -- From hv₂: k.val = b₂.val.
    have hb₂k : b₂.val = k.val := by
      have h1 : (⟨k.val + 1, hk⟩ : Fin (pairedCount G U + 1)).val = b₂.val + 1 := hv₂
      simp at h1
      omega
    -- Instead of working with a₂ and b₁ separately, use b₁ as the middle index.
    -- a₂ = b₁ numerically.
    have ha₂_eq_b₁ : a₂ = b₁ := Fin.ext (by omega)
    -- i < j ⇒ a₁ < b₁ (a₁.val = i.val, b₁.val = j.val), so c_{a₁} < c_{b₁}.
    have ha₁_lt_b₁ : pairedSurvivorsVal G U a₁ < pairedSurvivorsVal G U b₁ := by
      have : a₁ < b₁ := Fin.lt_def.mpr (by rw [ha₁i, hb₁j]; exact Fin.lt_def.mp hij)
      exact (pairedSurvivorsEmb G U).strictMono this
    -- j < k ⇒ b₁ < b₂, so c_{b₁} < c_{b₂}.
    have hb₁_lt_b₂ : pairedSurvivorsVal G U b₁ < pairedSurvivorsVal G U b₂ := by
      have : b₁ < b₂ := Fin.lt_def.mpr (by rw [hb₁j, hb₂k]; exact Fin.lt_def.mp hjk)
      exact (pairedSurvivorsEmb G U).strictMono this
    -- Transport hadj₂ so its first argument is c_{b₁} instead of c_{a₂}.
    have hadj₂' : G.Adj (pairedSurvivorsVal G U b₁)
        ⟨(pairedSurvivorsVal G U b₂).val + 1, hc₂⟩ := by
      have h := hadj₂
      rw [ha₂_eq_b₁] at h
      exact h
    -- Apply HH.transitivity on G at indices c_{a₁} < c_{b₁} < c_{b₂}.
    have hadj_G : G.Adj (pairedSurvivorsVal G U a₁)
        ⟨(pairedSurvivorsVal G U b₂).val + 1, hc₂⟩ :=
      hHH.transitivity _ _ _ hc₁ hc₂ ha₁_lt_b₁ hb₁_lt_b₂ hadj₁ hadj₂'
    -- Repackage as G'.Adj i ⟨k.val + 1, hk⟩.
    rw [smallerHHGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨a₁, b₂, ?_, hu₁, ?_, hc₂, hadj_G⟩⟩
    · -- i ≠ ⟨k.val + 1, hk⟩: since i < j < k, i.val < k.val < k.val + 1.
      intro heq
      have : i.val = k.val + 1 := congrArg Fin.val heq
      have hi_lt_k : i.val < k.val := lt_trans (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
      omega
    · -- a₁ ≤ b₂: a₁.val = i.val < k.val = b₂.val via i < j < k.
      have : a₁.val < b₂.val := by
        rw [ha₁i, hb₂k]
        exact lt_trans (Fin.lt_def.mp hij) (Fin.lt_def.mp hjk)
      exact le_of_lt (Fin.lt_def.mpr this)
    · -- (⟨k.val + 1, hk⟩ : Fin (r+1)).val = b₂.val + 1, since b₂.val = k.val.
      simp [hb₂k]

/-! #### Step 3 — restricted ring over `W`

For any `W : Set (BinomialEdgeVars (Fin n))`, we view `MvPolynomial W K` as
the polynomial ring over the subtype `{v // v ∈ W}`, and the restricted edge
set picks the HH edges whose both endpoints lie in `W`. -/

/-- The HH edge set restricted to edges with both endpoints in `W`. -/
private def hhEdgeSetRestrict {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) :
    Set (BinomialEdgeVars (Fin n) × BinomialEdgeVars (Fin n)) :=
  { e | e ∈ hhEdgeSet G ∧ e.1 ∈ W ∧ e.2 ∈ W }

/-- `K[W]`: the polynomial ring over the subtype `{v // v ∈ W}`. -/
abbrev polyRestrict {n : ℕ} (W : Set (BinomialEdgeVars (Fin n))) :
    Type _ :=
  MvPolynomial W K

/-- The restricted edge set transported to pairs of elements of `W`. -/
def restrictedEdgesSubtype {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) :
    Set (W × W) :=
  { e | (e.1.val, e.2.val) ∈ hhEdgeSet G }

/-- The restricted edge ideal inside `K[W]`. -/
def restrictedEdgeIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) :
    Ideal (polyRestrict (K := K) W) :=
  MvPolynomial.variablePairIdeal (R := K) (restrictedEdgesSubtype G W)

/-- The `Λ` set: survivors not in the paired-survivor pairs.

`Λ = W \ ({inl i : i ∈ C} ∪ {inr i : i ∈ C})`, where
`W = hhSurvivors G U` and `C = pairedSurvivors G U`. -/
def lambdaSet {n : ℕ} (G : SimpleGraph (Fin n))
    (U : Set (BinomialEdgeVars (Fin n))) :
    Set (BinomialEdgeVars (Fin n)) :=
  hhSurvivors G U \
    (((pairedSurvivors G U : Finset (Fin n)) : Set (Fin n)).image
        (fun i => (Sum.inl i : BinomialEdgeVars (Fin n))) ∪
     ((pairedSurvivors G U : Finset (Fin n)) : Set (Fin n)).image Sum.inr)

/-- The restricted HH ring `K[W] / I(Γ_G|_W)`. -/
abbrev restrictedHHRing {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Set (BinomialEdgeVars (Fin n))) : Type _ :=
  polyRestrict (K := K) W ⧸ restrictedEdgeIdeal (K := K) G W


end

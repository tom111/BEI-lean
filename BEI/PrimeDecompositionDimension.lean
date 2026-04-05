import BEI.PrimeDecomposition
import BEI.MinimalPrimes
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import toMathlib.QuotientDimension

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Dimension of quotients by prime components (Corollary 3.3)

This file computes `ringKrullDim (R ⧸ P_S(G))` and derives the dimension formula:
  `dim(K[x,y]/J_G) = max_{S ⊆ V} (|V| - |S| + c(S))`

## Main results

- `ringKrullDim_quot_primeComponent`: `dim(R/P_S) = |V| - |S| + c(S)`
- `corollary_3_3`: the dimension formula
- `corollary_3_3_lower_bound`: `dim ≥ |V| + c(G)`

## Reference: Herzog et al. (2010), Corollary 3.3
-/

noncomputable section

open MvPolynomial SimpleGraph Classical

/-! ## Corollary 3.3: Dimension formula -/

/-!
### Corollary 3.3: Dimension formula

**Corollary 3.3** (Herzog et al. 2010):
  `dim(K[x,y]/J_G) = max_{S ⊆ V} (|V| - |S| + c(S))`

The formal proof proceeds in two layers:

1. compute `dim(R / P_S(G)) = |V| - |S| + c(S)` for each prime component;
2. combine this with Theorem 3.2 and radicality of `J_G` to assemble the formula
   for `R / J_G`.

The lower-bound theorem `corollary_3_3_lower_bound` is then obtained by evaluating
the maximum at `S = ∅`.

Reference: Herzog et al. (2010), Corollary 3.3.
-/

/-- Upper bound: `dim(R/P_S) ≤ |V| - |S| + c(S)`.
Any chain of primes above P_S has length ≤ dim(R) - height(P_S). -/
theorem ringKrullDim_quot_primeComponent_le (G : SimpleGraph V) (S : Finset V) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) ≤
    (Fintype.card V - S.card + componentCount G S : ℕ) := by
  haveI hP := primeComponent_isPrime (K := K) G S
  set P := primeComponent (K := K) G S
  set p : PrimeSpectrum (MvPolynomial (BinomialEdgeVars V) K) := ⟨P, hP⟩
  set n := Fintype.card V
  set s := S.card
  set cS := componentCount G S
  -- dim(R/P) = coheight(p)
  have hdim_quot : ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ↑(Order.coheight p) := by
    rw [ringKrullDim_quotient]
    have : PrimeSpectrum.zeroLocus (P : Set (MvPolynomial (BinomialEdgeVars V) K)) =
        Set.Ici p := Set.ext fun _ => Iff.rfl
    rw [this, Order.coheight_eq_krullDim_Ici]
  -- height(p) = s + (n - cS)
  have hht : Order.height p = (s + (n - cS) : ℕ) := by
    change Ideal.primeHeight P = _
    rw [← Ideal.height_eq_primeHeight]; exact lemma_3_1 G S
  -- ringKrullDim R = 2n (as WithBot ℕ∞)
  have hdim : ringKrullDim (MvPolynomial (BinomialEdgeVars V) K) = (2 * n : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field K, zero_add]
    simp only [BinomialEdgeVars, Nat.card_eq_fintype_card, Fintype.card_sum]
    norm_cast; ring
  -- height + coheight ≤ 2n (in ℕ∞)
  set R := MvPolynomial (BinomialEdgeVars V) K
  have h_add_le : Order.height p + Order.coheight p ≤ (2 * n : ℕ∞) := by
    set f : PrimeSpectrum R → ℕ∞ := fun a => Order.height a + Order.coheight a
    have h1 : f p ≤ ⨆ a, f a := le_ciSup (OrderTop.bddAbove _) p
    have h2 : ↑(⨆ a, f a) = ringKrullDim R :=
      (Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
        (α := PrimeSpectrum R)).symm
    have h3 : (⨆ a, f a : ℕ∞) ≤ (2 * n : ℕ∞) := by
      rw [← WithBot.coe_le_coe, h2, hdim]; norm_cast
    exact h1.trans h3
  -- coheight p ≤ n - s + cS
  have hs_le : s ≤ n := Finset.card_le_univ S
  have hcS_le : cS ≤ n :=
    (Nat.card_le_card_of_surjective _ Quot.mk_surjective).trans
      (by rw [Nat.card_eq_fintype_card]; exact Fintype.card_subtype_le _)
  rw [hht] at h_add_le
  have hcoht : Order.coheight p ≤ (n - s + cS : ℕ) := by
    -- From h_add_le: ↑(s + (n - cS)) + coheight p ≤ 2 * ↑n
    -- We want: coheight p ≤ ↑(n - s + cS)
    -- Key arithmetic: s + (n - cS) + (n - s + cS) = 2 * n
    suffices hsuff : ↑(s + (n - cS)) + Order.coheight p ≤ ↑(s + (n - cS)) + ↑(n - s + cS) by
      exact (ENat.add_le_add_iff_left (ENat.coe_ne_top _)).mp hsuff
    calc ↑(s + (n - cS)) + Order.coheight p
        ≤ 2 * ↑n := h_add_le
      _ = ↑(2 * n) := by push_cast; ring
      _ = ↑(s + (n - cS) + (n - s + cS)) := by norm_cast; omega
      _ = ↑(s + (n - cS)) + ↑(n - s + cS) := by push_cast; ring
  -- Combine: dim(R/P) = coheight p ≤ n - s + cS
  rw [hdim_quot]
  exact WithBot.coe_le_coe.mpr hcoht

/-- Kill selected variables: compose `primeComponentMap` with an evaluation that
sends `X(inl v) ↦ 0` for `v ∈ Ux` and `X(inr v) ↦ 0` for `v ∈ Uy`.
The kernel is prime (codomain is `MvPolynomial`, a domain) and contains `P_S`. -/
noncomputable def dimChainMap (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) :
    MvPolynomial (BinomialEdgeVars V) K →ₐ[K]
    MvPolynomial (BinomialEdgeVars V) K :=
  (MvPolynomial.aeval (fun v : BinomialEdgeVars V =>
    match v with
    | Sum.inl j => if j ∈ Ux then 0 else X (Sum.inl j)
    | Sum.inr j => if j ∈ Uy then 0 else X (Sum.inr j))).comp
  (primeComponentMap G S)

/-- The kernel of `dimChainMap` is a prime ideal (codomain is a domain). -/
theorem dimChainMap_ker_isPrime (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) :
    (RingHom.ker (dimChainMap (K := K) G S Ux Uy).toRingHom).IsPrime :=
  RingHom.ker_isPrime _

/-- `P_S ≤ ker(dimChainMap)`: the kernel contains the prime component. -/
theorem primeComponent_le_dimChainMap_ker (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) :
    primeComponent (K := K) G S ≤
    RingHom.ker (dimChainMap (K := K) G S Ux Uy).toRingHom := by
  rw [primeComponent_eq_ker (K := K)]
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  change (dimChainMap (K := K) G S Ux Uy) f = 0
  simp only [dimChainMap, AlgHom.comp_apply]
  rw [show (primeComponentMap (K := K) G S) f = 0 from hf, map_zero]

/-- A "pure kill" map: sends `X(inl j) ↦ 0` for `j ∈ Ux`, `X(inr j) ↦ 0` for `j ∈ Uy`,
and leaves all other variables unchanged. -/
private noncomputable def pureKill (Ux Uy : Finset V) :
    MvPolynomial (BinomialEdgeVars V) K →ₐ[K]
    MvPolynomial (BinomialEdgeVars V) K :=
  MvPolynomial.aeval (fun v : BinomialEdgeVars V =>
    match v with
    | Sum.inl j => if j ∈ Ux then 0 else X (Sum.inl j)
    | Sum.inr j => if j ∈ Uy then 0 else X (Sum.inr j))

/-- `pureKill(Ux',Uy') = pureKill(Ux',Uy') ∘ pureKill(Ux,Uy)` when `Ux ⊆ Ux'`, `Uy ⊆ Uy'`. -/
private theorem pureKill_absorb {Ux Ux' Uy Uy' : Finset V}
    (hx : Ux ⊆ Ux') (hy : Uy ⊆ Uy') :
    pureKill (K := K) Ux' Uy' =
    (pureKill (K := K) Ux' Uy').comp (pureKill (K := K) Ux Uy) := by
  apply MvPolynomial.algHom_ext; intro w
  simp only [pureKill, AlgHom.comp_apply, MvPolynomial.aeval_X]
  cases w with
  | inl j =>
    by_cases h : j ∈ Ux
    · simp [h, map_zero, hx h]
    · by_cases h' : j ∈ Ux'
      · simp [h, MvPolynomial.aeval_X, h']
      · simp [h, MvPolynomial.aeval_X, h']
  | inr j =>
    by_cases h : j ∈ Uy
    · simp [h, map_zero, hy h]
    · by_cases h' : j ∈ Uy'
      · simp [h, MvPolynomial.aeval_X, h']
      · simp [h, MvPolynomial.aeval_X, h']

/-- Monotonicity: enlarging `Ux` or `Uy` grows the kernel of `dimChainMap`.
Uses: `dimChainMap(Ux',Uy') = pureKill(Ux',Uy') ∘ pcm = pureKill(Ux',Uy') ∘ pureKill(Ux,Uy) ∘ pcm
= pureKill(Ux',Uy') ∘ dimChainMap(Ux,Uy)`, then `f(x)=0 → g(f(x))=g(0)=0`. -/
theorem dimChainMap_ker_mono (G : SimpleGraph V) (S : Finset V)
    {Ux Ux' Uy Uy' : Finset V} (hx : Ux ⊆ Ux') (hy : Uy ⊆ Uy') :
    RingHom.ker (dimChainMap (K := K) G S Ux Uy).toRingHom ≤
    RingHom.ker (dimChainMap (K := K) G S Ux' Uy').toRingHom := by
  -- dimChainMap = pureKill ∘ primeComponentMap (by definition)
  -- pureKill(Ux',Uy') = pureKill(Ux',Uy') ∘ pureKill(Ux,Uy)  (by pureKill_absorb)
  -- So dimChainMap(Ux',Uy') = pureKill(Ux',Uy') ∘ dimChainMap(Ux,Uy)
  have hfact : dimChainMap (K := K) G S Ux' Uy' =
      (pureKill (K := K) Ux' Uy').comp (dimChainMap (K := K) G S Ux Uy) := by
    show (pureKill Ux' Uy').comp (primeComponentMap G S) =
      (pureKill Ux' Uy').comp ((pureKill Ux Uy).comp (primeComponentMap G S))
    rw [← AlgHom.comp_assoc, ← pureKill_absorb hx hy]
  intro f hf; rw [RingHom.mem_ker] at hf ⊢
  change (dimChainMap (K := K) G S Ux' Uy') f = 0
  rw [hfact, AlgHom.comp_apply,
      show (dimChainMap (K := K) G S Ux Uy) f = 0 from hf, map_zero]

/-! ### Strict inclusion witnesses for the chain -/

/-- Phase 1/3 witness: `X(inl v)` maps to 0 when `v ∉ S` and `v ∈ Ux`. -/
theorem dimChainMap_inl_eq_zero (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) (v : V) (hvS : v ∉ S) (hvUx : v ∈ Ux) :
    (dimChainMap (K := K) G S Ux Uy) (X (Sum.inl v)) = 0 := by
  simp only [dimChainMap, AlgHom.comp_apply, primeComponentMap, MvPolynomial.aeval_X,
    hvS, ↓reduceIte, hvUx]

/-- Phase 1/3 witness: `X(inl v)` maps to nonzero when `v ∉ S` and `v ∉ Ux`. -/
theorem dimChainMap_inl_ne_zero (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) (v : V) (hvS : v ∉ S) (hvUx : v ∉ Ux) :
    (dimChainMap (K := K) G S Ux Uy) (X (Sum.inl v)) ≠ 0 := by
  simp only [dimChainMap, AlgHom.comp_apply, primeComponentMap, MvPolynomial.aeval_X,
    hvS, ↓reduceIte, hvUx]
  exact MvPolynomial.X_ne_zero _

/-- Phase 2 witness: `X(inr v)` maps to 0 when `v ∉ S`, `compRep v = v`, and `v ∈ Uy`. -/
theorem dimChainMap_inr_rep_eq_zero (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) (v : V) (hvS : v ∉ S) (hvUy : v ∈ Uy)
    (hrep : compRep G S v = v) :
    (dimChainMap (K := K) G S Ux Uy) (X (Sum.inr v)) = 0 := by
  simp only [dimChainMap, AlgHom.comp_apply, primeComponentMap, MvPolynomial.aeval_X,
    hvS, ↓reduceIte, hrep, map_mul, hvUy, mul_zero]

/-- Phase 2 witness: `X(inr v)` maps to nonzero when `v ∉ S`, `compRep v = v`,
`v ∉ Ux`, and `v ∉ Uy`. -/
theorem dimChainMap_inr_rep_ne_zero (G : SimpleGraph V) (S : Finset V)
    (Ux Uy : Finset V) (v : V) (hvS : v ∉ S) (hvUx : v ∉ Ux) (hvUy : v ∉ Uy)
    (hrep : compRep G S v = v) :
    (dimChainMap (K := K) G S Ux Uy) (X (Sum.inr v)) ≠ 0 := by
  simp only [dimChainMap, AlgHom.comp_apply, primeComponentMap, MvPolynomial.aeval_X,
    hvS, ↓reduceIte, hrep, map_mul, hvUx, hvUy]
  exact mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)

/-- Lower bound: `dim(R/P_S) ≥ |V| - |S| + c(S)`.
Uses an explicit chain of primes (kernels of `dimChainMap` with increasing
variable kills) above P_S. See ANSWER_08 for the full strategy.  -/
theorem ringKrullDim_quot_primeComponent_ge (G : SimpleGraph V) (S : Finset V) :
    (Fintype.card V - S.card + componentCount G S : ℕ) ≤
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) := by
  -- Strategy: build a chain of prime ideals above P_S of length n - s + c.
  -- Each prime is ker(dimChainMap G S Ux Uy) for increasing (Ux, Uy).
  -- Three phases: (1) add nonReps to Ux, (2) add reps to Uy, (3) add reps to Ux.
  -- Track via coheight: each strict inclusion decreases coheight by ≥ 1.
  haveI hPS := primeComponent_isPrime (K := K) G S
  set P := primeComponent (K := K) G S
  set p : PrimeSpectrum (MvPolynomial (BinomialEdgeVars V) K) := ⟨P, hPS⟩
  -- dim(R/P) = coheight(p)
  have hdim_quot : ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ↑(Order.coheight p) := by
    rw [ringKrullDim_quotient]
    have : PrimeSpectrum.zeroLocus (P : Set (MvPolynomial (BinomialEdgeVars V) K)) =
        Set.Ici p := Set.ext fun _ => Iff.rfl
    rw [this, Order.coheight_eq_krullDim_Ici]
  rw [hdim_quot]
  -- Set up the finset partition
  set reps := Finset.univ.filter (fun v => v ∉ S ∧ compRep G S v = v)
  set nonReps := Finset.univ.filter (fun v => v ∉ S ∧ compRep G S v ≠ v)
  -- componentCount ≤ reps.card (injection from components to reps)
  -- reps.card ≤ componentCount (surjection from reps to components)
  -- Combined: reps.card = componentCount
  have hreps_eq : reps.card = componentCount G S := by
    apply le_antisymm
    · -- ≤: injection from reps to connected components
      set G' := G.induce {v : V | v ∉ S}
      unfold componentCount; rw [Nat.card_eq_fintype_card]
      let f : reps → G'.ConnectedComponent := fun ⟨v, hv⟩ =>
        G'.connectedComponentMk ⟨v, (Finset.mem_filter.mp hv).2.1⟩
      have hf_inj : Function.Injective f := by
        intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
        have h₁ := (Finset.mem_filter.mp hv₁).2
        have h₂ := (Finset.mem_filter.mp hv₂).2
        simp only [f] at heq
        have hreach := SimpleGraph.ConnectedComponent.exact heq
        have hsc := reachable_induce_imp_sameComponent G S hreach
        have hrep := compRep_eq_of_sameComponent G S hsc
        rw [h₁.2, h₂.2] at hrep; exact Subtype.ext hrep
      calc reps.card = Fintype.card reps := (Fintype.card_coe reps).symm
        _ ≤ Fintype.card G'.ConnectedComponent := Fintype.card_le_of_injective f hf_inj
    · -- ≥: Nat.card of components ≤ reps.card
      exact componentCount_le_fixedPoints G S
  have hpartition : nonReps.card + reps.card = Fintype.card V - S.card := by
    have hunion : nonReps ∪ reps = Finset.univ.filter (fun v : V => v ∉ S) := by
      ext v; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        nonReps, reps]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro h; by_cases heq : compRep G S v = v
        · exact Or.inr ⟨h, heq⟩
        · exact Or.inl ⟨h, heq⟩
    have hdisj : Disjoint nonReps reps := by
      rw [Finset.disjoint_filter]; intro v _ ⟨_, hne⟩ ⟨_, heq⟩; exact hne heq
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
    rw [show Finset.univ.filter (fun v : V => v ∉ S) = Sᶜ from by
      ext v; simp [Finset.mem_compl]]
    exact Finset.card_compl S
  -- The target becomes: N ≤ coheight p, where N = nonReps.card + 2 * reps.card
  have hN_eq : Fintype.card V - S.card + componentCount G S =
      nonReps.card + 2 * reps.card := by
    rw [← hreps_eq]; omega
  rw [hN_eq]
  -- ker(dimChainMap ∅ ∅) = P_S
  -- dimChainMap G S ∅ ∅ = pureKill ∅ ∅ ∘ primeComponentMap = id ∘ primeComponentMap
  have hdimChain_eq : (dimChainMap (K := K) G S ∅ ∅).toRingHom =
      (primeComponentMap (K := K) G S).toRingHom := by
    -- dimChainMap ∅ ∅ = pureKill ∅ ∅ ∘ pcm. And pureKill ∅ ∅ = id (no vars killed).
    suffices h : dimChainMap (K := K) G S ∅ ∅ = primeComponentMap (K := K) G S by
      rw [h]
    show (pureKill (K := K) ∅ ∅).comp (primeComponentMap G S) = primeComponentMap G S
    suffices hid : ∀ g : MvPolynomial (BinomialEdgeVars V) K,
        (pureKill (K := K) ∅ ∅) g = g by
      ext1 f; exact hid _
    intro g; induction g using MvPolynomial.induction_on with
    | C c => simp [pureKill, AlgHom.commutes]
    | add p q ihp ihq => simp [map_add, ihp, ihq]
    | mul_X p v ih =>
      simp only [map_mul, pureKill, MvPolynomial.aeval_X]
      cases v <;> simp [MvPolynomial.aeval_X]
      all_goals exact ih
  have hker_empty : RingHom.ker (dimChainMap (K := K) G S ∅ ∅).toRingHom = P := by
    show _ = primeComponent (K := K) G S
    rw [primeComponent_eq_ker (K := K), hdimChain_eq]
  -- Helper: PrimeSpectrum point from dimChainMap kernel
  set mk := fun (Ux Uy : Finset V) =>
    (⟨RingHom.ker (dimChainMap (K := K) G S Ux Uy).toRingHom,
      dimChainMap_ker_isPrime G S Ux Uy⟩ : PrimeSpectrum _)
  -- mk ∅ ∅ = p
  have hmk_empty : mk ∅ ∅ = p := PrimeSpectrum.ext hker_empty
  -- reps ∩ nonReps = ∅
  have reps_nonReps_disj : Disjoint reps nonReps := by
    rw [Finset.disjoint_filter]; intro v _ ⟨_, heq⟩ ⟨_, hne⟩; exact hne heq
  -- v ∈ reps → v ∉ nonReps
  have rep_not_nonRep : ∀ v ∈ reps, v ∉ nonReps := by
    intro v hv hnr; exact (Finset.mem_filter.mp hnr).2.2 (Finset.mem_filter.mp hv).2.2
  -- Phase 1: add nonReps to Ux (one at a time), Uy = ∅
  -- Track: coheight(mk F ∅) + F.card ≤ coheight(mk ∅ ∅) = coheight p
  have phase1 : ∀ F, F ⊆ nonReps →
      Order.coheight (mk F ∅) + F.card ≤ Order.coheight (mk ∅ ∅) := by
    intro F hF; induction F using Finset.induction with
    | empty => simp
    | @insert a F' haF' ihF =>
      have haF'Sub : F' ⊆ nonReps := (Finset.insert_subset_iff.mp hF).2
      have haInNonReps : a ∈ nonReps := hF (Finset.mem_insert_self a F')
      have haNotS : a ∉ S := (Finset.mem_filter.mp haInNonReps).2.1
      -- Strict inclusion: ker(F' ∅) < ker(insert a F' ∅)
      have hle : (mk F' ∅) ≤ (mk (insert a F') ∅) :=
        dimChainMap_ker_mono G S (Finset.subset_insert a F') (Finset.Subset.refl ∅)
      have hmem : X (Sum.inl a) ∈ (mk (insert a F') ∅).asIdeal := by
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact dimChainMap_inl_eq_zero G S (insert a F') ∅ a haNotS (Finset.mem_insert_self a F')
      have hnmem : X (Sum.inl a) ∉ (mk F' ∅).asIdeal := by
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact dimChainMap_inl_ne_zero G S F' ∅ a haNotS haF'
      have hlt : mk F' ∅ < mk (insert a F') ∅ := by
        exact lt_of_le_of_ne hle (fun heq => hnmem (heq ▸ hmem))
      rw [Finset.card_insert_of_notMem haF']
      calc Order.coheight (mk (insert a F') ∅) + (↑F'.card + 1)
          = (Order.coheight (mk (insert a F') ∅) + 1) + ↑F'.card := by ring
        _ ≤ Order.coheight (mk F' ∅) + ↑F'.card := by
            gcongr; exact Order.coheight_add_one_le hlt
        _ ≤ Order.coheight (mk ∅ ∅) := ihF haF'Sub
  -- Phase 2: add reps to Uy (one at a time), Ux = nonReps
  have phase2 : ∀ F, F ⊆ reps →
      Order.coheight (mk nonReps F) + (nonReps.card + F.card) ≤ Order.coheight (mk ∅ ∅) := by
    intro F hF; induction F using Finset.induction with
    | empty =>
      simp only [Finset.card_empty, Nat.cast_zero, add_zero]
      exact phase1 nonReps Finset.Subset.rfl
    | @insert a F' haF' ihF =>
      have haF'Sub : F' ⊆ reps := (Finset.insert_subset_iff.mp hF).2
      have haInReps : a ∈ reps := hF (Finset.mem_insert_self a F')
      have haNotS : a ∉ S := (Finset.mem_filter.mp haInReps).2.1
      have ha_rep : compRep G S a = a := (Finset.mem_filter.mp haInReps).2.2
      have haNotNonReps : a ∉ nonReps := rep_not_nonRep a haInReps
      -- Strict inclusion: ker(nonReps F' ) < ker(nonReps insert a F')
      have hle : mk nonReps F' ≤ mk nonReps (insert a F') :=
        dimChainMap_ker_mono G S (Finset.Subset.refl nonReps) (Finset.subset_insert a F')
      have hmem : X (Sum.inr a) ∈ (mk nonReps (insert a F')).asIdeal := by
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact dimChainMap_inr_rep_eq_zero G S nonReps (insert a F') a haNotS
          (Finset.mem_insert_self a F') ha_rep
      have hnmem : X (Sum.inr a) ∉ (mk nonReps F').asIdeal := by
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact dimChainMap_inr_rep_ne_zero G S nonReps F' a haNotS haNotNonReps haF' ha_rep
      have hlt : mk nonReps F' < mk nonReps (insert a F') := by
        exact lt_of_le_of_ne hle (fun heq => hnmem (heq ▸ hmem))
      rw [Finset.card_insert_of_notMem haF']
      calc Order.coheight (mk nonReps (insert a F')) + (↑nonReps.card + (↑F'.card + 1))
          = (Order.coheight (mk nonReps (insert a F')) + 1) + (↑nonReps.card + ↑F'.card) := by
            ring
        _ ≤ Order.coheight (mk nonReps F') + (↑nonReps.card + ↑F'.card) := by
            gcongr; exact Order.coheight_add_one_le hlt
        _ ≤ Order.coheight (mk ∅ ∅) := ihF haF'Sub
  -- Phase 3: add reps to Ux (one at a time), Uy = reps, Ux starts at nonReps
  have phase3 : ∀ F, F ⊆ reps →
      Order.coheight (mk (nonReps ∪ F) reps) + (nonReps.card + reps.card + F.card) ≤
      Order.coheight (mk ∅ ∅) := by
    intro F hF; induction F using Finset.induction with
    | empty =>
      simp only [Finset.union_empty, Finset.card_empty, Nat.cast_zero, add_zero]
      exact phase2 reps Finset.Subset.rfl
    | @insert a F' haF' ihF =>
      have haF'Sub : F' ⊆ reps := (Finset.insert_subset_iff.mp hF).2
      have haInReps : a ∈ reps := hF (Finset.mem_insert_self a F')
      have haNotS : a ∉ S := (Finset.mem_filter.mp haInReps).2.1
      have haNotNonReps : a ∉ nonReps := rep_not_nonRep a haInReps
      -- a ∉ nonReps ∪ F'
      have haNotUx : a ∉ nonReps ∪ F' := by
        rw [Finset.mem_union, not_or]; exact ⟨haNotNonReps, haF'⟩
      -- insert a (nonReps ∪ F') = nonReps ∪ insert a F'
      have hinsert_eq : insert a (nonReps ∪ F') = nonReps ∪ insert a F' := by
        ext v; simp only [Finset.mem_insert, Finset.mem_union]; tauto
      -- Strict inclusion
      have hle : mk (nonReps ∪ F') reps ≤ mk (nonReps ∪ insert a F') reps :=
        dimChainMap_ker_mono G S (Finset.union_subset_union_right
          (Finset.subset_insert a F')) (Finset.Subset.refl reps)
      have hmem : X (Sum.inl a) ∈ (mk (nonReps ∪ insert a F') reps).asIdeal := by
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact dimChainMap_inl_eq_zero G S (nonReps ∪ insert a F') reps a haNotS
          (Finset.mem_union_right nonReps (Finset.mem_insert_self a F'))
      have hnmem : X (Sum.inl a) ∉ (mk (nonReps ∪ F') reps).asIdeal := by
        rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
        exact dimChainMap_inl_ne_zero G S (nonReps ∪ F') reps a haNotS haNotUx
      have hlt : mk (nonReps ∪ F') reps < mk (nonReps ∪ insert a F') reps := by
        exact lt_of_le_of_ne hle (fun heq => hnmem (heq ▸ hmem))
      rw [Finset.card_insert_of_notMem haF']
      calc Order.coheight (mk (nonReps ∪ insert a F') reps) +
              (↑nonReps.card + ↑reps.card + (↑F'.card + 1))
          = (Order.coheight (mk (nonReps ∪ insert a F') reps) + 1) +
              (↑nonReps.card + ↑reps.card + ↑F'.card) := by ring
        _ ≤ Order.coheight (mk (nonReps ∪ F') reps) +
              (↑nonReps.card + ↑reps.card + ↑F'.card) := by
            gcongr; exact Order.coheight_add_one_le hlt
        _ ≤ Order.coheight (mk ∅ ∅) := ihF haF'Sub
  -- Combine: phase3 with F = reps gives the bound
  have hfinal := phase3 reps Finset.Subset.rfl
  rw [hmk_empty] at hfinal
  -- coheight(mk (nonReps ∪ reps) reps) + (nonReps.card + 2 * reps.card) ≤ coheight p
  -- so nonReps.card + 2 * reps.card ≤ coheight p
  suffices h : (nonReps.card + 2 * reps.card : ℕ∞) ≤ Order.coheight p by
    rw [show (↑(nonReps.card + 2 * reps.card) : WithBot ℕ∞) = ↑((nonReps.card + 2 * reps.card : ℕ∞))
      from by push_cast; norm_cast]
    exact WithBot.coe_le_coe.mpr h
  calc (↑nonReps.card + 2 * ↑reps.card : ℕ∞)
      = 0 + (↑nonReps.card + ↑reps.card + ↑reps.card) := by ring
    _ ≤ Order.coheight (mk (nonReps ∪ reps) reps) +
          (↑nonReps.card + ↑reps.card + ↑reps.card) := by gcongr; exact zero_le _
    _ ≤ Order.coheight p := hfinal

/-- The dimension of the quotient by a prime component. This is the key sub-theorem
for Corollary 3.3. -/
theorem ringKrullDim_quot_primeComponent (G : SimpleGraph V) (S : Finset V) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) =
    (Fintype.card V - S.card + componentCount G S : ℕ) :=
  le_antisymm (ringKrullDim_quot_primeComponent_le G S)
    (ringKrullDim_quot_primeComponent_ge G S)

theorem corollary_3_3 (G : SimpleGraph V) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    ⨆ S : Finset V, (Fintype.card V - S.card + componentCount G S : ℕ) := by
  -- Step 1: dim(R/J_G) = sup over minimal primes P of dim(R/P)
  have hrad := corollary_2_2 (K := K) G
  rw [ringKrullDim_quotient_radical _ hrad]
  -- Intermediate: ⨆ minPrimes dim(R/P) = ⨆ S, dim(R/P_S)
  -- (because minimalPrimes ⊆ {P_S} and for each S, some minPrime ≤ P_S)
  have hkey : (⨆ P ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes,
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P)) =
    ⨆ S : Finset V,
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) := by
    apply le_antisymm
    · apply iSup₂_le; intro P hP
      rw [minimalPrimes_characterization] at hP
      obtain ⟨S, rfl, _⟩ := hP
      exact le_iSup (f := fun S => ringKrullDim
        (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S)) S
    · apply iSup_le; intro S
      haveI := primeComponent_isPrime (K := K) G S
      obtain ⟨P, hP, hPS⟩ := Ideal.exists_minimalPrimes_le
        (binomialEdgeIdeal_le_primeComponent (K := K) G S)
      exact le_trans (ringKrullDim_quotient_anti hPS)
        (le_iSup₂ (f := fun P (_ : P ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes) =>
          ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P)) P hP)
  rw [hkey]; simp_rw [ringKrullDim_quot_primeComponent]
  -- Goal: ⨆ S, (↑(f S) : WithBot ℕ∞) = ↑(⨆ S, f S : ℕ)
  -- Both achieve their max at the same S₀ for finite Finset V.
  set f := fun S : Finset V => Fintype.card V - S.card + componentCount G S
  obtain ⟨S₀, _, hS₀⟩ := Finset.exists_max_image Finset.univ f ⟨∅, Finset.mem_univ _⟩
  have hbdd : BddAbove (Set.range f) :=
    ⟨f S₀, by rintro _ ⟨S, rfl⟩; exact hS₀ S (Finset.mem_univ S)⟩
  -- ℕ-iSup = f S₀
  have hnat : ⨆ S, f S = f S₀ :=
    le_antisymm (ciSup_le (fun S => hS₀ S (Finset.mem_univ S))) (le_ciSup hbdd S₀)
  rw [hnat]
  -- Goal: ⨆ S, (↑(f S) : WithBot ℕ∞) = ↑(f S₀)
  apply le_antisymm
  · exact iSup_le (fun S => by exact_mod_cast hS₀ S (Finset.mem_univ S))
  · exact le_iSup (fun S => (↑(f S) : WithBot ℕ∞)) S₀

/--
`J_G` is contained in the ideal generated by all `x`-variables.
This holds because each generator `x_i y_j - x_j y_i ∈ (x_1,...,x_n)`.
-/
theorem binomialEdgeIdeal_le_span_inl (G : SimpleGraph V) :
    binomialEdgeIdeal (K := K) G ≤
    Ideal.span (Set.range (fun v : V => X (Sum.inl v) : V → MvPolynomial (BinomialEdgeVars V) K)) := by
  apply Ideal.span_le.mpr
  intro f hf
  obtain ⟨i, j, _, _, rfl⟩ := hf
  -- f = x_i * y_j - x_j * y_i ∈ (x_i, x_j) ⊆ (x_v : v ∈ V)
  apply Ideal.sub_mem
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨i, rfl⟩)
  · exact Ideal.mul_mem_right _ _
      (Ideal.subset_span ⟨j, rfl⟩)

/--
Lower bound: `dim(K[x,y]/J_G) ≥ |V| + c(G)`, where `c(G)` is the number of
connected components of G (taking S = ∅).

**Proof strategy:** Construct a chain of `n + c` primes containing `J_G`:
```
  P_∅ < Q₁ < ... < Q_{c-1} < (x₁,...,xₙ) < (x₁,...,xₙ,y₁) < ... < m
```
where each `Q_k` replaces one component's complete-graph BEI with x-variable
generators. Primality of `Q_k` follows from: polynomial ring over a domain is a
domain (since each quotient R/Q_k ≅ D[y_v : v ∈ killed components] for a domain D).

**Blocker:** The chain construction requires showing primality of the intermediate
ideals Q_k, which needs the tensor product / polynomial-ring-over-domain argument
formalized for the specific structure of P_S(G).

Reference: Herzog et al. (2010), Corollary 3.3.
-/
theorem corollary_3_3_lower_bound (G : SimpleGraph V) :
    Fintype.card V + componentCount G ∅ ≤
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) := by
  -- Step 1: dim(R/J_G) ≥ dim(R/P_∅) by monotonicity (J_G ≤ P_∅)
  calc ↑(Fintype.card V + componentCount G ∅)
      ≤ ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G ∅) := by
        rw [ringKrullDim_quot_primeComponent]; simp
    _ ≤ ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) :=
        ringKrullDim_quotient_anti (binomialEdgeIdeal_le_primeComponent G ∅)

/-! ## Corollary 3.4: Cohen-Macaulay implies dimension equality -/

/--
**Corollary 3.4** (Herzog et al. 2010): If `K[x,y]/J_G` is Cohen-Macaulay, then
  `dim(K[x,y]/J_G) = |V| + c(G)`
where `c(G)` is the number of connected components of G.

Reference: Herzog et al. (2010), Corollary 3.4.
-/
theorem corollary_3_4 (G : SimpleGraph V)
    (hCM : IsCohenMacaulay (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G)) :
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) =
    Fintype.card V + componentCount G ∅ := by
  set J := binomialEdgeIdeal (K := K) G
  -- Step 1: CM equidimensionality → all minimal primes of J_G have equal dim(R/P)
  have hequal : ∀ P Q : Ideal (MvPolynomial (BinomialEdgeVars V) K),
      P ∈ J.minimalPrimes → Q ∈ J.minimalPrimes →
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ Q) := by
    intro P Q hP hQ
    rw [Ideal.minimalPrimes_eq_comap] at hP hQ
    obtain ⟨P', hP'min, rfl⟩ := hP
    obtain ⟨Q', hQ'min, rfl⟩ := hQ
    have hcm := hCM.equidimensional P' Q' hP'min hQ'min
    -- Third isomorphism: (R/J)/P' ≃+* R/(comap(mk J) P')
    have hiso := fun (X : Ideal (MvPolynomial (BinomialEdgeVars V) K ⧸ J)) =>
      (Ideal.quotEquivOfEq (Ideal.Quotient.factor_ker
        (Ideal.comap_mono (bot_le (a := X))))).symm.trans
      (RingHom.quotientKerEquivOfSurjective
        (Ideal.Quotient.factor_surjective (Ideal.comap_mono (bot_le (a := X)))))
    rw [ringKrullDim_eq_of_ringEquiv (hiso P').symm,
        ringKrullDim_eq_of_ringEquiv (hiso Q').symm, hcm]
  -- Step 2: dim(R/J_G) = |V| + c(G). By Cor 3.3 and equidimensionality.
  -- All minimal primes have dim = dim(R/P_∅) = |V| + c(G).
  sorry

/-! ## CM from equidimensional minimal primes -/

/-- Third isomorphism for quotient dimensions:
`dim((R/J)/P') = dim(R/(comap(mk J) P'))`. -/
private theorem ringKrullDim_quotQuot_eq
    (J : Ideal (MvPolynomial (BinomialEdgeVars V) K))
    (P' : Ideal (MvPolynomial (BinomialEdgeVars V) K ⧸ J)) :
    ringKrullDim ((MvPolynomial (BinomialEdgeVars V) K ⧸ J) ⧸ P') =
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸
      Ideal.comap (Ideal.Quotient.mk J) P') := by
  set Q := Ideal.comap (Ideal.Quotient.mk J) P'
  have hJQ : J ≤ Q := by
    intro x hx
    show Ideal.Quotient.mk J x ∈ P'
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P'.zero_mem
  have hmap_eq : Q.map (Ideal.Quotient.mk J) = P' :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P'
  rw [← hmap_eq]
  exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hJQ)

/-- If all `Ideal.minimalPrimes` of `J` have the same quotient dimension, then `R ⧸ J`
is Cohen–Macaulay (under the equidimensionality definition). -/
theorem isCohenMacaulay_of_equidim_minimalPrimes
    (J : Ideal (MvPolynomial (BinomialEdgeVars V) K))
    (hequal : ∀ P Q : Ideal (MvPolynomial (BinomialEdgeVars V) K),
      P ∈ J.minimalPrimes → Q ∈ J.minimalPrimes →
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ P) =
      ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ Q)) :
    IsCohenMacaulayRing (MvPolynomial (BinomialEdgeVars V) K ⧸ J) where
  equidimensional P' Q' hP'min hQ'min := by
    -- Convert: minimalPrimes (R/J) → J.minimalPrimes via comap
    have hP_mem : Ideal.comap (Ideal.Quotient.mk J) P' ∈ J.minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P', hP'min, rfl⟩
    have hQ_mem : Ideal.comap (Ideal.Quotient.mk J) Q' ∈ J.minimalPrimes := by
      rw [Ideal.minimalPrimes_eq_comap]; exact ⟨Q', hQ'min, rfl⟩
    rw [ringKrullDim_quotQuot_eq J P', ringKrullDim_quotQuot_eq J Q']
    exact hequal _ _ hP_mem hQ_mem

/-! ## Example 1.7(b): Path graph is CM -/

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
    -- The remaining sorry is cut-vertex preservation for path graphs (non-consecutive
    -- elements of S remain cut vertices after erasing one element).
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
        -- j ∈ S.erase i, so j ∈ S and j ≠ i
        -- j was a cut vertex relative to S; show it's a cut vertex relative to S.erase i
        -- This uses: in a path graph, if no two elements of S are adjacent,
        -- then removing i from S doesn't affect connectivity near j.
        sorry
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
**Example 1.7(b)** (Herzog et al. 2010): The path on `n` vertices (with natural ordering)
yields a Cohen–Macaulay quotient.

Proof: Every minimal prime `P_S` of `J_G` satisfies `dim(R/P_S) = n + 1`.
This is because for valid S (non-consecutive interior vertices), removing S from
the path creates |S| + 1 connected components, so `n - |S| + c(S) = n + 1`.
Since all minimal primes have equal quotient dimension, `R/J_G` is equidimensional = CM.
-/
theorem path_is_CM (n : ℕ) (G : SimpleGraph (Fin n))
    (hPath : ∀ (i j : Fin n),
      G.Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val)) :
    IsCohenMacaulay
      (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ binomialEdgeIdeal G) := by
  apply isCohenMacaulay_of_equidim_minimalPrimes
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

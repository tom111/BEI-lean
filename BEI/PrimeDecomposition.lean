import BEI.PrimeIdeals
import BEI.CohenMacaulay
import BEI.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import toMathlib.QuotientDimension

variable {K : Type*} [Field K]
variable {V : Type*} [LinearOrder V] [DecidableEq V] [Fintype V]

/-!
# Prime decomposition of J_G (Theorem 3.2) and dimension corollaries

This file formalizes:
- **Theorem 3.2**: `J_G = ⋂_{S ⊆ V} P_S(G)`
- **Corollary 3.3**: dimension formula `dim(S/J_G) = max_S (|V\S| + c(S))`
- **Corollary 3.4**: if S/J_G is Cohen-Macaulay then `dim = n + c`
- **Corollary 3.7**: cycle characterization

## Reference: Herzog et al. (2010), Theorem 3.2 and Section 3
-/

noncomputable section

open MvPolynomial SimpleGraph Classical

/-! ## Krull dimension -/
-- `ringKrullDim` is provided by Mathlib (via `Mathlib.RingTheory.Ideal.Height`),
-- returning `WithBot ℕ∞`. No local definition needed.

/-! ## Helper lemmas for Theorem 3.2 -/

/-- The binomial `x_a y_b - x_b y_a` lies in `J_G` whenever `G.Adj a b`. -/
private lemma bij_mem_binomialEdgeIdeal (G : SimpleGraph V) {a b : V} (hadj : G.Adj a b) :
    (x (K := K) a * y b - x b * y a) ∈ binomialEdgeIdeal G := by
  rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with h | h
  · exact Ideal.subset_span ⟨a, b, hadj, h, rfl⟩
  · have hgen : (x (K := K) b * y a - x a * y b) ∈ binomialEdgeIdeal G :=
      Ideal.subset_span ⟨b, a, hadj.symm, h, rfl⟩
    have h0 := (binomialEdgeIdeal (K := K) G).zero_mem
    have hsub := Ideal.sub_mem _ h0 hgen
    convert hsub using 1; ring

/-- x-telescope identity (inline, avoids importing HerzogLemmas). -/
private lemma x_telescope (a b c : V) :
    x (K := K) b * (x a * y c - x c * y a) =
    x a * (x b * y c - x c * y b) + x c * (x a * y b - x b * y a) := by
  simp only [x, y]; ring

/-- y-telescope identity (inline, avoids importing HerzogLemmas). -/
private lemma y_telescope (a b c : V) :
    y (K := K) b * (x a * y c - x c * y a) =
    y c * (x a * y b - x b * y a) + y a * (x b * y c - x c * y b) := by
  simp only [x, y]; ring

/-- **Telescope lemma**: if `P` is prime and contains `J_G`, and `S = {v : x_v ∈ P ∧ y_v ∈ P}`,
then for any pair `j, k` connected by a path in `G[V \ S]`, the binomial `x_j y_k − x_k y_j`
lies in `P`.

The proof proceeds by induction on the `ReflTransGen` path. At each step, the intermediate
vertex `b` satisfies `b ∉ S`, so either `x_b ∉ P` or `y_b ∉ P`. We use the corresponding
telescope identity and primality of `P` to conclude. -/
private lemma bij_mem_prime_of_reflTransGen (G : SimpleGraph V)
    (P : Ideal (MvPolynomial (BinomialEdgeVars V) K))
    (hPr : P.IsPrime) (hJG : binomialEdgeIdeal G ≤ P) (S : Finset V)
    (hS : ∀ v : V, v ∉ S → ¬(X (Sum.inl v : BinomialEdgeVars V) ∈ P ∧
                                X (Sum.inr v : BinomialEdgeVars V) ∈ P))
    {j k : V}
    (hpath : Relation.ReflTransGen (fun a b => G.Adj a b ∧ a ∉ S ∧ b ∉ S) j k) :
    (x (K := K) j * y k - x k * y j) ∈ P := by
  induction hpath with
  | refl => simp [x, y]
  | @tail b c _ hbc ih =>
    obtain ⟨hadj_bc, hbS, _⟩ := hbc
    have h_bc : (x (K := K) b * y c - x c * y b) ∈ P :=
      hJG (bij_mem_binomialEdgeIdeal G hadj_bc)
    by_cases hxb : X (Sum.inl b : BinomialEdgeVars V) ∈ P
    · -- x_b ∈ P, so y_b ∉ P (since b ∉ S means not both in P)
      have hyb : X (Sum.inr b : BinomialEdgeVars V) ∉ P :=
        fun hyb => hS b hbS ⟨hxb, hyb⟩
      have htele : y (K := K) b * (x j * y c - x c * y j) ∈ P := by
        rw [y_telescope j b c]
        exact P.add_mem (P.mul_mem_left _ ih) (P.mul_mem_left _ h_bc)
      exact (hPr.mem_or_mem htele).resolve_left hyb
    · -- x_b ∉ P: use x-telescope
      have htele : x (K := K) b * (x j * y c - x c * y j) ∈ P := by
        rw [x_telescope j b c]
        exact P.add_mem (P.mul_mem_left _ h_bc) (P.mul_mem_left _ ih)
      exact (hPr.mem_or_mem htele).resolve_left hxb

/-- For any prime ideal `P ≥ J_G`, the prime component `P_S(G)` is contained in `P`,
where `S = {v : x_v ∈ P ∧ y_v ∈ P}`.

This is the key inclusion needed for the minimal prime characterization. -/
lemma primeComponent_le_prime (G : SimpleGraph V)
    (P : Ideal (MvPolynomial (BinomialEdgeVars V) K))
    (hPr : P.IsPrime) (hJG : binomialEdgeIdeal G ≤ P)
    (S : Finset V)
    (hS_fwd : ∀ v : V, v ∈ S → X (Sum.inl v : BinomialEdgeVars V) ∈ P ∧
                                  X (Sum.inr v : BinomialEdgeVars V) ∈ P)
    (hS_bwd : ∀ v : V, v ∉ S → ¬(X (Sum.inl v : BinomialEdgeVars V) ∈ P ∧
                                    X (Sum.inr v : BinomialEdgeVars V) ∈ P)) :
    primeComponent (K := K) G S ≤ P := by
  apply Ideal.span_le.mpr
  intro f hf
  simp only [Set.mem_union, Set.mem_setOf_eq] at hf
  rcases hf with ⟨i, hiS, rfl | rfl⟩ | ⟨j, k, _, hsc, rfl⟩
  · exact (hS_fwd i hiS).1
  · exact (hS_fwd i hiS).2
  · exact bij_mem_prime_of_reflTransGen G P hPr hJG S hS_bwd hsc.2.2

/-- Every minimal prime of `J_G` equals `P_S(G)` for `S = {v : x_v ∈ P ∧ y_v ∈ P}`.

The proof: `P_S ≤ P` by `primeComponent_le_prime`, `P_S` is prime and `≥ J_G`,
so minimality forces `P = P_S`. -/
private lemma minimalPrime_eq_primeComponent (G : SimpleGraph V)
    (P : Ideal (MvPolynomial (BinomialEdgeVars V) K))
    (hmin : P ∈ (binomialEdgeIdeal (K := K) G).minimalPrimes) :
    ∃ S : Finset V, P = primeComponent (K := K) G S := by
  set S := Finset.univ.filter (fun v =>
    X (Sum.inl v : BinomialEdgeVars V) ∈ P ∧
    X (Sum.inr v : BinomialEdgeVars V) ∈ P)
  refine ⟨S, ?_⟩
  have hPr := Ideal.minimalPrimes_isPrime hmin
  have hJG : binomialEdgeIdeal G ≤ P := hmin.1.2
  have hS_fwd : ∀ v, v ∈ S → X (Sum.inl v : BinomialEdgeVars V) ∈ P ∧
                                X (Sum.inr v : BinomialEdgeVars V) ∈ P :=
    fun v hv => (Finset.mem_filter.mp hv).2
  have hS_bwd : ∀ v, v ∉ S → ¬(X (Sum.inl v : BinomialEdgeVars V) ∈ P ∧
                                  X (Sum.inr v : BinomialEdgeVars V) ∈ P) :=
    fun v hv h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
  -- P_S ≤ P
  have h_le : primeComponent (K := K) G S ≤ P :=
    primeComponent_le_prime G P hPr hJG S hS_fwd hS_bwd
  -- P ≤ P_S by minimality (P_S is prime and ≥ J_G)
  have h_ge : P ≤ primeComponent (K := K) G S :=
    hmin.2 ⟨primeComponent_isPrime G S, binomialEdgeIdeal_le_primeComponent G S⟩ h_le
  exact le_antisymm h_ge h_le

/-! ## Theorem 3.2: Prime decomposition -/

/-- The intersection of all `P_S(G)` equals the radical of `J_G`.

This is proved without assuming radicality: the ≤ direction uses the minimal prime
characterization, and the ≥ direction uses `Ideal.radical_eq_sInf`. -/
lemma iInf_primeComponent_eq_radical (G : SimpleGraph V) :
    ⨅ S : Finset V, primeComponent (K := K) G S = (binomialEdgeIdeal (K := K) G).radical := by
  apply le_antisymm
  · -- ⨅ P_S ≤ radical(J_G) = sInf minimalPrimes
    rw [← Ideal.sInf_minimalPrimes]
    exact le_sInf (fun Q hQ => by
      obtain ⟨S, hS⟩ := minimalPrime_eq_primeComponent G Q hQ
      rw [hS]; exact iInf_le _ S)
  · -- radical(J_G) ≤ ⨅ P_S (each P_S is prime and ≥ J_G)
    apply le_iInf
    intro S
    rw [Ideal.radical_eq_sInf]
    exact sInf_le ⟨binomialEdgeIdeal_le_primeComponent G S, primeComponent_isPrime G S⟩

/--
**Theorem 3.2** (Herzog et al. 2010):
  `J_G = ⋂_{S ⊆ V} P_S(G)`

The proof has two inclusions:
- `J_G ⊆ P_S(G)` for all S: shown in `PrimeIdeals.lean`.
- `⋂ P_S(G) ⊆ J_G`: follows from `⋂ P_S = radical(J_G)` and radicality of `J_G`.

Reference: Herzog et al. (2010), Theorem 3.2.
-/
theorem theorem_3_2 (G : SimpleGraph V) :
    binomialEdgeIdeal (K := K) G = ⨅ S : Finset V, primeComponent (K := K) G S := by
  apply le_antisymm
  · -- ⊆: J_G ≤ ⋂ P_S(G), from binomialEdgeIdeal_le_primeComponent
    exact le_iInf (fun S => binomialEdgeIdeal_le_primeComponent G S)
  · -- ⊇: ⋂ P_S(G) ≤ J_G
    calc ⨅ S, primeComponent (K := K) G S
        = (binomialEdgeIdeal (K := K) G).radical := iInf_primeComponent_eq_radical G
      _ ≤ binomialEdgeIdeal (K := K) G := corollary_2_2 G

/--
The minimal primes of `J_G` are exactly the minimal elements among `{P_S(G)}`.

Reference: Herzog et al. (2010), Theorem 3.2.
-/
theorem minimalPrimes_characterization (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).minimalPrimes =
    { P | ∃ S : Finset V,
        P = primeComponent (K := K) G S ∧
        ∀ T : Finset V, primeComponent (K := K) G T ≤ primeComponent (K := K) G S →
          primeComponent (K := K) G S ≤ primeComponent (K := K) G T } := by
  ext P
  constructor
  · -- Forward: minimal prime → minimal P_S
    intro hmin
    obtain ⟨S, hPS⟩ := minimalPrime_eq_primeComponent G P hmin
    refine ⟨S, hPS, fun T hTS => ?_⟩
    -- P_T ≤ P_S = P, P is minimal, P_T is prime and ≥ J_G → P ≤ P_T → P_S ≤ P_T
    have h : P ≤ primeComponent (K := K) G T :=
      hmin.2 ⟨primeComponent_isPrime G T, binomialEdgeIdeal_le_primeComponent G T⟩
        (hTS.trans (le_of_eq hPS.symm))
    rwa [hPS] at h
  · -- Backward: minimal P_S → minimal prime
    rintro ⟨S, rfl, hSmin⟩
    refine ⟨⟨primeComponent_isPrime G S, binomialEdgeIdeal_le_primeComponent G S⟩,
            fun Q ⟨hQpr, hQge⟩ hQle => ?_⟩
    -- Q is prime, J_G ≤ Q ≤ P_S. Need P_S ≤ Q.
    -- Define T from Q, then P_T ≤ Q ≤ P_S, and by minimality P_S ≤ P_T ≤ Q.
    set T := Finset.univ.filter (fun v =>
      X (Sum.inl v : BinomialEdgeVars V) ∈ Q ∧
      X (Sum.inr v : BinomialEdgeVars V) ∈ Q)
    have hT_le_Q : primeComponent (K := K) G T ≤ Q :=
      primeComponent_le_prime G Q hQpr hQge T
        (fun v hv => (Finset.mem_filter.mp hv).2)
        (fun v hv h => hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hT_le_S : primeComponent (K := K) G T ≤ primeComponent (K := K) G S :=
      hT_le_Q.trans hQle
    calc primeComponent (K := K) G S
        ≤ primeComponent (K := K) G T := hSmin T hT_le_S
      _ ≤ Q := hT_le_Q

/-! ## Proposition 3.6: J_G is prime iff components are complete -/

/--
**Proposition 3.6** (Herzog et al. 2010): `J_G` is a prime ideal if and only if
every connected component of G is a complete graph (i.e., reachable implies adjacent).

- **Forward**: If all components are complete, then `P_∅(G) = J_G` (generators
  coincide), and `P_∅` is prime by `primeComponent_isPrime`.
- **Backward**: If `J_G` is prime, the telescope argument gives `P_∅(G) ≤ J_G`,
  so any reachable binomial `x_u y_w − x_w y_u ∈ J_G`. An evaluation map that
  sends `x_u ↦ 1, y_w ↦ 1` and all other variables to `0` kills every generator
  of `J_G` (since `¬G.Adj u w`) but sends `x_u y_w − x_w y_u` to `1`, giving
  a contradiction.

**Fidelity: Equivalent.** The paper says "each connected component of G is a complete
graph"; the Lean statement uses `∀ u w, G.Reachable u w → G.Adj u w ∨ u = w`, which
is the same condition.

Reference: Herzog et al. (2010), Proposition 3.6.
-/
theorem prop_3_6 (G : SimpleGraph V) :
    (binomialEdgeIdeal (K := K) G).IsPrime ↔
    ∀ u w : V, G.Reachable u w → G.Adj u w ∨ u = w := by
  constructor
  · -- Backward: J_G prime → all components complete
    intro hPrime u w hreach
    by_cases heq : u = w
    · exact Or.inr heq
    · left; by_contra hnadj
      -- P_∅(G) ≤ J_G using telescope + primality
      have hP0_le : primeComponent (K := K) G ∅ ≤ binomialEdgeIdeal (K := K) G :=
        primeComponent_le_prime G _ hPrime (le_refl _) ∅
          (fun v hv => absurd hv (Finset.notMem_empty v))
          (fun v _ ⟨hx, _⟩ => X_inl_not_mem_primeComponent (K := K) G ∅
            (Finset.notMem_empty v) (binomialEdgeIdeal_le_primeComponent G ∅ hx))
      -- x_u y_w − x_w y_u ∈ P_∅ (since u,w are reachable → SameComponent G ∅ u w)
      have hsc : SameComponent G ∅ u w :=
        ⟨Finset.notMem_empty _, Finset.notMem_empty _,
         Relation.ReflTransGen.mono
           (fun a b h => ⟨h, Finset.notMem_empty _, Finset.notMem_empty _⟩)
           ((SimpleGraph.reachable_iff_reflTransGen u w).mp hreach)⟩
      -- Get x_u y_w − x_w y_u ∈ J_G via P_∅ ≤ J_G
      have hmem : (x (K := K) u * y w - x w * y u) ∈ binomialEdgeIdeal (K := K) G := by
        rcases lt_or_gt_of_ne heq with hlt | hgt
        · exact hP0_le (Ideal.subset_span (Set.mem_union_right _ ⟨u, w, hlt, hsc, rfl⟩))
        · convert (binomialEdgeIdeal (K := K) G).neg_mem (hP0_le
            (Ideal.subset_span (Set.mem_union_right _ ⟨w, u, hgt, hsc.symm, rfl⟩))) using 1
          ring
      -- Evaluation map: x_i ↦ δ_{i,u}, y_j ↦ δ_{j,w}
      let φ : MvPolynomial (BinomialEdgeVars V) K →ₐ[K] K :=
        MvPolynomial.aeval (Sum.elim (fun i => if i = u then (1 : K) else 0)
                                     (fun i => if i = w then (1 : K) else 0))
      -- φ kills all of J_G
      have hφ_kill : binomialEdgeIdeal (K := K) G ≤ RingHom.ker φ.toRingHom := by
        rw [binomialEdgeIdeal]; apply Ideal.span_le.mpr
        rintro _ ⟨a, b, hadj_ab, _, rfl⟩
        simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
                   AlgHom.coe_toRingHom, map_sub, map_mul, x, y, φ, MvPolynomial.aeval_X,
                   Sum.elim_inl, Sum.elim_inr]
        have : ¬(a = u ∧ b = w) := fun ⟨ha, hb⟩ => hnadj (ha ▸ hb ▸ hadj_ab)
        have : ¬(b = u ∧ a = w) := fun ⟨hb, ha⟩ => hnadj (ha ▸ hb ▸ hadj_ab.symm)
        split_ifs <;> simp_all
      -- φ(x_u y_w − x_w y_u) = 1 ≠ 0, contradicting hmem ∈ ker φ
      have hmem_ker := hφ_kill hmem
      rw [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at hmem_ker
      simp only [map_sub, map_mul, x, y, φ, MvPolynomial.aeval_X, Sum.elim_inl, Sum.elim_inr,
                 heq, Ne.symm heq, ite_true, ite_false, one_mul, mul_zero, sub_zero,
                 one_ne_zero] at hmem_ker
  · -- Forward: all components complete → J_G prime
    intro hComplete
    have hP0_le : primeComponent (K := K) G ∅ ≤ binomialEdgeIdeal (K := K) G := by
      apply Ideal.span_le.mpr
      intro f hf
      simp only [Set.mem_union, Set.mem_setOf_eq] at hf
      rcases hf with ⟨i, hiS, _⟩ | ⟨j, k, hjk, hsc, rfl⟩
      · exact absurd hiS (Finset.notMem_empty i)
      · have hreach : G.Reachable j k :=
          (SimpleGraph.reachable_iff_reflTransGen j k).mpr
            (hsc.2.2.mono (fun _ _ ⟨h, _, _⟩ => h))
        rcases hComplete j k hreach with hadj | heq
        · exact Ideal.subset_span ⟨j, k, hadj, hjk, rfl⟩
        · exact absurd (heq ▸ hjk) (lt_irrefl _)
    rw [show binomialEdgeIdeal (K := K) G = primeComponent (K := K) G ∅ from
      le_antisymm (binomialEdgeIdeal_le_primeComponent G ∅) hP0_le]
    exact primeComponent_isPrime G ∅

/-! ## Corollary 3.3: Dimension formula -/

/-!
### Corollary 3.3: Dimension formula

**Corollary 3.3** (Herzog et al. 2010):
  `dim(K[x,y]/J_G) = max_{S ⊆ V} (|V| - |S| + c(S))`

**Proof structure** (using `ringKrullDim_quotient_radical`):

Step 1: `dim(R/J_G) = sup_S dim(R/P_S)` — from `ringKrullDim_quotient_radical`
applied to `J_G` (radical by Cor 2.2), using `theorem_3_2` to identify J_G with
the intersection of P_S's.

Step 2: `dim(R/P_S) = |V| - |S| + c(S)` for each S — the key sub-theorem
`ringKrullDim_quot_primeComponent`, which requires computing the quotient
dimension directly for each prime component.

**Remaining blocker:** Step 2 (Layer 1 of the dimension guide). Computing
`dim(R/P_S)` requires either the catenary property or a direct chain/ring
equivalence argument for the specific structure of P_S.

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

/-- Monotonicity: enlarging `Ux` or `Uy` grows the kernel.
Proof: `dimChainMap(Ux', Uy') = extraKill ∘ dimChainMap(Ux, Uy)` when Ux ⊆ Ux', Uy ⊆ Uy'.
So `ker(f) ≤ ker(g ∘ f)` by `f(x)=0 → g(f(x))=g(0)=0`. -/
theorem dimChainMap_ker_mono (G : SimpleGraph V) (S : Finset V)
    {Ux Ux' Uy Uy' : Finset V} (hx : Ux ⊆ Ux') (hy : Uy ⊆ Uy') :
    RingHom.ker (dimChainMap (K := K) G S Ux Uy).toRingHom ≤
    RingHom.ker (dimChainMap (K := K) G S Ux' Uy').toRingHom := by
  -- Define the "extra kill" map: kills variables in Ux' \ Ux and Uy' \ Uy
  set extraKill : MvPolynomial (BinomialEdgeVars V) K →ₐ[K]
      MvPolynomial (BinomialEdgeVars V) K :=
    MvPolynomial.aeval (fun v : BinomialEdgeVars V =>
      match v with
      | Sum.inl j => if j ∈ Ux' then 0 else X (Sum.inl j)
      | Sum.inr j => if j ∈ Uy' then 0 else X (Sum.inr j))
  -- Factorization: dimChainMap(Ux', Uy') = extraKill ∘ dimChainMap(Ux, Uy)
  -- Both sides are AlgHoms R → R, so it suffices to check on generators X(w).
  -- Factorization: dimChainMap(Ux', Uy') = extraKill ∘ dimChainMap(Ux, Uy)
  suffices hfact : dimChainMap (K := K) G S Ux' Uy' =
      extraKill.comp (dimChainMap (K := K) G S Ux Uy) by
    intro f hf; rw [RingHom.mem_ker] at hf ⊢
    change (dimChainMap (K := K) G S Ux' Uy') f = 0
    rw [hfact, AlgHom.comp_apply, show (dimChainMap (K := K) G S Ux Uy) f = 0 from hf, map_zero]
  -- Both sides are AlgHoms; check on generators
  apply MvPolynomial.algHom_ext; intro w
  -- Unfold both sides: dimChainMap = killStep ∘ primeComponentMap
  -- LHS: extraKill(killStep(Ux,Uy)(pcm(X w)))
  -- RHS: killStep(Ux',Uy')(pcm(X w))
  -- They agree because extraKill ∘ killStep(Ux,Uy) = killStep(Ux',Uy') on images of pcm.
  simp only [dimChainMap, extraKill, AlgHom.comp_apply, MvPolynomial.aeval_X]
  -- Now pcm(X w) is determined by w = inl j or inr j, and whether j ∈ S.
  -- After unfolding pcm, the intermediate and final kill steps are if-then-else.
  simp only [primeComponentMap, MvPolynomial.aeval_X]
  -- The aeval/match reduction is deeply nested. Sorry the generator check
  -- pending a cleaner approach (e.g., proving the factorization via a helper
  -- that unfolds primeComponentMap on each case).
  sorry

/-- Lower bound: `dim(R/P_S) ≥ |V| - |S| + c(S)`.
Uses an explicit chain of primes (kernels of `dimChainMap` with increasing
variable kills) above P_S. See ANSWER_08 for the full strategy.  -/
theorem ringKrullDim_quot_primeComponent_ge (G : SimpleGraph V) (S : Finset V) :
    (Fintype.card V - S.card + componentCount G S : ℕ) ≤
    ringKrullDim (MvPolynomial (BinomialEdgeVars V) K ⧸ primeComponent (K := K) G S) := by
  -- Chain of prime kernels: vary (Ux, Uy) from (∅,∅) to (all non-reps, all reps, all reps)
  -- Each step adds one variable to Ux or Uy, giving a strictly larger kernel.
  -- Total chain length = |non-reps| + |reps| + |reps| = |V\S| - c(S) + c(S) + c(S) = |V\S| + c(S)
  sorry

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
  -- Step 1: dim(R/J_G) = sup_S dim(R/P_S)
  -- Step 2: dim(R/P_S) = |V| - |S| + c(S)
  sorry

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
        -- Step 2: dim(R/P_∅) ≥ n + c(G)
        -- This requires computing dim(R/P_∅) via an explicit chain of primes.
        -- Chain: P_∅ < Q₁ < ... < Q_{c-1} < (x_all) < (x_all,y₁) < ... < m
        -- Each Q_k replaces one component's BEI with x-variables (prime by poly-over-domain).
        sorry
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
  sorry

/-! ## Unmixedness -/

section Unmixed

variable {S : Type*} [CommRing S]

/-- An ideal `I` is **unmixed** if all its minimal primes have the same height. -/
def Ideal.IsUnmixed (I : Ideal S) : Prop :=
  ∀ P Q : Ideal S, P ∈ I.minimalPrimes → Q ∈ I.minimalPrimes → P.height = Q.height

/-- A prime ideal is trivially unmixed: it has exactly one minimal prime (itself). -/
theorem Ideal.IsPrime.isUnmixed {I : Ideal S} (hI : I.IsPrime) : I.IsUnmixed := by
  intro P Q hP hQ
  have hPeq : P = I := le_antisymm (hP.2 ⟨hI, le_refl I⟩ hP.1.2) hP.1.2
  have hQeq : Q = I := le_antisymm (hQ.2 ⟨hI, le_refl I⟩ hQ.1.2) hQ.1.2
  rw [hPeq, hQeq]

end Unmixed

/-! ## Corollary 3.7: Cycles -/

/-- A graph G on V is a cycle (every vertex has exactly 2 neighbors). -/
def IsCycleGraph (G : SimpleGraph V) : Prop :=
  G.Connected ∧
  ∀ v : V, ∃ u w : V, u ≠ w ∧ G.Adj v u ∧ G.Adj v w ∧ ∀ z : V, G.Adj v z → z = u ∨ z = w

/--
**Corollary 3.7** (Herzog et al. 2010): For a cycle G of length n ≥ 3:
  (a) n = 3
  (b) J_G is prime
  (c) J_G is unmixed
  (d) K[x,y]/J_G is Cohen-Macaulay
are all equivalent.

Reference: Herzog et al. (2010), Corollary 3.7.
-/
theorem corollary_3_7 (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    Fintype.card V = 3 ↔ (binomialEdgeIdeal (K := K) G).IsPrime := by
  obtain ⟨hConn, hDeg⟩ := hCyc
  -- Helper: complete cycle graph has ≤ 3 vertices
  have aux : (∀ u w : V, u ≠ w → G.Adj u w) → Fintype.card V ≤ 3 := by
    intro hAdj
    obtain ⟨v⟩ := hConn.nonempty
    obtain ⟨n1, n2, _, _, _, honly⟩ := hDeg v
    have hsub : (Finset.univ : Finset V) ⊆ {v, n1, n2} := by
      intro w _; simp only [Finset.mem_insert, Finset.mem_singleton]
      exact (eq_or_ne w v).imp_right fun hw => honly w (hAdj v w hw.symm)
    exact Finset.card_univ (α := V) ▸ (Finset.card_le_card hsub).trans Finset.card_le_three
  constructor
  · -- |V| = 3 → prime: in a 3-cycle every pair is adjacent
    intro hcard; rw [prop_3_6]
    intro u w hreach
    by_cases huw : u = w
    · exact Or.inr huw
    · left
      obtain ⟨n1, n2, hn12, hadj1, hadj2, _⟩ := hDeg u
      -- {u, n1, n2} has 3 distinct elements = |V|, so it equals Finset.univ
      have h3 : ({u, n1, n2} : Finset V).card = Fintype.card V := by
        rw [hcard, Finset.card_insert_of_notMem, Finset.card_pair hn12]
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨G.ne_of_adj hadj1, G.ne_of_adj hadj2⟩
      have hw_mem := (Finset.eq_univ_of_card _ h3) ▸ Finset.mem_univ w
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw_mem
      rcases hw_mem.resolve_left (Ne.symm huw) with rfl | rfl
      · exact hadj1
      · exact hadj2
  · -- prime → |V| = 3
    intro hPrime
    have hAdj : ∀ u w : V, u ≠ w → G.Adj u w := fun u w huw =>
      ((prop_3_6 (K := K) G).mp hPrime u w (hConn.preconnected u w)).resolve_right huw
    exact le_antisymm (aux hAdj) hn

-- Corollary 3.7 unmixed branch (a↔b↔c) is in MinimalPrimes.lean to avoid import cycle.

theorem corollary_3_7_CM (G : SimpleGraph V) (hCyc : IsCycleGraph G)
    (hn : 3 ≤ Fintype.card V) :
    IsCohenMacaulay (MvPolynomial (BinomialEdgeVars V) K ⧸ binomialEdgeIdeal (K := K) G) ↔
    (binomialEdgeIdeal (K := K) G).IsPrime := by
  sorry

end

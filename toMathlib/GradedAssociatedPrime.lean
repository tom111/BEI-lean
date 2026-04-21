/-
Copyright: BEI Lean project.

# Associated primes of a graded module are homogeneous

For a graded Noetherian commutative ring `A` (graded by ℕ), every associated
prime of `A` as an `A`-module is a homogeneous ideal. This is BH 1.5.6 /
Eisenbud Corollary 3.5.

## Main results

* `annihilator_singleton_isHomogeneous_of_homogeneousElem` — **PROVED**:
  if `x ∈ A` is homogeneous, then `Ann(x)` is a homogeneous ideal.

* `annihilator_mul_eq_of_prime_notMem` — **PROVED**: if `p = Ann(x)` is
  prime and `z ∉ p`, then `Ann(z · x) = p`.

* `isAssociatedPrime_isHomogeneous` — **PROOF STRATEGY DOCUMENTED;
  FORMALIZATION PENDING** (requires ~300 LOC of `DFinsupp.support` /
  `DirectSum.decompose` bookkeeping plus well-founded induction).

## Proof strategy (Eisenbud 3.5)

Given `p = Ann(x)` prime, strong induction on
`|(DirectSum.decompose 𝒜 x).support|`:

**Base** (support size 1): `x` is homogeneous; take `y := x`.

**Step** (support size ≥ 2): let `d` be the max index of the support,
`x_d` the top component, `J := Ann(x_d)` (homogeneous ideal by the
first sub-lemma). Trichotomy on `J` vs `p`:

* **Case A** (`J = p`): take `y := x_d`.
* **Case B** (`J ⊊ p` strictly): **Impossible**. Pick any `r ∈ p \ J`.
  Peel: the top-degree graded component of `r` (call it `r_{d_r}`)
  lies in `J` by the graded-product argument — the top-degree
  component of the product `r · x = 0` at degree `d_r + d` is
  `r_{d_r} · x_d`, which must vanish, so `r_{d_r} ∈ J ⊆ p`. Hence
  `r - r_{d_r} ∈ p \ J` with strictly fewer homogeneous components.
  Iterate to obtain a homogeneous `r* ∈ p \ J`. But `r*` homog +
  `r* · x = 0` forces (by graded degree separation)
  `r* · x_i = 0` for all `i ∈ supp(x)`, in particular `r* · x_d = 0`,
  i.e., `r* ∈ J`, contradicting `r* ∉ J`.
* **Case C** (`J ⊈ p`): Since `J` is homogeneous, pick any `r ∈ J \ p`
  and extract a homogeneous component `r_k ∉ p` (else all components
  in `p` ⟹ `r ∈ p`, contra). Set `z := r_k`: homogeneous, `∈ J`, `∉ p`.
  Then `z · x_d = 0`, so `z · x` has support embedded in
  `{k + i : i ∈ supp(x) \ {d}}` — strictly smaller. Also
  `Ann(z · x) = (p : z) = p` (primality + `z ∉ p`, via the proved
  `annihilator_mul_eq_of_prime_notMem`). Apply IH.

Once `p = Ann(y)` with `y` homogeneous, conclude via
`annihilator_singleton_isHomogeneous_of_homogeneousElem`.

## Status

The strategy is mathematically verified end-to-end, with all hard
algebraic sub-lemmas proved. The remaining Lean-level work is:

1. **Support-size decrease** (~80 LOC): If `z ∈ 𝒜 k` homogeneous and
   `z · x_d = 0`, then `|supp(z · x)| < |supp(x)|`. Uses
   `DirectSum.coe_decompose_mul_of_left_mem` to identify support
   elements as degree-shifts from `supp(x)`.

2. **Peeling argument** (~120 LOC): Formalizing Case B's contradiction
   requires nested induction on support size, careful subtraction of
   top-degree components (again via `coe_decompose_mul_add_of_right_mem`).

3. **Main induction** (~60 LOC): Strong induction on support size
   with case-split on `J ⊆ p` vs `J ⊈ p`.

4. **DFinsupp decidability glue** (~20 LOC): `Classical.decEq`
   instances for `𝒜 i`.

Total estimated: ~280-320 LOC. This exceeds single-session capacity.
See `guides/work_packages/ROUTE_B_OBSTACLE_PLAN.md`.
-/

import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Colon

noncomputable section

namespace GradedAssociatedPrime

open DirectSum

universe u

variable {A : Type u} [CommRing A]
variable (𝒜 : ℕ → AddSubgroup A) [GradedRing 𝒜]

attribute [local instance] Classical.propDecidable

/-! ### Sub-lemma 1: annihilator of a homogeneous element is homogeneous -/

/-- If `x ∈ A` is homogeneous, then `(⊥ : Submodule A A).colon {x}` (the
annihilator of `x`) is a homogeneous ideal of `A`. -/
theorem annihilator_singleton_isHomogeneous_of_homogeneousElem
    {x : A} (hx : SetLike.IsHomogeneousElem 𝒜 x) :
    Ideal.IsHomogeneous 𝒜
      ((⊥ : Submodule A A).colon {x}) := by
  classical
  obtain ⟨i₀, hx_mem⟩ := hx
  intro i a ha
  rw [Submodule.mem_colon_singleton] at ha
  rw [Submodule.mem_colon_singleton]
  change a * x = 0 at ha
  change (DirectSum.decompose 𝒜 a i : A) * x = 0
  have hcomp : ↑((DirectSum.decompose 𝒜 (a * x)) (i + i₀)) =
      (DirectSum.decompose 𝒜 a i : A) * x :=
    DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hx_mem
  rw [ha, decompose_zero] at hcomp
  simp at hcomp
  exact hcomp.symm

/-! ### Sub-lemma 2: colon identity -/

/-- If `p` is prime, `Ann(x) = p`, and `z ∉ p`, then `Ann(z · x) = p`. -/
theorem annihilator_mul_eq_of_prime_notMem
    {p : Ideal A} (hp_prime : p.IsPrime)
    {x z : A} (hx_ann : (⊥ : Submodule A A).colon {x} = p)
    (hz : z ∉ p) :
    (⊥ : Submodule A A).colon {z * x} = p := by
  ext a
  rw [Submodule.mem_colon_singleton]
  change a • (z * x) ∈ (⊥ : Submodule A A) ↔ a ∈ p
  rw [Submodule.mem_bot]
  constructor
  · intro h
    have haz_ann : a * z ∈ (⊥ : Submodule A A).colon {x} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      change (a * z) * x = 0
      calc (a * z) * x = a * (z * x) := by ring
        _ = a • (z * x) := rfl
        _ = 0 := h
    rw [hx_ann] at haz_ann
    rcases hp_prime.mem_or_mem haz_ann with ha | hz'
    · exact ha
    · exact absurd hz' hz
  · intro ha
    have hax_ann : a ∈ (⊥ : Submodule A A).colon {x} := hx_ann ▸ ha
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hax_ann
    change a * x = 0 at hax_ann
    change a * (z * x) = 0
    calc a * (z * x) = z * (a * x) := by ring
      _ = z * 0 := by rw [hax_ann]
      _ = 0 := by ring

/-! ### Sub-lemma 3: key identity for top-degree components

Given `r, x : A` with `d_r, d` indexing the top elements of the respective
supports (maxima), the `(d_r + d)`-th homogeneous component of `r · x`
equals `r_{d_r} · x_d`. This is the algebraic heart of BH 1.5.6. -/

private lemma decompose_mul_top_coe
    {r x : A}
    {d_r d : ℕ}
    (hdr_mem : d_r ∈ (DirectSum.decompose 𝒜 r).support)
    (hdr_max : ∀ i ∈ (DirectSum.decompose 𝒜 r).support, i ≤ d_r)
    (hd_mem : d ∈ (DirectSum.decompose 𝒜 x).support)
    (hd_max : ∀ j ∈ (DirectSum.decompose 𝒜 x).support, j ≤ d) :
    (DirectSum.decompose 𝒜 (r * x) (d_r + d) : A) =
      (DirectSum.decompose 𝒜 r d_r : A) *
        (DirectSum.decompose 𝒜 x d : A) := by
  classical
  rw [DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  -- The filtered sum has exactly one term: (d_r, d).
  have hfilter :
      ((DirectSum.decompose 𝒜 r).support ×ˢ
          (DirectSum.decompose 𝒜 x).support).filter
          (fun ij => ij.1 + ij.2 = d_r + d) = {(d_r, d)} := by
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton,
      Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨⟨hi, hj⟩, hij⟩
      have hi_le := hdr_max i hi
      have hj_le := hd_max j hj
      refine ⟨?_, ?_⟩ <;> omega
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨hdr_mem, hd_mem⟩, rfl⟩
  rw [hfilter, Finset.sum_singleton]

/-! ### Sub-lemma 4: support decrease under subtraction of a top component

For any `x : A` with `d ∈ supp(decompose 𝒜 x)`, subtracting the `d`-th
homogeneous component strictly decreases the support size: the resulting
support equals `(supp x).erase d`. -/

private lemma decompose_sub_component_ne
    (x : A) {d : ℕ} (i : ℕ) (hi : i ≠ d) :
    (DirectSum.decompose 𝒜 (x - (DirectSum.decompose 𝒜 x d : A)) i : A) =
      (DirectSum.decompose 𝒜 x i : A) := by
  classical
  rw [DirectSum.decompose_sub, DFinsupp.sub_apply, AddSubgroupClass.coe_sub]
  have : (DirectSum.decompose 𝒜 ((DirectSum.decompose 𝒜 x d : A)) i : A) = 0 :=
    DirectSum.decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) hi.symm
  rw [this]
  ring

private lemma decompose_sub_component_self
    (x : A) (d : ℕ) :
    (DirectSum.decompose 𝒜 (x - (DirectSum.decompose 𝒜 x d : A)) d : A) = 0 := by
  classical
  rw [DirectSum.decompose_sub, DFinsupp.sub_apply, AddSubgroupClass.coe_sub]
  have : (DirectSum.decompose 𝒜 ((DirectSum.decompose 𝒜 x d : A)) d : A) =
      (DirectSum.decompose 𝒜 x d : A) :=
    DirectSum.decompose_of_mem_same 𝒜 (SetLike.coe_mem _)
  rw [this]
  ring

private lemma support_sub_decompose_card_lt
    {x : A} {d : ℕ} (hd : d ∈ (DirectSum.decompose 𝒜 x).support) :
    (DirectSum.decompose 𝒜
        (x - (DirectSum.decompose 𝒜 x d : A))).support.card <
      (DirectSum.decompose 𝒜 x).support.card := by
  classical
  refine lt_of_le_of_lt
    (Finset.card_le_card (s := (DirectSum.decompose 𝒜
        (x - (DirectSum.decompose 𝒜 x d : A))).support)
      (t := (DirectSum.decompose 𝒜 x).support.erase d) ?_) ?_
  · intro i hi
    rw [DFinsupp.mem_support_iff] at hi
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · -- i ≠ d
      intro hid
      apply hi
      rw [hid]
      exact Subtype.ext (decompose_sub_component_self 𝒜 x d)
    · -- i ∈ supp(x)
      rw [DFinsupp.mem_support_iff]
      intro hnot_x
      apply hi
      -- Both decompose values coincide since i ≠ d.
      have hne : i ≠ d := by
        rintro rfl
        have hself := decompose_sub_component_self 𝒜 x i
        exact hi (Subtype.ext hself)
      have heq := decompose_sub_component_ne 𝒜 x (d := d) i hne
      apply Subtype.ext
      change (DirectSum.decompose 𝒜 (x - (DirectSum.decompose 𝒜 x d : A)) i : A) =
        ((0 : ↥(𝒜 i)) : A)
      rw [heq]
      have : (DirectSum.decompose 𝒜 x i : A) = ((0 : ↥(𝒜 i)) : A) := by
        rw [hnot_x]
      exact this
  · rw [Finset.card_erase_of_mem hd]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨d, hd⟩) Nat.zero_lt_one

/-! ### Sub-lemma 5: support decrease under multiplication by a killing
homogeneous element -/

private lemma support_mul_homog_lt
    {x : A} {d : ℕ}
    (hd_mem : d ∈ (DirectSum.decompose 𝒜 x).support)
    {k : ℕ} {z : A} (hz_mem : z ∈ 𝒜 k)
    (hz_kills : z * (DirectSum.decompose 𝒜 x d : A) = 0) :
    (DirectSum.decompose 𝒜 (z * x)).support.card <
      (DirectSum.decompose 𝒜 x).support.card := by
  classical
  -- Injection supp(z·x) ↪ supp(x).erase d via `n ↦ n - k`.
  refine lt_of_le_of_lt
    (Finset.card_le_card_of_injOn (f := fun n => n - k)
      (s := (DirectSum.decompose 𝒜 (z * x)).support)
      (t := (DirectSum.decompose 𝒜 x).support.erase d) ?_ ?_) ?_
  · -- Mapsto: for n ∈ supp(z·x), (n - k) ∈ supp(x).erase d.
    intro n hn
    rw [Finset.mem_coe, DFinsupp.mem_support_iff] at hn
    rw [Finset.mem_coe]
    have hcoe : (DirectSum.decompose 𝒜 (z * x) n : A) ≠ 0 := by
      intro h
      apply hn
      exact Subtype.ext h
    have heq := DirectSum.coe_decompose_mul_of_left_mem 𝒜 (a := z) (b := x) n hz_mem
    by_cases hkn : k ≤ n
    · -- coeff = z * x_{n-k}
      rw [if_pos hkn] at heq
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · -- n - k ≠ d, since if n - k = d, coeff = z * x_d = 0.
        intro h
        have h' : n - k = d := h
        apply hcoe
        show (DirectSum.decompose 𝒜 (z * x) n : A) = 0
        rw [heq, h', hz_kills]
      · -- n - k ∈ supp(x)
        rw [DFinsupp.mem_support_iff]
        intro hxcoe
        apply hcoe
        show (DirectSum.decompose 𝒜 (z * x) n : A) = 0
        rw [heq]
        have : (DirectSum.decompose 𝒜 x (n - k) : A) = 0 := by
          have : DirectSum.decompose 𝒜 x (n - k) = 0 := hxcoe
          rw [this]; rfl
        rw [this]; ring
    · rw [if_neg hkn] at heq
      exact absurd heq hcoe
  · -- Injectivity on supp(z·x).
    intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_coe, DFinsupp.mem_support_iff] at hn₁ hn₂
    have hcoe₁ : (DirectSum.decompose 𝒜 (z * x) n₁ : A) ≠ 0 := by
      intro h'; apply hn₁; exact Subtype.ext h'
    have hcoe₂ : (DirectSum.decompose 𝒜 (z * x) n₂ : A) ≠ 0 := by
      intro h'; apply hn₂; exact Subtype.ext h'
    -- Both n₁, n₂ ≥ k.
    have heq₁ := DirectSum.coe_decompose_mul_of_left_mem 𝒜 (a := z) (b := x) n₁ hz_mem
    have heq₂ := DirectSum.coe_decompose_mul_of_left_mem 𝒜 (a := z) (b := x) n₂ hz_mem
    have hk₁ : k ≤ n₁ := by
      by_contra hkn; rw [if_neg hkn] at heq₁; exact hcoe₁ heq₁
    have hk₂ : k ≤ n₂ := by
      by_contra hkn; rw [if_neg hkn] at heq₂; exact hcoe₂ heq₂
    simp only at h
    omega
  · rw [Finset.card_erase_of_mem hd_mem]
    exact Nat.sub_lt (Finset.card_pos.mpr ⟨d, hd_mem⟩) Nat.zero_lt_one

/-! ### Sub-lemma 6: peeling argument — `Ann(x_d) ⊊ p` is impossible

If `p = Ann(x)` is prime and `d` is max in `supp(decompose 𝒜 x)`, then
`Ann(x_d)` cannot be strictly contained in `p`. -/

private lemma ann_top_comp_not_lt
    {p : Ideal A} (_hp_prime : p.IsPrime)
    {x : A} (hx_ann : (⊥ : Submodule A A).colon {x} = p)
    {d : ℕ} (hd_mem : d ∈ (DirectSum.decompose 𝒜 x).support)
    (hd_max : ∀ i ∈ (DirectSum.decompose 𝒜 x).support, i ≤ d) :
    ¬ ((⊥ : Submodule A A).colon
        {(DirectSum.decompose 𝒜 x d : A)} < p) := by
  classical
  intro hlt
  -- Get an element r ∈ p \ Ann(x_d).
  have hnot_le : ¬ p ≤ (⊥ : Submodule A A).colon
      {(DirectSum.decompose 𝒜 x d : A)} := not_le_of_gt hlt
  rw [SetLike.not_le_iff_exists] at hnot_le
  obtain ⟨r₀, hr₀_p, hr₀_notAnn⟩ := hnot_le
  -- Strong induction on |supp r|.
  suffices h : ∀ n : ℕ, ∀ r : A, r ∈ p →
      r ∉ (⊥ : Submodule A A).colon {(DirectSum.decompose 𝒜 x d : A)} →
      (DirectSum.decompose 𝒜 r).support.card ≤ n → False by
    exact h _ r₀ hr₀_p hr₀_notAnn le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro r hr_p hr_notAnn hcard
    -- Get r ≠ 0.
    by_cases hr_zero : r = 0
    · apply hr_notAnn
      rw [hr_zero]; exact Submodule.zero_mem _
    -- supp r is nonempty.
    have hsupp_ne : (DirectSum.decompose 𝒜 r).support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hr_zero
      rw [← DirectSum.sum_support_decompose 𝒜 r, hempty, Finset.sum_empty]
    -- Let d_r = max supp r.
    set d_r := (DirectSum.decompose 𝒜 r).support.max' hsupp_ne with hd_r_def
    have hdr_mem : d_r ∈ (DirectSum.decompose 𝒜 r).support :=
      Finset.max'_mem _ _
    have hdr_max : ∀ i ∈ (DirectSum.decompose 𝒜 r).support, i ≤ d_r :=
      fun i hi => Finset.le_max' _ i hi
    -- Key fact: r_{d_r} · x_d = 0.
    have hrx_zero : r * x = 0 := by
      have hr_ann : r ∈ (⊥ : Submodule A A).colon {x} := hx_ann ▸ hr_p
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr_ann
      change r * x = 0 at hr_ann
      exact hr_ann
    have hprod_zero :
        (DirectSum.decompose 𝒜 r d_r : A) *
          (DirectSum.decompose 𝒜 x d : A) = 0 := by
      have := decompose_mul_top_coe 𝒜 hdr_mem hdr_max hd_mem hd_max
      rw [hrx_zero] at this
      rw [DirectSum.decompose_zero] at this
      simp at this
      exact this.symm
    -- Hence r_{d_r} ∈ Ann(x_d).
    have hrdr_ann : (DirectSum.decompose 𝒜 r d_r : A) ∈
        (⊥ : Submodule A A).colon {(DirectSum.decompose 𝒜 x d : A)} := by
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
      exact hprod_zero
    -- Hence r_{d_r} ∈ p (since Ann(x_d) ⊆ p).
    have hrdr_p : (DirectSum.decompose 𝒜 r d_r : A) ∈ p :=
      hlt.le hrdr_ann
    -- Set r' := r - r_{d_r}.
    set r' := r - (DirectSum.decompose 𝒜 r d_r : A) with hr'_def
    -- r' ∈ p.
    have hr'_p : r' ∈ p := by
      rw [hr'_def]; exact Ideal.sub_mem _ hr_p hrdr_p
    -- r' ∉ Ann(x_d) (else r = r' + r_{d_r} would be in Ann(x_d)).
    have hr'_notAnn : r' ∉ (⊥ : Submodule A A).colon
        {(DirectSum.decompose 𝒜 x d : A)} := by
      intro habs
      apply hr_notAnn
      have : r = r' + (DirectSum.decompose 𝒜 r d_r : A) := by
        rw [hr'_def]; ring
      rw [this]
      exact Submodule.add_mem _ habs hrdr_ann
    -- |supp r'| < |supp r| ≤ n.
    have hr'_card : (DirectSum.decompose 𝒜 r').support.card <
        (DirectSum.decompose 𝒜 r).support.card :=
      support_sub_decompose_card_lt 𝒜 hdr_mem
    -- Apply IH.
    have hr'_card' : (DirectSum.decompose 𝒜 r').support.card < n := by
      omega
    -- Case on n (strong induction).
    match n, hcard, hr'_card' with
    | 0, _, h => exact absurd h (Nat.not_lt_zero _)
    | n + 1, _, h =>
      exact IH (DirectSum.decompose 𝒜 r').support.card h r' hr'_p hr'_notAnn le_rfl

/-! ### Main theorem -/

/-- **BH 1.5.6 / Eisenbud 3.5**: Every associated prime of `A` (as an
`A`-module) is homogeneous. -/
theorem isAssociatedPrime_isHomogeneous
    {p : Ideal A} (hp : p ∈ associatedPrimes A A) :
    p.IsHomogeneous 𝒜 := by
  classical
  rw [AssociatePrimes.mem_iff] at hp
  obtain ⟨hp_prime, x₀, hx₀_ann⟩ := hp
  -- It suffices to find a homogeneous `y` with `Ann(y) = p`.
  suffices h : ∃ y : A, SetLike.IsHomogeneousElem 𝒜 y ∧
      (⊥ : Submodule A A).colon {y} = p by
    obtain ⟨y, hy_hom, hy_ann⟩ := h
    rw [← hy_ann]
    exact annihilator_singleton_isHomogeneous_of_homogeneousElem 𝒜 hy_hom
  -- Strong induction on the support size of `x`.
  suffices h : ∀ n : ℕ, ∀ x : A,
      (⊥ : Submodule A A).colon {x} = p →
      (DirectSum.decompose 𝒜 x).support.card ≤ n →
      ∃ y, SetLike.IsHomogeneousElem 𝒜 y ∧
        (⊥ : Submodule A A).colon {y} = p by
    exact h _ x₀ hx₀_ann.symm le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x hx_ann hcard
    -- Handle x = 0 case: then Ann(x) = ⊤, contradicting p prime.
    by_cases hx_zero : x = 0
    · exfalso
      rw [hx_zero] at hx_ann
      have : (⊥ : Submodule A A).colon {(0 : A)} = ⊤ := by
        ext a
        simp [Submodule.mem_colon_singleton]
      rw [this] at hx_ann
      exact hp_prime.ne_top hx_ann.symm
    -- supp is nonempty.
    have hsupp_ne : (DirectSum.decompose 𝒜 x).support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      apply hx_zero
      rw [← DirectSum.sum_support_decompose 𝒜 x, hempty, Finset.sum_empty]
    -- Let d = max supp x.
    set d := (DirectSum.decompose 𝒜 x).support.max' hsupp_ne with hd_def
    have hd_mem : d ∈ (DirectSum.decompose 𝒜 x).support := Finset.max'_mem _ _
    have hd_max : ∀ i ∈ (DirectSum.decompose 𝒜 x).support, i ≤ d :=
      fun i hi => Finset.le_max' _ i hi
    -- Case-split: Ann(x_d) ≤ p or not.
    set J := (⊥ : Submodule A A).colon {(DirectSum.decompose 𝒜 x d : A)} with hJ_def
    by_cases hJ_le : J ≤ p
    · -- Ann(x_d) ≤ p. By peeling, Ann(x_d) = p (can't be strict).
      have hJ_eq : J = p := by
        by_contra hne
        have hlt : J < p := lt_of_le_of_ne hJ_le hne
        exact ann_top_comp_not_lt 𝒜 hp_prime hx_ann hd_mem hd_max hlt
      -- Take y := x_d, homogeneous.
      refine ⟨(DirectSum.decompose 𝒜 x d : A), ⟨d, SetLike.coe_mem _⟩, hJ_eq⟩
    · -- Ann(x_d) ⊄ p. Find homogeneous z ∈ Ann(x_d) \ p.
      rw [SetLike.not_le_iff_exists] at hJ_le
      obtain ⟨r, hr_J, hr_notP⟩ := hJ_le
      -- r ∈ J = Ann(x_d). Decompose r; some component ∉ p.
      have hr_notMem_allP : ¬ ∀ i, (DirectSum.decompose 𝒜 r i : A) ∈ p := by
        intro hall
        apply hr_notP
        rw [← DirectSum.sum_support_decompose 𝒜 r]
        exact Ideal.sum_mem _ (fun i _ => hall i)
      push_neg at hr_notMem_allP
      obtain ⟨k, hrk_notP⟩ := hr_notMem_allP
      -- r_k · x_d = 0 (since r ∈ Ann(x_d) and x_d is scalar multiplication).
      have hrk_kills : (DirectSum.decompose 𝒜 r k : A) *
          (DirectSum.decompose 𝒜 x d : A) = 0 := by
        -- r ∈ J means r · x_d = 0. Its (k+d)-th component is r_k · x_d.
        rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hr_J
        have hr_prod_zero : r * (DirectSum.decompose 𝒜 x d : A) = 0 := hr_J
        have hcomp := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜
          (a := r) (b := (DirectSum.decompose 𝒜 x d : A))
          (i := k) (j := d) (SetLike.coe_mem _)
        rw [hr_prod_zero, DirectSum.decompose_zero] at hcomp
        simp at hcomp
        exact hcomp.symm
      -- Let z := r_k, homogeneous of degree k, not in p, kills x_d.
      set z := (DirectSum.decompose 𝒜 r k : A) with hz_def
      have hz_hom : z ∈ 𝒜 k := SetLike.coe_mem _
      -- Ann(z * x) = p via annihilator_mul_eq_of_prime_notMem.
      have hzx_ann : (⊥ : Submodule A A).colon {z * x} = p :=
        annihilator_mul_eq_of_prime_notMem hp_prime hx_ann hrk_notP
      -- |supp(z * x)| < |supp x| ≤ n.
      have hzx_card : (DirectSum.decompose 𝒜 (z * x)).support.card <
          (DirectSum.decompose 𝒜 x).support.card :=
        support_mul_homog_lt 𝒜 hd_mem hz_hom hrk_kills
      have hzx_card_n : (DirectSum.decompose 𝒜 (z * x)).support.card < n := by
        omega
      -- Apply IH.
      exact IH (DirectSum.decompose 𝒜 (z * x)).support.card hzx_card_n
        (z * x) hzx_ann le_rfl

end GradedAssociatedPrime

end

/-
Copyright: BEI Lean project.

# Graded prime avoidance

For a ℕ-graded commutative ring `A` and a finite family of homogeneous prime
ideals none of which contains the irrelevant ideal `𝒜₊`, we produce a single
homogeneous element of `𝒜₊` avoiding all of them.

This is the graded analogue of `Ideal.subset_union_prime_finite`
(Atiyah-Macdonald 1.11 / Eisenbud 3.3), needed as Step 1 of the Eisenbud
18.3-style generic-linear-form induction closing
`GradedCM.caseC_CM_transfer`.

## Main results

* `GradedPrimeAvoidance.exists_homogeneous_pos_notMem_of_forall_not_le`:
  Given a `Finset` `s` of homogeneous prime ideals of `A`, each strictly
  contained in the irrelevant ideal, there exists a homogeneous element
  of positive degree in `𝒜₊` not contained in any prime of `s`.

## Proof strategy (Bruns–Herzog 1.5.10)

Strong induction on `s.card`:

* Base `s = ∅`: take `ℓ = 0`.
* Step: pick a prime `p₀ ∈ s` that is *minimal* among `s` (so every other
  prime of `s` is not ⊆ `p₀`). By IH on `s \ {p₀}` get `ℓ'` avoiding the
  smaller set. If `ℓ' ∉ p₀`, done.

  Otherwise `ℓ' ∈ p₀`. Build a second homogeneous element `w ∈ 𝒜₊`
  that lies in every `p ∈ s \ {p₀}` but not in `p₀`, by taking a product
  of avoidance witnesses. Combine via the "equal-degree power sum"
  `ℓ = (ℓ')^a + w^b` where `a, b` are chosen so both summands have the
  same positive degree. Then `ℓ ∈ 𝒜₊` and avoids every prime of `s`.
-/

import toMathlib.GradedIrrelevant
import toMathlib.GradedQuotient
import toMathlib.CohenMacaulay.Localization
import toMathlib.CohenMacaulay.Polynomial
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

noncomputable section

namespace GradedPrimeAvoidance

open HomogeneousIdeal DirectSum SetLike

universe u

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

/-! ### Single-prime avoidance: find a homogeneous positive-degree element -/

/-- If the irrelevant ideal `𝒜₊` is not contained in a proper ideal `p`,
then some graded component `𝒜 i` with `i ≥ 1` is not contained in `p`. -/
private lemma exists_pos_degree_component_not_le
    {p : Ideal A} (hp : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p) :
    ∃ i : ℕ, 0 < i ∧ ∃ x ∈ 𝒜 i, x ∉ p := by
  by_contra hcon
  apply hp
  push_neg at hcon
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi_pos x hx_mem
  exact hcon i hi_pos x hx_mem

/-- For a homogeneous prime `p` with `𝒜₊ ⊄ p`, there is a homogeneous
element of positive degree not in `p`. -/
lemma exists_homogeneous_pos_notMem_of_not_le
    {p : Ideal A} (hp : ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p) :
    ∃ x : A, SetLike.IsHomogeneousElem 𝒜 x ∧
      x ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧ x ∉ p := by
  obtain ⟨i, hi_pos, x, hx_mem, hx_notMem⟩ :=
    exists_pos_degree_component_not_le 𝒜 hp
  refine ⟨x, ⟨i, hx_mem⟩, ?_, hx_notMem⟩
  exact HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hi_pos hx_mem

/-! ### Pairwise incomparable reduction -/

/-- Given a nonempty finset of homogeneous primes, there exists a
prime `p₀ ∈ s` that is *minimal* in `s`: every other `q ∈ s` fails to
be contained in `p₀`. -/
private lemma exists_minimal_prime_in_finset
    (s : Finset (Ideal A)) (hne : s.Nonempty)
    (_hprime : ∀ p ∈ s, p.IsPrime) :
    ∃ p₀ ∈ s, ∀ q ∈ s, q ≠ p₀ → ¬ q ≤ p₀ := by
  classical
  haveI : DecidableEq (Ideal A) := Classical.decEq _
  -- Use `Finset.exists_min_image` on `s` ordered by `⊆`-descent, i.e. by
  -- a natural number `(fun p => s.filter (· ≤ p) |>.card)` that is minimal
  -- exactly when `p` is minimal in `s`.
  -- Alternative cleaner approach: use well-foundedness of `⊂` on finsets
  -- of ideals via the Noetherian strong induction. We use a card-based
  -- argument to avoid extra instance requirements.
  let f : Ideal A → ℕ := fun p => (s.filter (· ≤ p)).card
  obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
    s.exists_min_image f hne
  refine ⟨p₀, hp₀_mem, ?_⟩
  intro q hq_mem hq_ne hq_le
  -- q ≤ p₀, so every ideal ≤ q is also ≤ p₀, so f q ≤ f p₀.
  -- Also p₀ ≤ p₀ but p₀ ≰ q (else q = p₀ by antisymm... wait no, only ≤)
  -- actually we need strict: f q < f p₀ because p₀ is in filter for p₀
  -- but if q ≤ p₀ strictly (q ≠ p₀ with q ≤ p₀), then p₀ ≰ q so p₀ ∉ (s.filter (· ≤ q)).
  have hfq_le : f q ≤ f p₀ := by
    apply Finset.card_le_card
    intro r hr
    simp only [Finset.mem_filter] at hr ⊢
    exact ⟨hr.1, hr.2.trans hq_le⟩
  have hp₀_in_filter_p₀ : p₀ ∈ s.filter (· ≤ p₀) := by
    simp [hp₀_mem]
  have hp₀_not_in_filter_q : p₀ ∉ s.filter (· ≤ q) := by
    intro h
    simp only [Finset.mem_filter] at h
    -- p₀ ≤ q and q ≤ p₀ gives p₀ = q by antisymm, contradicting hq_ne.
    exact hq_ne (le_antisymm hq_le h.2)
  have hfq_lt : f q < f p₀ := by
    refine lt_of_le_of_ne hfq_le ?_
    intro heq
    -- Then `(s.filter (· ≤ q)) = (s.filter (· ≤ p₀))` as both have the same
    -- card and the former ⊆ the latter; but p₀ is in the latter not the former.
    have hsub : s.filter (· ≤ q) ⊆ s.filter (· ≤ p₀) := by
      intro r hr
      simp only [Finset.mem_filter] at hr ⊢
      exact ⟨hr.1, hr.2.trans hq_le⟩
    have := Finset.eq_of_subset_of_card_le hsub heq.ge
    exact hp₀_not_in_filter_q (this ▸ hp₀_in_filter_p₀)
  exact absurd (hp₀_min q hq_mem) (not_le.mpr hfq_lt)

/-! ### Building the "in all other primes, not in p₀" witness -/

/-- Given a finite family of homogeneous primes with a designated prime `p₀`
minimal in the family, produce a homogeneous element in every other prime
but not in `p₀`. -/
private lemma exists_homogeneous_prod_mem_all_notMem_minimal
    [DecidableEq (Ideal A)]
    {s : Finset (Ideal A)} {p₀ : Ideal A}
    (hp₀_mem : p₀ ∈ s)
    (hp₀_prime : p₀.IsPrime)
    (hhom : ∀ p ∈ s, p.IsHomogeneous 𝒜)
    (hp₀_min : ∀ q ∈ s, q ≠ p₀ → ¬ q ≤ p₀) :
    ∃ w : A, SetLike.IsHomogeneousElem 𝒜 w ∧
      (∀ q ∈ s.erase p₀, w ∈ q) ∧ w ∉ p₀ := by
  classical
  -- For each q ∈ s.erase p₀, pick homogeneous h_q ∈ q \ p₀ via
  -- `SetLike.not_le_iff_exists` applied to q ≰ p₀, combined with
  -- `Ideal.IsHomogeneous.mem_iff` to extract a homogeneous component ∉ p₀
  -- from any non-element.
  -- Actually, since `q.IsHomogeneous 𝒜` and `q ≰ p₀` means ∃ x ∈ q, x ∉ p₀.
  -- Decompose x into homogeneous components; since p₀ is homogeneous (hhom),
  -- x ∉ p₀ implies some component is ∉ p₀, and that component is in q
  -- (because q is homogeneous).
  -- Then take the product of these homogeneous components over q ∈ s.erase p₀.
  -- The product is homogeneous, in each q, and not in p₀ (prime).
  -- For each q ∈ s.erase p₀, choose a homogeneous element of q not in p₀.
  have hchoose : ∀ q : Ideal A, q ∈ s.erase p₀ → ∃ h : A,
      SetLike.IsHomogeneousElem 𝒜 h ∧ h ∈ q ∧ h ∉ p₀ := by
    intro q hq
    rcases Finset.mem_erase.mp hq with ⟨hq_ne, hq_mem⟩
    have hq_le : ¬ q ≤ p₀ := hp₀_min q hq_mem hq_ne
    have hq_hom : q.IsHomogeneous 𝒜 := hhom q hq_mem
    have hp₀_hom : p₀.IsHomogeneous 𝒜 := hhom p₀ hp₀_mem
    rw [SetLike.not_le_iff_exists] at hq_le
    obtain ⟨x, hx_q, hx_p₀⟩ := hq_le
    rw [hp₀_hom.mem_iff] at hx_p₀
    push_neg at hx_p₀
    obtain ⟨i, hxi_notMem⟩ := hx_p₀
    refine ⟨(DirectSum.decompose 𝒜 x i : A), ⟨i, SetLike.coe_mem _⟩, ?_, hxi_notMem⟩
    exact hq_hom.mem_iff.mp hx_q i
  -- Extract witness functions via Classical.choose.
  let pick : ∀ q : Ideal A, q ∈ s.erase p₀ → A := fun q hq =>
    Classical.choose (hchoose q hq)
  have hpick_hom : ∀ q (hq : q ∈ s.erase p₀),
      SetLike.IsHomogeneousElem 𝒜 (pick q hq) := fun q hq =>
    (Classical.choose_spec (hchoose q hq)).1
  have hpick_mem : ∀ q (hq : q ∈ s.erase p₀), pick q hq ∈ q := fun q hq =>
    (Classical.choose_spec (hchoose q hq)).2.1
  have hpick_notMem : ∀ q (hq : q ∈ s.erase p₀), pick q hq ∉ p₀ := fun q hq =>
    (Classical.choose_spec (hchoose q hq)).2.2
  -- Take the product over q ∈ s.erase p₀ using Finset.attach.
  set P : Finset {q : Ideal A // q ∈ s.erase p₀} := (s.erase p₀).attach with hP_def
  set prodW : A := ∏ q ∈ P, pick q.1 q.2 with hprodW_def
  refine ⟨prodW, ?_, ?_, ?_⟩
  · -- Homogeneous: product of homogeneous elements.
    refine Finset.prod_induction (s := P) (f := fun q => pick q.1 q.2)
      (p := SetLike.IsHomogeneousElem 𝒜) ?_ ?_ ?_
    · intro a b ha hb; exact ha.mul hb
    · exact ⟨0, SetLike.GradedOne.one_mem⟩
    · intro q _; exact hpick_hom q.1 q.2
  · -- In every q ∈ s.erase p₀.
    intro q hq
    exact Ideal.prod_mem q (Finset.mem_attach _ ⟨q, hq⟩) (hpick_mem q hq)
  · -- Not in p₀: each factor is ∉ p₀ and p₀ is prime.
    rw [hp₀_prime.prod_mem_iff]
    push_neg
    intro q _
    exact hpick_notMem q.1 q.2

/-! ### Main theorem -/

/-- **Graded prime avoidance.** Given a finite set `s` of homogeneous prime
ideals in a connected ℕ-graded `K`-algebra `A`, each strictly contained in
the irrelevant ideal `𝒜₊`, there exists a homogeneous element `ℓ ∈ 𝒜₊` not
contained in any prime of `s`. -/
theorem exists_homogeneous_notMem_of_forall_not_le
    (s : Finset (Ideal A))
    (hhom : ∀ p ∈ s, p.IsHomogeneous 𝒜)
    (hprime : ∀ p ∈ s, p.IsPrime)
    (hirr_not_le : ∀ p ∈ s, ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p) :
    ∃ ℓ : A, SetLike.IsHomogeneousElem 𝒜 ℓ ∧
      ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      (∀ p ∈ s, ℓ ∉ p) := by
  classical
  -- Strong induction on `s.card`.
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n IH =>
    match n, hn with
    | 0, hn =>
      rw [Finset.card_eq_zero] at hn
      subst hn
      refine ⟨0, ⟨0, Submodule.zero_mem _⟩, Submodule.zero_mem _, ?_⟩
      intro p hp
      exact absurd hp (Finset.notMem_empty _)
    | k + 1, hn =>
      have hne : s.Nonempty := Finset.card_pos.mp (hn ▸ Nat.succ_pos _)
      -- Pick a minimal prime p₀ in s.
      obtain ⟨p₀, hp₀_mem, hp₀_min⟩ :=
        exists_minimal_prime_in_finset s hne hprime
      haveI hp₀_prime : p₀.IsPrime := hprime p₀ hp₀_mem
      -- Get a homogeneous `u` of positive degree with `u ∉ p₀`.
      obtain ⟨u, ⟨du, hu_mem_du⟩, hu_irr, hu_notMem_p₀⟩ :=
        exists_homogeneous_pos_notMem_of_not_le 𝒜
          (hirr_not_le p₀ hp₀_mem)
      have hdu_pos : 0 < du := by
        -- u ∈ 𝒜 du and u ∈ 𝒜₊; if du = 0 then u ∈ 𝒜 0, so proj₀ u = u.
        -- But u ∈ 𝒜₊ means proj₀ u = 0, so u = 0. Then u ∈ p₀, contradiction.
        rcases Nat.eq_zero_or_pos du with hdu_zero | hdu_pos
        · exfalso
          subst hdu_zero
          apply hu_notMem_p₀
          have hu_zero : u = 0 := by
            have hproj : GradedRing.projZeroRingHom 𝒜 u = u := by
              simp [GradedRing.projZeroRingHom_apply,
                DirectSum.decompose_of_mem_same 𝒜 hu_mem_du]
            have hu_irr' : GradedRing.projZeroRingHom 𝒜 u = 0 := hu_irr
            rw [hproj] at hu_irr'
            exact hu_irr'
          rw [hu_zero]; exact Submodule.zero_mem _
        · exact hdu_pos
      -- Case-split on whether s.erase p₀ is empty.
      by_cases hempty : s.erase p₀ = ∅
      · -- s = {p₀}, use u directly (avoids p₀, in 𝒜₊).
        refine ⟨u, ⟨du, hu_mem_du⟩, hu_irr, ?_⟩
        intro q hq
        have hq_p₀ : q = p₀ := by
          by_contra hne
          have : q ∈ s.erase p₀ := Finset.mem_erase.mpr ⟨hne, hq⟩
          rw [hempty] at this
          exact Finset.notMem_empty q this
        exact hq_p₀ ▸ hu_notMem_p₀
      · -- s.erase p₀ nonempty. Apply IH to it.
        have hne_erase : (s.erase p₀).Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        have hcard : (s.erase p₀).card = k := by
          rw [Finset.card_erase_of_mem hp₀_mem, hn]; rfl
        obtain ⟨ℓ', hℓ'_hom, hℓ'_irr, hℓ'_notMem⟩ :=
          IH k (by omega) (s.erase p₀)
            (fun p hp => hhom p (Finset.mem_of_mem_erase hp))
            (fun p hp => hprime p (Finset.mem_of_mem_erase hp))
            (fun p hp => hirr_not_le p (Finset.mem_of_mem_erase hp))
            hcard
        -- ℓ' ≠ 0 since it avoids some nonempty prime.
        have hℓ'_ne : ℓ' ≠ 0 := by
          intro hz
          obtain ⟨q, hq⟩ := hne_erase
          exact hℓ'_notMem q hq (hz ▸ q.zero_mem)
        -- Thus ℓ' has positive degree.
        obtain ⟨dℓ, hℓ_mem_dℓ⟩ := hℓ'_hom
        have hdℓ_pos : 0 < dℓ := by
          rcases Nat.eq_zero_or_pos dℓ with hdℓ_zero | hdℓ_pos
          · exfalso
            subst hdℓ_zero
            apply hℓ'_ne
            have hproj : GradedRing.projZeroRingHom 𝒜 ℓ' = ℓ' := by
              simp [GradedRing.projZeroRingHom_apply,
                DirectSum.decompose_of_mem_same 𝒜 hℓ_mem_dℓ]
            have hℓ'_irr' : GradedRing.projZeroRingHom 𝒜 ℓ' = 0 := hℓ'_irr
            rw [hproj] at hℓ'_irr'
            exact hℓ'_irr'
          · exact hdℓ_pos
        by_cases hℓ'_p₀ : ℓ' ∈ p₀
        · -- ℓ' ∈ p₀. Build power-sum (ℓ')^du + wu^dℓ where wu ∈ ⋂other primes \ p₀.
          obtain ⟨w, hw_hom, hw_mem_others, hw_notMem_p₀⟩ :=
            exists_homogeneous_prod_mem_all_notMem_minimal 𝒜
              hp₀_mem hp₀_prime hhom hp₀_min
          set wu := w * u with hwu_def
          have hwu_notMem_p₀ : wu ∉ p₀ := by
            intro h
            exact (hp₀_prime.mem_or_mem h).elim hw_notMem_p₀ hu_notMem_p₀
          have hwu_mem_others : ∀ q ∈ s.erase p₀, wu ∈ q := by
            intro q hq; exact Ideal.mul_mem_right _ _ (hw_mem_others q hq)
          -- Degrees: ℓ' ∈ 𝒜 dℓ, u ∈ 𝒜 du; w has some degree dw via hw_hom.
          obtain ⟨dw, hw_mem_dw⟩ := hw_hom
          -- wu = w * u ∈ 𝒜 (dw + du) via GradedMul.
          have hwu_mem_deg : wu ∈ 𝒜 (dw + du) :=
            SetLike.mul_mem_graded hw_mem_dw hu_mem_du
          -- Form ℓ := (ℓ')^(dw + du) + wu^dℓ, both of degree dℓ * (dw + du).
          set N : ℕ := dℓ * (dw + du) with hN_def
          set ℓ : A := ℓ' ^ (dw + du) + wu ^ dℓ with hℓ_def
          have hℓ_pow_mem : ℓ' ^ (dw + du) ∈ 𝒜 N := by
            rw [hN_def, mul_comm]
            exact SetLike.pow_mem_graded (dw + du) hℓ_mem_dℓ
          have hwu_pow_mem : wu ^ dℓ ∈ 𝒜 N := by
            rw [hN_def]
            exact SetLike.pow_mem_graded dℓ hwu_mem_deg
          have hℓ_mem_N : ℓ ∈ 𝒜 N := (𝒜 N).add_mem hℓ_pow_mem hwu_pow_mem
          refine ⟨ℓ, ⟨N, hℓ_mem_N⟩, ?_, ?_⟩
          · -- ℓ ∈ 𝒜₊.
            refine HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 ?_ hℓ_mem_N
            -- N = dℓ * (dw + du) > 0 since dℓ > 0 and dw + du ≥ du > 0.
            exact Nat.mul_pos hdℓ_pos (by omega)
          · -- ℓ avoids every p ∈ s.
            intro p hp
            by_cases hpp₀ : p = p₀
            · -- p = p₀: (ℓ')^(dw+du) ∈ p₀ since ℓ' ∈ p₀; wu^dℓ ∉ p₀.
              subst hpp₀
              intro habs
              have h1 : ℓ' ^ (dw + du) ∈ p := by
                exact Ideal.pow_mem_of_mem p hℓ'_p₀ _ (by omega)
              have h2 : wu ^ dℓ ∉ p := by
                intro habs2
                exact hwu_notMem_p₀ (hp₀_prime.mem_of_pow_mem _ habs2)
              apply h2
              have hsub : ℓ - ℓ' ^ (dw + du) ∈ p := Ideal.sub_mem p habs h1
              have heq : ℓ - ℓ' ^ (dw + du) = wu ^ dℓ := by
                rw [hℓ_def]; ring
              rw [heq] at hsub
              exact hsub
            · -- p ≠ p₀: ℓ' ∉ p; wu ∈ p so wu^dℓ ∈ p.
              have hp_erase : p ∈ s.erase p₀ := Finset.mem_erase.mpr ⟨hpp₀, hp⟩
              have hℓ'_notMem_p : ℓ' ∉ p := hℓ'_notMem p hp_erase
              have hwu_mem_p : wu ∈ p := hwu_mem_others p hp_erase
              haveI hp_prime : p.IsPrime := hprime p hp
              intro habs
              have h1 : ℓ' ^ (dw + du) ∉ p := by
                intro habs1
                exact hℓ'_notMem_p (hp_prime.mem_of_pow_mem _ habs1)
              apply h1
              have h2 : wu ^ dℓ ∈ p := Ideal.pow_mem_of_mem p hwu_mem_p _ (by omega)
              have hsub : ℓ - wu ^ dℓ ∈ p := Ideal.sub_mem p habs h2
              have heq : ℓ - wu ^ dℓ = ℓ' ^ (dw + du) := by
                rw [hℓ_def]; ring
              rw [heq] at hsub
              exact hsub
        · -- ℓ' ∉ p₀; ℓ' itself works.
          refine ⟨ℓ', ⟨dℓ, hℓ_mem_dℓ⟩, hℓ'_irr, ?_⟩
          intro p hp
          by_cases hpp₀ : p = p₀
          · exact hpp₀ ▸ hℓ'_p₀
          · exact hℓ'_notMem p (Finset.mem_erase.mpr ⟨hpp₀, hp⟩)

/-! ### Step 2: Generic homogeneous NZD existence

We apply the graded prime avoidance lemma to the homogeneous cores of the
associated primes of `A`. Using the fact that a homogeneous element lies
in an ideal iff it lies in the ideal's homogeneous core, we transfer
avoidance of homogeneous cores back to avoidance of the original
associated primes, producing a homogeneous non-zero-divisor. -/

section NZD

variable [IsNoetherianRing A]

/-- **Generic homogeneous NZD existence.** Let `A` be a ℕ-graded Noetherian
`K`-algebra, and assume no associated prime of `A` contains the irrelevant
ideal `𝒜₊`. Then there exists a homogeneous `ℓ ∈ 𝒜₊` that is a non-zero-
divisor on `A`. -/
theorem exists_homogeneous_nonZeroDivisor
    (hAss : ∀ p ∈ associatedPrimes A A,
        ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p) :
    ∃ ℓ : A, SetLike.IsHomogeneousElem 𝒜 ℓ ∧
      ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      ℓ ∈ nonZeroDivisors A := by
  classical
  -- Ass(A) is finite and bundles to a `Finset`.
  have hfin : (associatedPrimes A A).Finite := associatedPrimes.finite A A
  set Ass : Finset (Ideal A) := hfin.toFinset with hAss_def
  -- Map each associated prime to its homogeneous core.
  set S : Finset (Ideal A) := Ass.image (fun p => (p.homogeneousCore 𝒜).toIdeal)
    with hS_def
  -- Each element of `S` is a homogeneous prime.
  have hS_hom : ∀ q ∈ S, q.IsHomogeneous 𝒜 := by
    intro q hq
    rw [hS_def, Finset.mem_image] at hq
    obtain ⟨p, _, rfl⟩ := hq
    exact (p.homogeneousCore 𝒜).isHomogeneous
  have hS_prime : ∀ q ∈ S, q.IsPrime := by
    intro q hq
    rw [hS_def, Finset.mem_image] at hq
    obtain ⟨p, hp_ass, rfl⟩ := hq
    rw [hAss_def, Set.Finite.mem_toFinset] at hp_ass
    have hp_prime : p.IsPrime :=
      (AssociatePrimes.mem_iff.mp hp_ass).isPrime
    exact hp_prime.homogeneousCore
  have hS_not_le : ∀ q ∈ S,
      ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ q := by
    intro q hq hirr_le
    rw [hS_def, Finset.mem_image] at hq
    obtain ⟨p, hp_ass, rfl⟩ := hq
    rw [hAss_def, Set.Finite.mem_toFinset] at hp_ass
    -- 𝒜₊ ≤ homogeneousCore p implies 𝒜₊ ≤ p (via homogeneousCore ≤ p).
    apply hAss p hp_ass
    exact hirr_le.trans (p.toIdeal_homogeneousCore_le 𝒜)
  -- Apply Step 1.
  obtain ⟨ℓ, hℓ_hom, hℓ_irr, hℓ_notMem⟩ :=
    exists_homogeneous_notMem_of_forall_not_le 𝒜 S hS_hom hS_prime hS_not_le
  refine ⟨ℓ, hℓ_hom, hℓ_irr, ?_⟩
  -- ℓ ∈ nonZeroDivisors A iff ℓ ∉ ⋃ Ass(A).
  by_contra hnot
  have hℓ_compl : ℓ ∈ (↑(nonZeroDivisors A) : Set A)ᶜ := hnot
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors A] at hℓ_compl
  rw [Set.mem_iUnion₂] at hℓ_compl
  obtain ⟨p, hp_ass, hℓ_p⟩ := hℓ_compl
  -- Since ℓ is homogeneous and ℓ ∈ p, ℓ ∈ homogeneousCore p.
  have hℓ_core : ℓ ∈ (p.homogeneousCore 𝒜).toIdeal :=
    Ideal.mem_homogeneousCore_of_homogeneous_of_mem hℓ_hom hℓ_p
  -- But ℓ ∉ any q ∈ S; the homogeneous core of p is in S.
  have hp_mem_S : (p.homogeneousCore 𝒜).toIdeal ∈ S := by
    rw [hS_def]
    refine Finset.mem_image.mpr ⟨p, ?_, rfl⟩
    rw [hAss_def, Set.Finite.mem_toFinset]
    exact hp_ass
  exact hℓ_notMem _ hp_mem_S hℓ_core

end NZD

/-! ### Step 3: Descent to the quotient by a homogeneous element

Given a homogeneous `ℓ` of positive degree in a connected graded Noetherian
`K`-algebra `A`, the quotient `A ⧸ ⟨ℓ⟩` inherits a connected graded
Noetherian `K`-algebra structure via `toMathlib.GradedQuotient`. This
section packages the necessary facts for the induction on dim in Case C. -/

section Descent

open GradedQuotient

/-- The principal ideal generated by a homogeneous element is homogeneous. -/
lemma isHomogeneous_span_singleton_of_homogeneous
    {ℓ : A} (hℓ : SetLike.IsHomogeneousElem 𝒜 ℓ) :
    (Ideal.span ({ℓ} : Set A)).IsHomogeneous 𝒜 :=
  Ideal.homogeneous_span 𝒜 _ (fun _ hx => by rwa [Set.mem_singleton_iff.mp hx])

/-- The graded ring structure on `A ⧸ ⟨ℓ⟩` induced from a homogeneous `ℓ`. -/
noncomputable def quotientSpanSingletonGrading
    {ℓ : A} (hℓ : SetLike.IsHomogeneousElem 𝒜 ℓ) :
    GradedRing (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span {ℓ})) :=
  GradedQuotient.gradedRing 𝒜 _ (isHomogeneous_span_singleton_of_homogeneous 𝒜 hℓ)

-- Silences a false-positive `unused variable hℓ`: the lint does not
-- detect the use in the `letI` decorator on the `GradedRing` instance below.
set_option linter.unusedVariables false in
/-- **Connected graded transfer to quotient.** If the ambient grading `𝒜` is
connected and `ℓ` is homogeneous, then the induced grading on `A ⧸ ⟨ℓ⟩`
is also connected. -/
lemma connectedGraded_quotient
    (h𝒜₀ : GradedIrrelevant.ConnectedGraded 𝒜)
    {ℓ : A} (hℓ : SetLike.IsHomogeneousElem 𝒜 ℓ) :
    @GradedIrrelevant.ConnectedGraded K (A ⧸ Ideal.span ({ℓ} : Set A)) _ _ _
      (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span {ℓ})) := by
  classical
  haveI : GradedRing (GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span {ℓ})) :=
    GradedQuotient.gradedRing 𝒜 _
      (isHomogeneous_span_singleton_of_homogeneous 𝒜 hℓ)
  -- Every element of the degree-0 piece is the image of an element of 𝒜 0,
  -- which in turn is `algebraMap K A k` for some `k : K`. Its image in the
  -- quotient equals `algebraMap K (A ⧸ ⟨ℓ⟩) k`.
  intro x hx
  simp only [GradedQuotient.gradedQuotientPiece, Submodule.mem_map] at hx
  obtain ⟨a, ha_mem, ha_eq⟩ := hx
  -- `a ∈ 𝒜 0` gives `algebraMap K A k = a` by connectedness.
  obtain ⟨k, hk⟩ := h𝒜₀ a ha_mem
  refine ⟨k, ?_⟩
  rw [← ha_eq, ← hk]
  rfl

/-- The image of `𝒜 i` in `A ⧸ ⟨ℓ⟩` under the quotient map equals the induced
graded piece `gradedQuotientPiece 𝒜 ⟨ℓ⟩ i`. This is essentially by definition
but useful as a named rewrite target. -/
lemma gradedQuotientPiece_span_singleton_eq_map
    (ℓ : A) (i : ℕ) :
    GradedQuotient.gradedQuotientPiece 𝒜 (Ideal.span ({ℓ} : Set A)) i =
      (𝒜 i).map ((Ideal.Quotient.mkₐ K (Ideal.span ({ℓ} : Set A))).toLinearMap) :=
  rfl

end Descent

/-! ### Step 4 prerequisite: CM bridges to Ass(A)

If `A_{𝒜₊}` is Cohen–Macaulay local of positive Krull dimension, then
the irrelevant ideal `𝒜₊` is not contained in any associated prime of
`A`. This is the hypothesis needed to apply
`exists_homogeneous_nonZeroDivisor` inside the Route B induction. -/

section CMBridge

open IsLocalRing

variable [IsNoetherianRing A]

/-- **CM + positive dim ⟹ `𝒜₊ ∉ Ass(A)`.** For a connected ℕ-graded Noetherian
`K`-algebra `A`, if `A_{𝒜₊}` is Cohen–Macaulay local of strictly positive
Krull dimension, then no associated prime of `A` contains the irrelevant
ideal. -/
theorem irrelevant_notLe_associatedPrime_of_isCohenMacaulay_dim_pos
    [Nontrivial A]
    (h𝒜₀ : GradedIrrelevant.ConnectedGraded 𝒜)
    (hCM : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (hdim : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      (0 : WithBot ℕ∞) < ringKrullDim
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    ∀ p ∈ associatedPrimes A A,
      ¬ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p := by
  haveI hm_max : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsMaximal :=
    GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime := hm_max.isPrime
  set m := (HomogeneousIdeal.irrelevant 𝒜).toIdeal with hm_def
  -- Apply the CM theorem: there is a regular element in the maximal ideal
  -- of `A_m`.
  have hmax_pos : (0 : WithBot ℕ∞) <
      Ideal.height (IsLocalRing.maximalIdeal (Localization.AtPrime m)) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact hdim
  obtain ⟨x, hx_max, _, hxreg⟩ :=
    exists_smulRegular_mem_of_isCohenMacaulayLocalRing
      (IsLocalRing.maximalIdeal (Localization.AtPrime m)) hmax_pos
  -- Suppose p ∈ Ass(A) with m ≤ p. Then p = m (primality + maximality of m).
  intro p hp_ass hm_le
  haveI hp_prime : p.IsPrime := hp_ass.isPrime
  have hp_eq : p = m := by
    have := hm_max.eq_of_le hp_prime.ne_top hm_le
    exact this.symm
  -- Hence m ∈ Ass(A). By the localization lemma, maxId(A_m) ∈ Ass(A_m-localized module).
  subst hp_eq
  have hm_ass_loc :
      IsLocalRing.maximalIdeal (Localization.AtPrime m) ∈
        associatedPrimes (Localization.AtPrime m) (LocalizedModule.AtPrime m A) :=
    Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes
      hp_ass
  -- maxIdeal is the annihilator of some element z.
  rw [AssociatePrimes.mem_iff] at hm_ass_loc
  obtain ⟨_, z, hz_ann⟩ := hm_ass_loc
  -- Since maxIdeal ≠ ⊤, z ≠ 0 (else annihilator = ⊤).
  have hz_ne : z ≠ 0 := by
    intro hz_zero
    apply IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime m) |>.ne_top
    rw [hz_ann, hz_zero]
    simp [Submodule.colon]
  -- x ∈ maxIdeal = Ann(z), so x • z = 0.
  have hxz : x • z = 0 := by
    have hxann : x ∈ (⊥ : Submodule _ _).colon {z} := hz_ann ▸ hx_max
    rw [Submodule.mem_colon_singleton] at hxann
    simpa using hxann
  -- But x is R-regular on A_m, so z = 0. Contradiction with hz_ne.
  apply hz_ne
  apply hxreg
  simpa using hxz

/-- **Combined bridge:** CM-at-`𝒜₊` + positive dim gives a homogeneous NZD
of positive degree in `𝒜₊`. This is the complete Route B "pick an NZD"
step, combining the bridge lemma with `exists_homogeneous_nonZeroDivisor`. -/
theorem exists_homogeneous_nonZeroDivisor_of_isCohenMacaulay_dim_pos
    [Nontrivial A]
    (h𝒜₀ : GradedIrrelevant.ConnectedGraded 𝒜)
    (hCM : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (hdim : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      (0 : WithBot ℕ∞) < ringKrullDim
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    ∃ ℓ : A, SetLike.IsHomogeneousElem 𝒜 ℓ ∧
      ℓ ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal ∧
      ℓ ∈ nonZeroDivisors A :=
  exists_homogeneous_nonZeroDivisor 𝒜
    (irrelevant_notLe_associatedPrime_of_isCohenMacaulay_dim_pos 𝒜 h𝒜₀ hCM hdim)

end CMBridge

/-! ### Step 4 (ℓ ∈ p case): CM descent from the graded quotient to `A_p` -/

section DescentCase

open IsLocalRing

variable [IsNoetherianRing A]

/-- **Descent case `ℓ ∈ p`**: given a non-zero-divisor `ℓ ∈ p` in `A`, if
`(A ⧸ ⟨ℓ⟩)_{p/⟨ℓ⟩}` is Cohen–Macaulay, then `A_p` is Cohen–Macaulay. This is
the "easy half" of the case-split in the Route B induction. -/
theorem isCohenMacaulayLocalRing_of_quotient_cm_of_mem
    {ℓ : A} (hℓ_reg : IsSMulRegular A ℓ)
    (p : Ideal A) [hp_prime : p.IsPrime] (hℓ_p : ℓ ∈ p)
    (hCM_quot :
      haveI : (p.map (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime
          (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_p)
      IsCohenMacaulayLocalRing
        (Localization.AtPrime
          (p.map (Ideal.Quotient.mk (Ideal.span ({ℓ} : Set A)))))) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  classical
  set I := Ideal.span ({ℓ} : Set A) with hI_def
  have hI_le_p : I ≤ p := by
    rw [hI_def, Ideal.span_le, Set.singleton_subset_iff]; exact hℓ_p
  set p' : Ideal (A ⧸ I) := p.map (Ideal.Quotient.mk I) with hp'_def
  haveI hp'_prime : p'.IsPrime := Ideal.isPrime_map_quotientMk_of_isPrime hI_le_p
  have hp'_comap : p'.comap (Ideal.Quotient.mk I) = p := by
    rw [hp'_def, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hI_le_p
  -- Image of `ℓ` is in the maximal ideal of `Localization.AtPrime p`.
  have hℓ_max : algebraMap A (Localization.AtPrime p) ℓ ∈
      maximalIdeal (Localization.AtPrime p) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ hℓ_p
  -- Image of `ℓ` is regular on `Localization.AtPrime p` (flat localization).
  have hℓ_reg_loc :
      IsSMulRegular (Localization.AtPrime p) (algebraMap A _ ℓ) := hℓ_reg.of_flat
  -- Transfer CM back via the ring isomorphism
  -- `QuotSMulTop (algebraMap A A_p ℓ) A_p ≃+* (A/⟨ℓ⟩)_{p'}`.
  haveI : IsNoetherianRing (Localization.AtPrime p') :=
    IsLocalization.isNoetherianRing p'.primeCompl _ inferInstance
  haveI hloc := quotSMulTopLocalRing hℓ_max
  haveI hCM_qst :
      IsCohenMacaulayLocalRing
        (QuotSMulTop (algebraMap A (Localization.AtPrime p) ℓ)
          (Localization.AtPrime p)) :=
    isCohenMacaulayLocalRing_of_ringEquiv' hCM_quot
      (quotSMulTopLocalizationEquiv_of_mem hℓ_p hp'_comap).symm
  -- Apply converse CM transfer to conclude.
  exact isCohenMacaulayLocalRing_of_regular_quotient hℓ_reg_loc hℓ_max
    hCM_qst.depth_eq_dim

end DescentCase

/-! ### Strengthened Case B: CM at `𝒜₊` transfers to any prime `p ⊆ 𝒜₊`

The existing `isCohenMacaulayLocalRing_atPrime_of_isHomogeneous` uses
homogeneity only to derive `p ⊆ 𝒜₊`. For arbitrary (possibly
non-homogeneous) primes `p ⊆ 𝒜₊`, the same argument applies: `A_p` is
a localization of the CM local ring `A_{𝒜₊}`, and "CM localizes"
concludes the proof. -/

section CaseBStrong

variable [IsNoetherianRing A] [Nontrivial A]

/-- **Strengthened Case B**: CM at the irrelevant ideal transfers to any
prime ideal contained in `𝒜₊`, homogeneous or not. This extends
`GradedCM.isCohenMacaulayLocalRing_atPrime_of_isHomogeneous` to drop the
homogeneity assumption, requiring only `p ⊆ 𝒜₊` directly. -/
theorem isCohenMacaulayLocalRing_atPrime_of_le_irrelevant
    (h𝒜₀ : GradedIrrelevant.ConnectedGraded 𝒜)
    (hCM : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (p : Ideal A) [hp_prime : p.IsPrime]
    (hpm : p ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime :=
    (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
  set Am := Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  have hdisj : Disjoint
      (↑(HomogeneousIdeal.irrelevant 𝒜).toIdeal.primeCompl : Set A) (↑p) := by
    rw [Set.disjoint_left]; intro x hx hxp; exact hx (hpm hxp)
  set p' : Ideal Am := Ideal.map (algebraMap A Am) p
  haveI hp' : p'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ Am p hp_prime hdisj
  have hcomap : p'.comap (algebraMap A Am) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint _ Am hp_prime hdisj
  haveI : IsCohenMacaulayLocalRing Am := hCM
  haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p') :=
    isCohenMacaulayLocalRing_localization_atPrime p'
  haveI : (p'.comap (algebraMap A Am)).IsPrime := hcomap ▸ hp_prime
  have hCM_q : IsCohenMacaulayLocalRing
      (Localization.AtPrime (p'.comap (algebraMap A Am))) :=
    isCohenMacaulayLocalRing_of_ringEquiv'
      (show IsCohenMacaulayLocalRing (Localization.AtPrime p') from inferInstance)
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.primeCompl p').symm.toRingEquiv
  have hpc : (p'.comap (algebraMap A Am)).primeCompl = p.primeCompl := by
    ext x
    simp only [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk]
    rw [hcomap]
  exact cast (show IsCohenMacaulayLocalRing
      (Localization.AtPrime (p'.comap (algebraMap A Am))) =
      IsCohenMacaulayLocalRing (Localization.AtPrime p) by
      change IsCohenMacaulayLocalRing
          (Localization (p'.comap (algebraMap A Am)).primeCompl) =
        IsCohenMacaulayLocalRing (Localization p.primeCompl)
      rw [hpc]) hCM_q

end CaseBStrong

end GradedPrimeAvoidance

end

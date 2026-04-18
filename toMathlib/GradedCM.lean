/-
Copyright: BEI Lean project.

# Graded local-to-global Cohen–Macaulay theorem (Bruns–Herzog 2.1.27)

For a connected ℕ-graded Noetherian `K`-algebra `A` with `𝒜 0 = K` a field and
irrelevant ideal `𝒜₊`, if `A` localized at `𝒜₊` is Cohen–Macaulay local, then
`A` is Cohen–Macaulay globally (i.e. `A_p` is CM local for every prime `p`).

## Proof strategy

Let `m := 𝒜₊`, which is a maximal ideal (by `GradedIrrelevant.irrelevant_isMaximal`).
For an arbitrary prime `p` of `A` we need to show `A_p` is CM.

* **Case A (`p = m`)**: given as hypothesis.

* **Case B (`p` homogeneous)**: By `GradedIrrelevant.homogeneousCore_le_irrelevant`
  (applied to `p = p.homogeneousCore 𝒜` since `p` is homogeneous), we have
  `p ≤ m`. Hence `p` is disjoint from `m.primeCompl`, so `p.map (algebraMap A A_m)`
  is a prime `p'` of `A_m` with `comap p' = p`. "CM localizes"
  (`isCohenMacaulayLocalRing_localization_atPrime`) gives
  `IsCohenMacaulayLocalRing ((A_m)_{p'})`, and the canonical isomorphism
  `(A_m)_{p'} ≃ A_p` transports CM back.

* **Case C (`p` non-homogeneous)**: The classical argument uses the homogeneous
  core `p* := p.homogeneousCore 𝒜`, which is prime (by `Ideal.IsPrime.homogeneousCore`)
  and contained in `m`. One picks a homogeneous element `f_n ∉ p*` obtained from
  the top-degree non-vanishing homogeneous component of an element of `p ∖ p*`,
  then uses inversion of `f_n` to build a CM transfer between `A_p` and a
  localization of `A_{p*}`. We isolate this key step as
  `isCohenMacaulayLocalRing_nonhomogeneous_of_cm_at_irrelevant`.
-/

import toMathlib.GradedIrrelevant
import toMathlib.CohenMacaulay.Polynomial
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Graded CM local-to-global

## Main result

* `isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant`: connected
  ℕ-graded CM at the irrelevant ideal implies globally CM.
-/

noncomputable section

open IsLocalRing HomogeneousIdeal GradedIrrelevant

universe u

namespace GradedCM

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A] [Nontrivial A]
variable [IsNoetherianRing A]
variable (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

/-! ### Small instance helper -/

section SmallInstance

/-- `Small.{u} A` is automatic when `A : Type u` via `small_self`. -/
instance (priority := 100) small_self_cm : Small.{u} A := small_self A

end SmallInstance

/-! ### Irrelevant ideal is prime (and maximal) -/

section IrrelevantPrime

omit [IsNoetherianRing A] in
/-- Under the connected-graded hypothesis, the irrelevant ideal is maximal,
hence prime. -/
private lemma irrelevant_isPrime (h𝒜₀ : ConnectedGraded 𝒜) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime :=
  (irrelevant_isMaximal 𝒜 h𝒜₀).isPrime

end IrrelevantPrime

/-! ### Case A: prime equal to the irrelevant ideal -/

-- Case A is trivially discharged by the hypothesis `hCM`. It is absorbed into
-- the homogeneous branch of the main theorem, which covers every prime with
-- `p.IsHomogeneous 𝒜` (the irrelevant ideal is itself homogeneous, so
-- `p = 𝒜₊` falls under Case B).

/-! ### Case B: homogeneous primes -/

section CaseB

omit [Nontrivial A] [IsNoetherianRing A] in
/-- A homogeneous proper ideal is contained in the irrelevant ideal. This is
the version stated for an ideal `p` equal to its homogeneous core. -/
private lemma le_irrelevant_of_isHomogeneous
    (h𝒜₀ : ConnectedGraded 𝒜)
    {p : Ideal A} (hp_prime : p.IsPrime) (hp_hom : p.IsHomogeneous 𝒜) :
    p ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := by
  have hp_ne : p ≠ ⊤ := hp_prime.ne_top
  have hcore : (p.homogeneousCore 𝒜).toIdeal = p :=
    hp_hom.toIdeal_homogeneousCore_eq_self
  have h := homogeneousCore_le_irrelevant 𝒜 h𝒜₀ p hp_ne
  rw [hcore] at h
  exact h

/-- Case B — homogeneous primes: CM at `m := 𝒜₊` transfers to any homogeneous
prime `p`, by the tower `A → A_m → A_p`. -/
private theorem isCohenMacaulayLocalRing_atPrime_of_isHomogeneous
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := irrelevant_isPrime 𝒜 h𝒜₀
      IsCohenMacaulayLocalRing
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (p : Ideal A) [hp_prime : p.IsPrime]
    (hp_hom : p.IsHomogeneous 𝒜) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime :=
    irrelevant_isPrime 𝒜 h𝒜₀
  -- `p ≤ 𝒜₊`
  have hpm : p ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    le_irrelevant_of_isHomogeneous 𝒜 h𝒜₀ hp_prime hp_hom
  -- `(𝒜₊).primeCompl` is disjoint from `p`
  set Am := Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal
  have hdisj : Disjoint
      (↑(HomogeneousIdeal.irrelevant 𝒜).toIdeal.primeCompl : Set A) (↑p) := by
    rw [Set.disjoint_left]; intro x hx hxp; exact hx (hpm hxp)
  -- `p' := p.map (algebraMap A Am)` is a prime of `Am` with comap = p
  set p' : Ideal Am := Ideal.map (algebraMap A Am) p
  haveI hp' : p'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ Am p hp_prime hdisj
  have hcomap : p'.comap (algebraMap A Am) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint _ Am hp_prime hdisj
  haveI : IsCohenMacaulayLocalRing Am := hCM
  -- CM localizes: `(Am)_{p'}` is CM local
  haveI : IsCohenMacaulayLocalRing (Localization.AtPrime p') :=
    isCohenMacaulayLocalRing_localization_atPrime p'
  -- Transport via `(Am)_{p'} ≃ A_{comap p'} = A_p`.
  haveI : (p'.comap (algebraMap A Am)).IsPrime := hcomap ▸ hp_prime
  have hCM_q : IsCohenMacaulayLocalRing
      (Localization.AtPrime (p'.comap (algebraMap A Am))) :=
    isCohenMacaulayLocalRing_of_ringEquiv'
      (show IsCohenMacaulayLocalRing (Localization.AtPrime p') from inferInstance)
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
        (HomogeneousIdeal.irrelevant 𝒜).toIdeal.primeCompl p').symm.toRingEquiv
  -- `q.primeCompl = p.primeCompl`, so `Localization.AtPrime q` and
  -- `Localization.AtPrime p` are the same type.
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

end CaseB

/-! ### Case C: non-homogeneous primes

The classical argument (Bruns–Herzog 1.5.8 / 2.1.27) goes as follows. Let
`p* := p.homogeneousCore 𝒜`. Then `p*` is prime (since `p` is) and
`p* ⊆ m := 𝒜₊`. If `p` is non-homogeneous, pick `f ∈ p, f ∉ p*`. Decompose
`f = Σ f_i` with `f_i ∈ 𝒜 i` and take the top-degree `f_n ∉ p`; then `f_n`
is homogeneous of positive degree, unit in `A_p`, and the localization of
`A` at `p` agrees with the localization of the *homogeneous* localization
`A_{(p*)}` (= the ring of degree-zero elements in `A[f_n⁻¹]` etc.) at an
appropriate prime. The CM of `A_m` then propagates down to `A_p` through
`A_{p*}` via "CM localizes" twice, and a ring isomorphism.

We isolate the critical step as a single key sub-lemma. Supporting
purely-graded-theoretic lemmas (which have no CM content) are proved
outright in this section.
-/

section CaseC

/-! #### Supporting graded-theoretic lemmas -/

omit [Nontrivial A] [IsNoetherianRing A] in
/-- The homogeneous core of a prime ideal is prime. A thin wrapper around
`Ideal.IsPrime.homogeneousCore`. -/
private lemma isPrime_homogeneousCore (p : Ideal A) [hp : p.IsPrime] :
    (p.homogeneousCore 𝒜).toIdeal.IsPrime :=
  hp.homogeneousCore (𝒜 := 𝒜)

omit [Nontrivial A] [IsNoetherianRing A] in
/-- The homogeneous core of a prime ideal is a subset of the original prime. -/
private lemma homogeneousCore_le (p : Ideal A) :
    (p.homogeneousCore 𝒜).toIdeal ≤ p := p.toIdeal_homogeneousCore_le 𝒜

omit [Nontrivial A] [IsNoetherianRing A] in
/-- The homogeneous core is strictly smaller than a non-homogeneous ideal. -/
private lemma homogeneousCore_lt_of_not_isHomogeneous (p : Ideal A)
    (hp_not_hom : ¬ p.IsHomogeneous 𝒜) :
    (p.homogeneousCore 𝒜).toIdeal < p := by
  refine lt_of_le_of_ne (homogeneousCore_le 𝒜 p) ?_
  intro h
  apply hp_not_hom
  rw [Ideal.IsHomogeneous.iff_eq]
  exact h

omit [Nontrivial A] [IsNoetherianRing A] in
/-- For a non-homogeneous prime `p`, there exists an element of `p` not in its
homogeneous core `p*`. This is the starting point of the Case C argument:
decompose this element into homogeneous components and locate a
positive-degree component outside `p`. -/
private lemma exists_notMem_homogeneousCore (p : Ideal A)
    (hp_not_hom : ¬ p.IsHomogeneous 𝒜) :
    ∃ f ∈ p, f ∉ (p.homogeneousCore 𝒜).toIdeal := by
  have hlt := homogeneousCore_lt_of_not_isHomogeneous 𝒜 p hp_not_hom
  exact SetLike.exists_of_lt hlt

omit [Nontrivial A] [IsNoetherianRing A] in
/-- If all homogeneous components of an element `f` lie in a prime ideal `p`,
then `f` itself lies in `p`. (This follows because `p` is closed under finite
sums.) -/
private lemma mem_of_decomposition_mem (p : Ideal A) (f : A)
    (hall : ∀ i, (DirectSum.decompose 𝒜 f i : A) ∈ p) :
    f ∈ p := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 f]
  exact Ideal.sum_mem _ fun i _ => hall i

omit [Nontrivial A] [IsNoetherianRing A] in
/-- If every homogeneous component of `f` lies in `p`, then each component in
fact lies in `p.homogeneousCore 𝒜` (because the components are homogeneous
and in `p`). Together with the decomposition into components, this gives
the contrapositive of "there is some component outside `p.homogeneousCore`". -/
private lemma homogeneousCore_component_of_mem (p : Ideal A) (f : A)
    (i : ℕ) (hfi_p : (DirectSum.decompose 𝒜 f i : A) ∈ p) :
    (DirectSum.decompose 𝒜 f i : A) ∈ (p.homogeneousCore 𝒜).toIdeal := by
  refine Ideal.mem_homogeneousCore_of_homogeneous_of_mem ?_ hfi_p
  exact ⟨i, SetLike.coe_mem _⟩

omit [Nontrivial A] [IsNoetherianRing A] in
/-- **Key homogeneous selection**: given a non-homogeneous prime `p` of `A`,
there exists a homogeneous element `x` which is *not* in `p*` — witnessed by
one of the homogeneous components of some `f ∈ p ∖ p*`. Moreover `x ∉ p`
(the top-degree component still sitting outside `p`). -/
private lemma exists_homogeneous_notMem_of_not_isHomogeneous
    (p : Ideal A) [p.IsPrime] (hp_not_hom : ¬ p.IsHomogeneous 𝒜) :
    ∃ (i : ℕ) (x : A), x ∈ 𝒜 i ∧ x ∉ p := by
  classical
  -- Pick `f ∈ p ∖ p*`.
  obtain ⟨f, hfp, hfCore⟩ := exists_notMem_homogeneousCore 𝒜 p hp_not_hom
  -- If every component of `f` lay in `p`, it would lie in `p*`, contradiction.
  by_contra! hall
  apply hfCore
  -- Show `f ∈ p*` by showing each homogeneous component lies in `p*`.
  have hcomp_core : ∀ i, (DirectSum.decompose 𝒜 f i : A) ∈
      (p.homogeneousCore 𝒜).toIdeal := by
    intro i
    have hp_i : (DirectSum.decompose 𝒜 f i : A) ∈ p :=
      hall i _ (SetLike.coe_mem _)
    exact homogeneousCore_component_of_mem 𝒜 p f i hp_i
  exact mem_of_decomposition_mem 𝒜 (p.homogeneousCore 𝒜).toIdeal f hcomp_core

/-! #### Case C — isolated key gap

This is the genuinely hard mathematical content of the graded
local-to-global Cohen–Macaulay theorem (Bruns–Herzog 2.1.27): for a
*non-homogeneous* prime `p` we cannot reduce to Case B by a localisation
trick alone.

##### Why the naive "further localisation" approach fails

Write `p* := p.homogeneousCore 𝒜`. Then `p* ⊆ p`, hence
`p.primeCompl ⊆ p*.primeCompl`, so the canonical *direction* of the
algebra map is `A_p → A_{p*}` (because `A_{p*}` inverts more elements than
`A_p`). In particular `A_{p*}` is a localisation of `A_p`, **not** the
other way round; the localisation criterion `CM localizes` therefore
transports CM *out of* `A_p` into `A_{p*}`, exactly the wrong direction.

A previous attempt at this file claimed "express `A_p` as a localisation
of `A_{p*}`" using a homogeneous element `x ∉ p`. The argument was wrong:
to invert a generic `s ∈ p.primeCompl` inside `A_{p*}` one would need
`s ∉ p*`, but a non-homogeneous `s ∉ p` may very well have all of its
homogeneous components in `p*`, in which case `s ∈ p*` and `s` is not a
unit in `A_{p*}`. The graded-decomposition argument only produces *one*
homogeneous component outside `p` (and hence outside `p*`); it does **not**
give an algebra map `A_{p*} → A_p`.

##### What the classical proof actually uses

Bruns–Herzog 1.5.8 / 2.1.27 use the `*-local` theory of graded rings.
The relevant facts (none of which are in Mathlib v4.28) are:

* `*-depth` of a graded module agrees with ordinary depth at the irrelevant
  ideal, and one has the dimension/depth identity
  `depth A_p + dim(A_p / p A_p) = dim A_{p*} / p* A_{p*} + depth A_{p*}`.
* For a finitely generated graded `K`-algebra one further has
  `dim A_p = dim A_{p*} + tr.deg(κ(p) / κ(p*))`, where `κ(p) := A_p / p A_p`.
* Combining the two gives `depth A_p = dim A_p` from `depth A_{p*} = dim A_{p*}`.

Each of these requires building substantial graded commutative algebra
infrastructure (graded depth, `*-Cohen–Macaulayness`, transcendence-degree
estimates over residue fields, fibre dimension formulas) that is currently
not present in `toMathlib/` or upstream Mathlib.

##### Status of the sorry below

The sorry stated as `caseC_CM_transfer` is therefore *not* a thin
ring-theoretic gap that one could close with a small follow-up lemma; it
encapsulates the entire Bruns–Herzog 2.1.27 case-C content. We retain it
here as a single, clearly-named placeholder so that:

* the homogeneous (Case B) branch and the rest of the file remain valid;
* downstream consumers can still mention the global theorem, with the
  understanding that the non-homogeneous prime case is the open mathematical
  obligation;
* future work can attack the gap directly (or pivot to a different strategy
  for the BEI application — e.g. proving the specific HH bipartite quotient
  is globally CM by Stanley–Reisner / Reisner-criterion methods, rather
  than going through the general graded LTG theorem).

##### Strategies considered for closing the sorry

1. **Homogeneous-element unit trick (`A[1/f_n]`)** — direction problem, see
   above. Not viable as stated.
2. **`*-local` depth–dimension identity** — needs ~400–800 LOC of new
   infrastructure (graded depth, fibre dimension), not in Mathlib v4.28.
3. **Graded Noether normalisation + finite-extension CM transfer** — the
   ungraded version `Mathlib.RingTheory.NoetherNormalization.exists_finite_inj_algHom_of_fg`
   is available, but the graded refinement (parameters `θ_i` homogeneous)
   and CM-transfer along finite extensions are not in Mathlib; the latter
   alone is also several hundred LOC.
4. **Application-specific Stanley–Reisner argument** — bypasses the LTG
   theorem entirely and proves global CM directly for the HH bipartite
   quotient using monomial-ideal / shellability methods. This is the
   recommended pivot for the BEI project; it does not close the sorry
   here but makes the sorry irrelevant for the downstream consumer.
-/

/-- **Bruns–Herzog 2.1.27, non-homogeneous prime case** (currently axiomatised
as a single isolated `sorry`).

Given a connected ℕ-graded Noetherian `K`-algebra `A`, a prime ideal `p`
that is *not* homogeneous, and the assumption that the localisation
`A_{p*}` at the homogeneous core `p* := p.homogeneousCore 𝒜` is already
Cohen–Macaulay local, conclude that `A_p` is Cohen–Macaulay local.

This statement is *the* hard content of graded local-to-global CM for
non-homogeneous primes. See the long comment block above for why the
naive "further localisation" reduction does **not** work and why no
smaller ring-theoretic sub-lemma is the missing piece. -/
private theorem caseC_CM_transfer
    (p p_star : Ideal A) (_hp_prime : p.IsPrime)
    [_hpstar_prime : p_star.IsPrime]
    (_hpstar_sub_irr : p_star ≤ (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (_hCM_pstar : IsCohenMacaulayLocalRing (Localization.AtPrime p_star))
    (_hp_not_hom : ¬ p.IsHomogeneous 𝒜) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  sorry

/-- **Case C key lemma (non-homogeneous primes)**: if `A` is a connected
ℕ-graded Noetherian `K`-algebra whose localization at the irrelevant ideal
is Cohen–Macaulay local, then for every *non-homogeneous* prime `p` of `A`,
the localization `A_p` is also Cohen–Macaulay local.

The proof strategy is to transit through the homogeneous core
`p* := p.homogeneousCore 𝒜`, which is prime and sits inside `𝒜₊`:

1. By Case B / the homogeneous branch, `A_{p*}` is already Cohen–Macaulay
   local (we have `hCM` for `𝒜₊`, and "CM localizes" gives the same for
   the smaller prime `p*`).

2. Then `A_p` is a further localization of `A_{p*}` — namely, at the image
   of `p.primeCompl` under `algebraMap A A_{p*}` — and this image, being
   disjoint from `p* · A_{p*}` (one has `p* ≤ p` strictly since `p` is
   non-homogeneous), is the complement of a prime ideal `q` in `A_{p*}`.
   Applying "CM localizes" again yields `A_q` CM local, and the canonical
   isomorphism `A_q ≃ A_p` transports CM to `A_p`.

The graded-theoretic scaffolding (that `p*` is prime, that `p*` sits inside
`𝒜₊`, and that Case B gives CM at `p*`) is fully proved; the remaining
ring-theoretic transfer is isolated in `caseC_CM_transfer`. -/
private theorem isCohenMacaulayLocalRing_atPrime_of_not_isHomogeneous
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := irrelevant_isPrime 𝒜 h𝒜₀
      IsCohenMacaulayLocalRing
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal))
    (p : Ideal A) [hp_prime : p.IsPrime]
    (hp_not_hom : ¬ p.IsHomogeneous 𝒜) :
    IsCohenMacaulayLocalRing (Localization.AtPrime p) := by
  haveI hm_prime : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.IsPrime :=
    irrelevant_isPrime 𝒜 h𝒜₀
  -- `p* := p.homogeneousCore 𝒜` is prime and contained in `𝒜₊`.
  haveI hpstar : (p.homogeneousCore 𝒜).toIdeal.IsPrime :=
    isPrime_homogeneousCore 𝒜 p
  have hpstar_sub : (p.homogeneousCore 𝒜).toIdeal ≤
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal :=
    homogeneousCore_le_irrelevant 𝒜 h𝒜₀ p hp_prime.ne_top
  -- By Case B, `A_{p*}` is already Cohen–Macaulay local.
  have hCM_pstar : IsCohenMacaulayLocalRing
      (Localization.AtPrime (p.homogeneousCore 𝒜).toIdeal) :=
    isCohenMacaulayLocalRing_atPrime_of_isHomogeneous 𝒜 h𝒜₀ hCM
      (p.homogeneousCore 𝒜).toIdeal (p.homogeneousCore 𝒜).isHomogeneous
  -- The remaining step is the ring-theoretic transitivity of localisation
  -- to identify `A_p` with `(A_{p*})_{p'}` for some prime `p'` of `A_{p*}`,
  -- then apply "CM localizes" once more.
  exact caseC_CM_transfer 𝒜 p (p.homogeneousCore 𝒜).toIdeal hp_prime
    hpstar_sub hCM_pstar hp_not_hom

end CaseC

/-! ### Main theorem -/

section Main

/-- **Graded local-to-global Cohen–Macaulay theorem** (Bruns–Herzog 2.1.27,
specialised to ℕ-gradings with `𝒜 0 = K` a field).

For a connected ℕ-graded Noetherian `K`-algebra `A` with irrelevant ideal
`𝒜₊`, if `A` localized at `𝒜₊` is Cohen–Macaulay local, then `A` is
Cohen–Macaulay globally.

The proof splits by whether a prime `p` of `A` is homogeneous:

* **Homogeneous case (Case A ∪ B)** — fully proved: use
  `GradedIrrelevant.homogeneousCore_le_irrelevant` to place `p ≤ 𝒜₊`, then
  apply the tower `A → A_{𝒜₊} → A_p` together with "CM localizes" and the
  canonical ring isomorphism `(A_{𝒜₊})_{p'} ≃ A_p`.
* **Non-homogeneous case (Case C)** — isolated in the private sub-lemma
  `isCohenMacaulayLocalRing_atPrime_of_not_isHomogeneous`, which is the
  one remaining gap.

We package the `IsPrime` instance of the irrelevant ideal (follows from
`ConnectedGraded` via maximality) as an *explicit* `haveI`-derived premise
to phrase the hypothesis on `Localization.AtPrime` cleanly. -/
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := irrelevant_isPrime 𝒜 h𝒜₀
      IsCohenMacaulayLocalRing
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    IsCohenMacaulayRing A where
  CM_localize p hp := by
    haveI := irrelevant_isPrime 𝒜 h𝒜₀
    by_cases h : p.IsHomogeneous 𝒜
    · exact isCohenMacaulayLocalRing_atPrime_of_isHomogeneous 𝒜 h𝒜₀ hCM p h
    · exact isCohenMacaulayLocalRing_atPrime_of_not_isHomogeneous 𝒜 h𝒜₀ hCM p h

/-- Paper-facing version matching the spec requested in the work packet:
takes `h𝒜₀` in the `∀ x ∈ 𝒜 0, ∃ k, algebraMap K A k = x` form. -/
theorem isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant'
    (h𝒜₀ : ∀ x ∈ 𝒜 0, ∃ k : K, algebraMap K A k = x)
    (hCM : haveI := irrelevant_isPrime 𝒜 h𝒜₀
      IsCohenMacaulayLocalRing
      (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    IsCohenMacaulayRing A :=
  isCohenMacaulayRing_of_isCohenMacaulayLocalRing_at_irrelevant 𝒜 h𝒜₀ hCM

end Main

end GradedCM

end

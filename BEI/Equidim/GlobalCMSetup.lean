import BEI.Equidim.MonomialInitial
import BEI.Equidim.Bipartite
import BEI.Equidim.Transport
import BEI.Equidim.ClosedGraphIntervals
import BEI.Equidim.IteratedRegularity
import BEI.Equidim.AugmentationLocalCM
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

noncomputable section

open MvPolynomial SimpleGraph IsLocalRing

/-!
# Equidimensional surrogate: global CM scaffolding

This file isolates the scaffolding needed to lift local Cohen-Macaulayness
at the augmentation ideal to global Cohen-Macaulayness of the HH bipartite
edge ideal quotient: the ideal-quotient-form local CM helper
`isCohenMacaulayLocalRing_idealQuot_lastInl`, the reduced-HH local-CM
corollary `isCohenMacaulayLocalRing_reducedHH_at_augIdeal`, structural
lemmas, flat base change, minimal-prime / regular-element analysis,
the graded contraction lemma and the homogeneity result for the bipartite
edge monomial ideal.

## Reference: Herzog et al. (2010), proof of Proposition 1.6
-/

section GlobalCM

variable {K' : Type*} [Field K']

/-- CM of `Rp ⧸ Ideal.span {x_last}` (ideal-quotient form), transferred from CM of
`QuotSMulTop x_last Rp` via the bridging ring equiv. This unsticks the `Ideal` vs
`Submodule` quotient type mismatch for the second quotient iteration. -/
private theorem isCohenMacaulayLocalRing_idealQuot_lastInl {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    haveI : Nontrivial (Localization.AtPrime (augIdeal (K := K') G) ⧸
        Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
            (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
      Ideal.Quotient.nontrivial_iff.mpr (span_x_inl_last_ne_top (K := K') (by omega) G)
    haveI : IsLocalRing (Localization.AtPrime (augIdeal (K := K') G) ⧸
        Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
            (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
      IsLocalRing.of_surjective'
        (Ideal.Quotient.mk (Ideal.span {algebraMap _
          (Localization.AtPrime (augIdeal (K := K') G))
          (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
            (X (Sum.inl ⟨n - 1, by omega⟩)))}))
        Ideal.Quotient.mk_surjective
    IsCohenMacaulayLocalRing (Localization.AtPrime (augIdeal (K := K') G) ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}) := by
  haveI := quotSMulTopLocalRing (X_inl_last_mem_maximalIdeal (K := K') (by omega) G)
  haveI : Nontrivial (Localization.AtPrime (augIdeal (K := K') G) ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_x_inl_last_ne_top (K := K') (by omega) G)
  haveI : IsLocalRing (Localization.AtPrime (augIdeal (K := K') G) ⧸
      Ideal.span {algebraMap _ (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}) :=
    IsLocalRing.of_surjective'
      (Ideal.Quotient.mk (Ideal.span {algebraMap _
        (Localization.AtPrime (augIdeal (K := K') G))
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
          (X (Sum.inl ⟨n - 1, by omega⟩)))}))
      Ideal.Quotient.mk_surjective
  have hCM := isCohenMacaulayLocalRing_quot_lastInl (K := K') hn hHH
  exact isCohenMacaulayLocalRing_of_ringEquiv' hCM
    (quotSMulTopRingEquivIdealQuotient _)

set_option synthInstance.maxHeartbeats 400000 in
-- synth budget needed: iterated quotient-by-regular-element + CM instance search.
/-- **L5 CM corollary**: the reduced HH ring at its augmentation is Cohen–Macaulay.
Specifically, `(Rp ⧸ x_last) ⧸ (mk y_last)` is CM local. This is the reduced HH ring
(HH ring with the trailing isolated pair dropped) localized at its own augmentation. -/
theorem isCohenMacaulayLocalRing_reducedHH_at_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G) :
    let Rp := Localization.AtPrime (augIdeal (K := K') G)
    let xL : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
        (X (Sum.inl ⟨n - 1, by omega⟩)))
    let yL : Rp := algebraMap _ Rp
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K') G)
        (X (Sum.inr ⟨n - 1, by omega⟩)))
    let RpQ := Rp ⧸ Ideal.span {xL}
    let mkyL : RpQ := Ideal.Quotient.mk (Ideal.span {xL}) yL
    haveI : Nontrivial RpQ := Ideal.Quotient.nontrivial_iff.mpr
      (span_x_inl_last_ne_top (K := K') (by omega) G)
    haveI : IsLocalRing RpQ :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    haveI hmem_max : mkyL ∈ IsLocalRing.maximalIdeal RpQ := by
      have hlocal : IsLocalHom (Ideal.Quotient.mk (Ideal.span {xL})) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      rw [IsLocalRing.mem_maximalIdeal]
      intro hunit
      have hmem := X_inr_last_mem_maximalIdeal (K := K') (by omega) G
      rw [IsLocalRing.mem_maximalIdeal] at hmem
      exact hmem (hlocal.map_nonunit _ hunit)
    haveI := quotSMulTopLocalRing hmem_max
    IsCohenMacaulayLocalRing (QuotSMulTop mkyL RpQ) := by
  intros Rp xL yL RpQ mkyL
  haveI : Nontrivial RpQ := Ideal.Quotient.nontrivial_iff.mpr
    (span_x_inl_last_ne_top (K := K') (by omega) G)
  haveI : IsLocalRing RpQ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  haveI : IsCohenMacaulayLocalRing RpQ := isCohenMacaulayLocalRing_idealQuot_lastInl hn hHH
  have hmem_max : mkyL ∈ IsLocalRing.maximalIdeal RpQ := by
    have hlocal : IsLocalHom (Ideal.Quotient.mk (Ideal.span {xL})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [IsLocalRing.mem_maximalIdeal]
    intro hunit
    have hmem := X_inr_last_mem_maximalIdeal (K := K') (by omega) G
    rw [IsLocalRing.mem_maximalIdeal] at hmem
    exact hmem (hlocal.map_nonunit _ hunit)
  -- IsSMulRegular of mkyL on RpQ as self-scalar
  have hreg : IsSMulRegular RpQ mkyL := by
    -- Step 1: transfer IsSMulRegular of yL (Rp-scalar) from QuotSMulTop to RpQ
    have hreg_Rp : IsSMulRegular RpQ yL := by
      have h := isSMulRegular_X_inr_last_quot_lastInl (K := K') hn hHH
      exact (LinearEquiv.isSMulRegular_congr
        (Submodule.quotEquivOfEq _ _ (Submodule.smul_top_eq_span_singleton _)) _).mp h
    -- Step 2: convert Rp-scalar to self-scalar
    exact (isSMulRegular_map (a := yL)
      (fun r : Rp => (Ideal.Quotient.mk (Ideal.span {xL}) r))
      (fun _ => rfl)).mpr hreg_Rp
  exact isCohenMacaulayLocalRing_quotient hreg hmem_max



variable {K : Type*} [Field K]

/-! #### Structural lemmas for the graded local-to-global step -/

/-- In the quotient by the bipartite edge monomial ideal, if all variable images lie in
a prime `p`, then the augmentation ideal is contained in `p`.

The proof uses `MvPolynomial.mem_ideal_span_X_image`: a polynomial with zero constant
coefficient lies in the ideal generated by variables. -/
private lemma augIdeal_le_of_forall_mkI_X_mem {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    (hvar : ∀ v : BinomialEdgeVars (Fin n),
      Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∈ p) :
    augIdeal (K := K) G ≤ p := by
  intro a ha
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [augIdeal, RingHom.mem_ker, quotConstCoeff, Ideal.Quotient.lift_mk] at ha
  -- f has zero constant coefficient → f ∈ Ideal.span (range X)
  have hmem : f ∈ Ideal.span (Set.range
      (X : BinomialEdgeVars (Fin n) → MvPolynomial (BinomialEdgeVars (Fin n)) K)) := by
    rw [show Set.range X = X '' Set.univ from Set.image_univ.symm,
        MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    have : m ≠ 0 := by
      intro h; subst h
      simp only [MvPolynomial.mem_support_iff] at hm; exact hm ha
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp this
    exact ⟨i, Set.mem_univ _, hi⟩
  -- The image of span(range X) under mk is contained in p
  have hmap : Ideal.map (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
      (Ideal.span (Set.range X)) ≤ p := by
    rw [Ideal.map_span]
    apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hf
    exact hvar v
  exact hmap (Ideal.mem_map_of_mem _ hmem)

/-- If a prime `p` is not contained in the augmentation ideal, then some variable
image lies outside `p`.

Proof: `augIdeal` is maximal; if all variable images were in `p`, then
`augIdeal ≤ p` by `augIdeal_le_of_forall_mkI_X_mem`, so `p = augIdeal`
(maximality), contradicting `p ⊄ augIdeal`. -/
private lemma exists_var_not_mem_of_not_le_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    (hp : ¬(p ≤ augIdeal (K := K) G)) :
    ∃ v : BinomialEdgeVars (Fin n),
      Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∉ p := by
  by_contra h
  push_neg at h
  -- All variable images are in p, so augIdeal ≤ p
  have h_le := augIdeal_le_of_forall_mkI_X_mem G h
  -- augIdeal is maximal and p is proper, so augIdeal = p, hence p ≤ augIdeal
  exact hp ((augIdeal_isMaximal (K := K) G).eq_of_le
    (Ideal.IsPrime.ne_top ‹_›) h_le).symm.le

/-- A variable image not in `p` becomes a unit in the localization `R_p`. -/
private lemma isUnit_algebraMap_mkI_X {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {v : BinomialEdgeVars (Fin n)}
    (hv : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∉ p) :
    IsUnit (algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v))) :=
  IsLocalization.map_units (Localization.AtPrime p) ⟨_, show _ ∈ p.primeCompl from hv⟩

/-- In the localization `R_p`, if a variable `X v` is a unit and `X v * X w ∈ I`
(i.e., `(v, w)` is an edge of the HH bipartite graph), then `X w` maps to zero.

This is the key structural fact: inverting one variable kills its neighbors in the
bipartite graph. -/
private lemma algebraMap_mkI_X_eq_zero_of_edge {n : ℕ} (G : SimpleGraph (Fin n))
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {v w : BinomialEdgeVars (Fin n)}
    (hedge : X v * X w ∈ bipartiteEdgeMonomialIdeal (K := K) G)
    (hv : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X v) ∉ p) :
    algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G) (X w)) = 0 := by
  set mk := Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
  set Rp := Localization.AtPrime p
  have h0 : mk (X v * X w) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hedge
  have h1 : algebraMap _ Rp (mk (X v)) * algebraMap _ Rp (mk (X w)) = 0 := by
    rw [← map_mul, ← map_mul, h0, map_zero]
  exact (IsUnit.mul_right_eq_zero (isUnit_algebraMap_mkI_X G hv)).mp h1

/-- Under HH conditions with `p ⊄ augIdeal`, every diagonal edge `(x_i, y_i)` in the
HH bipartite graph has one endpoint that is a unit and the other that is zero in `R_p`.

More precisely: if `Sum.inl i` is not in `p`, then `y_i` maps to zero (and vice versa).
The HH diagonal ensures `x_i y_i ∈ I` for `i + 1 < n`. -/
private lemma algebraMap_mkI_y_eq_zero_of_x_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (hHH : HerzogHibiConditions n G)
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {i : Fin n} (hi : i.val + 1 < n)
    (hxi : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inl i)) ∉ p) :
    algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inr i))) = 0 := by
  apply algebraMap_mkI_X_eq_zero_of_edge G _ hxi
  exact Ideal.subset_span ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩

/-- Symmetric version: if `Sum.inr i` is not in `p`, then `x_i` maps to zero. -/
private lemma algebraMap_mkI_x_eq_zero_of_y_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (hHH : HerzogHibiConditions n G)
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    {i : Fin n} (hi : i.val + 1 < n)
    (hyi : Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
      (X (Sum.inr i)) ∉ p) :
    algebraMap _ (Localization.AtPrime p)
      (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G)
        (X (Sum.inl i))) = 0 := by
  apply algebraMap_mkI_X_eq_zero_of_edge G _ hyi
  -- Need X (Sum.inr i) * X (Sum.inl i) ∈ I; the ideal contains x_i * y_i = y_i * x_i
  have hmem : X (Sum.inl i) * X (Sum.inr i) ∈
      bipartiteEdgeMonomialIdeal (K := K) G :=
    Ideal.subset_span ⟨i, i, hi, hHH.diagonal i hi, le_refl i, rfl⟩
  rwa [mul_comm] at hmem

/-! #### Flat base change: full regular sequence is weakly regular on any localization -/

/-- The full regular sequence, mapped to any localization `R_p`, is weakly regular
on `R_p` as an `R_p`-module. This holds for ALL primes `p`, regardless of whether
`p ≤ augIdeal`.

The proof uses flat base change: localization is flat, so `IsWeaklyRegular R rs`
transfers to `IsWeaklyRegular (R ⊗ R_p) rs` by `isWeaklyRegular_rTensor`,
then `R ⊗_R R_p ≅ R_p` by `TensorProduct.lid`, and finally
`isWeaklyRegular_map_algebraMap_iff` converts to the mapped sequence. -/
private lemma fullRegSeq_isWeaklyRegular_localization
    {n : ℕ} (hn : 2 ≤ n) {G : SimpleGraph (Fin n)}
    (hHH : HerzogHibiConditions n G)
    (p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G))
    [p.IsPrime] :
    RingTheory.Sequence.IsWeaklyRegular (Localization.AtPrime p)
      (((fullRegSeq (K := K) n hn).map
        (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))).map
        (algebraMap _ (Localization.AtPrime p))) := by
  set R := MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G
  set Rp := Localization.AtPrime p
  set rs := (fullRegSeq (K := K) n hn).map
    (Ideal.Quotient.mk (bipartiteEdgeMonomialIdeal (K := K) G))
  -- fullRegSeq is weakly regular on R
  have hreg : RingTheory.Sequence.IsWeaklyRegular R rs :=
    bipartiteEdgeMonomialIdeal_isWeaklyRegular_full (K := K) hn hHH
  -- R_p is flat over R
  haveI : Module.Flat R Rp := IsLocalization.flat Rp p.primeCompl
  -- Flat base change + lid + algebraMap iff
  exact (RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff Rp Rp rs).mpr
    ((LinearEquiv.isWeaklyRegular_congr (TensorProduct.lid R Rp) rs).mp
      hreg.isWeaklyRegular_rTensor)

/-! #### Minimal primes are below the augmentation ideal -/

/-- Every minimal prime of the HH quotient ring is contained in the augmentation ideal.

The proof uses the minimal vertex cover classification: each minimal prime of the
bipartite edge monomial ideal is `span(X '' C)` for a vertex cover `C`. Its image
in the quotient ring is generated by variable images, all of which lie in the
augmentation ideal by `mkI_X_mem_augIdeal`. -/
private lemma minimalPrime_le_augIdeal {n : ℕ} (G : SimpleGraph (Fin n))
    {q : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    (hq : q ∈ minimalPrimes _) :
    q ≤ augIdeal (K := K) G := by
  -- Q = comap mk q is a minimal prime of bipartiteEdgeMonomialIdeal G
  have hQ : (q.comap (Ideal.Quotient.mk _)) ∈
      (bipartiteEdgeMonomialIdeal (K := K) G).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q, hq, rfl⟩
  -- Q = span(X '' C) for some minimal vertex cover C
  obtain ⟨C, _, hQeq⟩ := (minimalPrime_bipartiteEdgeMonomialIdeal_iff G).mp hQ
  -- q = map mk (comap mk q) since mk is surjective
  rw [show q = (q.comap (Ideal.Quotient.mk _)).map (Ideal.Quotient.mk _) from
    (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q).symm]
  -- Now q = map mk (span(X '' C)), generated by variable images
  rw [hQeq, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨v, _, rfl⟩ := hf
  exact mkI_X_mem_augIdeal G v

/-! #### Regular elements in primes of positive height -/

/-- **Regular element in `p ∩ augIdeal` for the HH quotient**: For any prime `p` not
contained in the augmentation ideal, there exists an element of `p ∩ augIdeal` that is
a non-zero-divisor on the HH quotient ring.

This is the key ingredient for the graded CM induction: it provides the regular element
in `maxIdeal(R_p) ∩ maxIdeal(R_{m⁺})` needed for both forward and converse CM transfer.

The proof uses:
- the HH quotient is reduced (`bipartiteEdgeMonomialIdeal_isRadical`);
- all minimal primes are below `augIdeal` (`minimalPrime_le_augIdeal`);
- a domain-based prime avoidance argument (`exists_smulRegular_in_inter`). -/
private lemma exists_smulRegular_in_augIdeal {n : ℕ} (hn : 2 ≤ n)
    {G : SimpleGraph (Fin n)} (hHH : HerzogHibiConditions n G)
    {p : Ideal (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G)}
    [p.IsPrime]
    (hp : ¬(p ≤ augIdeal (K := K) G)) :
    ∃ x ∈ p, x ∈ augIdeal (K := K) G ∧
      IsSMulRegular (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
        bipartiteEdgeMonomialIdeal (K := K) G) x := by
  -- Abbreviations (using let to avoid set-renaming issues)
  change ∃ x ∈ p, x ∈ augIdeal (K := K) G ∧ IsSMulRegular _ x
  haveI hm_prime : (augIdeal (K := K) G).IsPrime := augIdeal_isPrime G
  haveI : IsReduced (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (bipartiteEdgeMonomialIdeal_isRadical G)
  haveI : IsNoetherianRing (MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸
      bipartiteEdgeMonomialIdeal (K := K) G) :=
    Ideal.Quotient.isNoetherianRing _
  -- height(p) > 0: all minimal primes ≤ augIdeal, so p minimal ⟹ p ≤ augIdeal
  have hp_pos : (0 : WithBot ℕ∞) < Ideal.height p := by
    rw [Ideal.height_eq_primeHeight]
    by_contra h; push_neg at h
    have h0 : p.primeHeight = 0 := nonpos_iff_eq_zero.mp (by exact_mod_cast h)
    exact hp (minimalPrime_le_augIdeal G (Ideal.primeHeight_eq_zero_iff.mp h0))
  -- augIdeal is not minimal: if it were, sInf = augIdeal, but sInf = 0 (reduced).
  -- Then augIdeal = ⊥ means ⊥ is maximal, so R is a field with dim 0,
  -- contradicting dim(R) = n+1 ≥ 3.
  set R' := MvPolynomial (BinomialEdgeVars (Fin n)) K ⧸ bipartiteEdgeMonomialIdeal (K := K) G
  have hm_ne_min : augIdeal (K := K) G ∉ minimalPrimes R' := by
    intro hmin
    have hsInf : sInf (minimalPrimes R') = augIdeal (K := K) G := le_antisymm
      (sInf_le hmin)
      (le_sInf (fun q hq => (minimalPrimes_eq_minimals (R := R') ▸ hmin).2
        (minimalPrimes_eq_minimals (R := R') ▸ hq).1 (minimalPrime_le_augIdeal G hq)))
    have h0 : sInf (minimalPrimes R') = (⊥ : Ideal R') := by
      change sInf ((⊥ : Ideal R').minimalPrimes) = ⊥
      rw [Ideal.sInf_minimalPrimes]; exact nilradical_eq_zero R'
    have hbot : augIdeal (K := K) G = ⊥ := by rw [← hsInf, h0]
    have hdim := ringKrullDim_bipartiteEdgeMonomialIdeal (K := K) (by omega : 1 ≤ n) hHH
    haveI : (nilradical R').IsMaximal := by
      have : nilradical R' = ⊥ := nilradical_eq_zero R'
      rw [this]; exact hbot ▸ augIdeal_isMaximal G
    haveI := Ring.KrullDimLE.of_isMaximal_nilradical R'
    haveI : Nontrivial R' := Ideal.Quotient.nontrivial_iff.mpr
      (bipartiteEdgeMonomialIdeal_ne_top (K := K) G)
    have hfield : ringKrullDim R' = 0 := (ringKrullDimZero_iff_ringKrullDim_eq_zero).mp ‹_›
    rw [hfield] at hdim; exact absurd hdim (by norm_cast)
  exact exists_smulRegular_in_inter (augIdeal (K := K) G)
    (fun q hq => minimalPrime_le_augIdeal G hq) hm_ne_min p hp_pos

/-! #### Graded contraction lemma

The **graded contraction lemma** for `MvPolynomial` quotients:
in a quotient by a homogeneous ideal, any element with invertible constant
coefficient is a non-zero-divisor.  This is the key ingredient in the
Bruns–Herzog 2.1.3(b) proof that graded CM at the irrelevant ideal implies
global CM. -/

/-! #### Homogeneity of the bipartite edge monomial ideal -/

/-- The bipartite edge monomial ideal is a monomial ideal: for every polynomial
in `I`, each support monomial (with coefficient 1) is also in `I`. -/
private theorem bipartiteEdgeMonomialIdeal_isMonomial {n : ℕ}
    (G : SimpleGraph (Fin n)) :
    (bipartiteEdgeMonomialIdeal (K := K) G).IsMonomial := by
  apply isMonomial_span_of_support_singleton
  rintro _ ⟨i, j, hj, hadj, hle, rfl⟩
  exact ⟨Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1, by
    rw [show (X (Sum.inl i) * X (Sum.inr j) : MvPolynomial _ K) =
      monomial (Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr j) 1) 1 from by
      simp [X, monomial_mul]]
    exact support_monomial_subset⟩

/-- Monomial ideals are closed under taking homogeneous components. -/
private theorem isMonomial_homogeneousComponent_mem {n : ℕ}
    (G : SimpleGraph (Fin n))
    (p : MvPolynomial (BinomialEdgeVars (Fin n)) K)
    (hp : p ∈ bipartiteEdgeMonomialIdeal (K := K) G) (d : ℕ) :
    MvPolynomial.homogeneousComponent d p ∈ bipartiteEdgeMonomialIdeal (K := K) G := by
  classical
  rw [MvPolynomial.homogeneousComponent_apply]
  apply Ideal.sum_mem
  intro m hm
  rw [Finset.mem_filter] at hm
  have hmon : MvPolynomial.monomial m (1 : K) ∈ bipartiteEdgeMonomialIdeal (K := K) G :=
    bipartiteEdgeMonomialIdeal_isMonomial G p hp m hm.1
  rw [show MvPolynomial.monomial m (MvPolynomial.coeff m p) =
    MvPolynomial.C (MvPolynomial.coeff m p) * MvPolynomial.monomial m 1 from by
    rw [MvPolynomial.C_mul_monomial, mul_one]]
  exact Ideal.mul_mem_left _ _ hmon


end GlobalCM

end

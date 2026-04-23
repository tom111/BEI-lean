/-
Equidimensionality of graded f.g. K-algebras that are CM at the irrelevant ideal.

This assembles Step A + Step C of the finite-free Case C route with the
`IsEquidimRing.of_flat_finite` bridge from `toMathlib/FiniteFreeEquidim.lean`:
for a connected ℕ-graded Noetherian `K`-algebra `A` of finite type over `K`,
Cohen–Macaulayness at the irrelevant ideal makes `A` into a finite free module
over `MvPolynomial (Fin d) K` (Step A + Step C), and module-finite + module-flat
over a Noetherian domain forces every minimal prime to have quotient dimension
equal to `d`.

## Main result

- `isEquidimRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree` —
  CM at the irrelevant ideal ⟹ `IsEquidimRing A`.
-/

import toMathlib.GradedRegularSop
import toMathlib.FiniteFreeEquidim

open MvPolynomial GradedIrrelevant

namespace GradedFiniteFree

universe u

/-- **Graded CM at the irrelevant ideal ⟹ equidimensional.**

For a connected ℕ-graded Noetherian `K`-algebra `A` of finite type over `K`
whose localization at the irrelevant ideal is Cohen–Macaulay local, `A` is
equidimensional in the sense of `IsEquidimRing`: all minimal primes have
equal quotient Krull dimension.

Proof: Step A produces a homogeneous `A`-regular sop `θ` of length `d` with
`A ⧸ ⟨θ⟩` finite over `K`. Step C lifts this to a finite-free structure of
`A` as a `MvPolynomial (Fin d) K`-module via `T_i ↦ θ_i`. `MvPolynomial (Fin d) K`
is an integral domain, `Module.Free` implies `Module.Flat`, and then
`IsEquidimRing.of_flat_finite` applies. -/
theorem isEquidimRing_of_isCohenMacaulayLocalRing_at_irrelevant_finiteFree
    {K A : Type u} [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    [IsNoetherianRing A] [Algebra.FiniteType K A]
    (h𝒜₀ : ConnectedGraded 𝒜)
    (hCM : haveI := (GradedIrrelevant.irrelevant_isMaximal 𝒜 h𝒜₀).isPrime
      IsCohenMacaulayLocalRing
        (Localization.AtPrime (HomogeneousIdeal.irrelevant 𝒜).toIdeal)) :
    IsEquidimRing A := by
  classical
  obtain ⟨d, θ, hθ_len, hθ_hom, hθ_irr, hθ_reg, hA_fin⟩ :=
    GradedRegularSop.exists_homogeneous_regular_sop_of_cm_at_irrelevant 𝒜 h𝒜₀ hCM
  let θ' : Fin d → A := fun i => θ.get (Fin.cast hθ_len.symm i)
  have hθ'_list : List.ofFn θ' = θ := by
    apply List.ext_getElem
    · simp [hθ_len]
    · intros n hn1 hn2
      simp only [θ', List.getElem_ofFn, List.get_eq_getElem, Fin.cast_mk]
  have hθ'_hom : ∀ i, SetLike.IsHomogeneousElem 𝒜 (θ' i) := fun i =>
    hθ_hom _ (List.get_mem _ _)
  have hθ'_irr : ∀ i, θ' i ∈ (HomogeneousIdeal.irrelevant 𝒜).toIdeal := fun i =>
    hθ_irr _ (List.get_mem _ _)
  have hθ'_reg : RingTheory.Sequence.IsWeaklyRegular A (List.ofFn θ') := by
    rw [hθ'_list]; exact hθ_reg
  have hA'_fin : Module.Finite K (A ⧸ Ideal.ofList (List.ofFn θ')) := by
    rw [hθ'_list]; exact hA_fin
  letI alg : Algebra (MvPolynomial (Fin d) K) A :=
    (MvPolynomial.aeval θ').toAlgebra
  obtain ⟨_hFinite, _hFree⟩ :=
    finiteFree_over_mvPolynomial_of_homogeneous_regular_sop
      𝒜 h𝒜₀ θ' hθ'_hom hθ'_irr hθ'_reg hA'_fin
  haveI : IsDomain (MvPolynomial (Fin d) K) := inferInstance
  haveI : Module.Flat (MvPolynomial (Fin d) K) A := Module.Flat.of_free
  exact IsEquidimRing.of_flat_finite (R := MvPolynomial (Fin d) K)

end GradedFiniteFree

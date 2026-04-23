/-
Equidimensionality for flat module-finite algebras over a Noetherian domain.

For `R` an integral domain and `A` a module-finite, module-flat `R`-algebra
with `R → A` injective, every minimal prime `P` of `A` satisfies
`ringKrullDim (A ⧸ P) = ringKrullDim R`, and therefore `A` is equidimensional
in the sense of `IsEquidimRing`.

Proof outline:
- Going-down (`Module.Flat`) pins every minimal prime of `A` to lie over `⊥`
  in `R` (`Ideal.minimalPrimes_under_eq_bot_of_flat`).
- The induced composition `R → A → A/P` is still module-finite (integral) and
  injective, so `ringKrullDim (A/P) = ringKrullDim R` via
  `ringKrullDim_eq_of_finite_of_injective` from `toMathlib/IntegralDimension.lean`.
  (No flatness is needed for this dim equality — incomparability for `≤`
  and going-up chain lift for `≥`.)
-/

import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import toMathlib.Equidim.Defs
import toMathlib.IntegralDimension

open Ideal

namespace Ideal

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- For `A` flat over an integral domain `R`, every minimal prime of `A`
lies over `⊥` in `R`.

Proof: if `P.under R ≠ ⊥`, then `⊥ < P.under R` in `R` (`⊥` is prime since
`R` is a domain; `P.under R` is prime as a comap). Going-down (from flatness)
gives a prime `Q < P` in `A` with `Q.under R = ⊥`. But `P` is minimal,
forcing `P ≤ Q`, contradicting `Q < P`. -/
theorem minimalPrimes_under_eq_bot_of_flat [Module.Flat R A]
    {P : Ideal A} (hP : P ∈ minimalPrimes A) :
    P.under R = ⊥ := by
  haveI : P.IsPrime := hP.1.1
  haveI : (P.under R).IsPrime := inferInstance
  by_contra hne
  have hlt : (⊥ : Ideal R) < P.under R := lt_of_le_of_ne bot_le (Ne.symm hne)
  obtain ⟨Q, hQlt, hQ_prime, _⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt
      (p := (⊥ : Ideal R)) (q := P.under R) P hlt
  have hP_le_Q : P ≤ Q := hP.2 ⟨hQ_prime, bot_le⟩ hQlt.le
  exact absurd (le_antisymm hQlt.le hP_le_Q) (ne_of_lt hQlt)

end Ideal

namespace IsEquidimRing

variable {R A : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]

/-- For an integral domain `R` and a module-finite, module-flat `R`-algebra
`A`, each minimal prime `P` of `A` has quotient Krull dimension equal to
`ringKrullDim R`.

Proof: by `Ideal.minimalPrimes_under_eq_bot_of_flat`, `P.under R = ⊥`.
Hence the composition `R → A → A/P` is injective. `A/P` is module-finite over
`R` (quotient of a finite module). Apply
`ringKrullDim_eq_of_finite_of_injective`.

Injectivity of `R → A` is not assumed: flatness + `R` a domain forces the
kernel of `R → A` to be contained in every minimal prime of `A`, hence in
`⊥`, so the kernel is already `⊥` whenever `A` has a minimal prime. -/
theorem ringKrullDim_quotient_minimalPrime_eq
    [Module.Finite R A] [Module.Flat R A]
    {P : Ideal A} (hP : P ∈ minimalPrimes A) :
    ringKrullDim (A ⧸ P) = ringKrullDim R := by
  haveI : P.IsPrime := hP.1.1
  have hunder : P.under R = ⊥ :=
    Ideal.minimalPrimes_under_eq_bot_of_flat hP
  -- A/P is module-finite over R via the R-linear surjection A → A/P
  haveI : Module.Finite R (A ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R P).toLinearMap
      (Ideal.Quotient.mkₐ_surjective R P)
  -- R → A/P is injective: kernel = P.under R = ⊥
  have hinj' : Function.Injective (algebraMap R (A ⧸ P)) := by
    have hker : RingHom.ker (algebraMap R (A ⧸ P)) = ⊥ := by
      rw [show algebraMap R (A ⧸ P) =
          (Ideal.Quotient.mk P).comp (algebraMap R A) from rfl,
        ← RingHom.comap_ker, Ideal.mk_ker, ← Ideal.under_def, hunder]
    rw [RingHom.injective_iff_ker_eq_bot, hker]
  exact ringKrullDim_eq_of_finite_of_injective hinj'

/-- **Main bridge**: for an integral domain `R` and a module-finite,
module-flat `R`-algebra `A`, `A` is equidimensional in the sense of
`IsEquidimRing` (all minimal primes have equal quotient Krull dimension). -/
theorem of_flat_finite
    [Module.Finite R A] [Module.Flat R A] :
    IsEquidimRing A where
  equidimensional P Q hP hQ := by
    rw [ringKrullDim_quotient_minimalPrime_eq (R := R) hP,
        ringKrullDim_quotient_minimalPrime_eq (R := R) hQ]

end IsEquidimRing
